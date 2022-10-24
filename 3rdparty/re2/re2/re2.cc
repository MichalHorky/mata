// Copyright 2003-2009 The RE2 Authors.  All Rights Reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Regular expression interface RE2.
//
// Originally the PCRE C++ wrapper, but adapted to use
// the new automata-based regular expression engines.

#include "re2/re2.h"

#ifdef _MSC_VER
#endif
#include <stdint.h>
#include <string>
#include <vector>

#include "ca/derivatives.h"
#include "util/logging.h"
#include "re2/prog.h"
#include "re2/regexp.h"
#include "re2/sparse_array.h"

namespace re2 {

const int RE2::Options::kDefaultMaxMem;  // initialized in re2.h

// static empty objects for use as const references.
// To avoid global constructors, allocated in RE2::Init().
static const std::string* empty_string;
static const std::map<std::string, int>* empty_named_groups;
static const std::map<int, std::string>* empty_group_names;

// Converts from Regexp error code to RE2 error code.
// Maybe some day they will diverge.  In any event, this
// hides the existence of Regexp from RE2 users.
static RE2::ErrorCode RegexpErrorToRE2(re2::RegexpStatusCode code) {
  switch (code) {
    case re2::kRegexpSuccess:
        return RE2::NoError;
    case re2::kRegexpInternalError:
        return RE2::ErrorInternal;
    case re2::kRegexpBadEscape:
        return RE2::ErrorBadEscape;
    case re2::kRegexpBadCharClass:
        return RE2::ErrorBadCharClass;
    case re2::kRegexpBadCharRange:
        return RE2::ErrorBadCharRange;
    case re2::kRegexpMissingBracket:
        return RE2::ErrorMissingBracket;
    case re2::kRegexpMissingParen:
        return RE2::ErrorMissingParen;
    case re2::kRegexpUnexpectedParen:
        return RE2::ErrorUnexpectedParen;
    case re2::kRegexpTrailingBackslash:
        return RE2::ErrorTrailingBackslash;
    case re2::kRegexpRepeatArgument:
        return RE2::ErrorRepeatArgument;
    case re2::kRegexpRepeatSize:
        return RE2::ErrorRepeatSize;
    case re2::kRegexpRepeatOp:
        return RE2::ErrorRepeatOp;
    case re2::kRegexpBadPerlOp:
        return RE2::ErrorBadPerlOp;
    case re2::kRegexpBadUTF8:
        return RE2::ErrorBadUTF8;
    case re2::kRegexpBadNamedCapture:
        return RE2::ErrorBadNamedCapture;
  }
  return RE2::ErrorInternal;
}

static std::string trunc(const StringPiece& pattern) {
  if (pattern.size() < 100)
    return std::string(pattern);
  return std::string(pattern.substr(0, 100)) + "...";
}

RE2::RE2(const std::string& pattern) {
  RE2::Options opt;
  Init(pattern, opt);
}

int RE2::Options::ParseFlags() const {
  int flags = Regexp::ClassNL;
  switch (encoding()) {
    default:
      if (log_errors())
        LOG(ERROR) << "Unknown encoding " << encoding();
      break;
    case RE2::Options::EncodingUTF8:
      break;
    case RE2::Options::EncodingLatin1:
      flags |= Regexp::Latin1;
      break;
  }

  if (!posix_syntax())
    flags |= Regexp::LikePerl;

  if (literal())
    flags |= Regexp::Literal;

  if (never_nl())
    flags |= Regexp::NeverNL;

  if (dot_nl())
    flags |= Regexp::DotNL;

  if (never_capture())
    flags |= Regexp::NeverCapture;

  if (!case_sensitive())
    flags |= Regexp::FoldCase;

  if (perl_classes())
    flags |= Regexp::PerlClasses;

  if (word_boundary())
    flags |= Regexp::PerlB;

  if (one_line())
    flags |= Regexp::OneLine;

  return flags;
}

void RE2::Init(const StringPiece& pattern, const Options& options) {
    static std::once_flag empty_once;
    std::call_once(empty_once, []() {
        empty_string = new std::string;
        empty_named_groups = new std::map<std::string, int>;
        empty_group_names = new std::map<int, std::string>;
    });
    options_.Copy(options);
    std::string newPatternString;

    pattern_.assign(pattern.data(), pattern.size());
    entire_regexp_ = NULL;
    error_ = empty_string;
    error_code_ = NoError;
    error_arg_.clear();
    prefix_.clear();
    prefix_foldcase_ = false;
    suffix_regexp_ = NULL;
    prog_ = NULL;
    num_captures_ = -1;
    is_one_pass_ = false;

    rprog_ = NULL;
    named_groups_ = NULL;
    group_names_ = NULL;

    RegexpStatus status;
    entire_regexp_ = Regexp::Parse(
            pattern_,
            static_cast<Regexp::ParseFlags>(options_.ParseFlags()),
            &status);
    if (entire_regexp_ == NULL) {
        if (options_.log_errors()) {
            LOG(ERROR) << "Error parsing '" << trunc(pattern_) << "': "
                       << status.Text();
        }
        error_ = new std::string(status.Text());
        error_code_ = RegexpErrorToRE2(status.code());
        error_arg_ = std::string(status.error_arg());
        return;
    }

    re2::Regexp *suffix;
    if (entire_regexp_->RequiredPrefix(&prefix_, &prefix_foldcase_, &suffix))
        suffix_regexp_ = suffix;
    else
        suffix_regexp_ = entire_regexp_->Incref();

    // Two thirds of the memory goes to the forward Prog,
    // one third to the reverse prog, because the forward
    // Prog has two DFAs but the reverse prog has one.
    prog_ = suffix_regexp_->CompileToProg(options_.max_mem() * 2 / 3);
    if (prog_ == NULL) {
        if (options_.log_errors())
            LOG(ERROR) << "Error compiling '" << trunc(pattern_) << "'";
        error_ = new std::string("pattern too large - compile failed");
        error_code_ = RE2::ErrorPatternTooLarge;
        return;
    }
    // We used to compute this lazily, but it's used during the
    // typical control flow for a match call, so we now compute
    // it eagerly, which avoids the overhead of std::once_flag.
    num_captures_ = suffix_regexp_->NumCaptures();

    // Could delay this until the first match call that
    // cares about submatch information, but the one-pass
    // machine's memory gets cut from the DFA memory budget,
    // and that is harder to do if the DFA has already
    // been built.
    is_one_pass_ = prog_->IsOnePass();
}

RE2::~RE2() {
  if (suffix_regexp_)
    suffix_regexp_->Decref();
  if (entire_regexp_)
    entire_regexp_->Decref();
  delete prog_;
  delete rprog_;
  if (error_ != empty_string)
    delete error_;
  if (named_groups_ != NULL && named_groups_ != empty_named_groups)
    delete named_groups_;
  if (group_names_ != NULL &&  group_names_ != empty_group_names)
    delete group_names_;
}

}  // namespace re2
