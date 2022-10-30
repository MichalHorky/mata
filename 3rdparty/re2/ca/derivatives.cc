//
// Created by Michal Horký (xhorky23) on 21.08.2020.
//

#include "derivatives.h"
#include "re2/re2.h"
#include "re2/prog.h"

#include <iostream>

namespace re2 {
    re2::Regexp *Regexp::Derivatives::getCa(const std::string& pattern) {
        RE2 re2_regex(pattern);
        re2::Regexp *regexp = re2_regex.Regexp();
        re2::Prog *prog = re2_regex.Prog();
        const uint8_t *bytemap = prog->bytemap();
        int bytemapRange = prog->bytemap_range();
        re2::Regexp *normalizedRegex;
        normalizedRegex = this->normalizeRegexp(regexp);
        this->unsetFinalStateCondition = {};
        this->unsetFinalStateCondition.isSet = false;
        this->finalStates = std::vector<finalStateCondition>(50, this->unsetFinalStateCondition);
        this->partialDerivatives.resize(50, {});
        this->existingPartialDerivatives.resize(50, false);
        this->countingLoopBounds.resize(50, {});
        this->countingLoopCounter = 1;
        this->computeNewState(normalizedRegex, bytemap, bytemapRange);
        // The vector must have same length as CA have number of states so every state can be checked
        this->finalStates.resize(this->caStates.size(), this->unsetFinalStateCondition);
        this->finalStates[this->emptyStateNumber] = {Derivatives::True, 0, 0, 0, true};
        this->bytemap_array = bytemap;
        this->bytemap_range = prog->bytemap_range();
        return normalizedRegex;
    }

    void Regexp::Derivatives::computeNewState(re2::Regexp *regexp, const uint8_t *bytemap, int bytemapRange,
                                              const std::string &compositionStrToConcat) {
        // Used for searching in unordered_map and unordered_set
        std::unordered_map<std::string, unsigned int>::iterator regexNumberMapFound;
        std::unordered_set<std::string>::iterator foundSet;
        re2::Regexp *operand1, *operand2;
        Derivatives::equationTypes equationType;
        std::string regexpString = regexp->ToString();
        if (regexpString.empty()) {
            return;
        }
        caState currentState;
        re2::Regexp *currentStateRegexp;
        caState newState = {this->caStates.size(), {}};
        this->regexNumberMapping.insert({regexpString, this->caStates.size()});
        this->caStates.push_back(newState);
        if (this->caStates.size() > this->existingPartialDerivatives.size()) {
            this->existingPartialDerivatives.resize(this->caStates.size() + 50, false);
        }
        // The regex itself is the first state to be processed
        this->caStatesRegex.push_back(regexp);
        this->statesToCompute.push_back(regexp);
        // Compute derivatives for all states that occurred in previously computed derivatives
        while (!this->statesToCompute.empty()) {
            currentStateRegexp = this->statesToCompute.back();
            this->discoveredStates.insert(currentStateRegexp->ToString());
            this->statesToCompute.pop_back();
            // Get the type of equations that will be used and the operands of that equation
            equationType = this->getEquationTypeAndOperands(currentStateRegexp, operand1, operand2);
            // There is no need to process the epsilon equation, it represents an empty match
            if (equationType == Derivatives::epsilon) {
                continue;
            }
            // The state must be processed wrt all bytemaps
            for (int bytemapGroup = 0; bytemapGroup < bytemapRange; bytemapGroup++) {
                switch (equationType) {
                    case Derivatives::concatenation: {
                        // The ordinal number of the first operand will be used as an index in bytemap array to get the number of the bytemap group
                        unsigned char firstOperandChar;
                        bool negated = false;
                        std::unordered_set<int> bytemapGroupsForCharClasses;
                        // For charClass the char is saved differently
                        if (operand1->op() == kRegexpCharClass) {
                            CharClass *cc = operand1->cc();
                            CharClass::iterator it = operand1->cc()->begin();
                            RuneRange rr = *it;
                            firstOperandChar = rr.lo;
                            std::string operand1String = operand1->ToString();
                            // Negation - if char class is negated, the the second char must be ^ (first is opening bracket)
                            if (operand1String.length() >= 2 && operand1String[1] == '^') {
                                negated = true;
                                // Create negation of the Char class. Then, when getting all bytemapGroups, it will obtain groups of
                                // the negation; the groups that are not satisfiable for this char class
                                cc = operand1->cc()->Negate();
                            }
                            // Chars in char class can be in more than one bytemapGroup, we must get all of them
                            int max;
                            for (auto &i: *cc) {
                                // bytemap is an array of size 256, so the last index is 255, but i->hi can be up to Runemax, which
                                // can cause Segmentation fault
                                max = 255;
                                if (i.hi != re2::Runemax) {
                                    max = i.hi;
                                }
                                for (int index = i.lo; index <= max; index++) {
                                    bytemapGroupsForCharClasses.insert(bytemap[index]);
                                }
                            }
                        } else {
                            firstOperandChar = operand1->rune();
                            bytemapGroupsForCharClasses.insert(bytemap[int(firstOperandChar)]);
                        }
                        // This performs the check described in the second equation for conditional derivatives in the paper
                        // To be satisfiable, the checked character must be in the same bytemap group for which the derivatives
                        // are computed. Or if it is a negated character class, the checked character must be in any other group
                        bool satisfiable = false;
                        if (negated &&
                            bytemapGroupsForCharClasses.find(bytemapGroup) == bytemapGroupsForCharClasses.end()) {
                            satisfiable = true;
                        } else if (!negated &&
                                   bytemapGroupsForCharClasses.find(bytemapGroup) !=
                                   bytemapGroupsForCharClasses.end()) {
                            satisfiable = true;
                        }
                        // Save the new state
                        std::string operand2String = operand2->ToString();
                        regexNumberMapFound = this->regexNumberMapping.find(operand2String);
                        unsigned int operand2AsNumber;
                        if (regexNumberMapFound == this->regexNumberMapping.end()) {
                            this->regexNumberMapping.insert({operand2String, this->caStates.size()});
                            if (operand2String.empty()) {
                                this->emptyStateNumber = this->caStates.size();
                            }
                            operand2AsNumber = this->caStates.size();
                            this->caStates.push_back({this->caStates.size(), {}});
                            if (this->caStates.size() > this->existingPartialDerivatives.size()) {
                                this->existingPartialDerivatives.resize(this->caStates.size() + 50, false);
                            }
                            this->caStatesRegex.push_back(operand2);
                        } else {
                            operand2AsNumber = regexNumberMapFound->second;
                        }
                        if (satisfiable) {
                            // Create and try to find the key in already processed states
                            std::string key = currentStateRegexp->ToString();
                            unsigned int keyAsNumber = this->regexNumberMapping.at(key);
                            std::list<Derivatives::counterOperator> op = {{Derivatives::ID, 0, 0, 0}};
                            std::set<Derivatives::counterGuard> grd = {{True, 0, 0, 0, false}};
                            if (operand1->op() == kRegexpAnyChar) {
                                bytemapGroup = 256;
                            }
                            if (!this->existingPartialDerivatives[keyAsNumber]) {
                                // When the key is not found, the current state will be inserted to partial derivatives
                                // Also, the new transition, including the number of the bytemap group, is created and inserted into
                                // a vector of transitions
                                caTransition newTransition({bytemapGroup, operand2AsNumber}, {grd, op});
                                std::vector<caTransition> newTransitionsVector;
                                newTransitionsVector.push_back(newTransition);
                                if (this->isNullable(currentStateRegexp)) {
                                    if (this->finalStates.size() <= keyAsNumber) {
                                        this->finalStates.resize(keyAsNumber + 1, this->unsetFinalStateCondition);
                                    }
                                    this->finalStates[keyAsNumber] = {Derivatives::True, 0, 0, 0, true};
                                }
                                if (keyAsNumber >= this->partialDerivatives.size()) {
                                    this->partialDerivatives.resize(keyAsNumber + 1, {});
                                }
                                this->partialDerivatives[keyAsNumber] = {newTransitionsVector};
                                this->existingPartialDerivatives[keyAsNumber] = true;
                            } else {
                                // When the key already exists, only the vector of transitions will be updated
                                caTransition newTransition = {{bytemapGroup, operand2AsNumber},
                                                              {grd,          op}};
                                this->partialDerivatives[keyAsNumber].push_back(newTransition);
                            }
                        }
                        // If the state wasn't discovered before, it is added to the list of discovered states and the list
                        // of states to compute
                        foundSet = this->discoveredStates.find(operand2->ToString());
                        if (foundSet == this->discoveredStates.end()) {
                            this->statesToCompute.push_back(operand2);
                            this->discoveredStates.insert(operand2->ToString());
                        }
                        break;
                    }
                    case Derivatives::alternation: {
                        caTransition updatedTransition;
                        // Get the key for the whole state and prepare a list of keys that will arise from concatenating each part
                        // of the alternation with the rest of the regexp
                        std::string alternationKey = currentStateRegexp->ToString();
                        std::list<std::string> newConcatKeysFromAlternation;
                        // Each part of the alternation must be processed. The resulting states are a union of the derivatives
                        // of each part of alternation concatenated with the rest of the regexp
                        for (int i = 0; i < operand1->nsub(); i++) {
                            // Create a new regexp that consists of currently processing part of the alternation and the rest of the regexp
                            // When the second operand is an empty match, it is unnecessary to do concatenation
                            if (operand2->op() == kRegexpEmptyMatch) {
                                // When the second operand is an empty match, the result of the concatenation is only the currently processed part of the alternation
                                std::string keyConcat = operand1->sub()[i]->ToString();
                                newConcatKeysFromAlternation.push_back(keyConcat);
                                // If the derivatives of the state weren't computed before, it must be processed
                                if (this->regexNumberMapping.find(keyConcat) == this->regexNumberMapping.end() ||
                                    !this->existingPartialDerivatives[this->regexNumberMapping.at(keyConcat)]) {
                                    this->computeNewState(operand1->sub()[i], bytemap, bytemapRange);
                                }
                            } else {
                                // Create a key for the concatenation of one part of the alternation with the rest of the regexp (i.e., the newly created regexp)
                                auto *newRegexp = new Regexp(kRegexpConcat, regexp->parse_flags());
                                newRegexp->AllocSub(2);
                                Regexp **regexpSub = newRegexp->sub();
                                regexpSub[0] = operand1->sub()[i];
                                regexpSub[1] = operand2;
                                std::string newRegexpString = newRegexp->ToString();
                                newConcatKeysFromAlternation.push_back(newRegexpString);
                                // If the derivatives of the state weren't computed before, it must be processed
                                if (this->regexNumberMapping.find(newRegexpString) == this->regexNumberMapping.end() ||
                                    !this->existingPartialDerivatives[this->regexNumberMapping.at(newRegexpString)]) {
                                    this->computeNewState(newRegexp, bytemap, bytemapRange);
                                }
                            }
                        }
                        std::vector<caTransition> newTransitionsVector;
                        unsigned int alternationKeyInt = this->regexNumberMapping.at(alternationKey);
                        // Derivatives of the alternation equation are a union of states computed for each part of the alternation
                        // concatenated with the rest of the regexp. So all the keys (string representation of concatenated part of the alternation
                        // with the rest of the regexp) must be processed.
                        unsigned int newConcatKeyInt;
                        for (auto const &newConcatKey: newConcatKeysFromAlternation) {
                            if (newConcatKey.empty()) {
                                continue;
                            }
                            newConcatKeyInt = this->regexNumberMapping.at(newConcatKey);
                            if (this->existingPartialDerivatives[newConcatKeyInt]) {
                                // Each key can contain a vector of transitions (including derivatives of that equation), and all of them
                                // must be added to the states (derivative) of the alternation equation
                                for (auto const &transition: this->partialDerivatives[newConcatKeyInt]) {
                                    if (transition.first.first == bytemapGroup) {
                                        // If the key already exists, the states (derivative) for this equation will be extended
                                        // Otherwise, the states are inserted in a new vector of states
                                        updatedTransition = transition;
                                        if (this->existingPartialDerivatives[alternationKeyInt]) {
                                            this->partialDerivatives[alternationKeyInt].push_back(updatedTransition);
                                        } else {
                                            newTransitionsVector.push_back(updatedTransition);
                                        }
                                    }
                                }
                            }
                        }
                        // If the alternation key does not exist in the partial derivatives map, it will be inserted together
                        // with the new vector of the states
                        if (!this->existingPartialDerivatives[alternationKeyInt]) {
                            if (this->isNullable(currentStateRegexp)) {
                                unsigned int alternationKeyNumber = this->regexNumberMapping.at(alternationKey);
                                if (this->finalStates.size() <= alternationKeyNumber) {
                                    this->finalStates.resize(alternationKeyNumber + 1, this->unsetFinalStateCondition);
                                }
                                this->finalStates[alternationKeyNumber] = {Derivatives::True, 0, 0, 0, true};
                            }
                            if (alternationKeyInt >= this->partialDerivatives.size()) {
                                this->partialDerivatives.resize(alternationKeyInt + 1, {});
                            }
                            this->partialDerivatives[alternationKeyInt] = {newTransitionsVector};
                            this->existingPartialDerivatives[alternationKeyInt] = true;
                        }
                        break;
                    }
                    case Derivatives::repetition: {
                        caTransition updatedTransition;
                        unsigned int currentStateInt = this->regexNumberMapping.at(currentStateRegexp->ToString());
                        if (this->existingPartialDerivatives[currentStateInt]) {
                            // Nothing to be done if derivatives for this state are already computed
                            break;
                        }
                        // In the fourth equation in the paper, derivatives of the first and the second operand must be computed
                        std::string firstOperandKey = operand1->sub()[0]->ToString();
                        std::string secondOperandKey = operand2->ToString();
                        if (this->regexNumberMapping.find(firstOperandKey) == this->regexNumberMapping.end() ||
                            !this->existingPartialDerivatives[this->regexNumberMapping.at(firstOperandKey)]) {
                            this->computeNewState(operand1->sub()[0], bytemap, bytemapRange,
                                                  currentStateRegexp->ToString());
                        }
                        if (this->regexNumberMapping.find(secondOperandKey) == this->regexNumberMapping.end() ||
                            !this->existingPartialDerivatives[this->regexNumberMapping.at(secondOperandKey)]) {
                            this->computeNewState(operand2, bytemap, bytemapRange);
                        }
                        unsigned int firstOperandKeyInt = this->regexNumberMapping.at(firstOperandKey);
                        unsigned int secondOperandKeyInt = this->regexNumberMapping.at(secondOperandKey);
                        // One part of the result is derivatives created by a composition of operand1's derivatives with {<ID, currentState>}
                        std::vector<caTransition> newVector;
                        std::list<Derivatives::counterOperator> op = {{Derivatives::ID, 0, 0, 0}};
                        std::set<Derivatives::counterGuard> grd = {{Derivatives::True, 0, 0, 0, false}};
                        newVector = this->composition(currentStateRegexp->ToString(),
                                                      this->partialDerivatives[firstOperandKeyInt], op, grd,
                                                      currentStateRegexp, true);
                        // The second part of the result is operand2's derivatives
                        // But only if the key is not an empty string, empty string means epsilon, derivatives of epsilon is an empty
                        // set
                        if (!secondOperandKey.empty()) {
                            for (auto const &it: this->partialDerivatives[secondOperandKeyInt]) {
                                updatedTransition = it;
                                newVector.push_back(updatedTransition);
                            }
                        }
                        currentStateInt = this->regexNumberMapping.at(currentStateRegexp->ToString());
                        if (this->isNullable(currentStateRegexp)) {
                            if (this->finalStates.size() <= currentStateInt) {
                                this->finalStates.resize(currentStateInt + 1, this->unsetFinalStateCondition);
                            }
                            this->finalStates[currentStateInt] = {Derivatives::True, 0, 0, 0, true};
                        }
                        if (currentStateInt >= this->partialDerivatives.size()) {
                            this->partialDerivatives.resize(currentStateInt + 1, {});
                        }
                        this->partialDerivatives[currentStateInt] = {newVector};
                        this->existingPartialDerivatives[currentStateInt] = true;
                        break;
                    }
                    case Derivatives::countedRepetition: {
                        unsigned int currentStateInt = this->regexNumberMapping.at(currentStateRegexp->ToString());
                        if (this->existingPartialDerivatives[currentStateInt]) {
                            // Nothing to be done if derivatives for this state are already computed
                            break;
                        }
                        // In the fifth equation in the paper, derivatives of the repeated part of the first operand
                        // and the second operand must be computed
                        std::string firstOperandKey = operand1->sub()[0]->ToString();
                        std::string secondOperandKey = operand2->ToString();
                        if (this->regexNumberMapping.find(firstOperandKey) == this->regexNumberMapping.end() ||
                            !this->existingPartialDerivatives[this->regexNumberMapping.at(firstOperandKey)]) {
                            this->computeNewState(operand1->sub()[0], bytemap, bytemapRange,
                                                  currentStateRegexp->ToString());
                        }
                        unsigned int firstOperandKeyInt = this->regexNumberMapping.at(firstOperandKey);
                        // One part of the result is derivatives created by a composition of operand1's (it's repeated part) derivatives with {<INCRx, currentState>}
                        std::vector<caTransition> newVectorFirstPart;
                        std::string currentStateRegexpString = currentStateRegexp->ToString();
                        std::string operand1String = operand1->ToString();
                        std::string regexConcatString = currentStateRegexpString + compositionStrToConcat;
                        // Distinguish between counting loops represented by same strings
                        if (this->countingLoopStringIntMap.find(operand1String) !=
                            this->countingLoopStringIntMap.end()) {
                            unsigned long stateCounterMapCountCurrentRegex = this->stateCounterMap.count(
                                    currentStateRegexpString);
                            unsigned long stateCounterMapCountConcatRegex = this->stateCounterMap.count(
                                    regexConcatString);
                            if (stateCounterMapCountCurrentRegex == 0 && stateCounterMapCountConcatRegex == 0) {
                                int nextLoopNumber = ++this->sameCountingLoopCount.at(operand1String);
                                // Append counter at the end of the counting loop string
                                operand1String += std::to_string(nextLoopNumber);
                                this->countingLoopStringIntMap.insert({operand1String, this->countingLoopCounter});
                                this->countingLoops.insert(this->countingLoopCounter);
                                if (this->countingLoopCounter >= this->countingLoopBounds.size()) {
                                    this->countingLoopBounds.resize(this->countingLoopCounter + 50, {});
                                }
                                this->countingLoopBounds[this->countingLoopCounter] = {operand1->min(),
                                                                                       operand1->max()};
                                this->countingLoopCounter++;
                                this->stateCounterMap.insert({currentStateRegexpString, operand1String});
                                if (!compositionStrToConcat.empty()) {
                                    this->stateCounterMap.insert({regexConcatString, operand1String});
                                }
                            } else if (stateCounterMapCountCurrentRegex == 1) {
                                operand1String = this->stateCounterMap.at(currentStateRegexpString);
                            } else {
                                operand1String = this->stateCounterMap.at(regexConcatString);
                            }
                        } else {
                            // The first occurrence of the counting loop, save
                            this->countingLoopStringIntMap.insert({operand1String, this->countingLoopCounter});
                            this->countingLoops.insert(this->countingLoopCounter);
                            if (this->countingLoopCounter >= this->countingLoopBounds.size()) {
                                this->countingLoopBounds.resize(this->countingLoopCounter + 50, {});
                            }
                            this->countingLoopBounds[this->countingLoopCounter] = {operand1->min(), operand1->max()};
                            this->countingLoopCounter++;
                            this->sameCountingLoopCount.insert({operand1String, 0});
                            this->stateCounterMap.insert({currentStateRegexpString, operand1String});
                            if (!compositionStrToConcat.empty()) {
                                this->stateCounterMap.insert(
                                        {currentStateRegexpString + compositionStrToConcat, operand1String});
                            }
                        }
                        std::list<Derivatives::counterOperator> op = {
                                {Derivatives::INCR, this->countingLoopStringIntMap.at(operand1String), operand1->min(),
                                 operand1->max()}};
                        std::set<Derivatives::counterGuard> grd = {
                                {Derivatives::CanIncr, this->countingLoopStringIntMap.at(operand1String),
                                 operand1->min(), operand1->max(), false}};
                        newVectorFirstPart = this->composition(currentStateRegexp->ToString(),
                                                               this->partialDerivatives[firstOperandKeyInt], op, grd,
                                                               currentStateRegexp, true);

                        std::vector<caTransition> newVectorSecondPart;
                        // If the second operand is epsilon, the result will be empty set so it is not necessary to compute it
                        if (!secondOperandKey.empty()) {
                            if (this->regexNumberMapping.find(secondOperandKey) == this->regexNumberMapping.end() ||
                                !this->existingPartialDerivatives[this->regexNumberMapping.at(secondOperandKey)]) {
                                this->computeNewState(operand2, bytemap, bytemapRange, compositionStrToConcat);
                            }
                            unsigned int secondOperandKeyInt = this->regexNumberMapping.at(secondOperandKey);
                            // Second part of the result is derivatives created by a composition of {<EXITx, epsilon>} with operand2's derivatives
                            op = {{Derivatives::EXIT, this->countingLoopStringIntMap.at(operand1String),
                                   operand1->min(), operand1->max()}};
                            grd = {{Derivatives::CanExit, this->countingLoopStringIntMap.at(operand1String),
                                    operand1->min(), operand1->max(), false}};
                            newVectorSecondPart = this->composition(currentStateRegexp->ToString(),
                                                                    this->partialDerivatives[secondOperandKeyInt], op,
                                                                    grd,
                                                                    new Regexp(kRegexpEmptyMatch,
                                                                               regexp->parse_flags()), false);
                        }

                        // Derivatives of the current state are union of these two and will be combined in the first vector
                        for (auto const &it: newVectorSecondPart) {
                            newVectorFirstPart.push_back(it);
                        }
                        currentStateInt = this->regexNumberMapping.at(currentStateRegexpString);
                        if (this->finalStates.size() <= currentStateInt) {
                            this->finalStates.resize(currentStateInt + 1, this->unsetFinalStateCondition);
                        }
                        if (operand1->op() == kRegexpRepeat && this->isNullable(operand2)) {
                            this->finalStates[currentStateInt] = {Derivatives::CanExit,
                                                                  this->countingLoopStringIntMap.at(operand1String),
                                                                  operand1->min(), operand1->max(), true};
                        } else if (this->isNullable(currentStateRegexp)) {
                            this->finalStates[currentStateInt] = {Derivatives::True, 0, 0, 0, true};
                        }
                        if (currentStateInt >= this->partialDerivatives.size()) {
                            this->partialDerivatives.resize(currentStateInt + 1, {});
                        }
                        this->partialDerivatives[currentStateInt] = {newVectorFirstPart};
                        this->existingPartialDerivatives[currentStateInt] = true;
                        break;
                    }
                    case Derivatives::epsilon:
                        break;
                }
            }
        }
    }

    std::vector<Regexp::Derivatives::caTransition>
    Regexp::Derivatives::composition(
            const std::string &sourceState,
            const std::vector<caTransition> &transitionsVector,
            const std::list<Derivatives::counterOperator> &operatorForComposition,
            const std::set<Derivatives::counterGuard> &operatorForCompositionGuards,
            re2::Regexp *regexpForComposition,
            bool statesVectorFirst) {
        std::vector<caTransition> newVector;
        caState newState;
        re2::Regexp *state;
        int numberOfAllSubs;
        int numberOfStateSubs;
        int numberOfCompositionRegexpSubs = regexpForComposition->nsub();
        std::unordered_set<std::string>::iterator foundSet;
        // A literal and literal string has zero number of subs, but we will have this expression as one sub of the concatenation
        // If the regexp is EmptyMatch, we do not need to concatenate it - "something" concatenated with empty much is still "something"
        if (numberOfCompositionRegexpSubs == 0 && regexpForComposition->op() != kRegexpEmptyMatch) {
            numberOfCompositionRegexpSubs++;
        }
        std::list<Derivatives::counterOperator> operatorCompositionResult;
        std::set<Derivatives::counterGuard> guardCompositionResult;
        std::pair<std::list<Regexp::Derivatives::counterOperator>, std::set<Derivatives::counterGuard>> compositionResult;
        // Composition is done for all target state of the transitions. The composition adds a new operator and it concatenates
        // the states
        for (auto const &it: transitionsVector) {
            // The new state will also have a new operator
            // The resulting operator is dependent on the order of input operators
            if (statesVectorFirst) {
                compositionResult = re2::Regexp::Derivatives::getOperatorComposition(it.second.second, it.second.first,
                                                                                     operatorForComposition,
                                                                                     operatorForCompositionGuards);
            } else {
                compositionResult = re2::Regexp::Derivatives::getOperatorComposition(operatorForComposition,
                                                                                     operatorForCompositionGuards,
                                                                                     it.second.second, it.second.first);
            }
            operatorCompositionResult = compositionResult.first;
            guardCompositionResult = compositionResult.second;
            if (!operatorCompositionResult.empty()) {
                caState targetState = this->caStates[it.first.second];
                state = this->caStatesRegex[targetState.first];
                numberOfStateSubs = state->nsub();
                // A literal and literal string has zero number of subs, but we will have this expression as one sub of the concatenation
                // If the regexp is EmptyMatch, we do not need to concatenate it - "something" concatenated with empty much is still "something"
                if (numberOfStateSubs == 0 && state->op() != kRegexpEmptyMatch) {
                    numberOfStateSubs++;
                }
                numberOfAllSubs = numberOfStateSubs + numberOfCompositionRegexpSubs;
                // Create a new regexp that will represent the concatenation of the two regexes
                auto *concatRegexp = new Regexp(kRegexpConcat, state->parse_flags());
                concatRegexp->AllocSub(numberOfAllSubs);
                Regexp **concat = concatRegexp->sub();
                // If the state or the regexpForComposition has only one sub, we do not want to copy sub()[i]. This would
                // copy only part of the regex, in that case, we want to copy the whole regex
                if (numberOfStateSubs == 1) {
                    concat[0] = state;
                } else {
                    for (int i = 0; i < numberOfStateSubs; i++) {
                        concat[i] = state->sub()[i];
                    }
                }
                if (numberOfCompositionRegexpSubs == 1) {
                    concat[numberOfStateSubs] = regexpForComposition;
                } else {
                    for (int i = 0; i < numberOfCompositionRegexpSubs; i++) {
                        concat[i + numberOfStateSubs] = regexpForComposition->sub()[i];
                    }
                }
                // Save the new state
                std::string concatRegexpString = concatRegexp->ToString();
                if (this->regexNumberMapping.find(concatRegexpString) == this->regexNumberMapping.end()) {
                    this->regexNumberMapping.insert({concatRegexpString, this->caStates.size()});
                    if (concatRegexpString.empty()) {
                        this->emptyStateNumber = this->caStates.size();
                    }
                    this->caStates.push_back({this->caStates.size(), {}});
                    if (this->caStates.size() > this->existingPartialDerivatives.size()) {
                        this->existingPartialDerivatives.resize(this->caStates.size() + 50, false);
                    }
                    this->caStatesRegex.push_back(concatRegexp);
                }
                caTransition newTransition({it.first.first, this->regexNumberMapping.at(concatRegexp->ToString())},
                                           {guardCompositionResult, operatorCompositionResult});
                newVector.push_back(newTransition);
                // If the state wasn't discovered before, it is added to the list of discovered states and the list
                // of states to compute
                foundSet = this->discoveredStates.find(concatRegexp->ToString());
                if (foundSet == this->discoveredStates.end()) {
                    this->statesToCompute.push_back(concatRegexp);
                    this->discoveredStates.insert(concatRegexp->ToString());
                }
            }
        }
        return newVector;
    }

    std::pair<std::list<Regexp::Derivatives::counterOperator>, std::set<Regexp::Derivatives::counterGuard>>
    Regexp::Derivatives::getOperatorComposition(std::list<Derivatives::counterOperator> firstOperator,
                                                std::set<Derivatives::counterGuard> firstOperatorGuards,
                                                std::list<Derivatives::counterOperator> secondOperator,
                                                std::set<Derivatives::counterGuard> secondOperatorGuards) {
        Derivatives::counterOperator firstToCheck{}, secondToCheck{};
        unsigned long long firstOperatorSize, secondOperatorSize;
        // It is enough to check only the last two consecutive operators as the others were checked before (when they were
        // the last two consecutive operators)
        firstToCheck = firstOperator.back();
        secondToCheck = secondOperator.front();
        firstOperatorSize = firstOperator.size();
        secondOperatorSize = secondOperator.size();
        // There are some special cases when working with the same counting loop or when at least one of the operators is ID
        if ((firstToCheck.countingLoop == secondToCheck.countingLoop) || firstToCheck.op == Derivatives::ID ||
            secondToCheck.op == Derivatives::ID) {
            Derivatives::counterOperator resultOp{};
            bool wasResultOpSet = false;
            // Special cases based on the paper
            if (firstToCheck.op == Derivatives::ID && secondToCheck.op == Derivatives::INCR) {
                resultOp = secondToCheck;
                wasResultOpSet = true;
            } else if (firstToCheck.op == Derivatives::EXIT && secondToCheck.op == Derivatives::INCR) {
                Derivatives::counterOperator exit1 = {Derivatives::EXIT1, firstToCheck.countingLoop,
                                                      firstToCheck.counting_min, firstToCheck.counting_max};
                resultOp = exit1;
                wasResultOpSet = true;
            } else if (firstToCheck.op == Derivatives::EXIT && secondToCheck.op == Derivatives::ID) {
                resultOp = firstToCheck;
                wasResultOpSet = true;
            } else if (firstToCheck.op == Derivatives::ID && secondToCheck.op == Derivatives::ID) {
                // We do not have more information about the ID operator (such as counting loop and min/max) so it does not
                // matter if we use first or second operator, they are the same
                resultOp = firstToCheck;
                wasResultOpSet = true;
            } else if (firstToCheck.op == Derivatives::EXIT && secondToCheck.op == Derivatives::EXIT) {
                if (firstToCheck.counting_min == secondToCheck.counting_min && firstToCheck.counting_min == 0) {
                    // The operators are the same, it does not matter which one we use
                    resultOp = firstToCheck;
                    wasResultOpSet = true;
                } else {
                    return {{},
                            {}};
                }
            }
            // There will be one result operator only when the two checked operators matched one of the special cases
            if (wasResultOpSet) {
                if (firstOperatorSize >= secondOperatorSize) {
                    firstOperatorGuards.erase(re2::Regexp::Derivatives::getGuardForOperator(firstToCheck));
                    firstOperatorGuards.insert(re2::Regexp::Derivatives::getGuardForOperator(resultOp));
                    firstOperator.pop_back();
                    firstOperator.push_back(resultOp);
                    return {firstOperator, firstOperatorGuards};
                } else {
                    secondOperatorGuards.erase(re2::Regexp::Derivatives::getGuardForOperator(secondToCheck));
                    secondOperatorGuards.insert(re2::Regexp::Derivatives::getGuardForOperator(resultOp));
                    secondOperator.pop_front();
                    secondOperator.push_front(resultOp);
                    return {secondOperator, secondOperatorGuards};
                }
            }
        }
        // When both counter operators are EXIT and the minimum of the second counting loop is bigger than 0, the result is
        // undefined because it can not be exited without iterating it at least once
        if (firstToCheck.op == Derivatives::EXIT && secondToCheck.op == Derivatives::EXIT &&
            secondToCheck.counting_min != 0) {
            return {{},
                    {}};
        }
        if (firstOperatorSize >= secondOperatorSize) {
            firstOperatorGuards.insert(re2::Regexp::Derivatives::getGuardForOperator(secondToCheck));
            firstOperator.push_back(secondToCheck);
            return {firstOperator, firstOperatorGuards};
        } else {
            secondOperatorGuards.insert(re2::Regexp::Derivatives::getGuardForOperator(firstToCheck));
            secondOperator.push_front(firstToCheck);
            return {secondOperator, secondOperatorGuards};
        }
        return {{},
                {}};
    }

    Regexp::Derivatives::counterGuard
    Regexp::Derivatives::getGuardForOperator(const Regexp::Derivatives::counterOperator &op) {
        switch (op.op) {
            case Derivatives::ID:
                return {Derivatives::True, op.countingLoop, op.counting_min, op.counting_max, false};
                break;
            case Derivatives::INCR:
                return {Derivatives::CanIncr, op.countingLoop, op.counting_min, op.counting_max, false};
                break;
            case Derivatives::EXIT:
            case Derivatives::EXIT1:
                return {Derivatives::CanExit, op.countingLoop, op.counting_min, op.counting_max, false};
                break;
        }
        return {};
    }

        // find all counters referenced in transition
    std::string getTransitionCounters(const Regexp::Derivatives::caTransition &trans){
        std::set<unsigned> counters{};
        for (auto &grd : trans.second.first){
            if (grd.countingLoop != 0 && counters.find(grd.countingLoop) == counters.end()) {
                counters.insert(grd.countingLoop);
            }
            
        }
        std::string result = "";
        for (unsigned counter : counters) {
            result = result + std::to_string(counter) + ",";  
        }
        return result;
    }

    void Regexp::Derivatives::printToDOT1(std::ostream &outputStream) const {
        std::vector<std::string> numberToRegex(this->regexNumberMapping.size());
        for (const auto & pair : this->regexNumberMapping) {
            numberToRegex[pair.second] = pair.first;
        }
        outputStream << "digraph countingAutomaton {" << std::endl;
        outputStream << "node [shape=circle]" << std::endl;
        std::vector<unsigned> statesToProcess{0};
        std::vector<unsigned> processedStates{};
        
        while (!statesToProcess.empty()){
            unsigned cur = statesToProcess.back();
            statesToProcess.pop_back();
            processedStates.push_back(cur);
            for (const auto &trans : this->partialDerivatives[cur]){
                if (!std::count(processedStates.begin(), processedStates.end(), trans.first.second)
                    && !std::count(statesToProcess.begin(), statesToProcess.end(), trans.first.second)) {
                    statesToProcess.push_back(trans.first.second);
                }
                outputStream << "\"" << numberToRegex[cur] << "\""
                            << " -> "
                            << "\"" << numberToRegex[trans.first.second] << "\""
                            << " [label=\""  << trans.first.first
                            << "|"  << getTransitionCounters(trans) << "\"]\n";
            }
        }

        // states that can be potencialy final, based on their guard
        for (auto state : processedStates) {
            if (this->finalStates[state].isSet) {
                outputStream << "\"" << numberToRegex[state] << "\"[shape=doublecircle]\n";
            }
        }
        outputStream << "}" << std::endl;
    }

    std::string Regexp::Derivatives::transitionGrdsAndOpsToString(const CaTransition &trans) const {
        std::string str = "";
        for (auto &grd : std::get<2>(trans)) {
            switch (grd.grd)
            {
            case re2::Regexp::Derivatives::counterGuardEnum::True:
                str = str + "T";
                break;
            case re2::Regexp::Derivatives::counterGuardEnum::CanIncr:
                str = str + "CanInc";
                break;
            case re2::Regexp::Derivatives::counterGuardEnum::CanExit:
                str = str + "CanExit";
                break;
            case re2::Regexp::Derivatives::counterGuardEnum::False:
                str = str + "F";
                break;
            
            }
            str = str + " c:" + std::to_string(grd.countingLoop) + ", ";
        }
        str = str + "/";
        for (auto &op : std::get<3>(trans)) {
            switch (op.op)
            {
            case re2::Regexp::Derivatives::counterOperatorEnum::ID:
                str = str + "ID";
                break;
            case re2::Regexp::Derivatives::counterOperatorEnum::INCR:
                str = str + "Inc";
                break;
            case re2::Regexp::Derivatives::counterOperatorEnum::EXIT:
                str = str + "Exit";
                break;
            case re2::Regexp::Derivatives::counterOperatorEnum::EXIT1:
                str = str + "Exit1";
                break;
            }
            str = str + " c:" + std::to_string(op.countingLoop) + ", ";
        }
        return str;
    }


    void Regexp::Derivatives::printToDOT2(std::ostream &outputStream) const {
        outputStream << "digraph countingAutomaton {" << std::endl;
        outputStream << "node [shape=circle]" << std::endl;
        std::vector<unsigned> statesToProcess{0};
        std::vector<unsigned> processedStates{};
        
        while (!statesToProcess.empty()){
            unsigned cur = statesToProcess.back();
            statesToProcess.pop_back();
            processedStates.push_back(cur);
            for (const auto &trans : this->transitions[cur]){
                if (!std::count(processedStates.begin(), processedStates.end(), std::get<1>(trans))
                    && !std::count(statesToProcess.begin(), statesToProcess.end(), std::get<1>(trans))) {
                    statesToProcess.push_back(std::get<1>(trans));
                }
                outputStream << "\"" << cur << "\""
                            << " -> "
                            << "\"" << std::get<1>(trans) << "\""
                            << " [label=\""  << std::get<0>(trans)
                            << "|" << transitionGrdsAndOpsToString(trans) << "\"]\n";
            }
        }

        outputStream << "}" << std::endl;
    }


    void Regexp::Derivatives::removeUnreachableStates() {
        std::vector<unsigned> statesToProcess{0}; // starting with intial state
        std::vector<unsigned> processedStates{};
        this->transitions.resize(this->partialDerivatives.size());
        while (!statesToProcess.empty()) {
            unsigned cur = statesToProcess.back();
            statesToProcess.pop_back();
            processedStates.push_back(cur);
            for (auto &trans : this->partialDerivatives[cur]) {
                if (!std::count(statesToProcess.begin(), statesToProcess.end(), trans.first.second)
                    && !std::count(processedStates.begin(), processedStates.end(), trans.first.second)
                ) {
                    statesToProcess.push_back(trans.first.second);
                }
                this->transitions[cur].push_back(std::make_tuple(trans.first.first, trans.first.second, trans.second.first, trans.second.second));
            }
        }
    }

    void Regexp::Derivatives::rewriteToFlattenedRightAssociativeForm(re2::Regexp *&regexp) {
        // We want to rewrite all capture groups (if the regexp is (((a))) we want to rewrite it to a)
        while (true) {
            // The first case is when the type is kRegexpCapture
            if (regexp->op() == kRegexpCapture) {
                regexp = regexp->sub()[0]->Incref();
                // The second case is when the type of the regexp is kRegexpStar or kRegexpPlus
                // Then the first subexpression can be kRegexpCapture, and we want to rewrite it
            } else if ((regexp->op() == kRegexpPlus || regexp->op() == kRegexpStar) &&
                       regexp->sub()[0]->op() == kRegexpCapture) {
                regexp->sub()[0] = regexp->sub()[0]->sub()[0]->Incref();
            } else {
                return;
            }
        }
    }

    Regexp::Derivatives::equationTypes
    Regexp::Derivatives::getEquationTypeAndOperands(re2::Regexp *regexp, Regexp *&operand1, Regexp *&operand2) {
        switch (regexp->op()) {
            default:
                std::cerr << "USAGE OF NOT IMPLEMENTED OPERAND " << regexp->op() << std::endl;
                exit(EXIT_FAILURE);
            case kRegexpNoMatch:
            case kRegexpEmptyMatch:
                // The empty match and no match will be interpreted as the epsilon equation with epsilon as operands
                operand1 = new Regexp(kRegexpEmptyMatch, regexp->parse_flags());
                operand2 = new Regexp(kRegexpEmptyMatch, regexp->parse_flags());
                return Derivatives::epsilon;
            case kRegexpLiteral:
                // A literal is a single character, so it is a concatenation of the single character and the epsilon
                operand1 = regexp;
                operand2 = new Regexp(kRegexpEmptyMatch, regexp->parse_flags());
                return Derivatives::concatenation;
            case kRegexpLiteralString:
                // A literal string is a normal string (abcdef, for example). In terms of equations from the paper,
                // it is a concatenation of the first character and the rest of the string.
                operand1 = re2::Regexp::FirstLiteralFromLiteralString(regexp->runes(), regexp->parse_flags());
                operand2 = re2::Regexp::RestOfLiteralsFromLiteralString(regexp->runes(), regexp->nrunes() - 1,
                                                                        regexp->parse_flags());
                return Derivatives::concatenation;
            case kRegexpConcat:
                switch (regexp->sub()[0]->op()) {
                    case kRegexpNoMatch:
                    case kRegexpEmptyMatch: {
                        // The concatenation of an empty match and "something" will become just "something"
                        // Do not modify the original regexp; create a new one
                        auto **concat = new Regexp *[regexp->nsub() - 1];
                        for (int i = 1; i < regexp->nsub(); i++) {
                            concat[i - 1] = regexp->sub()[i]->Incref();
                        }
                        re2::Regexp *concatRegexp = re2::Regexp::Concat(concat, regexp->nsub() - 1,
                                                                        regexp->parse_flags());
                        // Process the rest of the regexp
                        return this->getEquationTypeAndOperands(concatRegexp, operand1, operand2);
                    }
                    case kRegexpLiteral: {
                        // If the first subexpression of a concatenation is Literal, it will be the first operand
                        operand1 = regexp->sub()[0]->Incref();
                        // Create a new regexp without the first node
                        // Do not modify the original regexp; create a new one
                        auto **concat = new Regexp *[regexp->nsub() - 1];
                        for (int i = 1; i < regexp->nsub(); i++) {
                            concat[i - 1] = regexp->sub()[i]->Incref();
                        }
                        re2::Regexp *concatRegexp = re2::Regexp::Concat(concat, regexp->nsub() - 1,
                                                                        regexp->parse_flags());
                        operand2 = concatRegexp;
                        return Derivatives::concatenation;
                    }
                    case kRegexpLiteralString: {
                        // Regexp string is a concatenation of chars; the first operand will be the first char from the string
                        operand1 = re2::Regexp::FirstLiteralFromLiteralString(regexp->sub()[0]->runes(),
                                                                              regexp->parse_flags());
                        // For the second operand, a new subexpression without the first char must be created
                        // but the original regexp should not be modified; it is used in functions that call getEquationTypeAndOperands()
                        // So new regexp will be created (it will be a copy of the original regexp), and the update will be done in the newly created regexp
                        auto **concat = new Regexp *[regexp->nsub()];
                        concat[0] = re2::Regexp::RestOfLiteralsFromLiteralString(regexp->sub()[0]->runes(),
                                                                                 regexp->sub()[0]->nrunes() - 1,
                                                                                 regexp->parse_flags());
                        for (int i = 1; i < regexp->nsub(); i++) {
                            concat[i] = regexp->sub()[i]->Incref();
                        }
                        re2::Regexp *concatRegexp = re2::Regexp::Concat(concat, regexp->nsub(), regexp->parse_flags());
                        operand2 = concatRegexp;
                        return Derivatives::concatenation;
                    }
                    case kRegexpConcat: {
                        // In case that regex was flattened, the structure could be a little bit different
                        // For regex like (aa{1,3}b)a{1,4} before flattening it is concatenation of
                        // capture (aa{1,3}b) and repeat a{1,4}, after flattening the regex will be
                        // aa{1,3}ba{1,4} and it is concatenation of two nodes aa{1,3}b and a{1,4}
                        // where the type of the first node is also kRegexpConcat
                        // To sum this up kRegexpConcat with the first node of type kRegexpCapture will become
                        // kRegexpConcat where the first node can have any type, so the first node must be
                        // processed as a "stand-alone" regexp, but all remaining nodes must be preserved
                        Derivatives::equationTypes equationType;
                        // Process the first node as a "stand-alone" regexp
                        equationType = this->getEquationTypeAndOperands(regexp->sub()[0], operand1, operand2);
                        // There are two different situations to handle - if RemoveFirstFromConcat or RestOfLiteralsFromLiteralString was used in
                        // getEquationTypeAndOperands function call above
                        if (regexp->sub()[0]->sub()[0]->op() != kRegexpLiteralString) {
                            // The original regexp can not be modified because it is used in functions that call getEquationType()
                            // Copy of the original regexp will be created - the changes will be done in this copy
                            auto *concatRegexp = new Regexp(kRegexpConcat, regexp->parse_flags());
                            concatRegexp->AllocSub(regexp->nsub());
                            Regexp **concat = concatRegexp->sub();
                            for (int i = 0; i < regexp->nsub(); i++) {
                                concat[i] = regexp->sub()[i]->Incref();
                            }
                            // Only the information about the first node (regexp->sub[0]) must be passed to the function,
                            // so only the first node gets processed, and the rest of the nodes remain unchanged
                            // When the equation type is concatenation, and the subexpression of the subexpression has type kRegexpStar,
                            // it was created from the plus operator; then nothing can be deleted from regex (which will become the second operand)
                            // because the first operand is not taken from it (it is a newly created node). The second operand is
                            // already updated and correct. (Example: a+ will become aa* - the first operand will be a, the second will be a+)
                            if (equationType != Derivatives::concatenation ||
                                regexp->sub()[0]->sub()[0]->op() != kRegexpStar) {
                                // If the first subexpression has nsub == 1, the RemoveFirstFromConcat return NULL, in other words
                                // we just want to delete this subexpression. In that case, the RemoveFirstFromConcat can not be used
                                // since the sub[0] would become NULL causing Segmentation Fault when working with it
                                if (concatRegexp->sub()[0]->nsub() == 1) {
                                    concatRegexp = new Regexp(kRegexpConcat, regexp->parse_flags());
                                    concatRegexp->AllocSub(regexp->nsub() - 1);
                                    concat = concatRegexp->sub();
                                    for (int i = 1; i < regexp->nsub(); i++) {
                                        concat[i - 1] = regexp->sub()[i]->Incref();
                                    }
                                } else {
                                    concatRegexp->sub()[0] = re2::Regexp::RemoveFirstFromConcat(
                                            concatRegexp->sub()[0]->sub(),
                                            concatRegexp->sub()[0]->nsub() - 1,
                                            concatRegexp->parse_flags(), false);
                                }
                            }
                            // The first operand is set correctly from the getEquationTypeAndOperands function, but the second operand is not
                            // The second operand is set only for the first node
                            // So after deleting the first node in the line above, the whole regexp becomes the second operand
                            operand2 = concatRegexp;
                        } else if (regexp->sub()[0]->sub()[0]->op() == kRegexpLiteralString) {
                            // The original regexp can not be modified because it is used in functions that call getEquationType()
                            // Copy of the original regexp will be created - the changes will be done in this copy
                            // Creating a copy here is a little bit more complicated than in the previous case.
                            // First, a new regexp for the original regexp will be prepared
                            auto *concatRegexp = new Regexp(kRegexpConcat, regexp->parse_flags());
                            concatRegexp->AllocSub(regexp->nsub());
                            Regexp **concat = concatRegexp->sub();
                            // Second, a new regexp for the first subexpression for the original regexp will be prepared
                            auto *firstSubexprRegexp = new Regexp(kRegexpConcat, regexp->parse_flags());
                            firstSubexprRegexp->AllocSub(regexp->sub()[0]->nsub());
                            Regexp **firstSubexpr = firstSubexprRegexp->sub();

                            // Because the first subexpression of the first subexpression (of type kRegexpLiteralString)
                            // will be modified, a new copy of it must be created
                            auto *newLiteralStringRegexp = new Regexp(kRegexpLiteralString, regexp->parse_flags());
                            newLiteralStringRegexp = re2::Regexp::LiteralString(regexp->sub()[0]->sub()[0]->runes(),
                                                                                regexp->sub()[0]->sub()[0]->nrunes(),
                                                                                regexp->parse_flags());

                            // Copy the newly created literal string to the prepared first subexpression regexp
                            firstSubexpr[0] = newLiteralStringRegexp;

                            // Copy the rest of the original first subexpression
                            for (int i = 1; i < regexp->sub()[0]->nsub(); i++) {
                                firstSubexpr[i] = regexp->sub()[0]->sub()[i]->Incref();
                            }

                            // Copy the newly created first subexpression to the prepared copy of the regexp
                            concat[0] = firstSubexprRegexp;

                            // Then copy the rest of the original regexp
                            for (int i = 1; i < regexp->nsub(); i++) {
                                concat[i] = regexp->sub()[i]->Incref();
                            }
                            // Because the original regexp is not modified in getEquationTypeAndOperands() call above, the modification
                            // must be done here. For kRegexpLiteral, the first char must be deleted (it is the first operand)
                            // Do it in a copy of the original regexp so that it won't be modified.
                            // The first subexpression of the first subexpression is newLiteralStringRegexp created above, so it
                            // is a copy and can be modified
                            concatRegexp->sub()[0]->sub()[0] = re2::Regexp::RestOfLiteralsFromLiteralString(
                                    regexp->sub()[0]->sub()[0]->runes(),
                                    regexp->sub()[0]->sub()[0]->nrunes() - 1,
                                    regexp->parse_flags());
                            operand2 = concatRegexp;
                        }
                        return equationType;
                    }
                    case kRegexpAlternate: {
                        // Take the Alternate node as the first operand
                        operand1 = regexp->sub()[0]->Incref();
                        // Create new subexpression without the first node (Alternate node)
                        // Do not modify the original regexp; create a new one
                        auto **concat = new Regexp *[regexp->nsub() - 1];
                        for (int i = 1; i < regexp->nsub(); i++) {
                            concat[i - 1] = regexp->sub()[i]->Incref();
                        }
                        re2::Regexp *concatRegexp = re2::Regexp::Concat(concat, regexp->nsub() - 1,
                                                                        regexp->parse_flags());
                        operand2 = concatRegexp;
                        return Derivatives::alternation;
                    }
                    case kRegexpStar: {
                        // Take the Star node as the first operand, delete capture group if
                        // needed (in subexpression of * - i.e., (a) in (a)*)
                        this->rewriteToFlattenedRightAssociativeForm(regexp->sub()[0]->sub()[0]);
                        operand1 = regexp->sub()[0];
                        // Create new subexpression without the first node (Star node)
                        // Do not modify the original regexp; create a new one
                        auto **concat = new Regexp *[regexp->nsub() - 1];
                        for (int i = 1; i < regexp->nsub(); i++) {
                            concat[i - 1] = regexp->sub()[i]->Incref();
                        }
                        re2::Regexp *concatRegexp = re2::Regexp::Concat(concat, regexp->nsub() - 1,
                                                                        regexp->parse_flags());
                        operand2 = concatRegexp;
                        return Derivatives::repetition;
                    }
                    case kRegexpRepeat: {
                        // Take the first node (Repeat node) as the first operand
                        operand1 = regexp->sub()[0]->Incref();
                        // Create new subexpression without the first node (Repeat node)
                        // Do not modify the original regexp; create a new one
                        auto **concat = new Regexp *[regexp->nsub() - 1];
                        for (int i = 1; i < regexp->nsub(); i++) {
                            concat[i - 1] = regexp->sub()[i]->Incref();
                        }
                        re2::Regexp *concatRegexp = re2::Regexp::Concat(concat, regexp->nsub() - 1,
                                                                        regexp->parse_flags());
                        operand2 = concatRegexp;
                        return Derivatives::countedRepetition;
                    }
                    case kRegexpCapture:
                        // Capture type is regex in the parentheses, flattening create abcd from (abcd), etc.
                        this->rewriteToFlattenedRightAssociativeForm(regexp->sub()[0]);
                        // Process flattened regexp
                        return getEquationTypeAndOperands(regexp, operand1, operand2);
                    case kRegexpCharClass: {
                        // Take the first subexpression (CharClass node) as the first operand
                        operand1 = regexp->sub()[0]->Incref();
                        // Create new subexpression without the first node (Repeat node)
                        // Do not modify the original regexp; create a new one
                        auto **concat = new Regexp *[regexp->nsub() - 1];
                        for (int i = 1; i < regexp->nsub(); i++) {
                            concat[i - 1] = regexp->sub()[i]->Incref();
                        }
                        re2::Regexp *concatRegexp = re2::Regexp::Concat(concat, regexp->nsub() - 1,
                                                                        regexp->parse_flags());
                        operand2 = concatRegexp;
                        return Derivatives::concatenation;
                    }
                    case kRegexpBeginLine: {
                        // If the first subexpression of a concatenation is kRegexpBeginLine, it will be the first operand
                        operand1 = regexp->sub()[0]->Incref();
                        // Create a new regexp without the first node
                        // Do not modify the original regexp; create a new one
                        auto **concat = new Regexp *[regexp->nsub() - 1];
                        for (int i = 1; i < regexp->nsub(); i++) {
                            concat[i - 1] = regexp->sub()[i]->Incref();
                        }
                        re2::Regexp *concatRegexp = re2::Regexp::Concat(concat, regexp->nsub() - 1,
                                                                        regexp->parse_flags());
                        operand2 = concatRegexp;
                        return Derivatives::concatenation;
                    }
                    case kRegexpEndLine: {
                        // If the first subexpression of a concatenation is kRegexpEndLine, it will be the first operand
                        operand1 = regexp->sub()[0]->Incref();
                        // Create a new regexp without the first node
                        // Do not modify the original regexp; create a new one
                        auto **concat = new Regexp *[regexp->nsub() - 1];
                        for (int i = 1; i < regexp->nsub(); i++) {
                            concat[i - 1] = regexp->sub()[i]->Incref();
                        }
                        re2::Regexp *concatRegexp = re2::Regexp::Concat(concat, regexp->nsub() - 1,
                                                                        regexp->parse_flags());
                        operand2 = concatRegexp;
                        return Derivatives::concatenation;
                    }
                    case kRegexpBeginText: {
                        // If the first subexpression of a concatenation is kRegexpBeginText, it will be the first operand
                        operand1 = regexp->sub()[0]->Incref();
                        // Create a new regexp without the first node
                        // Do not modify the original regexp; create a new one
                        auto **concat = new Regexp *[regexp->nsub() - 1];
                        for (int i = 1; i < regexp->nsub(); i++) {
                            concat[i - 1] = regexp->sub()[i]->Incref();
                        }
                        re2::Regexp *concatRegexp = re2::Regexp::Concat(concat, regexp->nsub() - 1,
                                                                        regexp->parse_flags());
                        operand2 = concatRegexp;
                        return Derivatives::concatenation;
                    }
                    case kRegexpEndText: {
                        // If the first subexpression of a concatenation is kRegexpEndText, it will be the first operand
                        operand1 = regexp->sub()[0]->Incref();
                        // Create a new regexp without the first node
                        // Do not modify the original regexp; create a new one
                        auto **concat = new Regexp *[regexp->nsub() - 1];
                        for (int i = 1; i < regexp->nsub(); i++) {
                            concat[i - 1] = regexp->sub()[i]->Incref();
                        }
                        re2::Regexp *concatRegexp = re2::Regexp::Concat(concat, regexp->nsub() - 1,
                                                                        regexp->parse_flags());
                        operand2 = concatRegexp;
                        return Derivatives::concatenation;
                    }
                    case kRegexpWordBoundary: {
                        // If the first subexpression of a concatenation is kRegexpWordBoundary, it will be the first operand
                        operand1 = regexp->sub()[0]->Incref();
                        // Create a new regexp without the first node
                        // Do not modify the original regexp; create a new one
                        auto **concat = new Regexp *[regexp->nsub() - 1];
                        for (int i = 1; i < regexp->nsub(); i++) {
                            concat[i - 1] = regexp->sub()[i]->Incref();
                        }
                        re2::Regexp *concatRegexp = re2::Regexp::Concat(concat, regexp->nsub() - 1,
                                                                        regexp->parse_flags());
                        operand2 = concatRegexp;
                        return Derivatives::concatenation;
                    }
                    case kRegexpNoWordBoundary: {
                        // If the first subexpression of a concatenation is kRegexpNoWordBoundary, it will be the first operand
                        operand1 = regexp->sub()[0]->Incref();
                        // Create a new regexp without the first node
                        // Do not modify the original regexp; create a new one
                        auto **concat = new Regexp *[regexp->nsub() - 1];
                        for (int i = 1; i < regexp->nsub(); i++) {
                            concat[i - 1] = regexp->sub()[i]->Incref();
                        }
                        re2::Regexp *concatRegexp = re2::Regexp::Concat(concat, regexp->nsub() - 1,
                                                                        regexp->parse_flags());
                        operand2 = concatRegexp;
                        return Derivatives::concatenation;
                    }
                    case kRegexpAnyChar: {
                        // If the first subexpression of a concatenation is kRegexpAnyChar, it will be the first operand
                        operand1 = regexp->sub()[0]->Incref();
                        // Create a new regexp without the first node
                        // Do not modify the original regexp; create a new one
                        auto **concat = new Regexp *[regexp->nsub() - 1];
                        for (int i = 1; i < regexp->nsub(); i++) {
                            concat[i - 1] = regexp->sub()[i]->Incref();
                        }
                        re2::Regexp *concatRegexp = re2::Regexp::Concat(concat, regexp->nsub() - 1,
                                                                        regexp->parse_flags());
                        operand2 = concatRegexp;
                        return Derivatives::concatenation;
                    }
                    case kRegexpAnyByte: {
                        // If the first subexpression of a concatenation is kRegexpAnyByte, it will be the first operand
                        operand1 = regexp->sub()[0]->Incref();
                        // Create a new regexp without the first node
                        // Do not modify the original regexp; create a new one
                        auto **concat = new Regexp *[regexp->nsub() - 1];
                        for (int i = 1; i < regexp->nsub(); i++) {
                            concat[i - 1] = regexp->sub()[i]->Incref();
                        }
                        re2::Regexp *concatRegexp = re2::Regexp::Concat(concat, regexp->nsub() - 1,
                                                                        regexp->parse_flags());
                        operand2 = concatRegexp;
                        return Derivatives::concatenation;
                    }
                    default:
                        std::cerr << "USAGE OF NOT IMPLEMENTED OPERAND " << regexp->op() << std::endl;
                        exit(EXIT_FAILURE);
                }
            case kRegexpAlternate:
                // Stand-alone Alternate node - the first operand will be the node itself
                operand1 = regexp;
                // There is no second operand, create an empty match (it will be interpreted as epsilon)
                operand2 = new Regexp(kRegexpEmptyMatch, regexp->parse_flags());
                return Derivatives::alternation;
            case kRegexpStar:
                // Stand-alone Star node - the first operand will be the node itself, delete capture group if
                // needed (in subexpression of * - i.e., (a) in (a)*)
                this->rewriteToFlattenedRightAssociativeForm(regexp->sub()[0]);
                operand1 = regexp;
                // There is no second operand, create an empty match (it will be interpreted as epsilon)
                operand2 = new Regexp(kRegexpEmptyMatch, regexp->parse_flags());
                return Derivatives::repetition;
            case kRegexpRepeat:
                // Stand-alone Repeat node - the first operand will be the node itself
                operand1 = regexp;
                // There is no second operand, create an empty match (it will be interpreted as epsilon)
                operand2 = new Regexp(kRegexpEmptyMatch, regexp->parse_flags());
                return Derivatives::countedRepetition;
            case kRegexpCapture:
                // Capture type is regex in the parentheses, flattening create abcd from (abcd), etc.
                this->rewriteToFlattenedRightAssociativeForm(regexp);
                // Process flattened regexp
                return getEquationTypeAndOperands(regexp, operand1, operand2);
            case kRegexpCharClass:
            case kRegexpBeginLine:
            case kRegexpEndLine:
            case kRegexpBeginText:
            case kRegexpEndText:
            case kRegexpWordBoundary:
            case kRegexpNoWordBoundary:
            case kRegexpAnyChar:
            case kRegexpAnyByte:
                // Stand-alone node - the first operand will be the node itself
                operand1 = regexp;
                // There is no second operand, create an empty match (it will be interpreted as epsilon)
                operand2 = new Regexp(kRegexpEmptyMatch, regexp->parse_flags());
                return Derivatives::concatenation;
        }
    }

    re2::Regexp *Regexp::Derivatives::normalizeRegexp(re2::Regexp *&regexp) {
        int numberOfPlusNodes = 0;
        int numberOfnsub;
        re2::RegexpOp regexpOp;
        // We do not want capture groups in the regexp
        this->rewriteToFlattenedRightAssociativeForm(regexp);
        // There could be Quest operator for the whole regex, we want to rewrite such operator too
        // Quest is rewritten to alternation so (abc)? becomes (?:)|abc, it matches zero repetition (epsilon)
        // or one repetition. Such representation of the Quest operator will fit the equations from the paper
        if (regexp->op() == kRegexpQuest) {
            // Create empty regexp
            auto *emptyRegexp = new Regexp(kRegexpEmptyMatch, regexp->parse_flags());
            // Allocate space for two regexes - empty and original without quest operator
            auto **alternate = new Regexp *[2];
            alternate[0] = emptyRegexp;
            this->rewriteToFlattenedRightAssociativeForm(regexp->sub()[0]);
            alternate[1] = regexp->sub()[0]->Incref();
            re2::Regexp *alternateRegexp = AlternateNoFactor(alternate, 2, regexp->parse_flags());
            regexp = alternateRegexp;
        }
        numberOfnsub = regexp->nsub();
        // All the subexpressions will be checked, the number of all plus operators will be counted
        for (int i = 0; i < numberOfnsub; i++) {
            // We do not want capture groups in the regexp
            this->rewriteToFlattenedRightAssociativeForm(regexp->sub()[i]);
            // When the type of the regexp is kRegexpRepeat, and the subexpression is nullable, the minimum of repeat
            // must be changed to zero
            if (regexp->op() == kRegexpRepeat && this->isNullable(regexp->sub()[i])) {
                regexp->min_ = 0;
            } else if (regexp->sub()[i]->op() == kRegexpQuest) {
                auto *emptyRegexp = new Regexp(kRegexpEmptyMatch, regexp->parse_flags());
                auto **alternate = new Regexp *[2];
                alternate[0] = emptyRegexp;
                this->rewriteToFlattenedRightAssociativeForm(regexp->sub()[i]->sub()[0]);
                alternate[1] = regexp->sub()[i]->sub()[0]->Incref();
                re2::Regexp *alternateRegexp = AlternateNoFactor(alternate, 2, regexp->parse_flags());
                regexp->sub()[i] = alternateRegexp;
            }
            // All subexpressions must be checked too
            if (regexp->sub()[i]->nsub() > 1) {
                regexp->sub()[i] = (this->normalizeRegexp(regexp->sub()[i]))->Incref();
                // Capture group in the plus and star operator can be in the first subexpression
            } else if (regexp->sub()[i]->op() == kRegexpPlus) {
                if (regexp->sub()[i]->sub()[0]->nsub() > 1) {
                    regexp->sub()[i]->sub()[0] = (this->normalizeRegexp(regexp->sub()[i]->sub()[0]))->Incref();
                }
                // Count all plus nodes
                numberOfPlusNodes++;
            } else if (regexp->sub()[i]->op() == kRegexpStar) {
                if (regexp->sub()[i]->sub()[0]->nsub() > 1) {
                    regexp->sub()[i]->sub()[0] = (this->normalizeRegexp(regexp->sub()[i]->sub()[0]))->Incref();
                }
            }
        }
        numberOfnsub = regexp->nsub();
        regexpOp = regexp->op();
        // The whole regexp wasn't  checked before, but it must be rewritten as well
        if (numberOfPlusNodes == 0) {
            if (regexp->op() == kRegexpPlus) {
                auto *starConcat = new Regexp(kRegexpConcat, regexp->parse_flags());
                starConcat->AllocSub(2);
                Regexp **starConcatSub = starConcat->sub();
                starConcatSub[0] = regexp->sub()[0]->Incref();
                starConcatSub[1] = re2::Regexp::Star(regexp->sub()[0], regexp->parse_flags());
                regexp->AllocSub(2);
                regexp->Swap(starConcat);
            }
            return regexp;
        }
        re2::Regexp *newRegexp;
        // The type of new regexp will be based on the type of the original regexp
        if (regexpOp == kRegexpAlternate) {
            newRegexp = new Regexp(kRegexpAlternate, regexp->parse_flags());
            // The number of the subexpressions will be the same - only parts of the alternation node could be changed
            newRegexp->AllocSub(numberOfnsub);
        } else {
            newRegexp = new Regexp(kRegexpConcat, regexp->parse_flags());
            // The concatenation node will have more subexpression - for every plus operator, there will be
            // two subexpressions - a+ to aa*
            newRegexp->AllocSub(numberOfnsub + numberOfPlusNodes);
        }
        Regexp **regexpSub = newRegexp->sub();
        int shift = 0;
        for (int i = 0; i < numberOfnsub; i++) {
            // All plus nodes will be rewritten
            if (regexp->sub()[i]->op() == kRegexpPlus) {
                if (regexpOp == kRegexpConcat) {
                    // In case of Concat regexp, a two new subexpressions will be added to regexp
                    regexpSub[i + shift] = regexp->sub()[i]->sub()[0]->Incref();
                    shift++;
                    regexpSub[i + shift] = regexp->sub()[i]->Incref();
                    regexpSub[i + shift]->op_ = kRegexpStar;
                } else {
                    // In the case of alternation regexp a new node that consists of two subexpressions
                    // (for example, a and a*) will be created and added to only one position - one part of
                    // the alternation regexp
                    auto *starConcat = new Regexp(kRegexpConcat, regexp->parse_flags());
                    starConcat->AllocSub(2);
                    Regexp **starConcatSub = starConcat->sub();
                    starConcatSub[0] = regexp->sub()[i]->sub()[0]->Incref();
                    starConcatSub[1] = regexp->sub()[i]->Incref();
                    starConcatSub[1]->op_ = kRegexpStar;
                    regexpSub[i + shift] = starConcat;
                }
            } else {
                // All other nodes will be added as they are
                regexpSub[i + shift] = regexp->sub()[i]->Incref();
            }
        }
        return newRegexp;
    }

    bool Regexp::Derivatives::isNullable(re2::Regexp *regexp) {
        // Star operator, empty match and counted repetition with zero as lower bound are nullable
        if (regexp->op() == kRegexpStar || regexp->op() == kRegexpEmptyMatch ||
            (regexp->op() == kRegexpRepeat && regexp->min_ == 0)) {
            return true;
        } else if (regexp->op() == kRegexpConcat || regexp->op() == kRegexpAlternate) {
            // Check all subexpressions of concat and alternation
            int numberOfSub = regexp->nsub();
            for (int i = 0; i < numberOfSub; i++) {
                this->rewriteToFlattenedRightAssociativeForm(regexp->sub()[i]);
                if (regexp->op() == kRegexpConcat || regexp->op() == kRegexpAlternate) {
                    if (!this->isNullable(regexp->sub()[i])) {
                        return false;
                    }
                    continue;
                }
                if (regexp->sub()[i]->op() != kRegexpStar && regexp->sub()[i]->op() != kRegexpEmptyMatch &&
                    (regexp->op() == kRegexpRepeat && regexp->min_ > 0)) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }
}