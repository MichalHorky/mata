
#include <mata/csa.hh>
#include <mata/re2parser.hh>
#include <re2/ca/derivatives.h>


using namespace Mata;


void Csa::print_ca(){
    std::cout << "hello, world\n";
    std::cout << "bytemap range: " << this->ca.bytemap_range << std::endl;
}

Csa::Csa(const std::string& pattern) {
    ca = Mata::RE2Parser::create_ca(pattern);
    ca.removeUnreachableStates();
    ca.delimitCountingLoops();
}

bool Csa::match(const std::string& text) {
    Csa::Config cur_config({Csa::State(0, {}, {})}, {});
    int cur_bytemap;

    for (unsigned char c : text) {
        cur_bytemap = this->ca.bytemap_array[c];
        std::cout << "char: " << c << " bytemap: " << cur_bytemap << std::endl;
        if (cur_bytemap == 0 || cur_bytemap >= this->ca.bytemap_range) {
            return false;
        }
        cur_config = compute_next_config(cur_config, cur_bytemap);
        if (cur_config.states.empty()) {
            return false;
        }
    }

    // todo: check if final condition holds for any state

    return true;
}


unsigned Csa::get_config_index(Csa::Config &cur_config) {
    std::map<Config, unsigned>::iterator iter = this->config_indexes.find(cur_config);
    if (iter == this->config_indexes.end()) {
        unsigned new_index = this->transition_indexes.size();
        this->config_indexes[cur_config] = new_index;
        this->transition_indexes.push_back(std::vector<int>(this->ca.bytemap_range, -1));
        return new_index;
    }
    return iter->second;
}

Csa::Trans Csa::compute_trans(Config &cur_config, int bytemap) {
    std::vector<CaTrans> always;
    std::vector<std::vector<CaTrans>> conditional;
    std::vector<Guard> guards;
    unsigned index = 0;

    for (auto state : cur_config.states) {
        int can_incr_index = -1;
        int can_exit_index = -1;
        for (auto &trans : this->ca.transitions[state.key]) {
            if (std::get<0>(trans) == bytemap) {
                for (auto &guard : std::get<2>(trans)) {
                    bool found_guard = false;
                    switch(guard.grd) {
                        case CounterGuard::CanIncr:
                            if (can_incr_index == -1) {
                                guards.push_back({state.key, CounterGuard::CanIncr});
                                can_incr_index = index;
                                conditional.push_back({
                                    {
                                    state.key,
                                    std::get<1>(trans),
                                    std::get<3>(trans)
                                    }
                                });
                                index++;
                            } else {
                                conditional[can_incr_index].push_back({
                                    state.key,
                                    std::get<1>(trans),
                                    std::get<3>(trans)
                                });
                            }
                            found_guard = true;
                            break;
                        case CounterGuard::CanExit:
                            if (can_exit_index == -1) {
                                guards.push_back({state.key, CounterGuard::CanExit});
                                can_exit_index = index;
                                conditional.push_back({
                                    {
                                    state.key,
                                    std::get<1>(trans),
                                    std::get<3>(trans)
                                    }
                                });
                                index++;
                            } else {
                                conditional[can_exit_index].push_back({
                                    state.key,
                                    std::get<1>(trans),
                                    std::get<3>(trans)
                                });
                            }
                            found_guard = true;
                            break;
                        default:;
                    }
                    if (!found_guard) {
                        always.push_back({
                            state.key,
                            std::get<1>(trans),
                            std::get<3>(trans)
                        });
                    }
                }
            }
        }
    }
    return {guards, conditional, always, std::vector<int>(1<<guards.size(), -1)};
}

bool Csa::eval_guard(Csa::Config &cur_config, Guard &guard) {
    State state = *std::find(
        cur_config.states.begin(),
        cur_config.states.end(),
        State{guard.state, {}, {}}
    );
    if (guard.condition == CounterGuard::CanIncr) {
        for (unsigned counter_set : state.normal) {
            if (cur_config.counter_sets[counter_set].offset
                - *cur_config.counter_sets[counter_set].list.begin()
                < ca.state_to_counter[state.key].max
            ) {
                return true;
            }
        }
        for (unsigned counter_set : state.plus) {
            if (cur_config.counter_sets[counter_set].offset + 1
                - *cur_config.counter_sets[counter_set].list.begin()
                < ca.state_to_counter[state.key].max
            ) {
                return true;
            }
        }

    } else {
        for (unsigned counter_set : state.normal) {
            if (cur_config.counter_sets[counter_set].offset
                - cur_config.counter_sets[counter_set].list.back()
                >= ca.state_to_counter[state.key].min
            ) {
                return true;
            }
        }
        for (unsigned counter_set : state.plus) {
            if (cur_config.counter_sets[counter_set].offset + 1
                - cur_config.counter_sets[counter_set].list.back()
                >= ca.state_to_counter[state.key].min
            ) {
                return true;
            }
        }
    }
    return false;
}

void Csa::compute_update(Csa::Config &cur_config, std::vector<CaTrans> &active) {
    this->cached_updates.push_back({{}, 0, {}});
    std::vector<std::set<unsigned>> rst1(ca.countingLoopCounter, std::set<unsigned>{});
    // maps indexes of old counter sets to new counter names
    std::set<unsigned> target_states{};
    std::vector<std::set<LValue>> cnt_set_to_lvals(cur_config.counter_sets.size(), std::set<LValue>{});
    for (CaTrans &trans : active) {
        target_states.insert(trans.target);
        StateVec::iterator cur_state = cur_config.states.find(State{trans.origin, std::set<unsigned>{}, std::set<unsigned>{}});
        if (ca.state_to_counter[trans.target].id != 0) {
            for (auto op : trans.operators) {
                switch(op.op) {
                    case CounterOperator::RST1:
                        rst1[ca.state_to_counter[trans.target].id].insert(trans.target);
                        break;
                    case CounterOperator::INCR:
                        for (unsigned i : cur_state->normal) {
                            cnt_set_to_lvals[i].insert(LValue{trans.target, CounterSetOperationInstructions::ADD1});
                        }
                        if (cur_state->plus.size()) {
                            // todo: add custom exception
                            throw std::invalid_argument("double increment");
                        }
                        break;
                    case CounterOperator::ID:
                        for (unsigned i : cur_state->normal) {
                            cnt_set_to_lvals[i].insert(LValue{trans.target, CounterSetOperationInstructions::MOVE});
                        }
                        for (unsigned i : cur_state->plus) {
                            cnt_set_to_lvals[i].insert(LValue{trans.target, CounterSetOperationInstructions::ADD1});
                        }
                    default:
                        break;
                }
            }
        }
    }
    std::set<std::set<unsigned>> sorted;
    for (unsigned i = 0; i < cnt_set_to_lvals.size(); i++) {
        bool all_incremented = true;
        for (const LValue &lval : cnt_set_to_lvals[i]) {
            if (lval.instruction != CounterSetOperationInstructions::INC) {
                all_incremented = false;
                break;
            }
        }
        if (cnt_set_to_lvals.size()) {
            if (all_incremented) {
                this->cached_updates.back()
                    .counter_updates
                    .push_back(CounterSetOperation{CounterSetOperationInstructions::INC, i, 0});
                for (const LValue &lval : cnt_set_to_lvals[i]) {
                    lval.instruction = CounterSetOperationInstructions::MOVE;
                }
            }
            std::set<unsigned> states;
            for (LValue lval : cnt_set_to_lvals[i]) {
                states.insert(lval.state);
            }
            sorted.insert(states);
        }
    }
    for (unsigned i = 1; i < ca.countingLoopCounter; i++) {
        if (rst1[i].size()) {
            sorted.insert(rst1[i]);
        }
    }
    this->cached_updates.back().counters_size = sorted.size();
    std::map<std::set<unsigned>, unsigned> map_to_new_counters;
    auto iter = sorted.begin();
    for (unsigned i = 0; i < sorted.size(); i++) {
        map_to_new_counters[*iter] = i;
    }
    for (unsigned state : target_states) {
        this->cached_updates.back().target_states.insert({state, {}, {}});
    }
    for (unsigned i = 0; i < cnt_set_to_lvals.size(); i++) {
        if (cnt_set_to_lvals[i].size()) {
            std::set<unsigned> key;
            for (const LValue &lval : cnt_set_to_lvals[i]) {
                key.insert(lval.state);
            }
            unsigned target = map_to_new_counters[key];
            for (const LValue &lval : cnt_set_to_lvals[i]) {
                State state = *(this->cached_updates.back().target_states.find(State{lval.state, {}, {}}));
                if (lval.instruction == CounterSetOperationInstructions::MOVE) {
                    state.normal.insert(target);
                } else {
                    state.plus.insert(target);
                }
            }
            this->cached_updates.back().counter_updates.push_back({CounterSetOperationInstructions::MOVE, i, target});
        }
    }
    for (unsigned i = 1; i < ca.countingLoopCounter; i++) {
        if (rst1[i].size()) {
            unsigned target = map_to_new_counters[rst1[i]];
            this->cached_updates.back().counter_updates.push_back({CounterSetOperationInstructions::ADD1, i, target});
            for (unsigned key : rst1[i]) {
                State state = *(this->cached_updates.back().target_states.find(State{key, {}, {}}));
                state.normal.insert(target);
            }

        }
    }
}

Csa::Update &Csa::get_update(Csa::Config &cur_config, Csa::Trans &trans) {
    unsigned index = 0;
    std::vector<CaTrans> active;
    for (CaTrans ca_trans : trans.always) {
        active.push_back(ca_trans);
    }
    for (unsigned i = 0; i < trans.guards.size(); i++) {
        if (eval_guard(cur_config, trans.guards[i])) {
            index = index + 1 << i;
            for (CaTrans ca_trans : trans.guarded[i]) {
                active.push_back(ca_trans);
            }
        }
    }
    if (trans.update_indexes[index] == -1) {
        trans.update_indexes[index] = this->cached_updates.size();
        this->compute_update(cur_config, active);
    }
    return this->cached_updates[trans.update_indexes[index]];
}

Csa::Config &Csa::compute_next_config(Csa::Config &cur_config, int bytemap) {
    unsigned config_index = get_config_index(cur_config);
    int trans_cache_index = this->transition_indexes[config_index][bytemap];
    if (trans_cache_index == -1) {
        trans_cache_index = transitions.size();
        this->transition_indexes[config_index][bytemap] = trans_cache_index;
        this->transitions.push_back(compute_trans(cur_config, bytemap));
    }
    Trans trans = this->transitions[trans_cache_index];
    Update update = get_update(cur_config, trans);
    Config new_config{};
    new_config.states = update.target_states;
    // execute all updates

}
