#ifndef _MATA_CSA_HH_
#define _MATA_CSA_HH_
#include <string>
#include <re2/ca/derivatives.h>
#include <mata/ord_vector.hh>
#include <mata/re2parser.hh>


namespace Mata
{
class Csa {

public:

    Csa(const std::string& pattern);

    using CounterGuard = re2::Regexp::Derivatives::counterGuardEnum;
    using CounterOperator = re2::Regexp::Derivatives::counterOperatorEnum;

    struct State {
        State(unsigned key, std::set<unsigned> normal, std::set<unsigned> plus)
            : key(key), normal(normal), plus(plus) {};
        unsigned key; // state of CA
        std::set<unsigned> normal; // indexes of CounterSets
        std::set<unsigned> plus; // indexes of CounterSets whith postponed increment

        bool operator<(const State &other) const {
            return this->key < other.key;
        }

        bool operator>(const State &other) const {
            return this->key > other.key;
        }

        bool operator==(const State &other) const {
            return this->key == other.key;
        }
    };

    // offset list structure
    struct CounterSet {
        unsigned offset; // offset
        std::list<unsigned> list; 
    };

    using StateVec = std::set<State>;

    struct Config {
        Config() : states(), counter_sets() {};
        Config(StateVec states, std::vector<CounterSet> counter_sets)
            : states(states), counter_sets(counter_sets) {};

        StateVec states;
        std::vector<CounterSet> counter_sets;

        bool operator<(const Config &other) const {
            if (this->states.size() > other.states.size()) {
                return false;
            }
            StateVec::iterator it1(this->states.begin());
            StateVec::iterator it2(other.states.begin());
            while (it1 != this->states.end()) {
                if (it1->key > it2->key
                    || it1->normal > it2->normal
                    || it1->plus > it2->plus
                ) {
                    return false;
                }
                it1++;
                it2++;
            }
            return it2 == other.states.end();
        }

        bool operator==(const Config &other) const {
            if (this->states.size() != other.states.size()) {
                return false;
            }
            StateVec::iterator it1(this->states.begin());
            StateVec::iterator it2(other.states.begin());
            while (it1 != this->states.end()) {
                if (it1->key != it2->key
                    || it1->normal != it2->normal
                    || it1->plus != it2->plus
                ) {
                    return false;
                } 
                it1++;
                it2++;
            }
            return true;
        }

    };

    enum CounterSetOperationInstructions {
        MOVE,
        INC,
        ADD1,
    };

    struct LValue {
        unsigned state;
        mutable CounterSetOperationInstructions instruction;
        bool operator<(const LValue &other) const {
            return this->state < other.state;
        }

    };

    struct CounterSetOperation {
        CounterSetOperationInstructions instruction;
        unsigned origin;
        unsigned target;
    };

    // compiled update
    struct Update {
        StateVec target_states;
        unsigned counters_size;
        std::vector<CounterSetOperation> counter_updates;
    };

    struct Guard {
        unsigned state;
        CounterGuard condition;
    };

    struct CaTrans {
        unsigned origin;
        unsigned target;
        std::list<re2::Regexp::Derivatives::counterOperator> &operators;
    };
    
    struct Trans {
        std::vector<Guard> guards;
        std::vector<std::vector<CaTrans>> guarded; // transitions that are active only if condition with same index is sat
        std::vector<CaTrans> always; // transitions that are always included
        std::vector<int> update_indexes; // indexes of already compiled updates
    };

    std::vector<Update> cached_updates;
    std::map<Config, unsigned> config_indexes;
    std::vector<std::vector<int>> transition_indexes;
    std::vector<Trans> transitions;
    re2::Regexp::Derivatives ca;

    bool match(const std::string& text);
    void print_ca();
private:
    void compute_update(Csa::Config &cur_config, std::vector<CaTrans> &active);
    Trans compute_trans(Config &cur_config, int bytemap);
    Config &compute_next_config(Config &cur_config, int bytemap);
    unsigned get_config_index(Csa::Config &cur_config);
    Update &get_update(Config &cur_config, Trans &trans);
    bool eval_guard(Config &cur_config, Guard &guard);

};

}

#endif