//
// Created by Michal Horký (xhorky23) on 21.08.2020.
//

#ifndef RE2_DERIVATIVES_H
#define RE2_DERIVATIVES_H

#include <list>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "re2/regexp.h"

namespace re2 {
    class Regexp::Derivatives {
    public:

        enum counterGuardEnum {
            True,
            CanIncr,
            CanExit,
            False,
        };

        // Besides the guard itself, it must be saved if logical not is used or not
        struct counterGuard {
            Regexp::Derivatives::counterGuardEnum grd;
            unsigned int countingLoop;
            int counting_min;
            int counting_max;
            bool logical_not;

            bool operator<(const counterGuard &other) const {
                if (grd == other.grd) {
                    if (countingLoop == other.countingLoop) {
                        return logical_not < other.logical_not;
                    }
                    return countingLoop < other.countingLoop;
                }
                return grd < other.grd;
            }

            bool operator==(const counterGuard &other) const {
                return (countingLoop == other.countingLoop && grd == other.grd && logical_not == other.logical_not);
            };
        };

        struct finalStateCondition {
            Regexp::Derivatives::counterGuardEnum grd;
            unsigned int countingLoop;
            int counting_min;
            int counting_max;

            bool isSet;

            // Needed for set
            bool operator<(const finalStateCondition &other) const {
                if (grd == other.grd) {
                    return countingLoop < other.countingLoop;
                }
                return grd < other.grd;
            }
        };

        enum counterOperatorEnum {
            ID,
            INCR,
            EXIT,
            EXIT1,
        };

        // Besides the operator itself, the counting loop must be saved
        struct counterOperator {
            Regexp::Derivatives::counterOperatorEnum op;
            unsigned int countingLoop;
            int counting_min;
            int counting_max;

            // Needed for unordered_map
            bool operator<(const counterOperator &other) const {
                return op < other.op;
            }

            bool operator==(const counterOperator &other) const {
                return op == other.op;
            }
        };

        // A CA state is identified by the regex and the set of counters in scope
        typedef std::pair<unsigned int, std::set<unsigned int>> caState;

        std::vector<caState> caStates;
        std::vector<re2::Regexp *> caStatesRegex;
        std::unordered_map<std::string, unsigned int> regexNumberMapping;

        std::vector<finalStateCondition> finalStates;
        // The information about all counting loops is needed later in the determinization
        std::unordered_map<std::string, unsigned int> countingLoopStringIntMap;
        std::unordered_set<unsigned int> countingLoops;
        unsigned int countingLoopCounter;

        std::unordered_map<std::string, int> sameCountingLoopCount;

        std::unordered_map<std::string, std::string> stateCounterMap;

        // We also need counter with min and max information to create missing implicit ID operators
        std::vector<std::pair<int, int>> countingLoopBounds;

        unsigned int emptyStateNumber = -1;

        // A CA transition is identified by a bytemap for which the transition can be taken, a set of counter guards,
        // a list of counter operators, and a target state
        typedef std::pair<std::pair<int, unsigned int>, std::pair<std::set<Derivatives::counterGuard>, std::list<Derivatives::counterOperator>>> caTransition;

        // A partial derivative is identified by the state (index) and a vector of outgoing transitions
        std::vector<std::vector<Derivatives::caTransition>> partialDerivatives;
        std::vector<bool> existingPartialDerivatives;


        // structs needed for csa
        const uint8_t* bytemap_array;
        int bytemap_range;
        
        // new structures usded for delimiting counting loops of ca
        typedef std::tuple<int, unsigned, std::set<re2::Regexp::Derivatives::counterGuard>, std::list<re2::Regexp::Derivatives::counterOperator>> CaTransition;
        std::vector<std::vector<CaTransition>> transitions;

        // just an interface for computing CA, it returns the normalized regex
        Regexp *getCa(const std::string& pattern);

        // Gets guard for the corresponding operator
        static Derivatives::counterGuard getGuardForOperator(const Derivatives::counterOperator &op);

        // parse to dot (only the reachable states)
        void printToDOT1(std::ostream &outputStream) const; 

        void printToDOT2(std::ostream &outputStream) const;

        void removeUnreachableStates();

    private:
        std::list<re2::Regexp *> statesToCompute;

        std::unordered_set<std::string> discoveredStates;
        enum equationTypes {
            epsilon,
            concatenation,
            alternation,
            repetition,
            countedRepetition
        };

        finalStateCondition unsetFinalStateCondition;


        // functions used to delimit loops of ca
        std::string transitionGrdsAndOpsToString(const CaTransition &trans) const;

        void computeNewState(re2::Regexp *regexp, const uint8_t *bytemap, int bytemapRange,
                             const std::string &compositionStrToConcat = "");

        // Regexes must be normalized, so for example (XY)Z must be rewritten to X(YZ)
        // All capture groups must be deleted (this means that (xyz) will become xyz - no capture group)
        static void rewriteToFlattenedRightAssociativeForm(re2::Regexp *&regexp);

        // Get the type of equation that will be used and the operands for that equation
        equationTypes getEquationTypeAndOperands(re2::Regexp *regexp, re2::Regexp *&operand1, re2::Regexp *&operand2);

        // This function performs composition based on the information from the paper
        // statesVectorFirst determines whether the states vector will be first or second in composition
        std::vector<caTransition>
        composition(const std::string &sourceState,
                    const std::vector<caTransition> &transitionsVector,
                    const std::list<Derivatives::counterOperator> &operatorForComposition,
                    const std::set<Derivatives::counterGuard> &operatorForCompositionGuards,
                    re2::Regexp *regexpForComposition,
                    bool statesVectorFirst);

        // This function gets an operator for a new state that arises from the composition, it also gets a corresponding
        // counter guards
        static std::pair<std::list<Regexp::Derivatives::counterOperator>, std::set<Regexp::Derivatives::counterGuard>>
        getOperatorComposition(std::list<Derivatives::counterOperator> firstOperator,
                               std::set<Derivatives::counterGuard> firstOperatorGuards,
                               std::list<Derivatives::counterOperator> secondOperator,
                               std::set<Derivatives::counterGuard> secondOperatorGuards);

        // Rewriting plus to star and quest to alternation will also be part of the normalization,
        re2::Regexp *normalizeRegexp(re2::Regexp *&regexp);

        // Checks if the expression is nullable for normalization purposes
        bool isNullable(re2::Regexp *regexp);
    };
}

#endif //RE2_DERIVATIVES_H
