#include <mata/re2parser.hh>
#include <iostream>

using namespace Mata::RE2Parser;


int main() {
    re2::Regexp::Derivatives derv = create_ca("(abc){0,4}(dg){2,3}df");
    derv.printToDOT1(std::cout);
    derv.removeUnreachableStates();
    derv.printToDOT2(std::cout);
    derv.delimitCountingLoops();
    derv.printToDOT2(std::cout);

    return 0;
}
