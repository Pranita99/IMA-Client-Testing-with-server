
#include "../PrintVisitor.hpp"
#include "../Symbolic/SEVisitor.hpp"
#include "../Symbolic/SymbolicEnv.hpp"
#include "../IMA.hpp"
#include "../testPaths/webApp1/path1.cpp"   

int main() {
   
    SymbolTable sym;  TypeMap tmap;
    Program mutant = IMA(clientProgram, spec, sym, tmap);

  
    {
        PrintVisitor pv;
        std::cout << "=== abstract test case ===\n";
        mutant.accept(pv);
    }

   
    {
        SymbolicEnv sigma;
        SEVisitor   se(sigma);
        mutant.accept(se);
        std::cout << "\n=== symbolic path constraints ===\n";
        std::cout << sigma.toSMTLib(/*withFooter=*/false) << '\n';
    }
}
