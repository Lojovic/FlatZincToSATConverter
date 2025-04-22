#include <iostream>
#include <fstream>
#include <sstream>
#include "parser.hpp"
#include "encoder.hpp"

extern int yyparse();
extern FILE* yyin;

extern YYSTYPE yyval;  

vector<Item>* parsing_result = new vector<Item>;

int main(int argc, char** argv) {

    if (argc > 1) {
        yyin = fopen(argv[1], "r");
        if (!yyin) {
            std::cerr << "Could not open file " << argv[1] << std::endl;
            return 1;
        }
    } else {
        yyin = stdin;
    }

    if(yyparse() != 0){
        cerr << "Parsing failed!" << endl;
        return 1;
    }

    Encoder encoder(*parsing_result);
    auto clauses = encoder.encode_to_cnf();

    if(!encoder.unsat){
        encoder.write_to_file("../formula.cnf");
        encoder.run_minisat("../formula.cnf", "model.out");
        encoder.read_minisat_output("model.out");
    }
    // for(auto clause : clauses){
    //     for(auto literal : clause)
    //         std::cout << (literal->pol ? "" : "-") << (literal->type == LiteralType::HELPER ? "q_" : "p_") 
    //                   << literal->id << "_" << literal->val << " ";
    //     std::cout << std::endl;
    // }

    return 0;
}
