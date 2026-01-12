#include <iostream>
#include <fstream>
#include <sstream>
#include "../includes/parser.hpp"
#include "../includes/encoder.hpp"

extern int yyparse();
extern FILE* yyin;

extern YYSTYPE yyval;  

vector<Item>* parsing_result = new vector<Item>;

#include <fstream>
#include <string>

bool has_optimization_goal(const char* filename) {
    ifstream in(filename);
    if (!in) return false;

    string line;
    while (getline(in, line)) {
        if (line.find("solve") != string::npos && (line.find("minimize") != string::npos ||
            line.find("maximize") != string::npos)) {
            return true;
        }
    }
    return false;
}


int main(int argc, char** argv) {

    ios::sync_with_stdio(false);
    cin.tie(nullptr);


    FileType file_type = DIMACS;
    SolverType solver_type = MINISAT;
    const char* input_file = nullptr;
    bool export_proof;

    for (int i = 1; i < argc; ++i) {
        string arg(argv[i]);

        if (arg.rfind("-solver=", 0) == 0) {
            string solver = arg.substr(8);
            if (solver == "minisat") solver_type = MINISAT;
            else if (solver == "cadical") solver_type = CADICAL;
            else if (solver == "glucose") solver_type = GLUCOSE;
            else if (solver == "z3") solver_type = Z3;
            else if (solver == "cvc5") solver_type = CVC5;
            else {
                cerr << "Unknown solver: " << solver << endl;
                return 1;
            }
        } else if (arg.rfind("-file=", 0) == 0) {
            string file = arg.substr(6);
            if (file == "dimacs") file_type = DIMACS;
            else if (file == "smt2") file_type = SMTLIB;
            else {
                cerr << "Unknown file type: " << file << endl;
                return 1;
            }
        } else if (arg.rfind("-export-proof", 0) == 0) {
            export_proof = true;
        } else if (arg[0] != '-') {
            input_file = argv[i]; 
        } else {
            cerr << "Unknown option: " << arg << endl;
            return 1;
        }
    }

    if(input_file && has_optimization_goal(input_file)){
        string cmd = "./optimizer ";
        cmd += input_file;
        system(cmd.c_str());
        return 0;
    }

    if (input_file) {
        yyin = fopen(input_file, "r");
        if (!yyin) {
            cerr << "Could not open file " << input_file << endl;
            return 1;
        }
    } else {
        yyin = stdin;
    }

    if(yyparse() != 0){
        cerr << "Parsing failed!" << endl;
        return 1;
    }

    Encoder encoder(*parsing_result, file_type, solver_type, export_proof);
    auto clauses = encoder.encode_to_cnf();

    encoder.write_to_file();
    encoder.run_solver("model.out");
    encoder.read_solver_output("model.out");
    if(export_proof)
        encoder.generate_proof();



    return 0;
}
