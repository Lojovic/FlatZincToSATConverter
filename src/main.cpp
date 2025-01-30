#include <iostream>
#include <fstream>
#include <sstream>
#include "Tokenizer.hpp"
#include "Parser.hpp"
#include "Encoder.hpp"

int main() {

    std::ifstream file("../input.fzn");

    if (!file.is_open()) {
        std::cerr << "Error opening file!" << std::endl;
        return 1;
    }

    std::stringstream buffer;
    buffer << file.rdbuf();

    std::string fileContents = buffer.str();

    Tokenizer tokenizer(fileContents);
    std::vector<Token> tokens = tokenizer.tokenize();

    Parser parser(tokens);
    parser.parse_program();

    Encoder encoder(parser.items);
    auto clauses = encoder.encode_to_cnf();

    if(!encoder.unsat){
        encoder.write_to_file("../formula.cnf");
        encoder.run_minisat("../formula.cnf", "model.out");
        encoder.read_minisat_output("model.out");
    }
    // for(auto clause : clauses){
    //     for(auto literal : clause)
    //         std::cout << literal << " ";
    //     std::cout << std::endl;
    // }

    return 0;
}
