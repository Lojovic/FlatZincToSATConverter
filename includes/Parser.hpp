#ifndef PARSER_HPP
#define PARSER_HPP

#include "Tokenizer.hpp"
#include <vector>
#include <string>
#include <memory>
#include <variant>
#include <unordered_map>

struct Parameter {
    std::string type;
    std::string name;
    std::string value;
};

struct Variable {
    std::string type;
    std::string name;
    std::string value;
};

struct Constraint {
    std::string name;
    std::string var1;
    std::string var2;
    std::string var3;
    std::string var4;
};

struct Predicate{
    std::string id;
};

struct Solve {
    std::string type;
};

using ParVar = std::variant<Parameter, Variable, int>;

struct Array{
    std::string type;
    std::string name;
    std::vector<ParVar> elems;
};

template<typename T>
bool is(const ParVar& parvar) { return std::holds_alternative<T>(parvar);}

template<typename T>
T as(const ParVar& parvar) { return std::get<T>(parvar); }

using Item = std::variant<Array, Parameter, Variable, Constraint, Solve, Predicate>;

template<typename T>
bool is(const Item& item) { return std::holds_alternative<T>(item);}

template<typename T>
T as(const Item& item) { return std::get<T>(item); }

class Parser {
public:
    Parser(const std::vector<Token>& tokens);
    void parse_program();
    std::vector<Item> items;
    //TODO make items private and a getter

private:
    std::vector<Token> tokens;
    size_t pos;
    
    std::unordered_map<std::string, Variable> var_map;

    Token current_token();
    void consume();
    void expect(TokenType type);
    
    Parameter parse_parameter_declaration();
    Variable parse_variable_declaration();
    Array parse_array_declaration();
    Constraint parse_constraint();
    Predicate parse_predicate();

    std::string parse_array();
};

#endif
