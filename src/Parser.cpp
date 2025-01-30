#include "Parser.hpp"
#include <iostream>

Parser::Parser(const std::vector<Token>& tokens) : tokens(tokens), pos(0) {}

Token Parser::current_token() {
    if (pos < tokens.size()) {
        return tokens[pos];
    }
    return {TokenType::MISMATCH, ""};
}

void Parser::consume() {
    if (pos < tokens.size()) {
        ++pos;
    }
}

void Parser::expect(TokenType type) {
    Token token = current_token();
    if (token.type == type) {
        consume();
    } else {
        std::cerr << "Unexpected token: " + token.value << std::endl;
    }
}

std::string Parser::parse_array(){
    consume(); // [
    std::string res = "";
    while(current_token().value != "]"){
        res += current_token().value;
        consume(); // ,
    }
    consume(); // ]
    consume(); // ,

    return res;
}

Parameter Parser::parse_parameter_declaration() {
    Token token = current_token();

    consume();
    expect(TokenType::SYMBOL);  // ':'
    std::string var_name = current_token().value;
    expect(TokenType::VAR);
    expect(TokenType::SYMBOL);  // '='
    std::string value = current_token().value;
    if (token.value == "int") {
        expect(TokenType::NUMBER);
        expect(TokenType::SYMBOL);  // ';'
        return {"int", var_name, value};
    }
    else if (token.value == "bool") {
        expect(TokenType::BOOLEAN);
        expect(TokenType::SYMBOL);  // ';'
        return {"bool", var_name, value};
    } else{
        return {"int_range", var_name, token.value};
    }

}

Variable Parser::parse_variable_declaration() {
    consume();                  //var

    Token token = current_token();
    consume();
    
    expect(TokenType::SYMBOL);  // ':'
    std::string var_name = current_token().value;
    expect(TokenType::VAR);
    expect(TokenType::SYMBOL);  // '=' or ';'
    std::string value = current_token().value;
    if (token.value == "int") {
        expect(TokenType::NUMBER);
        expect(TokenType::SYMBOL);  // ';'
        return {"int", var_name, value};
    }
    else if (token.value == "bool") {
        expect(TokenType::BOOLEAN);
        expect(TokenType::SYMBOL);  // ';'
        return {"bool", var_name, value};
    } else{
        return {"int_range", var_name, token.value};
    }

}

Array Parser::parse_array_declaration() {
    consume();                  //array

    expect(TokenType::SYMBOL);  // '['
    expect(TokenType::TYPE);    // '1..x'
    expect(TokenType::SYMBOL);  // ']'
    consume();                  // "of"

    bool vars = false;
    if(current_token().value == "var"){
        vars = true;
        consume();
    }
    std::string type = current_token().value;
    expect(TokenType::TYPE); 


    expect(TokenType::SYMBOL); // ':'

    std::string name = current_token().value;
    expect(TokenType::VAR);
    expect(TokenType::SYMBOL); // '='
    expect(TokenType::SYMBOL); // '['

    std::vector<ParVar> elems;
    while(current_token().value != "]"){
        if(current_token().type == TokenType::NUMBER){
            elems.push_back(std::stoi(current_token().value));
        } else if(vars){
            std::string var_name = current_token().value;
            elems.push_back(var_map[var_name]);
            expect(TokenType::VAR);
            if(current_token().value == "]")
                break;
            expect(TokenType::SYMBOL);
        } else {
            //TODO parametri
        }
    }

    expect(TokenType::SYMBOL); // ']'
    expect(TokenType::SYMBOL); // ';'

    return {type, name, elems};

}

Constraint Parser::parse_constraint() {
    consume();
    std::string name = current_token().value;
    expect(TokenType::VAR);
    expect(TokenType::SYMBOL);  // '('

    std::string var1 = "";
    std::string var2 = "";
    std::string var3 = "";
    std::string var4 = "";

    if(current_token().value != ")"){
        if(current_token().value == "[")
            var1 = parse_array();
        else{
            var1 = current_token().value;
            consume();
            if(current_token().value == ",")
                consume();
        }
    }
    if(current_token().value != ")"){
        if(current_token().value == "[")
            var2 = parse_array();
        else{
            var2 = current_token().value;
            consume();
            if(current_token().value == ",")
                consume();
        }
    }
    if(current_token().value != ")"){
        var3 = current_token().value;
        consume();
        if(current_token().value == ",")
            consume();
    }
    if(current_token().value != ")"){
        var4 = current_token().value;
        consume();
        if(current_token().value == ",")
            consume();
    }
    expect(TokenType::SYMBOL);
    expect(TokenType::SYMBOL);  // ';'
    return {name, var1, var2, var3, var4};

}

Predicate Parser::parse_predicate() {
    consume();
    std::string id = current_token().value;
    expect(TokenType::VAR);
    expect(TokenType::SYMBOL);  // '('
    std::string var2 = current_token().value;
    expect(TokenType::VAR);
    expect(TokenType::SYMBOL);  // ';'
    return {};

}


void Parser::parse_program() {
    while (pos < tokens.size()) {
        Token token = current_token();
        
        if(token.type == TokenType::KEYWORD && token.value == "predicate"){
            //TODO parse predicate
        } else if (token.type == TokenType::TYPE) {
            Parameter decl = parse_parameter_declaration();
            items.push_back(decl);
        } else if(token.type == TokenType::KEYWORD && token.value == "array"){
            Array array = parse_array_declaration();
            items.push_back(array);
        } else if(token.type == TokenType::KEYWORD && token.value == "var"){
            Variable decl = parse_variable_declaration();
            var_map[decl.name] = decl;
            items.push_back(decl);
        } else if (token.type == TokenType::KEYWORD && token.value == "constraint") {
            Constraint constr = parse_constraint();
            items.push_back(constr);
        } else if (token.type == TokenType::KEYWORD && token.value == "solve") {
            //TODO parse solve
        } else {
            std::cerr << "Unexpected token in program" << std::endl;
        }
    }
}
