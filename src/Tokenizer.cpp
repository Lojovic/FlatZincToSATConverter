#include "Tokenizer.hpp"
#include <iostream>  

// Available tokens for now
//TODO add set of int as parameter type
const std::vector<std::pair<TokenType, std::regex>> Tokenizer::token_specification = {
    {TokenType::KEYWORD, std::regex("(array|var|predicate|constraint|solve)")},         // Keywords
    {TokenType::TYPE, std::regex("(\\bint\\b|\\bbool\\b|(-?\\d+\\.\\.-?\\d+))")},       // Types
    {TokenType::BOOLEAN, std::regex("(true|false)")},                                   // Booleans
    {TokenType::VAR, std::regex("[a-zA-Z_][a-zA-Z0-9_]*")},                             // Variables
    {TokenType::NUMBER, std::regex("-?\\d+")},                                          // Numbers                    
    {TokenType::SYMBOL, std::regex("([=(){};:,\\[\\]])")},                              // Symbols
    {TokenType::SKIP, std::regex("[ \t\n]+")},                                          // Skip whitespace and newlines
    {TokenType::MISMATCH, std::regex(".")}                                              // Any other character (mismatch)
};

Tokenizer::Tokenizer(const std::string& input) : input(input), pos(0) {}

void Tokenizer::add_token(TokenType type, const std::string& value) {
    tokens.push_back({type, value});
}

void Tokenizer::skip_whitespace_and_newline() {
    while (pos < input.size() && std::isspace(input[pos])) {
        ++pos;
    }
}

// Break the input into tokens
std::vector<Token> Tokenizer::tokenize() {
    while (pos < input.size()) {
        skip_whitespace_and_newline();
        
        if (pos >= input.size()) break; 

        bool matched = false;

        for (const auto& spec : token_specification) {
            std::smatch match;
            
            std::string_view input_view(input.data() + pos, input.size() - pos);
            std::string input_substr(input_view.begin(), input_view.end()); 

            if (std::regex_search(input_substr, match, spec.second) && match.position() == 0) {
                add_token(spec.first, match.str());
                pos += match.length();
                matched = true;

                break;
            }
        }

        if (!matched) {
            std::cerr << "Unexpected token: " << input[pos] << std::endl;
            throw std::runtime_error("Unexpected token: " + std::string(1, input[pos]));
        }
    }

    if (pos < input.size()) {
        std::cerr << "Unexpected token: " << input[pos] << std::endl;
        throw std::runtime_error("Unexpected token: " + std::string(1, input[pos]));
    }

    return tokens;
}
