#ifndef TOKENIZER_HPP
#define TOKENIZER_HPP

#include <iostream>
#include <vector>
#include <string>
#include <regex>

enum class TokenType {
    KEYWORD, TYPE, VAR, NUMBER, BOOLEAN, SYMBOL, SKIP, MISMATCH
};

struct Token {
    TokenType type;
    std::string value;
};

class Tokenizer {
public:
    Tokenizer(const std::string& input);
    std::vector<Token> tokenize();
    
private:
    std::string input;
    size_t pos;
    std::vector<Token> tokens;

    static const std::vector<std::pair<TokenType, std::regex>> token_specification;
    
    void add_token(TokenType type, const std::string& value);
    void skip_whitespace_and_newline();
};

#endif
