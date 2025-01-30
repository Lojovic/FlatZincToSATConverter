#ifndef ENCODER_HPP
#define ENCODER_HPP

#include "Parser.hpp"
#include <vector>
#include <string>
#include <iostream>
#include <unordered_map>
#include <format>
#include <cmath>
#include <iterator>
#include <fstream>

struct IntParameter{
    std::string name;
    int value;
};

struct BoolParameter{
    std::string name;
    bool value;
};

struct IntRangeParameter{
    std::string name;
    int left;
    int right;
};

using Param = std::variant<IntParameter, BoolParameter, IntRangeParameter>;

template<typename T>
bool is(const Param& param) { return std::holds_alternative<T>(param);}

template<typename T>
T as(const Param& param) { return std::get<T>(param); }

struct IntVar{
    std::string name;
    int var_id;
    int value;
};

struct BoolVar{
    std::string name;
    int var_id;
};

struct IntRangeVar{
    std::string name;
    int var_id;
    int left;
    int right;
};

using IntRangeVarOrInt = std::variant<IntRangeVar, int>;

struct IntRangeVarArray{
    std::string name;
    std::vector<IntRangeVarOrInt> elems;
};

template<typename T>
bool is(const IntRangeVarOrInt& var) { return std::holds_alternative<T>(var);}

template<typename T>
T as(const IntRangeVarOrInt& var) { return std::get<T>(var); }

using Var = std::variant<IntVar, BoolVar, IntRangeVar>;

template<typename T>
bool is(const Var& var) { return std::holds_alternative<T>(var);}

template<typename T>
T as(const Var& var) { return std::get<T>(var); }

class Encoder {
public:
    Encoder(const std::vector<Item>& items);
    std::vector<std::vector<std::string>> encode_to_cnf();
    void write_to_file(std::string);
    void run_minisat(const std::string &inputFile, const std::string &outputFile);
    void read_minisat_output(const std::string &outputFile);

    bool unsat = false;

private:
    std::vector<std::vector<std::string>> cnf_clauses;
    const std::vector<Item>& items;
    std::unordered_map<std::string, Param> parameter_map;
    std::unordered_map<std::string, Var> variable_map;
    std::unordered_map<std::string, IntRangeVarArray> array_map; 
    std::unordered_map<int, Var> id_map; 
    std::unordered_map<std::string, int> literal_to_num;
    std::unordered_map<int, std::string> num_to_literal;
    int next_dimacs_num = 1;
    int next_var_id = 1; 
    int next_helper_id = 1; 
    int next_sub_id = 1;

    void declare_unsat();

    std::vector<int> parse_coefs(const std::string&);
    std::vector<IntRangeVarOrInt> parse_vars(const std::string&);

    int get_variable_id(const std::string& var_name);
    void encode_parameter(const Parameter& param, std::vector<std::vector<std::string>>& cnf_clauses);
    void encode_variable(const Variable& var, std::vector<std::vector<std::string>>& cnf_clauses);
    IntRangeVarOrInt encode_helper_variable(const int left, const int right, std::vector<std::vector<std::string>> &cnf_clauses);
    void encode_constraint(const Constraint &constr, std::vector<std::vector<std::string>> &cnf_clauses);
    void encode_predicate(const Predicate& pred, std::vector<std::vector<std::string>>& cnf_clauses);
    void encode_array(const Array &array, std::vector<std::vector<std::string>> &cnf_clauses);

    void encode_primitive_comparison_minus(const IntRangeVar &a, const IntRangeVar &b, int c, std::vector<std::vector<std::string>> &cnf_clauses);
    void encode_primitive_comparison_plus(const IntRangeVar &a, const IntRangeVar &b, int c, std::vector<std::vector<std::string>> &cnf_clauses);

    void encode_int_abs(const IntRangeVar &a, const IntRangeVar &b, std::vector<std::vector<std::string>> &cnf_clauses);
    void encode_int_eq(const IntRangeVar &a, const IntRangeVar &b, std::vector<std::vector<std::string>> &cnf_clauses);
    void encode_int_le(const IntRangeVar &a, const IntRangeVar &b, std::vector<std::vector<std::string>> &cnf_clauses);
    void encode_substitution(const IntRangeVarOrInt &var, const IntRangeVarOrInt &var1, const int coef1, const IntRangeVarOrInt &var2, const int coef2, std::vector<std::vector<std::string>> &cnf_clauses);
    void encode_int_lin_le(const std::vector<int> &coefs, const std::vector<IntRangeVarOrInt> &vars, int c, std::vector<std::vector<std::string>> &cnf_clauses);
    void encode_int_lt(const IntRangeVar &a, const IntRangeVar &b, std::vector<std::vector<std::string>> &cnf_clauses);
    void encode_int_max(const IntRangeVar &a, const IntRangeVar &b, const IntRangeVar& c, std::vector<std::vector<std::string>> &cnf_clauses);
    void encode_int_min(const IntRangeVar &a, const IntRangeVar &b, const IntRangeVar& c, std::vector<std::vector<std::string>> &cnf_clauses);
    void encode_int_ne(const IntRangeVar &a, const IntRangeVar &b, std::vector<std::vector<std::string>> &cnf_clauses);

};

#endif

