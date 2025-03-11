#ifndef ENCODER_HPP
#define ENCODER_HPP

#include "parser.hpp"
#include <vector>
#include <string>
#include <iostream>
#include <unordered_map>
#include <format>
#include <cmath>
#include <iterator>
#include <fstream>
#include <memory>
#include <algorithm>


using namespace std;

enum LiteralType{ORDER, BOOL_VARIABLE, HELPER, DIRECT};

struct Literal{
    LiteralType type;
    int id;
    bool pol;
    int val;
    Literal(LiteralType type, int id, bool pol, int val):
    type(type), id(id), pol(pol), val(val){}
};

struct tuple_hash {
    template <typename T1, typename T2, typename T3>
    std::size_t operator ()(const std::tuple<T1, T2, T3>& p) const {
        auto h1 = std::hash<T1>{}(get<0>(p));  
        auto h2 = std::hash<T2>{}(get<1>(p)); 
        auto h3 = std::hash<T3>{}(get<2>(p));
        return h1 ^ (h2 << 1) ^ (h3 << 1); 
    }
};


class Encoder {
public:
    Encoder(const std::vector<Item>& items);
    std::vector<std::vector<Literal*>> encode_to_cnf();
    void write_to_file(std::string);
    void run_minisat(const std::string &inputFile, const std::string &outputFile);
    void read_minisat_output(const std::string &outputFile);

    bool unsat = false;

private:
    std::vector<std::vector<Literal*>> cnf_clauses;
    const std::vector<Item>& items;
    std::unordered_map<std::string, Parameter*> parameter_map;
    std::unordered_map<std::string, Variable*> variable_map;
    std::unordered_map<std::string, Variable*> array_map; 
    std::unordered_map<int, Variable*> id_map; 
    std::unordered_map<tuple<LiteralType, int, int>, int, tuple_hash> literal_to_num;
    std::unordered_map<int, Literal*> num_to_literal;
    int next_dimacs_num = 1;
    int next_var_id = 1; 
    int next_helper_id = 1; 

    void declare_unsat();

    BasicVar* get_var(Constraint &constr, int ind);
    ArrayLiteral* get_array(Constraint &constr, int ind);
    BasicLiteralExpr* get_const(Constraint &constr, int ind);
    int get_int_from_array(const ArrayLiteral &a, int ind);
    BasicVar *get_var_from_array(const ArrayLiteral &a, int ind);
    int get_variable_id(const std::string &var_name);
    void encode_parameter(Parameter& param, std::vector<std::vector<Literal*>>& cnf_clauses);
    void encode_variable(Variable& var, std::vector<std::vector<Literal*>>& cnf_clauses);
    BasicVar* encode_int_range_helper_variable(const int left, const int right, std::vector<std::vector<Literal *>> &cnf_clauses);
    void encode_direct(const BasicVar &var, std::vector<std::vector<Literal *>> &cnf_clauses);
    void encode_constraint(Constraint &constr, std::vector<std::vector<Literal *>> &cnf_clauses);

    bool encode_primitive_comparison_minus(const BasicVar &a, const BasicVar &b, int c, std::vector<std::vector<Literal*>> &cnf_clauses);
    bool encode_primitive_comparison_plus(const BasicVar &a, const BasicVar &b, int c, std::vector<std::vector<Literal*>> &cnf_clauses);
    void reify(vector<vector<Literal *>>& temp_clauses, const BasicVar& r, vector<vector<Literal *>>& cnf_clauses);

    void encode_array_int_element(const BasicVar &b, const ArrayLiteral &as, BasicVar &c, vector<vector<Literal *>> &cnf_clauses);
    void encode_array_int_maximum(const BasicVar &m, const ArrayLiteral &x, vector<vector<Literal *>> &cnf_clauses);
    void encode_array_int_minimum(const BasicVar &m, const ArrayLiteral &x, vector<vector<Literal *>> &cnf_clauses);
    void encode_array_var_int_element(const BasicVar &b, const ArrayLiteral &as, BasicVar &c, vector<vector<Literal *>> &cnf_clauses);
    void encode_int_abs(const BasicVar &a, const BasicVar &b, std::vector<std::vector<Literal *>> &cnf_clauses);
    void encode_int_div(const BasicVar &a, const BasicVar &b, const BasicVar &c, std::vector<std::vector<Literal *>> &cnf_clauses);
    void encode_int_eq(const BasicVar &a, const BasicVar &b, std::vector<std::vector<Literal *>> &cnf_clauses);
    void encode_int_eq_reif(const BasicVar &a, const BasicVar &b, const BasicVar &r, std::vector<std::vector<Literal *>> &cnf_clauses);
    void encode_int_le(const BasicVar &a, const BasicVar &b, std::vector<std::vector<Literal *>> &cnf_clauses);
    void encode_int_le_reif(const BasicVar &a, const BasicVar &b, const BasicVar &r, std::vector<std::vector<Literal *>> &cnf_clauses);
    void encode_substitution(const BasicVar &var, const BasicVar &var1, const int coef1, const BasicVar &var2, const int coef2, std::vector<std::vector<Literal *>> &cnf_clauses);
    void encode_int_lin_eq(const ArrayLiteral &coefs, const ArrayLiteral &vars, int c, std::vector<std::vector<Literal *>> &cnf_clauses);
    void encode_int_lin_eq_reif(const ArrayLiteral &coefs, const ArrayLiteral &vars, int c, const BasicVar &r, std::vector<std::vector<Literal *>> &cnf_clauses);
    void encode_int_lin_le(const ArrayLiteral &coefs, const ArrayLiteral &vars, int c, std::vector<std::vector<Literal *>> &cnf_clauses);
    void encode_int_lin_le_reif(const ArrayLiteral &coefs, const ArrayLiteral &vars, int c, const BasicVar &r, std::vector<std::vector<Literal *>> &cnf_clauses);
    void encode_int_lin_ne(const ArrayLiteral &coefs, const ArrayLiteral &vars, int c, std::vector<std::vector<Literal *>> &cnf_clauses);
    void encode_int_lin_ne_reif(const ArrayLiteral &coefs, const ArrayLiteral &vars, int c, const BasicVar &r, std::vector<std::vector<Literal *>> &cnf_clauses);
    void encode_int_lt(const BasicVar &a, const BasicVar &b, std::vector<std::vector<Literal *>> &cnf_clauses);
    void encode_int_lt_reif(const BasicVar &a, const BasicVar &b, const BasicVar &r, std::vector<std::vector<Literal *>> &cnf_clauses);
    void encode_int_max(const BasicVar &a, const BasicVar &b, const BasicVar &c, std::vector<std::vector<Literal *>> &cnf_clauses);
    void encode_int_min(const BasicVar &a, const BasicVar &b, const BasicVar& c, std::vector<std::vector<Literal*>> &cnf_clauses);
    void encode_int_mod(const BasicVar &a, const BasicVar &b, const BasicVar &c, std::vector<std::vector<Literal *>> &cnf_clauses);
    void encode_int_ne(const BasicVar &a, const BasicVar &b, std::vector<std::vector<Literal *>> &cnf_clauses);
    void encode_int_ne_reif(const BasicVar &a, const BasicVar &b, const BasicVar &r, std::vector<std::vector<Literal *>> &cnf_clauses);
    void encode_int_plus(const BasicVar &a, const BasicVar &b, const BasicVar &c, std::vector<std::vector<Literal *>> &cnf_clauses);
    void encode_int_pow_nonnegative(const BasicVar &a, const BasicVar &b, const BasicVar &c, std::vector<std::vector<Literal *>> &cnf_clauses);
    void encode_int_pow(const BasicVar &a, const BasicVar &b, const BasicVar &c, std::vector<std::vector<Literal *>> &cnf_clauses);
    void encode_int_times_nonnegative(const BasicVar &a, const BasicVar &b, const BasicVar &c, std::vector<std::vector<Literal *>> &cnf_clauses);
    void encode_int_times(const BasicVar &a, const BasicVar &b, const BasicVar &c, std::vector<std::vector<Literal *>> &cnf_clauses);
};

#endif

