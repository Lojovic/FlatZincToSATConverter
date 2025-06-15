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
#include <set>


using namespace std;

enum LiteralType{ORDER, BOOL_VARIABLE, HELPER, DIRECT, SET_ELEM};

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
    size_t operator ()(const tuple<T1, T2, T3>& p) const {
        auto h1 = hash<T1>{}(get<0>(p));  
        auto h2 = hash<T2>{}(get<1>(p)); 
        auto h3 = hash<T3>{}(get<2>(p));
        return h1 ^ (h2 << 1) ^ (h3 << 1); 
    }
};


class Encoder {
public:
    Encoder(const vector<Item>& items, const string& file);
    vector<vector<shared_ptr<Literal>>> encode_to_cnf();
    void write_to_file();
    void run_minisat(const string &outputFile);
    void read_minisat_output(const string &outputFile);

    bool unsat = false;

private:

    std::shared_ptr<Literal> make_literal(LiteralType type, int id, bool pol, int val) {
        return std::make_shared<Literal>(type, id, pol, val);
    }

    void cleanup_variant(BasicVarType& var) {
        std::visit([](auto&& arg) {
            using T = std::decay_t<decltype(arg)>;
            if constexpr (std::is_pointer_v<T>) {
                delete arg; 
            }
        }, var);
    }

    void cleanup_helper_variables() {
        for (BasicVar* var : helper_vars) {
            cleanup_variant(*var->type);
            delete var->type;           
            delete var->name;              
            delete var;                   
        }
        helper_vars.clear();
    }

    void cleanup_arrays() {
        for (ArrayLiteral* arr : allocated_arrays) {
            for (BasicExpr* expr : *arr) {
                delete expr;
            }
            delete arr;
        }
        allocated_arrays.clear();
    }

    vector<vector<shared_ptr<Literal>>> cnf_clauses;
    const vector<Item>& items;
    unordered_map<string, Parameter*> parameter_map;
    unordered_map<string, Variable*> variable_map;
    unordered_map<string, Variable*> array_map; 
    unordered_map<int, Variable*> id_map; 
    unordered_map<tuple<LiteralType, int, int>, int, tuple_hash> literal_to_num;
    unordered_map<int, shared_ptr<Literal>> num_to_literal;
    unordered_map<int, set<int>> set_variable_map;
    set<ArrayVar*> array_set;
    vector<BasicVar*> helper_vars;
    vector<ArrayLiteral*> allocated_arrays;
    string fileName;

    int next_dimacs_num = 1;
    int next_var_id = 1; 
    int next_helper_id = 1;
    int clause_num = 0; 

    void declare_unsat();

    void write_clauses_to_file(vector<vector<shared_ptr<Literal>>>& cnf_clauses);
    ArrayLiteral* get_array(Constraint &constr, int ind);
    BasicLiteralExpr* get_const(Constraint &constr, int ind);
    SetLiteral* get_set_from_array(const ArrayLiteral &a, int ind);
    int get_int_from_array(const ArrayLiteral &a, int ind);
    bool get_bool_from_array(const ArrayLiteral &a, int ind);
    BasicVar *get_var_from_array(const ArrayLiteral &a, int ind);
    vector<int> *get_set_elems(const BasicVar &var);
    int get_variable_id(const string &var_name);
    void encode_parameter(Parameter& param, vector<vector<shared_ptr<Literal>>>& cnf_clauses);
    void encode_variable(Variable& var, vector<vector<shared_ptr<Literal>>>& cnf_clauses);
    BasicVar* encode_int_range_helper_variable(const int left, const int right, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    BasicVar *encode_bool_helper_variable(vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_direct(const BasicVar &var, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    BasicVar *encode_param_as_var(Parameter &param, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    BasicVar *get_var(Constraint &constr, int ind, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_constraint(Constraint &constr, vector<vector<shared_ptr<Literal>>> &cnf_clauses);

    bool encode_primitive_comparison_minus(const BasicVar &a, const BasicVar &b, int c, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    bool encode_primitive_comparison_plus(const BasicVar &a, const BasicVar &b, int c, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void reify(vector<vector<shared_ptr<Literal>>>& temp_clauses, const BasicVar& r, vector<vector<shared_ptr<Literal>>>& cnf_clauses);
    void impify(vector<vector<shared_ptr<Literal>>> &temp_clauses, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);

    void encode_array_int_element(const BasicVar &b, const ArrayLiteral &as, BasicVar &c, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_array_int_maximum(const BasicVar &m, const ArrayLiteral &x, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_array_int_minimum(const BasicVar &m, const ArrayLiteral &x, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_array_var_int_element(const BasicVar &b, const ArrayLiteral &as, BasicVar &c, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_abs(const BasicVar &a, const BasicVar &b, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_div(const BasicVar &a, const BasicVar &b, const BasicVar &c, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_eq(const BasicVar &a, const BasicVar &b, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_eq_reif(const BasicVar &a, const BasicVar &b, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_eq_imp(const BasicVar &a, const BasicVar &b, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_le(const BasicVar &a, const BasicVar &b, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_le_reif(const BasicVar &a, const BasicVar &b, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_le_imp(const BasicVar &a, const BasicVar &b, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_substitution(const BasicVar &var, const BasicVar &var1, const int coef1, const BasicVar &var2, const int coef2, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_lin_eq(const ArrayLiteral &coefs, const ArrayLiteral &vars, int c, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_lin_eq_reif(const ArrayLiteral &coefs, const ArrayLiteral &vars, int c, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_lin_eq_imp(const ArrayLiteral &coefs, const ArrayLiteral &vars, int c, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_lin_le(const ArrayLiteral &coefs, const ArrayLiteral &vars, int c, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_lin_le_reif(const ArrayLiteral &coefs, const ArrayLiteral &vars, int c, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_lin_le_imp(const ArrayLiteral &coefs, const ArrayLiteral &vars, int c, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_lin_ne(const ArrayLiteral &coefs, const ArrayLiteral &vars, int c, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_lin_ne_reif(const ArrayLiteral &coefs, const ArrayLiteral &vars, int c, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_lin_ne_imp(const ArrayLiteral &coefs, const ArrayLiteral &vars, int c, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_lt(const BasicVar &a, const BasicVar &b, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_lt_reif(const BasicVar &a, const BasicVar &b, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_lt_imp(const BasicVar &a, const BasicVar &b, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_max(const BasicVar &a, const BasicVar &b, const BasicVar &c, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_min(const BasicVar &a, const BasicVar &b, const BasicVar& c, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_mod(const BasicVar &a, const BasicVar &b, const BasicVar &c, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_ne(const BasicVar &a, const BasicVar &b, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_ne_reif(const BasicVar &a, const BasicVar &b, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_ne_imp(const BasicVar &a, const BasicVar &b, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_plus(const BasicVar &a, const BasicVar &b, const BasicVar &c, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_pow_nonnegative(const BasicVar &a, const BasicVar &b, const BasicVar &c, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_pow(const BasicVar &a, const BasicVar &b, const BasicVar &c, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_times_nonnegative(const BasicVar &a, const BasicVar &b, const BasicVar &c, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_int_times(const BasicVar &a, const BasicVar &b, const BasicVar &c, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_set_in(const BasicVar &x, const BasicLiteralExpr &S, vector<vector<shared_ptr<Literal>>> &cnf_clauses);

    void encode_array_bool_and(const ArrayLiteral &as, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_array_bool_element(const BasicVar &b, const ArrayLiteral &as, BasicVar &c, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_array_bool_or(const ArrayLiteral &as, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_array_bool_xor(const ArrayLiteral &as, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_array_var_bool_element(const BasicVar &b, const ArrayLiteral &as, BasicVar &c, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_bool2int(const BasicVar &a, const BasicVar &b, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_bool_and(const BasicVar &a, const BasicVar &b, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_bool_clause(const ArrayLiteral &as, const ArrayLiteral &bs, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_bool_eq(const BasicVar &a, const BasicVar &b, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_bool_eq_reif(const BasicVar &a, const BasicVar &b, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_bool_eq_imp(const BasicVar &a, const BasicVar &b, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_bool_le(const BasicVar &a, const BasicVar &b, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_bool_le_reif(const BasicVar &a, const BasicVar &b, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_bool_le_imp(const BasicVar &a, const BasicVar &b, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_bool_substitution(const BasicVar &x, const BasicVar &x1, int coef1, const BasicVar &x2, int coef2, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_bool_lin_eq(const ArrayLiteral &coefs, const ArrayLiteral &vars, int c, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_bool_lin_le(const ArrayLiteral &coefs, const ArrayLiteral &vars, int c, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_bool_lt(const BasicVar &a, const BasicVar &b, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_bool_lt_reif(const BasicVar &a, const BasicVar &b, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_bool_lt_imp(const BasicVar &a, const BasicVar &b, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_bool_not(const BasicVar &a, const BasicVar &b, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_bool_or(const BasicVar &a, const BasicVar &b, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_bool_xor(const BasicVar &a, const BasicVar &b, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_bool_xor(const BasicVar &a, const BasicVar &b, vector<vector<shared_ptr<Literal>>> &cnf_clauses);

    void encode_array_set_element(const BasicVar &b, const ArrayLiteral &as, const BasicVar &c, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_array_var_set_element(const BasicVar &b, const ArrayLiteral &as, const BasicVar &c, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_set_substitution(const BasicVar &x, const BasicVar &x1, int val1, int val2, int S_id, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_set_card(const BasicVar &S, int x, int x_is, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_set_card(const BasicVar &S, const BasicVar &x, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_set_diff(const BasicVar &x, const BasicVar &y, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_set_eq(const BasicVar &x, const BasicVar &y, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_set_eq_reif(const BasicVar &x, const BasicVar &y, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_set_eq_imp(const BasicVar &x, const BasicVar &y, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_set_in(const BasicVar &x, const BasicVar &S, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_set_in_reif(const BasicVar &x, const BasicLiteralExpr &S1, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_set_in_imp(const BasicVar &x, const BasicVar &S, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_set_in_reif(const BasicVar &x, const BasicVar &S, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_set_in_imp(const BasicVar &x, const BasicLiteralExpr &S1, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_set_ne(const BasicVar &x, const BasicVar &y, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_set_ne_reif(const BasicVar &x, const BasicVar &y, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_set_ne_imp(const BasicVar &x, const BasicVar &y, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_set_intersect(const BasicVar &x, const BasicVar &y, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void set_max(const BasicVar &x, const BasicVar &set, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_set_le(const BasicVar &x, const BasicVar &y, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_set_le_reif(const BasicVar &x, const BasicVar &y, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_set_lt(const BasicVar &x, const BasicVar &y, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_set_lt_reif(const BasicVar &x, const BasicVar &y, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_set_subset(const BasicVar &x, const BasicVar &y, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_set_subset_reif(const BasicVar &x, const BasicVar &y, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_set_subset_imp(const BasicVar &x, const BasicVar &y, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_set_superset(const BasicVar &x, const BasicVar &y, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_set_superset_reif(const BasicVar &x, const BasicVar &y, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_set_superset_imp(const BasicVar &x, const BasicVar &y, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_set_symdiff(const BasicVar &x, const BasicVar &y, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
    void encode_set_union(const BasicVar &x, const BasicVar &y, const BasicVar &r, vector<vector<shared_ptr<Literal>>> &cnf_clauses);
};

#endif

