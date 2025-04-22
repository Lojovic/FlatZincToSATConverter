/* A Bison parser, made by GNU Bison 3.8.2.  */

/* Skeleton interface for Bison GLR parsers in C

   Copyright (C) 2002-2015, 2018-2021 Free Software Foundation, Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

#ifndef YY_YY_HOME_UBUNTU_DESKTOP_AR_SEMINARSKI_SRC_PARSER_HPP_INCLUDED
# define YY_YY_HOME_UBUNTU_DESKTOP_AR_SEMINARSKI_SRC_PARSER_HPP_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 1
#endif
#if YYDEBUG
extern int yydebug;
#endif
/* "%code requires" blocks.  */
#line 15 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"

    #include <iostream>
    #include <vector>
    #include <variant>

    using namespace std;

    enum BasicParType{INT, BOOL, SETOFINT};

    struct SetRangeLiteral{
        int left;
        int right;
        SetRangeLiteral(int left, int right):
        left(left), right(right){}
    };

    struct SetSetLiteral{
        vector<int>* elems;
        SetSetLiteral(vector<int>* elems):
        elems(elems){}
    };

    using SetLiteral = variant<SetRangeLiteral*, SetSetLiteral*>;
    using BasicLiteralExpr = variant<int, bool, SetLiteral*>;
    using BasicExpr = variant<BasicLiteralExpr*, string*>;

    struct ParArrayType{
        BasicParType type;
        int num_of_elems;
        ParArrayType(BasicParType type, int num_of_elems) : 
        type(type), num_of_elems(num_of_elems){}
    };
    using ParType = variant<BasicParType, ParArrayType*>;

    struct ParArrayLiteral{
        vector<BasicLiteralExpr*>* elems;
        ParArrayLiteral(vector<BasicLiteralExpr*>* elems):
        elems(elems){}
    };
    using ParExpr = variant<BasicLiteralExpr*, ParArrayLiteral*>;

    struct Parameter {
        ParType* type;
        string* name;
        ParExpr* value;
        Parameter(ParType* type, string* name, ParExpr* value):
        type(type), name(name), value(value){}
    };

    struct IntRangeVarType{
        int left;
        int right;
        IntRangeVarType(int left, int right):
        left(left), right(right){}
    };

    struct IntSetVarType{
        vector<int>* elems;
        IntSetVarType(vector<int>* elems):
        elems(elems){}
    };

    struct SetVarType{
        vector<int>* elems;
        SetVarType(vector<int>* elems):
        elems(elems){}
    };

    using BasicVarType = variant<BasicParType, IntRangeVarType*, IntSetVarType*, 
                                 SetVarType*>;

    struct ArrayVarType{
        int size;
        BasicVarType* type;
        ArrayVarType(int size, BasicVarType* type):
        size(size), type(type){}
    };

    struct BasicVar{
        BasicVarType* type;
        string* name;
        BasicExpr* value;
        bool helper;
        int id;
        BasicVar(BasicVarType* type, string* name, BasicExpr* value, bool helper):
        type(type), name(name), value(value), helper(helper){}
        BasicVar(BasicVarType* type, string* name, bool helper):
        type(type), name(name), helper(helper){
            value = nullptr;
        }        
    };

    using ArrayLiteral = vector<BasicExpr*>;

    struct ArrayVar{
        ArrayVarType* type;
        string* name;
        ArrayLiteral* value;
        ArrayVar(ArrayVarType* type, string* name, ArrayLiteral* value):
        type(type), name(name), value(value){}
    };

    using Variable = variant<BasicVar*, ArrayVar*>;

    using Expr = variant<BasicExpr*, ArrayLiteral*>;
    using ArgsList = vector<Expr*>;

    struct Constraint {
        string* name;
        ArgsList* args;
        Constraint(string* name, ArgsList* args):
        name(name), args(args){}
    };

    using BasicPredParamType = variant<BasicParType, BasicVarType*, IntRangeVarType*, IntSetVarType*>;

    struct PredicateParam{
        string* name;
        BasicPredParamType* type;

        PredicateParam(string* name, BasicPredParamType* type) : 
        name(name), type(type){}
    };

    struct Predicate{
        string* name;
        vector<PredicateParam*>* params;

        Predicate(string* name, vector<PredicateParam*>* params) : 
        name(name), params(params){}
    };

    enum SolveType {ORDINARY, MINIMIZE, MAXIMIZE};

    struct Solve {
        SolveType type;
        BasicExpr* expr;
        Solve(SolveType type):
        type(type){}
        Solve(SolveType type, BasicExpr* expr):
        type(type), expr(expr){}
    };
    using Item = variant<Parameter*, Variable*, Constraint*, Solve*, Predicate*>;

    template<typename T>
    bool is(const Item& item) { return std::holds_alternative<T>(item);}

    template<typename T>
    T as(const Item& item) { return std::get<T>(item); }

    extern vector<Item>* parsing_result;


#line 198 "/home/ubuntu/Desktop/AR/seminarski/src/parser.hpp"

/* Token kinds.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    YYEMPTY = -2,
    YYEOF = 0,                     /* "end of file"  */
    YYerror = 256,                 /* error  */
    YYUNDEF = 257,                 /* "invalid token"  */
    BASIC_PAR_TYPE = 258,          /* BASIC_PAR_TYPE  */
    ARRAY = 259,                   /* ARRAY  */
    VAR = 260,                     /* VAR  */
    PREDICATE = 261,               /* PREDICATE  */
    CONSTRAINT = 262,              /* CONSTRAINT  */
    SOLVE = 263,                   /* SOLVE  */
    SET = 264,                     /* SET  */
    OF = 265,                      /* OF  */
    SOLVE_SATISFY = 266,           /* SOLVE_SATISFY  */
    SOLVE_MAXIMIZE = 267,          /* SOLVE_MAXIMIZE  */
    SOLVE_MINIMIZE = 268,          /* SOLVE_MINIMIZE  */
    BOOL_LITERAL = 269,            /* BOOL_LITERAL  */
    INT_LITERAL = 270,             /* INT_LITERAL  */
    VAR_PAR_IDENTIFIER = 271,      /* VAR_PAR_IDENTIFIER  */
    EQUALS = 272,                  /* EQUALS  */
    OPEN_PARENT_SMALL = 273,       /* OPEN_PARENT_SMALL  */
    CLOSED_PARENT_SMALL = 274,     /* CLOSED_PARENT_SMALL  */
    OPEN_PARENT_BIG = 275,         /* OPEN_PARENT_BIG  */
    CLOSED_PARENT_BIG = 276,       /* CLOSED_PARENT_BIG  */
    SEMICOLON = 277,               /* SEMICOLON  */
    COMMA = 278,                   /* COMMA  */
    DOUBLE_COLON = 279,            /* DOUBLE_COLON  */
    COLON = 280,                   /* COLON  */
    OPEN_PARENT_MED = 281,         /* OPEN_PARENT_MED  */
    CLOSED_PARENT_MED = 282,       /* CLOSED_PARENT_MED  */
    TWO_DOTS = 283,                /* TWO_DOTS  */
    TRIPLE_QUOTATIONS = 284,       /* TRIPLE_QUOTATIONS  */
    STRING_CONTENTS = 285,         /* STRING_CONTENTS  */
    MISMATCH = 286                 /* MISMATCH  */
  };
  typedef enum yytokentype yytoken_kind_t;
#endif

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
union YYSTYPE
{
#line 228 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"

    std::string* str_attr;
    vector<Item>* items_attr;
    bool bool_attr;
    int int_attr;
    vector<PredicateParam*>* pred_params_attr;
    PredicateParam* pred_param_attr;
    Predicate* pred_attr;
    BasicParType basic_par_type_attr;
    ParType* par_type_attr;
    BasicLiteralExpr* basic_literal_expr_attr;
    ParArrayLiteral* par_array_literal_attr;
    Parameter* par_attr;
    ParExpr* par_expr_attr;
    BasicVarType* basic_var_type_attr;
    BasicExpr* basic_expr_attr;
    ArrayVarType* array_var_type_attr;
    ArrayLiteral* array_literal_attr;
    Variable* variable_attr;
    vector<int>* vector_of_int_attr;
    Expr* expr_attr;
    ArgsList* args_list_attr;
    Constraint* constraint_attr;
    Solve* solve_attr;
    BasicPredParamType* basic_pred_param_type_attr;
    vector<Variable*>* variable_vector_attr;
    vector<Predicate*>* predicate_vector_attr;
    vector<Parameter*>* parameter_vector_attr;
    vector<Constraint*>* constraint_vector_attr;
    SetLiteral* set_literal_attr;

#line 278 "/home/ubuntu/Desktop/AR/seminarski/src/parser.hpp"

};
typedef union YYSTYPE YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif


extern YYSTYPE yylval;

int yyparse (void);

#endif /* !YY_YY_HOME_UBUNTU_DESKTOP_AR_SEMINARSKI_SRC_PARSER_HPP_INCLUDED  */
