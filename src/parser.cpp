/* A Bison parser, made by GNU Bison 3.8.2.  */

/* Skeleton implementation for Bison GLR parsers in C

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

/* C GLR parser skeleton written by Paul Hilfinger.  */

/* DO NOT RELY ON FEATURES THAT ARE NOT DOCUMENTED in the manual,
   especially those whose name start with YY_ or yy_.  They are
   private implementation details that can be changed or removed.  */

/* Identify Bison output, and Bison version.  */
#define YYBISON 30802

/* Bison version string.  */
#define YYBISON_VERSION "3.8.2"

/* Skeleton name.  */
#define YYSKELETON_NAME "glr.c"

/* Pure parsers.  */
#define YYPURE 0






/* First part of user prologue.  */
#line 1 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"


int yylex();

#define yyerror printf

#include <iostream>


#line 68 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"

# ifndef YY_CAST
#  ifdef __cplusplus
#   define YY_CAST(Type, Val) static_cast<Type> (Val)
#   define YY_REINTERPRET_CAST(Type, Val) reinterpret_cast<Type> (Val)
#  else
#   define YY_CAST(Type, Val) ((Type) (Val))
#   define YY_REINTERPRET_CAST(Type, Val) ((Type) (Val))
#  endif
# endif
# ifndef YY_NULLPTR
#  if defined __cplusplus
#   if 201103L <= __cplusplus
#    define YY_NULLPTR nullptr
#   else
#    define YY_NULLPTR 0
#   endif
#  else
#   define YY_NULLPTR ((void*)0)
#  endif
# endif

#include "parser.hpp"

/* Symbol kind.  */
enum yysymbol_kind_t
{
  YYSYMBOL_YYEMPTY = -2,
  YYSYMBOL_YYEOF = 0,                      /* "end of file"  */
  YYSYMBOL_YYerror = 1,                    /* error  */
  YYSYMBOL_YYUNDEF = 2,                    /* "invalid token"  */
  YYSYMBOL_BASIC_PAR_TYPE = 3,             /* BASIC_PAR_TYPE  */
  YYSYMBOL_ARRAY = 4,                      /* ARRAY  */
  YYSYMBOL_VAR = 5,                        /* VAR  */
  YYSYMBOL_PREDICATE = 6,                  /* PREDICATE  */
  YYSYMBOL_CONSTRAINT = 7,                 /* CONSTRAINT  */
  YYSYMBOL_SOLVE = 8,                      /* SOLVE  */
  YYSYMBOL_SET = 9,                        /* SET  */
  YYSYMBOL_OF = 10,                        /* OF  */
  YYSYMBOL_SOLVE_SATISFY = 11,             /* SOLVE_SATISFY  */
  YYSYMBOL_SOLVE_MAXIMIZE = 12,            /* SOLVE_MAXIMIZE  */
  YYSYMBOL_SOLVE_MINIMIZE = 13,            /* SOLVE_MINIMIZE  */
  YYSYMBOL_BOOL_LITERAL = 14,              /* BOOL_LITERAL  */
  YYSYMBOL_INT_LITERAL = 15,               /* INT_LITERAL  */
  YYSYMBOL_VAR_PAR_IDENTIFIER = 16,        /* VAR_PAR_IDENTIFIER  */
  YYSYMBOL_EQUALS = 17,                    /* EQUALS  */
  YYSYMBOL_OPEN_PARENT_SMALL = 18,         /* OPEN_PARENT_SMALL  */
  YYSYMBOL_CLOSED_PARENT_SMALL = 19,       /* CLOSED_PARENT_SMALL  */
  YYSYMBOL_OPEN_PARENT_BIG = 20,           /* OPEN_PARENT_BIG  */
  YYSYMBOL_CLOSED_PARENT_BIG = 21,         /* CLOSED_PARENT_BIG  */
  YYSYMBOL_SEMICOLON = 22,                 /* SEMICOLON  */
  YYSYMBOL_COMMA = 23,                     /* COMMA  */
  YYSYMBOL_DOUBLE_COLON = 24,              /* DOUBLE_COLON  */
  YYSYMBOL_COLON = 25,                     /* COLON  */
  YYSYMBOL_OPEN_PARENT_MED = 26,           /* OPEN_PARENT_MED  */
  YYSYMBOL_CLOSED_PARENT_MED = 27,         /* CLOSED_PARENT_MED  */
  YYSYMBOL_TWO_DOTS = 28,                  /* TWO_DOTS  */
  YYSYMBOL_TRIPLE_QUOTATIONS = 29,         /* TRIPLE_QUOTATIONS  */
  YYSYMBOL_STRING_CONTENTS = 30,           /* STRING_CONTENTS  */
  YYSYMBOL_MISMATCH = 31,                  /* MISMATCH  */
  YYSYMBOL_YYACCEPT = 32,                  /* $accept  */
  YYSYMBOL_model = 33,                     /* model  */
  YYSYMBOL_predicate_item_list = 34,       /* predicate_item_list  */
  YYSYMBOL_predicate_item = 35,            /* predicate_item  */
  YYSYMBOL_predicate_params = 36,          /* predicate_params  */
  YYSYMBOL_predicate_param = 37,           /* predicate_param  */
  YYSYMBOL_par_type = 38,                  /* par_type  */
  YYSYMBOL_array_var_type = 39,            /* array_var_type  */
  YYSYMBOL_index_set = 40,                 /* index_set  */
  YYSYMBOL_basic_var_type = 41,            /* basic_var_type  */
  YYSYMBOL_int_literal_list = 42,          /* int_literal_list  */
  YYSYMBOL_basic_pred_param_type = 43,     /* basic_pred_param_type  */
  YYSYMBOL_pred_param_type = 44,           /* pred_param_type  */
  YYSYMBOL_basic_literal_expr = 45,        /* basic_literal_expr  */
  YYSYMBOL_set_literal = 46,               /* set_literal  */
  YYSYMBOL_basic_expr = 47,                /* basic_expr  */
  YYSYMBOL_expr = 48,                      /* expr  */
  YYSYMBOL_par_expr = 49,                  /* par_expr  */
  YYSYMBOL_array_literal = 50,             /* array_literal  */
  YYSYMBOL_array_item_list = 51,           /* array_item_list  */
  YYSYMBOL_par_array_literal = 52,         /* par_array_literal  */
  YYSYMBOL_par_array_item_list = 53,       /* par_array_item_list  */
  YYSYMBOL_par_decl_item_list = 54,        /* par_decl_item_list  */
  YYSYMBOL_par_decl_item = 55,             /* par_decl_item  */
  YYSYMBOL_var_decl_item_list = 56,        /* var_decl_item_list  */
  YYSYMBOL_var_decl_item = 57,             /* var_decl_item  */
  YYSYMBOL_constraint_item_list = 58,      /* constraint_item_list  */
  YYSYMBOL_constraint_item = 59,           /* constraint_item  */
  YYSYMBOL_args_list = 60,                 /* args_list  */
  YYSYMBOL_solve_item = 61,                /* solve_item  */
  YYSYMBOL_annotations = 62,               /* annotations  */
  YYSYMBOL_annotation = 63,                /* annotation  */
  YYSYMBOL_anno_list = 64,                 /* anno_list  */
  YYSYMBOL_ann_expr = 65,                  /* ann_expr  */
  YYSYMBOL_basic_anno_list = 66            /* basic_anno_list  */
};
typedef enum yysymbol_kind_t yysymbol_kind_t;


/* Default (constant) value used for initialization for null
   right-hand sides.  Unlike the standard yacc.c template, here we set
   the default value of $$ to a zeroed-out value.  Since the default
   value is undefined, this behavior is technically correct.  */
static YYSTYPE yyval_default;



#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef short
# undef short
#endif

/* On compilers that do not define __PTRDIFF_MAX__ etc., make sure
   <limits.h> and (if available) <stdint.h> are included
   so that the code can choose integer types of a good width.  */

#ifndef __PTRDIFF_MAX__
# include <limits.h> /* INFRINGES ON USER NAME SPACE */
# if defined __STDC_VERSION__ && 199901 <= __STDC_VERSION__
#  include <stdint.h> /* INFRINGES ON USER NAME SPACE */
#  define YY_STDINT_H
# endif
#endif

/* Narrow types that promote to a signed type and that can represent a
   signed or unsigned integer of at least N bits.  In tables they can
   save space and decrease cache pressure.  Promoting to a signed type
   helps avoid bugs in integer arithmetic.  */

#ifdef __INT_LEAST8_MAX__
typedef __INT_LEAST8_TYPE__ yytype_int8;
#elif defined YY_STDINT_H
typedef int_least8_t yytype_int8;
#else
typedef signed char yytype_int8;
#endif

#ifdef __INT_LEAST16_MAX__
typedef __INT_LEAST16_TYPE__ yytype_int16;
#elif defined YY_STDINT_H
typedef int_least16_t yytype_int16;
#else
typedef short yytype_int16;
#endif

/* Work around bug in HP-UX 11.23, which defines these macros
   incorrectly for preprocessor constants.  This workaround can likely
   be removed in 2023, as HPE has promised support for HP-UX 11.23
   (aka HP-UX 11i v2) only through the end of 2022; see Table 2 of
   <https://h20195.www2.hpe.com/V2/getpdf.aspx/4AA4-7673ENW.pdf>.  */
#ifdef __hpux
# undef UINT_LEAST8_MAX
# undef UINT_LEAST16_MAX
# define UINT_LEAST8_MAX 255
# define UINT_LEAST16_MAX 65535
#endif

#if defined __UINT_LEAST8_MAX__ && __UINT_LEAST8_MAX__ <= __INT_MAX__
typedef __UINT_LEAST8_TYPE__ yytype_uint8;
#elif (!defined __UINT_LEAST8_MAX__ && defined YY_STDINT_H \
       && UINT_LEAST8_MAX <= INT_MAX)
typedef uint_least8_t yytype_uint8;
#elif !defined __UINT_LEAST8_MAX__ && UCHAR_MAX <= INT_MAX
typedef unsigned char yytype_uint8;
#else
typedef short yytype_uint8;
#endif

#if defined __UINT_LEAST16_MAX__ && __UINT_LEAST16_MAX__ <= __INT_MAX__
typedef __UINT_LEAST16_TYPE__ yytype_uint16;
#elif (!defined __UINT_LEAST16_MAX__ && defined YY_STDINT_H \
       && UINT_LEAST16_MAX <= INT_MAX)
typedef uint_least16_t yytype_uint16;
#elif !defined __UINT_LEAST16_MAX__ && USHRT_MAX <= INT_MAX
typedef unsigned short yytype_uint16;
#else
typedef int yytype_uint16;
#endif
#ifndef YYPTRDIFF_T
# if defined __PTRDIFF_TYPE__ && defined __PTRDIFF_MAX__
#  define YYPTRDIFF_T __PTRDIFF_TYPE__
#  define YYPTRDIFF_MAXIMUM __PTRDIFF_MAX__
# elif defined PTRDIFF_MAX
#  ifndef ptrdiff_t
#   include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  endif
#  define YYPTRDIFF_T ptrdiff_t
#  define YYPTRDIFF_MAXIMUM PTRDIFF_MAX
# else
#  define YYPTRDIFF_T long
#  define YYPTRDIFF_MAXIMUM LONG_MAX
# endif
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif defined __STDC_VERSION__ && 199901 <= __STDC_VERSION__
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned
# endif
#endif

#define YYSIZE_MAXIMUM                                  \
  YY_CAST (YYPTRDIFF_T,                                 \
           (YYPTRDIFF_MAXIMUM < YY_CAST (YYSIZE_T, -1)  \
            ? YYPTRDIFF_MAXIMUM                         \
            : YY_CAST (YYSIZE_T, -1)))

#define YYSIZEOF(X) YY_CAST (YYPTRDIFF_T, sizeof (X))


#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(Msgid) dgettext ("bison-runtime", Msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(Msgid) Msgid
# endif
#endif


#ifndef YYFREE
# define YYFREE free
#endif
#ifndef YYMALLOC
# define YYMALLOC malloc
#endif
#ifndef YYREALLOC
# define YYREALLOC realloc
#endif

#ifdef __cplusplus
  typedef bool yybool;
# define yytrue true
# define yyfalse false
#else
  /* When we move to stdbool, get rid of the various casts to yybool.  */
  typedef signed char yybool;
# define yytrue 1
# define yyfalse 0
#endif

#ifndef YYSETJMP
# include <setjmp.h>
# define YYJMP_BUF jmp_buf
# define YYSETJMP(Env) setjmp (Env)
/* Pacify Clang and ICC.  */
# define YYLONGJMP(Env, Val)                    \
 do {                                           \
   longjmp (Env, Val);                          \
   YY_ASSERT (0);                               \
 } while (yyfalse)
#endif

#ifndef YY_ATTRIBUTE_PURE
# if defined __GNUC__ && 2 < __GNUC__ + (96 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_PURE __attribute__ ((__pure__))
# else
#  define YY_ATTRIBUTE_PURE
# endif
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# if defined __GNUC__ && 2 < __GNUC__ + (7 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_UNUSED __attribute__ ((__unused__))
# else
#  define YY_ATTRIBUTE_UNUSED
# endif
#endif

/* The _Noreturn keyword of C11.  */
#ifndef _Noreturn
# if (defined __cplusplus \
      && ((201103 <= __cplusplus && !(__GNUC__ == 4 && __GNUC_MINOR__ == 7)) \
          || (defined _MSC_VER && 1900 <= _MSC_VER)))
#  define _Noreturn [[noreturn]]
# elif ((!defined __cplusplus || defined __clang__) \
        && (201112 <= (defined __STDC_VERSION__ ? __STDC_VERSION__ : 0) \
            || (!defined __STRICT_ANSI__ \
                && (4 < __GNUC__ + (7 <= __GNUC_MINOR__) \
                    || (defined __apple_build_version__ \
                        ? 6000000 <= __apple_build_version__ \
                        : 3 < __clang_major__ + (5 <= __clang_minor__))))))
   /* _Noreturn works as-is.  */
# elif (2 < __GNUC__ + (8 <= __GNUC_MINOR__) || defined __clang__ \
        || 0x5110 <= __SUNPRO_C)
#  define _Noreturn __attribute__ ((__noreturn__))
# elif 1200 <= (defined _MSC_VER ? _MSC_VER : 0)
#  define _Noreturn __declspec (noreturn)
# else
#  define _Noreturn
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YY_USE(E) ((void) (E))
#else
# define YY_USE(E) /* empty */
#endif

/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
#if defined __GNUC__ && ! defined __ICC && 406 <= __GNUC__ * 100 + __GNUC_MINOR__
# if __GNUC__ * 100 + __GNUC_MINOR__ < 407
#  define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                           \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")
# else
#  define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                           \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")              \
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# endif
# define YY_IGNORE_MAYBE_UNINITIALIZED_END      \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif

#if defined __cplusplus && defined __GNUC__ && ! defined __ICC && 6 <= __GNUC__
# define YY_IGNORE_USELESS_CAST_BEGIN                          \
    _Pragma ("GCC diagnostic push")                            \
    _Pragma ("GCC diagnostic ignored \"-Wuseless-cast\"")
# define YY_IGNORE_USELESS_CAST_END            \
    _Pragma ("GCC diagnostic pop")
#endif
#ifndef YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_END
#endif


#define YY_ASSERT(E) ((void) (0 && (E)))

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  6
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   158

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  32
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  35
/* YYNRULES -- Number of rules.  */
#define YYNRULES  72
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  155
/* YYMAXRHS -- Maximum number of symbols on right-hand side of rule.  */
#define YYMAXRHS 7
/* YYMAXLEFT -- Maximum number of symbols to the left of a handle
   accessed by $0, $-1, etc., in any rule.  */
#define YYMAXLEFT 0

/* YYMAXUTOK -- Last valid token kind.  */
#define YYMAXUTOK   286

/* YYTRANSLATE(TOKEN-NUM) -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, with out-of-bounds checking.  */
#define YYTRANSLATE(YYX)                                \
  (0 <= (YYX) && (YYX) <= YYMAXUTOK                     \
   ? YY_CAST (yysymbol_kind_t, yytranslate[YYX])        \
   : YYSYMBOL_YYUNDEF)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex.  */
static const yytype_int8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31
};

#if YYDEBUG
/* YYRLINE[YYN] -- source line where rule number YYN was defined.  */
static const yytype_int16 yyrline[] =
{
       0,   281,   281,   302,   306,   314,   321,   326,   333,   342,
     350,   363,   370,   378,   379,   383,   387,   394,   401,   405,
     409,   414,   422,   425,   428,   432,   440,   446,   447,   448,
     452,   456,   463,   464,   468,   472,   479,   482,   488,   492,
     497,   505,   511,   517,   522,   531,   535,   543,   549,   554,
     562,   577,   592,   609,   615,   624,   637,   642,   650,   651,
     652,   656,   660,   668,   671,   677,   681,   689,   692,   695,
     701,   704,   707
};
#endif

#define YYPACT_NINF (-124)
#define YYTABLE_NINF (-1)

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
static const yytype_int16 yypact[] =
{
      44,    37,    79,    88,    44,    54,  -124,  -124,    63,    68,
      91,    95,  -124,     4,    87,    89,    77,     5,    81,    82,
       8,  -124,  -124,  -124,    76,    -5,    90,    85,  -124,  -124,
      86,    84,    83,    96,    87,  -124,   104,    92,     2,    99,
     100,   101,  -124,    93,  -124,   103,    67,  -124,    98,  -124,
       4,   105,   107,   113,    48,    97,    29,   110,  -124,   102,
     102,   109,    72,  -124,  -124,  -124,  -124,    11,  -124,  -124,
    -124,  -124,   125,  -124,   106,    19,    45,  -124,  -124,   108,
    -124,   119,   111,     2,  -124,   115,   116,    56,    32,   114,
      61,    61,  -124,  -124,   117,  -124,    16,   118,  -124,   130,
     122,  -124,   120,   102,   121,    61,  -124,  -124,    61,  -124,
    -124,  -124,  -124,    10,  -124,   124,   126,  -124,    45,  -124,
    -124,  -124,  -124,    41,  -124,   127,   128,  -124,    14,   102,
      32,  -124,  -124,  -124,    41,  -124,  -124,  -124,    47,  -124,
    -124,    61,  -124,   129,  -124,    59,  -124,  -124,    41,  -124,
    -124,    41,  -124,  -124,  -124
};

/* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
   Performed when YYTABLE does not specify something else to do.  Zero
   means the default is an error.  */
static const yytype_int8 yydefact[] =
{
       3,     0,     0,    45,     3,     0,     1,     9,     0,     0,
       0,    45,     4,     0,     0,     0,     0,     0,     0,     0,
       0,    48,    46,    22,     0,     0,     0,     7,    23,    26,
       0,     0,     0,     0,     0,    13,     0,     0,    18,     0,
       0,     0,    49,     0,    53,     0,     0,    19,     0,     5,
       0,     0,     0,     0,     0,     0,     0,     0,    15,    61,
      61,     0,     0,    54,     2,    24,    20,    18,    25,     6,
       8,    12,     0,    27,    28,    18,    42,    36,    29,     0,
      37,     0,     0,    18,    14,     0,     0,     0,     0,     0,
       0,     0,    21,    10,     0,    31,    42,     0,    47,     0,
       0,    17,    63,    61,     0,     0,    51,    33,     0,    32,
      34,    56,    35,     0,    58,     0,     0,    30,    42,    44,
      41,    11,    16,     0,    62,     0,     0,    39,     0,    61,
       0,    60,    59,    43,    70,    67,    68,    64,     0,    52,
      50,     0,    38,     0,    57,     0,    69,    65,     0,    40,
      55,    70,    72,    66,    71
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -124,  -124,   136,  -124,    94,  -124,  -124,  -124,   123,   -12,
     -32,  -124,  -124,   -54,  -124,   -87,    12,  -124,    39,  -124,
    -124,   -91,   141,  -124,  -124,   133,  -124,   112,  -124,  -124,
     -58,    69,    -7,  -123,     7
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_uint8 yydefgoto[] =
{
       0,     2,     3,     4,    26,    27,     9,    18,    32,    19,
      48,    29,    30,   109,    78,   110,   111,    79,   112,   128,
      80,    97,    10,    11,    20,    21,    43,    44,   113,    64,
      86,   136,   137,   138,   146
};

/* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule whose
   number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_uint8 yytable[] =
{
      77,    28,    87,   115,   116,   119,    58,    23,    35,    17,
      46,   145,    16,    17,    36,    41,    47,    46,   126,    24,
      37,   127,    96,    47,    25,    38,    46,   133,   145,   129,
      73,    74,    47,   130,    46,    92,    75,   141,    28,   118,
      47,   142,    96,    95,    82,   124,    73,    74,   107,    83,
       1,   101,    75,     5,   149,    73,    74,   102,   108,    73,
      74,    75,    73,    74,    96,    75,   147,   134,    75,   135,
     148,   143,    13,   105,    76,    73,    74,   107,   106,     6,
     135,    75,   151,    89,    90,    91,   152,   121,    66,    14,
      67,     7,     8,    15,   135,    16,    17,   135,     7,     8,
      41,    62,    31,    34,    45,    33,    39,    40,    50,    49,
      53,    51,    52,    54,    56,    59,    60,    61,    65,    68,
      57,    70,    71,    72,    81,    84,    85,    88,    93,    99,
      98,   102,   117,   104,    94,    17,   114,   122,   123,   100,
      12,   153,   144,   125,    69,   120,   131,   108,   132,   139,
     140,   150,    22,    42,   103,    63,     0,    55,   154
};

static const yytype_int16 yycheck[] =
{
      54,    13,    60,    90,    91,    96,    38,     3,     3,     5,
      15,   134,     4,     5,     9,     7,    21,    15,   105,    15,
      15,   108,    76,    21,    20,    20,    15,   118,   151,    19,
      14,    15,    21,    23,    15,    67,    20,    23,    50,    23,
      21,    27,    96,    75,    15,   103,    14,    15,    16,    20,
       6,    83,    20,    16,   141,    14,    15,    16,    26,    14,
      15,    20,    14,    15,   118,    20,    19,    26,    20,   123,
      23,   129,    18,    17,    26,    14,    15,    16,    22,     0,
     134,    20,    23,    11,    12,    13,    27,    99,    21,    26,
      23,     3,     4,    25,   148,     4,     5,   151,     3,     4,
       7,     8,    15,    26,    28,    16,    25,    25,    23,    19,
      27,    25,    28,    17,    10,    16,    16,    16,    15,    21,
      28,    16,    15,    10,    27,    15,    24,    18,     3,    10,
      22,    16,    15,    17,    28,     5,    22,    15,    18,    28,
       4,   148,   130,   104,    50,    27,    22,    26,    22,    22,
      22,    22,    11,    20,    85,    43,    -1,    34,   151
};

/* YYSTOS[STATE-NUM] -- The symbol kind of the accessing symbol of
   state STATE-NUM.  */
static const yytype_int8 yystos[] =
{
       0,     6,    33,    34,    35,    16,     0,     3,     4,    38,
      54,    55,    34,    18,    26,    25,     4,     5,    39,    41,
      56,    57,    54,     3,    15,    20,    36,    37,    41,    43,
      44,    15,    40,    16,    26,     3,     9,    15,    20,    25,
      25,     7,    57,    58,    59,    28,    15,    21,    42,    19,
      23,    25,    28,    27,    17,    40,    10,    28,    42,    16,
      16,    16,     8,    59,    61,    15,    21,    23,    21,    36,
      16,    15,    10,    14,    15,    20,    26,    45,    46,    49,
      52,    27,    15,    20,    15,    24,    62,    62,    18,    11,
      12,    13,    42,     3,    28,    42,    45,    53,    22,    10,
      28,    42,    16,    63,    17,    17,    22,    16,    26,    45,
      47,    48,    50,    60,    22,    47,    47,    15,    23,    53,
      27,    41,    15,    18,    62,    50,    47,    47,    51,    19,
      23,    22,    22,    53,    26,    45,    63,    64,    65,    22,
      22,    23,    27,    62,    48,    65,    66,    19,    23,    47,
      22,    23,    27,    64,    66
};

/* YYR1[RULE-NUM] -- Symbol kind of the left-hand side of rule RULE-NUM.  */
static const yytype_int8 yyr1[] =
{
       0,    32,    33,    34,    34,    35,    36,    36,    37,    38,
      38,    39,    40,    41,    41,    41,    41,    41,    42,    42,
      42,    42,    43,    43,    43,    43,    44,    45,    45,    45,
      46,    46,    47,    47,    48,    48,    49,    49,    50,    51,
      51,    52,    53,    53,    53,    54,    54,    55,    56,    56,
      57,    57,    57,    58,    58,    59,    60,    60,    61,    61,
      61,    62,    62,    63,    63,    64,    64,    65,    65,    65,
      66,    66,    66
};

/* YYR2[RULE-NUM] -- Number of symbols on the right-hand side of rule RULE-NUM.  */
static const yytype_int8 yyr2[] =
{
       0,     2,     5,     0,     2,     5,     3,     1,     3,     1,
       6,     6,     3,     2,     4,     3,     6,     5,     0,     1,
       2,     3,     1,     1,     3,     3,     1,     1,     1,     1,
       3,     2,     1,     1,     1,     1,     1,     1,     3,     1,
       3,     3,     0,     3,     2,     0,     2,     6,     1,     2,
       7,     5,     7,     1,     2,     7,     1,     3,     3,     4,
       4,     0,     3,     1,     3,     2,     3,     1,     1,     2,
       0,     3,     2
};


/* YYDPREC[RULE-NUM] -- Dynamic precedence of rule #RULE-NUM (0 if none).  */
static const yytype_int8 yydprec[] =
{
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0
};

/* YYMERGER[RULE-NUM] -- Index of merging function for rule #RULE-NUM.  */
static const yytype_int8 yymerger[] =
{
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0
};

/* YYIMMEDIATE[RULE-NUM] -- True iff rule #RULE-NUM is not to be deferred, as
   in the case of predicates.  */
static const yybool yyimmediate[] =
{
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0
};

/* YYCONFLP[YYPACT[STATE-NUM]] -- Pointer into YYCONFL of start of
   list of conflicting reductions corresponding to action entry for
   state STATE-NUM in yytable.  0 means no conflicts.  The list in
   yyconfl is terminated by a rule number of 0.  */
static const yytype_int8 yyconflp[] =
{
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     5,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     7,     0,     0,     0,
       0,     0,     9,     0,    11,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     1,     0,     0,     0,     0,     0,     0,     3,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0
};

/* YYCONFL[I] -- lists of conflicting rule numbers, each terminated by
   0, pointed into by YYCONFLP.  */
static const short yyconfl[] =
{
       0,    45,     0,    45,     0,    18,     0,    18,     0,    18,
       0,    18,     0
};



YYSTYPE yylval;

int yynerrs;
int yychar;

enum { YYENOMEM = -2 };

typedef enum { yyok, yyaccept, yyabort, yyerr, yynomem } YYRESULTTAG;

#define YYCHK(YYE)                              \
  do {                                          \
    YYRESULTTAG yychk_flag = YYE;               \
    if (yychk_flag != yyok)                     \
      return yychk_flag;                        \
  } while (0)

/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   SIZE_MAX < YYMAXDEPTH * sizeof (GLRStackItem)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif

/* Minimum number of free items on the stack allowed after an
   allocation.  This is to allow allocation and initialization
   to be completed by functions that call yyexpandGLRStack before the
   stack is expanded, thus insuring that all necessary pointers get
   properly redirected to new data.  */
#define YYHEADROOM 2

#ifndef YYSTACKEXPANDABLE
#  define YYSTACKEXPANDABLE 1
#endif

#if YYSTACKEXPANDABLE
# define YY_RESERVE_GLRSTACK(Yystack)                   \
  do {                                                  \
    if (Yystack->yyspaceLeft < YYHEADROOM)              \
      yyexpandGLRStack (Yystack);                       \
  } while (0)
#else
# define YY_RESERVE_GLRSTACK(Yystack)                   \
  do {                                                  \
    if (Yystack->yyspaceLeft < YYHEADROOM)              \
      yyMemoryExhausted (Yystack);                      \
  } while (0)
#endif

/** State numbers. */
typedef int yy_state_t;

/** Rule numbers. */
typedef int yyRuleNum;

/** Item references. */
typedef short yyItemNum;

typedef struct yyGLRState yyGLRState;
typedef struct yyGLRStateSet yyGLRStateSet;
typedef struct yySemanticOption yySemanticOption;
typedef union yyGLRStackItem yyGLRStackItem;
typedef struct yyGLRStack yyGLRStack;

struct yyGLRState
{
  /** Type tag: always true.  */
  yybool yyisState;
  /** Type tag for yysemantics.  If true, yyval applies, otherwise
   *  yyfirstVal applies.  */
  yybool yyresolved;
  /** Number of corresponding LALR(1) machine state.  */
  yy_state_t yylrState;
  /** Preceding state in this stack */
  yyGLRState* yypred;
  /** Source position of the last token produced by my symbol */
  YYPTRDIFF_T yyposn;
  union {
    /** First in a chain of alternative reductions producing the
     *  nonterminal corresponding to this state, threaded through
     *  yynext.  */
    yySemanticOption* yyfirstVal;
    /** Semantic value for this state.  */
    YYSTYPE yyval;
  } yysemantics;
};

struct yyGLRStateSet
{
  yyGLRState** yystates;
  /** During nondeterministic operation, yylookaheadNeeds tracks which
   *  stacks have actually needed the current lookahead.  During deterministic
   *  operation, yylookaheadNeeds[0] is not maintained since it would merely
   *  duplicate yychar != YYEMPTY.  */
  yybool* yylookaheadNeeds;
  YYPTRDIFF_T yysize;
  YYPTRDIFF_T yycapacity;
};

struct yySemanticOption
{
  /** Type tag: always false.  */
  yybool yyisState;
  /** Rule number for this reduction */
  yyRuleNum yyrule;
  /** The last RHS state in the list of states to be reduced.  */
  yyGLRState* yystate;
  /** The lookahead for this reduction.  */
  int yyrawchar;
  YYSTYPE yyval;
  /** Next sibling in chain of options.  To facilitate merging,
   *  options are chained in decreasing order by address.  */
  yySemanticOption* yynext;
};

/** Type of the items in the GLR stack.  The yyisState field
 *  indicates which item of the union is valid.  */
union yyGLRStackItem {
  yyGLRState yystate;
  yySemanticOption yyoption;
};

struct yyGLRStack {
  int yyerrState;


  YYJMP_BUF yyexception_buffer;
  yyGLRStackItem* yyitems;
  yyGLRStackItem* yynextFree;
  YYPTRDIFF_T yyspaceLeft;
  yyGLRState* yysplitPoint;
  yyGLRState* yylastDeleted;
  yyGLRStateSet yytops;
};

#if YYSTACKEXPANDABLE
static void yyexpandGLRStack (yyGLRStack* yystackp);
#endif

_Noreturn static void
yyFail (yyGLRStack* yystackp, const char* yymsg)
{
  if (yymsg != YY_NULLPTR)
    yyerror (yymsg);
  YYLONGJMP (yystackp->yyexception_buffer, 1);
}

_Noreturn static void
yyMemoryExhausted (yyGLRStack* yystackp)
{
  YYLONGJMP (yystackp->yyexception_buffer, 2);
}

/** Accessing symbol of state YYSTATE.  */
static inline yysymbol_kind_t
yy_accessing_symbol (yy_state_t yystate)
{
  return YY_CAST (yysymbol_kind_t, yystos[yystate]);
}

#if YYDEBUG || 0
/* The user-facing name of the symbol whose (internal) number is
   YYSYMBOL.  No bounds checking.  */
static const char *yysymbol_name (yysymbol_kind_t yysymbol) YY_ATTRIBUTE_UNUSED;

/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "\"end of file\"", "error", "\"invalid token\"", "BASIC_PAR_TYPE",
  "ARRAY", "VAR", "PREDICATE", "CONSTRAINT", "SOLVE", "SET", "OF",
  "SOLVE_SATISFY", "SOLVE_MAXIMIZE", "SOLVE_MINIMIZE", "BOOL_LITERAL",
  "INT_LITERAL", "VAR_PAR_IDENTIFIER", "EQUALS", "OPEN_PARENT_SMALL",
  "CLOSED_PARENT_SMALL", "OPEN_PARENT_BIG", "CLOSED_PARENT_BIG",
  "SEMICOLON", "COMMA", "DOUBLE_COLON", "COLON", "OPEN_PARENT_MED",
  "CLOSED_PARENT_MED", "TWO_DOTS", "TRIPLE_QUOTATIONS", "STRING_CONTENTS",
  "MISMATCH", "$accept", "model", "predicate_item_list", "predicate_item",
  "predicate_params", "predicate_param", "par_type", "array_var_type",
  "index_set", "basic_var_type", "int_literal_list",
  "basic_pred_param_type", "pred_param_type", "basic_literal_expr",
  "set_literal", "basic_expr", "expr", "par_expr", "array_literal",
  "array_item_list", "par_array_literal", "par_array_item_list",
  "par_decl_item_list", "par_decl_item", "var_decl_item_list",
  "var_decl_item", "constraint_item_list", "constraint_item", "args_list",
  "solve_item", "annotations", "annotation", "anno_list", "ann_expr",
  "basic_anno_list", YY_NULLPTR
};

static const char *
yysymbol_name (yysymbol_kind_t yysymbol)
{
  return yytname[yysymbol];
}
#endif

/** Left-hand-side symbol for rule #YYRULE.  */
static inline yysymbol_kind_t
yylhsNonterm (yyRuleNum yyrule)
{
  return YY_CAST (yysymbol_kind_t, yyr1[yyrule]);
}

#if YYDEBUG

# ifndef YYFPRINTF
#  define YYFPRINTF fprintf
# endif

# define YY_FPRINTF                             \
  YY_IGNORE_USELESS_CAST_BEGIN YY_FPRINTF_

# define YY_FPRINTF_(Args)                      \
  do {                                          \
    YYFPRINTF Args;                             \
    YY_IGNORE_USELESS_CAST_END                  \
  } while (0)

# define YY_DPRINTF                             \
  YY_IGNORE_USELESS_CAST_BEGIN YY_DPRINTF_

# define YY_DPRINTF_(Args)                      \
  do {                                          \
    if (yydebug)                                \
      YYFPRINTF Args;                           \
    YY_IGNORE_USELESS_CAST_END                  \
  } while (0)





/*-----------------------------------.
| Print this symbol's value on YYO.  |
`-----------------------------------*/

static void
yy_symbol_value_print (FILE *yyo,
                       yysymbol_kind_t yykind, YYSTYPE const * const yyvaluep)
{
  FILE *yyoutput = yyo;
  YY_USE (yyoutput);
  if (!yyvaluep)
    return;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YY_USE (yykind);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}


/*---------------------------.
| Print this symbol on YYO.  |
`---------------------------*/

static void
yy_symbol_print (FILE *yyo,
                 yysymbol_kind_t yykind, YYSTYPE const * const yyvaluep)
{
  YYFPRINTF (yyo, "%s %s (",
             yykind < YYNTOKENS ? "token" : "nterm", yysymbol_name (yykind));

  yy_symbol_value_print (yyo, yykind, yyvaluep);
  YYFPRINTF (yyo, ")");
}

# define YY_SYMBOL_PRINT(Title, Kind, Value, Location)                  \
  do {                                                                  \
    if (yydebug)                                                        \
      {                                                                 \
        YY_FPRINTF ((stderr, "%s ", Title));                            \
        yy_symbol_print (stderr, Kind, Value);        \
        YY_FPRINTF ((stderr, "\n"));                                    \
      }                                                                 \
  } while (0)

static inline void
yy_reduce_print (yybool yynormal, yyGLRStackItem* yyvsp, YYPTRDIFF_T yyk,
                 yyRuleNum yyrule);

# define YY_REDUCE_PRINT(Args)          \
  do {                                  \
    if (yydebug)                        \
      yy_reduce_print Args;             \
  } while (0)

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;

static void yypstack (yyGLRStack* yystackp, YYPTRDIFF_T yyk)
  YY_ATTRIBUTE_UNUSED;
static void yypdumpstack (yyGLRStack* yystackp)
  YY_ATTRIBUTE_UNUSED;

#else /* !YYDEBUG */

# define YY_DPRINTF(Args) do {} while (yyfalse)
# define YY_SYMBOL_PRINT(Title, Kind, Value, Location)
# define YY_REDUCE_PRINT(Args)

#endif /* !YYDEBUG */



/** Fill in YYVSP[YYLOW1 .. YYLOW0-1] from the chain of states starting
 *  at YYVSP[YYLOW0].yystate.yypred.  Leaves YYVSP[YYLOW1].yystate.yypred
 *  containing the pointer to the next state in the chain.  */
static void yyfillin (yyGLRStackItem *, int, int) YY_ATTRIBUTE_UNUSED;
static void
yyfillin (yyGLRStackItem *yyvsp, int yylow0, int yylow1)
{
  int i;
  yyGLRState *s = yyvsp[yylow0].yystate.yypred;
  for (i = yylow0-1; i >= yylow1; i -= 1)
    {
#if YYDEBUG
      yyvsp[i].yystate.yylrState = s->yylrState;
#endif
      yyvsp[i].yystate.yyresolved = s->yyresolved;
      if (s->yyresolved)
        yyvsp[i].yystate.yysemantics.yyval = s->yysemantics.yyval;
      else
        /* The effect of using yyval or yyloc (in an immediate rule) is
         * undefined.  */
        yyvsp[i].yystate.yysemantics.yyfirstVal = YY_NULLPTR;
      s = yyvsp[i].yystate.yypred = s->yypred;
    }
}


/** If yychar is empty, fetch the next token.  */
static inline yysymbol_kind_t
yygetToken (int *yycharp)
{
  yysymbol_kind_t yytoken;
  if (*yycharp == YYEMPTY)
    {
      YY_DPRINTF ((stderr, "Reading a token\n"));
      *yycharp = yylex ();
    }
  if (*yycharp <= YYEOF)
    {
      *yycharp = YYEOF;
      yytoken = YYSYMBOL_YYEOF;
      YY_DPRINTF ((stderr, "Now at end of input.\n"));
    }
  else
    {
      yytoken = YYTRANSLATE (*yycharp);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }
  return yytoken;
}

/* Do nothing if YYNORMAL or if *YYLOW <= YYLOW1.  Otherwise, fill in
 * YYVSP[YYLOW1 .. *YYLOW-1] as in yyfillin and set *YYLOW = YYLOW1.
 * For convenience, always return YYLOW1.  */
static inline int yyfill (yyGLRStackItem *, int *, int, yybool)
     YY_ATTRIBUTE_UNUSED;
static inline int
yyfill (yyGLRStackItem *yyvsp, int *yylow, int yylow1, yybool yynormal)
{
  if (!yynormal && yylow1 < *yylow)
    {
      yyfillin (yyvsp, *yylow, yylow1);
      *yylow = yylow1;
    }
  return yylow1;
}

/** Perform user action for rule number YYN, with RHS length YYRHSLEN,
 *  and top stack item YYVSP.  YYLVALP points to place to put semantic
 *  value ($$), and yylocp points to place for location information
 *  (@$).  Returns yyok for normal return, yyaccept for YYACCEPT,
 *  yyerr for YYERROR, yyabort for YYABORT, yynomem for YYNOMEM.  */
static YYRESULTTAG
yyuserAction (yyRuleNum yyrule, int yyrhslen, yyGLRStackItem* yyvsp,
              yyGLRStack* yystackp, YYPTRDIFF_T yyk,
              YYSTYPE* yyvalp)
{
  const yybool yynormal YY_ATTRIBUTE_UNUSED = yystackp->yysplitPoint == YY_NULLPTR;
  int yylow = 1;
  YY_USE (yyvalp);
  YY_USE (yyk);
  YY_USE (yyrhslen);
# undef yyerrok
# define yyerrok (yystackp->yyerrState = 0)
# undef YYACCEPT
# define YYACCEPT return yyaccept
# undef YYABORT
# define YYABORT return yyabort
# undef YYNOMEM
# define YYNOMEM return yynomem
# undef YYERROR
# define YYERROR return yyerrok, yyerr
# undef YYRECOVERING
# define YYRECOVERING() (yystackp->yyerrState != 0)
# undef yyclearin
# define yyclearin (yychar = YYEMPTY)
# undef YYFILL
# define YYFILL(N) yyfill (yyvsp, &yylow, (N), yynormal)
# undef YYBACKUP
# define YYBACKUP(Token, Value)                                              \
  return yyerror (YY_("syntax error: cannot back up")),     \
         yyerrok, yyerr

  if (yyrhslen == 0)
    *yyvalp = yyval_default;
  else
    *yyvalp = yyvsp[YYFILL (1-yyrhslen)].yystate.yysemantics.yyval;
  /* If yyk == -1, we are running a deferred action on a temporary
     stack.  In that case, YY_REDUCE_PRINT must not play with YYFILL,
     so pretend the stack is "normal". */
  YY_REDUCE_PRINT ((yynormal || yyk == -1, yyvsp, yyk, yyrule));
  switch (yyrule)
    {
  case 2: /* model: predicate_item_list par_decl_item_list var_decl_item_list constraint_item_list solve_item  */
#line 285 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
               {
        if(!(((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-4)].yystate.yysemantics.yyval.predicate_vector_attr))->empty()))
            for(auto elem : *((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-4)].yystate.yysemantics.yyval.predicate_vector_attr)))
                parsing_result->emplace_back(elem);
        if(!(((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-3)].yystate.yysemantics.yyval.parameter_vector_attr))->empty()))
            for(auto elem : *((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-3)].yystate.yysemantics.yyval.parameter_vector_attr)))
                parsing_result->emplace_back(elem);
        if(!(((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-2)].yystate.yysemantics.yyval.variable_vector_attr))->empty()))        
            for(auto elem : *((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-2)].yystate.yysemantics.yyval.variable_vector_attr)))
                parsing_result->emplace_back(elem);
        if(!(((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-1)].yystate.yysemantics.yyval.constraint_vector_attr))->empty()))    
            for(auto elem : *((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-1)].yystate.yysemantics.yyval.constraint_vector_attr)))
                parsing_result->emplace_back(elem);
    }
#line 1173 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 3: /* predicate_item_list: %empty  */
#line 302 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
    {
        vector<Predicate*>* v = new vector<Predicate*>;
        ((*yyvalp).predicate_vector_attr) = v;
    }
#line 1182 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 4: /* predicate_item_list: predicate_item predicate_item_list  */
#line 306 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                        {       
        vector<Predicate*>* v = (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.predicate_vector_attr);
        v->emplace(v->begin(), (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-1)].yystate.yysemantics.yyval.pred_attr));
        ((*yyvalp).predicate_vector_attr) = v;
    }
#line 1192 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 5: /* predicate_item: PREDICATE VAR_PAR_IDENTIFIER OPEN_PARENT_SMALL predicate_params CLOSED_PARENT_SMALL  */
#line 314 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                                                                        {
        Predicate* pred = new Predicate((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-3)].yystate.yysemantics.yyval.str_attr), (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-1)].yystate.yysemantics.yyval.pred_params_attr));
        ((*yyvalp).pred_attr) = pred;
    }
#line 1201 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 6: /* predicate_params: predicate_param COMMA predicate_params  */
#line 321 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                             { 
        vector<PredicateParam*>* p = (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.pred_params_attr);
        p->emplace(p->begin(), (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-2)].yystate.yysemantics.yyval.pred_param_attr));
        ((*yyvalp).pred_params_attr) = p; 
     }
#line 1211 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 7: /* predicate_params: predicate_param  */
#line 326 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                      { 
        vector<PredicateParam*>* p = new vector<PredicateParam*>{(YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.pred_param_attr)};
        ((*yyvalp).pred_params_attr) = p; 
    }
#line 1220 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 8: /* predicate_param: pred_param_type COLON VAR_PAR_IDENTIFIER  */
#line 333 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                             {
        
        PredicateParam* p = new PredicateParam((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.str_attr), (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-2)].yystate.yysemantics.yyval.basic_pred_param_type_attr));
        ((*yyvalp).pred_param_attr) = p;
    }
#line 1230 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 9: /* par_type: BASIC_PAR_TYPE  */
#line 342 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                  {
        if((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.basic_par_type_attr) == BasicParType::INT)
            ((*yyvalp).par_type_attr) = new ParType(BasicParType::INT);
        else if((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.basic_par_type_attr) == BasicParType::BOOL)
            ((*yyvalp).par_type_attr) = new ParType(BasicParType::BOOL);
        else if((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.basic_par_type_attr) == BasicParType::SETOFINT)
            ((*yyvalp).par_type_attr) = new ParType(BasicParType::SETOFINT);
    }
#line 1243 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 10: /* par_type: ARRAY OPEN_PARENT_MED index_set CLOSED_PARENT_MED OF BASIC_PAR_TYPE  */
#line 350 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                                                         {
        if((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.basic_par_type_attr) == BasicParType::INT){
            ParArrayType* p = new ParArrayType(BasicParType::INT, (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-3)].yystate.yysemantics.yyval.int_attr));
            ((*yyvalp).par_type_attr) = new ParType(p);
        } else if((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.basic_par_type_attr) == BasicParType::BOOL){
            ParArrayType* p = new ParArrayType(BasicParType::BOOL, (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-3)].yystate.yysemantics.yyval.int_attr));
            ((*yyvalp).par_type_attr) = new ParType(p);
        }
    }
#line 1257 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 11: /* array_var_type: ARRAY OPEN_PARENT_MED index_set CLOSED_PARENT_MED OF basic_var_type  */
#line 363 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                                                        {
        ((*yyvalp).array_var_type_attr) = new ArrayVarType((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-3)].yystate.yysemantics.yyval.int_attr), (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.basic_var_type_attr));
    }
#line 1265 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 12: /* index_set: INT_LITERAL TWO_DOTS INT_LITERAL  */
#line 370 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                     { 
        if ((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-2)].yystate.yysemantics.yyval.int_attr) != 1){
            yyerror("Error: first term in index set must be 1\n");
        }
        ((*yyvalp).int_attr) = (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.int_attr); }
#line 1275 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 13: /* basic_var_type: VAR BASIC_PAR_TYPE  */
#line 378 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                       { ((*yyvalp).basic_var_type_attr) = new BasicVarType((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.basic_par_type_attr)); }
#line 1281 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 14: /* basic_var_type: VAR INT_LITERAL TWO_DOTS INT_LITERAL  */
#line 379 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                           { 
        IntRangeVarType* v = new IntRangeVarType((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-2)].yystate.yysemantics.yyval.int_attr), (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.int_attr));
        ((*yyvalp).basic_var_type_attr) = new BasicVarType(v); 
    }
#line 1290 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 15: /* basic_var_type: VAR OPEN_PARENT_BIG int_literal_list  */
#line 383 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                           {
        IntSetVarType* v = new IntSetVarType((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.vector_of_int_attr));
        ((*yyvalp).basic_var_type_attr) = new BasicVarType(v);
    }
#line 1299 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 16: /* basic_var_type: VAR SET OF INT_LITERAL TWO_DOTS INT_LITERAL  */
#line 387 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                                  {
        vector<int>* elems = new vector<int>;
        for(int i = (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-2)].yystate.yysemantics.yyval.int_attr); i <= (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.int_attr); i++)
            elems->push_back(i); 
        SetVarType* v = new SetVarType(elems);
        ((*yyvalp).basic_var_type_attr) = new BasicVarType(v); 
    }
#line 1311 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 17: /* basic_var_type: VAR SET OF OPEN_PARENT_BIG int_literal_list  */
#line 394 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                                  {
        SetVarType* v = new SetVarType((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.vector_of_int_attr));
        ((*yyvalp).basic_var_type_attr) = new BasicVarType(v);
    }
#line 1320 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 18: /* int_literal_list: %empty  */
#line 401 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
    {
        vector<int>* v = new vector<int>;
        ((*yyvalp).vector_of_int_attr) = v;
    }
#line 1329 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 19: /* int_literal_list: CLOSED_PARENT_BIG  */
#line 405 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                        {
        vector<int>* v = new vector<int>;
        ((*yyvalp).vector_of_int_attr) = v;
    }
#line 1338 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 20: /* int_literal_list: INT_LITERAL CLOSED_PARENT_BIG  */
#line 409 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                   {
        vector<int>* v = new vector<int>;
        v->emplace(v->begin(), (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-1)].yystate.yysemantics.yyval.int_attr));
        ((*yyvalp).vector_of_int_attr) = v;
    }
#line 1348 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 21: /* int_literal_list: INT_LITERAL COMMA int_literal_list  */
#line 414 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                        {
        vector<int>* v = (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.vector_of_int_attr);
        v->emplace(((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.vector_of_int_attr))->begin(), (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-2)].yystate.yysemantics.yyval.int_attr));
        ((*yyvalp).vector_of_int_attr) = v;
    }
#line 1358 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 22: /* basic_pred_param_type: BASIC_PAR_TYPE  */
#line 422 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                   {
        ((*yyvalp).basic_pred_param_type_attr) = new BasicPredParamType((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.basic_par_type_attr));
    }
#line 1366 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 23: /* basic_pred_param_type: basic_var_type  */
#line 425 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                     {
        ((*yyvalp).basic_pred_param_type_attr) = new BasicPredParamType((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.basic_var_type_attr));
    }
#line 1374 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 24: /* basic_pred_param_type: INT_LITERAL TWO_DOTS INT_LITERAL  */
#line 428 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                       {
        IntRangeVarType* t = new IntRangeVarType((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-2)].yystate.yysemantics.yyval.int_attr), (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.int_attr));
        ((*yyvalp).basic_pred_param_type_attr) = new BasicPredParamType(t);
    }
#line 1383 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 25: /* basic_pred_param_type: OPEN_PARENT_BIG int_literal_list CLOSED_PARENT_BIG  */
#line 432 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                                        {
        IntSetVarType* t = new IntSetVarType((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-1)].yystate.yysemantics.yyval.vector_of_int_attr));
        ((*yyvalp).basic_pred_param_type_attr) = new BasicPredParamType(t);
    }
#line 1392 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 26: /* pred_param_type: basic_pred_param_type  */
#line 440 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                          { ((*yyvalp).basic_pred_param_type_attr) = (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.basic_pred_param_type_attr);}
#line 1398 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 27: /* basic_literal_expr: BOOL_LITERAL  */
#line 446 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                 { ((*yyvalp).basic_literal_expr_attr) = new BasicLiteralExpr((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.bool_attr)); }
#line 1404 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 28: /* basic_literal_expr: INT_LITERAL  */
#line 447 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                  { ((*yyvalp).basic_literal_expr_attr) = new BasicLiteralExpr((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.int_attr)); }
#line 1410 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 29: /* basic_literal_expr: set_literal  */
#line 448 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                  { ((*yyvalp).basic_literal_expr_attr) = new BasicLiteralExpr((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.set_literal_attr)); }
#line 1416 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 30: /* set_literal: INT_LITERAL TWO_DOTS INT_LITERAL  */
#line 452 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                     {
        SetRangeLiteral* v = new SetRangeLiteral((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-2)].yystate.yysemantics.yyval.int_attr), (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.int_attr));
        ((*yyvalp).set_literal_attr) = new SetLiteral(v); 
    }
#line 1425 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 31: /* set_literal: OPEN_PARENT_BIG int_literal_list  */
#line 456 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                       {
        SetSetLiteral* v = new SetSetLiteral((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.vector_of_int_attr));
        ((*yyvalp).set_literal_attr) = new SetLiteral(v);
    }
#line 1434 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 32: /* basic_expr: basic_literal_expr  */
#line 463 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                       { ((*yyvalp).basic_expr_attr) = new BasicExpr((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.basic_literal_expr_attr)); }
#line 1440 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 33: /* basic_expr: VAR_PAR_IDENTIFIER  */
#line 464 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                         { ((*yyvalp).basic_expr_attr) = new BasicExpr((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.str_attr)); }
#line 1446 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 34: /* expr: basic_expr  */
#line 468 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
               {
        BasicExpr* b = (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.basic_expr_attr);
        ((*yyvalp).expr_attr) = new Expr(b);
    }
#line 1455 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 35: /* expr: array_literal  */
#line 472 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                    {
        ArrayLiteral* a = (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.array_literal_attr);
        ((*yyvalp).expr_attr) = new Expr(a);
    }
#line 1464 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 36: /* par_expr: basic_literal_expr  */
#line 479 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                       {
        ((*yyvalp).par_expr_attr) = new ParExpr((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.basic_literal_expr_attr));
    }
#line 1472 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 37: /* par_expr: par_array_literal  */
#line 482 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                       {
        ((*yyvalp).par_expr_attr) = new ParExpr((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.par_array_literal_attr));
    }
#line 1480 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 38: /* array_literal: OPEN_PARENT_MED array_item_list CLOSED_PARENT_MED  */
#line 488 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                                     { ((*yyvalp).array_literal_attr) = (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-1)].yystate.yysemantics.yyval.array_literal_attr); }
#line 1486 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 39: /* array_item_list: basic_expr  */
#line 492 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
               {
        ArrayLiteral* v = new ArrayLiteral();
        v->push_back((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.basic_expr_attr));
        ((*yyvalp).array_literal_attr) = v;
    }
#line 1496 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 40: /* array_item_list: array_item_list COMMA basic_expr  */
#line 497 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                       {
        ArrayLiteral* v = (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-2)].yystate.yysemantics.yyval.array_literal_attr);
        v->push_back((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.basic_expr_attr));
        ((*yyvalp).array_literal_attr) = v;
    }
#line 1506 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 41: /* par_array_literal: OPEN_PARENT_MED par_array_item_list CLOSED_PARENT_MED  */
#line 505 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                                         {
        ((*yyvalp).par_array_literal_attr) = (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-1)].yystate.yysemantics.yyval.par_array_literal_attr);
    }
#line 1514 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 42: /* par_array_item_list: %empty  */
#line 511 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
    {
        vector<BasicLiteralExpr*>* v = new vector<BasicLiteralExpr*>;
        ParArrayLiteral* p = new ParArrayLiteral(v); 
        ((*yyvalp).par_array_literal_attr) = p;

    }
#line 1525 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 43: /* par_array_item_list: basic_literal_expr COMMA par_array_item_list  */
#line 517 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                                   {
        ParArrayLiteral* p = (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.par_array_literal_attr);
        p->elems->emplace(p->elems->begin(), (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-2)].yystate.yysemantics.yyval.basic_literal_expr_attr));
        ((*yyvalp).par_array_literal_attr) = p;
    }
#line 1535 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 44: /* par_array_item_list: basic_literal_expr par_array_item_list  */
#line 522 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                             {
        ParArrayLiteral* p = (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.par_array_literal_attr);
        p->elems->emplace(p->elems->begin(), (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-1)].yystate.yysemantics.yyval.basic_literal_expr_attr));
        ((*yyvalp).par_array_literal_attr) = p;
    }
#line 1545 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 45: /* par_decl_item_list: %empty  */
#line 531 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
    {
        vector<Parameter*>* v = new vector<Parameter*>;
        ((*yyvalp).parameter_vector_attr) = v;
    }
#line 1554 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 46: /* par_decl_item_list: par_decl_item par_decl_item_list  */
#line 535 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                      {
        vector<Parameter*>* v = (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.parameter_vector_attr);
        v->emplace(v->begin(), (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-1)].yystate.yysemantics.yyval.par_attr));
        ((*yyvalp).parameter_vector_attr) = v;
    }
#line 1564 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 47: /* par_decl_item: par_type COLON VAR_PAR_IDENTIFIER EQUALS par_expr SEMICOLON  */
#line 544 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
    {
        ((*yyvalp).par_attr) = new Parameter((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-5)].yystate.yysemantics.yyval.par_type_attr), (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-3)].yystate.yysemantics.yyval.str_attr), (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-1)].yystate.yysemantics.yyval.par_expr_attr));
    }
#line 1572 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 48: /* var_decl_item_list: var_decl_item  */
#line 549 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                  {
        vector<Variable*>* v = new vector<Variable*>;
        v->push_back((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.variable_attr));
        ((*yyvalp).variable_vector_attr) = v;
    }
#line 1582 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 49: /* var_decl_item_list: var_decl_item_list var_decl_item  */
#line 554 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                       {
        vector<Variable*>* v = (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-1)].yystate.yysemantics.yyval.variable_vector_attr);
        v->push_back((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.variable_attr));
        ((*yyvalp).variable_vector_attr) = v;
    }
#line 1592 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 50: /* var_decl_item: basic_var_type COLON VAR_PAR_IDENTIFIER annotations EQUALS basic_expr SEMICOLON  */
#line 562 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                                                                    {
        BasicVar* v = new BasicVar((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-6)].yystate.yysemantics.yyval.basic_var_type_attr), (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-4)].yystate.yysemantics.yyval.str_attr), (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-1)].yystate.yysemantics.yyval.basic_expr_attr), false);
        auto annos = *((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-3)].yystate.yysemantics.yyval.annotation_list_attr));
        for(auto anno : annos){
            if(*anno->name == "output_var")
                v->is_output = true;
        }

        for (auto* annotation : *(YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-3)].yystate.yysemantics.yyval.annotation_list_attr)) {
            delete annotation;
        }
        delete (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-3)].yystate.yysemantics.yyval.annotation_list_attr);

        ((*yyvalp).variable_attr) = new Variable(v);
    }
#line 1612 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 51: /* var_decl_item: basic_var_type COLON VAR_PAR_IDENTIFIER annotations SEMICOLON  */
#line 577 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                                                    {
        BasicVar* v = new BasicVar((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-4)].yystate.yysemantics.yyval.basic_var_type_attr), (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-2)].yystate.yysemantics.yyval.str_attr), false);
        auto annos = *((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-1)].yystate.yysemantics.yyval.annotation_list_attr));
        for(auto anno : annos){
            if(*anno->name == "output_var")
                v->is_output = true;
        }

        for (auto* annotation : *(YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-1)].yystate.yysemantics.yyval.annotation_list_attr)) {
            delete annotation;
        }
        delete (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-1)].yystate.yysemantics.yyval.annotation_list_attr);

        ((*yyvalp).variable_attr) = new Variable(v);
    }
#line 1632 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 52: /* var_decl_item: array_var_type COLON VAR_PAR_IDENTIFIER annotations EQUALS array_literal SEMICOLON  */
#line 592 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                                                                         {
        ArrayVar* v = new ArrayVar((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-6)].yystate.yysemantics.yyval.array_var_type_attr), (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-4)].yystate.yysemantics.yyval.str_attr), (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-1)].yystate.yysemantics.yyval.array_literal_attr));
        auto annos = *((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-3)].yystate.yysemantics.yyval.annotation_list_attr));
        for(auto anno : annos){
            if(*anno->name == "output_array")
                v->is_output = true;
        }

        for (auto* annotation : *(YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-3)].yystate.yysemantics.yyval.annotation_list_attr)) {
            delete annotation;
        }
        delete (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-3)].yystate.yysemantics.yyval.annotation_list_attr);    

        ((*yyvalp).variable_attr) = new Variable(v);
    }
#line 1652 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 53: /* constraint_item_list: constraint_item  */
#line 610 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
    {
        vector<Constraint*>* v = new vector<Constraint*>;
        v->push_back((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.constraint_attr));
        ((*yyvalp).constraint_vector_attr) = v;
    }
#line 1662 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 54: /* constraint_item_list: constraint_item_list constraint_item  */
#line 616 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
    {
        vector<Constraint*>* v = (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-1)].yystate.yysemantics.yyval.constraint_vector_attr);
        v->push_back((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.constraint_attr));
        ((*yyvalp).constraint_vector_attr) = v;
    }
#line 1672 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 55: /* constraint_item: CONSTRAINT VAR_PAR_IDENTIFIER OPEN_PARENT_SMALL args_list CLOSED_PARENT_SMALL annotations SEMICOLON  */
#line 624 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                                                                                        {
        Constraint* c = new Constraint((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-5)].yystate.yysemantics.yyval.str_attr), (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-3)].yystate.yysemantics.yyval.args_list_attr));

        for (auto* annotation : *(YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-1)].yystate.yysemantics.yyval.annotation_list_attr)) {
            delete annotation;
        }
        delete (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-1)].yystate.yysemantics.yyval.annotation_list_attr);

        ((*yyvalp).constraint_attr) = c;
    }
#line 1687 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 56: /* args_list: expr  */
#line 637 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
         {
        ArgsList* a = new ArgsList();
        a->push_back((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.expr_attr));
        ((*yyvalp).args_list_attr) = a;
    }
#line 1697 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 57: /* args_list: args_list COMMA expr  */
#line 642 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                           {
        ArgsList* a = (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-2)].yystate.yysemantics.yyval.args_list_attr);
        a->push_back((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.expr_attr));
        ((*yyvalp).args_list_attr) = a;
    }
#line 1707 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 58: /* solve_item: SOLVE SOLVE_SATISFY SEMICOLON  */
#line 650 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                  { ((*yyvalp).solve_attr) = new Solve(SolveType::ORDINARY); }
#line 1713 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 59: /* solve_item: SOLVE SOLVE_MINIMIZE basic_expr SEMICOLON  */
#line 651 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                                { ((*yyvalp).solve_attr) = new Solve(SolveType::MINIMIZE, (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-1)].yystate.yysemantics.yyval.basic_expr_attr)); }
#line 1719 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 60: /* solve_item: SOLVE SOLVE_MAXIMIZE basic_expr SEMICOLON  */
#line 652 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                                { ((*yyvalp).solve_attr) = new Solve(SolveType::MAXIMIZE, (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-1)].yystate.yysemantics.yyval.basic_expr_attr)); }
#line 1725 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 61: /* annotations: %empty  */
#line 656 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
    {
        AnnotationList v = new vector<Annotation*>;
        ((*yyvalp).annotation_list_attr) = v;
    }
#line 1734 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 62: /* annotations: DOUBLE_COLON annotation annotations  */
#line 660 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                          {
        AnnotationList v = (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.annotation_list_attr);
        v->emplace(v->begin(), (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-1)].yystate.yysemantics.yyval.annotation_attr));
        ((*yyvalp).annotation_list_attr) = v;
    }
#line 1744 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 63: /* annotation: VAR_PAR_IDENTIFIER  */
#line 668 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                       {
        ((*yyvalp).annotation_attr) = new Annotation((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.str_attr));
    }
#line 1752 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 64: /* annotation: VAR_PAR_IDENTIFIER OPEN_PARENT_SMALL anno_list  */
#line 671 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                                     {
        ((*yyvalp).annotation_attr) = new Annotation((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-2)].yystate.yysemantics.yyval.str_attr), (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.anno_list_attr));
    }
#line 1760 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 65: /* anno_list: ann_expr CLOSED_PARENT_SMALL  */
#line 677 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                 {
        vector<variant<Annotation*, BasicLiteralExpr*>*>* v = new vector<variant<Annotation*, BasicLiteralExpr*>*>();
        v->push_back((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-1)].yystate.yysemantics.yyval.ann_expr_attr));
    }
#line 1769 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 66: /* anno_list: ann_expr COMMA anno_list  */
#line 681 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                              {
        auto v = (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.anno_list_attr);
        v->emplace(v->begin(), (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (-2)].yystate.yysemantics.yyval.ann_expr_attr));
        ((*yyvalp).anno_list_attr) = v;
    }
#line 1779 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 67: /* ann_expr: basic_literal_expr  */
#line 689 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                       {
        ((*yyvalp).ann_expr_attr) = new variant<Annotation*, BasicLiteralExpr*>((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.basic_literal_expr_attr));
    }
#line 1787 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 68: /* ann_expr: annotation  */
#line 692 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                 {
        ((*yyvalp).ann_expr_attr) = new variant<Annotation*, BasicLiteralExpr*>((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.annotation_attr));
    }
#line 1795 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 69: /* ann_expr: OPEN_PARENT_MED basic_anno_list  */
#line 695 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                      {
        ((*yyvalp).ann_expr_attr) = new variant<Annotation*, BasicLiteralExpr*>((YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.basic_literal_expr_attr));
    }
#line 1803 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 70: /* basic_anno_list: %empty  */
#line 701 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
    {
        ((*yyvalp).basic_literal_expr_attr) = new BasicLiteralExpr(0);
    }
#line 1811 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 71: /* basic_anno_list: ann_expr COMMA basic_anno_list  */
#line 704 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                     {
        ((*yyvalp).basic_literal_expr_attr) = (YY_CAST (yyGLRStackItem const *, yyvsp)[YYFILL (0)].yystate.yysemantics.yyval.basic_literal_expr_attr);
    }
#line 1819 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;

  case 72: /* basic_anno_list: ann_expr CLOSED_PARENT_MED  */
#line 707 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"
                                 {
        ((*yyvalp).basic_literal_expr_attr) = new BasicLiteralExpr(0);
    }
#line 1827 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"
    break;


#line 1831 "/home/ubuntu/Desktop/AR/seminarski/src/parser.cpp"

      default: break;
    }
  YY_SYMBOL_PRINT ("-> $$ =", yylhsNonterm (yyrule), yyvalp, yylocp);

  return yyok;
# undef yyerrok
# undef YYABORT
# undef YYACCEPT
# undef YYNOMEM
# undef YYERROR
# undef YYBACKUP
# undef yyclearin
# undef YYRECOVERING
}


static void
yyuserMerge (int yyn, YYSTYPE* yy0, YYSTYPE* yy1)
{
  YY_USE (yy0);
  YY_USE (yy1);

  switch (yyn)
    {

      default: break;
    }
}

                              /* Bison grammar-table manipulation.  */

/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
yydestruct (const char *yymsg,
            yysymbol_kind_t yykind, YYSTYPE *yyvaluep)
{
  YY_USE (yyvaluep);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yykind, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YY_USE (yykind);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}

/** Number of symbols composing the right hand side of rule #RULE.  */
static inline int
yyrhsLength (yyRuleNum yyrule)
{
  return yyr2[yyrule];
}

static void
yydestroyGLRState (char const *yymsg, yyGLRState *yys)
{
  if (yys->yyresolved)
    yydestruct (yymsg, yy_accessing_symbol (yys->yylrState),
                &yys->yysemantics.yyval);
  else
    {
#if YYDEBUG
      if (yydebug)
        {
          if (yys->yysemantics.yyfirstVal)
            YY_FPRINTF ((stderr, "%s unresolved", yymsg));
          else
            YY_FPRINTF ((stderr, "%s incomplete", yymsg));
          YY_SYMBOL_PRINT ("", yy_accessing_symbol (yys->yylrState), YY_NULLPTR, &yys->yyloc);
        }
#endif

      if (yys->yysemantics.yyfirstVal)
        {
          yySemanticOption *yyoption = yys->yysemantics.yyfirstVal;
          yyGLRState *yyrh;
          int yyn;
          for (yyrh = yyoption->yystate, yyn = yyrhsLength (yyoption->yyrule);
               yyn > 0;
               yyrh = yyrh->yypred, yyn -= 1)
            yydestroyGLRState (yymsg, yyrh);
        }
    }
}

#define yypact_value_is_default(Yyn) \
  ((Yyn) == YYPACT_NINF)

/** True iff LR state YYSTATE has only a default reduction (regardless
 *  of token).  */
static inline yybool
yyisDefaultedState (yy_state_t yystate)
{
  return yypact_value_is_default (yypact[yystate]);
}

/** The default reduction for YYSTATE, assuming it has one.  */
static inline yyRuleNum
yydefaultAction (yy_state_t yystate)
{
  return yydefact[yystate];
}

#define yytable_value_is_error(Yyn) \
  0

/** The action to take in YYSTATE on seeing YYTOKEN.
 *  Result R means
 *    R < 0:  Reduce on rule -R.
 *    R = 0:  Error.
 *    R > 0:  Shift to state R.
 *  Set *YYCONFLICTS to a pointer into yyconfl to a 0-terminated list
 *  of conflicting reductions.
 */
static inline int
yygetLRActions (yy_state_t yystate, yysymbol_kind_t yytoken, const short** yyconflicts)
{
  int yyindex = yypact[yystate] + yytoken;
  if (yytoken == YYSYMBOL_YYerror)
    {
      // This is the error token.
      *yyconflicts = yyconfl;
      return 0;
    }
  else if (yyisDefaultedState (yystate)
           || yyindex < 0 || YYLAST < yyindex || yycheck[yyindex] != yytoken)
    {
      *yyconflicts = yyconfl;
      return -yydefact[yystate];
    }
  else if (! yytable_value_is_error (yytable[yyindex]))
    {
      *yyconflicts = yyconfl + yyconflp[yyindex];
      return yytable[yyindex];
    }
  else
    {
      *yyconflicts = yyconfl + yyconflp[yyindex];
      return 0;
    }
}

/** Compute post-reduction state.
 * \param yystate   the current state
 * \param yysym     the nonterminal to push on the stack
 */
static inline yy_state_t
yyLRgotoState (yy_state_t yystate, yysymbol_kind_t yysym)
{
  int yyr = yypgoto[yysym - YYNTOKENS] + yystate;
  if (0 <= yyr && yyr <= YYLAST && yycheck[yyr] == yystate)
    return yytable[yyr];
  else
    return yydefgoto[yysym - YYNTOKENS];
}

static inline yybool
yyisShiftAction (int yyaction)
{
  return 0 < yyaction;
}

static inline yybool
yyisErrorAction (int yyaction)
{
  return yyaction == 0;
}

                                /* GLRStates */

/** Return a fresh GLRStackItem in YYSTACKP.  The item is an LR state
 *  if YYISSTATE, and otherwise a semantic option.  Callers should call
 *  YY_RESERVE_GLRSTACK afterwards to make sure there is sufficient
 *  headroom.  */

static inline yyGLRStackItem*
yynewGLRStackItem (yyGLRStack* yystackp, yybool yyisState)
{
  yyGLRStackItem* yynewItem = yystackp->yynextFree;
  yystackp->yyspaceLeft -= 1;
  yystackp->yynextFree += 1;
  yynewItem->yystate.yyisState = yyisState;
  return yynewItem;
}

/** Add a new semantic action that will execute the action for rule
 *  YYRULE on the semantic values in YYRHS to the list of
 *  alternative actions for YYSTATE.  Assumes that YYRHS comes from
 *  stack #YYK of *YYSTACKP. */
static void
yyaddDeferredAction (yyGLRStack* yystackp, YYPTRDIFF_T yyk, yyGLRState* yystate,
                     yyGLRState* yyrhs, yyRuleNum yyrule)
{
  yySemanticOption* yynewOption =
    &yynewGLRStackItem (yystackp, yyfalse)->yyoption;
  YY_ASSERT (!yynewOption->yyisState);
  yynewOption->yystate = yyrhs;
  yynewOption->yyrule = yyrule;
  if (yystackp->yytops.yylookaheadNeeds[yyk])
    {
      yynewOption->yyrawchar = yychar;
      yynewOption->yyval = yylval;
    }
  else
    yynewOption->yyrawchar = YYEMPTY;
  yynewOption->yynext = yystate->yysemantics.yyfirstVal;
  yystate->yysemantics.yyfirstVal = yynewOption;

  YY_RESERVE_GLRSTACK (yystackp);
}

                                /* GLRStacks */

/** Initialize YYSET to a singleton set containing an empty stack.  */
static yybool
yyinitStateSet (yyGLRStateSet* yyset)
{
  yyset->yysize = 1;
  yyset->yycapacity = 16;
  yyset->yystates
    = YY_CAST (yyGLRState**,
               YYMALLOC (YY_CAST (YYSIZE_T, yyset->yycapacity)
                         * sizeof yyset->yystates[0]));
  if (! yyset->yystates)
    return yyfalse;
  yyset->yystates[0] = YY_NULLPTR;
  yyset->yylookaheadNeeds
    = YY_CAST (yybool*,
               YYMALLOC (YY_CAST (YYSIZE_T, yyset->yycapacity)
                         * sizeof yyset->yylookaheadNeeds[0]));
  if (! yyset->yylookaheadNeeds)
    {
      YYFREE (yyset->yystates);
      return yyfalse;
    }
  memset (yyset->yylookaheadNeeds,
          0,
          YY_CAST (YYSIZE_T, yyset->yycapacity) * sizeof yyset->yylookaheadNeeds[0]);
  return yytrue;
}

static void yyfreeStateSet (yyGLRStateSet* yyset)
{
  YYFREE (yyset->yystates);
  YYFREE (yyset->yylookaheadNeeds);
}

/** Initialize *YYSTACKP to a single empty stack, with total maximum
 *  capacity for all stacks of YYSIZE.  */
static yybool
yyinitGLRStack (yyGLRStack* yystackp, YYPTRDIFF_T yysize)
{
  yystackp->yyerrState = 0;
  yynerrs = 0;
  yystackp->yyspaceLeft = yysize;
  yystackp->yyitems
    = YY_CAST (yyGLRStackItem*,
               YYMALLOC (YY_CAST (YYSIZE_T, yysize)
                         * sizeof yystackp->yynextFree[0]));
  if (!yystackp->yyitems)
    return yyfalse;
  yystackp->yynextFree = yystackp->yyitems;
  yystackp->yysplitPoint = YY_NULLPTR;
  yystackp->yylastDeleted = YY_NULLPTR;
  return yyinitStateSet (&yystackp->yytops);
}


#if YYSTACKEXPANDABLE
# define YYRELOC(YYFROMITEMS, YYTOITEMS, YYX, YYTYPE)                   \
  &((YYTOITEMS)                                                         \
    - ((YYFROMITEMS) - YY_REINTERPRET_CAST (yyGLRStackItem*, (YYX))))->YYTYPE

/** If *YYSTACKP is expandable, extend it.  WARNING: Pointers into the
    stack from outside should be considered invalid after this call.
    We always expand when there are 1 or fewer items left AFTER an
    allocation, so that we can avoid having external pointers exist
    across an allocation.  */
static void
yyexpandGLRStack (yyGLRStack* yystackp)
{
  yyGLRStackItem* yynewItems;
  yyGLRStackItem* yyp0, *yyp1;
  YYPTRDIFF_T yynewSize;
  YYPTRDIFF_T yyn;
  YYPTRDIFF_T yysize = yystackp->yynextFree - yystackp->yyitems;
  if (YYMAXDEPTH - YYHEADROOM < yysize)
    yyMemoryExhausted (yystackp);
  yynewSize = 2*yysize;
  if (YYMAXDEPTH < yynewSize)
    yynewSize = YYMAXDEPTH;
  yynewItems
    = YY_CAST (yyGLRStackItem*,
               YYMALLOC (YY_CAST (YYSIZE_T, yynewSize)
                         * sizeof yynewItems[0]));
  if (! yynewItems)
    yyMemoryExhausted (yystackp);
  for (yyp0 = yystackp->yyitems, yyp1 = yynewItems, yyn = yysize;
       0 < yyn;
       yyn -= 1, yyp0 += 1, yyp1 += 1)
    {
      *yyp1 = *yyp0;
      if (*YY_REINTERPRET_CAST (yybool *, yyp0))
        {
          yyGLRState* yys0 = &yyp0->yystate;
          yyGLRState* yys1 = &yyp1->yystate;
          if (yys0->yypred != YY_NULLPTR)
            yys1->yypred =
              YYRELOC (yyp0, yyp1, yys0->yypred, yystate);
          if (! yys0->yyresolved && yys0->yysemantics.yyfirstVal != YY_NULLPTR)
            yys1->yysemantics.yyfirstVal =
              YYRELOC (yyp0, yyp1, yys0->yysemantics.yyfirstVal, yyoption);
        }
      else
        {
          yySemanticOption* yyv0 = &yyp0->yyoption;
          yySemanticOption* yyv1 = &yyp1->yyoption;
          if (yyv0->yystate != YY_NULLPTR)
            yyv1->yystate = YYRELOC (yyp0, yyp1, yyv0->yystate, yystate);
          if (yyv0->yynext != YY_NULLPTR)
            yyv1->yynext = YYRELOC (yyp0, yyp1, yyv0->yynext, yyoption);
        }
    }
  if (yystackp->yysplitPoint != YY_NULLPTR)
    yystackp->yysplitPoint = YYRELOC (yystackp->yyitems, yynewItems,
                                      yystackp->yysplitPoint, yystate);

  for (yyn = 0; yyn < yystackp->yytops.yysize; yyn += 1)
    if (yystackp->yytops.yystates[yyn] != YY_NULLPTR)
      yystackp->yytops.yystates[yyn] =
        YYRELOC (yystackp->yyitems, yynewItems,
                 yystackp->yytops.yystates[yyn], yystate);
  YYFREE (yystackp->yyitems);
  yystackp->yyitems = yynewItems;
  yystackp->yynextFree = yynewItems + yysize;
  yystackp->yyspaceLeft = yynewSize - yysize;
}
#endif

static void
yyfreeGLRStack (yyGLRStack* yystackp)
{
  YYFREE (yystackp->yyitems);
  yyfreeStateSet (&yystackp->yytops);
}

/** Assuming that YYS is a GLRState somewhere on *YYSTACKP, update the
 *  splitpoint of *YYSTACKP, if needed, so that it is at least as deep as
 *  YYS.  */
static inline void
yyupdateSplit (yyGLRStack* yystackp, yyGLRState* yys)
{
  if (yystackp->yysplitPoint != YY_NULLPTR && yystackp->yysplitPoint > yys)
    yystackp->yysplitPoint = yys;
}

/** Invalidate stack #YYK in *YYSTACKP.  */
static inline void
yymarkStackDeleted (yyGLRStack* yystackp, YYPTRDIFF_T yyk)
{
  if (yystackp->yytops.yystates[yyk] != YY_NULLPTR)
    yystackp->yylastDeleted = yystackp->yytops.yystates[yyk];
  yystackp->yytops.yystates[yyk] = YY_NULLPTR;
}

/** Undelete the last stack in *YYSTACKP that was marked as deleted.  Can
    only be done once after a deletion, and only when all other stacks have
    been deleted.  */
static void
yyundeleteLastStack (yyGLRStack* yystackp)
{
  if (yystackp->yylastDeleted == YY_NULLPTR || yystackp->yytops.yysize != 0)
    return;
  yystackp->yytops.yystates[0] = yystackp->yylastDeleted;
  yystackp->yytops.yysize = 1;
  YY_DPRINTF ((stderr, "Restoring last deleted stack as stack #0.\n"));
  yystackp->yylastDeleted = YY_NULLPTR;
}

static inline void
yyremoveDeletes (yyGLRStack* yystackp)
{
  YYPTRDIFF_T yyi, yyj;
  yyi = yyj = 0;
  while (yyj < yystackp->yytops.yysize)
    {
      if (yystackp->yytops.yystates[yyi] == YY_NULLPTR)
        {
          if (yyi == yyj)
            YY_DPRINTF ((stderr, "Removing dead stacks.\n"));
          yystackp->yytops.yysize -= 1;
        }
      else
        {
          yystackp->yytops.yystates[yyj] = yystackp->yytops.yystates[yyi];
          /* In the current implementation, it's unnecessary to copy
             yystackp->yytops.yylookaheadNeeds[yyi] since, after
             yyremoveDeletes returns, the parser immediately either enters
             deterministic operation or shifts a token.  However, it doesn't
             hurt, and the code might evolve to need it.  */
          yystackp->yytops.yylookaheadNeeds[yyj] =
            yystackp->yytops.yylookaheadNeeds[yyi];
          if (yyj != yyi)
            YY_DPRINTF ((stderr, "Rename stack %ld -> %ld.\n",
                        YY_CAST (long, yyi), YY_CAST (long, yyj)));
          yyj += 1;
        }
      yyi += 1;
    }
}

/** Shift to a new state on stack #YYK of *YYSTACKP, corresponding to LR
 * state YYLRSTATE, at input position YYPOSN, with (resolved) semantic
 * value *YYVALP and source location *YYLOCP.  */
static inline void
yyglrShift (yyGLRStack* yystackp, YYPTRDIFF_T yyk, yy_state_t yylrState,
            YYPTRDIFF_T yyposn,
            YYSTYPE* yyvalp)
{
  yyGLRState* yynewState = &yynewGLRStackItem (yystackp, yytrue)->yystate;

  yynewState->yylrState = yylrState;
  yynewState->yyposn = yyposn;
  yynewState->yyresolved = yytrue;
  yynewState->yypred = yystackp->yytops.yystates[yyk];
  yynewState->yysemantics.yyval = *yyvalp;
  yystackp->yytops.yystates[yyk] = yynewState;

  YY_RESERVE_GLRSTACK (yystackp);
}

/** Shift stack #YYK of *YYSTACKP, to a new state corresponding to LR
 *  state YYLRSTATE, at input position YYPOSN, with the (unresolved)
 *  semantic value of YYRHS under the action for YYRULE.  */
static inline void
yyglrShiftDefer (yyGLRStack* yystackp, YYPTRDIFF_T yyk, yy_state_t yylrState,
                 YYPTRDIFF_T yyposn, yyGLRState* yyrhs, yyRuleNum yyrule)
{
  yyGLRState* yynewState = &yynewGLRStackItem (yystackp, yytrue)->yystate;
  YY_ASSERT (yynewState->yyisState);

  yynewState->yylrState = yylrState;
  yynewState->yyposn = yyposn;
  yynewState->yyresolved = yyfalse;
  yynewState->yypred = yystackp->yytops.yystates[yyk];
  yynewState->yysemantics.yyfirstVal = YY_NULLPTR;
  yystackp->yytops.yystates[yyk] = yynewState;

  /* Invokes YY_RESERVE_GLRSTACK.  */
  yyaddDeferredAction (yystackp, yyk, yynewState, yyrhs, yyrule);
}

#if YYDEBUG

/*----------------------------------------------------------------------.
| Report that stack #YYK of *YYSTACKP is going to be reduced by YYRULE. |
`----------------------------------------------------------------------*/

static inline void
yy_reduce_print (yybool yynormal, yyGLRStackItem* yyvsp, YYPTRDIFF_T yyk,
                 yyRuleNum yyrule)
{
  int yynrhs = yyrhsLength (yyrule);
  int yyi;
  YY_FPRINTF ((stderr, "Reducing stack %ld by rule %d (line %d):\n",
               YY_CAST (long, yyk), yyrule - 1, yyrline[yyrule]));
  if (! yynormal)
    yyfillin (yyvsp, 1, -yynrhs);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YY_FPRINTF ((stderr, "   $%d = ", yyi + 1));
      yy_symbol_print (stderr,
                       yy_accessing_symbol (yyvsp[yyi - yynrhs + 1].yystate.yylrState),
                       &yyvsp[yyi - yynrhs + 1].yystate.yysemantics.yyval                       );
      if (!yyvsp[yyi - yynrhs + 1].yystate.yyresolved)
        YY_FPRINTF ((stderr, " (unresolved)"));
      YY_FPRINTF ((stderr, "\n"));
    }
}
#endif

/** Pop the symbols consumed by reduction #YYRULE from the top of stack
 *  #YYK of *YYSTACKP, and perform the appropriate semantic action on their
 *  semantic values.  Assumes that all ambiguities in semantic values
 *  have been previously resolved.  Set *YYVALP to the resulting value,
 *  and *YYLOCP to the computed location (if any).  Return value is as
 *  for userAction.  */
static inline YYRESULTTAG
yydoAction (yyGLRStack* yystackp, YYPTRDIFF_T yyk, yyRuleNum yyrule,
            YYSTYPE* yyvalp)
{
  int yynrhs = yyrhsLength (yyrule);

  if (yystackp->yysplitPoint == YY_NULLPTR)
    {
      /* Standard special case: single stack.  */
      yyGLRStackItem* yyrhs
        = YY_REINTERPRET_CAST (yyGLRStackItem*, yystackp->yytops.yystates[yyk]);
      YY_ASSERT (yyk == 0);
      yystackp->yynextFree -= yynrhs;
      yystackp->yyspaceLeft += yynrhs;
      yystackp->yytops.yystates[0] = & yystackp->yynextFree[-1].yystate;
      return yyuserAction (yyrule, yynrhs, yyrhs, yystackp, yyk,
                           yyvalp);
    }
  else
    {
      yyGLRStackItem yyrhsVals[YYMAXRHS + YYMAXLEFT + 1];
      yyGLRState* yys = yyrhsVals[YYMAXRHS + YYMAXLEFT].yystate.yypred
        = yystackp->yytops.yystates[yyk];
      int yyi;
      for (yyi = 0; yyi < yynrhs; yyi += 1)
        {
          yys = yys->yypred;
          YY_ASSERT (yys);
        }
      yyupdateSplit (yystackp, yys);
      yystackp->yytops.yystates[yyk] = yys;
      return yyuserAction (yyrule, yynrhs, yyrhsVals + YYMAXRHS + YYMAXLEFT - 1,
                           yystackp, yyk, yyvalp);
    }
}

/** Pop items off stack #YYK of *YYSTACKP according to grammar rule YYRULE,
 *  and push back on the resulting nonterminal symbol.  Perform the
 *  semantic action associated with YYRULE and store its value with the
 *  newly pushed state, if YYFORCEEVAL or if *YYSTACKP is currently
 *  unambiguous.  Otherwise, store the deferred semantic action with
 *  the new state.  If the new state would have an identical input
 *  position, LR state, and predecessor to an existing state on the stack,
 *  it is identified with that existing state, eliminating stack #YYK from
 *  *YYSTACKP.  In this case, the semantic value is
 *  added to the options for the existing state's semantic value.
 */
static inline YYRESULTTAG
yyglrReduce (yyGLRStack* yystackp, YYPTRDIFF_T yyk, yyRuleNum yyrule,
             yybool yyforceEval)
{
  YYPTRDIFF_T yyposn = yystackp->yytops.yystates[yyk]->yyposn;

  if (yyforceEval || yystackp->yysplitPoint == YY_NULLPTR)
    {
      YYSTYPE yyval;

      YYRESULTTAG yyflag = yydoAction (yystackp, yyk, yyrule, &yyval);
      if (yyflag == yyerr && yystackp->yysplitPoint != YY_NULLPTR)
        YY_DPRINTF ((stderr,
                     "Parse on stack %ld rejected by rule %d (line %d).\n",
                     YY_CAST (long, yyk), yyrule - 1, yyrline[yyrule]));
      if (yyflag != yyok)
        return yyflag;
      yyglrShift (yystackp, yyk,
                  yyLRgotoState (yystackp->yytops.yystates[yyk]->yylrState,
                                 yylhsNonterm (yyrule)),
                  yyposn, &yyval);
    }
  else
    {
      YYPTRDIFF_T yyi;
      int yyn;
      yyGLRState* yys, *yys0 = yystackp->yytops.yystates[yyk];
      yy_state_t yynewLRState;

      for (yys = yystackp->yytops.yystates[yyk], yyn = yyrhsLength (yyrule);
           0 < yyn; yyn -= 1)
        {
          yys = yys->yypred;
          YY_ASSERT (yys);
        }
      yyupdateSplit (yystackp, yys);
      yynewLRState = yyLRgotoState (yys->yylrState, yylhsNonterm (yyrule));
      YY_DPRINTF ((stderr,
                   "Reduced stack %ld by rule %d (line %d); action deferred.  "
                   "Now in state %d.\n",
                   YY_CAST (long, yyk), yyrule - 1, yyrline[yyrule],
                   yynewLRState));
      for (yyi = 0; yyi < yystackp->yytops.yysize; yyi += 1)
        if (yyi != yyk && yystackp->yytops.yystates[yyi] != YY_NULLPTR)
          {
            yyGLRState *yysplit = yystackp->yysplitPoint;
            yyGLRState *yyp = yystackp->yytops.yystates[yyi];
            while (yyp != yys && yyp != yysplit && yyp->yyposn >= yyposn)
              {
                if (yyp->yylrState == yynewLRState && yyp->yypred == yys)
                  {
                    yyaddDeferredAction (yystackp, yyk, yyp, yys0, yyrule);
                    yymarkStackDeleted (yystackp, yyk);
                    YY_DPRINTF ((stderr, "Merging stack %ld into stack %ld.\n",
                                 YY_CAST (long, yyk), YY_CAST (long, yyi)));
                    return yyok;
                  }
                yyp = yyp->yypred;
              }
          }
      yystackp->yytops.yystates[yyk] = yys;
      yyglrShiftDefer (yystackp, yyk, yynewLRState, yyposn, yys0, yyrule);
    }
  return yyok;
}

static YYPTRDIFF_T
yysplitStack (yyGLRStack* yystackp, YYPTRDIFF_T yyk)
{
  if (yystackp->yysplitPoint == YY_NULLPTR)
    {
      YY_ASSERT (yyk == 0);
      yystackp->yysplitPoint = yystackp->yytops.yystates[yyk];
    }
  if (yystackp->yytops.yycapacity <= yystackp->yytops.yysize)
    {
      YYPTRDIFF_T state_size = YYSIZEOF (yystackp->yytops.yystates[0]);
      YYPTRDIFF_T half_max_capacity = YYSIZE_MAXIMUM / 2 / state_size;
      if (half_max_capacity < yystackp->yytops.yycapacity)
        yyMemoryExhausted (yystackp);
      yystackp->yytops.yycapacity *= 2;

      {
        yyGLRState** yynewStates
          = YY_CAST (yyGLRState**,
                     YYREALLOC (yystackp->yytops.yystates,
                                (YY_CAST (YYSIZE_T, yystackp->yytops.yycapacity)
                                 * sizeof yynewStates[0])));
        if (yynewStates == YY_NULLPTR)
          yyMemoryExhausted (yystackp);
        yystackp->yytops.yystates = yynewStates;
      }

      {
        yybool* yynewLookaheadNeeds
          = YY_CAST (yybool*,
                     YYREALLOC (yystackp->yytops.yylookaheadNeeds,
                                (YY_CAST (YYSIZE_T, yystackp->yytops.yycapacity)
                                 * sizeof yynewLookaheadNeeds[0])));
        if (yynewLookaheadNeeds == YY_NULLPTR)
          yyMemoryExhausted (yystackp);
        yystackp->yytops.yylookaheadNeeds = yynewLookaheadNeeds;
      }
    }
  yystackp->yytops.yystates[yystackp->yytops.yysize]
    = yystackp->yytops.yystates[yyk];
  yystackp->yytops.yylookaheadNeeds[yystackp->yytops.yysize]
    = yystackp->yytops.yylookaheadNeeds[yyk];
  yystackp->yytops.yysize += 1;
  return yystackp->yytops.yysize - 1;
}

/** True iff YYY0 and YYY1 represent identical options at the top level.
 *  That is, they represent the same rule applied to RHS symbols
 *  that produce the same terminal symbols.  */
static yybool
yyidenticalOptions (yySemanticOption* yyy0, yySemanticOption* yyy1)
{
  if (yyy0->yyrule == yyy1->yyrule)
    {
      yyGLRState *yys0, *yys1;
      int yyn;
      for (yys0 = yyy0->yystate, yys1 = yyy1->yystate,
           yyn = yyrhsLength (yyy0->yyrule);
           yyn > 0;
           yys0 = yys0->yypred, yys1 = yys1->yypred, yyn -= 1)
        if (yys0->yyposn != yys1->yyposn)
          return yyfalse;
      return yytrue;
    }
  else
    return yyfalse;
}

/** Assuming identicalOptions (YYY0,YYY1), destructively merge the
 *  alternative semantic values for the RHS-symbols of YYY1 and YYY0.  */
static void
yymergeOptionSets (yySemanticOption* yyy0, yySemanticOption* yyy1)
{
  yyGLRState *yys0, *yys1;
  int yyn;
  for (yys0 = yyy0->yystate, yys1 = yyy1->yystate,
       yyn = yyrhsLength (yyy0->yyrule);
       0 < yyn;
       yys0 = yys0->yypred, yys1 = yys1->yypred, yyn -= 1)
    {
      if (yys0 == yys1)
        break;
      else if (yys0->yyresolved)
        {
          yys1->yyresolved = yytrue;
          yys1->yysemantics.yyval = yys0->yysemantics.yyval;
        }
      else if (yys1->yyresolved)
        {
          yys0->yyresolved = yytrue;
          yys0->yysemantics.yyval = yys1->yysemantics.yyval;
        }
      else
        {
          yySemanticOption** yyz0p = &yys0->yysemantics.yyfirstVal;
          yySemanticOption* yyz1 = yys1->yysemantics.yyfirstVal;
          while (yytrue)
            {
              if (yyz1 == *yyz0p || yyz1 == YY_NULLPTR)
                break;
              else if (*yyz0p == YY_NULLPTR)
                {
                  *yyz0p = yyz1;
                  break;
                }
              else if (*yyz0p < yyz1)
                {
                  yySemanticOption* yyz = *yyz0p;
                  *yyz0p = yyz1;
                  yyz1 = yyz1->yynext;
                  (*yyz0p)->yynext = yyz;
                }
              yyz0p = &(*yyz0p)->yynext;
            }
          yys1->yysemantics.yyfirstVal = yys0->yysemantics.yyfirstVal;
        }
    }
}

/** Y0 and Y1 represent two possible actions to take in a given
 *  parsing state; return 0 if no combination is possible,
 *  1 if user-mergeable, 2 if Y0 is preferred, 3 if Y1 is preferred.  */
static int
yypreference (yySemanticOption* y0, yySemanticOption* y1)
{
  yyRuleNum r0 = y0->yyrule, r1 = y1->yyrule;
  int p0 = yydprec[r0], p1 = yydprec[r1];

  if (p0 == p1)
    {
      if (yymerger[r0] == 0 || yymerger[r0] != yymerger[r1])
        return 0;
      else
        return 1;
    }
  if (p0 == 0 || p1 == 0)
    return 0;
  if (p0 < p1)
    return 3;
  if (p1 < p0)
    return 2;
  return 0;
}

static YYRESULTTAG
yyresolveValue (yyGLRState* yys, yyGLRStack* yystackp);


/** Resolve the previous YYN states starting at and including state YYS
 *  on *YYSTACKP. If result != yyok, some states may have been left
 *  unresolved possibly with empty semantic option chains.  Regardless
 *  of whether result = yyok, each state has been left with consistent
 *  data so that yydestroyGLRState can be invoked if necessary.  */
static YYRESULTTAG
yyresolveStates (yyGLRState* yys, int yyn,
                 yyGLRStack* yystackp)
{
  if (0 < yyn)
    {
      YY_ASSERT (yys->yypred);
      YYCHK (yyresolveStates (yys->yypred, yyn-1, yystackp));
      if (! yys->yyresolved)
        YYCHK (yyresolveValue (yys, yystackp));
    }
  return yyok;
}

/** Resolve the states for the RHS of YYOPT on *YYSTACKP, perform its
 *  user action, and return the semantic value and location in *YYVALP
 *  and *YYLOCP.  Regardless of whether result = yyok, all RHS states
 *  have been destroyed (assuming the user action destroys all RHS
 *  semantic values if invoked).  */
static YYRESULTTAG
yyresolveAction (yySemanticOption* yyopt, yyGLRStack* yystackp,
                 YYSTYPE* yyvalp)
{
  yyGLRStackItem yyrhsVals[YYMAXRHS + YYMAXLEFT + 1];
  int yynrhs = yyrhsLength (yyopt->yyrule);
  YYRESULTTAG yyflag =
    yyresolveStates (yyopt->yystate, yynrhs, yystackp);
  if (yyflag != yyok)
    {
      yyGLRState *yys;
      for (yys = yyopt->yystate; yynrhs > 0; yys = yys->yypred, yynrhs -= 1)
        yydestroyGLRState ("Cleanup: popping", yys);
      return yyflag;
    }

  yyrhsVals[YYMAXRHS + YYMAXLEFT].yystate.yypred = yyopt->yystate;
  {
    int yychar_current = yychar;
    YYSTYPE yylval_current = yylval;
    yychar = yyopt->yyrawchar;
    yylval = yyopt->yyval;
    yyflag = yyuserAction (yyopt->yyrule, yynrhs,
                           yyrhsVals + YYMAXRHS + YYMAXLEFT - 1,
                           yystackp, -1, yyvalp);
    yychar = yychar_current;
    yylval = yylval_current;
  }
  return yyflag;
}

#if YYDEBUG
static void
yyreportTree (yySemanticOption* yyx, int yyindent)
{
  int yynrhs = yyrhsLength (yyx->yyrule);
  int yyi;
  yyGLRState* yys;
  yyGLRState* yystates[1 + YYMAXRHS];
  yyGLRState yyleftmost_state;

  for (yyi = yynrhs, yys = yyx->yystate; 0 < yyi; yyi -= 1, yys = yys->yypred)
    yystates[yyi] = yys;
  if (yys == YY_NULLPTR)
    {
      yyleftmost_state.yyposn = 0;
      yystates[0] = &yyleftmost_state;
    }
  else
    yystates[0] = yys;

  if (yyx->yystate->yyposn < yys->yyposn + 1)
    YY_FPRINTF ((stderr, "%*s%s -> <Rule %d, empty>\n",
                 yyindent, "", yysymbol_name (yylhsNonterm (yyx->yyrule)),
                 yyx->yyrule - 1));
  else
    YY_FPRINTF ((stderr, "%*s%s -> <Rule %d, tokens %ld .. %ld>\n",
                 yyindent, "", yysymbol_name (yylhsNonterm (yyx->yyrule)),
                 yyx->yyrule - 1, YY_CAST (long, yys->yyposn + 1),
                 YY_CAST (long, yyx->yystate->yyposn)));
  for (yyi = 1; yyi <= yynrhs; yyi += 1)
    {
      if (yystates[yyi]->yyresolved)
        {
          if (yystates[yyi-1]->yyposn+1 > yystates[yyi]->yyposn)
            YY_FPRINTF ((stderr, "%*s%s <empty>\n", yyindent+2, "",
                         yysymbol_name (yy_accessing_symbol (yystates[yyi]->yylrState))));
          else
            YY_FPRINTF ((stderr, "%*s%s <tokens %ld .. %ld>\n", yyindent+2, "",
                         yysymbol_name (yy_accessing_symbol (yystates[yyi]->yylrState)),
                         YY_CAST (long, yystates[yyi-1]->yyposn + 1),
                         YY_CAST (long, yystates[yyi]->yyposn)));
        }
      else
        yyreportTree (yystates[yyi]->yysemantics.yyfirstVal, yyindent+2);
    }
}
#endif

static YYRESULTTAG
yyreportAmbiguity (yySemanticOption* yyx0,
                   yySemanticOption* yyx1)
{
  YY_USE (yyx0);
  YY_USE (yyx1);

#if YYDEBUG
  YY_FPRINTF ((stderr, "Ambiguity detected.\n"));
  YY_FPRINTF ((stderr, "Option 1,\n"));
  yyreportTree (yyx0, 2);
  YY_FPRINTF ((stderr, "\nOption 2,\n"));
  yyreportTree (yyx1, 2);
  YY_FPRINTF ((stderr, "\n"));
#endif

  yyerror (YY_("syntax is ambiguous"));
  return yyabort;
}

/** Resolve the ambiguity represented in state YYS in *YYSTACKP,
 *  perform the indicated actions, and set the semantic value of YYS.
 *  If result != yyok, the chain of semantic options in YYS has been
 *  cleared instead or it has been left unmodified except that
 *  redundant options may have been removed.  Regardless of whether
 *  result = yyok, YYS has been left with consistent data so that
 *  yydestroyGLRState can be invoked if necessary.  */
static YYRESULTTAG
yyresolveValue (yyGLRState* yys, yyGLRStack* yystackp)
{
  yySemanticOption* yyoptionList = yys->yysemantics.yyfirstVal;
  yySemanticOption* yybest = yyoptionList;
  yySemanticOption** yypp;
  yybool yymerge = yyfalse;
  YYSTYPE yyval;
  YYRESULTTAG yyflag;

  for (yypp = &yyoptionList->yynext; *yypp != YY_NULLPTR; )
    {
      yySemanticOption* yyp = *yypp;

      if (yyidenticalOptions (yybest, yyp))
        {
          yymergeOptionSets (yybest, yyp);
          *yypp = yyp->yynext;
        }
      else
        {
          switch (yypreference (yybest, yyp))
            {
            case 0:
              return yyreportAmbiguity (yybest, yyp);
              break;
            case 1:
              yymerge = yytrue;
              break;
            case 2:
              break;
            case 3:
              yybest = yyp;
              yymerge = yyfalse;
              break;
            default:
              /* This cannot happen so it is not worth a YY_ASSERT (yyfalse),
                 but some compilers complain if the default case is
                 omitted.  */
              break;
            }
          yypp = &yyp->yynext;
        }
    }

  if (yymerge)
    {
      yySemanticOption* yyp;
      int yyprec = yydprec[yybest->yyrule];
      yyflag = yyresolveAction (yybest, yystackp, &yyval);
      if (yyflag == yyok)
        for (yyp = yybest->yynext; yyp != YY_NULLPTR; yyp = yyp->yynext)
          {
            if (yyprec == yydprec[yyp->yyrule])
              {
                YYSTYPE yyval_other;
                yyflag = yyresolveAction (yyp, yystackp, &yyval_other);
                if (yyflag != yyok)
                  {
                    yydestruct ("Cleanup: discarding incompletely merged value for",
                                yy_accessing_symbol (yys->yylrState),
                                &yyval);
                    break;
                  }
                yyuserMerge (yymerger[yyp->yyrule], &yyval, &yyval_other);
              }
          }
    }
  else
    yyflag = yyresolveAction (yybest, yystackp, &yyval);

  if (yyflag == yyok)
    {
      yys->yyresolved = yytrue;
      yys->yysemantics.yyval = yyval;
    }
  else
    yys->yysemantics.yyfirstVal = YY_NULLPTR;
  return yyflag;
}

static YYRESULTTAG
yyresolveStack (yyGLRStack* yystackp)
{
  if (yystackp->yysplitPoint != YY_NULLPTR)
    {
      yyGLRState* yys;
      int yyn;

      for (yyn = 0, yys = yystackp->yytops.yystates[0];
           yys != yystackp->yysplitPoint;
           yys = yys->yypred, yyn += 1)
        continue;
      YYCHK (yyresolveStates (yystackp->yytops.yystates[0], yyn, yystackp
                             ));
    }
  return yyok;
}

/** Called when returning to deterministic operation to clean up the extra
 * stacks. */
static void
yycompressStack (yyGLRStack* yystackp)
{
  /* yyr is the state after the split point.  */
  yyGLRState *yyr;

  if (yystackp->yytops.yysize != 1 || yystackp->yysplitPoint == YY_NULLPTR)
    return;

  {
    yyGLRState *yyp, *yyq;
    for (yyp = yystackp->yytops.yystates[0], yyq = yyp->yypred, yyr = YY_NULLPTR;
         yyp != yystackp->yysplitPoint;
         yyr = yyp, yyp = yyq, yyq = yyp->yypred)
      yyp->yypred = yyr;
  }

  yystackp->yyspaceLeft += yystackp->yynextFree - yystackp->yyitems;
  yystackp->yynextFree = YY_REINTERPRET_CAST (yyGLRStackItem*, yystackp->yysplitPoint) + 1;
  yystackp->yyspaceLeft -= yystackp->yynextFree - yystackp->yyitems;
  yystackp->yysplitPoint = YY_NULLPTR;
  yystackp->yylastDeleted = YY_NULLPTR;

  while (yyr != YY_NULLPTR)
    {
      yystackp->yynextFree->yystate = *yyr;
      yyr = yyr->yypred;
      yystackp->yynextFree->yystate.yypred = &yystackp->yynextFree[-1].yystate;
      yystackp->yytops.yystates[0] = &yystackp->yynextFree->yystate;
      yystackp->yynextFree += 1;
      yystackp->yyspaceLeft -= 1;
    }
}

static YYRESULTTAG
yyprocessOneStack (yyGLRStack* yystackp, YYPTRDIFF_T yyk,
                   YYPTRDIFF_T yyposn)
{
  while (yystackp->yytops.yystates[yyk] != YY_NULLPTR)
    {
      yy_state_t yystate = yystackp->yytops.yystates[yyk]->yylrState;
      YY_DPRINTF ((stderr, "Stack %ld Entering state %d\n",
                   YY_CAST (long, yyk), yystate));

      YY_ASSERT (yystate != YYFINAL);

      if (yyisDefaultedState (yystate))
        {
          YYRESULTTAG yyflag;
          yyRuleNum yyrule = yydefaultAction (yystate);
          if (yyrule == 0)
            {
              YY_DPRINTF ((stderr, "Stack %ld dies.\n", YY_CAST (long, yyk)));
              yymarkStackDeleted (yystackp, yyk);
              return yyok;
            }
          yyflag = yyglrReduce (yystackp, yyk, yyrule, yyimmediate[yyrule]);
          if (yyflag == yyerr)
            {
              YY_DPRINTF ((stderr,
                           "Stack %ld dies "
                           "(predicate failure or explicit user error).\n",
                           YY_CAST (long, yyk)));
              yymarkStackDeleted (yystackp, yyk);
              return yyok;
            }
          if (yyflag != yyok)
            return yyflag;
        }
      else
        {
          yysymbol_kind_t yytoken = yygetToken (&yychar);
          const short* yyconflicts;
          const int yyaction = yygetLRActions (yystate, yytoken, &yyconflicts);
          yystackp->yytops.yylookaheadNeeds[yyk] = yytrue;

          for (/* nothing */; *yyconflicts; yyconflicts += 1)
            {
              YYRESULTTAG yyflag;
              YYPTRDIFF_T yynewStack = yysplitStack (yystackp, yyk);
              YY_DPRINTF ((stderr, "Splitting off stack %ld from %ld.\n",
                           YY_CAST (long, yynewStack), YY_CAST (long, yyk)));
              yyflag = yyglrReduce (yystackp, yynewStack,
                                    *yyconflicts,
                                    yyimmediate[*yyconflicts]);
              if (yyflag == yyok)
                YYCHK (yyprocessOneStack (yystackp, yynewStack,
                                          yyposn));
              else if (yyflag == yyerr)
                {
                  YY_DPRINTF ((stderr, "Stack %ld dies.\n", YY_CAST (long, yynewStack)));
                  yymarkStackDeleted (yystackp, yynewStack);
                }
              else
                return yyflag;
            }

          if (yyisShiftAction (yyaction))
            break;
          else if (yyisErrorAction (yyaction))
            {
              YY_DPRINTF ((stderr, "Stack %ld dies.\n", YY_CAST (long, yyk)));
              yymarkStackDeleted (yystackp, yyk);
              break;
            }
          else
            {
              YYRESULTTAG yyflag = yyglrReduce (yystackp, yyk, -yyaction,
                                                yyimmediate[-yyaction]);
              if (yyflag == yyerr)
                {
                  YY_DPRINTF ((stderr,
                               "Stack %ld dies "
                               "(predicate failure or explicit user error).\n",
                               YY_CAST (long, yyk)));
                  yymarkStackDeleted (yystackp, yyk);
                  break;
                }
              else if (yyflag != yyok)
                return yyflag;
            }
        }
    }
  return yyok;
}






static void
yyreportSyntaxError (yyGLRStack* yystackp)
{
  if (yystackp->yyerrState != 0)
    return;
  yyerror (YY_("syntax error"));
  yynerrs += 1;
}

/* Recover from a syntax error on *YYSTACKP, assuming that *YYSTACKP->YYTOKENP,
   yylval, and yylloc are the syntactic category, semantic value, and location
   of the lookahead.  */
static void
yyrecoverSyntaxError (yyGLRStack* yystackp)
{
  if (yystackp->yyerrState == 3)
    /* We just shifted the error token and (perhaps) took some
       reductions.  Skip tokens until we can proceed.  */
    while (yytrue)
      {
        yysymbol_kind_t yytoken;
        int yyj;
        if (yychar == YYEOF)
          yyFail (yystackp, YY_NULLPTR);
        if (yychar != YYEMPTY)
          {
            yytoken = YYTRANSLATE (yychar);
            yydestruct ("Error: discarding",
                        yytoken, &yylval);
            yychar = YYEMPTY;
          }
        yytoken = yygetToken (&yychar);
        yyj = yypact[yystackp->yytops.yystates[0]->yylrState];
        if (yypact_value_is_default (yyj))
          return;
        yyj += yytoken;
        if (yyj < 0 || YYLAST < yyj || yycheck[yyj] != yytoken)
          {
            if (yydefact[yystackp->yytops.yystates[0]->yylrState] != 0)
              return;
          }
        else if (! yytable_value_is_error (yytable[yyj]))
          return;
      }

  /* Reduce to one stack.  */
  {
    YYPTRDIFF_T yyk;
    for (yyk = 0; yyk < yystackp->yytops.yysize; yyk += 1)
      if (yystackp->yytops.yystates[yyk] != YY_NULLPTR)
        break;
    if (yyk >= yystackp->yytops.yysize)
      yyFail (yystackp, YY_NULLPTR);
    for (yyk += 1; yyk < yystackp->yytops.yysize; yyk += 1)
      yymarkStackDeleted (yystackp, yyk);
    yyremoveDeletes (yystackp);
    yycompressStack (yystackp);
  }

  /* Pop stack until we find a state that shifts the error token.  */
  yystackp->yyerrState = 3;
  while (yystackp->yytops.yystates[0] != YY_NULLPTR)
    {
      yyGLRState *yys = yystackp->yytops.yystates[0];
      int yyj = yypact[yys->yylrState];
      if (! yypact_value_is_default (yyj))
        {
          yyj += YYSYMBOL_YYerror;
          if (0 <= yyj && yyj <= YYLAST && yycheck[yyj] == YYSYMBOL_YYerror
              && yyisShiftAction (yytable[yyj]))
            {
              /* Shift the error token.  */
              int yyaction = yytable[yyj];
              YY_SYMBOL_PRINT ("Shifting", yy_accessing_symbol (yyaction),
                               &yylval, &yyerrloc);
              yyglrShift (yystackp, 0, yyaction,
                          yys->yyposn, &yylval);
              yys = yystackp->yytops.yystates[0];
              break;
            }
        }
      if (yys->yypred != YY_NULLPTR)
        yydestroyGLRState ("Error: popping", yys);
      yystackp->yytops.yystates[0] = yys->yypred;
      yystackp->yynextFree -= 1;
      yystackp->yyspaceLeft += 1;
    }
  if (yystackp->yytops.yystates[0] == YY_NULLPTR)
    yyFail (yystackp, YY_NULLPTR);
}

#define YYCHK1(YYE)                             \
  do {                                          \
    switch (YYE) {                              \
    case yyok:     break;                       \
    case yyabort:  goto yyabortlab;             \
    case yyaccept: goto yyacceptlab;            \
    case yyerr:    goto yyuser_error;           \
    case yynomem:  goto yyexhaustedlab;         \
    default:       goto yybuglab;               \
    }                                           \
  } while (0)

/*----------.
| yyparse.  |
`----------*/

int
yyparse (void)
{
  int yyresult;
  yyGLRStack yystack;
  yyGLRStack* const yystackp = &yystack;
  YYPTRDIFF_T yyposn;

  YY_DPRINTF ((stderr, "Starting parse\n"));

  yychar = YYEMPTY;
  yylval = yyval_default;

  if (! yyinitGLRStack (yystackp, YYINITDEPTH))
    goto yyexhaustedlab;
  switch (YYSETJMP (yystack.yyexception_buffer))
    {
    case 0: break;
    case 1: goto yyabortlab;
    case 2: goto yyexhaustedlab;
    default: goto yybuglab;
    }
  yyglrShift (&yystack, 0, 0, 0, &yylval);
  yyposn = 0;

  while (yytrue)
    {
      /* For efficiency, we have two loops, the first of which is
         specialized to deterministic operation (single stack, no
         potential ambiguity).  */
      /* Standard mode. */
      while (yytrue)
        {
          yy_state_t yystate = yystack.yytops.yystates[0]->yylrState;
          YY_DPRINTF ((stderr, "Entering state %d\n", yystate));
          if (yystate == YYFINAL)
            goto yyacceptlab;
          if (yyisDefaultedState (yystate))
            {
              yyRuleNum yyrule = yydefaultAction (yystate);
              if (yyrule == 0)
                {
                  yyreportSyntaxError (&yystack);
                  goto yyuser_error;
                }
              YYCHK1 (yyglrReduce (&yystack, 0, yyrule, yytrue));
            }
          else
            {
              yysymbol_kind_t yytoken = yygetToken (&yychar);
              const short* yyconflicts;
              int yyaction = yygetLRActions (yystate, yytoken, &yyconflicts);
              if (*yyconflicts)
                /* Enter nondeterministic mode.  */
                break;
              if (yyisShiftAction (yyaction))
                {
                  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);
                  yychar = YYEMPTY;
                  yyposn += 1;
                  yyglrShift (&yystack, 0, yyaction, yyposn, &yylval);
                  if (0 < yystack.yyerrState)
                    yystack.yyerrState -= 1;
                }
              else if (yyisErrorAction (yyaction))
                {
                  /* Issue an error message unless the scanner already
                     did. */
                  if (yychar != YYerror)
                    yyreportSyntaxError (&yystack);
                  goto yyuser_error;
                }
              else
                YYCHK1 (yyglrReduce (&yystack, 0, -yyaction, yytrue));
            }
        }

      /* Nondeterministic mode. */
      while (yytrue)
        {
          yysymbol_kind_t yytoken_to_shift;
          YYPTRDIFF_T yys;

          for (yys = 0; yys < yystack.yytops.yysize; yys += 1)
            yystackp->yytops.yylookaheadNeeds[yys] = yychar != YYEMPTY;

          /* yyprocessOneStack returns one of three things:

              - An error flag.  If the caller is yyprocessOneStack, it
                immediately returns as well.  When the caller is finally
                yyparse, it jumps to an error label via YYCHK1.

              - yyok, but yyprocessOneStack has invoked yymarkStackDeleted
                (&yystack, yys), which sets the top state of yys to NULL.  Thus,
                yyparse's following invocation of yyremoveDeletes will remove
                the stack.

              - yyok, when ready to shift a token.

             Except in the first case, yyparse will invoke yyremoveDeletes and
             then shift the next token onto all remaining stacks.  This
             synchronization of the shift (that is, after all preceding
             reductions on all stacks) helps prevent double destructor calls
             on yylval in the event of memory exhaustion.  */

          for (yys = 0; yys < yystack.yytops.yysize; yys += 1)
            YYCHK1 (yyprocessOneStack (&yystack, yys, yyposn));
          yyremoveDeletes (&yystack);
          if (yystack.yytops.yysize == 0)
            {
              yyundeleteLastStack (&yystack);
              if (yystack.yytops.yysize == 0)
                yyFail (&yystack, YY_("syntax error"));
              YYCHK1 (yyresolveStack (&yystack));
              YY_DPRINTF ((stderr, "Returning to deterministic operation.\n"));
              yyreportSyntaxError (&yystack);
              goto yyuser_error;
            }

          /* If any yyglrShift call fails, it will fail after shifting.  Thus,
             a copy of yylval will already be on stack 0 in the event of a
             failure in the following loop.  Thus, yychar is set to YYEMPTY
             before the loop to make sure the user destructor for yylval isn't
             called twice.  */
          yytoken_to_shift = YYTRANSLATE (yychar);
          yychar = YYEMPTY;
          yyposn += 1;
          for (yys = 0; yys < yystack.yytops.yysize; yys += 1)
            {
              yy_state_t yystate = yystack.yytops.yystates[yys]->yylrState;
              const short* yyconflicts;
              int yyaction = yygetLRActions (yystate, yytoken_to_shift,
                              &yyconflicts);
              /* Note that yyconflicts were handled by yyprocessOneStack.  */
              YY_DPRINTF ((stderr, "On stack %ld, ", YY_CAST (long, yys)));
              YY_SYMBOL_PRINT ("shifting", yytoken_to_shift, &yylval, &yylloc);
              yyglrShift (&yystack, yys, yyaction, yyposn,
                          &yylval);
              YY_DPRINTF ((stderr, "Stack %ld now in state %d\n",
                           YY_CAST (long, yys),
                           yystack.yytops.yystates[yys]->yylrState));
            }

          if (yystack.yytops.yysize == 1)
            {
              YYCHK1 (yyresolveStack (&yystack));
              YY_DPRINTF ((stderr, "Returning to deterministic operation.\n"));
              yycompressStack (&yystack);
              break;
            }
        }
      continue;
    yyuser_error:
      yyrecoverSyntaxError (&yystack);
      yyposn = yystack.yytops.yystates[0]->yyposn;
    }

 yyacceptlab:
  yyresult = 0;
  goto yyreturnlab;

 yybuglab:
  YY_ASSERT (yyfalse);
  goto yyabortlab;

 yyabortlab:
  yyresult = 1;
  goto yyreturnlab;

 yyexhaustedlab:
  yyerror (YY_("memory exhausted"));
  yyresult = 2;
  goto yyreturnlab;

 yyreturnlab:
  if (yychar != YYEMPTY)
    yydestruct ("Cleanup: discarding lookahead",
                YYTRANSLATE (yychar), &yylval);

  /* If the stack is well-formed, pop the stack until it is empty,
     destroying its entries as we go.  But free the stack regardless
     of whether it is well-formed.  */
  if (yystack.yyitems)
    {
      yyGLRState** yystates = yystack.yytops.yystates;
      if (yystates)
        {
          YYPTRDIFF_T yysize = yystack.yytops.yysize;
          YYPTRDIFF_T yyk;
          for (yyk = 0; yyk < yysize; yyk += 1)
            if (yystates[yyk])
              {
                while (yystates[yyk])
                  {
                    yyGLRState *yys = yystates[yyk];
                    if (yys->yypred != YY_NULLPTR)
                      yydestroyGLRState ("Cleanup: popping", yys);
                    yystates[yyk] = yys->yypred;
                    yystack.yynextFree -= 1;
                    yystack.yyspaceLeft += 1;
                  }
                break;
              }
        }
      yyfreeGLRStack (&yystack);
    }

  return yyresult;
}

/* DEBUGGING ONLY */
#if YYDEBUG
/* Print *YYS and its predecessors. */
static void
yy_yypstack (yyGLRState* yys)
{
  if (yys->yypred)
    {
      yy_yypstack (yys->yypred);
      YY_FPRINTF ((stderr, " -> "));
    }
  YY_FPRINTF ((stderr, "%d@%ld", yys->yylrState, YY_CAST (long, yys->yyposn)));
}

/* Print YYS (possibly NULL) and its predecessors. */
static void
yypstates (yyGLRState* yys)
{
  if (yys == YY_NULLPTR)
    YY_FPRINTF ((stderr, "<null>"));
  else
    yy_yypstack (yys);
  YY_FPRINTF ((stderr, "\n"));
}

/* Print the stack #YYK.  */
static void
yypstack (yyGLRStack* yystackp, YYPTRDIFF_T yyk)
{
  yypstates (yystackp->yytops.yystates[yyk]);
}

/* Print all the stacks.  */
static void
yypdumpstack (yyGLRStack* yystackp)
{
#define YYINDEX(YYX)                                                    \
  YY_CAST (long,                                                        \
           ((YYX)                                                       \
            ? YY_REINTERPRET_CAST (yyGLRStackItem*, (YYX)) - yystackp->yyitems \
            : -1))

  yyGLRStackItem* yyp;
  for (yyp = yystackp->yyitems; yyp < yystackp->yynextFree; yyp += 1)
    {
      YY_FPRINTF ((stderr, "%3ld. ",
                   YY_CAST (long, yyp - yystackp->yyitems)));
      if (*YY_REINTERPRET_CAST (yybool *, yyp))
        {
          YY_ASSERT (yyp->yystate.yyisState);
          YY_ASSERT (yyp->yyoption.yyisState);
          YY_FPRINTF ((stderr, "Res: %d, LR State: %d, posn: %ld, pred: %ld",
                       yyp->yystate.yyresolved, yyp->yystate.yylrState,
                       YY_CAST (long, yyp->yystate.yyposn),
                       YYINDEX (yyp->yystate.yypred)));
          if (! yyp->yystate.yyresolved)
            YY_FPRINTF ((stderr, ", firstVal: %ld",
                         YYINDEX (yyp->yystate.yysemantics.yyfirstVal)));
        }
      else
        {
          YY_ASSERT (!yyp->yystate.yyisState);
          YY_ASSERT (!yyp->yyoption.yyisState);
          YY_FPRINTF ((stderr, "Option. rule: %d, state: %ld, next: %ld",
                       yyp->yyoption.yyrule - 1,
                       YYINDEX (yyp->yyoption.yystate),
                       YYINDEX (yyp->yyoption.yynext)));
        }
      YY_FPRINTF ((stderr, "\n"));
    }

  YY_FPRINTF ((stderr, "Tops:"));
  {
    YYPTRDIFF_T yyi;
    for (yyi = 0; yyi < yystackp->yytops.yysize; yyi += 1)
      YY_FPRINTF ((stderr, "%ld: %ld; ", YY_CAST (long, yyi),
                   YYINDEX (yystackp->yytops.yystates[yyi])));
    YY_FPRINTF ((stderr, "\n"));
  }
#undef YYINDEX
}
#endif

#undef yylval
#undef yychar
#undef yynerrs




#line 710 "/home/ubuntu/Desktop/AR/seminarski/parser_gen/parser.ypp"

 
