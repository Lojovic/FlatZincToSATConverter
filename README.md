# Flatzinc to SAT Converter

This project is a **Flatzinc to SAT converter**, built for a **course on Automated Reasoning**. The converter takes a Flatzinc model as input and converts it into a SAT (satisfiability) problem.

## Features

- **Converts Flatzinc to SAT**: The primary functionality of this project is converting a Flatzinc model into a SAT problem.
- **Encoding Constraints**: Currently, the converter supports the encoding of certain basic constraints listed below into the SAT format.
- **Supports Integer Range Variables**: The converter works with integer variables that fall within a defined range.
  
### Supported Constraints

- **int_abs(var int: a, var int: b)**: Constrains b to be the absolute value of a
- **int_eq(var int: a, var int: b)**: Constrains a to be equal to b
- **int_le(var int: a, var int: b)**: Constrains a to be less than or equal to b
- **int_lin_le(array [int] of int: as, array [int] of var int: bs,int: c)**: Constrains ∑ as [ i ]* bs [ i ] ≤ c
- **int_lt(var int: a, var int: b)**: Constrains a to be less than b
- **int_max(var int: a, var int: b, var int: c)**: Constrains max( a , b ) = c
- **int_min(var int: a, var int: b, var int: c)**: Constrains min( a , b ) = c
- **int_ne(var int: a, var int: b)**: Constrains a ≠ b


## Installation

To get started with this project, clone the repository and follow the steps below:

```bash

git clone https://github.com/yourusername/flatzinc-to-sat.git
cd flatzinc-to-sat

mkdir build
cd build

cmake ..
make
```

## Usage

To run this project, modify the input.fzn file to contain the FlatZinc model and run the following command:

```bash

./flatzinc_to_sat
```

The file formula.cnf contains the SAT formula of the FlatZinc model