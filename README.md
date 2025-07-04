# Flatzinc to SAT Converter

This project is a **Flatzinc to SAT converter**, built for a **course on Automated Reasoning**. The converter takes a Flatzinc model as input and converts it into a SAT (satisfiability) problem.

## Features

- **Converts Flatzinc to SAT**: The primary functionality of this project is converting a Flatzinc model into a SAT problem.
- **Encoding Constraints**: Currently, the converter supports the encoding of most FlatZinc constraints.
- **Supports different variable types**: The converter works with integer, bool and set variables.
- **Solving CSPs**: The converter can also be used as a CSP solver, as it invokes a backend SAT solver (MiniSAT) and decodes it's output.
  
### Supported Constraints

The list of FlatZinc builtin constraints can be found [here](https://docs.minizinc.dev/en/2.5.5/lib-flatzinc.html).



## Installation

Dependencies needed are flex (version 2.6.4 or greater), bison (version 3.8.2 or greater) and the minisat solver.

To get started with this project, clone the repository and follow the steps below:

```bash

git clone https://github.com/Lojovic/FlatZincToSATConverter
cd FlatZincToSATConverter

mkdir build
cd build

cmake ..
make
```

## Usage

To run this project run the following command, where input.fzn is an input FlatZinc model
:

```bash

./flatzinc_to_sat path/to/input.fzn
```

The file formula.cnf contains the SAT formula of the FlatZinc model