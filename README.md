# Flatzinc to SAT Converter

This project is a **Flatzinc to SAT converter**. The converter takes a Flatzinc model as input and converts it into a SAT (satisfiability) problem. 

## Features

- **Converts Flatzinc to SAT**: The project converts FlatZinc models into equivalent SAT problems.
- **Constraint encoding**: Supports encoding of all built-in FlatZinc Integer, Boolean, and Set constraints.
- **CSP solving**: Can be used as a CSP solver by invoking a backend SAT solver (MiniSAT, CaDiCaL, or Glucose) and decoding its output.
- **COP solving**: Supports solving constraint optimization problems (COPs) using a linear optimization strategy.
- **Proof export**: Can export a set of SMT-LIB theorems, enabling the generation of correctness proofs for the encoding.

### Supported Constraints

The list of FlatZinc builtin constraints can be found [here](https://docs.minizinc.dev/en/2.5.5/lib-flatzinc.html).



## Installation

Dependencies needed are:
- flex (version 2.6.4 or greater)
- bison (version 3.8.2 or greater)
- a C++ compiler that supports the C++17 standard or greater
- the MiniSAT/CaDiCaL/glucose SAT solver (whichever you wish to use as the backend solver).

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

To run the converter with the default settings, run the following command, where input.fzn is an input FlatZinc model
:

```bash

./flatzinc_to_sat path/to/input.fzn
```

The file formula.cnf now contains the SAT formula of the FlatZinc model. The default backend solver to be used is minisat.

To run the converter with a specific solver, use the option `-solver=solver_name`. For example:

```bash

./flatzinc_to_sat -solver=cadical path/to/input.fzn
```

If you wish to export a proof of correctness for the encoding, use the option `-export-proof`. The folder `proofs` will be created, and the file `proof.smt2` will contain a set of theorems which can be used for generating proofs of correctness for the encoding.