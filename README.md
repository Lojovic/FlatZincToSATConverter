# Flatzinc to SAT Converter

This project is a **Flatzinc to SAT converter**. The converter takes a Flatzinc model as input and converts it into a SAT (satisfiability) problem. 

## Features

- **Converts Flatzinc to SAT**: The primary functionality of this project is converting a Flatzinc model into a SAT problem.
- **Encoding Constraints**: The converter supports the encoding of all the builtin Integer, Bool and Set FlatZinc constraints.
- **Solving CSPs**: The converter can also be used as a CSP solver, as it invokes a backend SAT solver (MiniSAT, CaDiCaL or glucose) and decodes it's output.
- **Proof export**: The converter can export a proof of correctness for the encoding in the SMT-LIB format.

### Supported Constraints

The list of FlatZinc builtin constraints can be found [here](https://docs.minizinc.dev/en/2.5.5/lib-flatzinc.html).



## Installation

Dependencies needed are flex (version 2.6.4 or greater), bison (version 3.8.2 or greater) and the minisat/CaDiCaL/glucose SAT solver (whichever you wish to use as the backend solver).

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

If you wish to export a proof of correctness for the encoding, use the option `-export-proof`. The folder `proofs` will be created, and the file `proof.smt2` will contain the proof.