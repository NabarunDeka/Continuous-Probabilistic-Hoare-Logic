# Continuous Probabilistic Hoare Logic

Rocq formalization of program semantics and Hoare-rule soundness, with SVT
and Monte Carlo examples.

## Requirements

Install Git, Python 3, opam 2.x, a C compiler, Make, pkg-config, and GMP
development libraries. The tested environment uses OCaml 4.14.1, Rocq 9.0.0,
Stdlib 9.1.0, MathComp 2.6.0, MathComp Analysis and its Stdlib bridge 1.18.0,
Hierarchy Builder 1.10.3, and Rocq Elpi 3.5.1. `toolchain.opam-switch` records
all 61 tested package versions; `cphl.opam` lists the direct dependencies.

## Install dependencies and compile

Clone the repository, then run setup and build commands from its root:

```sh
git clone https://github.com/NabarunDeka/Continuous-Probabilistic-Hoare-Logic.git
cd Continuous-Probabilistic-Hoare-Logic
mkdir -p .build/opam-logs
export OPAMLOGS="$PWD/.build/opam-logs"
```

If opam has not been initialized, run `opam init --bare`. Register the Rocq
package repository, refresh package metadata, and create a fresh local switch:

```sh
opam repository add coq-released https://coq.inria.fr/opam/released --dont-select
opam update coq-released default
opam switch create .toolchain --empty --repositories=coq-released,default --no-switch
opam switch import --switch=.toolchain ./toolchain.opam-switch
python3 build.py
```

Importing the snapshot installs the pinned dependencies. Keep the `coq-core`
compatibility package, which some dependencies still require. The build
script checks all recorded versions and recompiles the 49 modules in
`_CoqProject` order. It does not install or upgrade packages.

To use an existing switch with the same package versions:

```sh
python3 build.py --switch /absolute/path/to/existing-switch
```

## Use the compiled modules

Save this as `CheckSoundness.v` at the repository root:

```coq
Require Import CPHL Soundness.HoareSoundness.
Check hoare_derivable_sound.
Check hoare_derivable_sound_joint.
Check hoare_derivable_sound_result.

Require SVT SVT_notation MonteCarloEst.
Check SVT.svt_01_bot_top_probability.
Check SVT_notation.run_01_bot_top_probability.
Check SVT_notation.run_11_bot_top_probability.
Check MonteCarloEst.monte_carlo_estimator_probability.
```

Compile it using the same switch and load path as the build:

```sh
opam exec --switch=.toolchain -- rocq compile -q -Q . "" CheckSoundness.v
```

The examples compile with four calculation axioms in `AnalyticalCalculations.v`:
three exponential integral identities for SVT and one quarter-disk identity
for Monte Carlo. These are not assumptions of the general soundness theorem.

## Build diagnostics

Compiler output is saved in `.build/build.log`; package versions, source hashes,
exit codes, and the final result are in `.build/result.json`. Opam diagnostic
logs stay in `.build/opam-logs/`. Use the same installed switch for compilation
and interactive checking to avoid incompatible compiled-library errors.
