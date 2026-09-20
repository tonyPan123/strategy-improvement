SimSat
====
SimSat is an tool for synthesizing winning strategies to logical games.

The strategy synthesis algorithms are implemented in
[duet](https://github.com/zkincaid/duet).  This repository contains the ark
library of duet along with a command line interface to the strategy synthesis
algorithms.

Building
========

### Quick start

`scripts/install-deps.sh` performs every step described below (opam switch,
MathSAT, Z3, OCRS, ocaml-mathsat).  It has been verified on Ubuntu 24.04 with
OCaml 4.14.2:

```
 sudo apt-get install opam libgmp-dev libmpfr-dev m4 pkg-config build-essential
 ./scripts/install-deps.sh
 eval $(opam env --switch=simsat)
 make
```

`make` produces `simsat.native`, `test_ark.native` and `arkTop.native` in the
top-level directory.  `./test_ark.native` runs the ark unit test suite.

### Dependencies

 + [opam](http://opam.ocaml.org) with OCaml 4.14.x & the native compiler
 + GMP and MPFR
 + [MathSAT](http://mathsat.fbk.eu) **version 5.3.14** (version 5.4 is incompatible),
   with `mathsat.h` and `libmathsat.a` installed under `/usr/local`
 + [ocaml-mathsat](https://github.com/zkincaid/ocaml-mathsat) (findlib name `mathsat`)
 + [OCRS](https://github.com/cyphertjohn/OCRS), release `20180427v3` (findlib name `ocrs`);
   the current OCRS master installs itself as `OCRS` and is *not* a drop-in replacement
 + Z3 with the OCaml API and the **interpolation** API (findlib name `Z3`)
 + `opam install batteries ppx_deriving ocamlgraph ounit menhir ocamlbuild camlidl apron oasis num`

The interpolation requirement is the reason a stock `opam install z3` will not
work: `Z3.Interpolation` was dropped from upstream Z3 after 4.5, and
`ArkZ3.interpolate_seq` &mdash; which the reachability game solver in `ark/game.ml`
depends on &mdash; needs it.  Build
[zkincaid/z3](https://github.com/zkincaid/z3) at tag `20180513` instead.  Two
adjustments are needed to build that tree with a modern toolchain:

 + its `scripts/mk_make.py` can be run with `python3` (the original instructions
   call for `python2.7`, which is no longer packaged on current distributions);
 + the four `#if 0 // ZK: multiple defs` blocks in
   `src/ast/proofs/proof_utils.cpp` have to be re-enabled, otherwise the
   `proof_utils::` member functions they contain are defined nowhere in the tree
   and `libz3.so` fails to link with undefined references to
   `proof_utils::reduce_hypotheses`, `proof_utils::permute_unit_resolution` and
   `proof_utils::push_instantiations_up`.

### Building SimSat

After SimSat's dependencies are installed, it can be built using `make`.

Satisfiability
==============

SimSat is a satisfiability testing procedure for quantified formulas in linear
integer arithmetic and linear rational arithmetic.  It accepts input in
SMT-LIB2 format, and can be executed as follows:

    simsat.native -sat FILE.smt2

A quantified formula can be viewed as a game between two players -- SAT and
UNSAT -- whose goals are to prove that formula is satisfiable / unsatisfiable,
respectively.  The SimSat algorithm is based on synthesizing a winning
strategy for one of the two players by mutually improving strategies for both.
The procedure is described in
* Azadeh Farzan, Zachary Kincaid: [Linear Arithmetic Satisfiability via Strategy Improvement](http://www.cs.princeton.edu/~zkincaid/pub/ijcai16.pdf).  IJCAI 2016.


Synthesis (SimSynth)
====================

SimSat is also capable of synthesizing winning strategies to satisfiability
games as well as reachability games.  It accepts satisfiability in SMT-LIB2
format (with a mandatory .smt2 file extension), and reachability games in a
format that will be described below (with a mandatory file .rg extension).  To
synthesize a strategy, execute simsat as follows:

    simsat.native -sat FILE.[smt2|rg]

Syntax of reachability games:
-----------------------------
```
vars: <var-list>     # comma-separated list of variables
init: <formula>      # formula describing initial positions of the game
safe: <formula>      # formula describing moves of the safety player
reach: <formula>     # formula describing moves of the reachability player
```

The init formula is defined over the variables that appear in 'vars'.  The
safe and reach formulas are defined over the variables in 'vars' plus primed
copies.  For example, if vars is x and y, then safe and reach are formulas
over the vocabulary {x,y,x',y'}, and safe (reach) may move from (a,b) to
(a',b') exactly when the the formula safe is satisfied by the assignment
        { x -> a, y -> b, x' -> a', y' -> b' }.

The syntax of formulas is as follows:
```
<formula> ::= <formula> && <formula> | <formula> || <formula>
            | !(<formula>) | ( <formula> )
            | <term> <= <term> | <term> < <term>
            | <term> >= <term> | <term> > <term>
            | <term> = <term>
<term> ::= <int> | <var>
         | <term> + <term> | <term> - <term>
	 | <term> * <term> | <term> / <term>
	 | ( term )
```
