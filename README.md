# The Iris tutorial @ POPL'18

This tutorial comes in two versions:

- The folder `exercises`: skeletons of the exercises with parts left `admit`ted.
- The folder `solutions`: the exercises together with their solutions.

## Dependencies

For the tutorial material you need to have the following dependencies installed:

- Coq 8.6.1 / 8.7.2 / 8.8.2
- Ssreflect 1.7.0
- Coq-std++ 1.1
- Iris (latest version)

*Note:* the tutorial material will not work with earlier versions of Iris, it
is important to install the exact versions as given above.

## Installing Iris via opam

The easiest, and recommend, way of installing Iris and its dependencies is via
the OCaml package manager opam (1.2.2 or newer). You first have to add the Coq
opam repository and the Iris development repository (if you have not already
done so earlier):

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev https://gitlab.mpi-sws.org/FP/opam-dev.git

Then you can do `opam install coq-iris`.

## Installing Iris from source

If you are unable to use opam, you can also build Iris from source. For this,
run `make; make install` for all of:

* ssreflect: <https://github.com/math-comp/math-comp/archive/mathcomp-1.7.0.tar.gz>
  (`cd mathcomp/ssreflect` to only compile and install what is needed)
* std++: <https://gitlab.mpi-sws.org/iris/stdpp/repository/coq-stdpp-1.1.0/archive.tar.gz>
* Iris: <https://gitlab.mpi-sws.org/FP/iris-coq/repository/iris-3.1.0/archive.tar.gz>

## Compiling the exercises

Run `make` to compile the exercises. You need to have exercise 3 compiled to
work on exercise 4 and 5.

## Documentation

The file `ProofMode.md` in the tutorial material (which can also be found in the
root of the Iris repository) contains a list of the Iris Proof Mode tactics.

If you would like to know more about Iris, we recommend to take a look at:

- http://iris-project.org/tutorial-material.html
  Lecture Notes on Iris: Higher-Order Concurrent Separation Logic
  Lars Birkedal and Aleš Bizjak
  Used for an MSc course on concurrent separation logic at Aarhus University

- https://www.mpi-sws.org/~dreyer/papers/iris-ground-up/paper.pdf
  Iris from the Ground Up: A Modular Foundation for Higher-Order Concurrent
  Separation Logic
  Ralf Jung, Robbert Krebbers, Jacques-Henri Jourdan, Aleš Bizjak, Lars
  Birkedal, Derek Dreyer.
  A detailed description of the Iris logic and its model
