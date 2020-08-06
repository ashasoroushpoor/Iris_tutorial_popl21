# The Iris tutorial @ POPL'18

This tutorial comes in two versions:

- The folder `exercises`: skeletons of the exercises with parts left `admit`ted.
- The folder `solutions`: the exercises together with their solutions.

## Dependencies

For the tutorial material you need to have the following dependencies installed:

- Coq 8.10.1 / 8.11.0
- [Iris](https://gitlab.mpi-sws.org/iris/iris) 3.3.0

*Note:* the tutorial material will not work with earlier versions of Iris, it
is important to install the exact versions as given above.

For a tutorial that works with Coq 8.6, and that can be installed without opam,
please check out the
[version of this tutorial for Iris 3.1](https://gitlab.mpi-sws.org/iris/tutorial-popl18/tree/iris-3.1.0).

## Installing Iris via opam

The easiest, and recommend, way of installing Iris and its dependencies is via
the OCaml package manager opam (2.0.0 or newer). You first have to add the Coq
opam repository and the Iris development repository (if you have not already
done so earlier):

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

Then you can do `make build-dep` to install exactly the right version of Iris.

## Compiling the exercises

Run `make` to compile the exercises. You need to have exercise 3 compiled to
work on exercise 4 and 5.

## Documentation

The files [`proof_mode.md`] and [`heap_lang.md`] in the Iris repository contain a
list of the Iris Proof Mode tactics as well as the specialized tactics for
reasoning about HeapLang programs.

[`proof_mode.md`]: https://gitlab.mpi-sws.org/iris/iris/blob/master/docs/proof_mode.md
[`heap_lang.md`]: https://gitlab.mpi-sws.org/iris/iris/blob/master/docs/heap_lang.md

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
