# The Iris tutorial @ POPL'18

This tutorial comes in two versions:

- The folder `exercises`: skeletons of the exercises with parts left `admit`ted.
- The folder `solutions`: the exercises together with their solutions.

## Dependencies

For the tutorial material you need to have the following dependencies installed:

- Coq 8.12.1
- A development version of [Iris](https://gitlab.mpi-sws.org/iris/iris)

*Note:* the tutorial material will not work with earlier or later versions of
Iris, it is important to install the exact versions as described below.

## Installing Iris via opam

The easiest, and recommend, way of installing Iris and its dependencies is via
the OCaml package manager opam (2.0.0 or newer). You first have to add the Coq
opam repository and the Iris development repository (if you have not already
done so earlier):

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

Once you got opam set up, run `make build-dep` to install the right versions
of the dependencies.

Run `make -jN` to build the full development, where `N` is the number of your
CPU cores.

To update, do `git pull`.  After an update, the development may fail to compile
because of outdated dependencies.  To fix that, please run `opam update`
followed by `make build-dep`.

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

## Generating the exercises

If you want to contribute to the tutorial, note that the files in `exercises/`
are generated from the corresponding files in `solutions/`. Run `make exercises`
to re-generate those files. This requires `gawk` to be installed (which should
usually be available on Linux, and on macOS can be installed with
`brew install gawk`).

The syntax for the solution files is as follows:
```
(* SOLUTION *) Proof.
  solution here.
Qed.
```
is replaced by
```
Proof.
  (* exercise *)
Admitted.
```
and the more powerful
```
(* BEGIN SOLUTION *)
  solution here.
(* END SOLUTION BEGIN TEMPLATE
  exercise template here.
END TEMPLATE *)
```
is replaced by
```
  exercise template here.
```
