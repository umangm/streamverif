
# StreamVerif : Automata Based Verification of Uninterpreted Programs


### Instructions for artifact of 'Deciding Memory Safety for Single-Pass Heap-Manipulating Programs', POPL 2020

#### Dependencies:

1. Ocaml version `4.07.0`
2. Ocaml packages: `core (0.11.3)`, `dune (1.2.1)`, `menhir (20180905)`

On Linux, use your package manager to install opam. For example, in Ubuntu this would be:
```
sudo apt install opam
```
Next use opam to install Ocaml 4.07.0 and the packages.
```
opam switch create 4.07.0
opam install core dune menhir
```

#### Build instructions

```
dune build main.exe
```

#### Reproducing results from the paper.
```
./scripts/evaluation.py
```
Running that script will create an output files under the "output" directory for each test program in the "tests" directory.
