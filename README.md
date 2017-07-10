# sequents [![Build Status](https://travis-ci.com/ayberkt/sequents.svg?token=2eB5JJ87XAYaE2ZJnQaJ&branch=master)](https://travis-ci.com/ayberkt/sequents)

**sequents** is an implementation of [Roy Dyckhoff's LJT](https://rd.host.cs.st-andrews.ac.uk/publications/jsl57.pdf)—a sequent
calculus for intuitionistic logic that is decidable and does _not_ need loop
checking

## Building

First make sure that you have `smlnj` installed. To build, run
```
./script/build.sh
```

## Trying out

Let's prove the commutativity of conjunction `A ∧ B ⊃ B ∧ A`. Using the ASCII
approximations of the connectives, we can pipe this proposition into `sequents`.
```
➜ echo "A /\ B => B /\ A" | ./sequents
```
which gives the following:
```
Proof found!
Theorem: A ∧ B ⊃ B ∧ A.
• A, B ----> B by init
• A ∧ B ----> B by ∧L

• B, A ----> A by init
• A ∧ B ----> A by ∧L

• A ∧ B ----> B ∧ A by ∧R
• ----> A ∧ B ⊃ B ∧ A by ⊃R
QED
```

You can also generate LaTeX with `--latex` flag:
```
➜ echo "A /\ B => B /\ A" | ./sequents --latex > out.tex
➜ pdflatex out.tex
```
![derivation](resources/derivation.png)
