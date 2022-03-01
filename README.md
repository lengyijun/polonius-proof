# polonius-abella

## What is this?
In [polonius](https://github.com/rust-lang/polonius), there are two datalog rules: naive and datafrog-opt.

This repo use [abella](http://abella-prover.org/) and Agda to prove that they are equivalent. 
(dependently, and slightly different lemmas)

## How to run abella version
```
abella datafrog_opt.thm
```

See `Proof completed.` in output.

## How to run Agda version
In `emacs two.agda`, `C-c C-l`

See `Agda checked`.

## How to prove 
Just to prove 
```
naive_error => datafrog_opt_error (Theorem Naive2DatafrogOpt)  AND
datafrog_opt_error => naive_error (Theorem DatafrogOpt2Naive)
```

`datafrog_opt_error => naive_error` is not so difficulty, 

but `naive_error => datafrog_opt_error` is not trival. 

I define another set of rules: `my_subset` and `my_origin_contains_loan_on_entry` to fix the gap.

## Axiom needed

I only rely on one axiom(lemma without proof): `origin_live_on_entry Origin Point` is conflicted with `!origin_live_on_entry Origin Point`.

At any point, an origin must either be *live* or *dead*.


## Benefit of this proof
We don't need to worry about the correctness of datafrog-opt.
The tests only serve for the correctness of implementation.

## TODO
I didn't care placeholder in naive. I guess placeholder loan will never be invalidated ?
