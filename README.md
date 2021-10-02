# polonius-abella

## What is this?
In [polonius](https://github.com/rust-lang/polonius), there are two datalog rules: naive and datafrog-opt.

This repo use [abella](http://abella-prover.org/) to prove that naive is equivalent to datafrog-opt.

## How to run
```
abella datafrog_opt.thm
```

## How to prove 
Just to prove 
```
naive_error => datafrog_opt_error  AND
datafrog_opt_error => naive_error 
```

`datafrog_opt_error => naive_error` is not so difficulty, 

but `naive_error => datafrog_opt_error` is not trival. 

I define another set of rules: `my_subset` and `my_origin_contains_loan_on_entry` to fix the gap.

## Axiom needed

I only rely on one axiom(lemma without proof): `origin_live_on_entry Origin Point` is conflicted with `!origin_live_on_entry Origin Point`.

At any point, an origin must either be *live* or *dead*.


## TODO
I didn't care placeholder in naive. I guess placeholder loan will never be invalidated ?
