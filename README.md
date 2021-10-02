# polonius-abella

## What is this?
In [polonius](https://github.com/rust-lang/polonius), there are two datalog rules: naive and datafrog-opt.

This repo use [abella](http://abella-prover.org/) to prove that naive is equivalent to datafrog-opt:
```
naive_error => datafrog_opt_error  AND
datafrog_opt_error => naive_error 
```

`datafrog_opt_error => naive_error` is not so difficulty, 

but `naive_error => datafrog_opt_error` is not trival. 

I define another set of rules: `my_subset` and `my_origin_contains_loan_on_entry` to fix the gap.

I only rely on one axiom: `origin_live_on_entry Origin Point` is conflicted with `!origin_live_on_entry Origin Point`

## How to run
```
abella datafrog_opt.thm
```

## TODO
I didn't care placeholder in naive. I guess placeholder loan will never be invalidated ?
