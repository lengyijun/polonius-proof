# polonius-abella

## What is this?
In [polonius](https://github.com/rust-lang/polonius), there are two datalog rules: naive and datafrog-opt.

This repo use [abella](http://abella-prover.org/) to prove that naive is equivalent to datafrog-opt:
```
naive_error => datafrog_opt_error  AND
datafrog_opt_error => naive_error 
```

## How to run
```
abella datafrog_opt.thm
```

## TODO
I didn't care placeholder in naive. I guess placeholder loan will never be invalidated ?
