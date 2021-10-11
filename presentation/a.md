---
theme: gaia
_class: lead
paginate: true
backgroundColor: #fff
---

# **Use Abella to prove equivalence of datalog rules**

In Polonius (the new Rust borrow checker)

By YIJUN Leng 

---
# Self introduction

vim
manjaro
ps aux

---
# WARMUP: Compile pass? Run pass?
```
#include<iostream>     
#include<vector>
using namespace std;

int main(){                          fn main() {            
  vector<int> v={12};                    let mut v=vec![12];
  auto x=&v[0];                          let x=&v[0];
  cout<<*x<<endl;                        dbg!(x);
                                     
  v.reserve(100);                        v.reserve(100);
  cout<<*x<<endl;                        dbg!(x);
}                                    }                       
```

<!-- left cpp: can compile,  can't run -->
<!-- right rust: can't compile -->

---
# How Rust borrow checker(NLL) work
1. identify mutable/immutable borrow
2. each borrow's live span (in lines)
3. check conflict (mutable borrow and immutable borrow at same line)

```
1 fn main() {            
2     let mut v=vec![12];
3     let x=&v[0];
4     dbg!(x);
5     v.reserve(100);
6     dbg!(x);
7 }                       
```

---
# Lightly desugared

```
1 fn main() {            
2     let mut v=vec![12];
3     let x=&v[0];
4     dbg!(x);
5     Vec::reserve(&mut v, 100);
6     dbg!(x);
7 }                       
```

multiple immutable borrows / one mutable borrow 

mutable borrow: L5 
immutable borrow: L6 L5 L4

---
# The problem of NLL 

```rust
fn get_or_insert(
    map: &mut HashMap<u32, String>,
) -> &String {
    match map.get(&22) {
        Some(v) => v,
        None => {
            map.insert(22, String::from("hi"));
            &map[&22]
        }
    }
}
```

--- 

```
error[E0502]: cannot borrow `*map` as mutable because also borrowed as immutable
 --> src/main.rs:11:13
  |
3 |   map: &mut HashMap<u32, String>,
  |        - let's call the lifetime of this reference `'1`
4 | ) -> &String {
5 |   match map.get(&22) {
  |         --- immutable borrow occurs here
6 |     Some(v) => v,
  |                - returning this value requires `*map` is borrowed for `'1`
7 |     None => {
8 |       map.insert(22, String::from("hi"));
  |       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ mutable borrow occurs here
```

---

# Lightly desugared

```rust
fn get_or_insert<'a>(
    map: &'a mut HashMap<u32, String>,
) -> &'a String {
    match HashMap::get(&*map, &22) {
        Some(v) => v,
        None => {
            HashMap::insert(&mut *map, 22, String::from("hi"));
            &map[&22]
        }
    }
}
```
https://nikomatsakis.github.io/rust-belt-rust-2019/
https://www.youtube.com/watch?v=_agDeiWek8w&t=329s&ab_channel=RustBeltRustConference

---

# How Polonius work?

```rust
cargo  rustc  -- -Zpolonius
// or
rustc -Zpolonius main.rs 
```

Polonius is based on datalog.

Compiler team created two set of datalog rules: 
1. naive 
2. datafrog-opt

---
![bg](naive.png )
![bg](datafrog-opt.png )

---

![bg left:35% 80%](liveness.drawio.png )

In practise, naive = datafrog-opt.

In logic, naive = datafrog-opt (not intuitively)

But how do we formally prove it?
(This problem is first proposed by me, and first solved by me.)

![width:500px](polonius-benchmark.png )

<!-- compiler emit a lot of facts: loan_issued_at, subset_base, .. -->
<!-- polonius take facts as input -->

---
# Choose a proof assistant to prove equivalence of datalog rules

- Isabelle
- Z3
- Lean3 Lean4
- lambda prolog
    Teyjus
    ELPI(OCaml)
    **Abella(OCaml)**: suitable to express datalog

A lot of under developing...

--- 
# Steps
1. use Abella to describe datalog
1.1 input
1.2 naive and datafrog-opt
2. datafrog_opt_error => naive_error
3. naive_error => datafrog_opt_error

![]( do2naive_question.drawio.png )

---
# 1. Use Abella to describe datalog
```
Kind origin type.
Kind loan type.
Kind point type.

Type origin_live_on_entry origin -> point -> prop.
Type loan_issued_at origin -> loan -> point -> prop.
Type cfg_edge point -> point -> prop.
Type loan_invalidated_at loan -> point -> prop.
Type not_loan_killed_at loan -> point -> prop.
Type subset_base origin -> origin -> point -> prop.
```

---

# 1. Use Abella to describe datalog
```
Define  naive_subset: origin -> origin -> point -> prop,
        naive_origin_contains_loan_on_entry: origin -> loan -> point -> prop,
        naive_loan_live_at: loan -> point -> prop,
        naive_errors: loan -> point -> prop  by

naive_subset Origin1  Origin2  Point  :=
  subset_base Origin1  Origin2  Point ;

naive_subset Origin1  Origin2  Point2  :=
  exists Point1,
  naive_subset Origin1  Origin2  Point1 /\
  cfg_edge Point1  Point2 /\
  origin_live_on_entry Origin1  Point2 /\
  origin_live_on_entry Origin2  Point2 ;
...
```

---
# 2. datafrog_opt_error => naive_error

```
Theorem DatafrogOpt2Naive:
  forall Loan,
  forall Point,
  datafrog_opt_errors Loan Point ->
  naive_errors Loan Point.
```

---
# Two important inspection

```
/* Lemma24 */
datafrog_opt_subset Origin1 Origin2 Point 
=> naive_subset Origin1 Origin2 Point

/* Lemma26 */
datafrog_origin_contain_loan_on_entry Origin Loan Point
=> naive_origin_contains_loan_on_entry Origin Loan Point
```
<!-- 为什么第一个lemma就是24, 因为前面23个全错了 -->

---
# Prove Lemma24

```
Theorem Lemma24:
  (
    forall Point,
    forall Origin1,
    forall Origin2,
    datafrog_opt_subset Origin1 Origin2 Point ->
    naive_subset Origin1 Origin2 Point
  ) /\ (
    forall Point1,
    forall Point2,
    forall Origin1,
    forall Origin2,
    dying_can_reach Origin1 Origin2 Point1 Point2  ->
    naive_subset Origin1 Origin2 Point1
  ).
```

---

# induction
```
Theorem even_odd : forall x , even x -> odd ( s x ) .
```

```
induction on 1.
```

Induction on one rule.

---

# Mutual induction: break cyclic proof

```
Define even : nat -> prop ,
       odd  : nat -> prop by
even z ;
even ( s N ) := odd N ;
odd ( s N ) := even N .

Theorem even_odd_nat :
  ( forall N , even N -> is_nat N ) /\ 
  ( forall N , odd N -> is_nat N ) .
```

```
induction on 1 1.
```


---
# 3. naive_error => datafrog_opt_error

Can we follow the trick before?
```
/* Lemma25 */
naive_subset Origin1 Origin9 Point
=> datafrog_opt_subset Origin1 Origin9 Point 

/* Lemma27 */
naive_origin_contains_loan_on_entry Origin Loan Point
=> datafrog_origin_contain_loan_on_entry Origin Loan Point
```

**WRONG!**

--- 
# Try applying small patches...

```
/* Lemma25 */
naive_subset Origin1 Origin9 Point
=> datafrog_opt_subset Origin2 Origin9 Point 

/* Lemma27 */
naive_origin_contains_loan_on_entry Origin9 Loan Point
=> datafrog_origin_contain_loan_on_entry Origin2 Loan Point
```

**STILL WRONG!**

Definitely, it's not trival to construct meaningful relationship from naive to datafrog-opt.

---

# Why we meet diffculity here ?
`naive_subset` has no least fixed point.
=> `naive_subset` should not extensible along Point
=> What if `naive_subset` is defined as ...

```
subset(origin1, origin2, point2) :-
  subset(origin1, origin2, point1),
  cfg_edge(point1, point2),
  origin_live_on_entry(origin1, point2),
  origin_live_on_entry(origin2, point2).
```

---

# Redefine my_* with datafrog_opt_*

![](myerror.drawio.png)

---
```
my_subset Origin1  Origin2  Point  :- datafrog_opt_subset Origin1  Origin2  Point .
my_subset Origin1  Origin3  Point  :-
  datafrog_opt_subset Origin1  Origin2  Point , 
  my_subset Origin2  Origin3  Point .
```

are similar to the classical recursive type definition:

```
Kind nat type.
Type zero nat.
Type s nat -> nat.
```

```
Kind list type .
Type empty list.
Type cons nat -> list -> list.
```
--- 

```
my_subset Origin1  Origin2  Point  :- datafrog_opt_subset Origin1  Origin2  Point .
my_subset Origin1  Origin3  Point  :-
  datafrog_opt_subset Origin1  Origin2  Point , 
  my_subset Origin2  Origin3  Point .
```

```
# naive
subset(origin1, origin2, point) :- subset_base(origin1, origin2, point).

subset(origin1, origin2, point2) :-
  subset(origin1, origin2, point1),
  cfg_edge(point1, point2),
  origin_live_on_entry(origin1, point2),
  origin_live_on_entry(origin2, point2).

subset(origin1, origin3, point) :-
  subset(origin1, origin2, point),
  subset(origin2, origin3, point).
```

--- 

# Steps
1. use Abella to describe datalog
1.1 input
1.2 naive and datafrog-opt
2. datafrog_opt_error => naive_error (100 LOC)
3. naive_error => datafrog_opt_error (400 LOC)


---
# Reaction from Rust community
![](zulip.png)
https://rust-lang.zulipchat.com/#narrow/stream/186049-t-compiler.2Fwg-polonius/topic/Prove.20equivalence.20between.20.20naive.20and.20datafrog-opt

---
# Conclusion

We prove two algorithms in Polonius produce the same result, based on only one axiom.

## Main tactic

(mutual) induction

--- 
# Benefit from this proof

Improve interpretability of prolog.

We don't need to test the correctness of datafrog-opt any more.
We only need to test the implementation correctness.

Helpful to verify new datalog rules before implementation.

---
# Future work
Another approach to prove?

# Personal future work 
1. Work on relationship between mlsub(2017) and ml-simple(2020)
2. Make Polonius the default borrow checker of Rust

---

# Why we need proof assistant?
- Succinctness
- Repeatability
- Discover problem in proof

<!-- 证明完之后，我一次都没有复查过逻辑，因为我知道一定是对的 -->

--- 

# Express negative in Abella

```
Theorem OriginLiveAxiom:                                                                                                    
  forall Origin,                                                                                                   
  forall Point,                                                                                                    
  (origin_live_on_entry Origin Point ) \/ ( origin_live_on_entry Origin Point -> false).                           
skip.
```
A function is the negative of fact!

```
H1: origin_live_on_entry Origin Point 
H2: origin_live_on_entry Origin Point -> false
```
We can use `search` tactic to get false quickly.
TODO: How to express three mutually exclusive states?

---

# Paradox in Abella

Both true and false!
Abella will give a warning.

```
Define p : prop by
p := p -> false .

Theorem p_true : p .
unfold . intros . case H1 ( keep ) . apply H2 to H1 .

Theorem notp_true : p -> false .
intros . case H1 ( keep ) . apply H2 to H1 .
```

---
# Axiom in Abella
```
/* The only axiom introduced */
Theorem OriginLiveAxiom:                                                                                                    
  forall Origin,                                                                                                   
  forall Point,                                                                                                    
  (origin_live_on_entry Origin Point ) \/ ( origin_live_on_entry Origin Point -> false).                           
skip.
```
`skip` is the only way to express axiom.

---

# Abella is powerful
Abella is suitable to express datalog.

But we only utilize a little functionality in Abella here.

Coinduction, nable, lambda calculas, pi calculas ...

# But Abella can't prove all truth !
Gödel's incompleteness theorems 

---

# Polonius can't deal with 1
```
struct S;

fn main() {
    let s=S;
    let mut v:Vec<&S>=vec![];
    v.push(&s);
    v.pop();
    drop(s);
    // although v has remove the last element,
    // but still throw error
    v;
}
```

---

# Polonius can't deal with 2

```
use std::collections::binary_heap::BinaryHeap ;

fn main() {
    let mut heap = BinaryHeap::new();
    if let Some(_) = heap.peek_mut() {
        heap.push(4);
    };
}
```

THINKING: compare with P5

https://github.com/rust-lang/rust/issues/70797


---
# What else can Polonius help?
Static program analysis: safe move

https://github.com/rust-lang/rust-clippy/issues/7459

https://github.com/rust-lang/rust-clippy/issues/7512

[redundant_clone](https://rust-lang.github.io/rust-clippy/master/index.html#redundant_clone)

---

# Datalog engines
1. swi(scala)

2. racket: 
https://docs.racket-lang.org/datalog/Tutorial.html
no negative？

3. souffle (c++): parallel. Rust is using

4. bddbddb (java): use binary decision diagram. Rely on NP problem.

5. https://github.com/vmware/differential-datalog
6. gnu-prolog gprolog (C)

---
# Datalog engines

![](datalog-benchmark.jpg )

---
# Q&A

Full proof here: 
https://github.com/lengyijun/polonius-abella

Welcome to reviewing.

