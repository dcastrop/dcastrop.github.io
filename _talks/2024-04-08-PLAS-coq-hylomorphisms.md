---
layout: slide
title: Mechanising Recursion Schemes with Magic-Free Coq Extraction
slides: true
venue: PLAS Seminar @ University of Kent
venueurl: https://www.kent.ac.uk/events/event/66301/mechanising-recursion-schemes-with-magic-free-coq-extraction-david-castro-perez
date: 2024-04-08
author: David Castro-Perez
description: 
comments: true
tags:
  - coq
  - hylomorphisms
  - code extraction
---

<style>
.container{
    display: flex;
}
.col{
    flex: 1;
}
</style>
<section data-markdown>
    <textarea data-template>
# Mechanising Recursion Schemes with Magic-Free Coq Extraction

<br>

<ins>David Castro-Perez</ins>, [Marco Paviotti](mailto:m.paviotti@kent.ac.uk), [Michael Vollmer](mailto:m.vollmer@kent.ac.uk)

<font size="-0.5">Email: [d.castro-perez@kent.ac.uk](maito:d-castro-perez@kent.ac.uk)</font>

<br>
<br>

<em>PLAS Seminar (8/04/2024)</em>

---
#### Motivation

+ Reasoning about nonstructural recursion in proof assistants is hard due
to nontermination issues.

+ Recursion schemes have easy-to-use associated equational theories, which can
  be used for *program calculation*. Such program calculation techniques can
capture program optimisations such as *shortcut deforestation*, or
*semi-automatic parallelisations*.

+ Common encodings of recursion schemes in Coq come with compromises:
  - extracting to OCaml code with unsafe casts;
  - using complex representations which do not follow the common, well-known
    recursive structure of algorithms;
  - the use of controversial axioms; 

---
#### Contributions

- A **fully-axiom-free** mechanisation of *hylomorphisms* in Coq.
- Code extraction to OCaml **without unsafe casts**.
- Encoding and using the equational theory of hylomorphisms for program
  optimisations.


---
## Non-structural Recursion in Coq

---
### Divide and Conquer Algorithms

```ocaml
let rec qsort xs =
  match divide xs with 
  | None -> []
  | Some (pivot, (smaller, larger)) -> qsort smaller @ (pivot::qsort larger)
```

---
### Divide and Conquer Algorithms in Coq

Definition rejected by Coq:

<br><br>

```coq
Fixpoint qsort (xs : list nat) :=
  match divide xs with
  | None => nil
  | Some (pivot, (smaller, larger)) => qsort smaller ++ pivot :: qsort larger
  end.
```

<br><br>

<b>The problem</b>: The arguments to the recursive calls are not structurally smaller to `xs`.

```coq
Error:
Recursive definition of qsort is ill-formed.
...
Recursive call to qsort has principal argument equal to "smaller" instead of a subterm of "xs".
```

---
### Well-founded Recursion in Coq

```coq
Require Coq.Program.Wf.
Program Fixpoint qsort (xs : list nat) {measure (length xs) } :=
  match divide xs with
  | None => nil
  | Some (pivot, (smaller, larger)) => qsort smaller ++ pivot :: qsort larger
  end.
Next Obligation.
```

<br><br>

This leaves us with the following goal:

```coq
xs : list nat
qsort : forall xs0 : list nat, length xs0 < length xs -> list nat
pivot : nat
smaller, larger : list nat
Heq_anonymous : Some (pivot, (smaller, larger)) = divide xs
============================
length smaller < length xs
```

---
### Coq's Well-founded Fixpoint Combinator

If we prove that our function respects a *well-founded* relation, we can use
Coq's `Fix` combinator to build non-structurally recursive functions:

```coq [1|5|6-7]
About Fix.

Fix :
  forall [A : Type] [R : A -> A -> Prop],
    well_founded R -> 
    forall P : A -> Type, 
      (forall x : A, (forall y : A, R y x -> P y) -> P x) -> 
      forall x : A, P x

```

<br><br>
---
## Well-founded Relations and Accessibility Proofs

A relation is _well-founded_ if it has no infinite decreasing chains.

<br>

```coq  [7|4-5]
Variable A : Type.
Variable R : A -> A -> Prop.

Inductive Acc (x : A) : Prop :=
  Acc_intro : (forall y:A, R y x -> Acc y) -> Acc x.

Definition well_founded (R : A -> A -> Prop) := forall a:A, Acc R a.

```

<br><br>
The Fixpoint combinator in Coq uses recursion **on accessibility proofs** (`Acc_inv a h`):
```coq [1-5|5]
Variable P : A -> Type.
Variable F : forall x:A, (forall y:A, R y x -> P y) -> P x.

Fixpoint Fix_F R (x : A) (a : Acc R x) : P x :=
    F (fun (y:A) (h:R y x) => Fix_F (Acc_inv a h)).
```

---
## Problems with Well-founded Recursion

+ Equational reasoning is hard. E.g.

```coq [7|9-10]
About Fix_eq.

Fix_eq :
  forall [A : Type] [R : A -> A -> Prop] (Rwf : well_founded R) (P : A -> Type)
    (F : forall x : A, (forall y : A, R y x -> P y) -> P x),
      (forall (x : A) (f g : forall y : A, R y x -> P y), 
        (forall (y : A) (p : R y x), f y p = g y p) -> F x f = F x g) ->
      forall x : A, 
        Fix Rwf P F x = 
        F x (fun (y : A) (_ : R y x) => Fix Rwf P F y)
```

<br>

+ Non-compositional reasoning<!-- .element: class="fragment" -->

---
## Recursion Schemes

---
### Intuition

+ Recursion schemes are *higher-order functions* that build recursive programs.

+ Familiar examples include common maps & folds (examples in Haskell syntax):

```haskell
map f [] = []
map f (x : xs) = f x : map f xs

foldr f z [] = z
foldr f z (x : xs) = f x (foldr f z xs)
```

+ Recursion schemes can capture more complex patterns of recursion, such as
*divide and conquer* computations:
```haskell
dc :: ([b] -> b) -> (a -> [a]) -> a -> b
dc conquer divide = h
  where h x = conquer (map h (divide x))
```

---
### Hylomorphisms

We can generalise our divide and conquer recursion scheme.

Instead of dividing our input into a list of sub-inputs, we can use an 
arbitrary *functor* `f`:

<br>

```haskell
hylo :: Functor f => (f b -> b) -> (a -> f a) -> a -> b
hylo conquer divide = h
  where h x = conquer (fmap h (divide x))
```

<br>

These are called **hylomorphisms** in the literature.

---
## Recursion Schemes as Hylomorphisms

Hylomorphisms are general enough to represent other recursion schemes, such as
*maps*, *folds*, *unfolds*, *dynamic programming algorithms*,
*mutual-recursion*, ... 

In fact,

<br>

> Every recursion scheme is an instance of a hylomorphism 

<p text-align="right"> (Hinze et. al)</p>

<br>

---
# "Extractable" Containers

---
# Mechanising Hylomorphisms in Coq

---
# Example

    </textarea>
</section>
