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

<font size="6">Email: [d.castro-perez@kent.ac.uk](maito:d-castro-perez@kent.ac.uk)</font>

<br>
<br>

<em>PLAS Seminar (8/04/2024)</em>

---
#### Motivation

+ Reasoning about nonstructural recursion in proof assistants is hard due
to nontermination issues.
<br>

+ Recursion schemes have easy-to-use associated equational theories, which can
  be used for *program calculation*. Such program calculation techniques can
capture program optimisations such as *shortcut deforestation*, or
*semi-automatic parallelisations*.
<br>

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

Coq's `Fix` combinator can be used to build a recursive function from a 
non-recursive definition. 

This non-recursive definition (line 7) is parameterised by the recursive call,
and it can only be used on _smaller_ inputs (i.e. on the elements `y` such that
`R y x`):

<br>

```coq [1|5|6-7]
About Fix.

Fix :
  forall [A : Type] [R : A -> A -> Prop],
    well_founded R -> 
    forall P : A -> Type, 
      (forall x : A, (forall y : A, R y x -> P y) -> P x) -> 
      forall x : A, P x

```

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

---
### Hylomorphisms

Divide-and-conquer computations are known in the functional programming
literature as **hylomorphisms**.

The `divide` function divides the input and produces a structure `f a`.  The
`conquer` part combines already processed sub-inputs in a structure `f b` into
the return type `b`.

<br>

```haskell
hylo :: Functor f => (f b -> b) -> (a -> f a) -> a -> b
hylo conquer divide = h
  where h x = conquer (fmap h (divide x))
```

<br>

Note that we know nothing of the structure `f`, except that we can keep
applying the divide and conquer computation recursively on every element that
it contains. Furthermore, even if `f` was fully known, we cannot know how
`divide` divides the inputs. Therefore, **we cannot guarantee termination** of
hylomorphisms.

---
### Recursion Schemes as Hylomorphisms

Hylomorphisms are general enough to represent other recursion schemes, such as
*maps*, *folds*, *unfolds*, *dynamic programming algorithms*,
*mutual-recursion*, ... 

In fact,

<br>

> Every recursion scheme is an instance of a hylomorphism 

<p text-align="right"> (Hinze et. al)</p>

<br>

---
### Example: List foldr as a Hylomorphism

```haskell
in_list :: Maybe (a, [a]) -> [a]
in_list Nothing = []
in_list (Just (h, t)) = h : t

out_list :: [a] -> Maybe (a, [a])
out_list [] = Nothing
out_list (h : t) = Just (h, t)

fold_hylo :: (a -> b -> b) -> b -> [a] -> b
fold_hylo f z = hylo alg out_list
  where
    alg :: Maybe (a, b) -> b
    alg Nothing = z
    alg (Just (h, t)) = f h t
```

---
### Algebras

Recall the types of *alg* and *in_list*:

```haskell
in_list :: Maybe (a, [a]) -> [a]
alg     :: Maybe (a,  b ) ->  b
```

We can generalise these types:
```haskell
data ListF a b = NilF | ConsF a b
instance Functor (ListF a) where
  fmap f NilF = NilF
  fmap f (ConsF a b) = ConsF a (f b)

in_list :: ListF a [a] -> [a]
alg     :: ListF a  b  ->  b
```

<br>

In general, given an endo-functor $F$, an **algebra** is an object $X$ (the
*carrier* of the algebra), and a morphism $F\ X \to X$.

---
### Initial Algebras


---
### Coalgebras

---
## "Extractable" Containers

---
### Avoiding the Functional Extensionality Axiom (I)

To avoid the functional extensionality axiom, we restrict to *setoids*:

<br>
<br>

```coq
Reserved Notation "f =e g" (at level 70, no associativity).
Class setoid A : Type :=
  MkSetoid
    { eqRel : A -> A -> Prop;
      e_refl : forall x, eqRel x x;
      e_sym : forall x y, eqRel x y -> eqRel y x;
      e_trans : forall x y z, eqRel x y -> eqRel y z -> eqRel x z;
    }.

Notation "f =e g" := (eqRel f g).
```

---
### Avoiding the Functional Extensionality Axiom (and II)

We only work with *morphisms* that are *respectful* (i.e. they map related
inputs to related outputs):

<br>
<br>

```coq
Structure morph :=
  MkMorph { app :> A -> B;
            app_eq : forall x y, x =e y -> app x =e app y
          }.

Notation "x ~> y" := (morph x y).
```

---
### Containers

Containers are defined by a pair of a type of shapes `Sh`, and a family
of positions in this shape `Pos`. 

<br>

In our work, we define the family of positions by requiring a type of **all**
positions, together with a **decidable** predicate that determines whether a
position is valid in a shape.

<br>

```coq
Class Cont `{Esh : setoid Sh} (P : Type) :=
  { valid : Sh * P ~> bool
  }.

Record Pos `{Cont Sh P} (s : Sh) :=
  MkElem {
      val : P;
      Valid : valid (s, val)
    }.


```

---
### Containers and Functors

Given a container `F`, its  **extension** (defined below) is a functor. 

```coq
Record App `{F : Cont Sh P} (X : Type) :=
  MkCont
    { shape : Sh;
      cont : Pos shape -> X
    }.
```

---
## Mechanising Hylomorphisms in Coq

---
## Example

    </textarea>
</section>
