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

##### The problem <!-- .element: class="fragment" data-fragment-index="2" -->

The arguments to the recursive calls are not structurally smaller to `xs`. 

<!-- .element: class="fragment" data-fragment-index="2" -->

<br>

```coq
Error:
Recursive definition of qsort is ill-formed.
...
Recursive call to qsort has principal argument equal to "smaller" instead of a subterm of "xs".
```

<!-- .element: class="fragment" data-fragment-index="2" -->

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

<br>

##### <!-- .element: class="fragment" data-fragment-index="2" -->

This leaves us with the following goal:

<!-- .element: class="fragment" data-fragment-index="2" -->

```coq
xs : list nat
qsort : forall xs0 : list nat, length xs0 < length xs -> list nat
pivot : nat
smaller, larger : list nat
Heq_anonymous : Some (pivot, (smaller, larger)) = divide xs
============================
length smaller < length xs
```

<!-- .element: class="fragment" data-fragment-index="2" -->

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
### Well-founded Relations and Accessibility Proofs

A relation is _well-founded_ if it has no infinite decreasing chains.

<br>

```coq  [7|4-5]
Variable A : Type.
Variable R : A -> A -> Prop.

Inductive Acc (x : A) : Prop :=
  Acc_intro : (forall y:A, R y x -> Acc y) -> Acc x.

Definition well_founded (R : A -> A -> Prop) := forall a:A, Acc R a.

```

##### <!-- .element: class="fragment" data-fragment-index="3" -->


The Fixpoint combinator in Coq uses recursion **on accessibility proofs**
`Acc_inv a h`
<!-- .element: class="fragment" data-fragment-index="3" -->

<br>

```coq
Variable P : A -> Type.
Variable F : forall x:A, (forall y:A, R y x -> P y) -> P x.

Fixpoint Fix_F (x : A) (a : Acc R x) : P x :=
    F (fun (y:A) (h:R y x) => Fix_F (Acc_inv a h)).
```
<!-- .element: class="fragment" data-fragment-index="3" -->

---
## Divide and Conquer with Well-founded Recursion

+ Equational reasoning is hard. E.g. `$\text{Fix}\ F = F\ (\text{Fix}\ F)$`:

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

+ Other approaches exist (e.g. equations) with similar problems <!--
  .element: class="fragment" -->

---
## Recursion Schemes

---
### Intuition

+ Recursion schemes are *higher-order functions* that build recursive programs.

+ Familiar examples include common maps & folds (examples in Haskell syntax):

#####

```haskell
map f [] = []
map f (x : xs) = f x : map f xs

foldr f z [] = z
foldr f z (x : xs) = f x (foldr f z xs)
```

---
### Hylomorphisms (informally)

Divide-and-conquer computations are known in the functional programming
literature as **hylomorphisms**.

`divide` "splits" the input and produces a structure `f a`.


`conquer` combines already processed elements in a structure `f b`.

<br><br>

```haskell
hylo :: Functor f => (f b -> b) -> (a -> f a) -> a -> b
hylo conquer divide = h
  where h x = conquer (fmap h (divide x))
```

##### <!-- .element: class="fragment" data-fragment-index="2" -->

---
### Recursion Schemes as Hylomorphisms

Hylomorphisms are general enough to represent other recursion schemes, such as
*maps*, *folds*, *unfolds*, *dynamic programming algorithms*,
*mutual-recursion*, ... 

<br><br>

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
```

<br><br>

```haskell
fold_hylo :: (a -> b -> b) -> b -> [a] -> b
fold_hylo f z = hylo alg out_list
  where
    alg :: Maybe (a, b) -> b
    alg Nothing = z
    alg (Just (h, t)) = f h t
```

---
### Algebras (slightly more formally)

Recall the types of *alg* and *in_list*:

```haskell
in_list :: Maybe (a, [a]) -> [a]
alg     :: Maybe (a,  b ) ->  b
```

<br>

We can generalise them:
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

<br>

`([a], in_list)` and `(b, alg)` are examples of algebras.


---
### Initial Algebras and Catamorphisms

Given an endo-functor `$F$`, an initial algebra is an `$F$`-algebra such that
there is an unique morphism from this initial algebra to any other algebra.

<br>

Initial algebras are *unique up to isomorphism* (due to initiality).

<br>

The unique morphism between the carriers of an initial algebra and some other
algebra is called a **catamorphism**. They correspond to folds over inductive
types.

<br>

Example initial (`ListF a`)-algebra:

```haskell
in_list :: ListF a [a] -> [a]
in_list NilF        = []
in_list (ConsF a b) = a : b

out_list :: [a] -> ListF a [a]
out_list []      = NilF
out_list (a : b) = ConsF a b

lcata :: (ListF a b -> b) -> [a] -> b
lcata a = f
  where
    f = a . fmap f . out_list
```

---
### Least Fixed Point of a Functor

Given a functor `$F$`, `$(\mu\ F, \text{in}_F)$` is an initial `$F$`-algebra.

`$$
\text{in}_F : F \ (\mu F) \to \mu F
$$`

+ Not all functors have a fixed point.
+ Defining least fixed points in Coq can be problematic (more in a few slides)


##### In Haskell: <!-- .element: class="fragment" data-fragment-index="2" -->

```haskell
newtype Fix f = Fix (f (Fix f))

in :: f (Fix f) -> Fix f
in = Fix
```
<!-- .element: class="fragment" data-fragment-index="2" -->

<br>

`Fix (ListF a)` and `[a]` are isomorphic.

<!-- .element: class="fragment" data-fragment-index="2" -->
<!-- .element: class="fragment" data-fragment-index="2" -->


---
### Coalgebras

`$f$`-coalgebras are morphisms from `$a \to f\; a$`. E.g.

<br>

```haskell
out_list :: [a] -> ListF a [a]
out_list []      = NilF
out_list (a : b) = ConsF a b
```

---
### Terminal Coalgebras and Anamorphisms

Given an endo-functor `$F$`, a terminal coalgebra is an `$F$`-coalgebra such
that there is an unique morphism from any coalgebra to this terminal coalgebra.

<br>

The unique morphism between the carriers of any coalgebra and the terminal coalgebra
is called an **anamorphism**. They correspond to unfolds over coinductive
types.

Example terminal `ListF a`-coalgebra:

```haskell
lana :: (b -> ListF a b) -> b -> [a]
lana c = f
  where
    f = in_list . fmap f . c
```

---
### Recursive Coalgebras

Coalgebras do not necessarily terminate.

<br>

```haskell
infiniteStreamOfOnes :: [Int]
infiniteStreamOfOnes = lana (\x -> ConsF x x) 1
```

<br>

The coalgebra `\x -> ConsF x x` is **not** recursive.

<br>

A coalgebra is recursive if it can be applied only finitely many times:

* When used to build an anamorphism, it only produces finite trees.

---
### Hylomorphisms

Hylomorphisms are solutions to the equation

$$
f = a \circ F \ f \circ c
$$

<br>

```haskell
lhylo :: (b -> ListF t b) -> (a -> ListF t a) -> a -> b
lhylo a c = f
  where
    f = a . fmap f . c
```

---
### Problems Mechanising Hylomorphisms

```haskell
hylo :: Functor f => (f b -> b) -> (a -> f a) -> a -> b
hylo alg coalg = h
  where h = alg . fmap h . coalg 
```

<br><br>



* In Haskell, algebras and coalgebras coincide, but **not in Coq**.
* We must prove termination if we want to build `hylo` in Coq
* We need to define *least* and *greatest* fixed-points of functors.

---
## Formalising Hylomorphisms in Coq

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
### Functors in Coq

In Coq, we can represent functors as functions from `Type -> Type`, together
with the `fmap` function:

<br>

```coq
Class functor (F : Type -> Type) := {
  fmap : forall A B, (A -> B) -> F A -> F B;
  fmap_id : forall A, fmap (@id A) =e id;
  fmap_comp : forall A B C (f : B -> C) (g : A -> B), fmap (f \o g) =e fmap f \o fmap g;
}.
```

<br>

However, we cannot take fixed-points of such functors due to the strict positivity requirement.

<br>

```coq
Fail Inductive LFix (F : Type -> Type) := LFix_in { LFix_out : F (LFix F) }.

The command has indeed failed with message:
Non strictly positive occurrence of "LFix" in "F (LFix F) -> LFix F".
```

---
### Containers (first attempt)

We use containers to represent strictly positive types. These are equivalent to polynomial functors.

<br>

Containers are defined by a pair of a type of shapes `Sh`, and a family
of positions in this shape `Pos`. 

<br>
<br>

```coq
Variable Shape : Type.
Variable Position : Shape -> Type.
```

<br>

Given a container, its **extension** (defined below) is a functor. 

<br>

```coq
Record App (X : Type) :=
  MkCont
    { shape : Shape;
      contents : Position shape -> X
    }.

Definition fmap (f : A -> B) (x : App A) : App B
  := MkCont (shape x) (fun e => f (contents x e))
```

---
### Problems with Extracting and Reasoning about Containers

+ Reasoning about container equality

```coq [2,4]
k : Pos C s -> X
P1, P2 : valid s p
---------------------------
k (ValidPos p P1) = k (ValidPos p P2)
```

<br><br>

+ Extracting type families to OCaml leads to unsafe casts with `Obj.magic`

```ocaml [4]
let outT x =
  let { shape = s; cont = p } = x in
  (match s with
   | Some x0 -> Some (Pair ((Pair (x0, (Obj.magic p True))), (Obj.magic p False)))
   | None -> None)
```



---
### Extractable Containers


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
### Container Extensions (Functors)

```coq
Record App `{F : Cont Sh P} (X : Type) :=
  MkCont
    { shape : Sh;
      cont : Pos shape -> X
    }.
```

<br><br>

+ Coq can now extract `Pos s` equivalently to `P`
+ We can also use the UIP for proofs of the form `valid(s, val) = true`
  **without axioms**, thanks to the decidability of boolean equality.

---
### Equality of Container Extensions

```coq
Inductive AppR `{F : Cont Sh P} (X : Type) {e : setoid X}
           (x y : App F X) : Prop :=
  | AppR_ext
      (Es : shape x =e shape y)
      (Ek : forall e1 e2, val e1 = val e2 -> cont x e1 =e cont y e2).
```

---
### Fixed-points of Container Extensions

```coq
Inductive LFix  : Type := LFix_in { LFix_out : App F LFix }.

Definition l_in : App F (LFix F) ~> LFix F := (* *)
Definition l_out : LFix F ~> App F (LFix F) := (* *)

Lemma l_in_out : l_in \o l_out =e id.
Lemma l_out_in : l_out \o l_in =e id.
```

<br>
Equality of `LFix`:
<br>

```coq
Fixpoint LFixR (x y : LFix) : Prop :=
  let f_x := LFix_out x in
  let f_y := LFix_out y in
  shape f_x =e shape f_y /\
    (forall e1 e2, val e1 = val e2 -> LFixR (cont f_x e1) (cont f_y e2)).
```

---
## Mechanising Hylomorphisms in Coq

---
### Recursive coalgebras

```coq
Inductive RecF `{setoid A} (h : Coalg F A) : A -> Prop :=
  | RecF_fold x : (forall e, RecF h (cont (h x) e)) -> RecF h x.


Structure RCoalg `{eA : setoid A} :=
  Rec {
      coalg :> Coalg F A;
      recP : forall x, RecF coalg x
    }.
```

<br><br>

We provide mechanisms for defining recursive coalgebras, if they respect a
well-founded relation.

```coq
Lemma wf_coalg_rec `{setoid A} {B}
  (m : A -> B) (R : B -> B -> Prop) (WF : well_founded R)
  (c : Coalg F A) (RR : respects_relation c m R) : forall x, RecF c x.
(**)
Defined.
```

---
### Hylomorphisms in Coq

```coq
Definition hylo_def (a : Alg F B) (c : Coalg F A) : forall (x : A), RecF c x -> B
 := fix f x H :=
      match c x as h return (forall e : Pos (shape h), RecF c (cont h e)) -> B with 
        | MkApp s_x c_x => fun H => a (MkApp s_x (fun e => f (c_x e) (H e)))
      end (RecF_inv H).
```

---
### Hylomorphism Properties

Recursive hylomorphisms satisfy the following universal property:

<br>

```coq
Lemma hylo_univ (g : Alg F B) (h : RCoalg F A) (f : A ~> B) 
  : f =e hylo g h <-> f =e g \o fmap f \o h.
(* *)
Qed.
```

<br><br>

Some useful corollaries:
<br>
```coq
Lemma hylo_fusion_l (h1 : RCoalg F A) (g1 : Alg F B) (g2 : Alg F C)
  (f2 : B ~> C) (E2 : f2 \o g1 =e g2 \o fmap f2)
  : f2 \o hylo g1 h1 =e hylo g2 h1.
Proof.
(**)
Qed.

Lemma deforest (h1 : RCoalg F A) (g2 : Alg F C)
  (g1 : Alg F B) (h2 : RCoalg F B) (INV: h2 \o g1 =e id)
  : hylo g2 h2 \o hylo g1 h1 =e hylo g2 h1.
Proof.
(**)
Qed.
```

---
## Example

---
### Specifying the Behaviour

```coq
Record Ext (f : A ~> B) :=
  MkExt
    { target :> A -> B;
      tgt_eq : app f =e target;
    }.
```

---
### Quicksort Hylomorphism in Coq 

##### merge

```coq
Definition merge : App (TreeF unit int) (list int) ~> list int.
|{ x : (App (TreeF unit int) (list int)) ~>
           match x with
           | MkCont sx kx =>
               match sx return (Container.Pos sx -> _) -> _ with
               | Leaf _ _ => fun _ => nil
               | Node _ h => fun k => List.app (k (posL h)) (h :: k (posR h))
               end kx
           end
}|.
Defined.
```

---
### Quicksort Hylomorphism in Coq 

##### split

```coq
Definition c_split : Coalg (TreeF unit int) (list int).
|{ x ~> match x with
        | nil => a_leaf tt
        | cons h t =>
            let (l, r) := List.partition (fun x => x <=? h) t in
            a_node h l r
        end
}|.
Defined.
```

---
### Quicksort Hylomorphism in Coq 

##### proving that c_split terminates

```coq
Lemma split_fin : respects_relation c_split (@length int) lt.
Proof.
(**)
Qed.

Definition tsplit : RCoalg (TreeF unit int) (list int)
  := mk_wf_coalg wf_lt split_fin.
```

---
### Quicksort Hylomorphism in Coq 

##### Extraction

```coq
Definition qsort : Ext (cata merge \o rana tsplit).
  calculate.
  rewrite cata_ana_hylo.
  simpl; reflexivity.
Defined.
```

<br><br>

```ocaml
let rec qsort = function
  | [] -> [] 
  | h :: t ->
    let (l, r) = partition (fun x0 -> leb x0 h) t in
    let x0 = fun e -> qsort (match e with | Lbranch -> l | Rbranch -> r) in
    app (x0 Lbranch) (h :: (x0 Rbranch))
```

---
### Quicksort Hylomorphism in Coq 

##### fusing a subsequent traversal

```coq
Definition qsort_times_two
  : Ext (Lmap times_two \o cata merge \o rana tsplit).
(*... applying hylo_fusion ... *)
Qed.
```

<br><br>

```ocaml
let rec qsort_times_two = function 
  | [] -> []
  | h :: t ->
      let (l, r) = partition (fun x0 -> leb x0 h) t in
      let x0 = fun p -> qsort_times_two (match p with | Lbranch -> l | Rbranch -> r) in
      app (x0 Lbranch) ((mul (Uint63.of_int (2)) h) :: (x0 Rbranch))
```

---
## Wrap-up

* (Recursive) Hylomorphisms in Coq.
* Hylomorphism Laws enable program optimisations as Coq tactics.
* Reasonable code extraction despite the extensive use of type families/indices in containers.

<br><br>

**Future work:**
* Side effects?
* N-ary containers?
* Improve Coq's code extraction? (inlining!)
* Deal with the "Setoid hell"?
* Ideas?

    </textarea>
</section>
