(* Live demo: sort-then-double, calculated in Rocq and extracted.
   The definitions are those of the library's examples/QSort.v.
   Step through it in VS Code (VsRocq); see README.md. *)
Set Warnings "-bad-template-constraint,-deprecated-transitive-library-file".
Generalizable All Variables.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Auto Template Polymorphism.

Require Import Hylo.Hylo.
Require Import Hylo.Examples.BTree.
Require Import Hylo.Extraction.Specialise.
From Stdlib Require Import List Uint63.

(* ------------------------------------------------------------------ *)
(* 1. Quicksort's divide (the coalgebra) and conquer (the algebra)     *)

Definition merge : App (TreeF unit int) (list int) ~> list int :=
  morph_of (fun x : App (TreeF unit int) (list int) =>
    let (sx, kx) := x in
    match sx return (Container.Pos (TreeF unit int) sx -> _) -> _ with
    | Leaf _ _ => fun _ => nil
    | Node _ h => fun k => List.app (k (posL h)) (h :: k (posR h))
    end kx).

Open Scope uint63_scope.
Definition c_split (x : list int) : App (TreeF unit int) (list int) :=
  match x with
  | nil => a_leaf tt
  | cons h t =>
      let (l, r) := List.partition (fun x => x <? h) t in
      a_node h l r
  end.
Arguments c_split x /.
Close Scope uint63_scope.

(* Termination, once for this coalgebra: the pieces are shorter *)
Lemma split_fin : respects_relation c_split (@length int) lt.
Proof.
  intros [|h t] p; simpl in *; try (apply (dom_leaf _ p)).
  rewrite PeanoNat.Nat.lt_succ_r; revert p; rewrite List.partition_as_filter.
  intros []; simpl in *; destruct val; apply List.filter_length_le.
Qed.

Definition tsplit : RCoalg (TreeF unit int) (list int)
  := mk_wf_coalg wf_lt split_fin.

(* ------------------------------------------------------------------ *)
(* 2. Doubling, and the fusion law it needs                            *)

Definition Lmap {A B} (f : A ~> B) (x : list A) : list B := List.map f x.

Ltac eq_args :=
  try to_eq; repeat (f_equal; auto with ffix; try apply bool_irrelevance).

Lemma Lmap_merge (f : int ~> int)
  : Lmap f \o merge =e merge \o natural (nt_shape id f) \o fmap (Lmap f).
Proof.
  intros [[n|n] kx]; simpl in *; auto with *.
  unfold Lmap, posL, posR; rewrite map_app; simpl; eq_args.
Qed.

Definition tsplit_k : CCoalg tsplit.
Proof. cps_from_coalg. Defined.

#[local] Hint Unfold merge tsplit c_split tsplit_k : unfold_code.

Open Scope uint63_scope.
Definition times_two (x : int) : int := 2 * x.
Arguments times_two x /.
Close Scope uint63_scope.

Lemma map_merge_fusion
  : Lmap times_two \o cata merge
    =e hylo (merge \o natural (nt_shape id times_two)) l_out.
Proof.
  apply hylo_uniq.
  rewrite fmap_comp; arewrite <- (Lmap_merge times_two).
  arewrite <- (cata_unfold merge); reflexivity.
Qed.

#[local] Hint Unfold times_two : unfold_code.

(* ------------------------------------------------------------------ *)
(* 3. The calculation: step through it, one rewrite at a time          *)

Derive qsort_times_two
  in (Lmap times_two \o cata merge \o rana tsplit =e morph_of qsort_times_two)
  as qsort_times_two_calc.
Proof.
  (* A wrong step is rejected: deforest needs an unfold next to a fold.
     Live: delete [Fail] to show the error. *)
  Fail rewrite deforest.
  (* Doubling moves into the algebra (fusion) *)
  rewrite map_merge_fusion.
  (* The tree between the unfold and the fold disappears *)
  rewrite hylo_ana, deforest by apply l_out_in.
  (* A continuation-passing coalgebra: no closures in the code *)
  rewrite <- (hylo_cps_hylo _ tsplit_k).
  finished.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. What comes out, and what it depends on                           *)

Extraction qsort_times_two.
Print Assumptions qsort_times_two_calc.

(* ------------------------------------------------------------------ *)
(* 5. A law with a false side condition: Rocq leaves it as a goal      *)

Open Scope uint63_scope.
Definition negate (x : int) : int := 0 - x.
Arguments negate x /.
Close Scope uint63_scope.

Derive qsort_negate
  in (cata merge \o rana tsplit \o Lmap negate =e morph_of qsort_negate)
  as qsort_negate_calc.
Proof.
  rewrite hylo_cata, hylo_ana, deforest by apply l_out_in.
  (* Fuse the negation into the divide step, choosing the new divide step
     (h2) wrongly: tsplit itself, as if negating changed nothing. Goal 1
     would make the program plain quicksort: the negation silently lost.
     Goal 2, the side condition for this choice, is false (negating changes
     the pivot and flips the order the partition uses), so this calculation
     can never be finished. The right h2 negates the pivot and compares
     negated values. *)
  rewrite (@hylo_fusion_r _ _ _ _ _ _ _ _ _ _ tsplit merge tsplit (Lmap negate)).
  Show 2.
Abort.
