Record Container := { Sh : Type; Pos : Sh -> Type }.
Record Ext C X := MkExt { shape : Sh C; cont : Pos C shape -> X }.

(* quicksort: a leaf, or a pivot with two positions *)
Definition TreeC : Container :=
  {| Sh := option nat;
     Pos := fun s => match s with None => False | Some _ => bool end |}.
