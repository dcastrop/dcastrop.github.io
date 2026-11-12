Class Cont `{setoid Sh} (P : Type) :=
  { valid : Sh * P ~> bool }.^\tikzmark{valid}^

Record Pos `{Cont Sh P} (s : Sh) :=
  MkElem { val : P; Valid : valid (s, val) }.^\tikzmark{Valid}^

Record App `{F : Cont Sh P} (X : Type) :=
  MkCont { shape : Sh; cont : Pos F shape -> X }.
