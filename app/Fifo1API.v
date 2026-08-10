From stdpp Require Import base.
From granite.core Require Import
  Bits
  Program.

Section WithContext.
  Context {Val: Type}.
  Inductive ActionMethod: Type -> Type :=
  | Enq (arg: Val) : ActionMethod unit
  | Deq : ActionMethod unit.
  
  Inductive ValueMethod : Type -> Type :=
  | First : ValueMethod Val
  | Empty : ValueMethod (bv 1)
  | Full : ValueMethod (bv 1).
  
End WithContext.

Arguments ActionMethod: clear implicits.
Arguments ValueMethod: clear implicits.


Notation fifo1_first := Fifo1API.First.
Notation fifo1_empty := Fifo1API.Empty.
Notation fifo1_full := Fifo1API.Full.
Notation fifo1_deq := Fifo1API.Deq.
Notation fifo1_enq := Fifo1API.Enq.
