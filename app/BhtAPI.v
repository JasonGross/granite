From stdpp Require Import base.
From granite.core Require Import Bits.
From granite.core Require Import
  Program.

Class Bht_sig := {
    idx_sz : Z;
    addr_sz : Z
}.

Section WithContext.
  Context {params: Bht_sig}.
  Inductive ActionMethod: Type -> Type := 
  | Update (pc: bits addr_sz) (taken: bool) : ActionMethod unit.

  Inductive ValueMethod : Type -> Type := 
  | PpcDP (pc: bits addr_sz) (targetPC: bits addr_sz) : ValueMethod (bits addr_sz).

End WithContext.
