From stdpp Require Import base.
From stdpp.bitvector Require Import definitions.
From granite.core Require Import
  Program.

Class Bht_sig := {
    idx_sz : N;
    addr_sz : N
}.

Section WithContext.
  Context {params: Bht_sig}.
  Inductive ActionMethod: Type -> Type := 
  | Update (pc: bv addr_sz) (taken: bool) : ActionMethod unit.

  Inductive ValueMethod : Type -> Type := 
  | PpcDP (pc: bv addr_sz) (targetPC: bv addr_sz) : ValueMethod (bv addr_sz).

End WithContext.
