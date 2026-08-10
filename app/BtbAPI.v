From stdpp Require Import base.
From stdpp.bitvector Require Import definitions.
From granite.core Require Import
  Program.

Class Btb_sig:= {
    idx_sz : N;
    tag_sz : N;
    addr_sz : N
}.

Section WithContext.
  Context {params: Btb_sig}.

  Inductive ActionMethod: Type -> Type := 
  | Update (pc: bv addr_sz) (nextPc: bv addr_sz) : ActionMethod unit.

  Inductive ValueMethod : Type -> Type := 
  | PredPc (pc: bv addr_sz) : ValueMethod (bv addr_sz).

End WithContext.
