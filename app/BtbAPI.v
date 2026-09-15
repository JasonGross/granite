From stdpp Require Import base.
From granite.core Require Import Bits.
From granite.core Require Import
  Program.

Class Btb_sig:= {
    idx_sz : Z;
    tag_sz : Z;
    addr_sz : Z
}.

Section WithContext.
  Context {params: Btb_sig}.

  Inductive ActionMethod: Type -> Type := 
  | Update (pc: bits addr_sz) (nextPc: bits addr_sz) : ActionMethod unit.

  Inductive ValueMethod : Type -> Type := 
  | PredPc (pc: bits addr_sz) : ValueMethod (bits addr_sz).

End WithContext.
