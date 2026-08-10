From stdpp Require Import base finite.
From stdpp.bitvector Require Import definitions.

From granite.core Require Import
  Bits
  Object
  Pair
  Program
  Reg.

Module Params.
  Class Params := {
    width: N;
    pfWidthNeZero : (width <> 0)%N
  }.
End Params.

Section WithContext.
  Context {params: Params.Params}.

  Record req_t := { 
    input_a : bv Params.width;
    input_b : bv Params.width 
  }.

  Inductive ActionMethod: Type -> Type :=
  | Enq (arg: req_t) : ActionMethod unit
  | Deq              : ActionMethod unit
  | Tick             : ActionMethod unit. 

  Inductive ValueMethod : Type -> Type :=
  | RespReady : ValueMethod (bv 1)
  | Full : ValueMethod (bv 1)
  | Peek : ValueMethod (bv (Params.width + Params.width)).


End WithContext.

