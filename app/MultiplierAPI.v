From stdpp Require Import base finite.
From granite.core Require Import Bits.

From granite.core Require Import
  Bits
  Object
  Pair
  Program
  Reg.

Module Params.
  Class Params := {
    width: Z;
    pfWidthNeZero : (width <> 0)%Z
  }.
End Params.

Section WithContext.
  Context {params: Params.Params}.

  Record req_t := { 
    input_a : bits Params.width;
    input_b : bits Params.width 
  }.

  Inductive ActionMethod: Type -> Type :=
  | Enq (arg: req_t) : ActionMethod unit
  | Deq              : ActionMethod unit
  | Tick             : ActionMethod unit. 

  Inductive ValueMethod : Type -> Type :=
  | RespReady : ValueMethod (bits 1)
  | Full : ValueMethod (bits 1)
  | Peek : ValueMethod (bits (Params.width + Params.width)).


End WithContext.

