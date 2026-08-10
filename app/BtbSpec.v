From stdpp Require Import base.
From stdpp.bitvector Require Import definitions.
From granite.core Require Import
  Program.
From granite.app Require Import
  BtbAPI.                

Section WithContext.
  Context {params: Btb_sig}.

  Definition trace_t := list (ActionMethod unit).
  
  Class BtbSpec_sig :=
  { predPc: trace_t -> bv addr_sz -> bv addr_sz}.
  
  Context {btbSpecParams: BtbSpec_sig}.

  Definition St : Type := trace_t.
  Definition initial_st : St := [].

  Definition evalActionMethod {A} (m: ActionMethod A) (st: St) : A * St :=
    match A, m with
    | _, Update pc nextPC => ((), st ++ [Update pc nextPC])
    end.

  Definition evalValueMethod {A} (m: ValueMethod A) (st: St) : A :=
    match m with
    | PredPc pc => predPc st pc 
    end.

  Definition spec : Spec ValueMethod ActionMethod :=
   {| State := St;
      EvalVMethod A := evalValueMethod;
      EvalMethod A := evalActionMethod;
      initialState := initial_st
   |}.

End WithContext.
