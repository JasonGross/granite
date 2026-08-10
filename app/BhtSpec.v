From stdpp Require Import base.
From stdpp.bitvector Require Import definitions.
From granite.core Require Import
  Program.
From granite.app Require Import BhtAPI.
Section WithContext.
  Context {params: Bht_sig}.

  Definition trace_t := list (ActionMethod unit).
  
  Class BhtSpec_sig :=
  { ppcDP: trace_t -> bv addr_sz -> bv addr_sz -> bv addr_sz}.
  
  Context {bhtSpecParams: BhtSpec_sig}.

  Definition St : Type := trace_t.
  Definition initial_st : St := [].

  Definition evalActionMethod {R} (m: ActionMethod R) (st: St) : R * St :=
    match R, m with
    | _, Update pc taken => ((), st ++ [Update pc taken])
    end.

  Definition evalValueMethod {A} (m: ValueMethod A) (st: St) : A :=
    match m with
    | PpcDP pc targetPc => ppcDP st pc targetPc
    end.

  Definition spec : Spec ValueMethod ActionMethod :=
   {| State := St;
      EvalVMethod A := evalValueMethod;
      EvalMethod A := evalActionMethod;
      initialState := initial_st
   |}.

End WithContext.
