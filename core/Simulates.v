From stdpp Require Import base.
From granite.core Require Import
  Program.

Section WithContext.
  Context {VMethod Method: Type -> Type}
          (spec1: Spec VMethod Method)  (* concrete *)
          (spec2: Spec VMethod Method). (* abstraction *)

  Definition refines (Rel: spec1.(State) -> spec2.(State) -> Prop) :=
    forall s1 s2,
    Rel s1 s2 ->
    (forall R (vmethod: VMethod R),
      spec1.(EvalVMethod) vmethod s1 = spec2.(EvalVMethod) vmethod s2) /\
    (forall R method (r: R) s1',
      spec1.(EvalMethod) method s1 = (r, s1') ->
      exists s2', spec2.(EvalMethod) method s2 = (r, s2') /\
             Rel s1' s2').
  
  Definition simulates :=
    exists (Rel: spec1.(State) -> spec2.(State) -> Prop),
      Rel spec1.(initialState) spec2.(initialState) /\ refines Rel.
End WithContext.
