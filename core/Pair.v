From stdpp Require Import base.
From granite.core Require Import
  Program.

Section Pair.
  Context {VMethodL MethodL VMethodR MethodR}
          {specL: Spec VMethodL MethodL}
          {specR: Spec VMethodR MethodR}.

  Definition PairVMethod (Ret: Type) := 
    sum (VMethodL Ret) (VMethodR Ret).

  Definition PairMethod (Ret: Type) := 
    sum (MethodL Ret) (MethodR Ret).

  Definition EvalPairVMethod A (met: VMethodL A + VMethodR A) st :=
    match met with
    | inl met => specL.(EvalVMethod) met st.1 
    | inr met => specR.(EvalVMethod) met st.2
    end.

  Definition EvalPairMethod A (met: MethodL A + MethodR A) st :=
    match met with
    | inl met => let '(a, st1') := specL.(EvalMethod) met st.1 in
                (a, (st1', st.2))
    | inr met => let '(a, st2') := specR.(EvalMethod) met st.2 in
                (a, (st.1, st2'))
    end.

  Definition PairSpec : Spec PairVMethod PairMethod :=
    {| State := specL.(State) * specR.(State);
       EvalVMethod := EvalPairVMethod;
       EvalMethod := EvalPairMethod;
       initialState := (specL.(initialState), specR.(initialState))
    |}.
End Pair.
Arguments PairVMethod : clear implicits.
Arguments PairMethod : clear implicits.
Arguments PairSpec {_ _ _ _} _ _.
