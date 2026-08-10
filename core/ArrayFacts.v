From stdpp Require Import base tactics vector.
From granite.core Require Import
  Tactics                  
  Program
  Pair
  Simulates
  SimulatesFacts
  Array.

Section ArrayObjSimulates.
  Context {VM M: Type -> Type}
          (obj1 obj2: Spec VM M).

  Lemma arrayObjRefines:
    forall R, 
    refines obj1 obj2 R -> 
    forall n, refines (ArraySpec obj1 n) (ArraySpec obj2 n) 
                 (fun s1 s2 => forall idx, R (s1 !!! idx) (s2 !!! idx)).
  Proof.
    cbv[refines].
    intros * H.
    intros * Hr.
    cbn in *. unfold EvalArrayVMethod, EvalArrayMethod.
    split; intros; destruct_match_pairs; simplify_tupless.
    - specialize H with (1 := Hr t). propositional.
    - specialize H with (1 := Hr t). propositional.
      edestruct H1; propositional; eauto; simplify_eqs; eauto.
      eexists; split; eauto. intros.
      destruct (decide (idx = t)); subst.
      + setoid_rewrite vlookup_insert. auto.
      + setoid_rewrite vlookup_insert_ne; auto.
  Qed.

  Lemma arrayObjSimulates:
    simulates obj1 obj2 ->
    forall n, simulates (ArraySpec obj1 n) (ArraySpec obj2 n). 
  Proof.
    intros * [Rel [Init Refines]].
    cbv[simulates].
    intros. eexists; split; [ | by eapply arrayObjRefines].
    cbn. setoid_rewrite lookup_fun_to_vec. auto.
  Qed.
End ArrayObjSimulates.

