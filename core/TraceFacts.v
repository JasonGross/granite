From stdpp Require Import base tactics.
From granite.core Require Import
  Program
  Trace.

Section WithContext.
  Context {VM M} (spec: Spec VM M).
  Notation execTrace := (execTrace spec).
  Lemma execTrace_app (tr1 tr2: Trace M) :
    forall st,
    execTrace (tr1 ++ tr2) st = execTrace tr2 (execTrace tr1 st).
  Proof.
    induction tr1; cbn; auto.
    intros. destruct a. by rewrite IHtr1. 
  Qed.

  Lemma execTrace_mapApp {X} (tr1 tr2: list X) :
    forall fn st,
    execTrace (map fn (tr1 ++ tr2)) st = execTrace (map fn tr2) (execTrace (map fn tr1) st).
  Proof.
    intros. rewrite map_app. by rewrite execTrace_app.
  Qed.

End WithContext.


