(*! Fifo1 simulation *)
From stdpp Require Import base tactics.
From RecordUpdate Require Import RecordSet.
From granite.core Require Import
  Bits
  Object
  Pair
  Program
  ProgramOps
  Reg
  Simulates
  Tactics
  Trace 
  TraceFacts
  Utils.
From granite.core Require PairFacts.
From granite.app Require 
  Fifo1API 
  Fifo1  
  Fifo1Spec.
Import domain.Zmod.
Section WithContext.
  Context [Val: Type].
  Context (initVal: Val).

  Notation trace_t := (Fifo1Spec.trace_t (Val := Val)).
  Notation concrete_spec := (Fifo1.fifo_spec (Val := Val) (initVal := initVal)).
  Notation impl_st_t := (Fifo1.FifoProdSt Val).
  Definition evalITrace (tr: trace_t) := 
    Trace.execTrace concrete_spec (map (CallEvent) tr) concrete_spec.(initialState).
  Definition default_first (tr: trace_t) : Val :=
    let st := evalITrace tr in
    (concrete_spec.(EvalVMethod) (Fifo1API.First) st).

  #[export] Instance specParams : Fifo1Spec.SpecParams (Val := Val) :=
    {| Fifo1Spec.default_first := default_first |}.

  Notation abstract_spec := (Fifo1Spec.spec (Val := Val)).

  Definition evalSTrace (tr: trace_t) := 
    Trace.execTrace abstract_spec (map (CallEvent) tr) abstract_spec.(initialState).

  Record RelBase (impl: State concrete_spec) (spec: State abstract_spec) :=
    { impl_hist_rel: evalITrace spec.(Fifo1Spec.hist) = impl
    ; spec_hist_rel: evalSTrace spec.(Fifo1Spec.hist) = spec
    }.                                                          
  Coercion Fifo1.FifoSt_of_prod : Fifo1.FifoProdSt >-> Fifo1.FifoSt.

  Record Rel (impl: impl_st_t) (spec: State abstract_spec) :=
    { Rel_base: RelBase impl spec;
      spec_st_rel : match spec.(Fifo1Spec.opt_val) with
                    | None => Fifo1.valid impl = false 
                    | Some v =>
                       Fifo1.valid impl = embed_bool true /\
                       Fifo1.data impl = v 
                    end
    }.
  Lemma Rel_init : Rel (initialState concrete_spec) (initialState abstract_spec).
  Proof.
    constructor; cbn; split; propositional; auto.
  Qed.

  Ltac fifosimp :=
    repeat match goal with
    | H: RelBase _ _
      |- context[evalITrace (Fifo1Spec.hist _)] =>
        rewrite impl_hist_rel with (1 := H)
    | H: _ * _ |- _ => destruct H
    end.

  Lemma evalITrace_app xs ys :
    evalITrace (xs ++ ys) =
    Trace.execTrace concrete_spec (map CallEvent ys) (evalITrace xs).
  Proof.
    unfold evalITrace. rewrite execTrace_mapApp. reflexivity.
  Qed.

  Lemma evalSTrace_app xs ys :
    evalSTrace (xs ++ ys) =
    Trace.execTrace abstract_spec (map CallEvent ys) (evalSTrace xs).
  Proof.
    unfold evalSTrace. rewrite execTrace_mapApp. reflexivity.
  Qed.

  Lemma default_first_eq (tr : trace_t) :
    default_first tr = fst (evalITrace tr).
  Proof.
    unfold default_first. cbn. reflexivity.
  Qed.

  Lemma valid_is_some_eq (impl : impl_st_t) (spec : State abstract_spec) :
    Rel impl spec ->
    Fifo1.valid impl = is_some spec.(Fifo1Spec.opt_val).
  Proof.
    intros Hrel. inv Hrel. destruct impl as [d b].
    destruct (Fifo1Spec.opt_val spec) as [v|] eqn:Hopt; cbn in spec_st_rel0 |- *.
    - destruct spec_st_rel0 as [Hvalid _]. rewrite nonzero_bool in Hvalid. exact Hvalid.
    - exact spec_st_rel0.
  Qed.

  Lemma FirstOk (impl : impl_st_t) (spec : State abstract_spec) :
    Rel impl spec ->
    EvalVMethod concrete_spec Fifo1API.First impl = EvalVMethod abstract_spec Fifo1API.First spec.
  Proof.
    intros Hrel. inv Hrel.
    destruct Rel_base0 as [impl_hist_rel0 spec_hist_rel0].
    destruct impl as [d b].
    destruct (Fifo1Spec.opt_val spec) as [v|] eqn:Hopt; cbn in spec_st_rel0 |- *.
    - destruct spec_st_rel0 as [_ Hdata]. rewrite Hopt. cbn. exact Hdata.
    - rewrite Hopt. cbn. rewrite impl_hist_rel0. reflexivity.
  Qed.

  Lemma EmptyOk (impl : impl_st_t) (spec : State abstract_spec) :
    Rel impl spec ->
    EvalVMethod concrete_spec Fifo1API.Empty impl = EvalVMethod abstract_spec Fifo1API.Empty spec.
  Proof.
    intros Hrel. destruct impl as [d b]. cbn. f_equal. f_equal.
    exact (valid_is_some_eq (d, b) spec Hrel).
  Qed.

  Lemma FullOk (impl : impl_st_t) (spec : State abstract_spec) :
    Rel impl spec ->
    EvalVMethod concrete_spec Fifo1API.Full impl = EvalVMethod abstract_spec Fifo1API.Full spec.
  Proof.
    intros Hrel. destruct impl as [d b]. cbn. f_equal.
    exact (valid_is_some_eq (d, b) spec Hrel).
  Qed.

  Ltac trace_step :=
    rewrite ?map_app, ?evalITrace_app, ?evalSTrace_app;
    repeat match goal with
    | H: evalITrace ?tr = _ |- context[Trace.execTrace concrete_spec (map CallEvent ?tr) _] =>
        rewrite H
    | H: evalSTrace ?tr = _ |- context[Trace.execTrace abstract_spec (map CallEvent ?tr) _] =>
        rewrite H
    end; cbn.

  Lemma EnqOk (impl impl' : impl_st_t) r (spec : State abstract_spec) (arg : Val) :
    Rel impl spec ->
    EvalMethod concrete_spec (Fifo1API.Enq arg) impl = (r, impl') ->
    exists spec', EvalMethod abstract_spec (Fifo1API.Enq arg) spec = (r, spec') /\ Rel impl' spec'.
  Proof.
    intros Hrel Himpl. inv Hrel.
    destruct Rel_base0 as [impl_hist_rel0 spec_hist_rel0].
    destruct impl as [d b].
    destruct spec as [spec_opt spec_hist].
    destruct spec_opt as [v|]; cbn in spec_st_rel0.
    - (* Some v: full, concrete does nothing *)
      destruct spec_st_rel0 as [Hvalid Hdata]. cbn in Hvalid, Hdata.
      rewrite nonzero_bool in Hvalid.
      (* Hvalid : b = true, Hdata : d = v. inv Himpl will subst b→true, d→v. *)
      assert (Hstep : EvalMethod concrete_spec (Fifo1API.Enq arg) (d, b) = ((), (d, b)))
        by (cbn; rewrite Hvalid; cbn; reflexivity).
      rewrite Hstep in Himpl. inv Himpl.
      exists (Fifo1Spec.Build_st_t (Some v) (spec_hist ++ [Fifo1API.Enq arg])).
      split.
      + reflexivity.
      + constructor.
        * constructor.
          { change (evalITrace (spec_hist ++ [Fifo1API.Enq arg]) = (v, true)).
            rewrite evalITrace_app.
            replace (evalITrace spec_hist) with (v, true) by exact (eq_sym impl_hist_rel0).
            cbn. reflexivity. }
          { change (evalSTrace (spec_hist ++ [Fifo1API.Enq arg]) =
              Fifo1Spec.Build_st_t (Some v) (spec_hist ++ [Fifo1API.Enq arg])).
            rewrite evalSTrace_app.
            replace (evalSTrace spec_hist) with (Fifo1Spec.Build_st_t (Some v) spec_hist) by exact (eq_sym spec_hist_rel0).
            cbn. reflexivity. }
        * cbn. split; [rewrite nonzero_bool; reflexivity | reflexivity].
    - (* None: not full, concrete enqueues *)
      cbn in spec_st_rel0.
      (* spec_st_rel0 : b = false. inv Himpl will subst b→false. *)
      assert (Hstep : EvalMethod concrete_spec (Fifo1API.Enq arg) (d, b) = ((), (arg, true)))
        by (cbn; rewrite spec_st_rel0; cbn; reflexivity).
      rewrite Hstep in Himpl. inv Himpl.
      eexists (Fifo1Spec.Build_st_t (Some arg) (spec_hist ++ [Fifo1API.Enq arg])).
      split.
      + cbn. reflexivity.
      + constructor.
        * constructor.
          { change (evalITrace (spec_hist ++ [Fifo1API.Enq arg]) = (arg, true)).
            rewrite evalITrace_app.
            replace (evalITrace spec_hist) with (d, false) by exact (eq_sym impl_hist_rel0).
            cbn. reflexivity. }
          { change (evalSTrace (spec_hist ++ [Fifo1API.Enq arg]) =
              Fifo1Spec.Build_st_t (Some arg) (spec_hist ++ [Fifo1API.Enq arg])).
            rewrite evalSTrace_app.
            replace (evalSTrace spec_hist) with (Fifo1Spec.Build_st_t None spec_hist) by exact (eq_sym spec_hist_rel0).
            cbn. reflexivity. }
        * cbn. split; [rewrite nonzero_bool; reflexivity | reflexivity].
  Qed.

  Lemma DeqOk (impl impl' : impl_st_t) r (spec : State abstract_spec) :
    Rel impl spec ->
    EvalMethod concrete_spec Fifo1API.Deq impl = (r, impl') ->
    exists spec', EvalMethod abstract_spec Fifo1API.Deq spec = (r, spec') /\ Rel impl' spec'.
  Proof.
    intros Hrel Himpl. inv Hrel.
    destruct Rel_base0 as [impl_hist_rel0 spec_hist_rel0].
    destruct impl as [d b].
    destruct spec as [spec_opt spec_hist].
    assert (Hstep : EvalMethod concrete_spec Fifo1API.Deq (d, b) = ((), (d, false)))
      by (cbn; reflexivity).
    rewrite Hstep in Himpl. inv Himpl.
    eexists (Fifo1Spec.Build_st_t None (spec_hist ++ [Fifo1API.Deq])).
    split.
    + cbn. reflexivity.
    + constructor.
      * constructor.
        { change (evalITrace (spec_hist ++ [Fifo1API.Deq]) = (d, false)).
          rewrite evalITrace_app.
          replace (evalITrace spec_hist) with (d, b) by exact (eq_sym impl_hist_rel0).
          cbn. reflexivity. }
        { change (evalSTrace (spec_hist ++ [Fifo1API.Deq]) =
            Fifo1Spec.Build_st_t None (spec_hist ++ [Fifo1API.Deq])).
          rewrite evalSTrace_app.
          replace (evalSTrace spec_hist) with (Fifo1Spec.Build_st_t spec_opt spec_hist) by exact (eq_sym spec_hist_rel0).
          cbn. reflexivity. }
      * cbn. reflexivity.
  Qed.

  Theorem refines :
    refines concrete_spec abstract_spec Rel.
  Proof.
    cbv [refines]. intros * Hrel *.
    split.
    - destruct vmethod.
      + by apply FirstOk.
      + by apply EmptyOk.
      + by apply FullOk.
    - destruct method; intros.
      + by eapply EnqOk; eauto.
      + by eapply DeqOk; eauto.
  Qed.

  Corollary simulates :
    simulates concrete_spec abstract_spec. 
  Proof.
    unfold simulates. exists Rel.
    split; [by apply Rel_init | by apply refines].
  Qed.
    
End WithContext.

Module TestProd.
  Module Impl.
    Definition st_t : Type := prod (@Fifo1.FifoSt nat) (@Fifo1.FifoSt bool).
    Definition base := PairSpec (Fifo1.fifo_spec (Val := nat) (initVal := 0)) (Fifo1.fifo_spec (Val := bool) (initVal := false)).
  End Impl.
  
  Module Spec.
    Definition st_t := prod (Fifo1Spec.st_t (Val := nat)) (Fifo1Spec.st_t (Val := bool)). 

    Definition base := 
      PairSpec (Fifo1Spec.spec (Val := nat) (specParams := specParams 0)) 
               (Fifo1Spec.spec (Val := bool) (specParams := specParams false)).
  End Spec.
  Import Simulates.

  Theorem simulates :
    simulates Impl.base Spec.base.
  Proof.
    apply PairFacts.pairObjSimulates.
    apply Fifo1Simulates.simulates.
    apply Fifo1Simulates.simulates.
  Qed.
End TestProd.
