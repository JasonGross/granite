From stdpp Require Import base finite nmap stringmap vector.
From Stdlib Require Import Strings.String.
From granite.core Require Import
  Bits
  Program
  Tactics
  Utils.
From RecordUpdate Require Import RecordSet.
Set Primitive Projections.
Import RecordSetNotations.

From granite.isaSpec Require Import
  Common.
Set Nested Proofs Allowed.

Create HintDb machine.
Record machine (input output: Type) :=
  { state : Type;
    init : state;
    step : state -> input -> state * output;
  }.

Arguments state [input output].
Arguments init [input output].
Arguments step [input output].

Inductive event (I O: Type) :=
| IO : I -> O -> event I O.

Arguments IO [I O].

Definition Input {I} {O} (ev: event I O) :=
  match ev with
  | IO i _ => i
  end.

Definition Output {I} {O} (ev: event I O) :=
  match ev with
  | IO _ o => o
  end.

Definition trace (I O: Type) := list (event I O).

Inductive execution {I O: Type} (M: machine I O) : M.(state) -> trace I O -> M.(state) -> Prop :=
| ExecutionEmpty : forall s, execution _ s nil s
| ExecutionStep : forall s i s' o tr s''
    (Hstep: M.(step) s i = (s',o))
    (Hrest:  execution _ s' tr s''),
    execution _ s (IO i o::tr) s''.

#[export] Hint Constructors execution : machine.

Inductive execution_r {I O : Type} (M : machine I O) : M.(state) -> trace I O -> M.(state) -> Prop :=
| ExecutionREmpty : forall s, execution_r _ s nil s
| ExecutionRStep : forall s tr s' i o s''
    (Hrest: execution_r _ s tr s')
    (Hstep: M.(step) s' i = (s'',o )),
    execution_r _ s (tr ++ (IO i o :: nil)) s''.

#[export] Hint Constructors execution_r : machine.

Definition in_traces {I O: Type} (M: machine I O) (tr: trace I O): Prop :=
  exists fs, execution M M.(init) tr fs.

#[export] Hint Unfold in_traces : machine.

Definition refines {I O: Type} (M1 M2: machine I O) : Prop :=
  forall tr, 
    in_traces M1 tr ->
    in_traces M2 tr.

#[export] Hint Unfold refines : machine.

#[export] Hint Unfold in_traces : machine.



Lemma refines_refl : 
  forall I O (M: machine I O),
    refines M M.
Proof.
  auto with machine.
Qed.

Lemma refines_trans :
  forall I O (M1 M2 M3 : machine I O),
    refines M1 M2 ->
    refines M2 M3 ->
    refines M1 M3.
Proof.
  auto with machine.
Qed.

(* any sequence of outputs that can be produced by one can be produced by the other *)
Definition equivalent {I O : Type} (M1 M2 : machine I O) : Prop :=
  refines M1 M2 /\ refines M2 M1.

#[export] Hint Unfold equivalent : machine.


Lemma equivalent_refl :
  forall I O (M : machine I O),
    equivalent M M.
Proof.
  auto with machine.
Qed.

Lemma equivalent_sym :
  forall I O (M1 M2 : machine I O),
    equivalent M1 M2 ->
    equivalent M2 M1.
Proof.
  unfold equivalent.
  intuition.
Qed.

Lemma equivalent_trans :
  forall I O (M1 M2 M3 : machine I O),
    equivalent M1 M2 ->
    equivalent M2 M3 ->
    equivalent M1 M3.
Proof.
  unfold equivalent.
  intuition (eauto using refines_trans).
Qed.


Definition forward_simulation_relation
  {I O : Type} {M1 M2 : machine I O}
  (R : M1.(state) -> M2.(state) -> Prop) :=
  (* initialization *)
  R M1.(init) M2.(init) /\
    (* step *)
    (forall s1 i o_i o_s s1' s2 s2',
        R s1 s2 ->
        M1.(step) s1 i = (s1',o_i) ->
        M2.(step) s2 i = (s2',o_s) -> 
        o_i = o_s /\ R s1' s2').
Theorem forward_simulation :
  forall (I O : Type) (M1 M2 : machine I O)
    (R : M1.(state) -> M2.(state) -> Prop),
    forward_simulation_relation R ->
    refines M1 M2.
Proof.
  intros I O M1 M2 R (Hinit & Hstep).
  unfold refines, in_traces.
  generalize dependent (M1.(init)).
  generalize dependent (M2.(init)).
  intros s2 s1 HR.
  intros tr Hexec.
  generalize dependent s2.
  destruct Hexec as [s1f Hexec].
  induction Hexec; try solve [ eauto with machine ].
  - intros s2 HR.
    destruct (step M2 s2 i) as [s2' o_s] eqn:Hspec_step.
    specialize (Hstep _ _ _ _ _ _ _ HR Hstep0 Hspec_step).
    destruct Hstep as [obs_eq HR']. 
    subst.
    destruct (IHHexec s2' HR') as [s2f Hexec'].
    eauto with machine.
Qed.

Lemma execution_join :
  forall I O (M : machine I O) s0 s1 s2 io1 io2,
    execution M s0 io1 s1 ->
    execution M s1 io2 s2 ->
    execution M s0 (io1 ++ io2) s2.
Proof.
  induction 1; subst; simpl; intros; eauto with machine.
Qed.

#[export] Hint Resolve execution_join : machine.

Lemma execution_cons :
  forall I O (M : machine I O) s0 s1 s2 tr1 tr2,
    execution M s0 (tr1 :: nil) s1 ->
    execution M s1 tr2 s2 ->
    execution M s0 (tr1 :: tr2) s2.
Proof.
  intros I O M s0 s1 s2 io1 io2 H H0.
  replace (io1 :: io2) with ((io1 :: nil) ++ io2) by auto.
  eapply execution_join; eauto.
Qed.

#[export] Hint Resolve execution_cons : machine.

Lemma execution_consume :
  forall I O (M : machine I O) s0 s2 evt tr,
    execution M s0 (evt :: tr) s2 ->
    exists s1,
      execution M s0 (evt :: nil) s1 /\
        execution M s1 tr s2.
Proof.
  intros I O M s0 s2 evt tr H.
  inversion H; subst;
    eauto with machine.
Qed.

#[export] Hint Resolve execution_consume : machine.

Lemma execution_split :
  forall I O (M : machine I O) s0 s2 tr1 tr2,
    execution M s0 (tr1 ++ tr2) s2 ->
    exists s1,
      execution M s0 tr1 s1 /\
        execution M s1 tr2 s2.
Proof.
  intros I O M s0 s2 io1.
  generalize dependent s2.
  generalize dependent s0.
  induction io1; eauto with machine.
  intros s0 s2 io2 H.
  pose proof (execution_consume _ _ _ _ _ _ _ H) as Hcons.
  inversion Hcons as [? [? Hintr]].
  specialize (IHio1 _ _ _ Hintr).
  inversion IHio1; eexists; intuition; eauto with machine.
Qed.



Lemma execution_r_join :
  forall I O (M : machine I O) s0 s1 s2 tr1 tr2,
    execution_r M s0 tr1 s1 ->
    execution_r M s1 tr2 s2 ->
    execution_r M s0 (tr1 ++ tr2) s2.
Proof.
  intros I O M s0 s1 s2 io1 io2.
  generalize dependent s2.
  generalize dependent s1.
  generalize dependent s0.
  generalize dependent io1.
  induction io2 as [| io] using rev_ind.
  - intros io1 s0 s1 s2 H0 H1.
    inversion H1; subst.
    + rewrite app_nil_r; assumption.
    + destruct tr; simpl in *; congruence.
  - intros io1 s0 s1 s2 H0 H1.
    destruct io as [i o ].
    + inversion H1.
      * destruct io2; simpl in *; congruence.
      * apply app_inj_tail in H3.
        destruct H3 as [Hio2 Hio].
        inversion Hio; clear Hio.
        subst.
        rewrite app_assoc.
        eauto with machine.
Qed.

#[export] Hint Resolve execution_r_join : machine.

Lemma execution_execution_r :
  forall I O (M : machine I O) s tr s',
    execution M s tr s' ->
    execution_r M s tr s'.
Proof.
  intros I O M s tr s' H.
  induction H; auto with machine.
  - replace (IO i o :: tr) with ((IO i o :: nil) ++ tr) by auto.
    eapply execution_r_join; eauto.
    replace (IO i o :: nil) with (nil ++ (IO i o :: nil)) by auto.
    eauto with machine.
Qed.

#[export] Hint Resolve execution_execution_r : machine.

Lemma execution_r_execution :
  forall I O (M : machine I O) s io s',
    execution_r M s io s' ->
    execution M s io s'.
Proof.
  intros I O M s io s' H.
  induction H; eauto with machine.
Qed.

Lemma deterministic_execution:
  forall I O (M: machine I O) (tr: trace I O) st st' st'',
  execution M st tr st' ->
  execution M st tr st'' ->
  st' = st''.
Proof.
  induction tr; intros.
  - inversion H; inversion H0; subst. reflexivity.
  - inversion H; inversion H0; subst.
    match goal with
    | H: IO _ _ = IO _ _  |- _ => inversion H; subst
    end.
    rewrite Hstep in *. simplify_tupless.
    eauto.
Qed.

Lemma deterministic_input_execution:
  forall I O (M: machine I O) (tr1 tr2: trace I O) st st' st'',
  execution M st tr1 st' ->
  execution M st tr2 st'' ->
  map Input tr1 = map Input tr2 ->
  st' = st'' /\ tr1 = tr2.
Proof.
  induction tr1; intros.
  - destruct tr2; cbn in *; [ | congruence].
    inversion H; inversion H0; subst. split; reflexivity.
  - destruct tr2; cbn in *; [congruence | ].
    inversion H1; clear H1.
    inversion H; inversion H0; subst. cbn in *. subst.
    rewrite Hstep in *. simplify_tupless.
    edestruct IHtr1; eauto; subst; auto.
Qed.

Lemma deterministic_output_execution:
  forall I O (M: machine I O) (tr1 tr2: trace I O) st st' st'',
  execution M st tr1 st' ->
  execution M st tr2 st'' ->
  map Input tr1 = map Input tr2 ->
  map Output tr1 = map Output tr2.
Proof.
  intros. specialize deterministic_input_execution with (1 := H) (2 := H0) (3 := H1).
  propositional.
Qed.

Lemma equivalent_execution:
  forall I O (M1 M2: machine I O) tr st1,  
  equivalent M1 M2 ->
  execution M1 (init M1) tr st1 ->
  exists st2, execution M2 (init M2) tr st2 /\
         (forall i st1' st2' o_i o_s, 
            step M1 st1 i = (st1', o_i) ->
            step M2 st2 i = (st2', o_s) ->
            o_i = o_s).
Proof.
  unfold equivalent, refines, in_traces.
  intros. propositional. eauto.
  pose proof (H1 tr). 
  destruct H; eauto.
  exists x; split; auto.
  intros.
  assert (execution_r M1 (init M1) (tr ++ [IO i o_i]) st1') as hstep.
  { econstructor; eauto. by apply execution_execution_r. }
  specialize H1 with (tr := tr ++ [IO i o_i]).
  destruct H1.
  { apply execution_r_execution in hstep. eauto. } 
  { apply execution_execution_r in H1.
    inversion H1; propositional.
    - destruct tr; discriminate.
    - apply app_inj_tail in H7. propositional.
      inversion H6; propositional.
      apply execution_r_execution in Hrest.
      replace x with s' in *.
      { rewrite Hstep in *. by simplify_tupless. }
      { eapply deterministic_execution; eauto. }
  }
Qed.

Lemma equivalent_in_traces_left:
  forall I O (M1 M2: machine I O) tr,
    equivalent M1 M2 ->
    in_traces M1 tr ->
    in_traces M2 tr.
Proof.
  consider @equivalent.
  intros. apply H. auto.
Qed.

Lemma equivalent_in_traces_right:
  forall I O (M1 M2: machine I O) tr,
    equivalent M1 M2 ->
    in_traces M2 tr ->
    in_traces M1 tr.
Proof.
  consider @equivalent.
  intros. apply H. auto.
Qed.

Lemma in_traces_app_one:
  forall {I O: Type} (M: machine I O) (tr: trace I O) ev,
  in_traces M (tr ++ [ev]) -> in_traces M tr.
Proof.
  consider @in_traces.
  propositional.
  apply execution_execution_r in H0.
  inversion H0; subst.
  + exists (init M); apply execution_r_execution.
    destruct tr; cbn in *; subst; eauto; congruence.
  + apply app_inj_tail in H2. propositional. 
    eexists; apply execution_r_execution; eauto.
Qed.

Lemma deterministic_refines_sym:
  forall {I O: Type} (M1 M2: machine I O),
  refines M1 M2 ->
  refines M2 M1.
Proof.
  intros. consider @refines. consider @in_traces.
  induction tr using rev_ind.
  - propositional. specialize (H []).
    exists (init M1). constructor.
  - intros hexec. propositional.
    apply execution_execution_r in hexec0.
    inversions hexec0; [destruct tr; cbn in *; congruence | ].
    apply execution_r_execution in Hrest.
    apply app_inj_tail_iff in H2; propositional.
    assert_pre_and_specialize IHtr.
    { eauto. }
    propositional.
    destruct (step M1 fs0 i) eqn:?.

    pose proof (H (tr ++ [IO i o0])) as Heq1.
    assert_pre_and_specialize Heq1.
    { exists s.
      apply execution_r_execution.
      apply execution_execution_r in IHtr0.
      eapply ExecutionRStep; eauto.
    }
    propositional.
    apply execution_execution_r in Heq0.
    inversions Heq0; [destruct tr; cbn in *; congruence | ].
    apply app_inj_tail_iff in H2. propositional. inversions H1.
    apply execution_r_execution in Hrest0.
    replace s'0 with s' in * by (eapply deterministic_execution; eauto).
    rewrite Hstep in *. simplify_tupless.
    exists s. apply execution_r_execution.
    apply execution_execution_r in IHtr0.
    eapply ExecutionRStep; eauto.
Qed.
  
Lemma refines_equivalent:
  forall {I O: Type} (M1 M2: machine I O),
  refines M1 M2 ->
  equivalent M1 M2.
Proof.
  intros * refines. unfold equivalent.
  split; auto.
  by apply deterministic_refines_sym.
Qed.


Definition Sim {I O: Type} (M1 M2: machine I O) 
  : M1.(state) -> M2.(state) -> Prop :=
  fun m1 m2 => 
    m1 = M1.(init) /\ m2 = M2.(init) \/
    exists io, execution_r M1 M1.(init) io m1 /\
          execution_r M2 M2.(init) io m2.

Theorem refines_forward_simulation :
  forall (I O : Type) (M1 M2 : machine I O),
    refines M1 M2 ->
    exists (R : M1.(state) -> M2.(state) -> Prop),
      forward_simulation_relation R.
Proof.
  intros I O M1 M2 H.
  exists (Sim M1 M2). unfold Sim.
  split; try solve [ auto ].
  intros s1 i o_i o_s s1' s2 s2' HR Hstep_i Hstep_s.
  destruct HR as [Hinit | Hhist].
  + destruct Hinit; subst.
    specialize (H (IO i o_i :: nil) ltac:(eauto with machine)).
    destruct H as [s2'' H].
    inversion H; subst.
    rewrite Hstep_s in *. simplify_tupless.
    split; eauto.
    right.
    exists ([] ++ [IO i o_i]).
    split; econstructor; eauto with machine.
  + destruct Hhist as [io [Hexec1 Hexec2]].
    specialize (H (io ++ IO i o_i :: nil)).
    assert (execution_r M1 (init M1) (io ++ IO i o_i :: nil) s1') as Hexec1' by eauto with machine.
    apply execution_r_execution in Hexec1'.
    specialize (H (ex_intro _ s1' Hexec1')).
    unfold in_traces in H.
    destruct H as [s2'' Hs2'].
    apply execution_execution_r in Hs2'.
    inversion Hs2'.
    1: { destruct io; simpl in *; congruence. }
    subst.
    apply app_inj_tail in H1. propositional.
    inversion H2; clear H2; subst.
    (* given the same inputs, final state must match *)
    assert (s2 = s').
    * clear - Hexec2 Hrest.
      generalize dependent Hexec2.
      generalize dependent Hrest.
      generalize dependent s2.
      generalize dependent s'.
      induction io using rev_ind.
      -- intros s s' H H'.
         inversion H; inversion H'; subst; auto; destruct tr; simpl in *; congruence.
      -- intros s s' H H'.
         destruct x.
         ++ inversion H.
            1:{ destruct io; simpl in *; congruence. }
            inversion H'.
            1:{ destruct io; simpl in *; congruence. }
            apply app_inj_tail in H5.
            apply app_inj_tail in H2.
            intuition.
            inversion H7; inversion H8; subst.
            specialize (IHio _ _ Hrest Hrest0); subst.
            rewrite Hstep in Hstep0. simplify_tupless. reflexivity.
    * subst. rewrite Hstep_s in *. simplify_tupless.
      split; auto.
      right. eexists; eauto with machine.
Qed.

Module ExternalWorld.
  Section WithContext.
    Context {I O: Type}.
    Context {M: machine I O}.
    Context {extWorld: list O -> I}. (* function from reversed outputs to inputs *)

    Record State :=
    { mState : M.(state);
      outputs : list O (* reversed *)
    }.

    Definition InitialState :=
      {| mState := M.(init);
         outputs := [] |}.

    Definition world : machine unit unit :=
      {| state := State;
         init := InitialState;
         step := fun st _ =>
                   let (mst', o) := M.(step) st.(mState) (extWorld st.(outputs)) in
                   ({| mState := mst';
                       outputs := o::st.(outputs)
                    |}, ())
      |}.

    Fixpoint exec' (fuel: nat) (st: State): State :=
      match fuel with
      | 0 => st
      | S n => let (st', _) := world.(step) st () in 
              exec' n st' 
      end.

    Definition exec (fuel: nat) : State :=
      exec' fuel world.(init).
      
  End WithContext.

  Arguments exec {_ _} _ _.
  Arguments State {_ _} _.
End ExternalWorld.


