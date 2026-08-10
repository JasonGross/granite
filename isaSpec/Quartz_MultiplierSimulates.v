From stdpp Require Import bitvector.tactics.
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
  SimulatesFacts
  Tactics
  Trace
  TraceFacts
  Utils.

From granite.app Require Import
  MultiplierAPI
  Multiplier
  MultiplierSpec.
From quartz.lang Require Import Syntax domain.
From quartz.examples Require Import Processor.
From granite.isaSpec Require Import QuartzLib Pipelined.
From Stdlib Require Import ZArith.
Import InterfaceExample.
Import type.
Import BV.
From Ltac2 Require Import Ltac2 Array Constr Printf Proj Ind. Set Default Proof Mode "Classic". Module UConstr := Constr.Unsafe.

Section WithContext.
  Context {implParams: MultiplierParams}.

  (* (* Fix the Quartz-hardcoded width of 32 *) *)
  #[local] Existing Instance mulParams. 
  Notation lns := (logNSteps).
  Notation qst := (multiplier.State lns).

  Coercion req_rep (v : multiplier.req_t) : multiplier.Req :=
    ltac2:(let t := struct.rep &v in exact $t).

  Definition lower_req (r: MultiplierAPI.req_t) : multiplier.req_t :=
    {| multiplier.input_a := r.(input_a);
       multiplier.input_b := r.(input_b) |}.

  Notation mul_impl := (multiplier.impl lns).

  Definition evalVMet_q {R} (m: MultiplierAPI.ValueMethod R) (qs: qst) : R :=
    match m with
    | RespReady => fn.interp (Multiplier.respReady _ mul_impl) qs
    | Full => fn.interp (Multiplier.full _ mul_impl) qs
    | Peek => fn.interp (Multiplier.peek _ mul_impl) qs
    end.

  Definition evalAMet_q {R} (m: MultiplierAPI.ActionMethod R) (qs: qst) : R * qst :=
    match m with
    | Enq req => ((), fn.interp (Multiplier.enq _ mul_impl) (qs, req_rep (lower_req req))) 
    | Deq => ((), fn.interp (Multiplier.deq _ mul_impl) qs)
    | Tick => ((), fn.interp (Multiplier.tick _ mul_impl) qs) 
    end.

  Definition mul_qspec : Spec MultiplierAPI.ValueMethod MultiplierAPI.ActionMethod :=
    {| State := qst;
       EvalVMethod {A} := evalVMet_q;
       EvalMethod {A} := evalAMet_q;
       initialState := default _
    |}.

  Definition evalITrace (tr: MultiplierSpec.trace_t) : qst :=
    execTrace mul_qspec (map CallEvent tr) mul_qspec.(initialState).

  Definition lift_leakage_event (ev: MultiplierSpec.LeakEvent)
      : MultiplierAPI.ActionMethod unit :=
    match ev with
    | LeakEnq zero_arg =>
        Enq (if zero_arg then
               {| input_a := bv_0 _; input_b := bv_0 _ |}
             else
               {| input_a := of_Z _ 1; input_b := of_Z _ 1 |})
    | LeakDeq => Deq
    | LeakTick => Tick
    end.

  Definition evalLeakageTrace (tr: MultiplierSpec.leakage_trace_t) : qst :=
    evalITrace (map lift_leakage_event tr).

  Definition default_peek (tr: MultiplierSpec.trace_t) : bv (32 + 32) :=
    (fn.interp (Multiplier.peek _ mul_impl) (evalITrace tr)).

  Definition resp_ready (leakage: MultiplierSpec.leakage_trace_t) : bool :=
    (fn.interp (Multiplier.respReady _ mul_impl) (evalLeakageTrace leakage)).

  Definition is_full (leakage: MultiplierSpec.leakage_trace_t) : bool :=
    (fn.interp (Multiplier.full _ mul_impl) (evalLeakageTrace leakage)).

  #[export] Instance mulQSpecParams : MultiplierSpec.SpecParams :=
    {| MultiplierSpec.default_peek := default_peek;
       MultiplierSpec.resp_ready := resp_ready;
       MultiplierSpec.is_full := is_full
    |}.

  Notation abstract_spec := MultiplierSpec.spec.
  Notation spec_st_t := (State abstract_spec).

  Definition evalSTrace (tr: MultiplierSpec.trace_t) :=
    execTrace abstract_spec (map CallEvent tr) abstract_spec.(initialState).

  Record RelBase (qs: qst) (spec: spec_st_t) :=
    { impl_hist_rel: evalITrace spec.(hist) = qs
    ; spec_hist_rel: evalSTrace spec.(hist) = spec
    }.

  Coercion reflect (qs: qst) : multiplier.state lns :=
    let '(_valid, (_op1, (_op2, (_result, (_nstep, (_finished, _)))))) := qs in 
    {| multiplier.valid := _valid;
       multiplier.op1 := _op1;
       multiplier.op2 := _op2;
       multiplier.result := _result;
       multiplier.nstep := _nstep;
       multiplier.finished := _finished
    |}.
  
  Definition QSignalsEq (qs pubQs: qst) :=
    qs.(multiplier.valid _ ) = pubQs.(multiplier.valid _) /\
    qs.(multiplier.nstep _) = pubQs.(multiplier.nstep _) /\
    qs.(multiplier.finished _) = pubQs.(multiplier.finished _).

  Notation PubImpl spec :=
    (evalLeakageTrace (MultiplierSpec.leakage spec.(hist))).

  Definition shortCircuitEqQ (qs pubQs: qst) :=
    (qs.(multiplier.op1 _ ) = bv_0 _ \/ qs.(multiplier.op2 _) = bv_0 _ ) <->
    (pubQs.(multiplier.op1 _ ) = (bv_0 _) \/ pubQs.(multiplier.op2 _) = bv_0 _).

  Inductive RelCore (qs: qst) (spec: spec_st_t) : Prop :=
  | CaseEmpty
      (pfINotValid: qs.(multiplier.valid _) = false)
      (pfINotFinished: qs.(multiplier.finished _) = false)
      (pfSEmpty: spec.(reqs) = [])
      (pfSignalsEq: QSignalsEq qs (PubImpl spec))
  | CaseBusy
      (pfIValid: qs.(multiplier.valid _) = true)
      (pfINotFinished: qs.(multiplier.finished _) = false)
      (pfReq: spec.(reqs) = [{| input_a := qs.(multiplier.op1 _);
                                 input_b := qs.(multiplier.op2 _) |}])
      (pfLeakage: let pubQs := PubImpl spec in
                  QSignalsEq qs pubQs /\ shortCircuitEqQ qs pubQs)
  | CaseFinished
      (pfIValid: qs.(multiplier.valid _) = true)
      (pfIFinished: qs.(multiplier.finished _) = true)
      (pfReq: exists req, spec.(reqs) = [req] /\
              qs.(multiplier.result _) = MultiplierSpec.handle_req req)
      (pfSignalsEq: QSignalsEq qs (PubImpl spec))
  .
  Record Rel (qs: qst) (spec: spec_st_t) : Prop :=
    { Rel_base: RelBase qs spec;
      Rel_core: RelCore qs spec }.
  Set Printing Coercions.
  Ltac solve_bv_eq :=
    match goal with
    | |- (_: bv _) = (_ :bv _) =>
        apply bv_eq; reflexivity
    end.

  Lemma Rel_init : Rel (initialState mul_qspec) (initialState abstract_spec).
  Proof.
    constructor; cbn; constructor; cbn; auto; try solve_bv_eq.
    unfold QSignalsEq; auto.
  Qed.

  Create HintDb mul.

  Lemma evalITrace_app:
    forall xs ys,
    evalITrace (xs ++ ys) =
    Trace.execTrace mul_qspec (map CallEvent ys) (evalITrace xs).
  Proof.
    intros; unfold evalITrace. rewrite execTrace_mapApp. reflexivity.
  Qed.

  Lemma evalSTrace_app:
    forall xs ys,
    evalSTrace (xs ++ ys) =
    Trace.execTrace abstract_spec (map CallEvent ys) (evalSTrace xs).
  Proof.
    intros; unfold evalSTrace. rewrite execTrace_mapApp. auto.
  Qed.

  Hint Rewrite evalITrace_app : mul.
  Hint Rewrite evalSTrace_app : mul.
  Hint Rewrite @execTrace_mapApp : mul.
  Hint Rewrite map_app : mul.

  Lemma evalLeakageTrace_app:
    forall xs ys,
    evalLeakageTrace (xs ++ ys) =
    Trace.execTrace mul_qspec
      (map CallEvent (map lift_leakage_event ys))
      (evalLeakageTrace xs).
  Proof.
    intros; unfold evalLeakageTrace, evalITrace.
    rewrite map_app, map_app, execTrace_app, map_map. auto.
  Qed.

  Hint Rewrite evalLeakageTrace_app : mul.

  Ltac mul_simplify :=
    repeat match goal with
    | H: RelBase ?qs ?s2 |- context[evalITrace (hist ?s2)] =>
        rewrite impl_hist_rel with (1 := H)
    | H: RelBase ?qs ?s2
      |- context[evalSTrace (hist ?s2)] =>
      setoid_rewrite spec_hist_rel with (1 := H)
     | H: ?x _ = ?x (evalLeakageTrace _) |- context[?x (evalLeakageTrace _)] => setoid_rewrite<-H
    | H : () |- _ => destruct H
    | H : ?x = ?x |- _ => clear H
    | _ => progress (repeat simpl_match; auto)
    end.

  Ltac mul_simp :=
    repeat progress (cbn in *; propositional; mul_simplify;
                     autorewrite with mul).

  Ltac simp_qSignalsEq :=
    mul_simp; repeat dep_simpl_match; repeat simpl_match;
    consider QSignalsEq; mul_simp.

  Arguments evalSTrace : simpl never.
  Arguments evalITrace : simpl never.

  Lemma RelImplQSignalsEq:
    forall qs spec,
    Rel qs spec ->
    QSignalsEq qs (PubImpl spec).
  Proof.
    intros * rel. apply Rel_core in rel.
    destruct rel; cbn in *; propositional.
  Qed.

  Lemma RespReadyOk:
    forall (qs: qst) spec,
    Rel qs spec ->
    evalVMet_q RespReady qs =
      EvalVMethod abstract_spec RespReady spec.
  Proof.
    intros * rel. pose proof rel as Hrel. inv Hrel.
    inv Rel_base0.
    inv Rel_core0; simpl; cbv[respReady]; simp_qSignalsEq; cbv[resp_ready].
    all: set (evalITrace (hist spec)) as tr in *; 
         set (PubImpl spec) as pub_tr in *; 
         simpl in *; destruct_pairs;
         simpl in *; subst; auto.
  Qed.

  Lemma FullOk:
    forall (qs: qst) spec,
    Rel qs spec ->
    evalVMet_q Full qs =
      EvalVMethod abstract_spec Full spec.
  Proof.
    intros * rel. pose proof rel as Hrel. inv Hrel.
    inv Rel_base0.
    inv Rel_core0; simpl; cbv[is_full]; simp_qSignalsEq; cbv[resp_ready].
    all: set (evalITrace (hist spec)) as tr in *; 
         set (PubImpl spec) as pub_tr in *; 
         simpl in *; destruct_pairs;
         simpl in *; subst; auto.
  Qed.

  Lemma PeekOk:
    forall (qs: qst) spec,
    Rel qs spec ->
    evalVMet_q Peek qs =
      EvalVMethod abstract_spec Peek spec.
  Proof.
    intros * rel. pose proof rel as Hrel. inv Hrel.
    inv Rel_base0.
    inv Rel_core0; simpl; cbv[peek]; simp_qSignalsEq; cbv[default_peek resp_ready].
    all: set (evalITrace (hist spec)) as tr in *; 
         set (PubImpl spec) as pub_tr in *; 
         simpl in *; destruct_pairs;
         simpl in *; subst; auto.
  Qed.

  Ltac start_action_method :=
    intros qs qs' r spec * Hrel *; pose proof Hrel as rel; inv rel;
    cbn; intros himpl; mul_simplify;
    eexists; split; simplify_tupless; eauto;
    unfold set; cbn.

  Lemma one_neq_zero:
    forall n,
    (n <> 0)%N ->
    of_Z n 1 = bv_0 n->
    False.
  Proof.
    intros. apply f_equal with (f := bv_unsigned) in H0.
    consider of_Z. rewrite bv_0_unsigned in H0.
    rewrite Z_to_bv_small in H0.
    - lia.
    - apply bv_modulus_gt_1 in H. lia.
  Qed.
  (* Lemma bv_to_bits_eq: *)
  (*   forall n (b: bv n) v, bv_to_bits b = v -> *)
  (*                  bv_unsigned b = (bv_to_bits b). *)
  Lemma bv_mul'_zero:
    forall m n (op1 op2: bv n),
    op1 = bv_0 _ \/ op2 = bv_0 _ ->
    bv_mul' m op1 op2 = bv_0 _.
  Proof.
    intros. unfold bv_mul'.
    destruct H; subst; rewrite @bv_0_unsigned; auto.
    - cbv. rewrite bv_eq. by rewrite @bv_0_unsigned.
    - rewrite bv_eq. rewrite @bv_0_unsigned.
      rewrite Z.mul_comm. auto.
  Qed.

  Lemma EnqOk:
    forall (qs qs': qst) r spec arg,
    Rel qs spec ->
    EvalMethod mul_qspec (Enq arg) qs = (r, qs')
    -> exists spec', EvalMethod abstract_spec (Enq arg) spec = (r, spec') /\
                     Rel qs' spec'.
  Proof.
    start_action_method.
    constructor.
    - (* RelBase *)
      constructor; cbn; mul_simp; unfold snd, set; mul_simp.
    - (* RelCore *)
      mul_simp. destruct spec. unfold MultiplierSpec.enq; cbn.
      destruct_pairs. simpl. inv Rel_base0.
      inv Rel_core0; simp_qSignalsEq; simpl in *; subst;
        mul_simp; simp_qSignalsEq.
      + (* CaseEmpty *)
        apply CaseBusy; cbv[is_full]; cbn; auto;
          simp_qSignalsEq;
          set (evalLeakageTrace (map leakage_of_AM hist)) as pubSt in *; simpl in *;
          destruct_pairs; simpl in *; subst;  eauto.
        { destruct arg; simpl;  auto.
        }
        { simp_qSignalsEq.
          unfold shortCircuitEqQ. cbn.
          destruct arg; simpl.
          cbv[BV.nonzero BV.embed_bool mk_bit]; simpl.
          rewrite Z_to_bv_unsigned. simpl.
          split_and!; auto.
          case_bool_decide as Hzero_arg; cbn; auto; repeat split; try by auto.
          { intros. 
            split_ors_in H.
            { apply one_neq_zero in H; auto. done. }
            { apply one_neq_zero in H; auto. done. }
          }
        }
      + (* CaseBusy *)
        apply CaseBusy; cbv[is_full]; cbn; auto;
          simp_qSignalsEq;
          set (evalLeakageTrace (map leakage_of_AM hist)) as pubSt in *; simpl in *;
          destruct_pairs; simpl in *; subst;  eauto.
      + (* CaseFinished *)
        apply CaseFinished; cbv[is_full]; cbn; eauto; simp_qSignalsEq;
          set (evalLeakageTrace (map leakage_of_AM hist)) as pubSt in *; simpl in *;
          destruct_pairs; simpl in *; subst;  eauto.
  Qed.

  Lemma DeqOk:
    forall qs r (qs': qst) spec,
    Rel qs spec ->
    EvalMethod mul_qspec Deq qs = (r, qs')
    -> exists spec', EvalMethod abstract_spec Deq spec = (r, spec') /\
                     Rel qs' spec'.
  Proof.
    start_action_method.
    constructor.
    - constructor; cbn; mul_simp; unfold snd, set; mul_simp.
    - mul_simp. destruct spec. unfold MultiplierSpec.deq, MultiplierSpec.respReady; cbn.
      destruct_pairs. simpl. inv Rel_base0.
      inv Rel_core0; simpl in *; subst; 
        simp_qSignalsEq; cbv[leakage] in *.
      + apply CaseEmpty; cbn; simp_qSignalsEq;
          simp_qSignalsEq;
          set (evalLeakageTrace (map leakage_of_AM hist)) as pubSt in *; simpl in *;
          destruct_pairs; simpl in *; subst;  auto.
      + apply CaseBusy; cbv[resp_ready]; cbn; eauto; simp_qSignalsEq;
          set (evalLeakageTrace (map leakage_of_AM hist)) as pubSt in *; simpl in *;
          destruct_pairs; simpl in *; subst;  auto.
      + apply CaseEmpty; cbv[resp_ready]; cbn; simp_qSignalsEq;
          set (evalLeakageTrace (map leakage_of_AM hist)) as pubSt in *; simpl in *;
          destruct_pairs; simpl in *; subst;  auto.
  Qed.

  Lemma unfold_match_andb:
    forall b1 b2 {A} (x y: A),
    (if b1 && b2 then x else y) =
    (if b1 then if b2 then x else y else y).
  Proof.
    intros. destruct b1; auto.
  Qed.

  Lemma unfold_match_negb:
    forall b1 {A} (x y: A),
    (if negb b1 then x else y) =
    (if b1 then y else x).
  Proof.
    intros. destruct b1; auto.
  Qed.

  Create HintDb progStep.
  Hint Rewrite unfold_match_andb : progStep.
  Hint Rewrite unfold_match_negb : progStep.

  Lemma embed_bool_false :
    embed_bool false = Z_to_bv 1 0. 
  Proof.
    apply bv_eq. reflexivity.
  Qed.
  Lemma embed_bool_true:
    embed_bool true = Z_to_bv 1 1. 
  Proof.
    apply bv_eq. reflexivity.
  Qed.

  Lemma bv_unsigned_mk_bit_true:
    bv_unsigned (mk_bit true) = 1%Z.
  Proof.
    reflexivity.
  Qed.
  Lemma bv_unsigned_mk_bit_false:
    bv_unsigned (mk_bit false) = 0%Z.
  Proof.
    reflexivity.
  Qed.

  Create HintDb bits.
  Hint Rewrite bv_unsigned_mk_bit_false : bits.
  Hint Rewrite bv_unsigned_mk_bit_true : bits.
  Hint Rewrite embed_bool_true : bits.
  Hint Rewrite embed_bool_false : bits.

  Lemma TickOk:
    forall qs r (qs': qst) spec,
    Rel qs spec ->
    EvalMethod mul_qspec Tick qs = (r, qs')
    -> exists spec', EvalMethod abstract_spec Tick spec = (r, spec') /\
                     Rel qs' spec'.
  Proof.
    start_action_method.
    constructor.
    - (* RelBase maintained *)
      constructor; mul_simp; unfold set; cbn; mul_simp.
    - (* RelCore: case split on current RelCore branch *)
      mul_simp. destruct spec. unfold MultiplierSpec.tick; cbn.
      destruct_pairs.
      inv Rel_core0; simp_qSignalsEq; simplify_tupless; mul_simp; simpl.

      + (* CaseEmpty: valid = false → outer if-then-else gives qs' = qs *)
        apply CaseEmpty; cbn; mul_simp;
          set (evalLeakageTrace (map leakage_of_AM hist)) as pubSt in *; simpl.
        rewrite embed_bool_false in *. 
        cbv[nonzero] in *. simpl in *.
        repeat rewrite Z_to_bv_unsigned. simpl.
        rewrite bv_and_unsigned. simpl.
        repeat rewrite Z_to_bv_unsigned. simpl.
        rewrite bv_not_unsigned. destruct_pairs; simpl in *; subst.
        destruct_pairs. simpl in *. subst.
        simp_qSignalsEq.
      + (* CaseBusy: valid = true, finished = false → active computation *)
        (* The Quartz tick uses bits arithmetic; correspondence with algebraic *)
    (*        tick follows by the same case analysis, using qzero_bv_zero and *)
    (*        the bits-arithmetic correspondence lemmas (cf. lower_mul_tick_ok in *)
    (*        QuartzImpl.v for the detailed proof). *)
    (*        We case-split on the Quartz zero-check condition: *)
        cbv[nonzero] in *.
        rewrite embed_bool_true in *.
        rewrite embed_bool_false in *.
        repeat rewrite bv_and_unsigned. 
        repeat rewrite Z_to_bv_unsigned. simpl.
        rewrite bv_unsigned_mk_bit_true. simpl.
        (* rewrite andb_true_l.  *)
        (* autorewrite with zmod. simpl. *)

        case_goal_match eqn : Hzero ; [ | case_goal_match eqn:Hones].
        * apply CaseFinished; cbn; eauto; mul_simp;
          set (evalLeakageTrace (map leakage_of_AM hist)) as pubSt in *; simpl;
            simp_qSignalsEq; destruct_pairs; simpl in *; subst;
            consider shortCircuitEqQ;  simpl.
          { eexists; split; eauto. cbv[handle_req bv_mul']. simpl.
            rewrite bv_or_unsigned in *.
            repeat rewrite Z_to_bv_unsigned in *. simpl in *.
            rewrite negb_true_iff in *.
            rewrite Z.eqb_neq in *.
            unfold not in *.
            rewrite Z.lor_eq_0_iff in *.
            rewrite Decidable.not_and_iff in *.
            destruct (bv_unsigned b0 =? 0)%Z eqn:Heqb0; 
              destruct (bv_unsigned b1 =? 0)%Z eqn:Heqb1; 
              try rewrite Z.eqb_eq in *;
              try rewrite Z.eqb_neq in *;
              try rewrite bv_eq in *; rewrite bv_0_unsigned in *;
              autorewrite with bits in *; propositional.
            { setoid_rewrite Heqb0. reflexivity. }
            { setoid_rewrite Heqb0. reflexivity. }
            { setoid_rewrite Heqb1. rewrite Z.mul_comm. reflexivity. }
          } 
          { simpl in *. 
            rewrite negb_true_iff in *.
            rewrite Z.eqb_neq in *. simpl in *.
            unfold not in *.
            rewrite bv_or_unsigned in *.
            rewrite Z.lor_eq_0_iff in *; autorewrite with bits in *.
            rewrite Decidable.not_and_iff in *.
            simpl.
            cbv[nonzero].
            repeat rewrite Z_to_bv_unsigned in *. simpl in *.
            rewrite bv_and_unsigned in *.
            repeat rewrite Z_to_bv_unsigned in *. simpl in *. simpl.
            rewrite bv_wrap_small by (unfold bv_modulus; lia). simpl.
            autorewrite with bits. simpl.
            case_match; auto.
            exfalso.
            rewrite negb_false_iff in *.
            rewrite Z.eqb_eq in *. simpl in *.
            rewrite bv_or_unsigned in *.
            destruct (bv_unsigned b3 =? 0)%Z eqn:Heqb3; 
              destruct (bv_unsigned b4 =? 0)%Z eqn:Heqb4; 
              try rewrite Z.eqb_eq in *;
              try rewrite Z.eqb_neq in *;
              try rewrite bv_eq in *; rewrite bv_0_unsigned in *;
              autorewrite with bits in *; simpl in *; propositional; try discriminate;
              try rewrite bv_eq in *; rewrite bv_0_unsigned in *.
            destruct (bv_unsigned b0 =? 0)%Z eqn:Heqb0; 
              destruct (bv_unsigned b1 =? 0)%Z eqn:Heqb1;
              autorewrite with bits in *; repeat rewrite bv_eq in *;
              try rewrite Z.eqb_eq in *;
              try rewrite Z.eqb_neq in *;
              try rewrite Heqb0 in *; try rewrite Heqb1 in *;
              propositional;repeat rewrite bv_0_unsigned in *.
            { split_ors_in pfLeakage0; propositional. }
            { split_ors_in pfLeakage0; propositional. }
            { split_ors_in pfLeakage0; propositional. }
          } 
        *
          apply CaseFinished; cbn; eauto; mul_simp;
          set (evalLeakageTrace (map leakage_of_AM hist)) as pubSt in *; simpl;
            simp_qSignalsEq; destruct_pairs; simpl in *; subst;
            consider shortCircuitEqQ; simpl in *.
          cbv[nonzero]. repeat rewrite bv_and_unsigned.
          repeat rewrite Z_to_bv_unsigned in *. simpl in *.
          rewrite bv_wrap_small by (unfold bv_modulus; lia). simpl.
          autorewrite with bits. simpl.
          rewrite bv_or_unsigned in *. simpl.
          repeat simpl_match.
          repeat rewrite bv_eq in *.
          repeat rewrite bv_0_unsigned in *.
          rewrite negb_false_iff in *.
          rewrite Z.eqb_eq in *.
          rewrite Z.lor_eq_0_iff in *; autorewrite with bits in *.
          repeat rewrite bool_to_bv_unsigned in * by lia.
          propositional.
          case_match; auto.
        * 
          apply CaseBusy; cbn; eauto; mul_simp.
          set (evalLeakageTrace (map leakage_of_AM hist)) as pubSt in *; simpl in *; subst.
          destruct_pairs; simpl in *; subst. consider shortCircuitEqQ.
          autorewrite with bits in *. simpl in *. simpl_match. simp_qSignalsEq.
          case_match ;propositional; simpl; auto.
          { case_match; simpl; auto.
            { exfalso.
              cbv in H0. cbv in Hzero.
              repeat rewrite bv_eq in *.
              repeat rewrite bv_0_unsigned in *.
              cbv[nonzero] in *.
              bash_destruct Hzero; vm_compute in H; try discriminate.
              bash_destruct H0; simpl in *; propositional; try discriminate;
                split_ors_in  pfLeakage2; try discriminate.
            }
            { split_and!; auto. split; auto. }
          }
          { vm_compute in H. discriminate. }
      + mul_simp.  simpl. 
        apply CaseFinished; cbn; eauto. mul_simp. simp_qSignalsEq.
          set (evalLeakageTrace (map leakage_of_AM hist)) as pubSt in *; simpl in *; subst.
          destruct_pairs; simpl in *; subst. consider shortCircuitEqQ.
          simpl in *. auto.
  Qed. 

  Theorem refines_mul_q :
    refines mul_qspec abstract_spec Rel.
  Proof.
    cbv[refines]. intros * Hrel *.
    split.
    - destruct vmethod.
      + by apply RespReadyOk.
      + by apply FullOk.
      + by apply PeekOk.
    - destruct method; intros.
      + by eapply EnqOk.
      + by eapply DeqOk.
      + by eapply TickOk.
  Qed.

  Corollary simulates_mul_q :
    simulates mul_qspec abstract_spec.
  Proof.
    unfold simulates. exists Rel.
    split; [by apply Rel_init | by apply refines_mul_q].
  Qed.

End WithContext.
