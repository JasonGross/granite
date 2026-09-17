(*! Proof that [MemoryImpl] satisfies the memory model [MemorySpec].

    This is the "simplest memory system, fully verified" promised in the
    rebuttal: a memory with no cache, write-through stores, one outstanding
    load and a one-slot response buffer, shown to be a correct
    (leakage-preserving) implementation of the memory specification that the
    pipelined-processor proof is stated against.

    Following the methodology of the paper (and of
    [MultiplierSimulates.v]/[Fifo1Simulates.v]), the abstract spec's
    quasi-nondeterministic [SpecParams] are *instantiated here*, as functions
    of the leakage trace replayed by the implementation; the resulting
    statement is [Simulates.simulates] between the implementation and
    [MemorySpec.spec], i.e. the implementation is trace-equivalent to the
    memory model while leaking exactly the same events. *)
From stdpp Require Import base nmap tactics.
From RecordUpdate Require Import RecordSet.
From granite.core Require Import
  Bits
  Utils
  Program
  Simulates
  Tactics
  Trace
  TraceFacts.
From granite.app Require Import
  MemoryAPI
  MemorySpec
  MemoryImpl.
Import RecordSetNotations.

Section WithContext.
  Context {params: Params.Params}.
  Context (init_mem: MemorySpec.memory_t).

  Notation impl_spec := (MemoryImpl.spec init_mem).
  Notation abs_spec := (MemorySpec.spec init_mem).

  (*! Run the implementation on an action-method trace. *)
  Definition evalITrace (tr: MemorySpec.trace_t) : MemoryImpl.St :=
    Trace.execTrace impl_spec (map CallEvent tr) impl_spec.(initialState).

  (*! The [SpecParams] of the abstraction, defined by replaying the
      implementation on the trace seen so far.  Consequently the abstraction
      is deterministic, and its schedule coincides with the implementation's. *)
  Definition default_peek (tr: MemorySpec.trace_t) : MemoryAPI.mem_resp_t :=
    MemoryImpl.peek (evalITrace tr).
  Definition resp_ready (tr: MemorySpec.leakage_trace_t) : bool :=
    MemoryImpl.respReady (MemoryImpl.execC init_mem tr (MemoryImpl.initial_st init_mem)).
  Definition is_full (tr: MemorySpec.leakage_trace_t) : bool :=
    MemoryImpl.full (MemoryImpl.execC init_mem tr (MemoryImpl.initial_st init_mem)).

  #[export] Instance memImplSpecParams : MemorySpec.SpecParams :=
    {| MemorySpec.default_peek := default_peek;
       MemorySpec.resp_ready := resp_ready;
       MemorySpec.is_full := is_full |}.

  Lemma default_peek_eq (h: MemorySpec.trace_t) :
    MemorySpec.default_peek h = MemoryImpl.peek (evalITrace h).
  Proof. reflexivity. Qed.

  (*! Response queue of the abstraction, as a function of the implementation
      state: the abstraction produces a load's response as soon as the request
      is accepted, and it becomes consumable one [Tick] later. *)
  Definition spec_resps (st: MemoryImpl.St) : list MemoryAPI.mem_resp_t :=
    match st.(MemoryImpl.resp_addr) with
    | Some a => [MemoryImpl.load_resp st a]
    (* the abstraction already produces a load's response when the request is
       accepted; it becomes consumable one [Tick] later *)
    | None =>
        match st.(MemoryImpl.inflight) with
        | Some a => [MemoryImpl.load_resp st a]
        | None => []
        end
    end.

  (*! Record updates of the two state records compute on projections; [cbn]
      does not perform these reductions, so we spell them out. *)
  Lemma array_set (st: MemoryImpl.St) (v: MemorySpec.memory_t) :
    MemoryImpl.array (st <| MemoryImpl.array := v |>) = v.
  Proof. reflexivity. Qed.
  Lemma array_set_inflight (st: MemoryImpl.St) (v: option (bits Params.width)) :
    MemoryImpl.array (st <| MemoryImpl.inflight := v |>) = MemoryImpl.array st.
  Proof. reflexivity. Qed.
  Lemma array_set_resp (st: MemoryImpl.St) (v: option (bits Params.width)) :
    MemoryImpl.array (st <| MemoryImpl.resp_addr := v |>) = MemoryImpl.array st.
  Proof. reflexivity. Qed.
  Lemma resp_addr_set (st: MemoryImpl.St) (v: option (bits Params.width)) :
    MemoryImpl.resp_addr (st <| MemoryImpl.resp_addr := v |>) = v.
  Proof. reflexivity. Qed.
  (* [tick] performs both updates at once. *)
  Lemma array_set_tick (st: MemoryImpl.St) (i r: option (bits Params.width)) :
    MemoryImpl.array (st <| MemoryImpl.inflight := i |> <| MemoryImpl.resp_addr := r |>)
    = MemoryImpl.array st.
  Proof. reflexivity. Qed.
  Lemma inflight_set_tick (st: MemoryImpl.St) (i r: option (bits Params.width)) :
    MemoryImpl.inflight (st <| MemoryImpl.inflight := i |> <| MemoryImpl.resp_addr := r |>) = i.
  Proof. reflexivity. Qed.
  Lemma resp_addr_set_tick (st: MemoryImpl.St) (i r: option (bits Params.width)) :
    MemoryImpl.resp_addr (st <| MemoryImpl.inflight := i |> <| MemoryImpl.resp_addr := r |>) = r.
  Proof. reflexivity. Qed.
  Lemma inflight_set_resp (st: MemoryImpl.St) (v: option (bits Params.width)) :
    MemoryImpl.inflight (st <| MemoryImpl.resp_addr := v |>) = MemoryImpl.inflight st.
  Proof. reflexivity. Qed.
  Lemma resp_set_inflight (st: MemoryImpl.St) (v: option (bits Params.width)) :
    MemoryImpl.resp_addr (st <| MemoryImpl.inflight := v |>) = MemoryImpl.resp_addr st.
  Proof. reflexivity. Qed.
  Lemma resp_addr_array_set (st: MemoryImpl.St) (v: MemorySpec.memory_t) :
    MemoryImpl.resp_addr (st <| MemoryImpl.array := v |>) = MemoryImpl.resp_addr st.
  Proof. reflexivity. Qed.
  Lemma inflight_array_set (st: MemoryImpl.St) (v: MemorySpec.memory_t) :
    MemoryImpl.inflight (st <| MemoryImpl.array := v |>) = MemoryImpl.inflight st.
  Proof. reflexivity. Qed.
  Lemma inflight_set (st: MemoryImpl.St) (v: option (bits Params.width)) :
    MemoryImpl.inflight (st <| MemoryImpl.inflight := v |>) = v.
  Proof. reflexivity. Qed.
  Lemma mem_set_b (b: MemorySpec.base_st_t) (v: MemorySpec.memory_t) :
    MemorySpec.mem (b <| MemorySpec.mem := v |>) = v.
  Proof. reflexivity. Qed.
  Lemma resps_mem_set (b: MemorySpec.base_st_t) (v: MemorySpec.memory_t) :
    MemorySpec.resps (b <| MemorySpec.mem := v |>) = MemorySpec.resps b.
  Proof. reflexivity. Qed.
  Lemma mem_resps_set (b: MemorySpec.base_st_t) (f: list MemoryAPI.mem_resp_t -> list MemoryAPI.mem_resp_t) :
    MemorySpec.mem (b <| MemorySpec.resps ::= f |>) = MemorySpec.mem b.
  Proof. reflexivity. Qed.
  Lemma resps_resps_set (b: MemorySpec.base_st_t) (f: list MemoryAPI.mem_resp_t -> list MemoryAPI.mem_resp_t) :
    MemorySpec.resps (b <| MemorySpec.resps ::= f |>) = f (MemorySpec.resps b).
  Proof. reflexivity. Qed.
  Lemma base_set (s: MemorySpec.st_t) (v: MemorySpec.base_st_t) :
    MemorySpec.base (s <| MemorySpec.base := v |>) = v.
  Proof. reflexivity. Qed.
  Lemma hist_set (s: MemorySpec.st_t) (v: MemorySpec.base_st_t) :
    MemorySpec.hist (s <| MemorySpec.base := v |>) = MemorySpec.hist s.
  Proof. reflexivity. Qed.
  Lemma base_fset (s: MemorySpec.st_t) (g: MemorySpec.base_st_t -> MemorySpec.base_st_t) :
    MemorySpec.base (s <| MemorySpec.base ::= g |>) = g (MemorySpec.base s).
  Proof. reflexivity. Qed.
  Lemma hist_fset (s: MemorySpec.st_t) (g: MemorySpec.trace_t -> MemorySpec.trace_t) :
    MemorySpec.hist (s <| MemorySpec.hist ::= g |>) = g (MemorySpec.hist s).
  Proof. reflexivity. Qed.

  Record Rel (impl: MemoryImpl.St) (spec: MemorySpec.st_t) := {
    rel_array : MemoryImpl.array impl = spec.(MemorySpec.base).(MemorySpec.mem);
    rel_resps : spec.(MemorySpec.base).(MemorySpec.resps) = spec_resps impl;
    rel_hist : evalITrace spec.(MemorySpec.hist) = impl;
    rel_inv : MemoryImpl.inflight impl = None \/ MemoryImpl.resp_addr impl = None
  }.

  Lemma evalITrace_app (tr1 tr2: MemorySpec.trace_t) :
    evalITrace (tr1 ++ tr2)
    = Trace.execTrace impl_spec (map CallEvent tr2) (evalITrace tr1).
  Proof.
    unfold evalITrace. rewrite execTrace_mapApp. reflexivity.
  Qed.

  Lemma evalITrace_exec (tr: MemorySpec.trace_t) :
    evalITrace tr = MemoryImpl.exec init_mem tr (MemoryImpl.initial_st init_mem).
  Proof. unfold evalITrace, impl_spec, MemoryImpl.spec, initialState; reflexivity. Qed.

  Lemma evalITrace_snoc_enq (req: MemoryAPI.mem_req_t) (h: MemorySpec.trace_t) :
    evalITrace (h ++ [MemoryAPI.Enq req]) = MemoryImpl.enq req (evalITrace h).
  Proof. rewrite evalITrace_app. reflexivity. Qed.

  Lemma evalITrace_snoc_deq (h: MemorySpec.trace_t) :
    evalITrace (h ++ [MemoryAPI.Deq]) = MemoryImpl.deq (evalITrace h).
  Proof. rewrite evalITrace_app. reflexivity. Qed.

  Lemma evalITrace_snoc_tick (h: MemorySpec.trace_t) :
    evalITrace (h ++ [MemoryAPI.Tick]) = MemoryImpl.tick (evalITrace h).
  Proof. rewrite evalITrace_app. reflexivity. Qed.

  Lemma evalITrace_step (m: MemoryAPI.ActionMethod unit) (tr: MemorySpec.trace_t) :
    evalITrace (m :: tr)
    = Trace.execTrace impl_spec (map CallEvent tr)
        (snd (impl_spec.(EvalMethod) m (impl_spec.(initialState)))).
  Proof.
    unfold evalITrace, impl_spec, initialState. cbn. reflexivity.
  Qed.

  (*! Scheduling facts: [resp_ready]/[is_full]/[default_peek] of the
      abstraction, at the state reached by a trace, are the implementation's
      own [respReady]/[full]/[peek]. *)
  Lemma resp_ready_sim (tr: MemorySpec.trace_t) :
    resp_ready (MemorySpec.leakage tr) = MemoryImpl.respReady (evalITrace tr).
  Proof.
    unfold resp_ready.
    rewrite MemoryImpl.respReady_ctrl.
    rewrite (MemoryImpl.ctrl_exec_leakage init_mem tr (MemoryImpl.initial_st init_mem)).
    rewrite <- MemoryImpl.respReady_ctrl, evalITrace_exec. done.
  Qed.

  Lemma is_full_sim (tr: MemorySpec.trace_t) :
    is_full (MemorySpec.leakage tr) = MemoryImpl.full (evalITrace tr).
  Proof.
    unfold is_full.
    rewrite MemoryImpl.full_ctrl.
    rewrite (MemoryImpl.ctrl_exec_leakage init_mem tr (MemoryImpl.initial_st init_mem)).
    rewrite <- MemoryImpl.full_ctrl, evalITrace_exec. done.
  Qed.

  Lemma Rel_init : Rel (impl_spec.(initialState)) (abs_spec.(initialState)).
  Proof.
    unfold impl_spec, abs_spec, initialState; simpl.
    constructor; simpl; auto; left; reflexivity.
  Qed.

  Lemma base_proj (b: MemorySpec.base_st_t) (h: MemorySpec.trace_t) :
    MemorySpec.base (Build_st_t b h) = b.
  Proof. reflexivity. Qed.

  Lemma hist_proj (b: MemorySpec.base_st_t) (h: MemorySpec.trace_t) :
    MemorySpec.hist (Build_st_t b h) = h.
  Proof. reflexivity. Qed.

  (*! The relation, phrased over a decomposed abstraction state; this is
      equivalent to [Rel] but avoids projections of record updates.  The last
      conjunct is a realisability invariant of the implementation: the module
      never has a load in flight and a buffered response at the same time. *)
  Definition RelB (impl: MemoryImpl.St) (b: MemorySpec.base_st_t) (h: MemorySpec.trace_t)
    : Prop :=
    MemoryImpl.array impl = MemorySpec.mem b /\
    MemorySpec.resps b = spec_resps impl /\
    evalITrace h = impl /\
    (MemoryImpl.inflight impl = None \/ MemoryImpl.resp_addr impl = None).

  Lemma rel_relB (impl: MemoryImpl.St) (b: MemorySpec.base_st_t) (h: MemorySpec.trace_t) :
    Rel impl (Build_st_t b h) <-> RelB impl b h.
  Proof.
    split.
    - intros [H1 H2 H3 H4]. unfold RelB. auto.
    - intros [H1 [H2 [H3 H4]]]. constructor; auto.
  Qed.

  (*! Value methods agree. *)
  Lemma respReady_simB (impl: MemoryImpl.St) (b: MemorySpec.base_st_t) (h: MemorySpec.trace_t)
                       (H: RelB impl b h) :
    MemorySpec.respReady (Build_st_t b h) = MemoryImpl.respReady impl.
  Proof.
    destruct H as [Harr [Hres [Hhist Hinv]]].
    unfold MemorySpec.respReady. rewrite base_proj, hist_proj. rewrite Hres.
    rewrite resp_ready_sim, Hhist.
    unfold spec_resps, MemoryImpl.respReady.
    destruct (MemoryImpl.resp_addr impl) as [a|] eqn:Hr;
      destruct (MemoryImpl.inflight impl) as [i|] eqn:Hi;
      reflexivity.
  Qed.

  Lemma full_simB (impl: MemoryImpl.St) (b: MemorySpec.base_st_t) (h: MemorySpec.trace_t)
                  (H: RelB impl b h) :
    MemorySpec.full (Build_st_t b h) = MemoryImpl.full impl.
  Proof.
    destruct H as [Harr [Hres [Hhist Hinv]]].
    unfold MemorySpec.full. rewrite hist_proj. rewrite is_full_sim, Hhist. done.
  Qed.

  Lemma peek_simB (impl: MemoryImpl.St) (b: MemorySpec.base_st_t) (h: MemorySpec.trace_t)
                  (H: RelB impl b h) :
    MemorySpec.peek (Build_st_t b h) = MemoryImpl.peek impl.
  Proof.
    pose proof (respReady_simB impl b h H) as Hrr.
    destruct H as [Harr [Hres [Hhist Hinv]]].
    unfold MemorySpec.peek, MemoryImpl.peek.
    rewrite base_proj, hist_proj.
    rewrite Hrr, Hres.
    unfold spec_resps, MemoryImpl.respReady.
    destruct (MemoryImpl.resp_addr impl) as [a|] eqn:Hr.
    - reflexivity.
    - rewrite default_peek_eq, Hhist; unfold MemoryImpl.peek; rewrite Hr; reflexivity.
  Qed.

  (*! One-step characterizations of the abstraction's methods. *)
  Lemma abs_enq_dropped (req: MemoryAPI.mem_req_t) (spec: MemorySpec.st_t) :
    MemorySpec.full spec = true -> MemorySpec.enq req spec = spec.(MemorySpec.base).
  Proof. unfold MemorySpec.enq; intros H; rewrite H; reflexivity. Qed.

  Lemma abs_enq_store (req: MemoryAPI.mem_req_t) (spec: MemorySpec.st_t) :
    MemorySpec.full spec = false -> mem_req_is_store req = true ->
    MemorySpec.enq req spec
      = spec.(MemorySpec.base)
        <| MemorySpec.mem := MemorySpec.mem_store (MemorySpec.mem (MemorySpec.base spec))
                                                  (to_N (mem_req_addr req))
                                                  (mem_req_data req) |>.
  Proof.
    unfold MemorySpec.enq, MemorySpec.handle_req.
    intros H1 H2; rewrite H1, H2; reflexivity.
  Qed.

  Lemma abs_enq_load (req: MemoryAPI.mem_req_t) (spec: MemorySpec.st_t) :
    MemorySpec.full spec = false -> mem_req_is_store req = false ->
    MemorySpec.enq req spec
      = spec.(MemorySpec.base)
        <| MemorySpec.resps ::= (fun r => r
                                   ++ [{| mem_resp_addr := mem_req_addr req;
                                          mem_resp_data := MemorySpec.mem_load
                                                             (MemorySpec.mem (MemorySpec.base spec))
                                                             (to_N (mem_req_addr req)) |}]) |>.
  Proof.
    unfold MemorySpec.enq, MemorySpec.handle_req.
    intros H1 H2; rewrite H1, H2; reflexivity.
  Qed.

  Lemma abs_deq_true (spec: MemorySpec.st_t) :
    MemorySpec.respReady spec = true ->
    MemorySpec.deq spec = spec.(MemorySpec.base) <| MemorySpec.resps ::= tl |>.
  Proof. unfold MemorySpec.deq; intros H; rewrite H; reflexivity. Qed.

  Lemma abs_deq_false (spec: MemorySpec.st_t) :
    MemorySpec.respReady spec = false -> MemorySpec.deq spec = spec.(MemorySpec.base).
  Proof. unfold MemorySpec.deq; intros H; rewrite H; reflexivity. Qed.

  Lemma abs_tick (spec: MemorySpec.st_t) :
    MemorySpec.tick spec = spec.(MemorySpec.base).
  Proof. reflexivity. Qed.


  (*! Action methods correspond. *)
  Lemma enq_sim (req: MemoryAPI.mem_req_t) (impl: MemoryImpl.St)
                (b: MemorySpec.base_st_t) (h: MemorySpec.trace_t) :
    RelB impl b h ->
    RelB (MemoryImpl.enq req impl)
         (MemorySpec.enq req (Build_st_t b h)) (h ++ [MemoryAPI.Enq req]).
  Proof.
    intros [Harr [Hres [Hhist Hinv]]].
    assert (Hfull: MemorySpec.full (Build_st_t b h) = MemoryImpl.full impl)
      by (apply (full_simB impl b h); constructor; auto).
    unfold MemoryImpl.full in Hfull.
    assert (Hbusy := Hfull).
    unfold MemoryImpl.enq, MemorySpec.enq, MemorySpec.handle_req.
    rewrite Hbusy.
    destruct (MemoryImpl.busy impl) as [|] eqn:Hb.
    - (* the request is dropped on both sides *)
      unfold RelB.
      rewrite evalITrace_snoc_enq, Hhist, (MemoryImpl.enq_busy_true req impl Hb).
      split; [assumption | split; [assumption | split; [reflexivity | assumption]]].
    - apply busy_false in Hb as [Hi Hr].
      assert (Hnb: MemoryImpl.busy impl = false)
        by (unfold MemoryImpl.busy; rewrite Hi, Hr; reflexivity).
      destruct req.(mem_req_is_store) as [|] eqn:Hs.
      + (* write-through store: the abstraction commits it immediately too *)
        unfold RelB.
        split; [| split; [| split]].
        * rewrite array_set, mem_set_b, Harr; reflexivity.
        * unfold spec_resps.
          rewrite resp_addr_array_set, inflight_array_set, Hi, Hr.
          rewrite resps_mem_set, base_proj, Hres.
          unfold spec_resps. rewrite Hr, Hi. reflexivity.
        * rewrite evalITrace_snoc_enq, Hhist, (MemoryImpl.enq_store req impl Hnb Hs);
            reflexivity.
        * rewrite resp_addr_array_set, inflight_array_set; assumption.
      + (* load: the abstraction's response becomes consumable one Tick later *)
        unfold RelB.
        split; [| split; [| split]].
        * rewrite array_set_inflight, mem_resps_set, Harr; reflexivity.
        * unfold spec_resps.
          rewrite resp_set_inflight, Hr, inflight_set.
          rewrite resps_resps_set, resps_mem_set, base_proj, Hres.
          unfold spec_resps. rewrite Hr, Hi. cbn.
          unfold MemoryImpl.load_resp.
          rewrite array_set_inflight, Harr. reflexivity.
        * rewrite evalITrace_snoc_enq, Hhist, (MemoryImpl.enq_load req impl Hnb Hs);
            reflexivity.
        * right. rewrite resp_set_inflight, Hr; reflexivity.
  Qed.

  Lemma deq_sim (impl: MemoryImpl.St) (b: MemorySpec.base_st_t) (h: MemorySpec.trace_t) :
    RelB impl b h ->
    RelB (MemoryImpl.deq impl)
         (MemorySpec.deq (Build_st_t b h)) (h ++ [MemoryAPI.Deq]).
  Proof.
    intros [Harr [Hres [Hhist Hinv]]].
    pose proof (respReady_simB impl b h (conj Harr (conj Hres (conj Hhist Hinv)))) as Hrr.
    unfold MemorySpec.deq.
    destruct (MemoryImpl.resp_addr impl) as [a|] eqn:Hr.
    - assert (Hrt: MemoryImpl.respReady impl = true)
        by (unfold MemoryImpl.respReady; rewrite Hr; reflexivity).
      assert (Hst: MemorySpec.respReady (Build_st_t b h) = true)
        by (rewrite Hrr, Hrt; reflexivity).
      destruct Hinv as [Hi|Hi]; [ | congruence ].
      rewrite (MemoryImpl.deq_true impl Hrt), Hst.
      unfold RelB, spec_resps.
      split; [| split; [| split]].
      * rewrite array_set_resp, Harr, mem_resps_set; reflexivity.
      * rewrite resp_addr_set, inflight_set_resp, Hi.
        rewrite resps_resps_set, base_proj, Hres.
        unfold spec_resps. rewrite Hr. reflexivity.
      * rewrite evalITrace_snoc_deq, Hhist, (MemoryImpl.deq_true impl Hrt); reflexivity.
      * left; rewrite inflight_set_resp, Hi; reflexivity.
    - assert (Hrt: MemoryImpl.respReady impl = false)
        by (unfold MemoryImpl.respReady; rewrite Hr; reflexivity).
      assert (Hst: MemorySpec.respReady (Build_st_t b h) = false)
        by (rewrite Hrr, Hrt; reflexivity).
      unfold RelB.
      rewrite (MemoryImpl.deq_false impl Hrt), Hst, evalITrace_snoc_deq, Hhist,
              (MemoryImpl.deq_false impl Hrt).
      split; [| split; [| split]].
      * rewrite Harr; reflexivity.
      * assumption.
      * reflexivity.
      * right; assumption.
  Qed.

  Lemma tick_sim (impl: MemoryImpl.St) (b: MemorySpec.base_st_t) (h: MemorySpec.trace_t) :
    RelB impl b h ->
    RelB (MemoryImpl.tick impl)
         (MemorySpec.tick (Build_st_t b h)) (h ++ [MemoryAPI.Tick]).
  Proof.
    intros [Harr [Hres [Hhist Hinv]]].
    rewrite abs_tick.
    unfold MemoryImpl.tick.
    destruct (MemoryImpl.inflight impl) as [a|] eqn:Hi.
    - destruct Hinv as [Hbad|Hr]; [discriminate|].
      unfold RelB, spec_resps.
      split; [| split; [| split]].
      * rewrite array_set_tick, Harr; reflexivity.
      * rewrite resp_addr_set_tick.
        rewrite base_proj, Hres. unfold spec_resps. rewrite Hr, Hi.
        unfold MemoryImpl.load_resp.
        rewrite array_set_tick, Harr; reflexivity.
      * rewrite evalITrace_snoc_tick, Hhist, (MemoryImpl.tick_some impl a Hi); reflexivity.
      * left; reflexivity.
    - unfold RelB.
      rewrite evalITrace_snoc_tick, Hhist, (MemoryImpl.tick_none impl Hi).
      split; [| split; [| split]].
      * assumption.
      * assumption.
      * reflexivity.
      * left; assumption.
  Qed.

  Lemma refines :
    @Simulates.refines MemoryAPI.ValueMethod MemoryAPI.ActionMethod
                       impl_spec abs_spec Rel.
  Proof.
    cbv [Simulates.refines]. intros s1 [b h] Hrel.
    assert (Hb: RelB s1 b h) by (apply rel_relB; auto).
    split.
    - intros R vmethod; destruct vmethod; cbn.
      + symmetry; exact (respReady_simB s1 b h Hb).
      + symmetry; exact (full_simB s1 b h Hb).
      + symmetry; exact (peek_simB s1 b h Hb).
    - intros R method r s1' Heval; simplify_tupless.
      destruct method as [req| |].
      + cbn in Heval. inv Heval.
        exists (Build_st_t (MemorySpec.enq req (Build_st_t b h)) (h ++ [MemoryAPI.Enq req])).
        split; [reflexivity | apply rel_relB, enq_sim, Hb].
      + cbn in Heval. inv Heval.
        exists (Build_st_t (MemorySpec.deq (Build_st_t b h)) (h ++ [MemoryAPI.Deq])).
        split; [reflexivity | apply rel_relB, deq_sim, Hb].
      + cbn in Heval. inv Heval.
        exists (Build_st_t (MemorySpec.tick (Build_st_t b h)) (h ++ [MemoryAPI.Tick])).
        split; [reflexivity | apply rel_relB, tick_sim, Hb].
  Qed.

  (*! Main theorem: the implementation satisfies the memory model. *)
  Corollary simulates :
    @Simulates.simulates MemoryAPI.ValueMethod MemoryAPI.ActionMethod
                         impl_spec abs_spec.
  Proof.
    unfold Simulates.simulates. exists Rel. split; [apply Rel_init | apply refines].
  Qed.

  (*! The number of buffered responses is also a function of the control state,
      hence of the leakage trace alone. *)
  Definition dmem_pub_sim (impl spec: MemorySpec.st_t) : Prop :=
    MemorySpec.leakage (MemorySpec.hist impl) = MemorySpec.leakage (MemorySpec.hist spec) /\
    length impl.(MemorySpec.base).(MemorySpec.resps)
      = length spec.(MemorySpec.base).(MemorySpec.resps).

  (*! [DmemPubSim] component (cf. [isaSpec/PipelineRefines.v]): the number of
      buffered responses of the abstraction is determined by the
      implementation's state, hence by its leakage trace. *)
  Corollary dmem_pub_sim_resps (impl: MemoryImpl.St) (spec spec': MemorySpec.st_t) :
    Rel impl spec -> Rel impl spec' ->
    length spec.(MemorySpec.base).(MemorySpec.resps)
      = length spec'.(MemorySpec.base).(MemorySpec.resps).
  Proof.
    intros [H1 H2 H3 H4] [H1' H2' H3' H4']. rewrite H2, H2'. done.
  Qed.

  (*! The public behavior of the implementation is a function of its leakage
      trace alone: two traces with the same leakage put the module in the same
      control state, i.e. the response schedule never depends on store data or
      on memory contents. *)
  Corollary public_deterministic (tr1 tr2: MemorySpec.trace_t) :
    MemorySpec.leakage tr1 = MemorySpec.leakage tr2 ->
    MemoryImpl.ctrl (evalITrace tr1) = MemoryImpl.ctrl (evalITrace tr2).
  Proof.
    intros Hleak.
    rewrite (evalITrace_exec tr1), (evalITrace_exec tr2).
    rewrite <- (MemoryImpl.ctrl_exec_leakage init_mem tr1 (MemoryImpl.initial_st init_mem)),
            <- (MemoryImpl.ctrl_exec_leakage init_mem tr2 (MemoryImpl.initial_st init_mem)).
    rewrite Hleak. reflexivity.
  Qed.

  (*! The number of buffered responses is a function of the control state. *)
  Lemma length_spec_resps (st: MemoryImpl.St) :
    length (spec_resps st) =
      (match snd (ctrl st) with
       | Some _ => 1
       | None => match fst (ctrl st) with Some _ => 1 | None => 0 end
       end).
  Proof.
    unfold spec_resps, ctrl.
    destruct (resp_addr st) as [a|]; destruct (inflight st) as [i|]; reflexivity.
  Qed.

  Corollary public_resps_deterministic (tr1 tr2: MemorySpec.trace_t) :
    MemorySpec.leakage tr1 = MemorySpec.leakage tr2 ->
    length (spec_resps (evalITrace tr1)) = length (spec_resps (evalITrace tr2)).
  Proof.
    intros Hleak. rewrite !length_spec_resps.
    rewrite (public_deterministic tr1 tr2 Hleak). reflexivity.
  Qed.

End WithContext.
