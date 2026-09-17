(*! Memory implementation: the simplest memory system that satisfies
      [MemorySpec] -- no cache, write-through stores, one outstanding load,
      one-slot response buffer, fixed one-cycle load latency.

    The interface is exactly the one of [MemoryAPI] (the same action methods
    [Enq]/[Deq]/[Tick] and value methods [RespReady]/[Full]/[Peek] that
    [MemorySpec] speaks about), so the machine below can be substituted for
    [MemorySpec.spec] in the pipeline proofs.

    Crucially, everything that is observable -- [RespReady], [Full], and the
    *timing* of responses -- is a function of the module's leakage trace
    ([MemorySpec.LeakEnq]/[LeakDeq]/[LeakTick], which record only whether a
    request is a store and its address): store data and memory contents never
    influence the schedule.  This is proved as [ctrl_exec_leakage] below and is
    what makes the module usable in a confidentiality proof. *)
From stdpp Require Import base nmap.
From RecordUpdate Require Import RecordSet.
From granite.core Require Import
  Bits
  Utils
  Program
  Trace.
From granite.app Require Import
  MemoryAPI
  MemorySpec.
Import RecordSetNotations.

Section WithContext.
  Context {params: Params.Params}.
  Notation addr_t := N.
  Notation bv_addr_t := (bits Params.width).
  Notation data_t := (bits Params.width).

  (*! The state machine.  [array] is the memory contents, [inflight] is the
      address of a load that has been accepted but not served yet, and
      [resp_addr] is the address of a served load waiting to be dequeued.
      The response *data* is not stored: while a load is in flight or its
      response is pending, no further [Enq] is accepted, so the memory cannot
      change and the data can be read combinationally. *)
  #[projections(primitive=no)]
  Record St := {
    array : MemorySpec.memory_t;
    inflight : option bv_addr_t;
    resp_addr : option bv_addr_t
  }.
  Instance eta_St : Settable _ := settable! Build_St<array; inflight; resp_addr>.

  Definition initial_st (init_mem: MemorySpec.memory_t) : St :=
    {| array := init_mem; inflight := None; resp_addr := None |}.

  (* Everything except the memory contents; determined by the leakage trace. *)
  Definition ctrl (st: St) : (option bv_addr_t * option bv_addr_t) :=
    (st.(inflight), st.(resp_addr)).

  Definition busy (st: St) : bool :=
    is_some st.(inflight) || is_some st.(resp_addr).

  Definition full (st: St) : bool := busy st.

  Definition respReady (st: St) : bool := is_some st.(resp_addr).

  Definition load_resp (st: St) (a: bv_addr_t) : MemoryAPI.mem_resp_t :=
    {| mem_resp_addr := a;
       mem_resp_data := MemorySpec.mem_load st.(array) (to_N a) |}.

  (* [Peek] never gets stuck: when no response is available the junk value is
      read out of the (inert) memory array, and the abstract spec is given
      exactly the same junk value through [MemorySpec.SpecParams.default_peek]. *)
  Definition peek (st: St) : MemoryAPI.mem_resp_t :=
    load_resp st (option.default zeroes st.(resp_addr)).

  (* Write-through store: commits immediately and occupies no slot.  A load is
      accepted only when the module is idle. *)
  Definition enq (req: MemoryAPI.mem_req_t) (st: St) : St :=
    if busy st then st
    else
      if req.(mem_req_is_store) then
        st <| array := MemorySpec.mem_store st.(array)
                                       (to_N req.(mem_req_addr))
                                       req.(mem_req_data) |>
      else st <| inflight := Some req.(mem_req_addr) |>.

  Definition tick (st: St) : St :=
    match st.(inflight) with
    | Some a => st <| inflight := None |> <| resp_addr := Some a |>
    | None => st
    end.

  Definition deq (st: St) : St :=
    if respReady st then st <| resp_addr := None |> else st.

  Definition evalVMethod {A} (m: MemoryAPI.ValueMethod A) (st: St) : A :=
    match m with
    | RespReady => respReady st
    | Full => full st
    | Peek => peek st
    end.

  Definition evalAMethod {A} (m: MemoryAPI.ActionMethod A) (st: St) : A * St :=
    match m with
    | Enq req => ((), enq req st)
    | Deq => ((), deq st)
    | Tick => ((), tick st)
    end.

  Definition spec (init_mem: MemorySpec.memory_t) : Spec MemoryAPI.ValueMethod MemoryAPI.ActionMethod :=
    {| State := St;
       EvalVMethod A := evalVMethod;
       EvalMethod A := evalAMethod;
       initialState := initial_st init_mem
    |}.

  (*! Running the machine on a method trace. *)
  Definition exec (init_mem: MemorySpec.memory_t) (tr: MemorySpec.trace_t) (st: St) : St :=
    Trace.execTrace (spec init_mem) (map CallEvent tr) st.

  (*! Running the machine on a leakage trace: stores get dummy data. *)
  Definition lift_leakage_event (ev: MemorySpec.LeakEvent) : MemoryAPI.ActionMethod unit :=
    match ev with
    | MemorySpec.LeakEnq is_store a =>
        Enq {| mem_req_is_store := is_store;
               mem_req_addr := a;
               mem_req_data := zeroes |}
    | MemorySpec.LeakDeq => Deq
    | MemorySpec.LeakTick => Tick
    end.

  Definition execC (init_mem: MemorySpec.memory_t) (tr: MemorySpec.leakage_trace_t) (st: St) : St :=
    Trace.execTrace (spec init_mem) (map (fun ev => CallEvent (lift_leakage_event ev)) tr) st.

  (*! Control-state formulations of the observable value methods. *)
  Lemma respReady_ctrl (st: St) : respReady st = is_some (snd (ctrl st)).
  Proof. done. Qed.

  Lemma full_ctrl (st: St) : full st = (is_some (fst (ctrl st)) || is_some (snd (ctrl st))).
  Proof. done. Qed.

  Lemma busy_false (st: St) :
    busy st = false -> inflight st = None /\ resp_addr st = None.
  Proof.
    unfold busy in *.
    destruct (inflight st) as [i|]; cbn; try discriminate.
    destruct (resp_addr st) as [r|]; cbn; try discriminate.
    auto.
  Qed.

  (*! Method evaluation computes to the method functions. *)
  Lemma evalAMethod_enq (req: MemoryAPI.mem_req_t) (st: St) :
    snd (evalAMethod (MemoryAPI.Enq req) st) = enq req st.
  Proof. reflexivity. Qed.
  Lemma evalAMethod_deq (st: St) :
    snd (evalAMethod MemoryAPI.Deq st) = deq st.
  Proof. reflexivity. Qed.
  Lemma evalAMethod_tick (st: St) :
    snd (evalAMethod MemoryAPI.Tick st) = tick st.
  Proof. reflexivity. Qed.

  (*! One-step characterizations of the methods. *)
  Lemma enq_busy_true (req: MemoryAPI.mem_req_t) (st: St) :
    busy st = true -> enq req st = st.
  Proof. unfold enq; intros H; rewrite H; reflexivity. Qed.

  Lemma enq_store (req: MemoryAPI.mem_req_t) (st: St) :
    busy st = false -> mem_req_is_store req = true ->
    enq req st
      = st <| array := MemorySpec.mem_store (array st) (to_N (mem_req_addr req))
                                            (mem_req_data req) |>.
  Proof. unfold enq; intros H1 H2; rewrite H1, H2; reflexivity. Qed.

  Lemma enq_load (req: MemoryAPI.mem_req_t) (st: St) :
    busy st = false -> mem_req_is_store req = false ->
    enq req st = st <| inflight := Some (mem_req_addr req) |>.
  Proof. unfold enq; intros H1 H2; rewrite H1, H2; reflexivity. Qed.

  Lemma deq_true (st: St) : respReady st = true -> deq st = st <| resp_addr := None |>.
  Proof. unfold deq; intros H; rewrite H; reflexivity. Qed.

  Lemma deq_false (st: St) : respReady st = false -> deq st = st.
  Proof. unfold deq; intros H; rewrite H; reflexivity. Qed.

  Lemma tick_some (st: St) (a: bv_addr_t) :
    inflight st = Some a -> tick st = st <| inflight := None |> <| resp_addr := Some a |>.
  Proof. unfold tick; intros H; rewrite H; reflexivity. Qed.

  Lemma tick_none (st: St) : inflight st = None -> tick st = st.
  Proof. unfold tick; intros H; rewrite H; reflexivity. Qed.

  (*! The control automaton: what [ctrl] does on a leakage trace.  This is the
      abstract control-state machine of the memory, and it is what the
      abstraction's [resp_ready]/[is_full] end up depending on. *)
  Definition busy_c (c: option bv_addr_t * option bv_addr_t) : bool :=
    is_some (fst c) || is_some (snd c).

  Definition ctrl_enq_step (is_store: bool) (a: bv_addr_t)
               (c: option bv_addr_t * option bv_addr_t)
           : option bv_addr_t * option bv_addr_t :=
    if busy_c c then c else if is_store then c else (Some a, snd c).

  Fixpoint ctrl_of (tr: MemorySpec.leakage_trace_t)
                   (c: option bv_addr_t * option bv_addr_t)
               : option bv_addr_t * option bv_addr_t :=
    match tr with
    | [] => c
    | MemorySpec.LeakEnq is_store a :: tr' => ctrl_of tr' (ctrl_enq_step is_store a c)
    | MemorySpec.LeakDeq :: tr' =>
        ctrl_of tr' (if is_some (snd c) then (fst c, None) else c)
    | MemorySpec.LeakTick :: tr' =>
        ctrl_of tr' (match fst c with
                     | Some a => (None, Some a)
                     | None => c
                     end)
    end.

  Lemma busy_c_ctrl (st: St) : busy st = busy_c (ctrl st).
  Proof. done. Qed.

  Lemma ctrl_enq (req: MemoryAPI.mem_req_t) (st: St) :
    ctrl (enq req st) =
      ctrl_enq_step req.(mem_req_is_store) req.(mem_req_addr) (ctrl st).
  Proof.
    unfold enq, ctrl_enq_step.
    rewrite <- busy_c_ctrl.
    unfold ctrl.
    destruct (busy st); [reflexivity|].
    destruct (mem_req_is_store req); cbn; reflexivity.
  Qed.

  Lemma ctrl_deq (st: St) :
    ctrl (deq st) =
      (if is_some (snd (ctrl st)) then (fst (ctrl st), None) else ctrl st).
  Proof.
    unfold deq, respReady, ctrl.
    destruct (resp_addr st) eqn:Hr; cbn; rewrite ?Hr; cbn; reflexivity.
  Qed.

  Lemma ctrl_tick (st: St) :
    ctrl (tick st) =
      match fst (ctrl st) with
      | Some a => (None, Some a)
      | None => ctrl st
      end.
  Proof.
    unfold tick, ctrl.
    destruct (inflight st) eqn:Hi; cbn; rewrite ?Hi; cbn; reflexivity.
  Qed.

  Lemma ctrl_execC (init_mem: MemorySpec.memory_t) (L: MemorySpec.leakage_trace_t) :
    forall (st: St), ctrl (execC init_mem L st) = ctrl_of L (ctrl st).
  Proof.
    unfold execC.
    induction L as [| ev L IH]; intros st; simpl.
    { done. }
    destruct ev; simpl.
    - rewrite (IH (enq {| mem_req_is_store := isStore;
                          mem_req_addr := addr;
                          mem_req_data := zeroes |} st)),
              ctrl_enq. reflexivity.
    - rewrite (IH (deq st)), ctrl_deq. reflexivity.
    - rewrite (IH (tick st)), ctrl_tick. reflexivity.
  Qed.

  Lemma ctrl_exec (init_mem: MemorySpec.memory_t) (tr: MemorySpec.trace_t) :
    forall (st: St),
      ctrl (exec init_mem tr st) = ctrl_of (MemorySpec.leakage tr) (ctrl st).
  Proof.
    unfold exec, MemorySpec.leakage.
    induction tr as [| m tr IH] using list_ind; intros st; simpl.
    { done. }
    destruct m as [req| |]; simpl.
    - rewrite (IH (enq req st)), ctrl_enq. reflexivity.
    - rewrite (IH (deq st)), ctrl_deq. reflexivity.
    - rewrite (IH (tick st)), ctrl_tick. reflexivity.
  Qed.

  (*! The control state is a function of the leakage trace alone: this is the
      "no data-dependent timing" property of this implementation. *)
  Theorem ctrl_exec_leakage (init_mem: MemorySpec.memory_t) (tr: MemorySpec.trace_t) :
    forall (st: St),
      ctrl (execC init_mem (MemorySpec.leakage tr) st) = ctrl (exec init_mem tr st).
  Proof.
    intros st.
    rewrite ctrl_execC, ctrl_exec. done.
  Qed.
End WithContext.
