From stdpp Require Import base tactics finite strings vector.
From granite.core Require Import Bits.
From granite.core Require Import
  Object
  Array
  Pair
  Program
  ProgramOps
  Reg
  Simulates
  Tactics
  Utils.
From granite.app Require Import
  RfScored.
From quartz.lang Require Import
  Syntax
  domain.
From quartz.examples Require Import Processor.
From granite.isaSpec Require Import QuartzLib.
Import InterfaceExample.
(* Import ZmodDef. *)
(* Import ZmodBase. *)
(* Import Bits. *)
(* Import (coercions) domain.Zmod. *)
(* Coercion  {n: N} {z: Z} (b: bv n) : bits z := *)
(*   bits.of_Z _ (bv_unsigned b). *)
(* Coercion bits_to_bv {z: Z} {n: N} (b: bits z) : bv n := *)
(*   Z_to_bv _ (Zmod.unsigned b). *)
Import domain.Zmod.
(* TODO: dependent types are annoying *)
Notation log_nregs  := 5%Z.

Section WithContext.
  Context {Val: Type} {initVal: Val}.
  Context {val: type}.
  Context (lift: type.interp val -> Val).
  Context (lower : Val -> type.interp val).
  Context {lift_lower_cancel: Cancel eq lift lower}.
  Context {lower_lift_cancel: Cancel eq lower lift}.
  (* Default of type.interp val corresponds to initVal *)
  Context {lift_initVal: initVal = lift (default val )}.
  (* Context {log_nregs: N}. *)

  Let lnr : Z := log_nregs.
  Notation idx_t := (bits log_nregs) (only parsing).

  (* ------------------------------------------------------------------ *)
  (* nregs equality: same number of entries in quartz and concrete specs  *)
  (* ------------------------------------------------------------------ *)

  Lemma nregs_eq : @rfScored.nregs lnr = @RfScored.nregs log_nregs _ _.
  Proof. vm_compute; reflexivity. Qed.

  Notation nr := (@rfScored.nregs lnr).

  (* Quartz state:    vec (bits 1 * type.interp val) nr *)
  Notation qst := (rfScored.state' val nr).
  (* Concrete state:  vec (bv 1 * Val) nr               *)
  Notation rfs_abs_spec := 
    (RfScored.rfScoredSpec (Val := Val) (initVal := initVal) (log_nregs := log_nregs)).

  Notation cst := (vec ((bits 1) * Val) nr) (only parsing).

  (* ------------------------------------------------------------------ *)
  (* Entry-wise correspondence                                            *)
  (* ------------------------------------------------------------------ *)

  Definition raise_entry (e : bits 1 * Val) : bits 1 * type.interp val :=
    (e.1, lower e.2).

  Definition lower_entry (e : bits 1 * type.interp val) : bits 1 * Val :=
    (e.1, lift e.2).
Set Printing Coercions.
  Lemma lower_raise_cancel (e : bits 1 * Val) :
    lower_entry (raise_entry e) = e.
  Proof.
    unfold lower_entry, raise_entry; cbn.
    rewrite lift_lower_cancel. destruct e; try reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* State correspondence                                                 *)
  (* ------------------------------------------------------------------ *)

  Definition raise_st (cs : cst) : qst := vmap raise_entry cs.
  Definition lower_st (qs : qst) : cst := vmap lower_entry qs.

  Lemma lower_raise_st (cs : cst) : lower_st (raise_st cs) = cs.
  Proof.
    unfold lower_st, raise_st.
    rewrite Vector.map_map.
    erewrite VectorSpec.map_ext; [ apply Vector.map_id | ].
    intros. apply lower_raise_cancel.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Key helper lemmas: connecting Quartz array access to vlookup         *)
  (* ------------------------------------------------------------------ *)

  (* nth_default at a fin index equals vlookup *)
  Lemma nth_default_vlookup {A n} (v : vec A n) (i : fin n) (d : A) :
    List.nth_default d (Vector.to_list v) (fin_to_nat i) = v !!! i.
  Proof.
    revert i. induction v as [|a n v IH]; intros i; inv_fin i; simpl.
    - reflexivity.
    - intro i. apply IH.
  Qed.

  (* Zmod.unsigned of  equals bv_unsigned *)
  (* Lemma bits_unsigned_bv (idx : idx_t) : *)
  (*   Zmod.unsigned (bits.of_Z lnr (bv_unsigned idx)) = bv_unsigned idx. *)
  (* Proof. *)
  (*   rewrite bits.unsigned_of_Z, Z.mod_small; [reflexivity|]. *)
  (*   unfold lnr. exact (bv_unsigned_in_range log_nregs idx). *)
  (* Qed. *)

  (* Combined: nth_default at a bv index equals vlookup at encode_fin *)
  (* Lemma nth_default_vlookup_bv {A} (v : vec A nr) (d : A) (idx : idx_t) : *)
  (*   v !!! encode_fin idx =  *)
  (*   List.nth_default d (Vector.to_list v) (Z.to_nat (bv_unsigned idx)). *)
  (* Proof. *)
  (*   rewrite <- fin_to_nat_encode_fin_bv. apply nth_default_vlookup. *)
  (* Qed. *)

  (* Vector.upd at a fin position equals vinsert *)
  Lemma vec_upd_eq_vinsert {A n} (v : vec A n) (i : fin n) (f : A -> A) :
    Vector.upd v (fin_to_nat i) f = vinsert i (f (v !!! i)) v.
  Proof.
    revert i. induction v as [|a n v IH]; intros i; inv_fin i; simpl.
    - reflexivity.
    - intro i. rewrite IH. reflexivity.
  Qed.

  (* Vector.upd at a bv index equals vinsert at encode_fin *)
  (* Lemma vec_upd_eq_vinsert_bv {A} (v : vec A nr) (f : A -> A) (idx : idx_t) : *)
  (*   Vector.upd v (Z.to_nat (bv_unsigned idx)) f = *)
  (*   vinsert (encode_fin idx) (f (v !!! encode_fin idx)) v. *)
  (* Proof. *)
  (*   rewrite <- fin_to_nat_encode_fin_bv. apply vec_upd_eq_vinsert. *)
  (* Qed. *)

  (* ------------------------------------------------------------------ *)
  (* Quartz spec: wraps fn.interp of rfScored.impl operations             *)
  (* ------------------------------------------------------------------ *)

  Definition evalVMet {R} (m : RfScored.ValueMethod (log_nregs := log_nregs) (Val := Val) R) (qs : qst) : R :=
    match m with
    | RfScored.Read idx =>
        lift (fn.interp (RfScored.read (rfScored.impl _ ) (log_nregs := lnr)) 
                        (qs, idx))
    | RfScored.IsLocked idx =>
        (fn.interp (RfScored.isLocked (rfScored.impl _) (log_nregs := lnr) )
                                (qs, idx))
    end.

  Definition evalAMet {R} (m : RfScored.ActionMethod (log_nregs := log_nregs) (Val := Val) R) (qs : qst)
                      : R * qst :=
    match m with
    | RfScored.AcquireLock idx =>
        ((), fn.interp (RfScored.acquireLock (rfScored.impl _) (log_nregs := lnr) )
                       (qs,  idx))
    | RfScored.ReleaseLock idx =>
        ((), fn.interp (RfScored.releaseLock (rfScored.impl _) (log_nregs := lnr) )
                       (qs,  idx))
    | RfScored.WriteAndRelease idx v =>
        ((), fn.interp (RfScored.writeAndRelease (rfScored.impl _) (log_nregs := lnr) )
                       (qs, (( idx), lower v)))
    end.
  Notation bit := (bits 1).
  Definition rfs_qspec : Spec (RfScored.ValueMethod (Val := Val))
                               (RfScored.ActionMethod (Val := Val)) :=
    {| State := qst;
       EvalVMethod {A} := evalVMet;
       EvalMethod {A} := evalAMet;
       initialState := default (Array (Pair Bool val) nr)
    |}.

  (* ------------------------------------------------------------------ *)
  (* Simulation relation: lower_st maps quartz state to concrete state    *)
  (* ------------------------------------------------------------------ *)

  Definition Rel (qs : qst) (cs : cst) : Prop :=
    (forall idx, (lower_st qs) !!! idx = cs !!! idx).

  Lemma lookup_default_array :
    forall f t n idx,
    default_array f t n !!! idx = f t.
  Proof.
    intros. induction n; inv_fin idx; [reflexivity | intro i; apply IHn].
  Qed.
  Lemma Rel_init : Rel (initialState rfs_qspec) (initialState rfs_abs_spec).
  Proof.
    unfold Rel, lower_st. cbn.
    intros.
    rewrite vlookup_map.
    rewrite (lookup_default_array default (Pair (Bits 1) val)).
    rewrite lookup_fun_to_vec.
    unfold lower_entry.
    simpl. rewrite lift_initVal. 
    autorewrite with bits. 
    f_equal. 
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Key index lemma: fin_to_nat (encode_fin idx) = Z.to_nat (bv_unsigned idx) *)
  (* NOTE: This requires the Countable instance for bv to be finite_countable  *)
  (* (priority 100) not bv_countable (priority 10). Currently bv_countable     *)
  (* takes priority, making this lemma FALSE. Fix: change priority or use      *)
  (* nat_to_fin in RfScored.v's Lookup definition.                             *)
  (* ------------------------------------------------------------------ *)
  Lemma fin_to_nat_encode_fin_bv (idx : idx_t) :
    fin_to_nat (encode_fin idx) = Z.to_nat (Zmod.unsigned idx).
  Proof. apply fin_to_nat_encode_fin_Zmod; lia. Qed.
  (* Lemma bv_unsigned_lt_nr (idx : idx_t) : (Z.to_nat (bv_unsigned idx) < nr)%nat. *)
  (* Proof. *)
  (*   unfold nr, rfScored.nregs. *)
  (*   pose proof bv_unsigned_in_range log_nregs idx as [Hlo Hhi]. *)
  (*   pose proof Z2Nat.inj_lt (bv_unsigned idx) (bv_modulus log_nregs) Hlo *)
  (*     ltac:(unfold bv_modulus; lia) as [H _]. *)
  (*   apply H. exact Hhi. *)
  (* Qed. *)

  (* Helper: Vector.upd at nat index = vinsert at corresponding fin index *)
  (* Lemma vec_upd_eq_vinsert {A n} (v : vec A n) (i : fin n) (f : A -> A) : *)
  (*   Vector.upd v (fin_to_nat i) f = vinsert i (f (v !!! i)) v. *)
  (* Proof. *)
  (*   revert i. induction v as [|a n v IH]; intros i; inv_fin i; simpl. *)
  (*   - reflexivity. *)
  (*   - intro i. rewrite IH. reflexivity. *)
  (* Qed. *)

  (* Helper: lower_st distributes over vinsert *)
  Lemma lower_st_vinsert (qs : qst) (i : fin nr) (e : bits 1 * type.interp val) :
    lower_st (vinsert i e qs) = vinsert i (lower_entry e) (lower_st qs).
  Proof. unfold lower_st. apply vmap_insert. Qed.
(* Opaque Zmod.of_Z. *)

  (* Helper: Rel implies lower_st qs = cs pointwise (i.e., as equal vectors) *)
(*   Lemma Rel_lower_eq (qs : qst) (cs : cst) :  *)
(*     Rel qs cs -> lower_st qs = cs. *)
(*   Proof. intros HRel. *)
         
(*         Search Vector.t.  *)
(* apply vlookup_ext. intro i. apply HRel. Qed. *)
  Import eexpr.
  (* Helper: Quartz acquireLock computes as a vector update *)
  Lemma qtz_acquireLock_eq (qs : qst) (idx : idx_t) :
    fn.interp (RfScored.acquireLock (rfScored.impl (log_nregs := lnr) val)) (qs,  idx) =
    Vector.upd qs (Z.to_nat (Zmod.unsigned idx))
               (fun _ => (embed_bool true,
                          (nth_default (default (Pair Bool val)) (Vector.to_list qs)
                                       (Z.to_nat (Zmod.unsigned idx))).2)).
  Proof.
    reflexivity.
  Qed.

  Lemma qtz_releaseLock_eq (qs : qst) (idx : idx_t) :
    fn.interp (RfScored.releaseLock (rfScored.impl (log_nregs := lnr) val)) (qs,  idx) =
    Vector.upd qs (Z.to_nat (Zmod.unsigned idx))
               (fun _ => (embed_bool false,
                          (nth_default (default (Pair Bool val)) (Vector.to_list qs)
                                       (Z.to_nat (Zmod.unsigned idx))).2)).
  Proof.
    reflexivity.
  Qed.

  Lemma qtz_writeAndRelease_eq (qs : qst) (idx : idx_t) (v : type.interp val) :
    fn.interp (RfScored.writeAndRelease (rfScored.impl (log_nregs := lnr) val)) (qs, ( idx, v)) =
    if nonzero (nth_default (default (Pair Bool val)) (Vector.to_list qs)
                                 (Z.to_nat (Zmod.unsigned idx))).1
    then Vector.upd qs (Z.to_nat (Zmod.unsigned idx))
                    (fun _ => (embed_bool false, v))
    else qs.
  Proof.
    cbn [fn.interp fn.body RfScored.writeAndRelease rfScored.impl].
    reflexivity.
  Qed.

  (* Helper: abstract acquireLock result *)
  Lemma abs_acquireLock_eq (cs : cst) (idx : idx_t) :
    EvalMethod rfs_abs_spec (AcquireLock idx) cs =
    ((), vinsert (encode_fin idx) (embed_bool true, (cs !!! encode_fin idx).2) cs).
  Proof.
    cbn. 
    match goal with
    | |- context[?x !!! ?y] => destruct (x !!! y) as [b v] eqn:H
    end.
    simpl in *. 
    reflexivity.
  Qed.

  Lemma abs_releaseLock_eq (cs : cst) (idx : idx_t) :
    EvalMethod rfs_abs_spec (ReleaseLock idx) cs =
    ((), vinsert (encode_fin idx) (embed_bool false, (cs !!! encode_fin idx).2) cs).
  Proof.
    cbn. 
    match goal with
    | |- context[?x !!! ?y] => destruct (x !!! y) as [b v] eqn:H
    end. simpl. reflexivity.
  Qed.

  Lemma abs_writeAndRelease_eq (cs : cst) (idx : idx_t) (v : Val) :
    EvalMethod rfs_abs_spec (WriteAndRelease idx v) cs =
    if nonzero ((cs !!! encode_fin idx).1) 
    then ((), vinsert (encode_fin idx) (embed_bool false, v) cs)
    else ((), cs).
  Proof.
    cbn. 
    match goal with
    | |- context[?x !!! ?y] => destruct (x !!! y) as [b z] eqn:H
    end. simpl. 
    case_goal_match; simpl; auto.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Key helper: Rel implies same entry at encode_fin idx                 *)
  (* ------------------------------------------------------------------ *)

  Lemma Rel_entry (qs : qst) (cs : cst) (idx : idx_t) :
    Rel qs cs ->
    lower_entry (qs !!! encode_fin idx) = cs !!! encode_fin idx.
  Proof.
    intros HRel. pose proof HRel (encode_fin idx) as H.
    unfold lower_st in H. rewrite vlookup_map in H. exact H.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Key Quartz fn.interp unfolding lemma for rfScored array access       *)
  (* ------------------------------------------------------------------ *)
  (* Helper: Quartz array access on a vmap-raised state gives lower of vlookup *)
  (* NOTE: Requires fin_to_nat_encode_fin_bv AND raise_entry ∘ lower_entry = id
     (which needs lower ∘ lift = id, stronger than lift_lower_cancel). *)
  (* Lemma embed_bool_nonzero: *)
  (*   forall b,  *)
  (*   embed_bv 1 (nonzero b) = b. *)
  (* Proof. *)
  (*   unfold nonzero, embed_bv 1. *)
  (*   intros. apply bv_eq. *)
  (*   destruct (bv 1_cases b) eqn:?; auto. *)
  (* Qed. *)

  Lemma rfScored_get_entry (qs : qst) (cs : cst) (idx : idx_t) :
    Rel qs cs ->
    List.nth_default (default (Pair (Bits 1) val)) (Vector.to_list qs) (Z.to_nat (Zmod.unsigned idx)) =
    raise_entry (cs !!! encode_fin idx).
  Proof.
    simpl.
    rewrite<-fin_to_nat_encode_fin_bv.
    rewrite nth_default_vlookup.
    intros hrel.
    unfold raise_entry. 
    rewrite<-hrel. simpl.
    unfold lower_st.
    rewrite vlookup_map. simpl.
    rewrite lower_lift_cancel.
    match goal with
    | |- context[?x !!! ?y] => destruct (x !!! y)
    end. simpl.
    f_equal. 
  Qed.
  Lemma bool_to_Z_zero:
    forall b,
    (Z.b2z (b =? 0) =? 0)%Z = negb (b =? 0)%Z.
  Proof.
    intros. destruct (Z.eqb_spec b 0); try reflexivity.
  Qed.
  (* ------------------------------------------------------------------ *)
  (* Main simulation theorem                                              *)
  (* ------------------------------------------------------------------ *)
  Lemma read_ok (qs : qst) (cs : cst) (idx : idx_t) :
    Rel qs cs ->
    EvalVMethod rfs_qspec (Read idx) qs = EvalVMethod rfs_abs_spec (Read idx) cs.
  Proof.
    intros hrel. 
    unfold read. simpl. unfold LetBlock, nonzero, Zmod.eqb.
    rewrite unsigned_embed_bool, Zmod.unsigned_0.
    rewrite rfScored_get_entry with (1 := hrel). 
    unfold raise_entry. cbn. 
    unfold read.
    rewrite bool_to_Z_zero. rewrite negb_involutive.
    match goal with
    | |- context[Z.eqb ?x 0%Z] => destruct (Z.eqb_spec x 0%Z)
    end.
    - case_decide; subst; auto.
      exfalso. apply H. apply Zmod.unsigned_inj. auto.
    - case_decide; simpl; subst.
      + rewrite ?unsigned_literal in *; congruence.
      + rewrite lift_lower_cancel. 
        match goal with
        | |- context[?x !!! ?y] => destruct (x !!! y)
        end. reflexivity.
  Qed.

  Lemma isLocked_ok (qs : qst) (cs : cst) (idx : idx_t) :
    Rel qs cs ->
    EvalVMethod rfs_qspec (IsLocked idx) qs =
    EvalVMethod rfs_abs_spec (IsLocked idx) cs.
  Proof.
    intros hrel. 
    unfold read. simpl. unfold LetBlock, nonzero.
    (* rewrite bv 1_to_bv_unsigned. bits_unsigned_bv. *)
    rewrite rfScored_get_entry with (1 := hrel). 
    unfold Rel in hrel.
    unfold raise_entry. cbn. 
    match goal with
    | |- context[?x !!! ?y] => destruct (x !!! y)
    end. 
    simpl.
    destruct z; reflexivity.
  Qed.

  (* Core: after updating same index, Rel is preserved *)
  Lemma Rel_insert (qs : qst) (cs : cst) (idx : idx_t)
      (qe : bits 1 * type.interp val) (ce : bits 1 * Val) :
    Rel qs cs ->
    lower_entry qe = ce ->
    Rel (vinsert (encode_fin idx) qe qs) (vinsert (encode_fin idx) ce cs).
  Proof.
    intros HRel Hle i.
    unfold lower_st. rewrite vmap_insert. 
    subst. 
    match goal with
    | |- context[vinsert ?x _ _ !!! ?y] =>
        destruct (decide (x = y)) as [-> | Hne]
    end.
    - rewrite !vlookup_insert. reflexivity. 
    - rewrite !vlookup_insert_ne by exact Hne. apply HRel.
  Qed.

  (* Helper: convert Quartz upd to vinsert via fin_to_nat_encode_fin_bv *)
  Lemma qtz_upd_to_vinsert (qs : qst) (idx : idx_t)
      (f : bits 1 * type.interp val -> bits 1 * type.interp val) :
    Vector.upd qs (Z.to_nat (Zmod.unsigned idx)) f =
    vinsert (encode_fin idx) (f (qs !!! encode_fin idx)) qs.
  Proof.
    rewrite <- fin_to_nat_encode_fin_bv. apply vec_upd_eq_vinsert.
  Qed.
  Lemma embed_bool_false :
    embed_bool false = 0%Zmod.
  Proof.
    apply Zmod.unsigned_inj. reflexivity.
  Qed.
  Lemma embed_bool_true:
    embed_bool true = 1%Zmod.
  Proof.
    apply Zmod.unsigned_inj. reflexivity.
  Qed.

  Lemma acquireLock_ok (qs qs' : qst) (cs cs' : cst) (idx : idx_t) :
    Rel qs cs ->
    EvalMethod rfs_qspec (AcquireLock idx) qs = ((), qs') ->
    EvalMethod rfs_abs_spec (AcquireLock idx) cs = ((), cs') ->
    Rel qs' cs'.
  Proof.
    intros HRel Hqs' Hcs'.
    (* Extract qs' from Quartz computation *)
    cbn [rfs_qspec EvalMethod evalAMet] in Hqs'.
    rewrite qtz_acquireLock_eq in Hqs'.
    injection Hqs' as Hqs'.
    (* Replace nth_default with vlookup via fin_to_nat_encode_fin_bv *)
    rewrite <- fin_to_nat_encode_fin_bv, nth_default_vlookup in Hqs'.
    rewrite abs_acquireLock_eq in Hcs'. injection Hcs' as Hcs'. subst cs'.
    rewrite fin_to_nat_encode_fin_bv in Hqs'.
    rewrite qtz_upd_to_vinsert in Hqs'. subst qs'.
    (* Extract cs' from abstract computation *)
    (* Now show Rel *)
    apply Rel_insert; [exact HRel |].
    unfold lower_entry. cbn. rewrite embed_bool_true.
    f_equal. 
    erewrite<-Rel_entry; eauto.
  Qed.

  Lemma releaseLock_ok (qs qs' : qst) (cs cs' : cst) (idx : idx_t) :
    Rel qs cs ->
    EvalMethod rfs_qspec (ReleaseLock idx) qs = ((), qs') ->
    EvalMethod rfs_abs_spec (ReleaseLock idx) cs = ((), cs') ->
    Rel qs' cs'.
  Proof.
    intros HRel Hqs' Hcs'.
    (* Extract qs' from Quartz computation *)
    cbn [rfs_qspec EvalMethod evalAMet] in Hqs'.
    rewrite qtz_releaseLock_eq in Hqs'.
    injection Hqs' as Hqs'.
    rewrite qtz_upd_to_vinsert in Hqs'. subst qs'.
    rewrite abs_releaseLock_eq in Hcs'. injection Hcs' as Hcs'. subst cs'.
    apply Rel_insert; [exact HRel |].
    rewrite<-fin_to_nat_encode_fin_bv. 
    rewrite nth_default_vlookup.
    erewrite<-Rel_entry; eauto.
  Qed.

  Lemma writeAndReleaseLock_ok (qs qs' : qst) (cs cs' : cst) (idx : idx_t) v:
    Rel qs cs ->
    EvalMethod rfs_qspec (WriteAndRelease idx v) qs = ((), qs') ->
    EvalMethod rfs_abs_spec (WriteAndRelease idx v) cs = ((), cs') ->
    Rel qs' cs'.
  Proof.
    intros HRel Hqs' Hcs'.
    (* Extract qs' from Quartz computation *)
    cbn [rfs_qspec EvalMethod evalAMet] in Hqs'.
    rewrite qtz_writeAndRelease_eq in Hqs'.
    injection Hqs' as Hqs'.
    rewrite qtz_upd_to_vinsert in Hqs'. subst qs'.
    rewrite abs_writeAndRelease_eq in Hcs'. 
    rewrite<-fin_to_nat_encode_fin_bv. 
    rewrite nth_default_vlookup.
    erewrite<-Rel_entry in Hcs'; eauto.
    cbv[lower_entry] in *. cbn in *.
    cbn.
    case_goal_match.
    - setoid_rewrite Heqb in Hcs'. simplify_tupless.
      eapply Rel_insert; auto.
      cbv[lower_entry]. simpl.
      rewrite lift_lower_cancel.
      done.
    - setoid_rewrite Heqb in Hcs'. simplify_tupless.
      auto.
  Qed.
  Opaque rfs_qspec.
  Opaque RfScored.rfScoredSpec.

  Theorem refines_rfs : Simulates.refines rfs_qspec rfs_abs_spec Rel.
  Proof.
    cbv [Simulates.refines]. intros qs cs HRel.
    split.
    - (* Value methods agree *)
      destruct vmethod. simpl.
      + apply read_ok. exact HRel.
      + apply isLocked_ok. exact HRel.
    - (* Action methods agree and preserve Rel *)
      intros R method qs' r Hmeth. destruct method; cbn in *.
      + (* AcquireLock *)
        destruct (EvalMethod rfs_abs_spec (AcquireLock idx) cs) as [u s2'] eqn:Hspec.
        destruct qs'. destruct u.
        eexists. split; [reflexivity|].
        apply acquireLock_ok with (1 := HRel) (2 := Hmeth) (3 := Hspec). 
      + (* ReleaseLock *)
        destruct (EvalMethod rfs_abs_spec (ReleaseLock idx) cs) as [u s2'] eqn:Hspec.
        destruct qs'. destruct u.
        eexists. split; [reflexivity|].
        apply releaseLock_ok with (1 := HRel) (2 := Hmeth) (3 := Hspec). 
      + (* WriteAndRelease *)
        destruct (EvalMethod rfs_abs_spec (WriteAndRelease idx value) cs) as [u s2'] eqn:Hspec.
        destruct qs'. destruct u.
        eexists. split; [reflexivity|].
        apply writeAndReleaseLock_ok with (1 := HRel) (2 := Hmeth) (3 := Hspec). 
  Qed.

  Corollary simulates_rfs : Simulates.simulates rfs_qspec rfs_abs_spec.
  Proof.
    unfold Simulates.simulates. exists Rel.
    split; [apply Rel_init | apply refines_rfs].
  Qed.

End WithContext.
