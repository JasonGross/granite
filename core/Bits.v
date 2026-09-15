From stdpp Require Export numbers.
From stdpp Require Import finite list_numbers.
From Stdlib Require Export ZArith Bits.
From Stdlib Require Import Lia.
From Stdlib Require Import String.
From quartz.lang Require domain.

Notation bits n := (Zmod (2 ^ n)%Z).

Global Arguments Zmod.unsigned : simpl never.
Global Arguments Zmod.signed : simpl never.
Global Opaque Zmod.of_small_Z.

Class ZmodLiteralWf (m z : Z) : Prop :=
  zmod_literal_wf : ltac:(let t := type of (Zmod.mk m z) in lazymatch t with ?A -> _ => exact A end).
Global Hint Extern 0 (ZmodLiteralWf _ _) => (vm_compute; exact I) : typeclass_instances.
Definition bits_literal (m z : Z) {pf : ZmodLiteralWf m z} : Zmod m := Zmod.mk m z pf.
Global Instance zmod_literal_wf_0 m : ZmodLiteralWf m 0.
Proof. unfold ZmodLiteralWf. rewrite <-(Zmod.unsigned_0 m). exact (Zmod.Private_range _ Zmod.zero). Qed.

Inductive zmod_literal := ZmodLiteral (z : Z) | ZmodLiteralNeg (z : Z).
Definition zmod_literal_to_Z (l : zmod_literal) : option Z :=
  match l with ZmodLiteral z => Some z | ZmodLiteralNeg _ => None end.
Definition Z_to_zmod_literal (z : Z) : zmod_literal :=
  match z with Zneg _ => ZmodLiteralNeg z | _ => ZmodLiteral z end.
Local Arguments bits_literal {_} _ {_}.
Local Arguments Zmod.of_Z {_} _.
Number Notation Zmod Z_to_zmod_literal zmod_literal_to_Z
  (via zmod_literal mapping [[bits_literal] => ZmodLiteral, [Zmod.of_Z] => ZmodLiteralNeg]) : Zmod_scope.
Local Arguments bits_literal _ _ {_}.
Local Arguments Zmod.of_Z : clear implicits.
Notation "0" := (bits_literal _ 0%Z) : Zmod_scope.
Notation "1" := (bits_literal _ 1%Z) : Zmod_scope.

Global Instance Zmod_eq_dec m : EqDecision (Zmod m).
Proof.
  intros x y. destruct (decide (Zmod.unsigned x = Zmod.unsigned y)) as [H|H];
    [left; exact (Zmod.unsigned_inj _ _ _ H) | right; congruence].
Defined.
Global Instance Zmod_countable m : Countable (Zmod m) :=
  inj_countable Zmod.unsigned (fun z => Some (Zmod.of_Z m z))
    (fun x => f_equal Some (Zmod.of_Z_unsigned x)).
Global Instance Zmod_inhabited m : Inhabited (Zmod m) := populate Zmod.zero.
Definition Zmod_finite m (Hm : (m <> 0)%Z) : Finite (Zmod m).
Proof.
  refine {| enum := Zmod.elements m |}.
  - apply NoDup_ListNoDup, Zmod.NoDup_elements.
  - intros x. apply list_elem_of_In, Zmod.in_elements, Hm.
Defined.
Global Instance bits_finite n {Hn : (0 <=? n)%Z = true} : Finite (bits n) :=
  Zmod_finite (2 ^ n) (Z.pow_nonzero 2 n ltac:(discriminate) (proj1 (Z.leb_le 0 n) Hn)).
Global Hint Extern 0 ((0 <=? _)%Z = true) => exact eq_refl : typeclass_instances.

Lemma list_lookup_nth_error {A} (l : list A) i : l !! i = nth_error l i.
Proof. revert i; induction l; destruct i; cbn; auto. Qed.

Lemma fin_to_nat_encode_fin_Zmod m {Hm : (m <> 0)%Z} (x : Zmod m) (Hpos : (0 < m)%Z) :
  fin_to_nat (@encode_fin _ _ (Zmod_finite m Hm) x) = Z.to_nat (Zmod.unsigned x).
Proof.
  unfold encode_fin. rewrite fin_to_nat_to_fin.
  pose proof (Zmod.unsigned_pos_bound x Hpos) as Hrange.
  assert (Hfwd : @enum (Zmod m) _ (Zmod_finite m Hm) !! Z.to_nat (Zmod.unsigned x) = Some x).
  { cbn [enum Zmod_finite]. rewrite list_lookup_nth_error, Zmod.nth_error_elements.
    destruct (Nat.ltb_spec (Z.to_nat (Zmod.unsigned x)) (Z.abs_nat m)); [|lia].
    rewrite Z2Nat.id by lia. f_equal. apply Zmod.of_Z_unsigned. }
  refine (NoDup_lookup _ _ _ _ (@NoDup_enum _ _ (Zmod_finite m Hm)) _ Hfwd).
  assert (H := @decode_encode_nat (Zmod m) _ (@finite_countable _ _ (Zmod_finite m Hm)) x).
  unfold decode_nat, decode, finite_countable in H.
  rewrite Nat2Pos.id in H by lia.
  cbn [Init.Nat.pred] in *. auto.
Qed.

Definition of_N n nn : bits n := bits.of_Z _ (Z.of_N nn).
Definition of_nat n nn : bits n := bits.of_Z _ (Z.of_nat nn).

Definition to_N [n] (w : bits n) : N := Z.to_N (Zmod.unsigned w).
Definition to_nat [n] (w : bits n) := Z.to_nat (Zmod.unsigned w).

Notation zeroes := (bits_literal _ 0%Z).
Lemma unsigned_literal m z pf : Zmod.unsigned (@bits_literal m z pf) = z.
Proof. reflexivity. Qed.
Lemma zeroes_zero m : (zeroes : Zmod m) = Zmod.zero.
Proof. apply Zmod.unsigned_inj. rewrite Zmod.unsigned_0. reflexivity. Qed.

Definition update_slice {m n} (w : bits m) i (v : bits n) : bits m :=
  Zmod.firstn m (Zmod.app (Zmod.firstn i w) (Zmod.app v (Zmod.skipn (i + n) w))).
Definition set_bit [n] (w : bits n) i b : bits n := update_slice w i (domain.Zmod.embed_bool b).

Definition bits_to_Z (l: list bool) := Z.of_N (Ascii.N_of_digits l).
Definition bits_to_word (l : list bool) : bits (Z.of_nat (List.length l)) :=
  bits.of_Z (Z.of_nat (List.length l)) (bits_to_Z l).

Definition bv_to_binary_string [n] (w : bits n) : String.string :=
  let bits := List.rev (map (Z.testbit (Zmod.unsigned w)) (seqZ 0 n)) in
  let digits := List.map (fun b : bool => if b then "1" else "0")%string bits in
  String.concat "" digits.

Declare Scope list_bits.
Delimit Scope list_bits with bits.

Notation "'1'" := [true] : list_bits.
Notation "'0'" := [false] : list_bits.
Notation "bs '~' '0'" := (cons false bs) (at level 7, left associativity) : list_bits.
Notation "bs '~' '1'" := (cons true bs) (at level 7, left associativity) : list_bits.
Notation "'Ob' '~' number" :=
  (bits_to_word number) (at level 99) : list_bits.

Notation mk_bit := domain.Zmod.embed_bool.

Definition bits_to_little_endian (m n z : Z) : list (bits n) :=
  map (Zmod.of_Z (2 ^ n)) (Z_to_little_endian m n z).
Definition little_endian_to_bits (n : Z) (bs : list (bits n)) : Z :=
  little_endian_to_Z n (map Zmod.unsigned bs).
Lemma length_bits_to_little_endian (m n z : Z) :
  (0 <= m)%Z -> List.length (bits_to_little_endian m n z) = Z.to_nat m.
Proof. intros H. unfold bits_to_little_endian. rewrite length_map. pose proof (length_Z_to_little_endian m n z H). lia. Qed.

Definition bv_mul' {m1 m2} n (x1 : bits m1) (x2 : bits m2) : bits n :=
  bits.of_Z n (Z.mul (Zmod.unsigned x1) (Zmod.unsigned x2)).
