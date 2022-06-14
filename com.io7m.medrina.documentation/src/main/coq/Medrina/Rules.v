Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Unicode.Utf8_core.
Require Import Coq.Strings.String.
Require Import Coq.Logic.Decidable.

Require Import Medrina.Names.
Require Import Medrina.Attributes.
Require Import Medrina.Actions.
Require Import Medrina.Roles.
Require Import Medrina.Types.
Require Import Medrina.Subjects.
Require Import Medrina.Objects.
Require Import Medrina.Forall.
Require Import Medrina.ListExtras.

Import ListNotations.

Open Scope string_scope.
Open Scope char_scope.

(* Many types carry proofs of their properties, and we want to be able
   to treat equality of values of these types as decidable. *)
Require Import Coq.Logic.ProofIrrelevance.

Set Mangle Names.

Inductive rule_conclusion_t :=
  | Allow
  | AllowImmediately
  | Deny
  | DenyImmediately
  .

Lemma rule_conclusion_eq_dec : forall (r0 r1 : rule_conclusion_t),
  decidable (r0 = r1).
Proof.
  intros r0 r1.
  destruct r0.
    destruct r1.
      left; reflexivity.
      right; discriminate.
      right; discriminate.
      right; discriminate.
    destruct r1.
      right; discriminate.
      left; reflexivity.
      right; discriminate.
      right; discriminate.
    destruct r1.
      right; discriminate.
      right; discriminate.
      left; reflexivity.
      right; discriminate.
    destruct r1.
      right; discriminate.
      right; discriminate.
      right; discriminate.
      left; reflexivity.
Qed.

Inductive rule_t := Rule {
  rule_conclusion : rule_conclusion_t;
  rule_subject    : subject_match_expression_t;
  rule_object     : object_match_expression_t;
  rule_action     : action_match_expression_t;
}.

Lemma rule_eq_dec : forall (r0 r1 : rule_t),
  decidable (r0 = r1).
Proof.
  intros r0 r1.
  destruct r0 as [rc0 rs0 ro0 ra0].
  destruct r1 as [rc1 rs1 ro1 ra1].
  destruct (rule_conclusion_eq_dec rc0 rc1) as [H_rc_eq|H_rc_neq].
  destruct (subject_match_expression_eq_dec rs0 rs1) as [H_rs_eq|H_rs_neq].
  destruct (object_match_expression_eq_dec ro0 ro1) as [H_ro_eq|H_ro_neq].
  destruct (action_match_expression_eq_dec ra0 ra1) as [H_ra_eq|H_ra_neq].
  left; congruence.
  right; congruence.
  right; congruence.
  right; congruence.
  right; congruence.
Qed.

Definition rule_matches
  (o : object_t)
  (s : subject_t)
  (a : action_t)
  (r : rule_t)
: bool :=
  let om := object_match_evaluate o (rule_object r) in
  let sm := subject_match_evaluate s (rule_subject r) in
  let am := action_match_evaluate a (rule_action r) in
   andb (andb om sm) am.

Inductive rule_compiled_t := RuleCompiled {
  compiled_rule_number : nat;
  compiled_rule        : rule_t
}.

Lemma rule_compiled_eq_dec : forall (r0 r1 : rule_compiled_t),
  decidable (r0 = r1).
Proof.
  intros r0 r1.
  destruct r0 as [rn0 rr0].
  destruct r1 as [rn1 rr1].
  destruct (Nat.eq_dec rn0 rn1) as [H_rn_eq|H_rn_neq].
  destruct (rule_eq_dec rr0 rr1) as [H_rr_eq|H_rr_neq].
  left; congruence.
  right; congruence.
  right; congruence.
Qed.

Inductive rule_compiled_ordered_t : list rule_compiled_t → Prop :=
  | RCEnd   : rule_compiled_ordered_t []
  | RCOne   : ∀ c, rule_compiled_ordered_t [c]
  | RCRest  : ∀ c0 c1 c_rest,
    rule_compiled_ordered_t c_rest →
        rule_compiled_ordered_t (c1 :: c_rest) →
          compiled_rule_number c1 = S (compiled_rule_number c0) →
              rule_compiled_ordered_t (c0 :: c1 :: c_rest).

Lemma rule_compiled_ordered_cons : ∀ r rs,
  rule_compiled_ordered_t (r :: rs) →
    rule_compiled_ordered_t rs.
Proof.
  intros r rs H_ord.
  inversion H_ord. {
    apply RCEnd.
  } {
    assumption.
  }
Qed.

Lemma rule_compiled_ordered_S : ∀ r0 r1 rs,
  rule_compiled_ordered_t (r0 :: r1 :: rs) →
    compiled_rule_number r1 = S (compiled_rule_number r0).
Proof.
  intros r0 r1 rs H_ord.
  inversion H_ord; assumption.
Qed.

Inductive rule_compiled_weak_ordered_t : list rule_compiled_t → Prop :=
  | RCWEnd   : rule_compiled_weak_ordered_t []
  | RCWOne   : ∀ c, rule_compiled_weak_ordered_t [c]
  | RCWRest  : ∀ c0 c1 c_rest,
    rule_compiled_weak_ordered_t c_rest →
        rule_compiled_weak_ordered_t (c1 :: c_rest) →
          compiled_rule_number c0 < compiled_rule_number c1 →
              rule_compiled_weak_ordered_t (c0 :: c1 :: c_rest).

Lemma rule_compiled_weak_ordered_cons : ∀ r rs,
  rule_compiled_weak_ordered_t (r :: rs) →
    rule_compiled_weak_ordered_t rs.
Proof.
  intros r rs H_ord.
  inversion H_ord. {
    apply RCWEnd.
  } {
    assumption.
  }
Qed.

Lemma rule_compiled_ordered_weaken : ∀ rs,
  rule_compiled_ordered_t rs →
    rule_compiled_weak_ordered_t rs.
Proof.
  intros rs.
  induction rs as [|x xs H_induction]. {
    intros. constructor.
  } {
    intros H_ord.
    inversion H_ord as [|k [Heq0 Heq1]|k0 k1 ks H_kord0 H_kord1 H_num [H_eq0 H_eq1]]. {
      constructor.
    } {
      subst x.
      pose proof (rule_compiled_ordered_cons _ _ H_ord) as H_ord_xs.
      pose proof (H_induction H_ord_xs) as H_weak_xs.
      assert ((compiled_rule_number k0) < (compiled_rule_number k1)) as H_lt. {
        rewrite H_num.
        apply Nat.lt_succ_diag_r.
      }
      constructor.
      rewrite <- H_eq1 in H_weak_xs.
      apply (rule_compiled_weak_ordered_cons _ _ H_weak_xs).
      rewrite <- H_eq1 in H_weak_xs.
      assumption.
      assumption.
    }
  }
Qed.

Lemma rule_compiled_weak_ordered_lt : ∀ rs r0,
  rule_compiled_weak_ordered_t (r0 :: rs) →
    Forall (λ m, compiled_rule_number r0 < compiled_rule_number m) rs.
Proof.
  intros rs.
  induction rs as [|r1 rrs H_induction]. {
    intros.
    constructor.
  } {
    intros r H_ord.
    assert (rule_compiled_weak_ordered_t (r1 :: rrs)) as H_ord_rrs
      by (apply (rule_compiled_weak_ordered_cons _ _ H_ord)).
    assert (Forall (λ m, (compiled_rule_number r1) < (compiled_rule_number m)) rrs) as H_fa
      by (apply (H_induction r1 H_ord_rrs)).

    inversion H_ord_rrs as [ |z [Heq0 Heq1]|z0 z1 zs H_ord_zs H_ord_z1zs H_lt0 [Heq0 Heq1]]. {
      constructor.
      inversion H_ord. assumption. constructor.
    } {
      rewrite <- Heq1 in H_ord_rrs.
      subst r1.
      inversion H_ord as [ | |? ? ? ? ? H_lt1]. {
        constructor.
        assumption.
        constructor.
        apply (Nat.lt_trans _ _ _ H_lt1 H_lt0).
        subst rrs.
        inversion H_fa as [|? ? ? H_fa2].
        apply (Forall_lt_trans_map _ compiled_rule_number zs r _ H_fa2 H_lt1).
      }
    }
  }
Qed.

Lemma rule_compiled_order_lt : ∀ rs r,
  rule_compiled_ordered_t (r :: rs) →
    Forall (λ m, compiled_rule_number r < compiled_rule_number m) rs.
Proof.
  intros rs r H_ord.
  assert (rule_compiled_weak_ordered_t (r :: rs)) as H0
    by (apply (rule_compiled_ordered_weaken _ H_ord)).
  assert (Forall (λ m, (compiled_rule_number r) < (compiled_rule_number m)) rs) as H1
    by (apply (rule_compiled_weak_ordered_lt _ _ H0)).
  assumption.
Qed.

Lemma rule_compiled_order_neq : ∀ rs r,
  rule_compiled_ordered_t (r :: rs) →
    Forall (λ m, compiled_rule_number r ≠ compiled_rule_number m) rs.
Proof.
  intros rs r H_ord.
  assert (rule_compiled_weak_ordered_t (r :: rs)) as H0
    by (apply (rule_compiled_ordered_weaken _ H_ord)).
  assert (Forall (λ m, (compiled_rule_number r) < (compiled_rule_number m)) rs) as H1
    by (apply (rule_compiled_weak_ordered_lt _ _ H0)).
  apply (
    @Forall_impl
    _
    (λ m, (compiled_rule_number r) < (compiled_rule_number m))
    (λ m, (compiled_rule_number r) ≠ (compiled_rule_number m))
  ). {
    intros a H_oalt.
    apply Nat.lt_neq.
    assumption.
  }
  assumption.
Qed.

Theorem rule_compiled_ordered_nodup : ∀ rs,
  rule_compiled_ordered_t rs -> NoDup rs.
Proof.
  intros rs H_ord.
  induction rs as [|y ys H_induction]. {
    constructor.
  } {
    assert (rule_compiled_ordered_t ys) as H_soy
      by (apply (rule_compiled_ordered_cons _ _ H_ord)).
    assert (NoDup ys) as H_nds
      by (apply (H_induction H_soy)).

    assert (Forall (λ z, compiled_rule_number y < compiled_rule_number z) ys) as H_falt. {
      apply rule_compiled_weak_ordered_lt.
      apply rule_compiled_ordered_weaken.
      assumption.
    }

    assert (Forall (λ z, compiled_rule_number y <> compiled_rule_number z) ys) as H_faneq. {
      apply (
        @Forall_impl
        _
        (λ z, (compiled_rule_number y) < (compiled_rule_number z))
        (λ z, (compiled_rule_number y) ≠ (compiled_rule_number z))
      ).
      intros H_impl.
      apply Nat.lt_neq.
      assumption.
    }

    assert (Forall (λ z, y ≠ z) ys) as H_yneqys. {
      apply (
        @Forall_impl
        _
        (λ z, (compiled_rule_number y) ≠ (compiled_rule_number z))
        (λ z, y ≠ z)
      ).
      intros o_some H_ya_neq.
      intros H_contra.
      subst o_some.
      contradiction.
      assumption.
    }

    assert (¬ In y ys) as H_yninys. {
      apply (Forall_neq_not_in _ ys _ H_yneqys).
    }

    constructor.
    assumption.
    assumption.
  }
Qed.

Inductive rule_compiled_ordered_zero_t : list rule_compiled_t → Prop :=
  | RC0Empty    : rule_compiled_ordered_zero_t []
  | RC0NonEmpty : ∀ r rs,
    rule_compiled_ordered_t rs →
      rule_compiled_ordered_t (r :: rs) →
        compiled_rule_number r = 0 →
          rule_compiled_ordered_zero_t (r :: rs).

Lemma rule_compiled_ordered_zero_weaken : ∀ rs,
  rule_compiled_ordered_zero_t rs → rule_compiled_ordered_t rs.
Proof.
  intros rs H0.
  inversion H0.
  constructor.
  assumption.
Qed.

Theorem rule_compiled_ordered_zero_nodup : ∀ rs,
  rule_compiled_ordered_zero_t rs → NoDup rs.
Proof.
  intros rs H0.
  pose proof (rule_compiled_ordered_zero_weaken _ H0) as H1.  
  apply (rule_compiled_ordered_nodup _ H1).
Qed.
