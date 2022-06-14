Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Unicode.Utf8_core.
Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.
Require Import OrderedType OrderedTypeEx.
Require Import Coq.Strings.String.
Require Import Coq.Logic.Decidable.

(* Many types carry proofs of their properties, and we want to be able
   to treat equality of values of these types as decidable. *)
Require Import Coq.Logic.ProofIrrelevance.

Import ListNotations.

Open Scope string_scope.
Open Scope char_scope.

Require Import Medrina.Names.
Require Import Medrina.Attributes.
Require Import Medrina.Actions.
Require Import Medrina.Roles.
Require Import Medrina.Types.
Require Import Medrina.Subjects.
Require Import Medrina.Objects.
Require Import Medrina.Forall.
Require Import Medrina.ListExtras.
Require Import Medrina.Rules.

Set Mangle Names.

Definition policy_first_index
  (rs          : list rule_compiled_t)
  (H_not_equal : [] ≠ rs)
: nat :=
  compiled_rule_number (head_non_empty _ rs H_not_equal).

Inductive policy_t := Policy {
  policy_rules         : list rule_compiled_t;
  policy_rules_ordered : rule_compiled_ordered_zero_t policy_rules
}.

Fixpoint policy_compile_rules_aux
  (rules   : list rule_t)
  (counter : nat)
: list rule_compiled_t :=
  match rules with
  | []      => []
  | r :: rs => (RuleCompiled counter r) :: (policy_compile_rules_aux rs (S counter))
  end.

Definition policy_compile_rules (rules : list rule_t) : list rule_compiled_t :=
  policy_compile_rules_aux rules 0.

Definition list_induction_3
  (A     : Type)
  (P     : list A → Prop)
  (H_nil : P [])
  (H_one : ∀ (r : A), P [r])
  (H_rec : ∀ (r0 r1 : A) (rest : list A), P rest → P (r1 :: rest) → P (r0 :: r1 :: rest))
  : ∀ (L : list A), P L :=
  fix IHL (L : list A) : P L :=
    match L with
    | []       => H_nil
    | r0 :: L0 =>
      let IHL' := IHL L0 in
        match L0 return (P L0 → P (r0 :: L0)) with
        | []         => fun _ => H_one r0
        | r1 :: rest => fun IHL' => H_rec r0 r1 rest (IHL rest) IHL'
        end IHL'
    end.

Lemma policy_compile_rules_aux_cons : ∀ r rs n,
  policy_compile_rules_aux (r :: rs) n = (RuleCompiled n r) :: policy_compile_rules_aux rs (S n).
Proof.
  intros r rs.
  induction rs as [|x|y0 y1 ys] using list_induction_3.
  intros n; reflexivity.
  intros n; reflexivity.
  intros n; reflexivity.
Qed.

Lemma policy_compile_rules_aux_ordered : ∀ rs n,
  rule_compiled_ordered_t (policy_compile_rules_aux rs n).
Proof.
  intros rs.
  unfold policy_compile_rules.
  induction rs as [|x|y0 y1 ys H_ind0 H_ind1] using list_induction_3. {
    intro n. apply RCEnd.
  } {
    intro n. apply RCOne.
  } {
    intro n.
    rewrite policy_compile_rules_aux_cons.
    rewrite policy_compile_rules_aux_cons.
    apply RCRest.
    apply (H_ind0 (S (S n))).
    rewrite <- policy_compile_rules_aux_cons.
    apply (H_ind1 (S n)).
    reflexivity.
  }
Qed.

Lemma policy_compile_rules_ordered : ∀ rs,
  rule_compiled_ordered_t (policy_compile_rules rs).
Proof. intros rs; apply policy_compile_rules_aux_ordered. Qed.

Lemma policy_compile_rules_ordered_zero : ∀ rs,
  rule_compiled_ordered_zero_t (policy_compile_rules rs).
Proof.
  intro rs.
  assert (rule_compiled_ordered_t (policy_compile_rules rs)) as H_ord
    by (apply (policy_compile_rules_ordered rs)).

  destruct rs as [|x xs]. {
    constructor.
  } {
    unfold policy_compile_rules in *.
    inversion H_ord as [|r [H_req H_eq0]|y0 y1 ys H_rc0 H_rc1 H_eq [H_yeq0 H_yeq1]]. {
      simpl.
      subst r.
      constructor.
      rewrite <- H_eq0.
      constructor.
      rewrite <- H_eq0.
      constructor.
      reflexivity.
    } {
      simpl.
      subst y0.
      constructor.
      rewrite <- H_yeq1.
      assumption.
      rewrite <- H_yeq1.
      constructor.
      assumption.
      assumption.
      assumption.
      reflexivity.
    }
  }
Qed.

Definition policy_compile (rules : list rule_t) : policy_t :=
  let r     := policy_compile_rules rules in
  let r_ord := policy_compile_rules_ordered_zero rules in
    Policy r r_ord.

Fixpoint policy_decompile_rules 
  (rs : list rule_compiled_t)
: list rule_t :=
  match rs with
  | []      => []
  | r :: rs => (compiled_rule r) :: (policy_decompile_rules rs)
  end.

Definition policy_decompile (p : policy_t) : list rule_t :=
  policy_decompile_rules (policy_rules p).

Theorem policy_compile_decompile_id : ∀ rs,
  rs = policy_decompile (policy_compile rs).
Proof.
  intros rs.
  unfold policy_compile.
  unfold policy_compile_rules.
  unfold policy_decompile.
  simpl.
  generalize dependent 0.
  induction rs as [|y ys H_ind]. {
    reflexivity.
  } {
    intros n.
    rewrite policy_compile_rules_aux_cons.
    simpl.
    assert (ys = (policy_decompile_rules (policy_compile_rules_aux ys (S n)))) as H
      by (apply (H_ind (S n))).
    rewrite <- H.
    reflexivity.
  }
Qed.

Fixpoint policy_up_to_not_including_aux
  (rs    : list rule_compiled_t)
  (index : nat)
: list rule_compiled_t :=
  match rs with
  | []      => []
  | x :: xs =>
    match lt_dec (compiled_rule_number x) index with
    | left _  => x :: (policy_up_to_not_including_aux xs index)
    | right _ => []
    end
  end.

Lemma policy_up_to_not_including_aux_ordered : ∀ rs n,
  rule_compiled_ordered_t rs → rule_compiled_ordered_t (policy_up_to_not_including_aux rs n).
Proof.
  intros rs n H_ord_rs.
  generalize dependent n.

  induction rs as [|x xs H_ind]. {
    intro m.
    apply RCEnd.
  } {
    simpl.
    destruct xs as [|y ys]. {
      intro m.
      destruct (lt_dec (compiled_rule_number x) m) as [H_lt|H_nlt]. {
        apply RCOne.
      } {
        apply RCEnd.
      }
    } {
      assert (rule_compiled_ordered_t (y :: ys)) as H_y_ord
        by (apply (rule_compiled_ordered_cons _ _ H_ord_rs)).
      assert (∀ n : nat, rule_compiled_ordered_t (policy_up_to_not_including_aux (y :: ys) n)) as H_ord_p_ys
        by (apply (H_ind H_y_ord)).
      assert (compiled_rule_number y = S (compiled_rule_number x)) as H_succ
        by (apply (rule_compiled_ordered_S _ _ _ H_ord_rs)).

      intros m.
      destruct (lt_dec (compiled_rule_number x) m) as [H_xlt|H_xnlt]. {
        simpl.
        destruct (lt_dec (compiled_rule_number y) m) as [H_ylt|H_ynlt]. {
          apply (RCRest x y).

          assert (rule_compiled_ordered_t (policy_up_to_not_including_aux (y :: ys) m)) as H_ord_p_ys_m
            by (apply (H_ord_p_ys m)).

          inversion H_ord_p_ys_m as [H_eq0|z H_eq12|cz0 cz1 c_rest H_rest_ord H_cz1_rest_ord H_succ2 H_cz0_cz1_rest_eq]. {
            destruct (lt_dec (compiled_rule_number y) m) in H_eq0.
            contradict H_eq0.
            discriminate.
            contradiction.
          } {
            destruct (lt_dec (compiled_rule_number y) m) in H_eq12. {
              assert (policy_up_to_not_including_aux ys m = []) as H_ys_nil. {
                assert (((policy_up_to_not_including_aux ys m) = []) ∧ (z = y)) as H_both
                  by (apply (cons_nil_head_eq _ _ _ _ H_eq12)).
                destruct H_both as [H_nil H_eq_zy].
                rewrite H_nil.
                reflexivity.
              }
              rewrite H_ys_nil.
              apply RCEnd.
            } {
              contradiction.
            }
          } {
            destruct (lt_dec (compiled_rule_number y) m) in H_cz0_cz1_rest_eq. {
              assert (cz1 :: c_rest = (policy_up_to_not_including_aux ys m)) as H_cz1_rest_eq
                by (inversion H_cz0_cz1_rest_eq; reflexivity).
              rewrite <- H_cz1_rest_eq.
              assumption.
            } {
              contradiction.
            }
          }

          assert (rule_compiled_ordered_t (policy_up_to_not_including_aux (y :: ys) m)) as H_ord_p_ys_m
            by (apply (H_ord_p_ys m)).

          inversion H_ord_p_ys_m as [H_eq0|z H_eq12|cz0 cz1 c_rest H_rest_ord H_cz1_rest_ord H_succ2 H_cz0_cz1_rest_eq]. {
            destruct (lt_dec (compiled_rule_number y) m) in H_eq0.
            contradict H_eq0.
            discriminate.
            contradiction.
          } {
            destruct (lt_dec (compiled_rule_number y) m) in H_eq12. {
              assert (policy_up_to_not_including_aux ys m = []) as H_ys_nil. {
                assert (((policy_up_to_not_including_aux ys m) = []) ∧ (z = y)) as H_both
                  by (apply (cons_nil_head_eq _ _ _ _ H_eq12)).
                destruct H_both as [H_nil H_eq_zy].
                rewrite H_nil.
                reflexivity.
              }
              rewrite H_ys_nil.
              apply RCOne.
            } {
              contradiction.
            }
          } {
            destruct (lt_dec (compiled_rule_number y) m) in H_cz0_cz1_rest_eq. {
              assert (cz1 :: c_rest = (policy_up_to_not_including_aux ys m)) as H_cz1_rest_eq
                by (inversion H_cz0_cz1_rest_eq; reflexivity).
              assert (cz0 = y) as H_cz0_y_eq
                by (inversion H_cz0_cz1_rest_eq; reflexivity).
              rewrite <- H_cz1_rest_eq.
              subst y.
              apply RCRest.
              assumption.
              assumption.
              assumption.
            } {
              contradiction.
            }
          } {
            assumption.
          }
        } {
          apply RCOne.
        }
      } {
        apply RCEnd.
      } 
    }
  }
Qed.

Lemma policy_up_to_not_including_aux_lt : ∀ rs n r,
  List.In r (policy_up_to_not_including_aux rs n) →
    (compiled_rule_number r) < n.
Proof.
  intros rs.
  induction rs as [|x xs H_ind]. {
    intros m r H_in.
    contradict H_in.
  } {
    intros m r H_in.
    simpl in H_in.
    destruct (lt_dec (compiled_rule_number x) m) as [H_lt|H_nlt] in H_in. {
      destruct (in_inv H_in) as [H_xeqr|H_r_in_pxs]. {
        subst x.
        assumption.
      } {
        apply (H_ind m r H_r_in_pxs).
      }
    } {
      contradict H_in.
    }
  }
Qed.

Lemma policy_up_to_not_including_aux_lt_forall : ∀ rs n,
  Forall (λ r, (compiled_rule_number r) < n) (policy_up_to_not_including_aux rs n).
Proof.
  intros rs.
  induction rs as [|x xs H_ind]. {
    intros m.
    constructor.
  } {
    intros m.
    simpl.
    destruct (lt_dec (compiled_rule_number x) m) as [H_lt|H_nlt]. {
      constructor.
      assumption.
      apply (H_ind m).
    } {
      constructor.
    }
  }
Qed.

Lemma policy_up_to_not_including_aux_cons : ∀ r rs n,
  compiled_rule_number r < n →
    rule_compiled_ordered_t (r :: rs) →
      policy_up_to_not_including_aux (r :: rs) n = r :: (policy_up_to_not_including_aux rs n).
Proof.
  intros r rs n H_lt H_ord.
  simpl.
  destruct (lt_dec (compiled_rule_number r) n) as [H_rlt|H_rnlt]. {
    reflexivity.
  } {
    contradiction.
  }
Qed.

Lemma policy_up_to_not_including_aux_ordered_zero : ∀ rs n,
  rule_compiled_ordered_zero_t rs → rule_compiled_ordered_zero_t (policy_up_to_not_including_aux rs n).
Proof.
  intros rs m H_rs0.
  assert (rule_compiled_ordered_t rs) as H_ord
    by (apply (rule_compiled_ordered_zero_weaken _ H_rs0)).
  assert (rule_compiled_ordered_t (policy_up_to_not_including_aux rs m)) as H_ord_upto
    by (apply (policy_up_to_not_including_aux_ordered _ _ H_ord)).

  destruct rs as [|x xs]. {
    constructor.
  } {
    assert (compiled_rule_number x = 0) as H_xeq0
      by (inversion H_rs0; assumption).
    simpl.
    destruct m as [|p]. {
      destruct (lt_dec (compiled_rule_number x) 0) as [H_lt|H_nlt]. {
        contradict H_lt.
        apply Nat.nlt_0_r.
      } {
        constructor.
      }
    } {
      destruct (lt_dec (compiled_rule_number x) (S p)) as [H_lt|H_nlt]. {
        constructor.
        rewrite policy_up_to_not_including_aux_cons in H_ord_upto.
        apply (rule_compiled_ordered_cons _ _ H_ord_upto).
        assumption.
        assumption.
        rewrite <- policy_up_to_not_including_aux_cons.
        assumption.
        assumption.
        assumption.
        assumption.
      } {
        constructor.
      }
    }
  }
Qed.

Definition policy_up_to_not_including
  (p     : policy_t)
  (index : nat)
: policy_t :=
  let r     := policy_up_to_not_including_aux (policy_rules p) index in
  let r_ord := policy_up_to_not_including_aux_ordered_zero _ _ (policy_rules_ordered p) in
    Policy r r_ord.

Theorem policy_up_to_not_including_lt_forall : ∀ p n,
  Forall (λ r, (compiled_rule_number r) < n) (policy_rules (policy_up_to_not_including p n)).
Proof. intros p n. apply policy_up_to_not_including_aux_lt_forall. Qed.

Unset Mangle Names.

Lemma policy_up_to_not_including_eq : ∀ p n,
  firstn n (policy_rules p) = policy_rules (policy_up_to_not_including p n).
Proof.
  intros p.
  destruct p as [p_rules p_zero].
Abort.

Inductive policy_result_t :=
  | Allowed
  | Denied
  .

Fixpoint policy_evaluate_aux
  (rs    : list rule_compiled_t)
  (o     : object_t)
  (s     : subject_t)
  (a     : action_t)
  (state : policy_result_t)
: policy_result_t :=
  match rs with
  | []          => state
  | r :: r_next =>
    match rule_matches o s a (compiled_rule r) with
    | true =>
      match rule_conclusion (compiled_rule r) with
      | Allow            => policy_evaluate_aux r_next o s a Allowed
      | AllowImmediately => Allowed
      | Deny             => policy_evaluate_aux r_next o s a Denied
      | DenyImmediately  => Denied
      end
    | false => policy_evaluate_aux r_next o s a state
    end
  end.

Definition policy_evaluate
  (p : policy_t)
  (o : object_t)
  (s : subject_t)
  (a : action_t)
: policy_result_t :=
  policy_evaluate_aux (policy_rules p) o s a Denied.

Theorem policy_nothing_matches_denied : ∀ o s a (p : policy_t),
  Forall (λ r, rule_matches o s a (compiled_rule r) = false) (policy_rules p) →
    policy_evaluate p o s a = Denied.
Proof.
  intros o s a p H_all.
  unfold policy_evaluate.
  induction (policy_rules p) as [|k r0 rules_remaining]. {
    reflexivity.
  } {
    simpl.
    destruct (rule_matches o s a (compiled_rule k)) eqn:H_matches. {
      contradict H_matches.
      assert (rule_matches o s a (compiled_rule k) = false) as H_false
        by (apply (@Forall_inv _ _ _ _ H_all)).
      rewrite H_false.
      discriminate.
    }
    apply rules_remaining.
    apply (@Forall_inv_tail _ _ _ _ H_all).
  }
Qed.

Unset Mangle Names.

Lemma policy_allow_immediately_nothing_prior : ∀ (p : policy_t) n o s a r_matching,
  Forall (λ k, compiled_rule_number k < n → rule_matches o s a (compiled_rule k) = false) (policy_rules p) →
    List.In r_matching (policy_rules p) →
      compiled_rule_number r_matching = n →
        rule_conclusion (compiled_rule r_matching) = DenyImmediately →
          rule_matches o s a (compiled_rule r_matching) = true →
            policy_evaluate p o s a = policy_evaluate (policy_up_to_not_including p (S n)) o s a.
Proof.
  intros p n o s a r_matching H_fa H_in H_num H_conc H_match.
  unfold policy_evaluate.
  induction (policy_rules p) as [|r_current r_remaining H_induction]. {
    contradiction.
  } {
    pose proof (policy_up_to_not_including_lt_forall p (S n)) as H_sub_lt.
    simpl.
    destruct (lt_dec (compiled_rule_number r_current) n) as [H_rltn|H_rnltn]. {
      pose proof (Forall_inv H_fa H_rltn) as H_no_match.
      rewrite H_no_match.
      simpl.
      destruct (lt_dec (compiled_rule_number r_current) (S n)) as [H_rltsn|H_rnltsn]. {
        simpl.
Abort.

Theorem policy_allow_immediately_nothing_prior : ∀ (p : policy_t) n o s a r_matching,
  Forall (λ k, compiled_rule_number k < n → rule_matches o s a (compiled_rule k) = false) (policy_rules p) →
    List.In r_matching (policy_rules p) →
      compiled_rule_number r_matching = n →
        rule_conclusion (compiled_rule r_matching) = DenyImmediately →
          rule_matches o s a (compiled_rule r_matching) = true →
            policy_evaluate p o s a = Denied.
Proof.
  intro p.
  unfold policy_evaluate.
  induction (policy_rules p) as [|r_current rs H_ind]. {
    intros n o s a r_matching H_fa H_in.
    contradiction.
  } {
    intros n o s a r_matching H_fa H_in H_num H_conc H_match.
    simpl.
    destruct (rule_compiled_eq_dec r_matching r_current) as [H_eq|H_neq]. {
      destruct H_eq.
      rewrite H_match.
      rewrite H_conc.
      reflexivity.
    } {
Abort.
