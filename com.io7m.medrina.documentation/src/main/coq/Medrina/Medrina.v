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

Require Import Medrina.Forall.
Require Import Medrina.ListExtras.

Set Mangle Names.

Definition acceptable_characters : list Ascii.ascii :=
  list_ascii_of_string "abcdefghijklmnopqrstuvwxyz0123456789_.". 

Definition valid_name (s : string) : Prop :=
  Forall (λ c, In c acceptable_characters) (list_ascii_of_string s)
  ∧ length s >= 1
  ∧ length s <= 256.

Lemma dec_map : ∀ P : Prop,
  {P}+{¬P} → decidable P.
Proof.
  intros p Hdec.
  destruct Hdec as [Hp|HpF].
    left; assumption.
    right; assumption.
Qed.

(* Whether all characters in a string are valid is decidable. *)
Lemma valid_name_acceptable_dec_S : ∀ s,
  {Forall (λ c, In c acceptable_characters) (list_ascii_of_string s)}
  +
  {¬ Forall (λ c, In c acceptable_characters) (list_ascii_of_string s)}.
Proof.
  intros s.
  apply Forall_dec.
  intro x.
  apply in_dec.
  apply Ascii.ascii_dec.
Qed.

(* Whether all characters in a string are valid is decidable. *)
Lemma valid_name_acceptable_dec : ∀ s,
  decidable (Forall (λ c, In c acceptable_characters) (list_ascii_of_string s)).
Proof. intros s. apply (dec_map _ (valid_name_acceptable_dec_S s)). Qed.

(* Whether a string is non-empty is decidable. *)
Lemma valid_name_length1_dec_S : ∀ s,
  {length s >= 1}+{¬ length s >= 1}.
Proof. intros s. apply Compare_dec.ge_dec. Qed.

(* Whether a string is non-empty is decidable. *)
Lemma valid_name_length1_dec : ∀ s,
  decidable (length s >= 1).
Proof. intro s. apply (dec_map _ (valid_name_length1_dec_S s)). Qed.

(* Whether a string is short enough is decidable. *)
Lemma valid_name_length256_dec_S : ∀ s,
  {length s <= 256}+{¬ length s <= 256}.
Proof. intros s. apply Compare_dec.le_dec. Qed.

(* Whether a string is short enough is decidable. *)
Lemma valid_name_length256_dec : ∀ s,
  decidable (length s <= 256).
Proof. intro s. apply (dec_map _ (valid_name_length256_dec_S s)). Qed.

(* Whether a string is valid is decidable. *)
Lemma valid_name_dec_S : ∀ s,
  {valid_name s}+{¬ valid_name s}.
Proof.
  intros s.
  unfold valid_name.
  destruct (valid_name_acceptable_dec_S s); firstorder.
  destruct (valid_name_length1_dec_S s); firstorder.
  destruct (valid_name_length256_dec_S s); firstorder.
Qed.

(* Whether a string is valid is decidable. *)
Lemma valid_name_dec : ∀ s,
  decidable (valid_name s).
Proof.
  intros s.
  unfold valid_name.
  destruct (valid_name_acceptable_dec_S s); firstorder.
  destruct (valid_name_length1_dec_S s); firstorder.
  destruct (valid_name_length256_dec_S s); firstorder.
Qed.

Class textual (A : Set) := {
  text_of : A → string
}.

Inductive action_name_t :=
  ActionName : ∀ s, valid_name s → action_name_t.

Lemma action_name_eq_dec : ∀ (s0 s1 : action_name_t),
  decidable (s0 = s1).
Proof.
  intros s0 s1.
  destruct s0 as [s0s s0p].
  destruct s1 as [s1s s1p].
  destruct (string_dec s0s s1s) as [Hseq|Hsneq]. {
    left.
    destruct Hseq.
    rewrite (proof_irrelevance (valid_name s0s) s0p s1p).
    reflexivity.
  } {
    right.
    intro H_contra.
    injection H_contra.
    assumption.
  }
Qed.

#[local]
Instance action_name_textual : textual action_name_t := {
  text_of (s : action_name_t) :=
    match s with
    | ActionName t _ => t
    end
}.

Inductive attribute_name_t :=
  AttributeName : ∀ s, valid_name s → attribute_name_t.

Lemma attribute_name_eq_dec : ∀ (s0 s1 : attribute_name_t),
  decidable (s0 = s1).
Proof.
  intros s0 s1.
  destruct s0 as [s0s s0p].
  destruct s1 as [s1s s1p].
  destruct (string_dec s0s s1s) as [Hseq|Hsneq]. {
    left.
    destruct Hseq.
    rewrite (proof_irrelevance (valid_name s0s) s0p s1p).
    reflexivity.
  } {
    right.
    intro H_contra.
    injection H_contra.
    assumption.
  }
Qed.

#[local]
Instance attribute_name_textual : textual attribute_name_t := {
  text_of (s : attribute_name_t) :=
    match s with
    | AttributeName t _ => t
    end
}.

Inductive attribute_value_t :=
  AttributeValue : ∀ s, valid_name s → attribute_value_t.

Lemma attribute_value_eq_dec : ∀ (s0 s1 : attribute_value_t),
  decidable (s0 = s1).
Proof.
  intros s0 s1.
  destruct s0 as [s0s s0p].
  destruct s1 as [s1s s1p].
  destruct (string_dec s0s s1s) as [Hseq|Hsneq]. {
    left.
    destruct Hseq.
    rewrite (proof_irrelevance (valid_name s0s) s0p s1p).
    reflexivity.
  } {
    right.
    intro H_contra.
    injection H_contra.
    assumption.
  }
Qed.

#[local]
Instance attribute_value_textual : textual attribute_value_t := {
  text_of (s : attribute_value_t) :=
    match s with
    | AttributeValue t _ => t
    end
}.

Inductive role_name_t :=
  RoleName : ∀ s, valid_name s → role_name_t.

Lemma role_name_eq_dec : ∀ (s0 s1 : role_name_t),
  decidable (s0 = s1).
Proof.
  intros s0 s1.
  destruct s0 as [s0s s0p].
  destruct s1 as [s1s s1p].
  destruct (string_dec s0s s1s) as [Hseq|Hsneq]. {
    left.
    destruct Hseq.
    rewrite (proof_irrelevance (valid_name s0s) s0p s1p).
    reflexivity.
  } {
    right.
    intro H_contra.
    injection H_contra.
    assumption.
  }
Qed.

#[local]
Instance role_name_textual : textual role_name_t := {
  text_of (s : role_name_t) :=
    match s with
    | RoleName t _ => t
    end
}.

Inductive type_name_t :=
  TypeName : ∀ s, valid_name s → type_name_t.

Lemma type_name_eq_dec : ∀ (s0 s1 : type_name_t),
  decidable (s0 = s1).
Proof.
  intros s0 s1.
  destruct s0 as [s0s s0p].
  destruct s1 as [s1s s1p].
  destruct (string_dec s0s s1s) as [Hseq|Hsneq]. {
    left.
    destruct Hseq.
    rewrite (proof_irrelevance (valid_name s0s) s0p s1p).
    reflexivity.
  } {
    right.
    intro H_contra.
    injection H_contra.
    assumption.
  }
Qed.

#[local]
Instance type_name_textual : textual type_name_t := {
  text_of (s : type_name_t) :=
    match s with
    | TypeName t _ => t
    end
}.

Inductive object_t := Object {
  object_type             : type_name_t;
  object_attributes       : list (attribute_name_t * attribute_value_t);
  object_attributes_names : NoDup (map fst object_attributes);
}.

Lemma attribute_eq_dec : ∀ (a b : (attribute_name_t * attribute_value_t)),
  decidable (a = b).
Proof.
  intros a b.
  destruct a as [a_name a_value].
  destruct b as [b_name b_value].

  destruct (attribute_name_eq_dec a_name b_name) as [Hn_eq|Hn_neq]. {
    destruct (attribute_value_eq_dec a_value b_value) as [Hv_eq|Hv_neq]. {
      left.
      subst a_name.
      subst a_value.
      reflexivity.
    } {
      right.
      intro H_contra.
      inversion H_contra.
      contradiction.
    }
  } {
    destruct (attribute_value_eq_dec a_value b_value) as [Hv_eq|Hv_neq]. {
      right.
      intro H_contra.
      inversion H_contra.
      contradiction.
    } {
      right.
      intro H_contra.
      inversion H_contra.
      contradiction.
    }
  }
Qed.

Lemma object_eq_dec : ∀ (o0 o1 : object_t),
  decidable (o0 = o1).
Proof.
  intros o0 o1.
  destruct o0 as [o0_type o0_attr o0_p].
  destruct o1 as [o1_type o1_attr o1_p].

  destruct (type_name_eq_dec o0_type o1_type) as [H_oeq|H_oneq]. {
    destruct (list_eq_dec attribute_eq_dec o0_attr o1_attr) as [H_aeq|H_aneq]. {
      left.
      destruct H_oeq.
      destruct H_aeq.
      rewrite (proof_irrelevance _ o0_p o1_p).
      reflexivity.
    } {
      right.
      intro H_contra.
      inversion H_contra.
      contradiction.
    }
  } {
    destruct (list_eq_dec attribute_eq_dec o0_attr o1_attr) as [H_aeq|H_aneq]. {
      right.
      intro H_contra.
      inversion H_contra.
      contradiction.
    } {
      right.
      intro H_contra.
      inversion H_contra.
      contradiction.
    }
  }
Qed.

Inductive subject_t := Subject {
  subject_roles : list role_name_t
}.

Lemma subject_eq_dec : ∀ (s0 s1 : subject_t),
  decidable (s0 = s1).
Proof.
  intros s0 s1.
  destruct s0 as [s0_roles].
  destruct s1 as [s1_roles].
  destruct (list_eq_dec role_name_eq_dec s0_roles s1_roles) as [H_eq|H_neq]. {
    left.
    destruct H_eq.
    reflexivity.
  } {
    right.
    intro H_contra.
    inversion H_contra.
    contradiction.
  }
Qed.

Inductive action_t := Action {
  action_name : action_name_t
}.

Lemma action_eq_dec : ∀ (a0 a1 : action_t),
  decidable (a0 = a1).
Proof.
  intros a0 a1.
  destruct a0 as [a0_name].
  destruct a1 as [a1_name].

  destruct (action_name_eq_dec a0_name a1_name) as [H_eq|H_neq]. {
    left.
    destruct H_eq.
    reflexivity.
  } {
    right.
    intro H_contra.
    inversion H_contra.
    contradiction.
  }
Qed.

Section ObjectMatchExpressions.

  Local Unset Elimination Schemes.

  Inductive object_match_expression_t :=
    | OETrue     : object_match_expression_t
    | OEFalse    : object_match_expression_t
    | OEWithType : type_name_t → object_match_expression_t
    | OEAnd      : list object_match_expression_t → object_match_expression_t
    | OEOr       : list object_match_expression_t → object_match_expression_t
    .

  Section rect.
    Variable P              : object_match_expression_t → Type.
    Variable P_list         : list object_match_expression_t → Type.
    Hypothesis P_nil        : P_list [].
    Hypothesis P_cons       : ∀ x xs, P x → P_list xs → P_list (x :: xs).
    Hypothesis P_OETrue     : P OETrue.
    Hypothesis P_OEFalse    : P OEFalse.
    Hypothesis P_OEWithType : ∀ t, P (OEWithType t).
    Hypothesis P_OEAnd      : ∀ es, P_list es → P (OEAnd es).
    Hypothesis P_OEOr       : ∀ es, P_list es → P (OEOr es).

    Fixpoint object_match_expression_t_rect (e : object_match_expression_t) : P e :=
      let
        fix exp_for_all (xs : list object_match_expression_t) : P_list xs :=
          match xs as rxs return (P_list rxs) with
          | []        => @P_nil
          | (y :: ys) => @P_cons y ys (object_match_expression_t_rect y) (exp_for_all ys)
          end
      in
        match e with
        | OETrue       => P_OETrue
        | OEFalse      => P_OEFalse
        | OEWithType t => P_OEWithType t
        | OEAnd es     => P_OEAnd es (exp_for_all es)
        | OEOr es      => P_OEOr es (exp_for_all es)
        end.
  End rect.

  Section ind.
    Variable P              : object_match_expression_t → Prop.
    Hypothesis P_OETrue     : P OETrue.
    Hypothesis P_OEFalse    : P OEFalse.
    Hypothesis P_OEWithType : ∀ t, P (OEWithType t).
    Hypothesis P_OEAnd      : ∀ es, Forall P es → P (OEAnd es).
    Hypothesis P_OEOr       : ∀ es, Forall P es → P (OEOr es).

    Definition object_match_expression_t_ind (e : object_match_expression_t) : P e :=
      object_match_expression_t_rect
        P
        (Forall P)
        (Forall_nil _)
        (λ x xs Px Pxs, Forall_cons _ Px Pxs)
        P_OETrue
        P_OEFalse
        P_OEWithType
        P_OEAnd
        P_OEOr
        e.
  End ind.

End ObjectMatchExpressions.

Lemma object_match_expression_eq_dec : forall (e0 e1 : object_match_expression_t),
  decidable (e0 = e1).
Proof.
  intros e0.
  induction e0 as [ | |t0|es0 H_fa0|es0 H_fa0]. {
    intros e1.
    destruct e1.
    left; reflexivity.
    right; discriminate.
    right; discriminate.
    right; discriminate.
    right; discriminate.
  } {
    intros e1.
    destruct e1.
    right; discriminate.
    left; reflexivity.
    right; discriminate.
    right; discriminate.
    right; discriminate.
  } {
    intros e1.
    destruct e1 as [ | |t1|es1|es1].
    right; discriminate.
    right; discriminate.
    destruct (type_name_eq_dec t0 t1) as [H_teq|H_tneq]. {
      destruct H_teq.
      left; reflexivity.
    } {
      right. intro H_contra. inversion H_contra. contradiction.
    }
    right; discriminate.
    right; discriminate.
  } {
    induction es0 as [|x xs H_induction]. {
      intro e1.
      destruct e1 as [ | |t1|es1|es1].
      right; discriminate.
      right; discriminate.
      right; discriminate.
      destruct es1 as [|y ys]. {
        left; reflexivity.
      } {
        right; discriminate.
      }
      right; discriminate.
    } {
      intro e1.
      destruct e1 as [ | |t1|es1|es1].
      right; discriminate.
      right; discriminate.
      right; discriminate.
      destruct es1 as [|y ys]. {
        right; discriminate.
      } {
        pose proof (Forall_inv H_fa0 y) as H_dec_head.
        pose proof (Forall_inv_tail H_fa0) as H_dec_tail.
        pose proof (H_induction H_dec_tail) as H_dec_xs.
        pose proof (H_dec_xs (OEAnd ys)) as H_dec_ys.

        destruct H_dec_head as [H_head_eq|H_head_neq]. {
          destruct H_dec_ys as [H_tail_eq|H_tail_neq]. {
            left. congruence.
          } {
            right. congruence.
          }
        } {
          destruct H_dec_ys as [H_tail_eq|H_tail_neq]. {
            right. congruence.
          } {
            right. congruence.
          }
        }
      }
      right; discriminate.
    }
  } {
    induction es0 as [|x xs H_induction]. {
      intro e1.
      destruct e1 as [ | |t1|es1|es1].
      right; discriminate.
      right; discriminate.
      right; discriminate.
      right; discriminate.
      destruct es1 as [|y ys]. {
        left; reflexivity.
      } {
        right; discriminate.
      }
    } {
      intro e1.
      destruct e1 as [ | |t1|es1|es1].
      right; discriminate.
      right; discriminate.
      right; discriminate.
      right; discriminate.
      destruct es1 as [|y ys]. {
        right; discriminate.
      } {
        pose proof (Forall_inv H_fa0 y) as H_dec_head.
        pose proof (Forall_inv_tail H_fa0) as H_dec_tail.
        pose proof (H_induction H_dec_tail) as H_dec_xs.
        pose proof (H_dec_xs (OEOr ys)) as H_dec_ys.

        destruct H_dec_head as [H_head_eq|H_head_neq]. {
          destruct H_dec_ys as [H_tail_eq|H_tail_neq]. {
            left. congruence.
          } {
            right. congruence.
          }
        } {
          destruct H_dec_ys as [H_tail_eq|H_tail_neq]. {
            right. congruence.
          } {
            right. congruence.
          }
        }
      }
    }
  }
Qed.

Fixpoint object_match_evaluate
  (o : object_t)
  (e : object_match_expression_t)
: bool :=
  match e with
  | OETrue                    => true
  | OEFalse                   => false
  | OEWithType (TypeName t _) => eqb t (text_of (object_type o))
  | OEAnd es                  => List.fold_right (λ e acc, andb acc (object_match_evaluate o e)) true es
  | OEOr es                   => List.fold_right (λ e acc, orb acc (object_match_evaluate o e)) false es
  end.

Section SubjectMatchExpressions.

  Local Unset Elimination Schemes.

  Inductive subject_match_expression_t :=
    | SETrue         : subject_match_expression_t
    | SEFalse        : subject_match_expression_t
    | SEWithRolesAll : list role_name_t → subject_match_expression_t
    | SEWithRolesAny : list role_name_t → subject_match_expression_t
    | SEAnd          : list subject_match_expression_t → subject_match_expression_t
    | SEOr           : list subject_match_expression_t → subject_match_expression_t
    .

  Section rect.
    Variable P                  : subject_match_expression_t → Type.
    Variable P_list             : list subject_match_expression_t → Type.
    Hypothesis P_nil            : P_list [].
    Hypothesis P_cons           : ∀ x xs, P x → P_list xs → P_list (x :: xs).
    Hypothesis P_SETrue         : P SETrue.
    Hypothesis P_SEFalse        : P SEFalse.
    Hypothesis P_SEWithRolesAll : ∀ rs, P (SEWithRolesAll rs).
    Hypothesis P_SEWithRolesAny : ∀ rs, P (SEWithRolesAny rs).
    Hypothesis P_SEAnd          : ∀ es, P_list es → P (SEAnd es).
    Hypothesis P_SEOr           : ∀ es, P_list es → P (SEOr es).

    Fixpoint subject_match_expression_t_rect (e : subject_match_expression_t) : P e :=
      let
        fix exp_for_all (xs : list subject_match_expression_t) : P_list xs :=
          match xs as rxs return (P_list rxs) with
          | []        => @P_nil
          | (y :: ys) => @P_cons y ys (subject_match_expression_t_rect y) (exp_for_all ys)
          end
      in
        match e with
        | SETrue            => P_SETrue
        | SEFalse           => P_SEFalse
        | SEWithRolesAll ts => P_SEWithRolesAll ts
        | SEWithRolesAny ts => P_SEWithRolesAny ts
        | SEAnd es          => P_SEAnd es (exp_for_all es)
        | SEOr es           => P_SEOr es (exp_for_all es)
        end.
  End rect.

  Section ind.
    Variable P                  : subject_match_expression_t → Prop.
    Hypothesis P_SETrue         : P SETrue.
    Hypothesis P_SEFalse        : P SEFalse.
    Hypothesis P_SEWithRolesAll : ∀ ts, P (SEWithRolesAll ts).
    Hypothesis P_SEWithRolesAny : ∀ ts, P (SEWithRolesAny ts).
    Hypothesis P_SEAnd          : ∀ es, Forall P es → P (SEAnd es).
    Hypothesis P_SEOr           : ∀ es, Forall P es → P (SEOr es).

    Definition subject_match_expression_t_ind (e : subject_match_expression_t) : P e :=
      subject_match_expression_t_rect
        P
        (Forall P)
        (Forall_nil _)
        (λ x xs Px Pxs, Forall_cons _ Px Pxs)
        P_SETrue
        P_SEFalse
        P_SEWithRolesAll
        P_SEWithRolesAny
        P_SEAnd
        P_SEOr
        e.
  End ind.

End SubjectMatchExpressions.

Lemma subject_match_expression_eq_dec : forall (e0 e1 : subject_match_expression_t),
  decidable (e0 = e1).
Proof.
  intros e0.
  induction e0 as [ | |ts|ts|es0 H_fa0|es0 H_fa0]. {
    (* SETrue = ... *)
    intros e1.
    destruct e1.
    left; reflexivity.
    right; discriminate.
    right; discriminate.
    right; discriminate.
    right; discriminate.
    right; discriminate.
  } {
    (* SEFalse = ... *)
    intros e1.
    destruct e1.
    right; discriminate.
    left; reflexivity.
    right; discriminate.
    right; discriminate.
    right; discriminate.
    right; discriminate.
  } {
    (* SEWithRolesAll = ... *)
    intros e1.
    destruct e1 as [ | |ss|ss|es1|es1].
    right; discriminate.
    right; discriminate.
    destruct (list_eq_dec role_name_eq_dec ts ss) as [H_teq|H_tneq]. {
      destruct H_teq.
      left; reflexivity.
    } {
      right. intro H_contra. inversion H_contra. contradiction.
    }
    right; discriminate.
    right; discriminate.
    right; discriminate.
  } {
    (* SEWithRolesAny = ... *)
    intros e1.
    destruct e1 as [ | |ss|ss|es1|es1].
    right; discriminate.
    right; discriminate.
    right; discriminate.
    destruct (list_eq_dec role_name_eq_dec ts ss) as [H_teq|H_tneq]. {
      destruct H_teq.
      left; reflexivity.
    } {
      right. intro H_contra. inversion H_contra. contradiction.
    }
    right; discriminate.
    right; discriminate.
  } {
    (* SEAnd = ... *)
    induction es0 as [|x xs H_induction]. {
      intro e1.
      destruct e1 as [ | |ts1|ts1|es1|es1].
      right; discriminate.
      right; discriminate.
      right; discriminate.
      right; discriminate.
      destruct es1 as [|y ys]. {
        left; reflexivity.
      } {
        right; discriminate.
      }
      right; discriminate.
    } {
      intro e1.
      destruct e1 as [ | |ts1|ts1|es1|es1].
      right; discriminate.
      right; discriminate.
      right; discriminate.
      right; discriminate.
      destruct es1 as [|y ys]. {
        right; discriminate.
      } {
        pose proof (Forall_inv H_fa0 y) as H_dec_head.
        pose proof (Forall_inv_tail H_fa0) as H_dec_tail.
        pose proof (H_induction H_dec_tail) as H_dec_xs.
        pose proof (H_dec_xs (SEAnd ys)) as H_dec_ys.

        destruct H_dec_head as [H_head_eq|H_head_neq]. {
          destruct H_dec_ys as [H_tail_eq|H_tail_neq]. {
            left. congruence.
          } {
            right. congruence.
          }
        } {
          destruct H_dec_ys as [H_tail_eq|H_tail_neq]. {
            right. congruence.
          } {
            right. congruence.
          }
        }
      }
      right; discriminate.
    }
  } {
    (* SEOr = ... *)
    induction es0 as [|x xs H_induction]. {
      intro e1.
      destruct e1 as [ | |ts1|ts1|es1|es1].
      right; discriminate.
      right; discriminate.
      right; discriminate.
      right; discriminate.
      right; discriminate.
      destruct es1 as [|y ys]. {
        left; reflexivity.
      } {
        right; discriminate.
      }
    } {
      intro e1.
      destruct e1 as [ | |ts1|ts1|es1|es1].
      right; discriminate.
      right; discriminate.
      right; discriminate.
      right; discriminate.
      right; discriminate.
      destruct es1 as [|y ys]. {
        right; discriminate.
      } {
        pose proof (Forall_inv H_fa0 y) as H_dec_head.
        pose proof (Forall_inv_tail H_fa0) as H_dec_tail.
        pose proof (H_induction H_dec_tail) as H_dec_xs.
        pose proof (H_dec_xs (SEOr ys)) as H_dec_ys.

        destruct H_dec_head as [H_head_eq|H_head_neq]. {
          destruct H_dec_ys as [H_tail_eq|H_tail_neq]. {
            left. congruence.
          } {
            right. congruence.
          }
        } {
          destruct H_dec_ys as [H_tail_eq|H_tail_neq]. {
            right. congruence.
          } {
            right. congruence.
          }
        }
      }
    }
  }
Qed.

Definition subject_has_roleb
  (s : subject_t)
  (r : role_name_t)
: bool :=
  List.existsb (λ sr, eqb (text_of sr) (text_of r)) (subject_roles s).

Fixpoint subject_match_evaluate
  (s : subject_t)
  (e : subject_match_expression_t)
: bool :=
  match e with
  | SETrue            => true
  | SEFalse           => false
  | SEWithRolesAll rs => List.forallb (λ r, subject_has_roleb s r) rs
  | SEWithRolesAny rs => List.fold_right (λ sr acc, orb acc (subject_has_roleb s sr)) false rs
  | SEAnd es          => List.fold_right (λ e acc, andb acc (subject_match_evaluate s e)) true es
  | SEOr es           => List.fold_right (λ e acc, orb acc (subject_match_evaluate s e)) false es
  end.

Section ActionMatchExpressions.

  Local Unset Elimination Schemes.

  Inductive action_match_expression_t :=
    | AETrue     : action_match_expression_t
    | AEFalse    : action_match_expression_t
    | AEWithName : action_name_t → action_match_expression_t
    | AEAnd      : list action_match_expression_t → action_match_expression_t
    | AEOr       : list action_match_expression_t → action_match_expression_t
    .

  Section rect.
    Variable P              : action_match_expression_t → Type.
    Variable P_list         : list action_match_expression_t → Type.
    Hypothesis P_nil        : P_list [].
    Hypothesis P_cons       : ∀ x xs, P x → P_list xs → P_list (x :: xs).
    Hypothesis P_AETrue     : P AETrue.
    Hypothesis P_AEFalse    : P AEFalse.
    Hypothesis P_AEWithName : ∀ n, P (AEWithName n).
    Hypothesis P_AEAnd      : ∀ es, P_list es → P (AEAnd es).
    Hypothesis P_AEOr       : ∀ es, P_list es → P (AEOr es).

    Fixpoint action_match_expression_t_rect (e : action_match_expression_t) : P e :=
      let
        fix exp_for_all (xs : list action_match_expression_t) : P_list xs :=
          match xs as rxs return (P_list rxs) with
          | []        => @P_nil
          | (y :: ys) => @P_cons y ys (action_match_expression_t_rect y) (exp_for_all ys)
          end
      in
        match e with
        | AETrue       => P_AETrue
        | AEFalse      => P_AEFalse
        | AEWithName n => P_AEWithName n
        | AEAnd es     => P_AEAnd es (exp_for_all es)
        | AEOr es      => P_AEOr es (exp_for_all es)
        end.
  End rect.

  Section ind.
    Variable P              : action_match_expression_t → Prop.
    Hypothesis P_AETrue     : P AETrue.
    Hypothesis P_AEFalse    : P AEFalse.
    Hypothesis P_AEWithName : ∀ n, P (AEWithName n).
    Hypothesis P_AEAnd      : ∀ es, Forall P es → P (AEAnd es).
    Hypothesis P_AEOr       : ∀ es, Forall P es → P (AEOr es).

    Definition action_match_expression_t_ind (e : action_match_expression_t) : P e :=
      action_match_expression_t_rect
        P
        (Forall P)
        (Forall_nil _)
        (λ x xs Px Pxs, Forall_cons _ Px Pxs)
        P_AETrue
        P_AEFalse
        P_AEWithName
        P_AEAnd
        P_AEOr
        e.
  End ind.

End ActionMatchExpressions.

Lemma action_match_expression_eq_dec : forall (e0 e1 : action_match_expression_t),
  decidable (e0 = e1).
Proof.
  intros e0.
  induction e0 as [ | |t|es0 H_fa0|es0 H_fa0]. {
    (* AETrue = ... *)
    intros e1.
    destruct e1.
    left; reflexivity.
    right; discriminate.
    right; discriminate.
    right; discriminate.
    right; discriminate.
  } {
    (* AEFalse = ... *)
    intros e1.
    destruct e1.
    right; discriminate.
    left; reflexivity.
    right; discriminate.
    right; discriminate.
    right; discriminate.
  } {
    (* AEWithName = ... *)
    intros e1.
    destruct e1 as [ | |tr| | ].
    right; discriminate.
    right; discriminate.
    destruct (action_name_eq_dec t tr) as [H_nameeq|H_nameneq]. {
      destruct H_nameeq. left; reflexivity.
    } {
      right; congruence.
    }
    right; discriminate.
    right; discriminate.
  } {
    (* AEAnd = ... *)
    induction es0 as [|x xs H_induction]. {
      intro e1.
      destruct e1 as [ | | |es1|].
      right; discriminate.
      right; discriminate.
      right; discriminate.
      destruct es1 as [|y ys]. {
        left; reflexivity.
      } {
        right; discriminate.
      }
      right; discriminate.
    } {
      intro e1.
      destruct e1 as [ | | |es1|].
      right; discriminate.
      right; discriminate.
      right; discriminate.
      destruct es1 as [|y ys]. {
        right; discriminate.
      } {
        pose proof (Forall_inv H_fa0 y) as H_dec_head.
        pose proof (Forall_inv_tail H_fa0) as H_dec_tail.
        pose proof (H_induction H_dec_tail) as H_dec_xs.
        pose proof (H_dec_xs (AEAnd ys)) as H_dec_ys.

        destruct H_dec_head as [H_head_eq|H_head_neq]. {
          destruct H_dec_ys as [H_tail_eq|H_tail_neq]. {
            left. congruence.
          } {
            right. congruence.
          }
        } {
          destruct H_dec_ys as [H_tail_eq|H_tail_neq]. {
            right. congruence.
          } {
            right. congruence.
          }
        }
      }
      right; discriminate.
    }
  } {
    (* AEOr = ... *)
    induction es0 as [|x xs H_induction]. {
      intro e1.
      destruct e1 as [ | | | |es1].
      right; discriminate.
      right; discriminate.
      right; discriminate.
      right; discriminate.
      destruct es1 as [|y ys]. {
        left; reflexivity.
      } {
        right; discriminate.
      }
    } {
      intro e1.
      destruct e1 as [ | | | |es1].
      right; discriminate.
      right; discriminate.
      right; discriminate.
      right; discriminate.
      destruct es1 as [|y ys]. {
        right; discriminate.
      } {
        pose proof (Forall_inv H_fa0 y) as H_dec_head.
        pose proof (Forall_inv_tail H_fa0) as H_dec_tail.
        pose proof (H_induction H_dec_tail) as H_dec_xs.
        pose proof (H_dec_xs (AEOr ys)) as H_dec_ys.

        destruct H_dec_head as [H_head_eq|H_head_neq]. {
          destruct H_dec_ys as [H_tail_eq|H_tail_neq]. {
            left. congruence.
          } {
            right. congruence.
          }
        } {
          destruct H_dec_ys as [H_tail_eq|H_tail_neq]. {
            right. congruence.
          } {
            right. congruence.
          }
        }
      }
    }
  }
Qed.

Fixpoint action_match_evaluate
  (a : action_t)
  (e : action_match_expression_t)
: bool :=
  match e with
  | AETrue        => true
  | AEFalse       => false
  | AEWithName n  => eqb (text_of n) (text_of (action_name a))
  | AEAnd es      => List.fold_right (λ e acc, andb acc (action_match_evaluate a e)) true es
  | AEOr es       => List.fold_right (λ e acc, orb acc (action_match_evaluate a e)) false es
  end.

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

Lemma head_non_empty : ∀ (A : Type) (xs : list A),
  [] ≠ xs → A.
Proof.
  intros A xs H_neq.
  destruct xs as [|x].
    contradict H_neq.
    reflexivity.
    exact x.
Qed.

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

Lemma list_in_one_both_eq : ∀ (A : Type) (x y z : A),
  List.In x (z :: []) →
    List.In y (z :: []) →
      x = y.
Proof.
  intros A x y z H_inx H_iny.
  assert ((z = x) ∨ (List.In x [])) as H_inv0
    by (apply (in_inv H_inx)).
  assert ((z = y) ∨ (List.In y [])) as H_inv1
    by (apply (in_inv H_iny)).
  inversion H_inv0. {
    inversion H_inv1. {
      subst x.
      subst y.
      reflexivity.
    } {
      contradiction.
    }
  } {
    contradiction.
  }
Qed.

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

Lemma cons_nil_head_eq : ∀ (A : Type) (x y : A) (ys : list A),
  x :: [] = y :: ys →
    ys = [] ∧ x = y.
Proof.
  intros A x y ys H_eq.
  constructor.
  induction ys as [|z zs]. {
    reflexivity.
  } {
    contradict H_eq.
    discriminate.
  }
  induction ys as [|z zs]. {
    inversion H_eq.
    reflexivity.
  } {
    contradict H_eq.
    discriminate.
  }
Qed.

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

Lemma policy_up_to_not_including_aux_length : ∀ rs n,
  rule_compiled_ordered_zero_t rs → 
    List.length (policy_up_to_not_including_aux rs n) = Nat.min (pred n) (List.length rs).
Proof.
  intros rs n H_ordz.
  pose proof (rule_compiled_ordered_zero_weaken _ H_ordz) as H_ord.
  clear H_ordz.
  generalize dependent n.
  induction rs as [|x xs H_induction]. {
    intros n.
    simpl.
    rewrite Nat.min_0_r.
    reflexivity.
  } {
    intros n.
    pose proof (rule_compiled_ordered_cons _ _ H_ord) as H0.
    pose proof (H_induction H0 n) as H1.
Abort.

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

Lemma policy_up_to_not_including_eq : ∀ p n,
  firstn n (policy_rules p) = policy_rules (policy_up_to_not_including p n).
Proof.
  intros p.
  destruct p as [p_rules p_zero].
  pose proof (rule_compiled_ordered_zero_weaken p_rules p_zero) as H_ord.
  unfold policy_rules.
  unfold policy_up_to_not_including.
  unfold policy_rules.
  clear p_zero.

  induction p_rules as [|x xs H_induction]. {
    intros n.
    rewrite firstn_nil.
    reflexivity.
  } {
    intros n.
    simpl.
    pose proof (rule_compiled_order_lt _ _ H_ord) as H2.
    pose proof (rule_compiled_ordered_cons _ _ H_ord) as H0.
    pose proof (H_induction H0 n) as H1.

    inversion H2 as [H3|H4]. {
      simpl.
      destruct (lt_dec (compiled_rule_number x) n) as [H_xlt|H_xnlt]. {
        destruct n as [|m]. {
          contradict H_xlt.
          apply Nat.nlt_0_r.
        } {
          rewrite firstn_one.
          reflexivity.
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

