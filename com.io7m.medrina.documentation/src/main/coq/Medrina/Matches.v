(*
 * Copyright © 2023 Mark Raynsford <code@io7m.com> https://www.io7m.com
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR
 * IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Import ListNotations.

Require Import Medrina.Actions.
Require Import Medrina.Names.
Require Import Medrina.Subjects.
Require Import Medrina.Roles.
Require Import Medrina.Objects.

(** An expression that matches a subject. *)
Inductive exprMatchSubject : Type :=
  | EMS_False        : exprMatchSubject
  | EMS_True         : exprMatchSubject
  | EMS_WithRolesAll : RoleSets.t -> exprMatchSubject
  | EMS_WithRolesAny : RoleSets.t -> exprMatchSubject
  | EMS_And          : list exprMatchSubject -> exprMatchSubject
  | EMS_Or           : list exprMatchSubject -> exprMatchSubject
  .

Section ExprMatchSubjects_ind.
  Variable P : exprMatchSubject -> Prop.
  Hypothesis P_False        : P EMS_False.
  Hypothesis P_True         : P EMS_True.
  Hypothesis P_WithRolesAll : forall r, P (EMS_WithRolesAll r).
  Hypothesis P_WithRolesAny : forall r, P (EMS_WithRolesAny r).
  Hypothesis P_And          : forall es, Forall P es -> P (EMS_And es).
  Hypothesis P_Or           : forall es, Forall P es -> P (EMS_Or es).

  Fixpoint exprMatchSubject_extendedInd (e : exprMatchSubject) : P e :=
    let
      fix e_list (xs : list exprMatchSubject) : Forall P xs :=
        match xs as rxs return (Forall P rxs) with
        | []        => Forall_nil _
        | (y :: ys) => @Forall_cons _ _ y ys (exprMatchSubject_extendedInd y) (e_list ys)
        end
    in
      match e with
      | EMS_False          => P_False
      | EMS_True           => P_True
      | EMS_WithRolesAll r => P_WithRolesAll r
      | EMS_WithRolesAny r => P_WithRolesAny r
      | EMS_And es         => P_And es (e_list es)
      | EMS_Or es          => P_Or es (e_list es)
      end.

End ExprMatchSubjects_ind.

(** An evaluation function for subject match expressions. *)
Fixpoint exprMatchSubjectEvalF
  (s : subject)
  (e : exprMatchSubject)
: bool :=
  match e with
  | EMS_False          => false
  | EMS_True           => true
  | EMS_WithRolesAll r => RoleSets.subset r (sRoles s)
  | EMS_WithRolesAny r => RoleSets.exists_ (fun x => RoleSets.mem x (sRoles s)) r
  | EMS_And es         => forallb (exprMatchSubjectEvalF s) es
  | EMS_Or es          => existsb (exprMatchSubjectEvalF s) es
  end.

(** The evaluation function for subject match expressions as a relation. *)
Inductive exprMatchSubjectEvalR (s : subject) : exprMatchSubject -> Prop :=
  | EMSR_True :
      exprMatchSubjectEvalR s EMS_True
  | EMSR_WithRolesAll :
    forall (r : RoleSets.t),
      RoleSets.Subset r (sRoles s) ->
        exprMatchSubjectEvalR s (EMS_WithRolesAll r)
  | EMSR_WithRolesAny :
    forall (r : RoleSets.t),
      (exists x, RoleSets.In x r /\ RoleSets.In x (sRoles s)) ->
        exprMatchSubjectEvalR s (EMS_WithRolesAny r)
  | EMSR_And :
    forall (es : list exprMatchSubject),
      Forall (exprMatchSubjectEvalR s) es ->
        exprMatchSubjectEvalR s (EMS_And es)
  | EMSR_Or :
    forall (e : exprMatchSubject) (es : list exprMatchSubject),
      Exists (exprMatchSubjectEvalR s) (e :: es) ->
        exprMatchSubjectEvalR s (EMS_Or (e :: es))
  .

(** Implication lifted into the Forall structure. *)
Lemma Forall_impl_lifted : forall
  (A  : Type)
  (P  : A -> Prop)
  (Q  : A -> Prop)
  (xs : list A),
  Forall (fun x => P x) xs ->
    Forall (fun x => P x -> Q x) xs ->
      Forall (fun x => Q x) xs.
Proof.
  induction xs as [|y ys IH]. {
    intros F0 H1.
    constructor.
  } {
    intros F0 F1.
    constructor. {
      apply (Forall_inv F1).
      apply (Forall_inv F0).
    } {
      apply IH.
      apply (Forall_inv_tail F0).
      apply (Forall_inv_tail F1).
    }
  }
Qed.

Lemma exprMatchSubjectEvalEquivalent_FR_T : forall s e,
  true = exprMatchSubjectEvalF s e -> exprMatchSubjectEvalR s e.
Proof.
  intros s e.
  induction e as [
    |
    |
    |
    |es Hes
    |es Hes
  ] using exprMatchSubject_extendedInd. {
    (* EMS_False *)
    intros Ht.
    inversion Ht.
  } {
    (* EMS_True *)
    intros Ht.
    constructor.
  } {
    (* EMS_WithRolesAll *)
    intros Ht.
    unfold exprMatchSubjectEvalF in Ht.
    constructor.
    apply RoleSets.subset_2.
    intuition.
  } {
    (* EMS_WithRolesAny *)
    intros Ht.
    unfold exprMatchSubjectEvalF in Ht.
    constructor.
    symmetry in Ht.

    assert (
      SetoidList.compat_bool
        RoleSets.E.eq (fun x : RoleSets.elt => RoleSets.mem x (sRoles s))
    ) as Hsetcomp. {
      unfold SetoidList.compat_bool.
      unfold Morphisms.Proper.
      unfold Morphisms.respectful.
      intros x y Heq.
      rewrite Heq.
      reflexivity.
    }

    pose proof (RoleSets.exists_2 Hsetcomp Ht) as [x [H0 H1]].
    exists x.
    intuition.
  } {
    (* EMS_And *)
    destruct es as [|y ys]. {
      intros Ht.
      constructor.
      constructor.
    } {
      simpl.
      intros Ht.

      (* We need to show that the relation holds for all (y :: ys). *)
      assert (Forall (exprMatchSubjectEvalR s) (y :: ys)) as H0. {
        (* We do this by showing it holds for y... *)
        assert (exprMatchSubjectEvalR s y) as H1. {
          symmetry in Ht.
          rewrite Bool.andb_true_iff in Ht.
          rewrite forallb_forall in Ht.
          destruct Ht as [HT0 HT1].
          rewrite <- (@Forall_forall exprMatchSubject _ ys) in HT1.

          apply (Forall_inv Hes).
          symmetry.
          exact HT0.
        }

        (* ... And for all ys. *)
        assert (Forall (exprMatchSubjectEvalR s) ys) as H2. {
          symmetry in Ht.
          rewrite Bool.andb_true_iff in Ht.
          rewrite forallb_forall in Ht.
          destruct Ht as [HT0 HT1].
          rewrite <- (@Forall_forall exprMatchSubject _ ys) in HT1.

          assert (Forall (fun x : exprMatchSubject => true = exprMatchSubjectEvalF s x) ys) as H2. {
            rewrite Forall_forall.
            symmetry.
            generalize dependent x.
            rewrite <- Forall_forall.
            exact HT1.
          }

          pose proof (Forall_inv_tail Hes) as HesT.
          apply (Forall_impl_lifted _ _ _ ys H2 HesT).
        }

        (* ... And then composing the two. *)
        constructor.
        exact H1.
        exact H2.
      }

      constructor.
      exact H0.
    }
  } {
    (* EMS_Or *)
    destruct es as [|y ys]. {
      intros Ht.
      contradict Ht. simpl. discriminate.
    } {
      intros Ht.

      (* We need to show that the relation holds for y or something in ys. *)
      constructor.

      simpl in Ht.
      symmetry in Ht.
      destruct (Bool.orb_true_elim _ _ Ht) as [HtL|HtR]. {
        constructor.
        apply (Forall_inv Hes).
        auto.
      } {
        assert (Exists (exprMatchSubjectEvalR s) (y :: ys)) as H0. {
          rewrite existsb_exists in HtR.
          destruct HtR as [k [Htk0 Htk1]].
          rewrite Forall_forall in Hes.
          pose proof (in_cons y k ys Htk0) as H0.
          pose proof (Hes k H0 (eq_sym Htk1)) as H1.
          apply Exists_cons_tl.
          rewrite Exists_exists.
          exists k.
          auto.
        }
        exact H0.
      }
    }
  }
Qed.

Lemma  exprMatchSubjectEvalEquivalent_RF_T : forall s e,
  exprMatchSubjectEvalR s e -> true = exprMatchSubjectEvalF s e.
Proof.
  intros s e.
  induction e as [
    |
    |
    |
    |es Hes
    |es Hes
  ] using exprMatchSubject_extendedInd. {
    (* EMS_False *)
    intros Ht.
    inversion Ht.
  } {
    (* EMS_True *)
    intros Ht.
    reflexivity.
  } {
    (* EMS_WithRolesAll *)
    intros Ht.
    symmetry.
    apply RoleSets.subset_1.
    inversion Ht.
    intuition.
  } {
    (* EMS_WithRolesAny *)
    intros Ht.
    symmetry.
    inversion Ht as [ | |s0 Hexist Heq| | ].
    subst s0.
    simpl.
    assert (
      RoleSets.Exists
        (fun x : RoleSets.elt => RoleSets.mem x (sRoles s) = true) r
    ) as Hex. {
      unfold RoleSets.Exists.
      destruct Hexist as [y [Hy0 Hy1]].
      exists y.
      intuition.
    }

    assert (
      SetoidList.compat_bool
        RoleSets.E.eq (fun x : RoleSets.elt => RoleSets.mem x (sRoles s))
    ) as Hsetcomp. {
      unfold SetoidList.compat_bool.
      unfold Morphisms.Proper.
      unfold Morphisms.respectful.
      intros x y Heq.
      rewrite Heq.
      reflexivity.
    }

    apply (RoleSets.exists_1 Hsetcomp Hex).
  } {
    (* EMS_And *)
    intros Ht.
    inversion Ht as [ | | |es0 Hfa Heq|].
    subst es0.
    simpl.
    symmetry.
    rewrite forallb_forall.
    intros x Hin.
    symmetry.
    generalize dependent x.
    rewrite <- Forall_forall.
    apply (Forall_impl_lifted exprMatchSubject _ _ es Hfa Hes).
  } {
    (* EMS_Or *)
    intros Ht.
    symmetry.
    simpl.
    rewrite existsb_exists.

    inversion Ht as [ | | | |e es0 Hex Heq].
    subst es.
    destruct Hex as [k ks Hk|k ks Hk]. {
      exists k.
      constructor.
      constructor; reflexivity.
      apply (eq_sym (Forall_inv Hes Hk)).
    } {
      rewrite Exists_exists in Hk.
      destruct Hk as [q [Hq0 Hq1]].
      exists q.
      constructor.
      apply (in_cons k q ks Hq0).
      pose proof (Forall_inv_tail Hes) as HesT.
      rewrite Forall_forall in HesT.
      apply (eq_sym (HesT q Hq0 Hq1)).
    }
  }
Qed.

(** The evaluation function and the evaluation relation are equivalent. *)
Theorem exprMatchSubjectEvalEquivalentT : forall s e,
  true = exprMatchSubjectEvalF s e <-> exprMatchSubjectEvalR s e.
Proof.
  split.
  apply exprMatchSubjectEvalEquivalent_FR_T.
  apply exprMatchSubjectEvalEquivalent_RF_T.
Qed.

Lemma exprMatchSubjectEvalEquivalent_FR_F : forall s e,
  false = exprMatchSubjectEvalF s e -> ~exprMatchSubjectEvalR s e.
Proof.
  intros s e.
  induction e as [
    |
    |
    |
    |es Hes
    |es Hes
  ] using exprMatchSubject_extendedInd. {
    (* EMS_False *)
    intros Ht.
    intro Hcontra.
    inversion Hcontra.
  } {
    (* EMS_True *)
    intros Ht.
    contradict Ht.
    discriminate.
  } {
    (* EMS_WithRolesAll *)
    intros Ht.
    intros Hcontra.
    rewrite <- (exprMatchSubjectEvalEquivalent_RF_T _ _ Hcontra) in Ht.
    contradict Ht; discriminate.
  } {
    (* EMS_WithRolesAny *)
    intros Ht.
    intros Hcontra.
    rewrite <- (exprMatchSubjectEvalEquivalent_RF_T _ _ Hcontra) in Ht.
    contradict Ht; discriminate.
  } {
    (* EMS_And *)
    intros Ht.
    intros Hcontra.
    rewrite <- (exprMatchSubjectEvalEquivalent_RF_T _ _ Hcontra) in Ht.
    contradict Ht; discriminate.
  } {
    (* EMS_Or *)
    intros Ht.
    intros Hcontra.
    rewrite <- (exprMatchSubjectEvalEquivalent_RF_T _ _ Hcontra) in Ht.
    contradict Ht; discriminate.
  }
Qed.

Lemma exprMatchSubjectEvalEquivalent_RF_F : forall s e,
  ~exprMatchSubjectEvalR s e -> false = exprMatchSubjectEvalF s e.
Proof.
  intros s e.
  induction e as [
    |
    |
    |
    |es Hes
    |es Hes
  ] using exprMatchSubject_extendedInd. {
    (* EMS_False *)
    intros Ht.
    reflexivity.
  } {
    (* EMS_True *)
    intros Ht.
    contradict Ht.
    constructor.
  } {
    (* EMS_WithRolesAll *)
    intros Ht.
    simpl.
    assert (~RoleSets.Subset r (sRoles s)) as Hns. {
      intros Hcontra.
      apply Ht.
      constructor.
      exact Hcontra.
    }
    symmetry.
    rewrite <- roleSubsetFalse.
    intuition.
  } {
    (* EMS_WithRolesAny *)
    intros Ht.
    symmetry.
    intuition.
    simpl.

    assert (
      SetoidList.compat_bool
        RoleSets.E.eq (fun x : RoleSets.elt => RoleSets.mem x (sRoles s))
    ) as Hsetcomp. {
      unfold SetoidList.compat_bool.
      unfold Morphisms.Proper.
      unfold Morphisms.respectful.
      intros x y Heq.
      rewrite Heq.
      reflexivity.
    }

    rewrite <- (roleExistsFalse r _ Hsetcomp).
    intro Hcontra.
    apply Ht.
    constructor.
    inversion Hcontra as [z [Hz0 Hz1]].
    exists z.
    intuition.
  } {
    (* EMS_And *)
    intros Ht.
    destruct (exprMatchSubjectEvalF s (EMS_And es)) eqn:H. {
      symmetry in H.
      rewrite exprMatchSubjectEvalEquivalentT in H.
      contradiction.
    } {
      reflexivity.
    }
  } {
    (* EMS_Or *)
    intros Ht.
    destruct (exprMatchSubjectEvalF s (EMS_Or es)) eqn:H. {
      symmetry in H.
      rewrite exprMatchSubjectEvalEquivalentT in H.
      contradiction.
    } {
      reflexivity.
    }
  }
Qed.

(** The evaluation function and the evaluation relation are equivalent. *)
Theorem exprMatchSubjectEvalEquivalentF : forall s e,
  false = exprMatchSubjectEvalF s e <-> ~exprMatchSubjectEvalR s e.
Proof.
  split.
  apply exprMatchSubjectEvalEquivalent_FR_F.
  apply exprMatchSubjectEvalEquivalent_RF_F.
Qed.

(** The evaluation relation is decidable. *)
Theorem exprMatchSubjectEvalRDec : forall s e,
  {exprMatchSubjectEvalR s e}+{~exprMatchSubjectEvalR s e}.
Proof.
  intros s e.
  destruct (exprMatchSubjectEvalF s e) eqn:Hev. {
    symmetry in Hev.
    rewrite exprMatchSubjectEvalEquivalentT in Hev.
    left; intuition.
  } {
    symmetry in Hev.
    rewrite exprMatchSubjectEvalEquivalentF in Hev.
    right; intuition.
  }
Qed.

(** An expression that matches an action. *)
Inductive exprMatchAction : Type :=
  | EMA_False : exprMatchAction
  | EMA_True : exprMatchAction
  | EMA_WithName :
    forall (n : actionName),
      exprMatchAction
  | EMA_And :
    exprMatchAction ->
      exprMatchAction ->
        exprMatchAction
  | EMA_Or :
    exprMatchAction ->
      exprMatchAction ->
        exprMatchAction
  .

(** An evaluation function for action match expressions. *)
Fixpoint exprMatchActionEvalF
  (a : action)
  (e : exprMatchAction)
: bool :=
  match e with
  | EMA_False => false
  | EMA_True => true
  | EMA_WithName n =>
    eqb (ivName (aName a)) (ivName n)
  | EMA_And x y =>
    andb (exprMatchActionEvalF a x) (exprMatchActionEvalF a y)
  | EMA_Or x y =>
    orb (exprMatchActionEvalF a x) (exprMatchActionEvalF a y)
  end.

(** The evaluation function for action match expressions as a relation. *)
Inductive exprMatchActionEvalR : action -> exprMatchAction -> Prop :=
  | EMAR_True :
    forall (a : action),
      exprMatchActionEvalR a EMA_True
  | EMAR_WithName :
    forall (a : action) (x : actionName),
      ivName (aName a) = ivName x ->
        exprMatchActionEvalR a (EMA_WithName x)
  | EMAR_And :
    forall (a : action) (e0 e1 : exprMatchAction),
      exprMatchActionEvalR a e0 /\ exprMatchActionEvalR a e1 ->
        exprMatchActionEvalR a (EMA_And e0 e1)
  | EMAR_Or :
    forall (a : action) (e0 e1 : exprMatchAction),
      exprMatchActionEvalR a e0 \/ exprMatchActionEvalR a e1 ->
        exprMatchActionEvalR a (EMA_Or e0 e1)
  .

(** The evaluation function and the evaluation relation are equivalent. *)
Theorem exprMatchActionEvalEquivalentT : forall s e,
  true = exprMatchActionEvalF s e <-> exprMatchActionEvalR s e.
Proof.
  intros a e.
  induction e as [
    |
    |r
    |e0 He0 e1 He1
    |e0 He0 e1 He1
  ]. {
    (* EMA_False *)
    split. {
      intros Ht.
      inversion Ht.
    } {
      intros Ht.
      inversion Ht.
    }
  } {
    (* EMA_True *)
    split. {
      intros Ht; constructor.
    } {
      intros Ht; reflexivity.
    }
  } {
    (* EMA_WithName *)
    split. {
      intros Ht.
      unfold exprMatchActionEvalF in Ht.
      symmetry in Ht.
      rewrite eqb_eq in Ht.
      pose proof (ivIrrelevantEqual _ _ Ht).
      subst r.
      constructor.
      intuition.
    } {
      intros Ht.
      simpl.
      inversion Ht as [ |y z Hyz| | ].
      subst y.
      subst z.
      pose proof (ivIrrelevantEqual _ _ Hyz) as H0.
      rewrite H0.
      symmetry.
      apply eqb_refl.
    }
  } {
    (* EMA_And *)
    split. {
      intros Ht.
      simpl in Ht.
      pose proof (Bool.andb_true_eq _ _ Ht) as [HT0 HT1].
      constructor.
      intuition.
    } {
      intros Ht.
      inversion Ht as [ | |a0 e2 e3 He| ].
      subst a0.
      subst e2.
      subst e3.
      rewrite <- He0 in He.
      rewrite <- He1 in He.
      symmetry.
      simpl.
      rewrite Bool.andb_true_iff.
      intuition.
    }
  } {
    (* EMA_Or *)
    split. {
      intros Ht.
      constructor.
      simpl in Ht.
      symmetry in Ht.
      pose proof (Bool.orb_prop _ _ Ht) as Hb.
      destruct Hb as [Hb0|Hb1]. {
        symmetry in Hb0.
        rewrite He0 in Hb0.
        intuition.
      } {
        symmetry in Hb1.
        rewrite He1 in Hb1.
        intuition.
      }
    } {
      intros Ht.
      simpl.
      symmetry.
      rewrite Bool.orb_true_iff.
      inversion Ht as [ | | |a0 e2 e3 He].
      subst a0.
      subst e2.
      subst e3.
      intuition.
    }
  }
Qed.

(** The evaluation function and the evaluation relation are equivalent. *)
Theorem exprMatchActionEvalEquivalentF : forall a e,
  false = exprMatchActionEvalF a e <-> ~exprMatchActionEvalR a e.
Proof.
  intros a e.
  induction e as [
    |
    |r
    |e0 He0 e1 He1
    |e0 He0 e1 He1
  ]. {
    (* EMA_False *)
    split. {
      intros H Ht; inversion Ht.
    } {
      intros H; reflexivity.
    }
  } {
    (* EMA_True *)
    split. {
      intros H Ht.
      contradict H; discriminate.
    } {
      intros H.
      contradict H; constructor.
    }
  } {
    (* EMA_WithName *)
    split. {
      intros H Ht.
      inversion Ht as [ |o1 t1 Heq| | ].
      subst o1.
      subst t1.
      pose proof (ivIrrelevantEqual _ _ Heq) as Hir.
      subst r.
      contradict H.
      simpl.
      rewrite eqb_refl.
      discriminate.
    } {
      intros H.
      destruct (exprMatchActionEvalF a (EMA_WithName r)) eqn:Hd. {
        simpl in Hd.
        rewrite eqb_eq in Hd.
        pose proof (@ivIrrelevantEqual actionName _ _ _ Hd) as Heq.
        subst r.
        assert (
          exprMatchActionEvalR a (EMA_WithName (aName a))
        ) as Hcontra. {
          constructor.
          reflexivity.
        }
        contradiction.
      } {
        reflexivity.
      }
    }
  } {
    (* EMA_And *)
    split. {
      intros Ht.
      intros Hcontra.
      inversion Hcontra as [ | |a1 e2 e3 [Hf0 Hf1]| ].
      subst a1.
      subst e2.
      subst e3.
      simpl in Ht.
      destruct (Bool.andb_false_elim _ _ (eq_sym Ht)); intuition.
    } {
      intros Ht.
      destruct (exprMatchActionEvalF a (EMA_And e0 e1)) eqn:H. {
        symmetry in H.
        rewrite exprMatchActionEvalEquivalentT in H.
        contradiction.
      } {
        reflexivity.
      }
    }
  } {
    (* EMA_Or *)
    split. {
      intros Ht.
      intros Hcontra.
      inversion Hcontra as [ | | |a1 e2 e3 [Hf0|Hf1]].
      subst a1.
      subst e2.
      subst e3.
      simpl in Ht.
      destruct (Bool.orb_false_elim _ _ (eq_sym Ht)) as [Hk0 Hk1]. {
        symmetry in Hk0.
        rewrite He0 in Hk0.
        contradiction.
      }
      subst a1.
      subst e2.
      subst e3.
      simpl in Ht.
      destruct (Bool.orb_false_elim _ _ (eq_sym Ht)) as [Hk0 Hk1]. {
        symmetry in Hk1.
        rewrite He1 in Hk1.
        contradiction.
      }
    } {
      intros Ht.
      destruct (exprMatchActionEvalF a (EMA_Or e0 e1)) eqn:H. {
        symmetry in H.
        rewrite exprMatchActionEvalEquivalentT in H.
        contradiction.
      } {
        reflexivity.
      }
    }
  }
Qed.

(** The evaluation relation is decidable. *)
Theorem exprMatchActionEvalRDec : forall a e,
  {exprMatchActionEvalR a e}+{~exprMatchActionEvalR a e}.
Proof.
  intros a e.
  destruct (exprMatchActionEvalF a e) eqn:Hev. {
    symmetry in Hev.
    rewrite exprMatchActionEvalEquivalentT in Hev.
    left; intuition.
  } {
    symmetry in Hev.
    rewrite exprMatchActionEvalEquivalentF in Hev.
    right; intuition.
  }
Qed.

(** An expression that matches an object. *)
Inductive exprMatchObject : Type :=
  | EMO_False : exprMatchObject
  | EMO_True : exprMatchObject
  | EMO_WithType :
    forall (n : typeName),
      exprMatchObject
  | EMO_And :
    exprMatchObject ->
      exprMatchObject ->
        exprMatchObject
  | EMO_Or :
    exprMatchObject ->
      exprMatchObject ->
        exprMatchObject
  .

(** An evaluation function for object match expressions. *)
Fixpoint exprMatchObjectEvalF
  (o : object)
  (e : exprMatchObject)
: bool :=
  match e with
  | EMO_False => false
  | EMO_True => true
  | EMO_WithType n =>
    eqb (ivName (oType o)) (ivName n)
  | EMO_And x y =>
    andb (exprMatchObjectEvalF o x) (exprMatchObjectEvalF o y)
  | EMO_Or x y =>
    orb (exprMatchObjectEvalF o x) (exprMatchObjectEvalF o y)
  end.

(** The evaluation function for object match expressions as a relation. *)
Inductive exprMatchObjectEvalR : object -> exprMatchObject -> Prop :=
  | EMOR_True :
    forall (o : object),
      exprMatchObjectEvalR o EMO_True
  | EMOR_WithName :
    forall (o : object) (t : typeName),
      ivName (oType o) = ivName t ->
        exprMatchObjectEvalR o (EMO_WithType t)
  | EMOR_And :
    forall (o : object) (e0 e1 : exprMatchObject),
      exprMatchObjectEvalR o e0 /\ exprMatchObjectEvalR o e1 ->
        exprMatchObjectEvalR o (EMO_And e0 e1)
  | EMOR_Or :
    forall (o : object) (e0 e1 : exprMatchObject),
      exprMatchObjectEvalR o e0 \/ exprMatchObjectEvalR o e1 ->
        exprMatchObjectEvalR o (EMO_Or e0 e1)
  .

(** The evaluation function and the evaluation relation are equivalent. *)
Theorem exprMatchObjectEvalEquivalentT : forall s e,
  true = exprMatchObjectEvalF s e <-> exprMatchObjectEvalR s e.
Proof.
  intros o e.
  induction e as [
    |
    |r
    |e0 He0 e1 He1
    |e0 He0 e1 He1
  ]. {
    (* EMO_False *)
    split. {
      intros Ht.
      inversion Ht.
    } {
      intros Ht.
      inversion Ht.
    }
  } {
    (* EMO_True *)
    split. {
      intros Ht; constructor.
    } {
      intros Ht; reflexivity.
    }
  } {
    (* EMO_WithType *)
    split. {
      intros Ht.
      unfold exprMatchObjectEvalF in Ht.
      symmetry in Ht.
      rewrite eqb_eq in Ht.
      pose proof (ivIrrelevantEqual _ _ Ht).
      subst r.
      constructor.
      intuition.
    } {
      intros Ht.
      simpl.
      inversion Ht as [ |y z Hyz| | ].
      subst y.
      subst z.
      pose proof (ivIrrelevantEqual _ _ Hyz) as H0.
      rewrite H0.
      symmetry.
      apply eqb_refl.
    }
  } {
    (* EMO_And *)
    split. {
      intros Ht.
      simpl in Ht.
      pose proof (Bool.andb_true_eq _ _ Ht) as [HT0 HT1].
      constructor.
      intuition.
    } {
      intros Ht.
      inversion Ht as [ | |a0 e2 e3 He| ].
      subst a0.
      subst e2.
      subst e3.
      rewrite <- He0 in He.
      rewrite <- He1 in He.
      symmetry.
      simpl.
      rewrite Bool.andb_true_iff.
      intuition.
    }
  } {
    (* EMO_Or *)
    split. {
      intros Ht.
      constructor.
      simpl in Ht.
      symmetry in Ht.
      pose proof (Bool.orb_prop _ _ Ht) as Hb.
      destruct Hb as [Hb0|Hb1]. {
        symmetry in Hb0.
        rewrite He0 in Hb0.
        intuition.
      } {
        symmetry in Hb1.
        rewrite He1 in Hb1.
        intuition.
      }
    } {
      intros Ht.
      simpl.
      symmetry.
      rewrite Bool.orb_true_iff.
      inversion Ht as [ | | |a0 e2 e3 He].
      subst a0.
      subst e2.
      subst e3.
      intuition.
    }
  }
Qed.

(** The evaluation function and the evaluation relation are equivalent. *)
Theorem exprMatchObjectEvalEquivalentF : forall s e,
  false = exprMatchObjectEvalF s e <-> ~exprMatchObjectEvalR s e.
Proof.
  intros o e.
  induction e as [
    |
    |r
    |e0 He0 e1 He1
    |e0 He0 e1 He1
  ]. {
    (* EMO_False *)
    split. {
      intros H Ht; inversion Ht.
    } {
      intros H; reflexivity.
    }
  } {
    (* EMO_True *)
    split. {
      intros H Ht.
      contradict H; discriminate.
    } {
      intros H.
      contradict H; constructor.
    }
  } {
    (* EMO_WithType *)
    split. {
      intros H Ht.
      inversion Ht as [ |o1 t1 Heq| | ].
      subst o1.
      subst t1.
      pose proof (ivIrrelevantEqual _ _ Heq) as Hir.
      subst r.
      contradict H.
      simpl.
      rewrite eqb_refl.
      discriminate.
    } {
      intros H.
      destruct (exprMatchObjectEvalF o (EMO_WithType r)) eqn:Hd. {
        simpl in Hd.
        rewrite eqb_eq in Hd.
        pose proof (ivIrrelevantEqual _ _ Hd) as Heq.
        subst r.
        assert (
          exprMatchObjectEvalR o (EMO_WithType (oType o))
        ) as Hcontra. {
          constructor.
          reflexivity.
        }
        contradiction.
      } {
        reflexivity.
      }
    }
  } {
    (* EMO_And *)
    split. {
      intros Ht.
      intros Hcontra.
      inversion Hcontra as [ | |o1 e2 e3 [Hf0 Hf1]| ].
      subst o1.
      subst e2.
      subst e3.
      simpl in Ht.
      destruct (Bool.andb_false_elim _ _ (eq_sym Ht)); intuition.
    } {
      intros Ht.
      destruct (exprMatchObjectEvalF o (EMO_And e0 e1)) eqn:H. {
        symmetry in H.
        rewrite exprMatchObjectEvalEquivalentT in H.
        contradiction.
      } {
        reflexivity.
      }
    }
  } {
    (* EMO_Or *)
    split. {
      intros Ht.
      intros Hcontra.
      inversion Hcontra as [ | | |o1 e2 e3 [Hf0|Hf1]].
      subst o1.
      subst e2.
      subst e3.
      simpl in Ht.
      destruct (Bool.orb_false_elim _ _ (eq_sym Ht)) as [Hk0 Hk1]. {
        symmetry in Hk0.
        rewrite He0 in Hk0.
        contradiction.
      }
      subst o1.
      subst e2.
      subst e3.
      simpl in Ht.
      destruct (Bool.orb_false_elim _ _ (eq_sym Ht)) as [Hk0 Hk1]. {
        symmetry in Hk1.
        rewrite He1 in Hk1.
        contradiction.
      }
    } {
      intros Ht.
      destruct (exprMatchObjectEvalF o (EMO_Or e0 e1)) eqn:H. {
        symmetry in H.
        rewrite exprMatchObjectEvalEquivalentT in H.
        contradiction.
      } {
        reflexivity.
      }
    }
  }
Qed.

(** The evaluation relation is decidable. *)
Theorem exprMatchObjectEvalRDec : forall o e,
  {exprMatchObjectEvalR o e}+{~exprMatchObjectEvalR o e}.
Proof.
  intros o e.
  destruct (exprMatchObjectEvalF o e) eqn:Hev. {
    symmetry in Hev.
    rewrite exprMatchObjectEvalEquivalentT in Hev.
    left; intuition.
  } {
    symmetry in Hev.
    rewrite exprMatchObjectEvalEquivalentF in Hev.
    right; intuition.
  }
Qed.
