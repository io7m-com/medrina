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

Require Import Medrina.Actions.
Require Import Medrina.Names.
Require Import Medrina.Subjects.
Require Import Medrina.Roles.
Require Import Medrina.Objects.

(** An expression that matches a subject. *)
Inductive exprMatchSubject : Type :=
  | EMS_False : exprMatchSubject
  | EMS_True : exprMatchSubject
  | EMS_WithRolesAll :
    forall (r : RoleSets.t),
      exprMatchSubject
  | EMS_WithRolesAny :
    forall (r : RoleSets.t),
      exprMatchSubject
  | EMS_And :
    exprMatchSubject ->
      exprMatchSubject ->
        exprMatchSubject
  | EMS_Or :
    exprMatchSubject ->
      exprMatchSubject ->
        exprMatchSubject
  .

(** An evaluation function for subject match expressions. *)
Fixpoint exprMatchSubjectEvalF
  (s : subject)
  (e : exprMatchSubject)
: bool :=
  match e with
  | EMS_False => false
  | EMS_True => true
  | EMS_WithRolesAll r =>
    RoleSets.subset r (sRoles s)
  | EMS_WithRolesAny r =>
    RoleSets.exists_ (fun x => RoleSets.mem x (sRoles s)) r
  | EMS_And x y =>
    andb (exprMatchSubjectEvalF s x) (exprMatchSubjectEvalF s y)
  | EMS_Or x y =>
    orb (exprMatchSubjectEvalF s x) (exprMatchSubjectEvalF s y)
  end.

(** The evaluation function for subject match expressions as a relation. *)
Inductive exprMatchSubjectEvalR : subject -> exprMatchSubject -> Prop :=
  | EMSR_True :
    forall (s : subject),
      exprMatchSubjectEvalR s EMS_True
  | EMSR_WithRolesAll :
    forall (s : subject) (r : RoleSets.t),
      RoleSets.Subset r (sRoles s) ->
        exprMatchSubjectEvalR s (EMS_WithRolesAll r)
  | EMSR_WithRolesAny :
    forall (s : subject) (r : RoleSets.t),
      (exists x, RoleSets.In x r /\ RoleSets.In x (sRoles s)) ->
        exprMatchSubjectEvalR s (EMS_WithRolesAny r)
  | EMSR_And :
    forall (s : subject) (e0 e1 : exprMatchSubject),
      exprMatchSubjectEvalR s e0 /\ exprMatchSubjectEvalR s e1 ->
        exprMatchSubjectEvalR s (EMS_And e0 e1)
  | EMSR_Or :
    forall (s : subject) (e0 e1 : exprMatchSubject),
      exprMatchSubjectEvalR s e0 \/ exprMatchSubjectEvalR s e1 ->
        exprMatchSubjectEvalR s (EMS_Or e0 e1)
  .

(** The evaluation function and the evaluation relation are equivalent. *)
Theorem exprMatchSubjectEvalEquivalent : forall s e,
  true = exprMatchSubjectEvalF s e <-> exprMatchSubjectEvalR s e.
Proof.
  intros s e.
  induction e as [
    |
    |r
    |r
    |e0 He0 e1 He1
    |e0 He0 e1 He1
  ]. {
    (* EMS_False *)
    split. {
      intros Ht.
      inversion Ht.
    } {
      intros Ht.
      inversion Ht.
    }
  } {
    (* EMS_True *)
    split. {
      intros Ht; constructor.
    } {
      intros Ht; reflexivity.
    }
  } {
    (* EMS_WithRolesAll *)
    split. {
      intros Ht.
      unfold exprMatchSubjectEvalF in Ht.
      constructor.
      apply RoleSets.subset_2.
      intuition.
    } {
      intros Ht.
      symmetry.
      apply RoleSets.subset_1.
      inversion Ht.
      intuition.
    }
  } {
    (* EMS_WithRolesAny *)
    split. {
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
      intros Ht.
      symmetry.
      inversion Ht as [ | |s0 r0 HHt| | ].
      subst s0.
      subst r0.
      simpl.
      assert (
        RoleSets.Exists 
          (fun x : RoleSets.elt => RoleSets.mem x (sRoles s) = true) r
      ) as Hex. {
        unfold RoleSets.Exists.
        destruct HHt as [y [Hy0 Hy1]].
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
    }
  } {
    (* EMS_And *)
    split. {
      intros Ht.
      constructor.
      simpl in Ht.
      pose proof (Bool.andb_true_eq _ _ Ht) as [HT0 HT1].
      intuition.
    } {
      intros Ht.
      inversion Ht as [ | | |s0 e2 e3 He| ].
      subst s0.
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
    (* EMS_Or *)
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
      inversion Ht as [ | | |  |s0 e2 e3 He].
      subst s0.
      subst e2.
      subst e3.
      intuition.
    }
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
Theorem exprMatchActionEvalEquivalent : forall s e,
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

(** An expression that matches an object. *)
Inductive exprMatchObject : Type :=
  | EMO_False : exprMatchObject
  | EMO_True : exprMatchObject
  | EMO_WithName :
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
  | EMO_WithName n =>
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
        exprMatchObjectEvalR o (EMO_WithName t)
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
Theorem exprMatchObjectEvalEquivalent : forall s e,
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
    (* EMO_WithName *)
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
