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

Require Import Medrina.Objects.
Require Import Medrina.Subjects.
Require Import Medrina.Actions.
Require Import Medrina.Matches.
Require Import Medrina.Names.

Require Import Coq.Strings.String.

(** The conclusion for a rule, if the rule matches. *)
Inductive ruleConclusion : Set :=
  (** Allow access and continue evaluating rules. *)
  | RC_Allow
  (** Allow access and halt evaluation. *)
  | RC_AllowImmediately
  (** Deny access and continue evaluating rules. *)
  | RC_Deny
  (** Deny access and halt evaluation. *)
  | RC_DenyImmediately
  .

(** Rule conclusion equality is decidable. *)
Theorem ruleConclusionDec : forall (x y : ruleConclusion), {x = y}+{~x = y}.
Proof. decide equality. Qed.

(** A single rule in a policy. *)
Record rule := Rule {
  (** The rule conclusion. *)
  rConclusion   : ruleConclusion;
  (** The expression that matches a subject. *)
  rMatchSubject : exprMatchSubject;
  (** The expression that matches an object. *)
  rMatchObject  : exprMatchObject;
  (** The expression that matches a subject. *)
  rMatchAction  : exprMatchAction;
  (** The rule name. *)
  rName         : string;
  rNameValid    : validName rName;
  (** The rule description. *)
  rDescription  : string;
}.

(** A function that determines if a rule matches. *)
Definition ruleMatchesF
  (s : subject)
  (o : object)
  (a : action)
  (r : rule)
: bool :=
  let sm := exprMatchSubjectEvalF s (rMatchSubject r) in
  let om := exprMatchObjectEvalF o (rMatchObject r) in
  let am := exprMatchActionEvalF a (rMatchAction r) in
    andb (andb sm om) am.

(** The rule matching relation. *)
Inductive ruleMatchesR : subject -> object -> action -> rule -> Prop :=
  RM_Matches : forall s o a r,
    exprMatchSubjectEvalR s (rMatchSubject r) ->
      exprMatchObjectEvalR o (rMatchObject r) ->
        exprMatchActionEvalR a (rMatchAction r) ->
          ruleMatchesR s o a r.

(** The match function and relation are equivalent. *)
Theorem ruleMatchesFEquivalentT : forall s o a r,
  ruleMatchesF s o a r = true <-> ruleMatchesR s o a r.
Proof.
  intros s o a r.
  split. {
    intros Hm.
    unfold ruleMatchesF in Hm.
    rewrite Bool.andb_true_iff in Hm.
    rewrite Bool.andb_true_iff in Hm.
    destruct Hm as [[Hm0 Hm1] Hm2].
    symmetry in Hm0.
    symmetry in Hm1.
    symmetry in Hm2.
    rewrite exprMatchSubjectEvalEquivalentT in Hm0.
    rewrite exprMatchObjectEvalEquivalentT in Hm1.
    rewrite exprMatchActionEvalEquivalentT in Hm2.
    constructor; auto.
  } {
    intros Hm.
    inversion Hm as [x0 x1 x2 x3 H0 H1 H2].
    subst x0.
    subst x1.
    subst x2.
    subst x3.
    rewrite <- exprMatchSubjectEvalEquivalentT in H0.
    rewrite <- exprMatchObjectEvalEquivalentT in H1.
    rewrite <- exprMatchActionEvalEquivalentT in H2.
    unfold ruleMatchesF.
    intuition.
  }
Qed.

(** The match function and relation are equivalent. *)
Theorem ruleMatchesFEquivalentF : forall s o a r,
  ruleMatchesF s o a r = false <-> ~ruleMatchesR s o a r.
Proof.
  intros s o a r.
  split. {
    intros Hm.
    unfold ruleMatchesF in Hm.
    rewrite Bool.andb_false_iff in Hm.
    rewrite Bool.andb_false_iff in Hm.
    destruct Hm as [[Hm0|Hm1]|Hm2]. {
      intros Hnot.
      inversion Hnot as [x0 x1 x2 x3 H0 H1 H2].
      subst x0.
      subst x1.
      subst x2.
      subst x3.
      rewrite <- exprMatchSubjectEvalEquivalentT in H0.
      rewrite <- H0 in Hm0.
      contradict Hm0; discriminate.
    } {
      intros Hnot.
      inversion Hnot as [x0 x1 x2 x3 H0 H1 H2].
      subst x0.
      subst x1.
      subst x2.
      subst x3.
      rewrite <- exprMatchObjectEvalEquivalentT in H1.
      rewrite <- H1 in Hm1.
      contradict Hm1; discriminate.
    } {
      intros Hnot.
      inversion Hnot as [x0 x1 x2 x3 H0 H1 H2].
      subst x0.
      subst x1.
      subst x2.
      subst x3.
      rewrite <- exprMatchActionEvalEquivalentT in H2.
      rewrite <- H2 in Hm2.
      contradict Hm2; discriminate.
    }
  } {
    intros Hnot.
    unfold ruleMatchesF.
    rewrite Bool.andb_false_iff.
    rewrite Bool.andb_false_iff.
    destruct (exprMatchSubjectEvalF s (rMatchSubject r)) eqn:H0. {
      destruct (exprMatchObjectEvalF o (rMatchObject r)) eqn:H1. {
        destruct (exprMatchActionEvalF a (rMatchAction r)) eqn:H2. {
          symmetry in H0.
          symmetry in H1.
          symmetry in H2.
          rewrite exprMatchSubjectEvalEquivalentT in H0.
          rewrite exprMatchObjectEvalEquivalentT in H1.
          rewrite exprMatchActionEvalEquivalentT in H2.
          assert (ruleMatchesR s o a r) as Hcontra. {
            constructor; intuition.
          }
          contradiction.
        } {
          intuition.
        }
      } {
        intuition.
      }
    } {
      intuition.
    }
  }
Qed.

(** The match relation is decidable. *)
Theorem ruleMatchesDec : forall s o a r,
  {ruleMatchesR s o a r}+{~ruleMatchesR s o a r}.
Proof.
  intros s o a r.
  destruct (ruleMatchesF s o a r) eqn:Hm. {
    rewrite ruleMatchesFEquivalentT in Hm.
    left; intuition.
  } {
    rewrite ruleMatchesFEquivalentF in Hm.
    right; intuition.
  }
Qed.
