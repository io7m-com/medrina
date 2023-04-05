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
Require Import Medrina.Names.

(** The type of role names. *)
Record roleName := RNMake {
  (** The name of the role. *)
  rnName  : string;
  (** Role names are valid. *)
  rnValid : validName rnName
}.

Require Import Coq.Logic.ProofIrrelevance.

(** Equality of role names is decidable. *)
Theorem roleNameDec : forall (a b : roleName),
  {a = b}+{a <> b}.
Proof.
  intros a b.
  destruct a as [a0 [a1 [a2 a3]]].
  destruct b as [b0 [b1 [b2 b3]]].
  destruct (string_dec a0 b0) as [H0|H1]. {
    subst b0.
    left.
    assert (a1 = b1) by apply proof_irrelevance. subst b1.
    assert (a2 = b2) by apply proof_irrelevance. subst b2.
    assert (a3 = b3) by apply proof_irrelevance. subst b3.
    intuition.
  } {
    right.
    congruence.
  }
Qed.

Require Import Coq.FSets.FSetInterface.
Require Import Coq.FSets.FSetWeakList.
Require Import Coq.FSets.FSetFacts.
Require Import Coq.Structures.Equalities.

(** A mini decidable type module to instantiate sets. *)
Module RoleNameMiniDec : MiniDecidableType
  with Definition t := roleName.

  Definition t        := roleName.
  Definition eq       := @Logic.eq t.
  Definition eq_refl  := @Logic.eq_refl t.
  Definition eq_sym   := @Logic.eq_sym t.
  Definition eq_trans := @Logic.eq_trans t.

  Theorem eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof. apply roleNameDec. Qed.
End RoleNameMiniDec.

(** A usual decidable type module to instantiate sets. *)
Module RoleNameDec <: UsualDecidableType
  with Definition t := roleName
  with Definition eq := @Logic.eq roleName
:= Make_UDT RoleNameMiniDec.

(** A Maps module with attribute name keys. *)
Module RoleSets : FSetInterface.WS
  with Definition E.t  := roleName
  with Definition E.eq := @Logic.eq roleName
:= FSetWeakList.Make RoleNameDec.

Module RoleSetsFacts :=
  Facts RoleSets.

(** Proof irrelevance allows for equality between instances with equal names. *)
Theorem roleNameIrrelevance : forall (a b : roleName),
  rnName a = rnName b -> a = b.
Proof.
  intros a b Heq.
  destruct a as [a0 a1].
  destruct b as [b0 b1].
  simpl in Heq.
  subst b0.
  assert (a1 = b1) by apply proof_irrelevance.
  subst b1.
  reflexivity.
Qed.

#[export]
Instance roleNameName : IsValidName roleName := {
  ivName            := rnName;
  ivValid           := rnValid;
  ivIrrelevantEqual := roleNameIrrelevance
}.

Theorem roleSubsetFalse : forall (r s : RoleSets.t),
  ~ RoleSets.Subset r s <-> RoleSets.subset r s = false.
Proof.
  intros r s.
  split. {
    intros Hnot.
    destruct (RoleSets.subset r s) eqn:H. {
      rewrite <- RoleSetsFacts.subset_iff in H.
      contradiction.
    } {
      reflexivity.
    }
  } {
    intros Hnot.
    destruct (RoleSets.subset r s) eqn:H. {
      contradict Hnot; discriminate.
    } {
      intro Hfalse.
      rewrite RoleSetsFacts.subset_iff in Hfalse.
      rewrite Hfalse in H.
      contradict H; discriminate.
    }
  }
Qed.

Theorem roleExistsFalse : forall (r : RoleSets.t) (f : RoleSets.elt -> bool),
  compat_bool eq f ->
    ~ RoleSets.Exists (fun x => f x = true) r <-> RoleSets.exists_ f r = false.
Proof.
  intros r f Hf.

  split. {
    intros Hnot.
    intuition.
    destruct (RoleSets.exists_ f r) eqn:H. {
      rewrite <- (RoleSetsFacts.exists_iff r Hf) in H.
      contradiction.
    } {
      reflexivity.
    }
  } {
    intros Hnot.
    intros Hfalse.
    rewrite (RoleSetsFacts.exists_iff _ Hf) in Hfalse.
    rewrite Hfalse in Hnot.
    contradict Hnot.
    discriminate.
  }
Qed.
