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

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Local Open Scope string_scope.

Set Mangle Names.

(** The set of acceptable characters in a name. *)
Definition acceptableCharacters : list Ascii.ascii :=
  list_ascii_of_string "abcdefghijklmnopqrstuvwxyz0123456789_.".

(** A description of a valid name. *)
Definition validName (s : string) : Prop :=
  Forall (fun c => In c acceptableCharacters) (list_ascii_of_string s)
  /\ length s >= 1
  /\ length s <= 256.

(** Whether all characters in a string are valid is decidable. *)
Lemma validNameForall_dec : forall s,
  {Forall (fun c => In c acceptableCharacters) (list_ascii_of_string s)}+
  {~Forall (fun c => In c acceptableCharacters) (list_ascii_of_string s)}.
Proof.
  intros s.
  apply Forall_dec.
  intros c.
  apply in_dec.
  apply Ascii.ascii_dec.
Qed.

(** Whether a string is non-empty is decidable. *)
Lemma validNameLength1_dec : forall s,
  {length s >= 1}+{~length s >= 1}.
Proof.
  intros s.
  apply Compare_dec.ge_dec.
Qed.

(** Whether a string is short enough is decidable. *)
Lemma validNameLength256_dec : forall s,
  {length s <= 256}+{~length s <= 256}.
Proof.
  intros s.
  apply Compare_dec.ge_dec.
Qed.

(** Whether a string is valid is decidable. *)
Theorem validNameDecidable : forall s,
  {validName s}+{~validName s}.
Proof.
  intros s.
  unfold validName.
  destruct (validNameForall_dec s); intuition.
  destruct (validNameLength1_dec s); intuition.
  destruct (validNameLength256_dec s); intuition.
Qed.

(** The class of valid names. *)
Class IsValidName (A : Type) := {
  (** A valid name exposes its contents as a string. *)
  ivName  : A -> string;
  (** A valid name's contents are valid according to _validName_. *)
  ivValid : forall (x : A), validName (ivName x);
  (** Two names with the same contents are equal. *)
  ivIrrelevantEqual : forall (x y : A),
    ivName x = ivName y -> x = y
}.
