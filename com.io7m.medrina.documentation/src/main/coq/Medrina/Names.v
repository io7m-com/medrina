Require Import Coq.Lists.List.
Require Import Coq.Unicode.Utf8_core.
Require Import Coq.Strings.String.
Require Import Coq.Logic.Decidable.

Import ListNotations.

Open Scope string_scope.
Open Scope char_scope.

Set Mangle Names.

Class textual (A : Set) := {
  text_of : A → string
}.

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
