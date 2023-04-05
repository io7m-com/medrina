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

Require Import Medrina.Matches.

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

(** A single rule in a policy. *)
Record rule := Rule {
  (** The rule conclusion. *)
  rConclusion   : ruleConclusion;
  (** The expression that matches a subject. *)
  rMatchSubject : exprMatchSubject;
  (** The expression that matches an object. *)
  rMatchObject  : exprMatchObject;
  (** The expression that matches a subject. *)
  rMatchAction  : exprMatchAction
}.
