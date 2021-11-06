/*
 * Copyright © 2021 Mark Raynsford <code@io7m.com> https://www.io7m.com
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
 */

package com.io7m.medrina.api;

import java.util.Objects;

/**
 * A single rule in a policy.
 *
 * @param conclusion   The rule conclusion
 * @param matchAction  The expression that matches an action
 * @param matchObject  The expression that matches an object
 * @param matchSubject The expression that matches a subject
 */

public record MRule(
  MRuleConclusion conclusion,
  MMatchSubjectType matchSubject,
  MMatchObjectType matchObject,
  MMatchActionType matchAction)
{
  /**
   * A single rule in a policy.
   *
   * @param conclusion   The rule conclusion
   * @param matchAction  The expression that matches an action
   * @param matchObject  The expression that matches an object
   * @param matchSubject The expression that matches a subject
   */

  public MRule
  {
    Objects.requireNonNull(conclusion, "conclusion");
    Objects.requireNonNull(matchSubject, "matchSubject");
    Objects.requireNonNull(matchObject, "matchObject");
    Objects.requireNonNull(matchAction, "matchAction");
  }
}
