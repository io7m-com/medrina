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

import net.jcip.annotations.ThreadSafe;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import static com.io7m.medrina.api.MPolicyAccess.ACCESS_ALLOWED;
import static com.io7m.medrina.api.MPolicyAccess.ACCESS_DENIED;

/**
 * The default policy evaluator implementation.
 */

@ThreadSafe
public final class MPolicyEvaluator implements MPolicyEvaluatorType
{
  private MPolicyEvaluator()
  {

  }

  /**
   * Create a policy evaluator.
   *
   * @return A policy evaluator
   */

  public static MPolicyEvaluatorType create()
  {
    return new MPolicyEvaluator();
  }

  @Override
  public MPolicyResult evaluate(
    final MPolicy policy,
    final MSubject subject,
    final MObject object,
    final MActionName actionName)
  {
    Objects.requireNonNull(policy, "policy");
    Objects.requireNonNull(subject, "subject");
    Objects.requireNonNull(object, "object");
    Objects.requireNonNull(actionName, "actionName");

    var access = ACCESS_DENIED;
    var halt = false;
    final var rules = policy.rules();

    final var results = new ArrayList<MRuleResult>(rules.size());
    for (var index = 0; index < rules.size(); ++index) {
      if (halt) {
        break;
      }

      final var rule =
        rules.get(index);
      final var matchesObject =
        rule.matchObject().matches(object);
      final var matchesSubject =
        rule.matchSubject().matches(subject);
      final var matchesAction =
        rule.matchAction().matches(actionName);

      results.add(
        new MRuleResult(index, matchesSubject, matchesObject, matchesAction)
      );

      if (matchesObject && matchesSubject && matchesAction) {
        switch (rule.conclusion()) {
          case ALLOW -> {
            access = ACCESS_ALLOWED;
          }
          case ALLOW_IMMEDIATELY -> {
            access = ACCESS_ALLOWED;
            halt = true;
          }
          case DENY -> {
            access = ACCESS_DENIED;
          }
          case DENY_IMMEDIATELY -> {
            access = ACCESS_DENIED;
            halt = true;
          }
        }
      }
    }

    return new MPolicyResult(access, List.copyOf(results));
  }
}
