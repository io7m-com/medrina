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

import java.util.List;
import java.util.Objects;

/**
 * An expression that matches actions.
 */

public sealed interface MMatchActionType
{
  /**
   * A function that returns {@code true} if this expression matches the given
   * action.
   *
   * @param action The action
   *
   * @return {@code true} if this expression matches
   */

  boolean matches(
    MActionName action);

  /**
   * An expression that matches if the incoming action has the given name.
   *
   * @param name The action name
   */

  record MMatchActionWithName(MActionName name)
    implements MMatchActionType
  {
    /**
     * An expression that matches if the incoming action has the given name.
     */

    public MMatchActionWithName
    {
      Objects.requireNonNull(name, "type");
    }

    @Override
    public boolean matches(
      final MActionName action)
    {
      return Objects.equals(this.name, action);
    }
  }

  /**
   * An expression that matches iff all the sub expressions match.
   *
   * @param subExpressions The subexpressions
   */

  record MMatchActionAnd(List<MMatchActionType> subExpressions)
    implements MMatchActionType
  {
    /**
     * An expression that matches iff all the sub expressions match.
     */

    public MMatchActionAnd
    {
      Objects.requireNonNull(subExpressions, "subExpressions");
    }

    @Override
    public boolean matches(
      final MActionName action)
    {
      Objects.requireNonNull(action, "action");

      for (final var subExpression : this.subExpressions) {
        if (!subExpression.matches(action)) {
          return false;
        }
      }

      return true;
    }
  }

  /**
   * An expression that matches iff any of the sub expressions match.
   *
   * @param subExpressions The subexpressions
   */

  record MMatchActionOr(List<MMatchActionType> subExpressions)
    implements MMatchActionType
  {
    /**
     * An expression that matches iff any of the sub expressions match.
     */

    public MMatchActionOr
    {
      Objects.requireNonNull(subExpressions, "subExpressions");
    }

    @Override
    public boolean matches(
      final MActionName action)
    {
      Objects.requireNonNull(action, "action");

      for (final var subExpression : this.subExpressions) {
        if (subExpression.matches(action)) {
          return true;
        }
      }

      return false;
    }
  }

  /**
   * An expression that always matches.
   */

  record MMatchActionTrue()
    implements MMatchActionType
  {
    @Override
    public boolean matches(final MActionName action)
    {
      Objects.requireNonNull(action, "action");
      return true;
    }
  }

  /**
   * An expression that never matches.
   */

  record MMatchActionFalse()
    implements MMatchActionType
  {
    @Override
    public boolean matches(final MActionName action)
    {
      Objects.requireNonNull(action, "action");
      return false;
    }
  }
}
