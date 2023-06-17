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
import java.util.Map;
import java.util.Objects;

/**
 * An expression that matches objects.
 */

public sealed interface MMatchObjectType
{
  /**
   * A function that returns {@code true} if this expression matches the given
   * object.
   *
   * @param object The object
   *
   * @return {@code true} if this expression matches
   */

  boolean matches(
    MObject object);

  /**
   * An expression that matches iff all the sub expressions match.
   *
   * @param subExpressions The subexpressions
   */

  record MMatchObjectAnd(List<MMatchObjectType> subExpressions)
    implements MMatchObjectType
  {
    /**
     * An expression that matches iff all the sub expressions match.
     */

    public MMatchObjectAnd
    {
      Objects.requireNonNull(subExpressions, "subExpressions");
    }

    @Override
    public boolean matches(
      final MObject object)
    {
      Objects.requireNonNull(object, "object");

      for (final var subExpression : this.subExpressions) {
        if (!subExpression.matches(object)) {
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

  record MMatchObjectOr(List<MMatchObjectType> subExpressions)
    implements MMatchObjectType
  {
    /**
     * An expression that matches iff any of the sub expressions match.
     */

    public MMatchObjectOr
    {
      Objects.requireNonNull(subExpressions, "subExpressions");
    }

    @Override
    public boolean matches(
      final MObject object)
    {
      Objects.requireNonNull(object, "object");

      for (final var subExpression : this.subExpressions) {
        if (subExpression.matches(object)) {
          return true;
        }
      }

      return false;
    }
  }

  /**
   * An expression that matches if the incoming object has the given type.
   *
   * @param type The object type
   */

  record MMatchObjectWithType(MTypeName type)
    implements MMatchObjectType
  {
    /**
     * An expression that matches if the incoming object has the given type.
     */

    public MMatchObjectWithType
    {
      Objects.requireNonNull(type, "type");
    }

    @Override
    public boolean matches(
      final MObject object)
    {
      return Objects.equals(this.type, object.type());
    }
  }

  /**
   * An expression that matches if the incoming object has (at least) all
   * the given attributes.
   *
   * @param required The required attributes
   */

  record MMatchObjectWithAttributesAll(
    Map<MAttributeName, MAttributeValue> required)
    implements MMatchObjectType
  {
    /**
     * An expression that matches if the incoming object has (at least) all
     * the given attributes.
     */

    public MMatchObjectWithAttributesAll
    {
      Objects.requireNonNull(required, "required");
    }

    @Override
    public boolean matches(
      final MObject object)
    {
      final var provided = object.attributes();
      for (final var entry : this.required.entrySet()) {
        final var existing = provided.get(entry.getKey());
        if (!Objects.equals(existing, entry.getValue())) {
          return false;
        }
      }
      return true;
    }
  }

  /**
   * An expression that matches if the incoming object has any of
   * the given attributes.
   *
   * @param required The required attributes
   */

  record MMatchObjectWithAttributesAny(
    Map<MAttributeName, MAttributeValue> required)
    implements MMatchObjectType
  {
    /**
     * An expression that matches if the incoming object has any of
     * the given attributes.
     */

    public MMatchObjectWithAttributesAny
    {
      Objects.requireNonNull(required, "required");
    }

    @Override
    public boolean matches(
      final MObject object)
    {
      final var provided = object.attributes();
      for (final var entry : this.required.entrySet()) {
        final var existing = provided.get(entry.getKey());
        if (Objects.equals(existing, entry.getValue())) {
          return true;
        }
      }
      return false;
    }
  }

  /**
   * An expression that always matches.
   */

  record MMatchObjectTrue()
    implements MMatchObjectType
  {
    @Override
    public boolean matches(final MObject object)
    {
      Objects.requireNonNull(object, "object");
      return true;
    }
  }

  /**
   * An expression that never matches.
   */

  record MMatchObjectFalse()
    implements MMatchObjectType
  {
    @Override
    public boolean matches(final MObject object)
    {
      Objects.requireNonNull(object, "object");
      return false;
    }
  }
}
