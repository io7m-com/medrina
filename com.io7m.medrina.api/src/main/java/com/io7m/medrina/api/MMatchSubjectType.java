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
import java.util.Set;

/**
 * An expression that matches subjects.
 */

public sealed interface MMatchSubjectType
{
  /**
   * A function that returns {@code true} if this expression matches the given
   * roles.
   *
   * @param subject The subject
   *
   * @return {@code true} if this expression matches
   */

  boolean matches(
    MSubject subject);

  /**
   * An expression that matches iff all the sub expressions match.
   *
   * @param subExpressions The subexpressions
   */

  record MMatchSubjectAnd(List<MMatchSubjectType> subExpressions)
    implements MMatchSubjectType
  {
    /**
     * An expression that matches iff all the sub expressions match.
     */

    public MMatchSubjectAnd
    {
      Objects.requireNonNull(subExpressions, "subExpressions");
    }

    @Override
    public boolean matches(
      final MSubject subject)
    {
      Objects.requireNonNull(subject, "subject");

      for (final var subExpression : this.subExpressions) {
        if (!subExpression.matches(subject)) {
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

  record MMatchSubjectOr(List<MMatchSubjectType> subExpressions)
    implements MMatchSubjectType
  {
    /**
     * An expression that matches iff any of the sub expressions match.
     */

    public MMatchSubjectOr
    {
      Objects.requireNonNull(subExpressions, "subExpressions");
    }

    @Override
    public boolean matches(
      final MSubject subject)
    {
      Objects.requireNonNull(subject, "subject");

      for (final var subExpression : this.subExpressions) {
        if (subExpression.matches(subject)) {
          return true;
        }
      }
      return false;
    }
  }

  /**
   * An expression that matches if all the required roles are present in the
   * set of incoming roles.
   *
   * More formally, given the set of required roles {@code R} and the
   * set of incoming roles {@code S}, the expression matches if
   * {@code R ⊆ S}.
   *
   * @param requiredRoles The required roles
   */

  record MMatchSubjectWithRolesAll(Set<MRoleName> requiredRoles)
    implements MMatchSubjectType
  {
    /**
     * An expression that matches if all the required roles are present in the
     * set of incoming roles.
     */

    public MMatchSubjectWithRolesAll
    {
      Objects.requireNonNull(requiredRoles, "requiredRoles");
    }

    @Override
    public boolean matches(
      final MSubject subject)
    {
      return subject.roles().containsAll(this.requiredRoles);
    }
  }

  /**
   * An expression that matches if at least one of the required roles are
   * present in the set of incoming roles.
   *
   * More formally, given the set of required roles {@code R} and the
   * set of incoming roles {@code S}, the expression matches if
   * {@code ∃x. x ∈ R ∧ x ∈ S }.
   *
   * @param requiredRoles The required roles
   */

  record MMatchSubjectWithRolesAny(Set<MRoleName> requiredRoles)
    implements MMatchSubjectType
  {
    /**
     * An expression that matches if at least one of the required roles are
     * present in the set of incoming roles.
     */

    public MMatchSubjectWithRolesAny
    {
      Objects.requireNonNull(requiredRoles, "requiredRoles");
    }

    @Override
    public boolean matches(
      final MSubject subject)
    {
      Objects.requireNonNull(subject, "subject");

      final var incomingRoles = subject.roles();
      for (final var role : this.requiredRoles) {
        if (incomingRoles.contains(role)) {
          return true;
        }
      }
      return false;
    }
  }

  /**
   * An expression that always matches.
   */

  record MMatchSubjectTrue()
    implements MMatchSubjectType
  {
    @Override
    public boolean matches(final MSubject subject)
    {
      Objects.requireNonNull(subject, "subject");
      return true;
    }
  }

  /**
   * An expression that never matches.
   */

  record MMatchSubjectFalse()
    implements MMatchSubjectType
  {
    @Override
    public boolean matches(final MSubject subject)
    {
      Objects.requireNonNull(subject, "subject");
      return false;
    }
  }
}
