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

package com.io7m.medrina.tests;

import com.io7m.medrina.api.MMatchSubjectType;
import com.io7m.medrina.api.MMatchSubjectType.MMatchSubjectFalse;
import com.io7m.medrina.api.MMatchSubjectType.MMatchSubjectTrue;
import com.io7m.medrina.api.MRoleName;
import net.jqwik.api.Arbitraries;
import net.jqwik.api.Arbitrary;
import net.jqwik.api.arbitraries.IntegerArbitrary;

import java.util.List;

public final class MMatchSubjects
{
  private static final IntegerArbitrary CASE_INTEGERS =
    Arbitraries.integers()
      .between(0, 5);

  private MMatchSubjects()
  {

  }

  public static Arbitrary<MMatchSubjectType> trues()
  {
    return Arbitraries.of(new MMatchSubjectTrue());
  }

  public static Arbitrary<MMatchSubjectType> falses()
  {
    return Arbitraries.of(new MMatchSubjectFalse());
  }

  public static Arbitrary<MMatchSubjectType> arbitrary()
  {
    final var names =
      Arbitraries.defaultFor(MRoleName.class);
    return CASE_INTEGERS
      .map(integer -> generateSubject(names, 0, integer));
  }

  private static MMatchSubjectType generateSubject(
    final Arbitrary<MRoleName> names,
    final int depth,
    final Integer integer)
  {
    if (depth >= 3) {
      return new MMatchSubjectType.MMatchSubjectTrue();
    }

    return switch (integer.intValue()) {
      case 0 ->
        new MMatchSubjectType.MMatchSubjectTrue();
      case 1 ->
        new MMatchSubjectType.MMatchSubjectFalse();
      case 2 ->
        new MMatchSubjectType.MMatchSubjectAnd(
          List.of(
            generateSubject(names, depth + 1, CASE_INTEGERS.sample()),
            generateSubject(names, depth + 1, CASE_INTEGERS.sample()),
            generateSubject(names, depth + 1, CASE_INTEGERS.sample())
          )
        );
      case 3 ->
        new MMatchSubjectType.MMatchSubjectOr(
          List.of(
            generateSubject(names, depth + 1, CASE_INTEGERS.sample()),
            generateSubject(names, depth + 1, CASE_INTEGERS.sample()),
            generateSubject(names, depth + 1, CASE_INTEGERS.sample())
          )
        );
      case 4 ->
        new MMatchSubjectType.MMatchSubjectWithRolesAny(
          names.set().sample()
        );
      case 5 ->
        new MMatchSubjectType.MMatchSubjectWithRolesAll(
          names.set().sample()
        );
      default ->
        throw new IllegalStateException();
    };
  }
}
