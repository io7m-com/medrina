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
import com.io7m.medrina.api.MMatchSubjectType.MMatchSubjectAnd;
import com.io7m.medrina.api.MMatchSubjectType.MMatchSubjectOr;
import com.io7m.medrina.api.MMatchSubjectType.MMatchSubjectWithRolesAll;
import com.io7m.medrina.api.MMatchSubjectType.MMatchSubjectWithRolesAny;
import com.io7m.medrina.api.MRoleName;
import com.io7m.medrina.api.MSubject;
import net.jqwik.api.Arbitrary;
import net.jqwik.api.ForAll;
import net.jqwik.api.Property;
import net.jqwik.api.Provide;
import net.jqwik.api.constraints.NotEmpty;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

public final class MMatchSubjectTest
{
  @Test
  public void testAllRequiredEmptyReceivedEmpty()
  {
    assertTrue(
      new MMatchSubjectWithRolesAll(Set.of())
        .matches(new MSubject(Collections.emptySortedSet()))
    );
  }

  @Test
  public void testAllRequiredEmptyReceivedNonEmpty()
  {
    assertTrue(
      new MMatchSubjectWithRolesAll(Set.of())
        .matches(new MSubject(Set.of(new MRoleName("x"))))
    );
  }

  @Test
  public void testAllRequiredNonEmptyReceivedEmpty()
  {
    assertFalse(
      new MMatchSubjectWithRolesAll(Set.of(new MRoleName("x")))
        .matches(new MSubject(Set.of()))
    );
  }

  @Test
  public void testAllRequiredNonEmptyReceivedDifferent()
  {
    assertFalse(
      new MMatchSubjectWithRolesAll(Set.of(new MRoleName("x")))
        .matches(new MSubject(Set.of(new MRoleName("y"))))
    );
  }

  @Test
  public void testAllRequiredNonEmptyReceivedSame()
  {
    assertTrue(
      new MMatchSubjectWithRolesAll(Set.of(new MRoleName("x")))
        .matches(new MSubject(Set.of(new MRoleName("x"))))
    );
  }

  @Test
  public void testAnyRequiredEmptyReceivedEmpty()
  {
    assertFalse(
      new MMatchSubjectWithRolesAny(Set.of())
        .matches(new MSubject(Set.of()))
    );
  }

  @Test
  public void testAnyRequiredEmptyReceivedNonEmpty()
  {
    assertFalse(
      new MMatchSubjectWithRolesAny(Set.of())
        .matches(new MSubject(Set.of(new MRoleName("x"))))
    );
  }

  @Test
  public void testAnyRequiredNonEmptyReceivedSame()
  {
    assertTrue(
      new MMatchSubjectWithRolesAny(Set.of(new MRoleName("x")))
        .matches(new MSubject(Set.of(new MRoleName("x"))))
    );
  }

  @Test
  public void testAnyRequiredNonEmptyReceivedDifferent()
  {
    assertFalse(
      new MMatchSubjectWithRolesAny(Set.of(new MRoleName("x")))
        .matches(new MSubject(Set.of(new MRoleName("y"))))
    );
  }

  @Test
  public void testAnyRequiredNonEmptyReceivedSuperset()
  {
    assertTrue(
      new MMatchSubjectWithRolesAny(Set.of(new MRoleName("x")))
        .matches(new MSubject(Set.of(
          new MRoleName("a"),
          new MRoleName("b"),
          new MRoleName("x"))))
    );
  }

  @Provide
  public Arbitrary<List<MMatchSubjectType>> trues()
  {
    return MMatchSubjects.trues().list();
  }

  @Provide
  public Arbitrary<List<MMatchSubjectType>> falses()
  {
    return MMatchSubjects.falses().list();
  }

  /**
   * If all expressions return {@code false}, then ANDing the expressions
   * together returns {@code false}.
   */

  @Property
  public void testAndFalse(
    @ForAll final MSubject subject,
    @ForAll("falses") @NotEmpty final List<MMatchSubjectType> falses)
  {
    assertFalse(
      new MMatchSubjectAnd(falses).matches(subject)
    );
  }

  /**
   * ANDing an empty list of expressions together returns {@code true}.
   */

  @Property
  public void testAndEmpty(
    @ForAll final MSubject subject)
  {
    assertTrue(
      new MMatchSubjectAnd(List.of()).matches(subject)
    );
  }

  /**
   * If all expressions return {@code true}, then ANDing the expressions
   * together returns {@code true}.
   */

  @Property
  public void testAndTrue(
    @ForAll final MSubject subject,
    @ForAll("trues") @NotEmpty final List<MMatchSubjectType> trues)
  {
    assertTrue(
      new MMatchSubjectAnd(trues).matches(subject)
    );
  }

  /**
   * If at least one expression returns {@code false}, then ANDing the
   * expressions together returns {@code false}.
   */

  @Property
  public void testAndTrueFalseMixed(
    @ForAll final MSubject subject,
    @ForAll("trues") @NotEmpty final List<MMatchSubjectType> trues,
    @ForAll("falses") @NotEmpty final List<MMatchSubjectType> falses)
  {
    final var all = new ArrayList<MMatchSubjectType>();
    all.addAll(trues);
    all.addAll(falses);
    Collections.shuffle(all);

    assertFalse(
      new MMatchSubjectAnd(all).matches(subject)
    );
  }

  /**
   * If all expressions return {@code false}, then ORing the expressions
   * together returns {@code false}.
   */

  @Property
  public void testOrFalse(
    @ForAll final MSubject subject,
    @ForAll("falses") @NotEmpty final List<MMatchSubjectType> falses)
  {
    assertFalse(
      new MMatchSubjectOr(falses).matches(subject)
    );
  }

  /**
   * ORing an empty list of expressions together returns {@code false}.
   */

  @Property
  public void testOrEmpty(
    @ForAll final MSubject subject)
  {
    assertFalse(
      new MMatchSubjectOr(List.of()).matches(subject)
    );
  }

  /**
   * If all expressions return {@code true}, then ORing the expressions
   * together returns {@code true}.
   */

  @Property
  public void testOrTrue(
    @ForAll final MSubject subject,
    @ForAll("trues") @NotEmpty final List<MMatchSubjectType> trues)
  {
    assertTrue(
      new MMatchSubjectOr(trues).matches(subject)
    );
  }

  /**
   * If at least one expression returns {@code false}, then ORing the
   * expressions together returns {@code true}.
   */

  @Property
  public void testOrTrueFalseMixed(
    @ForAll final MSubject subject,
    @ForAll("trues") @NotEmpty final List<MMatchSubjectType> trues,
    @ForAll("falses") @NotEmpty final List<MMatchSubjectType> falses)
  {
    final var all = new ArrayList<MMatchSubjectType>();
    all.addAll(trues);
    all.addAll(falses);
    Collections.shuffle(all);

    assertTrue(
      new MMatchSubjectOr(all).matches(subject)
    );
  }
}
