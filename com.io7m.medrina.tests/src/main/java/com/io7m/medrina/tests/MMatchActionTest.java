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

import com.io7m.medrina.api.MActionName;
import com.io7m.medrina.api.MMatchActionType;
import com.io7m.medrina.api.MMatchActionType.MMatchActionAnd;
import com.io7m.medrina.api.MMatchActionType.MMatchActionOr;
import com.io7m.medrina.api.MMatchActionType.MMatchActionWithName;
import net.jqwik.api.Arbitrary;
import net.jqwik.api.ForAll;
import net.jqwik.api.Property;
import net.jqwik.api.Provide;
import net.jqwik.api.constraints.NotEmpty;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

public final class MMatchActionTest
{
  @Provide
  public Arbitrary<List<MMatchActionType>> trues()
  {
    return MMatchActions.trues().list();
  }

  @Provide
  public Arbitrary<List<MMatchActionType>> falses()
  {
    return MMatchActions.falses().list();
  }

  /**
   * If all expressions return {@code false}, then ANDing the expressions
   * together returns {@code false}.
   */

  @Property
  public void testAndFalse(
    @ForAll final MActionName object,
    @ForAll("falses") @NotEmpty final List<MMatchActionType> falses)
  {
    assertFalse(
      new MMatchActionAnd(falses).matches(object)
    );
  }

  /**
   * If at least one expression returns {@code false}, then ANDing the
   * expressions together returns {@code false}.
   */

  @Property
  public void testAndTrueFalseMixed(
    @ForAll final MActionName object,
    @ForAll("trues") @NotEmpty final List<MMatchActionType> trues,
    @ForAll("falses") @NotEmpty final List<MMatchActionType> falses)
  {
    final var all = new ArrayList<MMatchActionType>();
    all.addAll(trues);
    all.addAll(falses);
    Collections.shuffle(all);

    assertFalse(
      new MMatchActionAnd(all).matches(object)
    );
  }

  /**
   * ANDing an empty list of expressions together returns {@code true}.
   */

  @Property
  public void testAndEmpty(
    @ForAll final MActionName object)
  {
    assertTrue(
      new MMatchActionAnd(List.of()).matches(object)
    );
  }

  /**
   * If all expressions return {@code true}, then ANDing the expressions
   * together returns {@code true}.
   */

  @Property
  public void testAndTrue(
    @ForAll final MActionName object,
    @ForAll("trues") @NotEmpty final List<MMatchActionType> trues)
  {
    assertTrue(
      new MMatchActionAnd(trues).matches(object)
    );
  }

  /**
   * All objects with name {@code T} are matched by an expression
   * that checks for name {@code T}.
   */

  @Property
  public void testWithType(
    @ForAll final MActionName name)
  {

    assertTrue(new MMatchActionWithName(name).matches(name));
  }

  /**
   * If all expressions return {@code false}, then ORing the expressions
   * together returns {@code false}.
   */

  @Property
  public void testOrFalse(
    @ForAll final MActionName object,
    @ForAll("falses") @NotEmpty final List<MMatchActionType> falses)
  {
    assertFalse(
      new MMatchActionOr(falses).matches(object)
    );
  }

  /**
   * If at least one expression returns {@code false}, then ORing the
   * expressions together returns {@code false}.
   */

  @Property
  public void testOrTrueFalseMixed(
    @ForAll final MActionName object,
    @ForAll("trues") @NotEmpty final List<MMatchActionType> trues,
    @ForAll("falses") @NotEmpty final List<MMatchActionType> falses)
  {
    final var all = new ArrayList<MMatchActionType>();
    all.addAll(trues);
    all.addAll(falses);
    Collections.shuffle(all);

    assertTrue(
      new MMatchActionOr(all).matches(object)
    );
  }

  /**
   * ORing an empty list of expressions together returns {@code true}.
   */

  @Property
  public void testOrEmpty(
    @ForAll final MActionName object)
  {
    assertFalse(
      new MMatchActionOr(List.of()).matches(object)
    );
  }

  /**
   * If all expressions return {@code true}, then ORing the expressions
   * together returns {@code true}.
   */

  @Property
  public void testOrTrue(
    @ForAll final MActionName object,
    @ForAll("trues") @NotEmpty final List<MMatchActionType> trues)
  {
    assertTrue(
      new MMatchActionOr(trues).matches(object)
    );
  }
}
