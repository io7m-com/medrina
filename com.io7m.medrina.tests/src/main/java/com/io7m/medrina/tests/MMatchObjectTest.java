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

import com.io7m.lanark.core.RDottedName;
import com.io7m.medrina.api.MAttributeName;
import com.io7m.medrina.api.MAttributeValue;
import com.io7m.medrina.api.MMatchObjectType;
import com.io7m.medrina.api.MMatchObjectType.MMatchObjectAnd;
import com.io7m.medrina.api.MMatchObjectType.MMatchObjectOr;
import com.io7m.medrina.api.MMatchObjectType.MMatchObjectWithAttributesAll;
import com.io7m.medrina.api.MMatchObjectType.MMatchObjectWithAttributesAny;
import com.io7m.medrina.api.MMatchObjectType.MMatchObjectWithType;
import com.io7m.medrina.api.MObject;
import com.io7m.medrina.api.MTypeName;
import net.jqwik.api.Arbitrary;
import net.jqwik.api.ForAll;
import net.jqwik.api.Property;
import net.jqwik.api.Provide;
import net.jqwik.api.constraints.NotEmpty;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assumptions.assumeFalse;

public final class MMatchObjectTest
{
  @Provide
  public Arbitrary<List<MMatchObjectType>> trues()
  {
    return MMatchObjects.trues().list();
  }

  @Provide
  public Arbitrary<List<MMatchObjectType>> falses()
  {
    return MMatchObjects.falses().list();
  }

  /**
   * If all expressions return {@code false}, then ANDing the expressions
   * together returns {@code false}.
   */

  @Property
  public void testAndFalse(
    @ForAll final MObject object,
    @ForAll("falses") @NotEmpty final List<MMatchObjectType> falses)
  {
    assertFalse(
      new MMatchObjectAnd(falses).matches(object)
    );
  }

  /**
   * If at least one expression returns {@code false}, then ANDing the
   * expressions together returns {@code false}.
   */

  @Property
  public void testAndTrueFalseMixed(
    @ForAll final MObject object,
    @ForAll("trues") @NotEmpty final List<MMatchObjectType> trues,
    @ForAll("falses") @NotEmpty final List<MMatchObjectType> falses)
  {
    final var all = new ArrayList<MMatchObjectType>();
    all.addAll(trues);
    all.addAll(falses);
    Collections.shuffle(all);

    assertFalse(
      new MMatchObjectAnd(all).matches(object)
    );
  }

  /**
   * ANDing an empty list of expressions together returns {@code true}.
   */

  @Property
  public void testAndEmpty(
    @ForAll final MObject object)
  {
    assertTrue(
      new MMatchObjectAnd(List.of()).matches(object)
    );
  }

  /**
   * If all expressions return {@code true}, then ANDing the expressions
   * together returns {@code true}.
   */

  @Property
  public void testAndTrue(
    @ForAll final MObject object,
    @ForAll("trues") @NotEmpty final List<MMatchObjectType> trues)
  {
    assertTrue(
      new MMatchObjectAnd(trues).matches(object)
    );
  }

  /**
   * All objects with type {@code T} are matched by an expression
   * that checks for type {@code T}.
   */

  @Property
  public void testWithType(
    @ForAll final MObject object,
    @ForAll final MTypeName typeName)
  {
    final var objectWith =
      new MObject(typeName, object.attributes());

    assertTrue(new MMatchObjectWithType(typeName).matches(objectWith));
  }

  /**
   * If all expressions return {@code false}, then ORing the expressions
   * together returns {@code false}.
   */

  @Property
  public void testOrFalse(
    @ForAll final MObject object,
    @ForAll("falses") @NotEmpty final List<MMatchObjectType> falses)
  {
    assertFalse(
      new MMatchObjectOr(falses).matches(object)
    );
  }

  /**
   * If at least one expression returns {@code false}, then ORing the
   * expressions together returns {@code false}.
   */

  @Property
  public void testOrTrueFalseMixed(
    @ForAll final MObject object,
    @ForAll("trues") @NotEmpty final List<MMatchObjectType> trues,
    @ForAll("falses") @NotEmpty final List<MMatchObjectType> falses)
  {
    final var all = new ArrayList<MMatchObjectType>();
    all.addAll(trues);
    all.addAll(falses);
    Collections.shuffle(all);

    assertTrue(
      new MMatchObjectOr(all).matches(object)
    );
  }

  /**
   * ORing an empty list of expressions together returns {@code true}.
   */

  @Property
  public void testOrEmpty(
    @ForAll final MObject object)
  {
    assertFalse(
      new MMatchObjectOr(List.of()).matches(object)
    );
  }

  /**
   * If all expressions return {@code true}, then ORing the expressions
   * together returns {@code true}.
   */

  @Property
  public void testOrTrue(
    @ForAll final MObject object,
    @ForAll("trues") @NotEmpty final List<MMatchObjectType> trues)
  {
    assertTrue(
      new MMatchObjectOr(trues).matches(object)
    );
  }

  /**
   * An object always matches its own attributes.
   */

  @Property
  public void testWithAllAttributes(
    @ForAll final MObject object)
  {
    assertTrue(
      new MMatchObjectWithAttributesAll(object.attributes()).matches(object)
    );
  }

  /**
   * An object always matches its own attributes.
   */

  @Property
  public void testWithAnyAttributes(
    @ForAll final MObject object)
  {
    assumeFalse(object.attributes().isEmpty());

    assertTrue(
      new MMatchObjectWithAttributesAny(object.attributes()).matches(object)
    );
  }

  /**
   * The 'WithAttributesAny' expression does not match empty maps.
   */

  @Test
  public void testWithAnyAttributesEmpty()
  {
    assertFalse(
      new MMatchObjectWithAttributesAny(Map.of()).matches(new MObject(
        new MTypeName(new RDottedName("x")),
        Map.of()
      ))
    );
  }

  /**
   * An empty set of attributes matches any object using WithAttributesAll.
   */

  @Property
  public void testWithAllAttributesEmpty(
    @ForAll final MObject object)
  {
    assertTrue(
      new MMatchObjectWithAttributesAll(Map.of()).matches(object)
    );
  }

  /**
   * An empty set of attributes matches any object using WithAttributesAny.
   */

  @Property
  public void testWithAnyAttributesEmpty(
    @ForAll final MObject object)
  {
    assertFalse(
      new MMatchObjectWithAttributesAny(Map.of()).matches(object)
    );
  }

  /**
   * The 'WithAttributesAll' expression requires attributes to have the
   * correct values, not just names.
   */

  @Test
  public void testWithAllAttributesValue()
  {
    assertFalse(
      new MMatchObjectWithAttributesAll(Map.of(
        MAttributeName.of("x"),
        MAttributeValue.of("y")
      )).matches(new MObject(
        new MTypeName(new RDottedName("a")),
        Map.of(
          MAttributeName.of("x"),
          MAttributeValue.of("z")
        )
      ))
    );
  }

  /**
   * The 'WithAttributesAny' expression requires attributes to have the
   * correct values, not just names.
   */

  @Test
  public void testWithAnyAttributesValue()
  {
    assertFalse(
      new MMatchObjectWithAttributesAny(Map.of(
        MAttributeName.of("x"),
        MAttributeValue.of("y")
      )).matches(new MObject(
        new MTypeName(new RDottedName("a")),
        Map.of(
          MAttributeName.of("x"),
          MAttributeValue.of("z")
        )
      ))
    );
  }
}
