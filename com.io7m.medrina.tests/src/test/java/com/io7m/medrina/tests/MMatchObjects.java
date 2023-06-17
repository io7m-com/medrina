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

import com.io7m.medrina.api.MAttributeName;
import com.io7m.medrina.api.MAttributeValue;
import com.io7m.medrina.api.MMatchObjectType;
import com.io7m.medrina.api.MMatchObjectType.MMatchObjectFalse;
import com.io7m.medrina.api.MMatchObjectType.MMatchObjectTrue;
import com.io7m.medrina.api.MMatchObjectType.MMatchObjectWithAttributesAll;
import com.io7m.medrina.api.MMatchObjectType.MMatchObjectWithAttributesAny;
import com.io7m.medrina.api.MTypeName;
import net.jqwik.api.Arbitraries;
import net.jqwik.api.Arbitrary;
import net.jqwik.api.arbitraries.IntegerArbitrary;

import java.util.List;
import java.util.Map;

public final class MMatchObjects
{
  private static final IntegerArbitrary CASE_INTEGERS =
    Arbitraries.integers()
      .between(0, 6);

  private MMatchObjects()
  {

  }

  public static Arbitrary<MAttributeValue> attributeValues()
  {
    return Arbitraries.strings()
      .withCharRange('a', 'z')
      .withCharRange('0', '9')
      .withChars('.', '_', '-')
      .ofMinLength(1)
      .ofMaxLength(256)
      .map(MAttributeValue::new);
  }

  public static Arbitrary<MAttributeName> attributeNames()
  {
    return Arbitraries.strings()
      .withCharRange('a', 'z')
      .withCharRange('0', '9')
      .withChars('.', '_', '-')
      .ofMinLength(1)
      .ofMaxLength(256)
      .map(MAttributeName::new);
  }

  public static Arbitrary<Map<MAttributeName, MAttributeValue>> attributeMaps()
  {
    return Arbitraries.maps(
      attributeNames(),
      attributeValues()
    );
  }

  public static Arbitrary<MMatchObjectType> trues()
  {
    return Arbitraries.of(new MMatchObjectTrue());
  }

  public static Arbitrary<MMatchObjectType> falses()
  {
    return Arbitraries.of(new MMatchObjectFalse());
  }

  public static Arbitrary<MMatchObjectType> arbitrary()
  {
    final Arbitrary<MTypeName> names =
      Arbitraries.strings()
        .withCharRange('a', 'z')
        .withCharRange('0', '9')
        .withChars('.', '_', '-')
        .ofMinLength(1)
        .ofMaxLength(256)
        .map(MTypeName::new);

    final var maps =
      attributeMaps();

    return CASE_INTEGERS
      .map(integer -> generateObject(names, maps, 0, integer));
  }

  private static MMatchObjectType generateObject(
    final Arbitrary<MTypeName> names,
    final Arbitrary<Map<MAttributeName, MAttributeValue>> attributes,
    final int depth,
    final Integer integer)
  {
    if (depth >= 3) {
      return new MMatchObjectTrue();
    }

    return switch (integer.intValue()) {
      case 0 -> new MMatchObjectTrue();
      case 1 -> new MMatchObjectFalse();
      case 2 -> new MMatchObjectType.MMatchObjectAnd(
        List.of(
          generateObject(names, attributes, depth + 1, CASE_INTEGERS.sample()),
          generateObject(names, attributes, depth + 1, CASE_INTEGERS.sample()),
          generateObject(names, attributes, depth + 1, CASE_INTEGERS.sample())
        )
      );
      case 3 -> new MMatchObjectType.MMatchObjectOr(
        List.of(
          generateObject(names, attributes, depth + 1, CASE_INTEGERS.sample()),
          generateObject(names, attributes, depth + 1, CASE_INTEGERS.sample()),
          generateObject(names, attributes, depth + 1, CASE_INTEGERS.sample())
        )
      );
      case 4 -> new MMatchObjectType.MMatchObjectWithType(
        names.sample()
      );
      case 5 -> new MMatchObjectWithAttributesAll(attributes.sample());
      case 6 -> new MMatchObjectWithAttributesAny(attributes.sample());
      default -> throw new IllegalStateException();
    };
  }
}
