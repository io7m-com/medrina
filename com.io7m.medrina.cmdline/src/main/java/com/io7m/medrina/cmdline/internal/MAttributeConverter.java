/*
 * Copyright © 2023 Mark Raynsford <code@io7m.com> https://www.io7m.com
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


package com.io7m.medrina.cmdline.internal;

import com.io7m.lanark.core.RDottedName;
import com.io7m.medrina.api.MAttributeName;
import com.io7m.medrina.api.MAttributeValue;
import com.io7m.quarrel.core.QValueConverterType;

import java.util.List;

/**
 * A converter for attributes.
 */

public final class MAttributeConverter
  implements QValueConverterType<MAttribute>
{
  /**
   * A converter for attributes.
   */

  public MAttributeConverter()
  {

  }

  @Override
  public MAttribute convertFromString(
    final String text)
  {
    final var segments = List.of(text.split(":"));
    if (segments.size() == 2) {
      return new MAttribute(
        new MAttributeName(new RDottedName(segments.get(0))),
        new MAttributeValue(new RDottedName(segments.get(1)))
      );
    }

    throw new IllegalArgumentException("Parse error.");
  }

  @Override
  public String convertToString(
    final MAttribute attribute)
  {
    return "%s:%s".formatted(
      attribute.name().value(),
      attribute.value().value()
    );
  }

  @Override
  public MAttribute exampleValue()
  {
    return new MAttribute(
      new MAttributeName(new RDottedName("animal")),
      new MAttributeValue(new RDottedName("lizard"))
    );
  }

  @Override
  public String syntax()
  {
    return "<name> ':' <name>";
  }

  @Override
  public Class<MAttribute> convertedClass()
  {
    return MAttribute.class;
  }
}
