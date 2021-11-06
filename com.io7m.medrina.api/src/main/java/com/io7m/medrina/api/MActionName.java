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

import java.util.Comparator;
import java.util.Objects;
import java.util.regex.Pattern;

/**
 * The name of an action.
 *
 * @param value The name
 */

public record MActionName(String value)
  implements Comparable<MActionName>
{
  /**
   * The pattern that defines a valid action name.
   */

  public static final Pattern VALID_PATTERN =
    Pattern.compile("[a-z_0-9-\\.]{1,256}");

  /**
   * The name of an action.
   *
   * @param value The name
   */

  public MActionName
  {
    Objects.requireNonNull(value, "value");

    final var matcher = VALID_PATTERN.matcher(value);
    if (!matcher.matches()) {
      throw new IllegalArgumentException(
        String.format(
          "Action name '%s' must match %s",
          value,
          VALID_PATTERN
        ));
    }
  }

  @Override
  public int compareTo(
    final MActionName other)
  {
    return Comparator.comparing(MActionName::value).compare(this, other);
  }
}
