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

package com.io7m.medrina.vanilla.internal;

import com.io7m.jxtrand.vanilla.JXTAbstractStrings;

import java.io.IOException;
import java.util.Locale;

/**
 * The strings used by the vanilla implementation.
 */

public final class MStrings extends JXTAbstractStrings
{
  /**
   * Construct a string provider.
   *
   * @param locale The locale
   *
   * @throws IOException On I/O errors
   */

  public MStrings(
    final Locale locale)
    throws IOException
  {
    super(
      locale,
      MStrings.class,
      "/com/io7m/medrina/vanilla/internal",
      "Messages"
    );
  }
}
