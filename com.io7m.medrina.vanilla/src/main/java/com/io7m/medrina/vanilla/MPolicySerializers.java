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

package com.io7m.medrina.vanilla;

import com.io7m.anethum.api.SerializationException;
import com.io7m.anethum.api.Unused;
import com.io7m.jsx.prettyprint.JSXPrettyPrinterCodeStyle;
import com.io7m.jsx.prettyprint.JSXPrettyPrinterType;
import com.io7m.medrina.api.MPolicy;
import com.io7m.medrina.parser.api.MPolicySerializerFactoryType;
import com.io7m.medrina.parser.api.MPolicySerializerType;
import com.io7m.medrina.vanilla.internal.MExpressionSerializer;

import java.io.IOException;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.net.URI;
import java.util.Objects;

import static java.nio.charset.StandardCharsets.UTF_8;

/**
 * The default provider of policy parsers.
 */

public final class MPolicySerializers implements MPolicySerializerFactoryType
{
  /**
   * The default provider of policy parsers.
   */

  public MPolicySerializers()
  {

  }

  @Override
  public MPolicySerializerType createSerializerWithContext(
    final Unused context,
    final URI target,
    final OutputStream stream)
  {
    final var writer =
      new OutputStreamWriter(stream, UTF_8);
    final var printer =
      JSXPrettyPrinterCodeStyle.newPrinterWithWidthIndent(
        writer, 80, 1);

    return new MPolicySerializer(stream, printer);
  }

  private static final class MPolicySerializer
    implements MPolicySerializerType
  {
    private final OutputStream stream;
    private final JSXPrettyPrinterType printer;

    MPolicySerializer(
      final OutputStream inStream,
      final JSXPrettyPrinterType inPrinter)
    {
      this.stream =
        Objects.requireNonNull(inStream, "stream");
      this.printer =
        Objects.requireNonNull(inPrinter, "printer");
    }

    @Override
    public void execute(
      final MPolicy value)
      throws SerializationException
    {
      Objects.requireNonNull(value, "value");

      try {
        final var expressions =
          new MExpressionSerializer()
            .serialize(value);

        for (final var expression : expressions) {
          this.printer.print(expression);
        }

        this.printer.close();
      } catch (final IOException e) {
        throw new SerializationException(e.getMessage(), e);
      }
    }

    @Override
    public void close()
      throws IOException
    {
      this.stream.close();
    }
  }
}
