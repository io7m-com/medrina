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

import com.io7m.anethum.api.ParsingException;
import com.io7m.anethum.api.SerializationException;
import com.io7m.medrina.api.MPolicy;
import com.io7m.medrina.vanilla.MPolicyParsers;
import com.io7m.medrina.vanilla.MPolicySerializers;
import net.jqwik.api.Arbitrary;
import net.jqwik.api.ForAll;
import net.jqwik.api.Property;
import net.jqwik.api.Provide;
import net.jqwik.api.constraints.Size;
import org.apache.commons.io.input.BrokenInputStream;
import org.apache.commons.io.output.BrokenOutputStream;
import org.junit.jupiter.api.Test;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.InputStream;
import java.net.URI;
import java.time.Duration;

import static java.nio.charset.StandardCharsets.UTF_8;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTimeout;

public final class MPolicyParserSerializerTest
{
  @Provide
  public Arbitrary<MPolicy> policies()
  {
    return MPolicies.policies();
  }

  @Property
  public void testRoundTrip(
    @ForAll("policies") final MPolicy policy)
    throws Exception
  {
    assertFalse(policy.rules().isEmpty());

    final var serializers =
      new MPolicySerializers();
    final var parsers =
      new MPolicyParsers();

    try (var byteOut = new ByteArrayOutputStream()) {
      try (var serializer = serializers.createSerializer(
        URI.create("urn:output"),
        byteOut)) {
        serializer.execute(policy);
      }

      byteOut.flush();

      try (var parser = parsers.createParser(
        URI.create("urn:output"),
        new ByteArrayInputStream(byteOut.toByteArray()),
        parseStatus -> {
        }
      )) {
        final var read = parser.execute();
        assertEquals(policy, read);
      }
    }
  }

  @Property
  public void testParseGarbage(
    @ForAll @Size(min = 1, max = 1000) final String data)
  {
    final var parsers = new MPolicyParsers();

    if (data.isBlank() || data.startsWith("#")) {
      return;
    }

    assertTimeout(Duration.ofSeconds(1000L), () -> {
      try {
        assertThrows(ParsingException.class, () -> {
          parsers.parse(
            URI.create("urn:create"),
            new ByteArrayInputStream(data.getBytes(UTF_8)));
        });
      } catch (final Exception e) {
        System.out.println("Input failed to fail: " + data);
      }
    });
  }

  @Test
  public void testParseIO()
  {
    final var parsers = new MPolicyParsers();

    assertThrows(ParsingException.class, () -> {
      parsers.parse(
        URI.create("urn:create"),
        new BrokenInputStream()
      );
    });
  }

  @Property
  public void testSerializeIO(
    @ForAll("policies") final MPolicy policy)
    throws Exception
  {
    assertFalse(policy.rules().isEmpty());

    final var serializers =
      new MPolicySerializers();

    assertThrows(SerializationException.class, () -> {
      serializers.serialize(
        URI.create("urn:create"),
        new BrokenOutputStream(),
        policy
      );
    });
  }

  @Test
  public void testParseExample0()
    throws Exception
  {
    final var parsers = new MPolicyParsers();

    try (var stream = resource("example0.mp")) {
      try {
        final var policy =
          parsers.parse(URI.create("urn:create"), stream);
      } catch (final ParsingException e) {
        e.statusValues().forEach(System.out::println);
        throw e;
      }
    }
  }

  @Test
  public void testParseErrorDuplicateRuleNames()
    throws Exception
  {
    final var parsers = new MPolicyParsers();

    try (var stream = resource("errorDuplicateRule0.mp")) {
      assertThrows(ParsingException.class, () -> {
        parsers.parse(URI.create("urn:create"), stream);
      });
    }
  }

  @Test
  public void testParseUnknownVersion0()
    throws Exception
  {
    final var parsers = new MPolicyParsers();

    assertThrows(ParsingException.class, () -> {
      parsers.parse(
        URI.create("urn:create"),
        new ByteArrayInputStream("[Medrina 9999 0]".getBytes(UTF_8))
      );
    });
  }

  private static InputStream resource(
    final String name)
  {
    final var path =
      "/com/io7m/medrina/tests/%s".formatted(name);

    return MPolicyParserSerializerTest.class.getResourceAsStream(path);
  }
}
