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

import com.io7m.medrina.api.MRoleName;
import net.jqwik.api.ForAll;
import net.jqwik.api.Property;
import net.jqwik.api.constraints.LowerChars;
import net.jqwik.api.constraints.NumericChars;
import net.jqwik.api.constraints.StringLength;
import nl.jqno.equalsverifier.EqualsVerifier;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.TestFactory;

import java.util.stream.Stream;

public final class MRoleNameTest
{
  private static DynamicTest validTestOf(
    final String text)
  {
    return DynamicTest.dynamicTest(
      "testValid_" + text,
      () -> {
        new MRoleName(text);
      });
  }

  private static DynamicTest invalidTestOf(
    final String text)
  {
    return DynamicTest.dynamicTest(
      "testInvalid_" + text,
      () -> {
        Assertions.assertThrows(IllegalArgumentException.class, () -> {
          new MRoleName(text);
        });
      });
  }

  @Test
  public void testEquals()
  {
    EqualsVerifier.forClass(MRoleName.class)
      .withNonnullFields("value")
      .verify();
  }

  @TestFactory
  public Stream<DynamicTest> testInvalids()
  {
    return Stream.of("", "A", String.format("%0257x", Integer.valueOf(123)))
      .map(MRoleNameTest::invalidTestOf);
  }

  @TestFactory
  public Stream<DynamicTest> testValids()
  {
    return Stream.of(
        "a",
        "0",
        "_",
        "-",
        ".",
        "abcd1234abcd1234abcd1234abcd1234")
      .map(MRoleNameTest::validTestOf);
  }

  @Property
  public void testOrdering(
    @ForAll
    @LowerChars
    @NumericChars
    @StringLength(min = 1, max = 16) final String textA,
    @ForAll
    @LowerChars
    @NumericChars
    @StringLength(min = 1, max = 16) final String textB)
  {
    Assertions.assertEquals(
      textA.compareTo(textB),
      new MRoleName(textA).compareTo(new MRoleName(textB))
    );
  }
}
