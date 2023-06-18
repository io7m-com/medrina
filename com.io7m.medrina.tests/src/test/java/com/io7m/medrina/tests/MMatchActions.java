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
import com.io7m.medrina.api.MMatchActionType.MMatchActionFalse;
import com.io7m.medrina.api.MMatchActionType.MMatchActionTrue;
import net.jqwik.api.Arbitraries;
import net.jqwik.api.Arbitrary;
import net.jqwik.api.arbitraries.IntegerArbitrary;

import java.util.List;

import static com.io7m.medrina.api.MMatchActionType.MMatchActionAnd;
import static com.io7m.medrina.api.MMatchActionType.MMatchActionOr;
import static com.io7m.medrina.api.MMatchActionType.MMatchActionWithName;

public final class MMatchActions
{
  private static final IntegerArbitrary CASE_INTEGERS =
    Arbitraries.integers()
      .between(0, 4);

  private MMatchActions()
  {

  }

  public static Arbitrary<MMatchActionType> trues()
  {
    return Arbitraries.of(new MMatchActionTrue());
  }

  public static Arbitrary<MMatchActionType> falses()
  {
    return Arbitraries.of(new MMatchActionFalse());
  }

  public static Arbitrary<MMatchActionType> arbitrary()
  {
    final Arbitrary<MActionName> names =
      Arbitraries.defaultFor(MActionName.class);

    return CASE_INTEGERS
      .map(integer -> generateAction(names, 0, integer));
  }

  private static MMatchActionType generateAction(
    final Arbitrary<MActionName> names,
    final int depth,
    final Integer integer)
  {
    if (depth >= 3) {
      return new MMatchActionTrue();
    }

    return switch (integer.intValue()) {
      case 0 -> new MMatchActionWithName(names.sample());
      case 1 -> new MMatchActionAnd(
        List.of(
          generateAction(names, depth + 1, CASE_INTEGERS.sample()),
          generateAction(names, depth + 1, CASE_INTEGERS.sample()),
          generateAction(names, depth + 1, CASE_INTEGERS.sample())
        )
      );
      case 2 -> new MMatchActionOr(
        List.of(
          generateAction(names, depth + 1, CASE_INTEGERS.sample()),
          generateAction(names, depth + 1, CASE_INTEGERS.sample()),
          generateAction(names, depth + 1, CASE_INTEGERS.sample())
        )
      );
      case 3 -> new MMatchActionTrue();
      case 4 -> new MMatchActionFalse();
      default -> throw new IllegalStateException();
    };
  }
}
