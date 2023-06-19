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

import java.util.HashSet;
import java.util.List;
import java.util.Objects;

/**
 * A security policy.
 *
 * @param rules The list of rules, in evaluation order
 */

public record MPolicy(List<MRule> rules)
{
  /**
   * A security policy.
   *
   * @param rules The list of rules, in evaluation order
   */

  public MPolicy
  {
    Objects.requireNonNull(rules, "rules");

    final var names = new HashSet<MRuleName>(rules.size());
    for (final var rule : rules) {
      if (names.contains(rule.name())) {
        throw new IllegalArgumentException(
          "Duplicate rule name: %s".formatted(rule.name().value().value())
        );
      }
      names.add(rule.name());
    }
  }
}
