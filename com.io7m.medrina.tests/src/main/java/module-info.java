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

/**
 * Mandatory Access Control (Test suite)
 */

open module com.io7m.medrina.tests
{
  requires com.io7m.medrina.api;
  requires com.io7m.medrina.cmdline;
  requires com.io7m.medrina.parser.api;
  requires com.io7m.medrina.vanilla;

  requires com.io7m.jdeferthrow.core;
  requires com.io7m.jeucreader.core;
  requires com.io7m.jsx.core;
  requires com.io7m.jsx.parser.api;
  requires com.io7m.jsx.parser;
  requires com.io7m.jsx.prettyprint;
  requires com.io7m.junreachable.core;
  requires com.io7m.jxtrand.vanilla;
  requires com.io7m.lanark.arbitraries;
  requires com.io7m.lanark.core;
  requires net.jqwik.api;
  requires org.apache.commons.io;
  requires org.apiguardian.api;
  requires org.slf4j;

  requires org.junit.jupiter.api;
  requires org.junit.jupiter.engine;
  requires org.junit.platform.commons;
  requires org.junit.platform.engine;
  requires org.junit.platform.launcher;

  provides net.jqwik.api.providers.ArbitraryProvider
    with com.io7m.medrina.tests.MActionNames,
      com.io7m.medrina.tests.MAttributeNames,
      com.io7m.medrina.tests.MAttributeValues,
      com.io7m.medrina.tests.MObjects,
      com.io7m.medrina.tests.MRuleNames,
      com.io7m.medrina.tests.MRoleNames,
      com.io7m.medrina.tests.MTypeNames,
      com.io7m.medrina.tests.MSubjects;

  exports com.io7m.medrina.tests;
}
