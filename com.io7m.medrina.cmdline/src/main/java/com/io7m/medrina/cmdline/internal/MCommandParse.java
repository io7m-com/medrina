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

import com.io7m.anethum.api.ParseStatus;
import com.io7m.anethum.api.ParsingException;
import com.io7m.medrina.vanilla.MPolicyParsers;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QCommandStatus;
import com.io7m.quarrel.core.QCommandType;
import com.io7m.quarrel.core.QParameterNamed1;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType;
import com.io7m.quarrel.ext.logback.QLogback;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.nio.file.Path;
import java.util.List;
import java.util.Optional;

import static com.io7m.quarrel.core.QCommandStatus.FAILURE;
import static com.io7m.quarrel.core.QCommandStatus.SUCCESS;

/**
 * The "parse" command.
 */

public final class MCommandParse implements QCommandType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(MCommandParse.class);

  private static final QParameterNamed1<Path> POLICY_FILE =
    new QParameterNamed1<>(
      "--file",
      List.of(),
      new QStringType.QConstant("The policy file."),
      Optional.empty(),
      Path.class
    );

  private final QCommandMetadata metadata;

  /**
   * Construct a command.
   */

  public MCommandParse()
  {
    this.metadata = new QCommandMetadata(
      "parse",
      new QStringType.QConstant("Parse a security policy."),
      Optional.empty()
    );
  }

  private static void logStatus(
    final ParseStatus status)
  {
    switch (status.severity()) {
      case PARSE_ERROR -> {
        LOG.error(
          "{}:{}: {}: {}",
          Integer.valueOf(status.lexical().line()),
          Integer.valueOf(status.lexical().column()),
          status.errorCode(),
          status.message()
        );
      }
      case PARSE_WARNING -> {
        LOG.warn(
          "{}:{}: {}: {}",
          Integer.valueOf(status.lexical().line()),
          Integer.valueOf(status.lexical().column()),
          status.errorCode(),
          status.message()
        );
      }
      case PARSE_INFO -> {
        LOG.info(
          "{}:{}: {}: {}",
          Integer.valueOf(status.lexical().line()),
          Integer.valueOf(status.lexical().column()),
          status.errorCode(),
          status.message()
        );
      }
    }
  }

  @Override
  public List<QParameterNamedType<?>> onListNamedParameters()
  {
    return QLogback.plusParameters(
      List.of(POLICY_FILE)
    );
  }

  @Override
  public QCommandStatus onExecute(
    final QCommandContextType context)
    throws Exception
  {
    final var file =
      context.parameterValue(POLICY_FILE);
    final var parsers =
      new MPolicyParsers();

    try (var parser =
           parsers.createParser(file, MCommandParse::logStatus)) {
      parser.execute();
    } catch (final ParsingException e) {
      LOG.error("One or more parse errors were encountered.");
      return FAILURE;
    }
    return SUCCESS;
  }

  @Override
  public QCommandMetadata metadata()
  {
    return this.metadata;
  }
}
