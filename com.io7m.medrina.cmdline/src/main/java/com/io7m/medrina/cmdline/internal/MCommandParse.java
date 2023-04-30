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

import com.beust.jcommander.Parameter;
import com.beust.jcommander.Parameters;
import com.io7m.anethum.common.ParseException;
import com.io7m.anethum.common.ParseStatus;
import com.io7m.claypot.core.CLPAbstractCommand;
import com.io7m.claypot.core.CLPCommandContextType;
import com.io7m.medrina.vanilla.MPolicyParsers;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.nio.file.Path;

import static com.io7m.claypot.core.CLPCommandType.Status.FAILURE;
import static com.io7m.claypot.core.CLPCommandType.Status.SUCCESS;

/**
 * The "parse" command.
 */

@Parameters(commandDescription = "Parse a security policy.")
public final class MCommandParse extends CLPAbstractCommand
{
  private static final Logger LOG =
    LoggerFactory.getLogger(MCommandParse.class);

  @Parameter(
    names = "--file",
    required = true,
    description = "The policy file.")
  private Path file;

  /**
   * Construct a command.
   *
   * @param inContext The command context
   */

  public MCommandParse(
    final CLPCommandContextType inContext)
  {
    super(inContext);
  }

  @Override
  protected Status executeActual()
    throws Exception
  {
    final var parsers =
      new MPolicyParsers();

    try (var parser =
           parsers.createParser(this.file, MCommandParse::logStatus)) {
      parser.execute();
    } catch (final ParseException e) {
      LOG.error("One or more parse errors were encountered.");
      return FAILURE;
    }
    return SUCCESS;
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
  public String name()
  {
    return "parse";
  }
}
