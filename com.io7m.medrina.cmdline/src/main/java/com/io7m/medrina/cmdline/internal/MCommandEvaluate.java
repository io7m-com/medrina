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
import com.io7m.medrina.api.MActionName;
import com.io7m.medrina.api.MObject;
import com.io7m.medrina.api.MPolicy;
import com.io7m.medrina.api.MPolicyEvaluator;
import com.io7m.medrina.api.MRoleName;
import com.io7m.medrina.api.MSubject;
import com.io7m.medrina.api.MTypeName;
import com.io7m.medrina.vanilla.MPolicyParsers;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static com.io7m.claypot.core.CLPCommandType.Status.FAILURE;
import static com.io7m.claypot.core.CLPCommandType.Status.SUCCESS;

/**
 * The "parse" command.
 */

@Parameters(commandDescription = "Evaluate an action against a security policy.")
public final class MCommandEvaluate extends CLPAbstractCommand
{
  private static final Logger LOG =
    LoggerFactory.getLogger(MCommandEvaluate.class);

  @Parameter(
    names = "--file",
    required = true,
    description = "The policy file.")
  private Path file;

  @Parameter(
    names = "--subject-role",
    required = false,
    description = "The subject's roles.")
  private List<String> rolesS = new ArrayList<>();

  @Parameter(
    names = "--object-type",
    required = true,
    description = "The object type.")
  private String objectTypeS;

  @Parameter(
    names = "--action",
    required = true,
    description = "The action.")
  private String actionS;

  /**
   * Construct a command.
   *
   * @param inContext The command context
   */

  public MCommandEvaluate(
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

    final MPolicy policy;
    try (var parser =
           parsers.createParser(this.file, MCommandEvaluate::logStatus)) {
      policy = parser.execute();
    } catch (final ParseException e) {
      LOG.error("One or more parse errors were encountered.");
      return FAILURE;
    }

    final var subject =
      new MSubject(
        this.rolesS.stream()
          .map(MRoleName::new)
          .collect(Collectors.toUnmodifiableSet())
      );

    final var object =
      new MObject(
        new MTypeName(this.objectTypeS),
        Map.of()
      );

    final var action =
      new MActionName(this.actionS);

    final var evaluator =
      MPolicyEvaluator.create();

    final var result =
      evaluator.evaluate(policy, subject, object, action);

    for (final var info : result.results()) {
      LOG.debug(
        "[{}] {} {} {}",
        Integer.valueOf(info.index()),
        Boolean.valueOf(info.matchedSubject()),
        Boolean.valueOf(info.matchedObject()),
        Boolean.valueOf(info.matchedAction())
      );
    }

    LOG.info("{}", result.accessResult());
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
    return "evaluate";
  }
}
