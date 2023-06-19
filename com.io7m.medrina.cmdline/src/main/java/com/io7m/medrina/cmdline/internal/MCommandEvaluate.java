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
import com.io7m.lanark.core.RDottedName;
import com.io7m.medrina.api.MActionName;
import com.io7m.medrina.api.MObject;
import com.io7m.medrina.api.MPolicy;
import com.io7m.medrina.api.MPolicyEvaluator;
import com.io7m.medrina.api.MRoleName;
import com.io7m.medrina.api.MSubject;
import com.io7m.medrina.api.MTypeName;
import com.io7m.medrina.vanilla.MPolicyParsers;
import com.io7m.quarrel.core.QCommandContextType;
import com.io7m.quarrel.core.QCommandMetadata;
import com.io7m.quarrel.core.QCommandStatus;
import com.io7m.quarrel.core.QCommandType;
import com.io7m.quarrel.core.QParameterNamed0N;
import com.io7m.quarrel.core.QParameterNamed1;
import com.io7m.quarrel.core.QParameterNamedType;
import com.io7m.quarrel.core.QStringType.QConstant;
import com.io7m.quarrel.ext.logback.QLogback;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.nio.file.Path;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import static com.io7m.quarrel.core.QCommandStatus.FAILURE;
import static com.io7m.quarrel.core.QCommandStatus.SUCCESS;

/**
 * The "parse" command.
 */

public final class MCommandEvaluate implements QCommandType
{
  private static final Logger LOG =
    LoggerFactory.getLogger(MCommandEvaluate.class);

  private final QCommandMetadata metadata;

  private static final QParameterNamed1<Path> POLICY_FILE =
    new QParameterNamed1<>(
      "--file",
      List.of(),
      new QConstant("The policy file."),
      Optional.empty(),
      Path.class
    );

  private static final QParameterNamed0N<String> SUBJECT_ROLES =
    new QParameterNamed0N<>(
      "--subject-role",
      List.of(),
      new QConstant("The subject's roles."),
      List.of(),
      String.class
    );

  private static final QParameterNamed1<String> OBJECT_TYPE =
    new QParameterNamed1<>(
      "--object-type",
      List.of(),
      new QConstant("The object type."),
      Optional.empty(),
      String.class
    );

  private static final QParameterNamed0N<MAttribute> OBJECT_ATTRIBUTES =
    new QParameterNamed0N<>(
      "--object-attribute",
      List.of(),
      new QConstant("The object attribute(s)."),
      List.of(),
      MAttribute.class
    );

  private static final QParameterNamed1<String> ACTION =
    new QParameterNamed1<>(
      "--action",
      List.of(),
      new QConstant("The action."),
      Optional.empty(),
      String.class
    );

  /**
   * Construct a command.
   */

  public MCommandEvaluate()
  {
    this.metadata = new QCommandMetadata(
      "evaluate",
      new QConstant("Evaluate an action against a security policy."),
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
      List.of(
        POLICY_FILE,
        SUBJECT_ROLES,
        OBJECT_TYPE,
        OBJECT_ATTRIBUTES,
        ACTION
      )
    );
  }

  @Override
  public QCommandStatus onExecute(
    final QCommandContextType context)
    throws Exception
  {
    final var parsers =
      new MPolicyParsers();

    final var file =
      context.parameterValue(POLICY_FILE);
    final var rolesS =
      context.parameterValues(SUBJECT_ROLES);
    final var objectTypeS =
      context.parameterValue(OBJECT_TYPE);
    final var objectAttributes =
      context.parameterValues(OBJECT_ATTRIBUTES);
    final var actionS =
      context.parameterValue(ACTION);

    final MPolicy policy;
    try (var parser =
           parsers.createParser(file, MCommandEvaluate::logStatus)) {
      policy = parser.execute();
    } catch (final ParsingException e) {
      LOG.error("One or more parse errors were encountered.");
      return FAILURE;
    }

    final var subject =
      new MSubject(
        rolesS.stream()
          .map(RDottedName::new)
          .map(MRoleName::new)
          .collect(Collectors.toUnmodifiableSet())
      );

    final var object =
      new MObject(
        new MTypeName(new RDottedName(objectTypeS)),
        objectAttributes.stream()
          .collect(Collectors.toMap(MAttribute::name, MAttribute::value))
      );

    final var action =
      new MActionName(new RDottedName(actionS));

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

  @Override
  public QCommandMetadata metadata()
  {
    return this.metadata;
  }
}
