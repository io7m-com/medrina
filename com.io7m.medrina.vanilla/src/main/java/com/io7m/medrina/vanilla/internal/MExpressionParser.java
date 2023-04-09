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

package com.io7m.medrina.vanilla.internal;

import com.io7m.anethum.common.ParseStatus;
import com.io7m.jdeferthrow.core.ExceptionTracker;
import com.io7m.jlexing.core.LexicalPosition;
import com.io7m.jsx.SExpressionType;
import com.io7m.jsx.SExpressionType.SList;
import com.io7m.jsx.SExpressionType.SQuotedString;
import com.io7m.jsx.SExpressionType.SSymbol;
import com.io7m.junreachable.UnreachableCodeException;
import com.io7m.medrina.api.MActionName;
import com.io7m.medrina.api.MMatchActionType;
import com.io7m.medrina.api.MMatchActionType.MMatchActionAnd;
import com.io7m.medrina.api.MMatchActionType.MMatchActionOr;
import com.io7m.medrina.api.MMatchActionType.MMatchActionWithName;
import com.io7m.medrina.api.MMatchObjectType;
import com.io7m.medrina.api.MMatchObjectType.MMatchObjectAnd;
import com.io7m.medrina.api.MMatchObjectType.MMatchObjectOr;
import com.io7m.medrina.api.MMatchObjectType.MMatchObjectWithType;
import com.io7m.medrina.api.MMatchSubjectType;
import com.io7m.medrina.api.MMatchSubjectType.MMatchSubjectAnd;
import com.io7m.medrina.api.MMatchSubjectType.MMatchSubjectOr;
import com.io7m.medrina.api.MMatchSubjectType.MMatchSubjectWithRolesAll;
import com.io7m.medrina.api.MMatchSubjectType.MMatchSubjectWithRolesAny;
import com.io7m.medrina.api.MPolicy;
import com.io7m.medrina.api.MRoleName;
import com.io7m.medrina.api.MRule;
import com.io7m.medrina.api.MRuleConclusion;
import com.io7m.medrina.api.MTypeName;
import com.io7m.medrina.api.MVersion;

import java.math.BigInteger;
import java.net.URI;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.function.Consumer;
import java.util.stream.Collectors;

import static com.io7m.anethum.common.ParseSeverity.PARSE_ERROR;
import static com.io7m.medrina.api.MMatchActionType.MMatchActionFalse;
import static com.io7m.medrina.api.MMatchActionType.MMatchActionTrue;
import static com.io7m.medrina.api.MMatchObjectType.MMatchObjectFalse;
import static com.io7m.medrina.api.MMatchObjectType.MMatchObjectTrue;
import static com.io7m.medrina.api.MMatchSubjectType.MMatchSubjectFalse;
import static com.io7m.medrina.api.MMatchSubjectType.MMatchSubjectTrue;

/**
 * An expression parser.
 */

public final class MExpressionParser
{
  private final MStrings strings;
  private final Consumer<ParseStatus> errorConsumer;
  private final String describeMatchAction;
  private final String describeMatchActionE;
  private final String describeMatchObject;
  private final String describeMatchObjectE;
  private final String describeMatchSubject;
  private final String describeMatchSubjectE;
  private final String describeRule;
  private final String describeRuleConclusion;
  private final String describeVersion;
  private final String syntaxMatchAction;
  private final String syntaxMatchActionE;
  private final String syntaxMatchObject;
  private final String syntaxMatchObjectE;
  private final String syntaxMatchSubject;
  private final String syntaxMatchSubjectE;
  private final String syntaxRule;
  private final String syntaxRuleConclusion;
  private final String syntaxVersion;

  /**
   * Construct a parser.
   *
   * @param inStrings       The strings
   * @param inErrorConsumer The error consumer
   */

  public MExpressionParser(
    final MStrings inStrings,
    final Consumer<ParseStatus> inErrorConsumer)
  {
    this.strings =
      Objects.requireNonNull(inStrings, "strings");
    this.errorConsumer =
      Objects.requireNonNull(inErrorConsumer, "errorConsumer");

    this.syntaxMatchActionE =
      inStrings.format("matchActionE");
    this.syntaxMatchSubjectE =
      inStrings.format("matchSubjectE");
    this.syntaxMatchObjectE =
      inStrings.format("matchObjectE");
    this.syntaxMatchAction =
      inStrings.format("matchAction");
    this.syntaxMatchSubject =
      inStrings.format("matchSubject");
    this.syntaxMatchObject =
      inStrings.format("matchObject");
    this.syntaxRule =
      inStrings.format("rule");
    this.syntaxRuleConclusion =
      inStrings.format("ruleConclusion");
    this.syntaxVersion =
      inStrings.format("version");

    this.describeMatchActionE =
      inStrings.format("describeMatchActionE");
    this.describeMatchSubjectE =
      inStrings.format("describeMatchSubjectE");
    this.describeMatchObjectE =
      inStrings.format("describeMatchObjectE");
    this.describeMatchAction =
      inStrings.format("describeMatchAction");
    this.describeMatchSubject =
      inStrings.format("describeMatchSubject");
    this.describeMatchObject =
      inStrings.format("describeMatchObject");
    this.describeRule =
      inStrings.format("describeRule");
    this.describeRuleConclusion =
      inStrings.format("describeRuleConclusion");
    this.describeVersion =
      inStrings.format("describeVersion");
  }

  private MMatchActionAnd parseMatchActionAnd(
    final List<SExpressionType> subExpressions)
    throws ExpressionParseException
  {
    final var exceptions =
      new ExceptionTracker<ExpressionParseException>();
    final var matches =
      new ArrayList<MMatchActionType>(subExpressions.size());

    for (int index = 1; index < subExpressions.size(); ++index) {
      final var expression = subExpressions.get(index);
      try {
        matches.add(this.parseMatchActionE(expression));
      } catch (final ExpressionParseException e) {
        exceptions.addException(e);
      }
    }

    exceptions.throwIfNecessary();
    return new MMatchActionAnd(matches);
  }

  private MMatchActionOr parseMatchActionOr(
    final List<SExpressionType> subExpressions)
    throws ExpressionParseException
  {
    final var exceptions =
      new ExceptionTracker<ExpressionParseException>();
    final var matches =
      new ArrayList<MMatchActionType>(subExpressions.size());

    for (int index = 1; index < subExpressions.size(); ++index) {
      final var expression = subExpressions.get(index);
      try {
        matches.add(this.parseMatchActionE(expression));
      } catch (final ExpressionParseException e) {
        exceptions.addException(e);
      }
    }

    exceptions.throwIfNecessary();
    return new MMatchActionOr(matches);
  }

  /**
   * Parse an object match expression.
   *
   * @param expression The raw expression
   *
   * @return A parsed expression
   *
   * @throws ExpressionParseException On errors
   */

  public MMatchActionType parseMatchAction(
    final SExpressionType expression)
    throws ExpressionParseException
  {
    Objects.requireNonNull(expression, "expression");

    if (expression instanceof SList list
        && list.size() == 2
        && list.get(0) instanceof SSymbol symbol
        && Objects.equals(symbol.text(), "action")) {
      return this.parseMatchActionE(list.get(1));
    }

    throw this.errorExpectedReceived(
      expression.lexical(),
      this.describeMatchAction,
      this.show(expression),
      this.syntaxMatchAction
    );
  }

  private MMatchActionType parseMatchActionE(
    final SExpressionType expression)
    throws ExpressionParseException
  {
    if (expression instanceof final SSymbol symbol) {
      return switch (symbol.text()) {
        case "true" -> new MMatchActionTrue();
        case "false" -> new MMatchActionFalse();
        default -> throw this.errorExpectedReceived(
          expression.lexical(),
          this.describeMatchActionE,
          this.show(expression),
          this.syntaxMatchActionE
        );
      };
    }

    if (expression instanceof final SList list) {
      final var subExpressions = list.expressions();
      if (subExpressions.size() >= 1) {
        final var symbol =
          this.requireSymbol(
            subExpressions.get(0),
            this.describeMatchActionE,
            this.syntaxMatchActionE
          );

        return switch (symbol.text()) {
          case "and" -> {
            try {
              yield this.parseMatchActionAnd(subExpressions);
            } catch (final ExpressionParseException e) {
              throw this.errorExpectedReceived(
                expression.lexical(),
                this.describeMatchActionE,
                this.show(expression),
                this.syntaxMatchActionE
              );
            }
          }
          case "or" -> {
            try {
              yield this.parseMatchActionOr(subExpressions);
            } catch (final ExpressionParseException e) {
              throw this.errorExpectedReceived(
                expression.lexical(),
                this.describeMatchActionE,
                this.show(expression),
                this.syntaxMatchActionE
              );
            }
          }
          case "with-name" -> {
            try {
              yield this.parseMatchActionWithName(subExpressions);
            } catch (final ExpressionParseException e) {
              throw this.errorExpectedReceived(
                expression.lexical(),
                this.describeMatchActionE,
                this.show(expression),
                this.syntaxMatchActionE
              );
            }
          }
          default -> throw this.errorExpectedReceived(
            expression.lexical(),
            this.describeMatchActionE,
            this.show(expression),
            this.syntaxMatchActionE
          );
        };
      }
    }

    throw this.errorExpectedReceived(
      expression.lexical(),
      this.describeMatchActionE,
      this.show(expression),
      this.syntaxMatchActionE
    );
  }

  private MMatchActionWithName parseMatchActionWithName(
    final List<SExpressionType> subExpressions)
    throws ExpressionParseException
  {
    final var exceptions =
      new ExceptionTracker<ExpressionParseException>();

    if (subExpressions.size() == 2) {
      final var expression = subExpressions.get(1);

      try {
        return new MMatchActionWithName(new MActionName(
          this.requireSymbol(
              expression,
              this.describeMatchActionE,
              this.syntaxMatchActionE)
            .text()
        ));
      } catch (final IllegalArgumentException e) {
        try {
          throw this.errorExpectedReceived(
            expression.lexical(),
            this.describeMatchActionE,
            this.show(expression),
            this.syntaxMatchActionE
          );
        } catch (final ExpressionParseException ex) {
          exceptions.addException(ex);
        }
      } catch (final ExpressionParseException e) {
        exceptions.addException(e);
      }
    }

    throw this.errorExpectedReceived(
      subExpressions.get(0).lexical(),
      this.describeMatchActionE,
      this.show(subExpressions.get(0)),
      this.syntaxMatchActionE
    );
  }

  /**
   * Parse an object match expression.
   *
   * @param expression The raw expression
   *
   * @return A parsed expression
   *
   * @throws ExpressionParseException On errors
   */

  public MMatchObjectType parseMatchObject(
    final SExpressionType expression)
    throws ExpressionParseException
  {
    Objects.requireNonNull(expression, "expression");

    if (expression instanceof SList list
        && list.size() == 2
        && list.get(0) instanceof SSymbol symbol
        && Objects.equals(symbol.text(), "object")) {
      return this.parseMatchObjectE(list.get(1));
    }

    throw this.errorExpectedReceived(
      expression.lexical(),
      this.describeMatchObject,
      this.show(expression),
      this.syntaxMatchObject
    );
  }

  private MMatchObjectType parseMatchObjectE(
    final SExpressionType expression)
    throws ExpressionParseException
  {
    if (expression instanceof final SSymbol symbol) {
      return switch (symbol.text()) {
        case "true" -> new MMatchObjectTrue();
        case "false" -> new MMatchObjectFalse();
        default -> throw this.errorExpectedReceived(
          expression.lexical(),
          this.describeMatchObjectE,
          this.show(expression),
          this.syntaxMatchObjectE
        );
      };
    }

    if (expression instanceof final SList list) {
      final var subExpressions = list.expressions();
      if (subExpressions.size() >= 1) {
        final var symbol =
          this.requireSymbol(
            subExpressions.get(0),
            this.describeMatchObjectE,
            this.syntaxMatchObjectE
          );

        return switch (symbol.text()) {
          case "and" -> {
            try {
              yield this.parseMatchObjectAnd(subExpressions);
            } catch (final ExpressionParseException e) {
              throw this.errorExpectedReceived(
                expression.lexical(),
                this.describeMatchObjectE,
                this.show(expression),
                this.syntaxMatchObjectE
              );
            }
          }
          case "or" -> {
            try {
              yield this.parseMatchObjectOr(subExpressions);
            } catch (final ExpressionParseException e) {
              throw this.errorExpectedReceived(
                expression.lexical(),
                this.describeMatchObjectE,
                this.show(expression),
                this.syntaxMatchObjectE
              );
            }
          }
          case "with-type" -> {
            try {
              yield this.parseMatchObjectWithType(subExpressions);
            } catch (final ExpressionParseException e) {
              throw this.errorExpectedReceived(
                expression.lexical(),
                this.describeMatchObjectE,
                this.show(expression),
                this.syntaxMatchObjectE
              );
            }
          }
          default -> throw this.errorExpectedReceived(
            expression.lexical(),
            this.describeMatchObjectE,
            this.show(expression),
            this.syntaxMatchObjectE
          );
        };
      }
    }

    throw this.errorExpectedReceived(
      expression.lexical(),
      this.describeMatchObjectE,
      this.show(expression),
      this.syntaxMatchObjectE
    );
  }

  private MMatchObjectWithType parseMatchObjectWithType(
    final List<SExpressionType> subExpressions)
    throws ExpressionParseException
  {
    final var exceptions =
      new ExceptionTracker<ExpressionParseException>();

    if (subExpressions.size() == 2) {
      final var expression = subExpressions.get(1);

      try {
        return new MMatchObjectWithType(new MTypeName(
          this.requireSymbol(
              expression,
              this.describeMatchObjectE,
              this.syntaxMatchObjectE)
            .text()
        ));
      } catch (final IllegalArgumentException e) {
        try {
          throw this.errorExpectedReceived(
            expression.lexical(),
            this.describeMatchObjectE,
            this.show(expression),
            this.syntaxMatchObjectE
          );
        } catch (final ExpressionParseException ex) {
          exceptions.addException(ex);
        }
      } catch (final ExpressionParseException e) {
        exceptions.addException(e);
      }
    }

    throw this.errorExpectedReceived(
      subExpressions.get(0).lexical(),
      this.describeMatchObjectE,
      this.show(subExpressions.get(0)),
      this.syntaxMatchObjectE
    );
  }

  /**
   * Parse a subject role match expression.
   *
   * @param expression The raw expression
   *
   * @return A parsed expression
   *
   * @throws ExpressionParseException On errors
   */

  public MMatchSubjectType parseMatchSubject(
    final SExpressionType expression)
    throws ExpressionParseException
  {
    Objects.requireNonNull(expression, "expression");

    if (expression instanceof SList list
        && list.size() == 2
        && list.get(0) instanceof SSymbol symbol
        && Objects.equals(symbol.text(), "subject")) {
      return this.parseMatchSubjectE(list.get(1));
    }

    throw this.errorExpectedReceived(
      expression.lexical(),
      this.describeMatchSubject,
      this.show(expression),
      this.syntaxMatchSubject
    );
  }

  private MMatchSubjectType parseMatchSubjectE(
    final SExpressionType expression)
    throws ExpressionParseException
  {
    if (expression instanceof final SSymbol symbol) {
      return switch (symbol.text()) {
        case "true" -> new MMatchSubjectTrue();
        case "false" -> new MMatchSubjectFalse();
        default -> throw this.errorExpectedReceived(
          expression.lexical(),
          this.describeMatchSubjectE,
          this.show(expression),
          this.syntaxMatchSubjectE
        );
      };
    }

    if (expression instanceof final SList list) {
      final var subExpressions = list.expressions();
      if (subExpressions.size() >= 1) {
        final var symbol =
          this.requireSymbol(
            subExpressions.get(0),
            this.describeMatchSubjectE,
            this.syntaxMatchSubjectE
          );

        return switch (symbol.text()) {
          case "and" -> {
            try {
              yield this.parseMatchSubjectAnd(subExpressions);
            } catch (final ExpressionParseException e) {
              throw this.errorExpectedReceived(
                expression.lexical(),
                this.describeMatchSubjectE,
                this.show(expression),
                this.syntaxMatchSubjectE
              );
            }
          }
          case "or" -> {
            try {
              yield this.parseMatchSubjectOr(subExpressions);
            } catch (final ExpressionParseException e) {
              throw this.errorExpectedReceived(
                expression.lexical(),
                this.describeMatchSubjectE,
                this.show(expression),
                this.syntaxMatchSubjectE
              );
            }
          }
          case "with-all-roles" -> {
            try {
              yield this.parseMatchSubjectRolesWithAll(subExpressions);
            } catch (final ExpressionParseException e) {
              throw this.errorExpectedReceived(
                expression.lexical(),
                this.describeMatchSubjectE,
                this.show(expression),
                this.syntaxMatchSubjectE
              );
            }
          }
          case "with-any-roles" -> {
            try {
              yield this.parseMatchSubjectRolesWithAny(subExpressions);
            } catch (final ExpressionParseException e) {
              throw this.errorExpectedReceived(
                expression.lexical(),
                this.describeMatchSubjectE,
                this.show(expression),
                this.syntaxMatchSubjectE
              );
            }
          }
          default -> throw this.errorExpectedReceived(
            expression.lexical(),
            this.describeMatchSubjectE,
            this.show(expression),
            this.syntaxMatchSubjectE
          );
        };
      }
    }

    throw this.errorExpectedReceived(
      expression.lexical(),
      this.describeMatchSubjectE,
      this.show(expression),
      this.syntaxMatchSubjectE
    );
  }

  private MMatchObjectAnd parseMatchObjectAnd(
    final List<SExpressionType> subExpressions)
    throws ExpressionParseException
  {
    final var exceptions =
      new ExceptionTracker<ExpressionParseException>();
    final var matches =
      new ArrayList<MMatchObjectType>(subExpressions.size());

    for (int index = 1; index < subExpressions.size(); ++index) {
      final var expression = subExpressions.get(index);
      try {
        matches.add(this.parseMatchObjectE(expression));
      } catch (final ExpressionParseException e) {
        exceptions.addException(e);
      }
    }

    exceptions.throwIfNecessary();
    return new MMatchObjectAnd(matches);
  }

  private MMatchObjectOr parseMatchObjectOr(
    final List<SExpressionType> subExpressions)
    throws ExpressionParseException
  {
    final var exceptions =
      new ExceptionTracker<ExpressionParseException>();
    final var matches =
      new ArrayList<MMatchObjectType>(subExpressions.size());

    for (int index = 1; index < subExpressions.size(); ++index) {
      final var expression = subExpressions.get(index);
      try {
        matches.add(this.parseMatchObjectE(expression));
      } catch (final ExpressionParseException e) {
        exceptions.addException(e);
      }
    }

    exceptions.throwIfNecessary();
    return new MMatchObjectOr(matches);
  }

  private MMatchSubjectAnd parseMatchSubjectAnd(
    final List<SExpressionType> subExpressions)
    throws ExpressionParseException
  {
    final var exceptions =
      new ExceptionTracker<ExpressionParseException>();
    final var matches =
      new ArrayList<MMatchSubjectType>(subExpressions.size());

    for (int index = 1; index < subExpressions.size(); ++index) {
      final var expression = subExpressions.get(index);
      try {
        matches.add(this.parseMatchSubjectE(expression));
      } catch (final ExpressionParseException e) {
        exceptions.addException(e);
      }
    }

    exceptions.throwIfNecessary();
    return new MMatchSubjectAnd(matches);
  }

  private MMatchSubjectOr parseMatchSubjectOr(
    final List<SExpressionType> subExpressions)
    throws ExpressionParseException
  {
    final var exceptions =
      new ExceptionTracker<ExpressionParseException>();
    final var matches =
      new ArrayList<MMatchSubjectType>(subExpressions.size());

    for (int index = 1; index < subExpressions.size(); ++index) {
      final var expression = subExpressions.get(index);
      try {
        matches.add(this.parseMatchSubjectE(expression));
      } catch (final ExpressionParseException e) {
        exceptions.addException(e);
      }
    }

    exceptions.throwIfNecessary();
    return new MMatchSubjectOr(matches);
  }

  private MMatchSubjectWithRolesAny parseMatchSubjectRolesWithAny(
    final List<SExpressionType> subExpressions)
    throws ExpressionParseException
  {
    final var exceptions =
      new ExceptionTracker<ExpressionParseException>();
    final var names =
      new HashSet<MRoleName>();

    for (int index = 1; index < subExpressions.size(); ++index) {
      final var expression = subExpressions.get(index);
      try {
        names.add(new MRoleName(
          this.requireSymbol(
              expression,
              this.describeMatchSubjectE,
              this.syntaxMatchSubjectE)
            .text()
        ));
      } catch (final IllegalArgumentException e) {
        try {
          throw this.errorExpectedReceived(
            expression.lexical(),
            this.describeMatchSubjectE,
            this.show(expression),
            this.syntaxMatchSubjectE
          );
        } catch (final ExpressionParseException ex) {
          exceptions.addException(ex);
        }
      } catch (final ExpressionParseException e) {
        exceptions.addException(e);
      }
    }

    exceptions.throwIfNecessary();
    return new MMatchSubjectWithRolesAny(Set.copyOf(names));
  }

  private MMatchSubjectWithRolesAll parseMatchSubjectRolesWithAll(
    final List<SExpressionType> subExpressions)
    throws ExpressionParseException
  {
    final var exceptions =
      new ExceptionTracker<ExpressionParseException>();
    final var names =
      new HashSet<MRoleName>();

    for (int index = 1; index < subExpressions.size(); ++index) {
      final var expression = subExpressions.get(index);
      try {
        names.add(new MRoleName(
          this.requireSymbol(
              expression,
              this.describeMatchSubjectE,
              this.syntaxMatchSubjectE)
            .text()
        ));
      } catch (final IllegalArgumentException e) {
        try {
          throw this.errorExpectedReceived(
            expression.lexical(),
            this.describeMatchSubjectE,
            this.show(expression),
            this.syntaxMatchSubjectE
          );
        } catch (final ExpressionParseException ex) {
          exceptions.addException(ex);
        }
      } catch (final ExpressionParseException e) {
        exceptions.addException(e);
      }
    }

    exceptions.throwIfNecessary();
    return new MMatchSubjectWithRolesAll(Set.copyOf(names));
  }

  private SSymbol requireSymbol(
    final SExpressionType expression,
    final String objectType,
    final String expected)
    throws ExpressionParseException
  {
    if (expression instanceof final SSymbol symbol) {
      return symbol;
    }

    throw this.errorExpectedReceived(
      expression.lexical(),
      objectType,
      this.show(expression),
      expected
    );
  }

  private SList requireList(
    final SExpressionType expression,
    final String objectType,
    final String expected)
    throws ExpressionParseException
  {
    if (expression instanceof final SList list) {
      return list;
    }

    throw this.errorExpectedReceived(
      expression.lexical(),
      objectType,
      this.show(expression),
      expected
    );
  }

  private ExpressionParseException errorExpectedReceived(
    final LexicalPosition<URI> lexical,
    final String objectType,
    final String received,
    final String expected)
  {
    final var error =
      ParseStatus.builder()
        .setErrorCode("parse-error")
        .setMessage(this.strings.format(
          "errorExpectedReceived",
          objectType,
          expected,
          received))
        .setLexical(lexical)
        .setSeverity(PARSE_ERROR)
        .build();

    this.errorConsumer.accept(error);
    return new ExpressionParseException();
  }

  private String showInner(
    final SExpressionType expression,
    final boolean expand)
  {
    if (expression instanceof final SList list) {
      final String inner;
      if (expand) {
        inner = list.expressions()
          .stream()
          .map(e -> this.showInner(e, false))
          .collect(Collectors.joining(" "));
      } else {
        inner = "...";
      }

      if (list.isSquare()) {
        return String.format("[%s]", inner);
      }
      return String.format("(%s)", inner);
    }

    if (expression instanceof final SSymbol symbol) {
      return symbol.text();
    }

    if (expression instanceof final SQuotedString quotedString) {
      return String.format("\"%s\"", quotedString.text());
    }

    throw new UnreachableCodeException();
  }

  /**
   * Parse a version expression.
   *
   * @param expression The raw expression
   *
   * @return A version
   *
   * @throws ExpressionParseException On errors
   */

  public MVersion parseVersion(
    final SExpressionType expression)
    throws ExpressionParseException
  {
    Objects.requireNonNull(expression, "expression");

    try {
      if (expression instanceof final SList list) {
        if (list.size() == 3
            && list.get(0) instanceof final SSymbol symbol
            && list.get(1) instanceof final SSymbol major
            && list.get(2) instanceof final SSymbol minor) {
          if (Objects.equals(symbol.text(), "medrina")) {
            return new MVersion(
              new BigInteger(major.text()),
              new BigInteger(minor.text())
            );
          }
        }
      }
    } catch (final Exception e) {
      throw new ExpressionParseException(e);
    }

    throw this.errorExpectedReceived(
      expression.lexical(),
      this.describeVersion,
      this.show(expression),
      this.syntaxVersion
    );
  }

  /**
   * Parse a rule.
   *
   * @param expression The raw expression
   *
   * @return A rule
   *
   * @throws ExpressionParseException On errors
   */

  public MRule parseRule(
    final SExpressionType expression)
    throws ExpressionParseException
  {
    Objects.requireNonNull(expression, "expression");

    final SList list =
      this.requireList(
        expression,
        this.describeRule,
        this.syntaxRule);

    final var subExpressions = list.expressions();
    if (subExpressions.size() == 4) {
      final var exceptions =
        new ExceptionTracker<ExpressionParseException>();

      MRuleConclusion conclusion = null;
      try {
        conclusion = this.parseRuleConclusion(subExpressions.get(0));
      } catch (final ExpressionParseException e) {
        exceptions.addException(e);
      }

      MMatchSubjectType matchSubject = null;
      try {
        matchSubject = this.parseMatchSubject(subExpressions.get(1));
      } catch (final ExpressionParseException e) {
        exceptions.addException(e);
      }

      MMatchObjectType matchObject = null;
      try {
        matchObject = this.parseMatchObject(subExpressions.get(2));
      } catch (final ExpressionParseException e) {
        exceptions.addException(e);
      }

      MMatchActionType matchAction = null;
      try {
        matchAction = this.parseMatchAction(subExpressions.get(3));
      } catch (final ExpressionParseException e) {
        exceptions.addException(e);
      }

      exceptions.throwIfNecessary();
      return new MRule(
        conclusion,
        matchSubject,
        matchObject,
        matchAction
      );
    }

    throw this.errorExpectedReceived(
      expression.lexical(),
      this.describeRule,
      this.show(expression),
      this.syntaxRule
    );
  }

  /**
   * Parse a security policy.
   *
   * @param expressions The policy rules
   *
   * @return A security policy
   *
   * @throws ExpressionParseException On errors
   */

  public MPolicy parsePolicy(
    final List<SExpressionType> expressions)
    throws ExpressionParseException
  {
    Objects.requireNonNull(expressions, "expressions");

    final var exceptions =
      new ExceptionTracker<ExpressionParseException>();
    final var rules =
      new ArrayList<MRule>(expressions.size());

    var first = true;
    for (final var expression : expressions) {
      if (first) {
        first = false;
        try {
          this.checkVersion(this.parseVersion(expression));
          continue;
        } catch (final ExpressionParseException e) {
          exceptions.addException(e);
          continue;
        }
      }

      try {
        rules.add(this.parseRule(expression));
      } catch (final ExpressionParseException e) {
        exceptions.addException(e);
      }
    }

    exceptions.throwIfNecessary();
    return new MPolicy(rules);
  }

  private MRuleConclusion parseRuleConclusion(
    final SExpressionType expression)
    throws ExpressionParseException
  {
    final SSymbol symbol =
      this.requireSymbol(
        expression,
        this.describeRuleConclusion,
        this.syntaxRuleConclusion);

    return switch (symbol.text()) {
      case "allow" -> MRuleConclusion.ALLOW;
      case "deny" -> MRuleConclusion.DENY;
      case "allow-immediately" -> MRuleConclusion.ALLOW_IMMEDIATELY;
      case "deny-immediately" -> MRuleConclusion.DENY_IMMEDIATELY;
      default -> throw this.errorExpectedReceived(
        expression.lexical(),
        this.describeRuleConclusion,
        this.show(expression),
        this.syntaxRuleConclusion
      );
    };
  }

  private String show(
    final SExpressionType expression)
  {
    return this.showInner(expression, true);
  }

  /**
   * Check the given version is supported.
   *
   * @param version The version
   *
   * @throws ExpressionParseException On errors
   */

  public void checkVersion(
    final MVersion version)
    throws ExpressionParseException
  {
    if (Objects.equals(version.major(), BigInteger.ONE)
        && Objects.equals(version.minor(), BigInteger.ZERO)) {
      return;
    }

    final var error =
      ParseStatus.builder()
        .setErrorCode("unsupported-version")
        .setMessage(this.strings.format(
          "errorUnsupportedVersion",
          version.major(),
          version.minor(),
          BigInteger.ONE,
          BigInteger.ZERO
        ))
        .setSeverity(PARSE_ERROR)
        .build();

    this.errorConsumer.accept(error);
    throw new ExpressionParseException();
  }

  /**
   * Parsing failed.
   */

  public static final class ExpressionParseException
    extends Exception
  {
    /**
     * Parsing failed.
     *
     * @param cause The cause
     */

    public ExpressionParseException(
      final Throwable cause)
    {
      super(cause);
    }

    /**
     * Parsing failed.
     */

    public ExpressionParseException()
    {

    }
  }
}
