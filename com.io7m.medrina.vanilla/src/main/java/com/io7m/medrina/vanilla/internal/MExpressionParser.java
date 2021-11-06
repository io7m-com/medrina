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
  private final ArrayList<ParseStatus> errors;
  private final Consumer<ParseStatus> errorConsumer;
  private final String syntaxRoleName;
  private final String syntaxRoleMatch;
  private final String objectSubjectMatch;
  private final String objectObjectMatch;
  private final String syntaxObjectMatch;
  private final String syntaxTypeName;
  private final String objectActionMatch;
  private final String syntaxActionMatch;
  private final String syntaxActionName;
  private final String syntaxRule;
  private final String objectRule;
  private final String syntaxRuleConclusion;
  private final String objectRuleConclusion;

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
    this.errors =
      new ArrayList<ParseStatus>();

    this.objectActionMatch =
      this.strings.format("objectActionMatch");
    this.objectSubjectMatch =
      this.strings.format("objectSubjectMatch");
    this.objectObjectMatch =
      this.strings.format("objectObjectMatch");
    this.objectRule =
      this.strings.format("objectRule");
    this.objectRuleConclusion =
      this.strings.format("objectRuleConclusion");
    this.syntaxRoleName =
      this.strings.format("syntaxRoleName");
    this.syntaxActionName =
      this.strings.format("syntaxActionName");
    this.syntaxRoleMatch =
      this.strings.format("syntaxSubjectMatch");
    this.syntaxObjectMatch =
      this.strings.format("syntaxObjectMatch");
    this.syntaxActionMatch =
      this.strings.format("syntaxActionMatch");
    this.syntaxTypeName =
      this.strings.format("syntaxTypeName");
    this.syntaxRule =
      this.strings.format("syntaxRule");
    this.syntaxRuleConclusion =
      this.strings.format("syntaxRuleConclusion");
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
        matches.add(this.parseMatchAction(expression));
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
        matches.add(this.parseMatchAction(expression));
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

    if (expression instanceof SSymbol symbol) {
      return switch (symbol.text()) {
        case "true" -> new MMatchActionTrue();
        case "false" -> new MMatchActionFalse();
        default -> throw this.errorExpectedReceived(
          expression.lexical(),
          this.objectActionMatch,
          this.show(expression),
          this.syntaxActionMatch
        );
      };
    }

    if (expression instanceof SList list) {
      final var subExpressions = list.expressions();
      if (subExpressions.size() >= 1) {
        final var symbol =
          this.requireSymbol(
            subExpressions.get(0),
            this.objectActionMatch,
            this.syntaxActionMatch
          );

        return switch (symbol.text()) {
          case "and" -> {
            try {
              yield this.parseMatchActionAnd(subExpressions);
            } catch (final ExpressionParseException e) {
              throw this.errorExpectedReceived(
                expression.lexical(),
                this.objectActionMatch,
                this.show(expression),
                this.syntaxActionMatch
              );
            }
          }
          case "or" -> {
            try {
              yield this.parseMatchActionOr(subExpressions);
            } catch (final ExpressionParseException e) {
              throw this.errorExpectedReceived(
                expression.lexical(),
                this.objectActionMatch,
                this.show(expression),
                this.syntaxActionMatch
              );
            }
          }
          case "action-with-name" -> {
            try {
              yield this.parseMatchActionWithName(subExpressions);
            } catch (final ExpressionParseException e) {
              throw this.errorExpectedReceived(
                expression.lexical(),
                this.objectActionMatch,
                this.show(expression),
                this.syntaxActionMatch
              );
            }
          }
          default -> throw this.errorExpectedReceived(
            expression.lexical(),
            this.objectActionMatch,
            this.show(expression),
            this.syntaxActionMatch
          );
        };
      }
    }

    throw this.errorExpectedReceived(
      expression.lexical(),
      this.objectActionMatch,
      this.show(expression),
      this.syntaxActionMatch
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
              this.objectActionMatch,
              this.syntaxActionName)
            .text()
        ));
      } catch (final IllegalArgumentException e) {
        try {
          throw this.errorExpectedReceived(
            expression.lexical(),
            this.objectActionMatch,
            this.show(expression),
            this.syntaxTypeName
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
      this.objectActionMatch,
      this.show(subExpressions.get(0)),
      this.syntaxActionName
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

    if (expression instanceof SSymbol symbol) {
      return switch (symbol.text()) {
        case "true" -> new MMatchObjectTrue();
        case "false" -> new MMatchObjectFalse();
        default -> throw this.errorExpectedReceived(
          expression.lexical(),
          this.objectActionMatch,
          this.show(expression),
          this.syntaxActionMatch
        );
      };
    }

    if (expression instanceof SList list) {
      final var subExpressions = list.expressions();
      if (subExpressions.size() >= 1) {
        final var symbol =
          this.requireSymbol(
            subExpressions.get(0),
            this.objectObjectMatch,
            this.syntaxObjectMatch
          );

        return switch (symbol.text()) {
          case "and" -> {
            try {
              yield this.parseMatchObjectAnd(subExpressions);
            } catch (final ExpressionParseException e) {
              throw this.errorExpectedReceived(
                expression.lexical(),
                this.objectObjectMatch,
                this.show(expression),
                this.syntaxObjectMatch
              );
            }
          }
          case "or" -> {
            try {
              yield this.parseMatchObjectOr(subExpressions);
            } catch (final ExpressionParseException e) {
              throw this.errorExpectedReceived(
                expression.lexical(),
                this.objectObjectMatch,
                this.show(expression),
                this.syntaxObjectMatch
              );
            }
          }
          case "object-with-type" -> {
            try {
              yield this.parseMatchObjectWithType(subExpressions);
            } catch (final ExpressionParseException e) {
              throw this.errorExpectedReceived(
                expression.lexical(),
                this.objectObjectMatch,
                this.show(expression),
                this.syntaxObjectMatch
              );
            }
          }
          default -> throw this.errorExpectedReceived(
            expression.lexical(),
            this.objectObjectMatch,
            this.show(expression),
            this.syntaxObjectMatch
          );
        };
      }
    }

    throw this.errorExpectedReceived(
      expression.lexical(),
      this.objectObjectMatch,
      this.show(expression),
      this.syntaxObjectMatch
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
              this.objectSubjectMatch,
              this.syntaxTypeName)
            .text()
        ));
      } catch (final IllegalArgumentException e) {
        try {
          throw this.errorExpectedReceived(
            expression.lexical(),
            this.objectSubjectMatch,
            this.show(expression),
            this.syntaxTypeName
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
      this.objectSubjectMatch,
      this.show(subExpressions.get(0)),
      this.syntaxTypeName
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

    if (expression instanceof SSymbol symbol) {
      return switch (symbol.text()) {
        case "true" -> new MMatchSubjectTrue();
        case "false" -> new MMatchSubjectFalse();
        default -> throw this.errorExpectedReceived(
          expression.lexical(),
          this.objectActionMatch,
          this.show(expression),
          this.syntaxActionMatch
        );
      };
    }

    if (expression instanceof SList list) {
      final var subExpressions = list.expressions();
      if (subExpressions.size() >= 1) {
        final var symbol =
          this.requireSymbol(
            subExpressions.get(0),
            this.objectSubjectMatch,
            this.syntaxRoleMatch
          );

        return switch (symbol.text()) {
          case "and" -> {
            try {
              yield this.parseMatchRolesAnd(subExpressions);
            } catch (final ExpressionParseException e) {
              throw this.errorExpectedReceived(
                expression.lexical(),
                this.objectSubjectMatch,
                this.show(expression),
                this.syntaxRoleMatch
              );
            }
          }
          case "or" -> {
            try {
              yield this.parseMatchRolesOr(subExpressions);
            } catch (final ExpressionParseException e) {
              throw this.errorExpectedReceived(
                expression.lexical(),
                this.objectSubjectMatch,
                this.show(expression),
                this.syntaxRoleMatch
              );
            }
          }
          case "subject-with-all-roles" -> {
            try {
              yield this.parseMatchRolesWithAll(subExpressions);
            } catch (final ExpressionParseException e) {
              throw this.errorExpectedReceived(
                expression.lexical(),
                this.objectSubjectMatch,
                this.show(expression),
                this.syntaxRoleMatch
              );
            }
          }
          case "subject-with-any-roles" -> {
            try {
              yield this.parseMatchRolesWithAny(subExpressions);
            } catch (final ExpressionParseException e) {
              throw this.errorExpectedReceived(
                expression.lexical(),
                this.objectSubjectMatch,
                this.show(expression),
                this.syntaxRoleMatch
              );
            }
          }
          default -> throw this.errorExpectedReceived(
            expression.lexical(),
            this.objectSubjectMatch,
            this.show(expression),
            this.syntaxRoleMatch
          );
        };
      }
    }

    throw this.errorExpectedReceived(
      expression.lexical(),
      this.objectSubjectMatch,
      this.show(expression),
      this.syntaxRoleMatch
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
        matches.add(this.parseMatchObject(expression));
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
        matches.add(this.parseMatchObject(expression));
      } catch (final ExpressionParseException e) {
        exceptions.addException(e);
      }
    }

    exceptions.throwIfNecessary();
    return new MMatchObjectOr(matches);
  }

  private MMatchSubjectAnd parseMatchRolesAnd(
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
        matches.add(this.parseMatchSubject(expression));
      } catch (final ExpressionParseException e) {
        exceptions.addException(e);
      }
    }

    exceptions.throwIfNecessary();
    return new MMatchSubjectAnd(matches);
  }

  private MMatchSubjectOr parseMatchRolesOr(
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
        matches.add(this.parseMatchSubject(expression));
      } catch (final ExpressionParseException e) {
        exceptions.addException(e);
      }
    }

    exceptions.throwIfNecessary();
    return new MMatchSubjectOr(matches);
  }

  private MMatchSubjectWithRolesAny parseMatchRolesWithAny(
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
              this.objectSubjectMatch,
              this.syntaxRoleName)
            .text()
        ));
      } catch (final IllegalArgumentException e) {
        try {
          throw this.errorExpectedReceived(
            expression.lexical(),
            this.objectSubjectMatch,
            this.show(expression),
            this.syntaxRoleName
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

  private MMatchSubjectWithRolesAll parseMatchRolesWithAll(
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
              this.objectSubjectMatch,
              this.syntaxRoleName)
            .text()
        ));
      } catch (final IllegalArgumentException e) {
        try {
          throw this.errorExpectedReceived(
            expression.lexical(),
            this.objectSubjectMatch,
            this.show(expression),
            this.syntaxRoleName
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
    if (expression instanceof SSymbol symbol) {
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
    if (expression instanceof SList list) {
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

    this.errors.add(error);
    this.errorConsumer.accept(error);
    return new ExpressionParseException();
  }

  private String showInner(
    final SExpressionType expression,
    final boolean expand)
  {
    if (expression instanceof SList list) {
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

    if (expression instanceof SSymbol symbol) {
      return symbol.text();
    }

    if (expression instanceof SQuotedString quotedString) {
      return String.format("\"%s\"", quotedString.text());
    }

    throw new UnreachableCodeException();
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
        this.objectRule,
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
      this.objectRule,
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

    for (final var expression : expressions) {
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
        this.objectRuleConclusion,
        this.syntaxRuleConclusion);

    return switch (symbol.text()) {
      case "allow" -> MRuleConclusion.ALLOW;
      case "deny" -> MRuleConclusion.DENY;
      case "allow-immediately" -> MRuleConclusion.ALLOW_IMMEDIATELY;
      case "deny-immediately" -> MRuleConclusion.DENY_IMMEDIATELY;
      default -> throw this.errorExpectedReceived(
        expression.lexical(),
        this.objectRuleConclusion,
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
   * Parsing failed.
   */

  public static final class ExpressionParseException
    extends Exception
  {
    /**
     * Parsing failed.
     */

    public ExpressionParseException()
    {

    }
  }
}
