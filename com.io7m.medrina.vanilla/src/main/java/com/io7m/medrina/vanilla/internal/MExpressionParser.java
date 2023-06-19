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

import com.io7m.anethum.api.ParseStatus;
import com.io7m.jdeferthrow.core.ExceptionTracker;
import com.io7m.jlexing.core.LexicalPosition;
import com.io7m.jlexing.core.LexicalType;
import com.io7m.jsx.SExpressionType;
import com.io7m.jsx.SExpressionType.SAtomType;
import com.io7m.jsx.SExpressionType.SList;
import com.io7m.jsx.SExpressionType.SQuotedString;
import com.io7m.jsx.SExpressionType.SSymbol;
import com.io7m.junreachable.UnreachableCodeException;
import com.io7m.lanark.core.RDottedName;
import com.io7m.medrina.api.MActionName;
import com.io7m.medrina.api.MAttributeName;
import com.io7m.medrina.api.MAttributeValue;
import com.io7m.medrina.api.MMatchActionType;
import com.io7m.medrina.api.MMatchActionType.MMatchActionAnd;
import com.io7m.medrina.api.MMatchActionType.MMatchActionOr;
import com.io7m.medrina.api.MMatchActionType.MMatchActionWithName;
import com.io7m.medrina.api.MMatchObjectType;
import com.io7m.medrina.api.MMatchObjectType.MMatchObjectAnd;
import com.io7m.medrina.api.MMatchObjectType.MMatchObjectOr;
import com.io7m.medrina.api.MMatchObjectType.MMatchObjectWithAttributesAll;
import com.io7m.medrina.api.MMatchObjectType.MMatchObjectWithAttributesAny;
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
import com.io7m.medrina.api.MRuleName;
import com.io7m.medrina.api.MTypeName;
import com.io7m.medrina.api.MVersion;

import java.math.BigInteger;
import java.net.URI;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.TreeMap;
import java.util.function.Consumer;
import java.util.stream.Collectors;

import static com.io7m.anethum.api.ParseSeverity.PARSE_ERROR;
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
  private BigInteger ruleCount;
  private final Consumer<ParseStatus> errorConsumer;
  private final MStrings strings;
  private final String describeAttribute;
  private final String describeMatchAction;
  private final String describeMatchActionE;
  private final String describeMatchObject;
  private final String describeMatchObjectE;
  private final String describeMatchSubject;
  private final String describeMatchSubjectE;
  private final String describeRule;
  private final String describeRuleConclusion;
  private final String describeRuleDescription;
  private final String describeRuleName;
  private final String describeVersion;
  private final String syntaxAttribute;
  private final String syntaxMatchAction;
  private final String syntaxMatchActionE;
  private final String syntaxMatchObject;
  private final String syntaxMatchObjectE;
  private final String syntaxMatchSubject;
  private final String syntaxMatchSubjectE;
  private final String syntaxRule;
  private final String syntaxRuleConclusion;
  private final String syntaxRuleDescription;
  private final String syntaxRuleName;
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
    this.syntaxAttribute =
      inStrings.format("attribute");
    this.syntaxRuleName =
      inStrings.format("ruleName");
    this.syntaxRuleDescription =
      inStrings.format("ruleDescription");

    this.describeAttribute =
      inStrings.format("describeAttribute");
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
    this.describeRuleName =
      inStrings.format("describeRuleName");
    this.describeRuleDescription =
      inStrings.format("describeRuleDescription");

    this.ruleCount =
      BigInteger.ZERO;
  }

  private MMatchActionAnd parseMatchActionAnd(
    final List<SExpressionType> subExpressions)
    throws MExpressionParseException
  {
    final var exceptions =
      new ExceptionTracker<MExpressionParseException>();
    final var matches =
      new ArrayList<MMatchActionType>(subExpressions.size());

    for (int index = 1; index < subExpressions.size(); ++index) {
      final var expression = subExpressions.get(index);
      try {
        matches.add(this.parseMatchActionE(expression));
      } catch (final MExpressionParseException e) {
        exceptions.addException(e);
      }
    }

    exceptions.throwIfNecessary();
    return new MMatchActionAnd(matches);
  }

  private MMatchActionOr parseMatchActionOr(
    final List<SExpressionType> subExpressions)
    throws MExpressionParseException
  {
    final var exceptions =
      new ExceptionTracker<MExpressionParseException>();
    final var matches =
      new ArrayList<MMatchActionType>(subExpressions.size());

    for (int index = 1; index < subExpressions.size(); ++index) {
      final var expression = subExpressions.get(index);
      try {
        matches.add(this.parseMatchActionE(expression));
      } catch (final MExpressionParseException e) {
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
   * @throws MExpressionParseException On errors
   */

  public MMatchActionType parseMatchAction(
    final SExpressionType expression)
    throws MExpressionParseException
  {
    Objects.requireNonNull(expression, "expression");

    if (expression instanceof final SList list
        && list.size() == 2
        && list.get(0) instanceof final SSymbol symbol
        && Objects.equals(symbol.text(), "MatchAction")) {
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
    throws MExpressionParseException
  {
    if (expression instanceof final SSymbol symbol) {
      return switch (symbol.text()) {
        case "True" -> new MMatchActionTrue();
        case "False" -> new MMatchActionFalse();
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
          case "And" -> {
            try {
              yield this.parseMatchActionAnd(subExpressions);
            } catch (final MExpressionParseException e) {
              throw this.errorExpectedReceived(
                expression.lexical(),
                this.describeMatchActionE,
                this.show(expression),
                this.syntaxMatchActionE
              );
            }
          }
          case "Or" -> {
            try {
              yield this.parseMatchActionOr(subExpressions);
            } catch (final MExpressionParseException e) {
              throw this.errorExpectedReceived(
                expression.lexical(),
                this.describeMatchActionE,
                this.show(expression),
                this.syntaxMatchActionE
              );
            }
          }
          case "WithName" -> {
            try {
              yield this.parseMatchActionWithName(subExpressions);
            } catch (final MExpressionParseException e) {
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
    throws MExpressionParseException
  {
    final var exceptions =
      new ExceptionTracker<MExpressionParseException>();

    if (subExpressions.size() == 2) {
      final var expression = subExpressions.get(1);

      try {
        return new MMatchActionWithName(new MActionName(
          new RDottedName(
            this.requireSymbol(
                expression,
                this.describeMatchActionE,
                this.syntaxMatchActionE)
              .text()
          )
        ));
      } catch (final IllegalArgumentException e) {
        try {
          throw this.errorExpectedReceived(
            expression.lexical(),
            this.describeMatchActionE,
            this.show(expression),
            this.syntaxMatchActionE
          );
        } catch (final MExpressionParseException ex) {
          exceptions.addException(ex);
        }
      } catch (final MExpressionParseException e) {
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
   * @throws MExpressionParseException On errors
   */

  public MMatchObjectType parseMatchObject(
    final SExpressionType expression)
    throws MExpressionParseException
  {
    Objects.requireNonNull(expression, "expression");

    if (expression instanceof final SList list
        && list.size() == 2
        && list.get(0) instanceof final SSymbol symbol
        && Objects.equals(symbol.text(), "MatchObject")) {
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
    throws MExpressionParseException
  {
    if (expression instanceof final SSymbol symbol) {
      return this.parseMatchObjectESymbol(expression, symbol);
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
          case "And" -> {
            try {
              yield this.parseMatchObjectAnd(subExpressions);
            } catch (final MExpressionParseException e) {
              throw this.errorExpectedReceived(
                expression.lexical(),
                this.describeMatchObjectE,
                this.show(expression),
                this.syntaxMatchObjectE
              );
            }
          }

          case "Or" -> {
            try {
              yield this.parseMatchObjectOr(subExpressions);
            } catch (final MExpressionParseException e) {
              throw this.errorExpectedReceived(
                expression.lexical(),
                this.describeMatchObjectE,
                this.show(expression),
                this.syntaxMatchObjectE
              );
            }
          }

          case "WithAnyAttributesFrom" -> {
            try {
              yield this.parseMatchObjectWithAnyAttributes(subExpressions);
            } catch (final MExpressionParseException e) {
              throw this.errorExpectedReceived(
                expression.lexical(),
                this.describeMatchObjectE,
                this.show(expression),
                this.syntaxMatchObjectE
              );
            }
          }

          case "WithAllAttributesFrom" -> {
            try {
              yield this.parseMatchObjectWithAllAttributes(subExpressions);
            } catch (final MExpressionParseException e) {
              throw this.errorExpectedReceived(
                expression.lexical(),
                this.describeMatchObjectE,
                this.show(expression),
                this.syntaxMatchObjectE
              );
            }
          }

          case "WithType" -> {
            try {
              yield this.parseMatchObjectWithType(subExpressions);
            } catch (final MExpressionParseException e) {
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

  private MMatchObjectType parseMatchObjectESymbol(
    final SExpressionType expression,
    final SSymbol symbol)
    throws MExpressionParseException
  {
    return switch (symbol.text()) {
      case "True" -> new MMatchObjectTrue();
      case "False" -> new MMatchObjectFalse();
      default -> throw this.errorExpectedReceived(
        expression.lexical(),
        this.describeMatchObjectE,
        this.show(expression),
        this.syntaxMatchObjectE
      );
    };
  }

  private MMatchObjectType parseMatchObjectWithAnyAttributes(
    final List<SExpressionType> subExpressions)
    throws MExpressionParseException
  {
    final var exceptions =
      new ExceptionTracker<MExpressionParseException>();

    if (subExpressions.size() >= 1) {
      final var expression =
        subExpressions.get(0);

      final var tail =
        subExpressions.stream()
          .skip(1L)
          .toList();

      try {
        return new MMatchObjectWithAttributesAny(this.parseAttributes(tail));
      } catch (final IllegalArgumentException e) {
        try {
          throw this.errorExpectedReceived(
            expression.lexical(),
            this.describeMatchObjectE,
            this.show(expression),
            this.syntaxMatchObjectE
          );
        } catch (final MExpressionParseException ex) {
          exceptions.addException(ex);
        }
      } catch (final MExpressionParseException e) {
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

  private MMatchObjectType parseMatchObjectWithAllAttributes(
    final List<SExpressionType> subExpressions)
    throws MExpressionParseException
  {
    final var exceptions =
      new ExceptionTracker<MExpressionParseException>();

    if (subExpressions.size() >= 1) {
      final var expression =
        subExpressions.get(0);

      final var tail =
        subExpressions.stream()
          .skip(1L)
          .toList();

      try {
        return new MMatchObjectWithAttributesAll(this.parseAttributes(tail));
      } catch (final IllegalArgumentException e) {
        try {
          throw this.errorExpectedReceived(
            expression.lexical(),
            this.describeMatchObjectE,
            this.show(expression),
            this.syntaxMatchObjectE
          );
        } catch (final MExpressionParseException ex) {
          exceptions.addException(ex);
        }
      } catch (final MExpressionParseException e) {
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

  private Map<MAttributeName, MAttributeValue> parseAttributes(
    final List<SExpressionType> expressions)
    throws MExpressionParseException
  {
    final var exceptions =
      new ExceptionTracker<MExpressionParseException>();

    final var outputs = new TreeMap<MAttributeName, MAttributeValue>();
    for (final var expression : expressions) {
      try {
        this.parseAttribute(expression, outputs);
      } catch (final MExpressionParseException e) {
        exceptions.addException(e);
      }
    }

    exceptions.throwIfNecessary();
    return Collections.unmodifiableSortedMap(outputs);
  }

  private void parseAttribute(
    final SExpressionType expression,
    final Map<MAttributeName, MAttributeValue> outputs)
    throws MExpressionParseException
  {
    if (expression instanceof final SList list) {
      if (list.size() == 3) {
        if (list.get(0) instanceof final SSymbol kw
            && Objects.equals(kw.text(), "Attribute")
            && list.get(1) instanceof final SAtomType name
            && list.get(2) instanceof final SAtomType value) {

          outputs.put(
            new MAttributeName(new RDottedName(name.text())),
            new MAttributeValue(new RDottedName(value.text()))
          );
          return;
        }
      }
    }

    throw this.errorExpectedReceived(
      expression.lexical(),
      this.describeAttribute,
      this.show(expression),
      this.syntaxAttribute
    );
  }

  private MMatchObjectWithType parseMatchObjectWithType(
    final List<SExpressionType> subExpressions)
    throws MExpressionParseException
  {
    final var exceptions =
      new ExceptionTracker<MExpressionParseException>();

    if (subExpressions.size() == 2) {
      final var expression = subExpressions.get(1);

      try {
        return new MMatchObjectWithType(new MTypeName(
          new RDottedName(
            this.requireSymbol(
                expression,
                this.describeMatchObjectE,
                this.syntaxMatchObjectE)
              .text()
          )
        ));
      } catch (final IllegalArgumentException e) {
        try {
          throw this.errorExpectedReceived(
            expression.lexical(),
            this.describeMatchObjectE,
            this.show(expression),
            this.syntaxMatchObjectE
          );
        } catch (final MExpressionParseException ex) {
          exceptions.addException(ex);
        }
      } catch (final MExpressionParseException e) {
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
   * @throws MExpressionParseException On errors
   */

  public MMatchSubjectType parseMatchSubject(
    final SExpressionType expression)
    throws MExpressionParseException
  {
    Objects.requireNonNull(expression, "expression");

    if (expression instanceof final SList list
        && list.size() == 2
        && list.get(0) instanceof final SSymbol symbol
        && Objects.equals(symbol.text(), "MatchSubject")) {
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
    throws MExpressionParseException
  {
    if (expression instanceof final SSymbol symbol) {
      return switch (symbol.text()) {
        case "True" -> new MMatchSubjectTrue();
        case "False" -> new MMatchSubjectFalse();
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
          case "And" -> {
            try {
              yield this.parseMatchSubjectAnd(subExpressions);
            } catch (final MExpressionParseException e) {
              throw this.errorExpectedReceived(
                expression.lexical(),
                this.describeMatchSubjectE,
                this.show(expression),
                this.syntaxMatchSubjectE
              );
            }
          }
          case "Or" -> {
            try {
              yield this.parseMatchSubjectOr(subExpressions);
            } catch (final MExpressionParseException e) {
              throw this.errorExpectedReceived(
                expression.lexical(),
                this.describeMatchSubjectE,
                this.show(expression),
                this.syntaxMatchSubjectE
              );
            }
          }
          case "WithAllRolesFrom" -> {
            try {
              yield this.parseMatchSubjectRolesWithAll(subExpressions);
            } catch (final MExpressionParseException e) {
              throw this.errorExpectedReceived(
                expression.lexical(),
                this.describeMatchSubjectE,
                this.show(expression),
                this.syntaxMatchSubjectE
              );
            }
          }
          case "WithAnyRolesFrom" -> {
            try {
              yield this.parseMatchSubjectRolesWithAny(subExpressions);
            } catch (final MExpressionParseException e) {
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
    throws MExpressionParseException
  {
    final var exceptions =
      new ExceptionTracker<MExpressionParseException>();
    final var matches =
      new ArrayList<MMatchObjectType>(subExpressions.size());

    for (int index = 1; index < subExpressions.size(); ++index) {
      final var expression = subExpressions.get(index);
      try {
        matches.add(this.parseMatchObjectE(expression));
      } catch (final MExpressionParseException e) {
        exceptions.addException(e);
      }
    }

    exceptions.throwIfNecessary();
    return new MMatchObjectAnd(matches);
  }

  private MMatchObjectOr parseMatchObjectOr(
    final List<SExpressionType> subExpressions)
    throws MExpressionParseException
  {
    final var exceptions =
      new ExceptionTracker<MExpressionParseException>();
    final var matches =
      new ArrayList<MMatchObjectType>(subExpressions.size());

    for (int index = 1; index < subExpressions.size(); ++index) {
      final var expression = subExpressions.get(index);
      try {
        matches.add(this.parseMatchObjectE(expression));
      } catch (final MExpressionParseException e) {
        exceptions.addException(e);
      }
    }

    exceptions.throwIfNecessary();
    return new MMatchObjectOr(matches);
  }

  private MMatchSubjectAnd parseMatchSubjectAnd(
    final List<SExpressionType> subExpressions)
    throws MExpressionParseException
  {
    final var exceptions =
      new ExceptionTracker<MExpressionParseException>();
    final var matches =
      new ArrayList<MMatchSubjectType>(subExpressions.size());

    for (int index = 1; index < subExpressions.size(); ++index) {
      final var expression = subExpressions.get(index);
      try {
        matches.add(this.parseMatchSubjectE(expression));
      } catch (final MExpressionParseException e) {
        exceptions.addException(e);
      }
    }

    exceptions.throwIfNecessary();
    return new MMatchSubjectAnd(matches);
  }

  private MMatchSubjectOr parseMatchSubjectOr(
    final List<SExpressionType> subExpressions)
    throws MExpressionParseException
  {
    final var exceptions =
      new ExceptionTracker<MExpressionParseException>();
    final var matches =
      new ArrayList<MMatchSubjectType>(subExpressions.size());

    for (int index = 1; index < subExpressions.size(); ++index) {
      final var expression = subExpressions.get(index);
      try {
        matches.add(this.parseMatchSubjectE(expression));
      } catch (final MExpressionParseException e) {
        exceptions.addException(e);
      }
    }

    exceptions.throwIfNecessary();
    return new MMatchSubjectOr(matches);
  }

  private MMatchSubjectWithRolesAny parseMatchSubjectRolesWithAny(
    final List<SExpressionType> subExpressions)
    throws MExpressionParseException
  {
    final var exceptions =
      new ExceptionTracker<MExpressionParseException>();
    final var names =
      new HashSet<MRoleName>();

    for (int index = 1; index < subExpressions.size(); ++index) {
      final var expression = subExpressions.get(index);
      try {
        names.add(new MRoleName(
          new RDottedName(
            this.requireSymbol(
                expression,
                this.describeMatchSubjectE,
                this.syntaxMatchSubjectE)
              .text()
          )
        ));
      } catch (final IllegalArgumentException e) {
        try {
          throw this.errorExpectedReceived(
            expression.lexical(),
            this.describeMatchSubjectE,
            this.show(expression),
            this.syntaxMatchSubjectE
          );
        } catch (final MExpressionParseException ex) {
          exceptions.addException(ex);
        }
      } catch (final MExpressionParseException e) {
        exceptions.addException(e);
      }
    }

    exceptions.throwIfNecessary();
    return new MMatchSubjectWithRolesAny(Set.copyOf(names));
  }

  private MMatchSubjectWithRolesAll parseMatchSubjectRolesWithAll(
    final List<SExpressionType> subExpressions)
    throws MExpressionParseException
  {
    final var exceptions =
      new ExceptionTracker<MExpressionParseException>();
    final var names =
      new HashSet<MRoleName>();

    for (int index = 1; index < subExpressions.size(); ++index) {
      final var expression = subExpressions.get(index);
      try {
        names.add(new MRoleName(
          new RDottedName(
            this.requireSymbol(
                expression,
                this.describeMatchSubjectE,
                this.syntaxMatchSubjectE)
              .text()
          )
        ));
      } catch (final IllegalArgumentException e) {
        try {
          throw this.errorExpectedReceived(
            expression.lexical(),
            this.describeMatchSubjectE,
            this.show(expression),
            this.syntaxMatchSubjectE
          );
        } catch (final MExpressionParseException ex) {
          exceptions.addException(ex);
        }
      } catch (final MExpressionParseException e) {
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
    throws MExpressionParseException
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
    throws MExpressionParseException
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

  private MExpressionParseException errorExpectedReceived(
    final LexicalPosition<URI> lexical,
    final String objectType,
    final String received,
    final String expected)
  {
    final var builder =
      ParseStatus.builder(
        "parse-error",
        this.strings.format("errorParse")
      );

    builder.withSeverity(PARSE_ERROR);
    builder.withLexical(lexical);
    builder.withAttribute("Expected", expected);
    builder.withAttribute("Received", received);
    builder.withAttribute("Type", objectType);

    this.errorConsumer.accept(builder.build());
    return new MExpressionParseException();
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
   * @throws MExpressionParseException On errors
   */

  public MVersion parseVersion(
    final SExpressionType expression)
    throws MExpressionParseException
  {
    Objects.requireNonNull(expression, "expression");

    try {
      if (expression instanceof final SList list) {
        if (list.size() == 3
            && list.get(0) instanceof final SSymbol symbol
            && list.get(1) instanceof final SSymbol major
            && list.get(2) instanceof final SSymbol minor) {
          if (Objects.equals(symbol.text(), "Medrina")) {
            return new MVersion(
              new BigInteger(major.text()),
              new BigInteger(minor.text())
            );
          }
        }
      }
    } catch (final Exception e) {
      throw new MExpressionParseException(e);
    }

    throw this.errorExpectedReceived(
      expression.lexical(),
      this.describeVersion,
      this.show(expression),
      this.syntaxVersion
    );
  }

  private static boolean isListStartingWithSymbol(
    final SExpressionType expression,
    final String name)
  {
    return expression instanceof final SList ls
           && ls.size() > 0
           && ls.get(0) instanceof final SSymbol sym
           && Objects.equals(sym.text(), name);
  }

  private MExpressionParseException errorAlreadySpecified(
    final LexicalPosition<URI> lexical,
    final String objectType,
    final String existing)
  {
    final var builder =
      ParseStatus.builder(
        "parse-error",
        this.strings.format("errorAlreadyProvided")
      );

    builder.withSeverity(PARSE_ERROR);
    builder.withLexical(lexical);
    builder.withAttribute("Existing", existing);
    builder.withAttribute("Type", objectType);

    this.errorConsumer.accept(builder.build());
    return new MExpressionParseException();
  }

  private MExpressionParseException errorMissingRequired(
    final LexicalPosition<URI> lexical,
    final String objectType)
  {
    final var builder =
      ParseStatus.builder(
        "parse-error",
        this.strings.format("errorMissingRequired")
      );

    builder.withSeverity(PARSE_ERROR);
    builder.withLexical(lexical);
    builder.withAttribute("Required", objectType);

    this.errorConsumer.accept(builder.build());
    return new MExpressionParseException();
  }

  /**
   * Parse a rule.
   *
   * @param expression The raw expression
   *
   * @return A rule
   *
   * @throws MExpressionParseException On errors
   */

  public MRule parseRule(
    final SExpressionType expression)
    throws MExpressionParseException
  {
    Objects.requireNonNull(expression, "expression");

    if (!isListStartingWithSymbol(expression, "Rule")) {
      throw this.errorExpectedReceived(
        expression.lexical(),
        this.describeRule,
        this.show(expression),
        this.syntaxRule
      );
    }

    final SList list =
      this.requireList(expression, this.describeRule, this.syntaxRule);
    final var subExpressions =
      new ArrayList<>(list.expressions());

    subExpressions.remove(0);

    Optional<MRuleName> name = Optional.empty();
    Optional<String> description = Optional.empty();
    Optional<MRuleConclusion> conclusion = Optional.empty();
    Optional<MMatchActionType> matchAction = Optional.empty();
    Optional<MMatchObjectType> matchObject = Optional.empty();
    Optional<MMatchSubjectType> matchSubject = Optional.empty();

    final var exceptions =
      new ExceptionTracker<MExpressionParseException>();

    for (final var subExpression : subExpressions) {
      try {
        if (subExpression instanceof final SList subList
          && subList.size() >= 1
          && subList.get(0) instanceof final SSymbol sym) {

          switch (sym.text()) {
            case "Name" -> {
              if (name.isPresent()) {
                throw this.errorAlreadySpecified(
                  sym.lexical(),
                  this.describeRuleName,
                  name.get().value().value()
                );
              }
              name = Optional.of(this.parseRuleName(subList));
            }
            case "Description" -> {
              if (description.isPresent()) {
                throw this.errorAlreadySpecified(
                  sym.lexical(),
                  this.describeRuleDescription,
                  description.get()
                );
              }
              description = Optional.of(this.parseRuleDescription(subList));
            }
            case "Conclusion" -> {
              if (conclusion.isPresent()) {
                throw this.errorAlreadySpecified(
                  sym.lexical(),
                  this.describeRuleConclusion,
                  conclusion.toString()
                );
              }
              conclusion = Optional.of(this.parseRuleConclusion(subList));
            }
            case "MatchAction" -> {
              if (matchAction.isPresent()) {
                throw this.errorAlreadySpecified(
                  sym.lexical(),
                  this.describeMatchAction,
                  "[MatchAction ...]"
                );
              }
              matchAction = Optional.of(this.parseMatchAction(subList));
            }
            case "MatchSubject" -> {
              if (matchSubject.isPresent()) {
                throw this.errorAlreadySpecified(
                  sym.lexical(),
                  this.describeMatchSubject,
                  "[MatchSubject ...]"
                );
              }
              matchSubject = Optional.of(this.parseMatchSubject(subList));
            }
            case "MatchObject" -> {
              if (matchObject.isPresent()) {
                throw this.errorAlreadySpecified(
                  sym.lexical(),
                  this.describeMatchObject,
                  "[MatchObject ...]"
                );
              }
              matchObject = Optional.of(this.parseMatchObject(subList));
            }
            default -> {

            }
          }
        }
      } catch (final MExpressionParseException e) {
        exceptions.addException(e);
      }
    }

    this.checkRequired(
      matchSubject, exceptions, list, this.describeMatchSubject);
    this.checkRequired(
      matchAction, exceptions, list, this.describeMatchAction);
    this.checkRequired(
      matchObject, exceptions, list, this.describeMatchObject);
    this.checkRequired(
      conclusion, exceptions, list, this.describeRuleConclusion);

    exceptions.throwIfNecessary();

    return new MRule(
      name.orElseGet(this::freshRuleName),
      description.orElse(""),
      conclusion.get(),
      matchSubject.get(),
      matchObject.get(),
      matchAction.get()
    );
  }

  private MRuleName freshRuleName()
  {
    final var name =
      new MRuleName(new RDottedName("rule-%s".formatted(this.ruleCount)));
    this.ruleCount = this.ruleCount.add(BigInteger.ONE);
    return name;
  }

  private void checkRequired(
    final Optional<?> provided,
    final ExceptionTracker<MExpressionParseException> exceptions,
    final LexicalType<URI> expression,
    final String text)
  {
    if (provided.isEmpty()) {
      exceptions.addException(
        this.errorMissingRequired(expression.lexical(), text)
      );
    }
  }

  private String parseRuleDescription(
    final SList expression)
    throws MExpressionParseException
  {
    if (expression.size() == 2
        && expression.get(1) instanceof final SQuotedString quoted) {
      return quoted.text();
    }

    throw this.errorExpectedReceived(
      expression.lexical(),
      this.describeRuleDescription,
      this.show(expression),
      this.syntaxRuleDescription
    );
  }

  private MRuleName parseRuleName(
    final SList expression)
    throws MExpressionParseException
  {
    if (expression.size() == 2
        && expression.get(1) instanceof final SAtomType atom) {
      return new MRuleName(new RDottedName(atom.text()));
    }

    throw this.errorExpectedReceived(
      expression.lexical(),
      this.describeRuleName,
      this.show(expression),
      this.syntaxRuleName
    );
  }

  /**
   * Parse a security policy.
   *
   * @param expressions The policy rules
   *
   * @return A security policy
   *
   * @throws MExpressionParseException On errors
   */

  public MPolicy parsePolicy(
    final List<SExpressionType> expressions)
    throws MExpressionParseException
  {
    Objects.requireNonNull(expressions, "expressions");

    final var exceptions =
      new ExceptionTracker<MExpressionParseException>();
    final var rules =
      new ArrayList<MRule>(expressions.size());

    var first = true;
    for (final var expression : expressions) {
      if (first) {
        first = false;
        try {
          this.checkVersion(this.parseVersion(expression));
          continue;
        } catch (final MExpressionParseException e) {
          exceptions.addException(e);
          continue;
        }
      }

      try {
        rules.add(this.parseRule(expression));
      } catch (final MExpressionParseException e) {
        exceptions.addException(e);
      }
    }

    exceptions.throwIfNecessary();
    return new MPolicy(rules);
  }

  private MRuleConclusion parseRuleConclusion(
    final SList expression)
    throws MExpressionParseException
  {
    if (expression.size() == 2
        && expression.get(1) instanceof final SAtomType atom) {
      return switch (atom.text()) {
        case "Allow" -> MRuleConclusion.ALLOW;
        case "Deny" -> MRuleConclusion.DENY;
        case "AllowImmediately" -> MRuleConclusion.ALLOW_IMMEDIATELY;
        case "DenyImmediately" -> MRuleConclusion.DENY_IMMEDIATELY;
        default -> throw this.errorExpectedReceived(
          expression.lexical(),
          this.describeRuleConclusion,
          this.show(expression),
          this.syntaxRuleConclusion
        );
      };
    }

    throw this.errorExpectedReceived(
      expression.lexical(),
      this.describeRuleConclusion,
      this.show(expression),
      this.syntaxRuleConclusion
    );
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
   * @throws MExpressionParseException On errors
   */

  public void checkVersion(
    final MVersion version)
    throws MExpressionParseException
  {
    if (Objects.equals(version.major(), BigInteger.ONE)
        && Objects.equals(version.minor(), BigInteger.ZERO)) {
      return;
    }

    final var builder =
      ParseStatus.builder(
        "unsupported-version",
        this.strings.format("errorUnsupportedVersion")
      );

    builder.withAttribute(
      "Expected",
      String.format("%s.%s", BigInteger.ONE, BigInteger.ZERO)
    );
    builder.withAttribute(
      "Received",
      String.format("%s.%s", version.major(), version.minor())
    );
    builder.withSeverity(PARSE_ERROR);

    this.errorConsumer.accept(builder.build());
    throw new MExpressionParseException();
  }
}
