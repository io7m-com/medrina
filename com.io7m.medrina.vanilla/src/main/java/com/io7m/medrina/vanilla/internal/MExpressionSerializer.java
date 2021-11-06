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

import com.io7m.jsx.SExpressionType;
import com.io7m.junreachable.UnreachableCodeException;
import com.io7m.medrina.api.MMatchActionType;
import com.io7m.medrina.api.MMatchObjectType;
import com.io7m.medrina.api.MMatchSubjectType;
import com.io7m.medrina.api.MPolicy;
import com.io7m.medrina.api.MRule;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static com.io7m.jlexing.core.LexicalPositions.zero;
import static com.io7m.jsx.SExpressionType.SList;
import static com.io7m.jsx.SExpressionType.SSymbol;
import static com.io7m.medrina.api.MMatchActionType.MMatchActionAnd;
import static com.io7m.medrina.api.MMatchActionType.MMatchActionFalse;
import static com.io7m.medrina.api.MMatchActionType.MMatchActionOr;
import static com.io7m.medrina.api.MMatchActionType.MMatchActionTrue;
import static com.io7m.medrina.api.MMatchActionType.MMatchActionWithName;
import static com.io7m.medrina.api.MMatchObjectType.MMatchObjectAnd;
import static com.io7m.medrina.api.MMatchObjectType.MMatchObjectFalse;
import static com.io7m.medrina.api.MMatchObjectType.MMatchObjectOr;
import static com.io7m.medrina.api.MMatchObjectType.MMatchObjectTrue;
import static com.io7m.medrina.api.MMatchObjectType.MMatchObjectWithType;
import static com.io7m.medrina.api.MMatchSubjectType.MMatchSubjectAnd;
import static com.io7m.medrina.api.MMatchSubjectType.MMatchSubjectFalse;
import static com.io7m.medrina.api.MMatchSubjectType.MMatchSubjectOr;
import static com.io7m.medrina.api.MMatchSubjectType.MMatchSubjectTrue;
import static com.io7m.medrina.api.MMatchSubjectType.MMatchSubjectWithRolesAll;
import static com.io7m.medrina.api.MMatchSubjectType.MMatchSubjectWithRolesAny;

/**
 * An expression serializer.
 */

public final class MExpressionSerializer
{
  /**
   * An expression serializer.
   */

  public MExpressionSerializer()
  {

  }

  /**
   * Serialize the given policy.
   *
   * @param policy The policy
   *
   * @return A list of serialized s-expressions
   */

  public List<SExpressionType> serialize(
    final MPolicy policy)
  {
    Objects.requireNonNull(policy, "policy");

    final var rules = new ArrayList<SExpressionType>();
    for (final var rule : policy.rules()) {
      rules.add(this.serializeRule(rule));
    }

    return List.copyOf(rules);
  }

  private SExpressionType serializeRule(
    final MRule rule)
  {
    final var subjectMatch =
      this.serializeSubjectMatch(rule.matchSubject());
    final var objectMatch =
      this.serializeObjectMatch(rule.matchObject());
    final var actionMatch =
      this.serializeActionMatch(rule.matchAction());

    return switch (rule.conclusion()) {
      case ALLOW -> new SList(
        zero(),
        false,
        List.of(
          new SSymbol(zero(), "allow"),
          subjectMatch,
          objectMatch,
          actionMatch
        )
      );

      case DENY -> new SList(
        zero(),
        false,
        List.of(
          new SSymbol(zero(), "deny"),
          subjectMatch,
          objectMatch,
          actionMatch
        )
      );

      case ALLOW_IMMEDIATELY -> new SList(
        zero(),
        false,
        List.of(
          new SSymbol(zero(), "allow-immediately"),
          subjectMatch,
          objectMatch,
          actionMatch
        )
      );

      case DENY_IMMEDIATELY -> new SList(
        zero(),
        false,
        List.of(
          new SSymbol(zero(), "deny-immediately"),
          subjectMatch,
          objectMatch,
          actionMatch
        )
      );
    };
  }

  private SExpressionType serializeActionMatch(
    final MMatchActionType matchAction)
  {
    if (matchAction instanceof MMatchActionTrue) {
      return new SSymbol(zero(), "true");
    }

    if (matchAction instanceof MMatchActionFalse) {
      return new SSymbol(zero(), "false");
    }

    if (matchAction instanceof MMatchActionWithName name) {
      return new SList(
        zero(),
        true,
        List.of(
          new SSymbol(zero(), "action-with-name"),
          new SSymbol(zero(), name.name().value())
        )
      );
    }

    if (matchAction instanceof MMatchActionOr or) {
      return new SList(
        zero(),
        true,
        Stream.concat(
          Stream.of(new SSymbol(zero(), "or")),
          or.subExpressions()
            .stream()
            .map(this::serializeActionMatch)
        ).collect(Collectors.toList())
      );
    }

    if (matchAction instanceof MMatchActionAnd and) {
      return new SList(
        zero(),
        true,
        Stream.concat(
          Stream.of(new SSymbol(zero(), "and")),
          and.subExpressions()
            .stream()
            .map(this::serializeActionMatch)
        ).collect(Collectors.toList())
      );
    }

    throw new UnreachableCodeException();
  }

  private SExpressionType serializeObjectMatch(
    final MMatchObjectType matchObject)
  {
    if (matchObject instanceof MMatchObjectTrue) {
      return new SSymbol(zero(), "true");
    }

    if (matchObject instanceof MMatchObjectFalse) {
      return new SSymbol(zero(), "false");
    }

    if (matchObject instanceof MMatchObjectWithType type) {
      return new SList(
        zero(),
        true,
        List.of(
          new SSymbol(zero(), "object-with-type"),
          new SSymbol(zero(), type.type().value())
        )
      );
    }

    if (matchObject instanceof MMatchObjectOr or) {
      return new SList(
        zero(),
        true,
        Stream.concat(
          Stream.of(new SSymbol(zero(), "or")),
          or.subExpressions()
            .stream()
            .map(this::serializeObjectMatch)
        ).collect(Collectors.toList())
      );
    }

    if (matchObject instanceof MMatchObjectAnd and) {
      return new SList(
        zero(),
        true,
        Stream.concat(
          Stream.of(new SSymbol(zero(), "and")),
          and.subExpressions()
            .stream()
            .map(this::serializeObjectMatch)
        ).collect(Collectors.toList())
      );
    }

    throw new UnreachableCodeException();
  }

  private SExpressionType serializeSubjectMatch(
    final MMatchSubjectType matchSubject)
  {
    if (matchSubject instanceof MMatchSubjectTrue) {
      return new SSymbol(zero(), "true");
    }

    if (matchSubject instanceof MMatchSubjectFalse) {
      return new SSymbol(zero(), "false");
    }

    if (matchSubject instanceof MMatchSubjectWithRolesAll all) {
      return new SList(
        zero(),
        true,
        Stream.concat(
          Stream.of(new SSymbol(zero(), "subject-with-all-roles")),
          all.requiredRoles()
            .stream()
            .map(name -> new SSymbol(zero(), name.value()))
        ).collect(Collectors.toList())
      );
    }

    if (matchSubject instanceof MMatchSubjectWithRolesAny any) {
      return new SList(
        zero(),
        true,
        Stream.concat(
          Stream.of(new SSymbol(zero(), "subject-with-any-roles")),
          any.requiredRoles()
            .stream()
            .map(name -> new SSymbol(zero(), name.value()))
        ).collect(Collectors.toList())
      );
    }

    if (matchSubject instanceof MMatchSubjectOr or) {
      return new SList(
        zero(),
        true,
        Stream.concat(
          Stream.of(new SSymbol(zero(), "or")),
          or.subExpressions()
            .stream()
            .map(this::serializeSubjectMatch)
        ).collect(Collectors.toList())
      );
    }

    if (matchSubject instanceof MMatchSubjectAnd and) {
      return new SList(
        zero(),
        true,
        Stream.concat(
          Stream.of(new SSymbol(zero(), "and")),
          and.subExpressions()
            .stream()
            .map(this::serializeSubjectMatch)
        ).collect(Collectors.toList())
      );
    }

    throw new UnreachableCodeException();
  }
}
