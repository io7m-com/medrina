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
import com.io7m.jsx.SExpressionType.SQuotedString;
import com.io7m.junreachable.UnreachableCodeException;
import com.io7m.medrina.api.MAttributeName;
import com.io7m.medrina.api.MAttributeValue;
import com.io7m.medrina.api.MMatchActionType;
import com.io7m.medrina.api.MMatchObjectType;
import com.io7m.medrina.api.MMatchObjectType.MMatchObjectWithAttributesAll;
import com.io7m.medrina.api.MMatchObjectType.MMatchObjectWithAttributesAny;
import com.io7m.medrina.api.MMatchSubjectType;
import com.io7m.medrina.api.MPolicy;
import com.io7m.medrina.api.MRoleName;
import com.io7m.medrina.api.MRule;
import com.io7m.medrina.api.MRuleConclusion;
import com.io7m.medrina.api.MRuleName;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
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
    rules.add(new SList(
      zero(),
      false,
      List.of(
        new SSymbol(zero(), "Medrina"),
        new SSymbol(zero(), "1"),
        new SSymbol(zero(), "0")
      )
    ));

    for (final var rule : policy.rules()) {
      rules.add(serializeRule(rule));
    }

    return List.copyOf(rules);
  }

  private static SExpressionType serializeRule(
    final MRule rule)
  {
    final var name =
      serializeName(rule.name());
    final var description =
      serializeDescription(rule.description());
    final var conclusion =
      serializeConclusion(rule.conclusion());
    final var subjectMatch =
      serializeSubjectMatchOuter(rule.matchSubject());
    final var objectMatch =
      serializeObjectMatchOuter(rule.matchObject());
    final var actionMatch =
      serializeActionMatchOuter(rule.matchAction());

    return new SList(
      zero(),
      false,
      List.of(
        new SSymbol(zero(), "Rule"),
        name,
        description,
        conclusion,
        subjectMatch,
        objectMatch,
        actionMatch
      )
    );
  }

  private static SList serializeConclusion(
    final MRuleConclusion conclusion)
  {
    return new SList(
      zero(),
      true,
      List.of(
        new SSymbol(zero(), "Conclusion"),
        new SSymbol(
          zero(),
          switch (conclusion) {
            case ALLOW -> "Allow";
            case ALLOW_IMMEDIATELY -> "AllowImmediately";
            case DENY -> "Deny";
            case DENY_IMMEDIATELY -> "DenyImmediately";
          })
      )
    );
  }

  private static SList serializeDescription(
    final String description)
  {
    return new SList(
      zero(),
      true,
      List.of(
        new SSymbol(zero(), "Description"),
        new SQuotedString(zero(), description)
      )
    );
  }

  private static SList serializeName(
    final MRuleName name)
  {
    return new SList(
      zero(),
      true,
      List.of(
        new SSymbol(zero(), "Name"),
        new SSymbol(zero(), name.value().value())
      )
    );
  }

  private static SExpressionType serializeActionMatchOuter(
    final MMatchActionType m)
  {
    return new SList(
      zero(),
      true,
      List.of(
        new SSymbol(zero(), "MatchAction"),
        serializeActionMatchE(m)
      )
    );
  }

  private static SExpressionType serializeObjectMatchOuter(
    final MMatchObjectType m)
  {
    return new SList(
      zero(),
      true,
      List.of(
        new SSymbol(zero(), "MatchObject"),
        serializeObjectMatchE(m)
      )
    );
  }

  private static SExpressionType serializeSubjectMatchOuter(
    final MMatchSubjectType m)
  {
    return new SList(
      zero(),
      true,
      List.of(
        new SSymbol(zero(), "MatchSubject"),
        serializeSubjectMatchE(m)
      )
    );
  }

  private static SExpressionType serializeActionMatchE(
    final MMatchActionType matchAction)
  {
    if (matchAction instanceof MMatchActionTrue) {
      return new SSymbol(zero(), "True");
    }

    if (matchAction instanceof MMatchActionFalse) {
      return new SSymbol(zero(), "False");
    }

    if (matchAction instanceof final MMatchActionWithName name) {
      return new SList(
        zero(),
        true,
        List.of(
          new SSymbol(zero(), "WithName"),
          new SSymbol(zero(), name.name().value().value())
        )
      );
    }

    if (matchAction instanceof final MMatchActionOr or) {
      return new SList(
        zero(),
        true,
        Stream.concat(
          Stream.of(new SSymbol(zero(), "Or")),
          or.subExpressions()
            .stream()
            .map(MExpressionSerializer::serializeActionMatchE)
        ).collect(Collectors.toList())
      );
    }

    if (matchAction instanceof final MMatchActionAnd and) {
      return new SList(
        zero(),
        true,
        Stream.concat(
          Stream.of(new SSymbol(zero(), "And")),
          and.subExpressions()
            .stream()
            .map(MExpressionSerializer::serializeActionMatchE)
        ).collect(Collectors.toList())
      );
    }

    throw new UnreachableCodeException();
  }

  private static SExpressionType serializeObjectMatchE(
    final MMatchObjectType matchObject)
  {
    if (matchObject instanceof MMatchObjectTrue) {
      return new SSymbol(zero(), "True");
    }

    if (matchObject instanceof MMatchObjectFalse) {
      return new SSymbol(zero(), "False");
    }

    if (matchObject instanceof final MMatchObjectWithType type) {
      return new SList(
        zero(),
        true,
        List.of(
          new SSymbol(zero(), "WithType"),
          new SSymbol(zero(), type.type().value().value())
        )
      );
    }

    if (matchObject instanceof final MMatchObjectWithAttributesAll all) {
      return new SList(
        zero(),
        true,
        Stream.concat(
          Stream.of(new SSymbol(zero(), "WithAllAttributesFrom")),
          all.required()
            .entrySet()
            .stream()
            .sorted(Map.Entry.comparingByKey())
            .map(MExpressionSerializer::serializeAttribute)
        ).collect(Collectors.toList())
      );
    }

    if (matchObject instanceof final MMatchObjectWithAttributesAny any) {
      return new SList(
        zero(),
        true,
        Stream.concat(
          Stream.of(new SSymbol(zero(), "WithAnyAttributesFrom")),
          any.required()
            .entrySet()
            .stream()
            .sorted(Map.Entry.comparingByKey())
            .map(MExpressionSerializer::serializeAttribute)
        ).collect(Collectors.toList())
      );
    }

    if (matchObject instanceof final MMatchObjectOr or) {
      return new SList(
        zero(),
        true,
        Stream.concat(
          Stream.of(new SSymbol(zero(), "Or")),
          or.subExpressions()
            .stream()
            .map(MExpressionSerializer::serializeObjectMatchE)
        ).collect(Collectors.toList())
      );
    }

    if (matchObject instanceof final MMatchObjectAnd and) {
      return new SList(
        zero(),
        true,
        Stream.concat(
          Stream.of(new SSymbol(zero(), "And")),
          and.subExpressions()
            .stream()
            .map(MExpressionSerializer::serializeObjectMatchE)
        ).collect(Collectors.toList())
      );
    }

    throw new UnreachableCodeException();
  }

  private static SList serializeAttribute(
    final Map.Entry<MAttributeName, MAttributeValue> entry)
  {
    return new SList(
      zero(),
      true,
      List.of(
        new SSymbol(zero(), "Attribute"),
        new SQuotedString(zero(), entry.getKey().value().value()),
        new SQuotedString(zero(), entry.getValue().value().value())
      )
    );
  }

  private static SExpressionType serializeSubjectMatchE(
    final MMatchSubjectType matchSubject)
  {
    if (matchSubject instanceof MMatchSubjectTrue) {
      return new SSymbol(zero(), "True");
    }

    if (matchSubject instanceof MMatchSubjectFalse) {
      return new SSymbol(zero(), "False");
    }

    if (matchSubject instanceof final MMatchSubjectWithRolesAll all) {
      return new SList(
        zero(),
        true,
        Stream.concat(
          Stream.of(new SSymbol(zero(), "WithAllRolesFrom")),
          all.requiredRoles()
            .stream()
            .sorted(MRoleName::compareTo)
            .map(name -> new SSymbol(zero(), name.value().value()))
        ).collect(Collectors.toList())
      );
    }

    if (matchSubject instanceof final MMatchSubjectWithRolesAny any) {
      return new SList(
        zero(),
        true,
        Stream.concat(
          Stream.of(new SSymbol(zero(), "WithAnyRolesFrom")),
          any.requiredRoles()
            .stream()
            .sorted(MRoleName::compareTo)
            .map(name -> new SSymbol(zero(), name.value().value()))
        ).collect(Collectors.toList())
      );
    }

    if (matchSubject instanceof final MMatchSubjectOr or) {
      return new SList(
        zero(),
        true,
        Stream.concat(
          Stream.of(new SSymbol(zero(), "Or")),
          or.subExpressions()
            .stream()
            .map(MExpressionSerializer::serializeSubjectMatchE)
        ).collect(Collectors.toList())
      );
    }

    if (matchSubject instanceof final MMatchSubjectAnd and) {
      return new SList(
        zero(),
        true,
        Stream.concat(
          Stream.of(new SSymbol(zero(), "And")),
          and.subExpressions()
            .stream()
            .map(MExpressionSerializer::serializeSubjectMatchE)
        ).collect(Collectors.toList())
      );
    }

    throw new UnreachableCodeException();
  }
}
