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

package com.io7m.medrina.tests;

import com.io7m.anethum.api.ParseStatus;
import com.io7m.jeucreader.UnicodeCharacterReader;
import com.io7m.jsx.SExpressionType;
import com.io7m.jsx.api.lexer.JSXLexerComment;
import com.io7m.jsx.api.lexer.JSXLexerConfiguration;
import com.io7m.jsx.api.parser.JSXParserConfiguration;
import com.io7m.jsx.lexer.JSXLexer;
import com.io7m.jsx.parser.JSXParser;
import com.io7m.jsx.prettyprint.JSXPrettyPrinterCodeStyle;
import com.io7m.lanark.core.RDottedName;
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
import com.io7m.medrina.api.MRuleName;
import com.io7m.medrina.api.MTypeName;
import com.io7m.medrina.vanilla.internal.MExpressionParser;
import com.io7m.medrina.vanilla.internal.MExpressionSerializer;
import com.io7m.medrina.vanilla.internal.MStrings;
import net.jqwik.api.Arbitrary;
import net.jqwik.api.ForAll;
import net.jqwik.api.Property;
import net.jqwik.api.Provide;
import net.jqwik.api.lifecycle.BeforeProperty;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.io.StringReader;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.List;
import java.util.Locale;
import java.util.Optional;
import java.util.Set;

import static com.io7m.medrina.api.MRuleConclusion.ALLOW;
import static com.io7m.medrina.api.MRuleConclusion.ALLOW_IMMEDIATELY;
import static com.io7m.medrina.api.MRuleConclusion.DENY;
import static com.io7m.medrina.api.MRuleConclusion.DENY_IMMEDIATELY;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

public final class MExpressionParserTest
{
  private static final Logger LOG =
    LoggerFactory.getLogger(MExpressionParserTest.class);

  private ArrayList<ParseStatus> errors;

  private static MRoleName role(
    final String x)
  {
    return new MRoleName(new RDottedName(x));
  }

  private static MTypeName type(
    final String x)
  {
    return new MTypeName(new RDottedName(x));
  }

  private static MActionName action(
    final String x)
  {
    return new MActionName(new RDottedName(x));
  }

  @BeforeEach
  @BeforeProperty
  public void setup()
  {
    this.errors = new ArrayList<>();
  }

  private SExpressionType parse(
    final String text)
    throws Exception
  {
    final var lexerConfig =
      new JSXLexerConfiguration(
        true,
        true,
        Optional.empty(),
        EnumSet.of(JSXLexerComment.COMMENT_HASH),
        1
      );

    final var parserConfig =
      new JSXParserConfiguration(true);
    final var reader =
      UnicodeCharacterReader.newReader(new StringReader(text));
    final var lexer =
      JSXLexer.newLexer(lexerConfig, reader);
    final var parser =
      JSXParser.newParser(parserConfig, lexer);

    return parser.parseExpression();
  }

  @Test
  public void testMatchRoleError0()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchSubject(this.parse("(what x y z)"));
    });

    this.assertErrors(1);
  }

  @Test
  public void testMatchRoleError1()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchSubject(this.parse("()"));
    });

    this.assertErrors(1);
  }

  @Test
  public void testMatchRoleError2()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchSubject(this.parse("x"));
    });

    this.assertErrors(1);
  }

  @Test
  public void testMatchRoleError3()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchSubject(this.parse("[what x y z]"));
    });

    this.assertErrors(1);
  }

  @Test
  public void testMatchSubjectError0()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchSubject(this.parse("(MatchSubject x)"));
    });

    this.assertErrors(1);
  }

  @Test
  public void testMatchSubjectError1()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchSubject(this.parse("(MatchSubject \"x\")"));
    });

    this.assertErrors(1);
  }

  @Test
  public void testMatchSubjectError2()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchSubject(this.parse("(MatchSubject [x])"));
    });

    this.assertErrors(1);
  }

  @Test
  public void testSubjectWithAllRolesError0()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchSubject(this.parse("(MatchSubject (WithAllRolesFrom X Y Z))"));
    });

    this.assertErrors(4);
  }

  @Test
  public void testSubjectWithAllRolesError1()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchSubject(this.parse("(MatchSubject (WithAllRolesFrom () \"x\"))"));
    });

    this.assertErrors(3);
  }

  @Test
  public void testSubjectWithAllRoles0()
    throws Exception
  {
    final var r =
      (MMatchSubjectWithRolesAll) this.createParser()
        .parseMatchSubject(this.parse("(MatchSubject (WithAllRolesFrom x y z))"));

    assertEquals(
      Set.of(
        role("x"),
        role("y"),
        role("z")),
      r.requiredRoles()
    );
  }

  @Test
  public void testSubjectWithAllRoles1()
    throws Exception
  {
    final var r =
      (MMatchSubjectWithRolesAll) this.createParser()
        .parseMatchSubject(this.parse("(MatchSubject (WithAllRolesFrom))"));

    assertEquals(
      Set.of(),
      r.requiredRoles()
    );
  }

  @Test
  public void testSubjectWithAnyRolesError0()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchSubject(this.parse("(MatchSubject (WithAnyRolesFrom X Y Z))"));
    });

    this.assertErrors(4);
  }

  @Test
  public void testSubjectWithAnyRolesError1()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchSubject(this.parse("(MatchSubject (WithAnyRolesFrom () \"x\"))"));
    });

    this.assertErrors(3);
  }

  @Test
  public void testSubjectWithAnyRoles0()
    throws Exception
  {
    final var r =
      (MMatchSubjectWithRolesAny) this.createParser()
        .parseMatchSubject(this.parse("(MatchSubject (WithAnyRolesFrom x y z))"));

    assertEquals(
      Set.of(
        role("x"),
        role("y"),
        role("z")),
      r.requiredRoles()
    );
  }

  @Test
  public void testSubjectWithAnyRoles1()
    throws Exception
  {
    final var r =
      (MMatchSubjectWithRolesAny) this.createParser()
        .parseMatchSubject(this.parse("(MatchSubject (WithAnyRolesFrom))"));

    assertEquals(
      Set.of(),
      r.requiredRoles()
    );
  }

  @Test
  public void testMatchRolesAnd0()
    throws Exception
  {
    final var r =
      (MMatchSubjectAnd) this.createParser()
        .parseMatchSubject(this.parse(
          "(MatchSubject (And (WithAnyRolesFrom x y z) (WithAllRolesFrom a b c)))"));

    final var any =
      (MMatchSubjectWithRolesAny) r.subExpressions().get(0);
    final var all =
      (MMatchSubjectWithRolesAll) r.subExpressions().get(1);

    assertEquals(
      Set.of(
        role("x"),
        role("y"),
        role("z")),
      any.requiredRoles()
    );

    assertEquals(
      Set.of(
        role("a"),
        role("b"),
        role("c")),
      all.requiredRoles()
    );
  }

  @Test
  public void testMatchRolesAndError0()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchSubject(this.parse(
          "(MatchSubject (And (WithAllRolesFrom X) (WithAnyRolesFrom Y)))"));
    });

    this.assertErrors(5);
  }

  @Test
  public void testMatchRolesOr0()
    throws Exception
  {
    final var r =
      (MMatchSubjectOr) this.createParser()
        .parseMatchSubject(this.parse(
          "(MatchSubject (Or (WithAnyRolesFrom x y z) (WithAllRolesFrom a b c)))"));

    final var any =
      (MMatchSubjectWithRolesAny) r.subExpressions().get(0);
    final var all =
      (MMatchSubjectWithRolesAll) r.subExpressions().get(1);

    assertEquals(
      Set.of(
        role("x"),
        role("y"),
        role("z")),
      any.requiredRoles()
    );

    assertEquals(
      Set.of(
        role("a"),
        role("b"),
        role("c")),
      all.requiredRoles()
    );
  }

  @Test
  public void testMatchRolesOrError0()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchSubject(this.parse(
          "(MatchSubject (Or (WithAllRolesFrom X) (WithAnyRolesFrom Y)))"));
    });

    this.assertErrors(5);
  }

  @Test
  public void testMatchObjectError0()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchObject(this.parse("(what x y z)"));
    });

    this.assertErrors(1);
  }

  @Test
  public void testMatchObjectError1()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchObject(this.parse("()"));
    });

    this.assertErrors(1);
  }

  @Test
  public void testMatchObjectError2()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchObject(this.parse("x"));
    });

    this.assertErrors(1);
  }

  @Test
  public void testMatchObjectError3()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchObject(this.parse("[what x y z]"));
    });

    this.assertErrors(1);
  }

  @Test
  public void testMatchObjectError4()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchObject(this.parse("(MatchObject (with-q X))"));
    });

    this.assertErrors(1);
  }

  @Test
  public void testMatchObjectError5()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchObject(this.parse("(MatchObject \"q\")"));
    });

    this.assertErrors(1);
  }

  @Test
  public void testMatchObjectError6()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchObject(this.parse("(MatchObject q)"));
    });

    this.assertErrors(1);
  }

  @Test
  public void testObjectWithTypeError0()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchObject(this.parse("(MatchObject (WithType X))"));
    });

    this.assertErrors(3);
  }

  @Test
  public void testObjectWithTypeError1()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchObject(this.parse("(MatchObject (WithType ()))"));
    });

    this.assertErrors(3);
  }

  @Test
  public void testObjectWithType0()
    throws Exception
  {
    final var r =
      (MMatchObjectWithType) this.createParser()
        .parseMatchObject(this.parse("(MatchObject (WithType x))"));

    assertEquals(
      type("x"),
      r.type()
    );
  }

  @Test
  public void testObjectWithAllAttributesError0()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchObject(this.parse("(MatchObject (WithAllAttributesFrom X))"));
    });

    this.assertErrors(3);
  }

  @Test
  public void testObjectWithAllAttributesError1()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchObject(this.parse(
          "(MatchObject (WithAllAttributesFrom [Attribute x]))"));
    });

    this.assertErrors(3);
  }

  @Test
  public void testObjectWithAllAttributesError2()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchObject(this.parse(
          "(MatchObject (WithAllAttributesFrom [Attribute X Y]))"));
    });

    this.assertErrors(3);
  }

  @Test
  public void testObjectWithAllAttributesError3()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchObject(this.parse(
          "(MatchObject (WithAllAttributesFrom [Attribute \"A\" \"B\"]))"));
    });

    this.assertErrors(3);
  }

  @Test
  public void testObjectWithAnyAttributesError0()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchObject(this.parse("(MatchObject (WithAnyAttributesFrom X))"));
    });

    this.assertErrors(3);
  }

  @Test
  public void testObjectWithAnyAttributesError1()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchObject(this.parse(
          "(MatchObject (WithAnyAttributesFrom [Attribute x]))"));
    });

    this.assertErrors(3);
  }

  @Test
  public void testObjectWithAnyAttributesError2()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchObject(this.parse(
          "(MatchObject (WithAnyAttributesFrom [Attribute A B]))"));
    });

    this.assertErrors(3);
  }

  @Test
  public void testObjectWithAnyAttributesError3()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchObject(this.parse(
          "(MatchObject (WithAnyAttributesFrom [Attribute \"A\" \"B\"]))"));
    });

    this.assertErrors(3);
  }

  @Test
  public void testMatchObjectsAnd0()
    throws Exception
  {
    final var r =
      (MMatchObjectAnd) this.createParser()
        .parseMatchObject(this.parse(
          "(MatchObject (And (WithType x) (WithType a)))"));

    final var x =
      (MMatchObjectWithType) r.subExpressions().get(0);
    final var a =
      (MMatchObjectWithType) r.subExpressions().get(1);

    assertEquals(
      type("x"),
      x.type()
    );

    assertEquals(
      type("a"),
      a.type()
    );
  }

  @Test
  public void testMatchObjectsAndError0()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchObject(this.parse(
          "(MatchObject (And (WithType X) (WithType Y)))"));
    });

    this.assertErrors(7);
  }

  @Test
  public void testMatchObjectsOr0()
    throws Exception
  {
    final var r =
      (MMatchObjectOr) this.createParser()
        .parseMatchObject(this.parse(
          "(MatchObject (Or (WithType x) (WithType a)))"));

    final var x =
      (MMatchObjectWithType) r.subExpressions().get(0);
    final var a =
      (MMatchObjectWithType) r.subExpressions().get(1);

    assertEquals(
      type("x"),
      x.type()
    );

    assertEquals(
      type("a"),
      a.type()
    );
  }

  @Test
  public void testMatchObjectsOrError0()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchObject(this.parse(
          "(MatchObject (Or (WithType X) (WithType Y)))"));
    });

    this.assertErrors(7);
  }

  @Test
  public void testMatchActionError0()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchAction(this.parse("(what x y z)"));
    });

    this.assertErrors(1);
  }

  @Test
  public void testMatchActionError1()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchAction(this.parse("()"));
    });

    this.assertErrors(1);
  }

  @Test
  public void testMatchActionError2()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchAction(this.parse("x"));
    });

    this.assertErrors(1);
  }

  @Test
  public void testMatchActionError3()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchAction(this.parse("[what x y z]"));
    });

    this.assertErrors(1);
  }

  @Test
  public void testMatchActionError4()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchAction(this.parse("(MatchAction x)"));
    });

    this.assertErrors(1);
  }

  @Test
  public void testMatchActionError5()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchAction(this.parse("(MatchAction \"x\")"));
    });

    this.assertErrors(1);
  }

  @Test
  public void testMatchActionError6()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchAction(this.parse("(MatchAction [x])"));
    });

    this.assertErrors(1);
  }

  @Test
  public void testActionWithNameError0()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchAction(this.parse("(MatchAction (WithName X))"));
    });

    this.assertErrors(3);
  }

  @Test
  public void testActionWithNameError1()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchAction(this.parse("(MatchAction (WithName ()))"));
    });

    this.assertErrors(3);
  }

  @Test
  public void testActionWithName0()
    throws Exception
  {
    final var r =
      (MMatchActionWithName) this.createParser()
        .parseMatchAction(this.parse("(MatchAction (WithName x))"));

    assertEquals(
      action("x"),
      r.name()
    );
  }

  @Test
  public void testMatchActionsAnd0()
    throws Exception
  {
    final var r =
      (MMatchActionAnd) this.createParser()
        .parseMatchAction(this.parse(
          "(MatchAction (And (WithName x) (WithName a)))"));

    final var x =
      (MMatchActionWithName) r.subExpressions().get(0);
    final var a =
      (MMatchActionWithName) r.subExpressions().get(1);

    assertEquals(
      action("x"),
      x.name()
    );

    assertEquals(
      action("a"),
      a.name()
    );
  }

  @Test
  public void testMatchActionsAndError0()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchAction(this.parse(
          "(MatchAction (And (WithName X) (WithName Y)))"));
    });

    this.assertErrors(7);
  }

  @Test
  public void testMatchActionsOr0()
    throws Exception
  {
    final var r =
      (MMatchActionOr) this.createParser()
        .parseMatchAction(this.parse(
          "(MatchAction (Or (WithName x) (WithName a)))"));

    final var x =
      (MMatchActionWithName) r.subExpressions().get(0);
    final var a =
      (MMatchActionWithName) r.subExpressions().get(1);

    assertEquals(
      action("x"),
      x.name()
    );

    assertEquals(
      action("a"),
      a.name()
    );
  }

  @Test
  public void testMatchActionsOrError0()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchAction(this.parse(
          "(MatchAction (Or (WithName X) (WithName Y)))"));
    });

    this.assertErrors(7);
  }

  @Test
  public void testRule0()
    throws Exception
  {
    final var r =
      this.createParser()
        .parseRule(this.parse("""
                                (Rule
                                  [Name "rule0"]
                                  [Description "Rule 0"]
                                  [Conclusion Allow]
                                  [MatchSubject (WithAnyRolesFrom x)]
                                  [MatchObject (WithType t)]
                                  [MatchAction (WithName a)])
                                    """));

    assertEquals(
      ALLOW,
      r.conclusion()
    );
    assertEquals(
      role("x"),
      ((MMatchSubjectWithRolesAny) r.matchSubject()).requiredRoles().iterator().next()
    );
    assertEquals(
      type("t"),
      ((MMatchObjectWithType) r.matchObject()).type()
    );
    assertEquals(
      action("a"),
      ((MMatchActionWithName) r.matchAction()).name()
    );

    this.roundTrip(r);
  }

  @Test
  public void testRule1()
    throws Exception
  {
    final var r =
      this.createParser()
        .parseRule(this.parse("""
                                (Rule
                                  [Name rule1]
                                  [Description "Rule 1"]
                                  [Conclusion Deny]
                                  [MatchSubject (WithAnyRolesFrom x)]
                                  [MatchObject (WithType t)]
                                  [MatchAction (WithName a)])
                                    """));

    assertEquals(
      DENY,
      r.conclusion()
    );
    assertEquals(
      role("x"),
      ((MMatchSubjectWithRolesAny) r.matchSubject()).requiredRoles().iterator().next()
    );
    assertEquals(
      type("t"),
      ((MMatchObjectWithType) r.matchObject()).type()
    );
    assertEquals(
      action("a"),
      ((MMatchActionWithName) r.matchAction()).name()
    );

    this.roundTrip(r);
  }

  @Test
  public void testRule2()
    throws Exception
  {
    final var r =
      this.createParser()
        .parseRule(this.parse("""
                                (Rule
                                  [Name rule1]
                                  [Description "Rule 1"]
                                  [Conclusion AllowImmediately]
                                  [MatchSubject (WithAnyRolesFrom x)]
                                  [MatchObject (WithType t)]
                                  [MatchAction (WithName a)])
                                    """));

    assertEquals(
      ALLOW_IMMEDIATELY,
      r.conclusion()
    );
    assertEquals(
      role("x"),
      ((MMatchSubjectWithRolesAny) r.matchSubject()).requiredRoles().iterator().next()
    );
    assertEquals(
      type("t"),
      ((MMatchObjectWithType) r.matchObject()).type()
    );
    assertEquals(
      action("a"),
      ((MMatchActionWithName) r.matchAction()).name()
    );

    this.roundTrip(r);
  }

  @Test
  public void testRule3()
    throws Exception
  {
    final var r =
      this.createParser()
        .parseRule(this.parse("""
                                (Rule
                                  [Name rule1]
                                  [Description "Rule 1"]
                                  [Conclusion DenyImmediately]
                                  [MatchSubject (WithAnyRolesFrom x)]
                                  [MatchObject (WithType t)]
                                  [MatchAction (WithName a)])
                                    """));

    assertEquals(
      DENY_IMMEDIATELY,
      r.conclusion()
    );
    assertEquals(
      role("x"),
      ((MMatchSubjectWithRolesAny) r.matchSubject()).requiredRoles().iterator().next()
    );
    assertEquals(
      type("t"),
      ((MMatchObjectWithType) r.matchObject()).type()
    );
    assertEquals(
      action("a"),
      ((MMatchActionWithName) r.matchAction()).name()
    );

    this.roundTrip(r);
  }

  private void roundTrip(final MRule r)
    throws Exception
  {
    final var policy =
      new MPolicy(List.of(r));

    final var serializer =
      new MExpressionSerializer();
    final var expressions =
      serializer.serialize(policy);
    final var writer =
      new StringWriter();
    final var xSerializer =
      JSXPrettyPrinterCodeStyle.newPrinterWithWidthIndent(
        writer, 80, 2);

    for (final var expression : expressions) {
      xSerializer.print(expression);
      writer.append("\n");
    }
    writer.flush();

    LOG.debug("{}", writer);

    final var parserConfig =
      new JSXParserConfiguration(true);
    final var lexerConfig =
      new JSXLexerConfiguration(
        true,
        true,
        Optional.empty(),
        EnumSet.noneOf(JSXLexerComment.class),
        1
      );
    final var reader =
      UnicodeCharacterReader.newReader(new StringReader(writer.toString()));
    final var lexer =
      JSXLexer.newLexer(lexerConfig, reader);
    final var xParser =
      JSXParser.newParser(parserConfig, lexer);

    final var outPolicy =
      this.createParser()
        .parsePolicy(xParser.parseExpressions());

    for (var index = 0; index < policy.rules().size(); ++index) {
      final var rule =
        policy.rules().get(index);
      final var outRule =
        outPolicy.rules().get(index);

      assertEquals(rule, outRule);
    }

    assertEquals(policy, outPolicy);
  }

  @Test
  public void testRuleError0()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseRule(this.parse("(deny)"));
    });

    this.assertErrors(1);
  }

  private void assertErrors(
    final int expected)
  {
    for (final var error : this.errors) {
      LOG.error("{}", error);
    }
    assertEquals(expected, this.errors.size());
  }

  @Test
  public void testRuleError1()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseRule(this.parse("(a x y z)"));
    });

    this.assertErrors(1);
  }

  @Test
  public void testRuleError2()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseRule(this.parse("""
[Rule
  [Name a]
  [Name b]
  [Description ""]
  [Description ""]
  [Conclusion Allow]
  [Conclusion Allow]
  [MatchSubject True]
  [MatchSubject True]
  [MatchObject  True]
  [MatchObject  True]
  [MatchAction  True]
  [MatchAction  True]
]
                                """));
    });

    this.assertErrors(6);
  }

  @Test
  public void testRuleError3()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseRule(this.parse("""
[Rule

]
                                """));
    });

    this.assertErrors(4);
  }

  @Test
  public void testRuleError4()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseRule(this.parse("""
[Rule
  [Name ["x"]]
  [Description ["y"]]
  [Conclusion ["z"]]
  [Conclusion Malformed]
]
                                """));
    });

    this.assertErrors(8);
  }

  @Property
  public void testRoundTripArbitrary(
    @ForAll final MRuleName name,
    @ForAll final String description,
    @ForAll final MRuleConclusion conclusion,
    @ForAll("actionArbitrary") final MMatchActionType action,
    @ForAll("objectArbitrary") final MMatchObjectType object,
    @ForAll("subjectArbitrary") final MMatchSubjectType subject)
    throws Exception
  {
    this.roundTrip(
      new MRule(name, description, conclusion, subject, object, action)
    );
  }

  @Provide
  public Arbitrary<MMatchActionType> actionArbitrary()
  {
    return MMatchActions.arbitrary();
  }

  @Provide
  public Arbitrary<MMatchObjectType> objectArbitrary()
  {
    return MMatchObjects.arbitrary();
  }

  @Provide
  public Arbitrary<MMatchSubjectType> subjectArbitrary()
  {
    return MMatchSubjects.arbitrary();
  }

  private MExpressionParser createParser()
    throws IOException
  {
    return new MExpressionParser(
      new MStrings(Locale.getDefault()), this::onError);
  }

  private void onError(
    final ParseStatus parseStatus)
  {
    LOG.error(
      "{}:{}: {}",
      Integer.valueOf(parseStatus.lexical().line()),
      Integer.valueOf(parseStatus.lexical().column()),
      parseStatus.message()
    );

    this.errors.add(parseStatus);
  }
}
