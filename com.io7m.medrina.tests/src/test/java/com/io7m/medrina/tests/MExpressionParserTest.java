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

import com.io7m.anethum.common.ParseStatus;
import com.io7m.jeucreader.UnicodeCharacterReader;
import com.io7m.jsx.SExpressionType;
import com.io7m.jsx.api.lexer.JSXLexerComment;
import com.io7m.jsx.api.lexer.JSXLexerConfiguration;
import com.io7m.jsx.api.parser.JSXParserConfiguration;
import com.io7m.jsx.lexer.JSXLexer;
import com.io7m.jsx.parser.JSXParser;
import com.io7m.jsx.prettyprint.JSXPrettyPrinterCodeStyle;
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

  @BeforeEach
  @BeforeProperty
  public void setup()
  {
    this.errors = new ArrayList<ParseStatus>();
  }

  private SExpressionType parse(
    final String text)
    throws Exception
  {
    final var lexerConfig =
      new JSXLexerConfiguration(
        true,
        false,
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

    assertEquals(1, this.errors.size());
  }

  @Test
  public void testMatchRoleError1()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchSubject(this.parse("()"));
    });

    assertEquals(1, this.errors.size());
  }

  @Test
  public void testMatchRoleError2()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchSubject(this.parse("x"));
    });

    assertEquals(1, this.errors.size());
  }

  @Test
  public void testMatchRoleError3()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchSubject(this.parse("[what x y z]"));
    });

    assertEquals(1, this.errors.size());
  }

  @Test
  public void testSubjectWithAllRolesError0()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchSubject(this.parse("(subject (with-all-roles X Y Z))"));
    });

    assertEquals(4, this.errors.size());
  }

  @Test
  public void testSubjectWithAllRolesError1()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchSubject(this.parse("(subject (with-all-roles () \"x\"))"));
    });

    assertEquals(3, this.errors.size());
  }

  @Test
  public void testSubjectWithAllRoles0()
    throws Exception
  {
    final var r =
      (MMatchSubjectWithRolesAll) this.createParser()
        .parseMatchSubject(this.parse("(subject (with-all-roles x y z))"));

    assertEquals(
      Set.of(
        new MRoleName("x"),
        new MRoleName("y"),
        new MRoleName("z")),
      r.requiredRoles()
    );
  }

  @Test
  public void testSubjectWithAllRoles1()
    throws Exception
  {
    final var r =
      (MMatchSubjectWithRolesAll) this.createParser()
        .parseMatchSubject(this.parse("(subject (with-all-roles))"));

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
        .parseMatchSubject(this.parse("(subject (with-any-roles X Y Z))"));
    });

    assertEquals(4, this.errors.size());
  }

  @Test
  public void testSubjectWithAnyRolesError1()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchSubject(this.parse("(subject (with-any-roles () \"x\"))"));
    });

    assertEquals(3, this.errors.size());
  }

  @Test
  public void testSubjectWithAnyRoles0()
    throws Exception
  {
    final var r =
      (MMatchSubjectWithRolesAny) this.createParser()
        .parseMatchSubject(this.parse("(subject (with-any-roles x y z))"));

    assertEquals(
      Set.of(
        new MRoleName("x"),
        new MRoleName("y"),
        new MRoleName("z")),
      r.requiredRoles()
    );
  }

  @Test
  public void testSubjectWithAnyRoles1()
    throws Exception
  {
    final var r =
      (MMatchSubjectWithRolesAny) this.createParser()
        .parseMatchSubject(this.parse("(subject (with-any-roles))"));

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
          "(subject (and (with-any-roles x y z) (with-all-roles a b c)))"));

    final var any =
      (MMatchSubjectWithRolesAny) r.subExpressions().get(0);
    final var all =
      (MMatchSubjectWithRolesAll) r.subExpressions().get(1);

    assertEquals(
      Set.of(
        new MRoleName("x"),
        new MRoleName("y"),
        new MRoleName("z")),
      any.requiredRoles()
    );

    assertEquals(
      Set.of(
        new MRoleName("a"),
        new MRoleName("b"),
        new MRoleName("c")),
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
          "(subject (and (with-all-roles X) (with-any-roles Y)))"));
    });

    assertEquals(5, this.errors.size());
  }

  @Test
  public void testMatchRolesOr0()
    throws Exception
  {
    final var r =
      (MMatchSubjectOr) this.createParser()
        .parseMatchSubject(this.parse(
          "(subject (or (with-any-roles x y z) (with-all-roles a b c)))"));

    final var any =
      (MMatchSubjectWithRolesAny) r.subExpressions().get(0);
    final var all =
      (MMatchSubjectWithRolesAll) r.subExpressions().get(1);

    assertEquals(
      Set.of(
        new MRoleName("x"),
        new MRoleName("y"),
        new MRoleName("z")),
      any.requiredRoles()
    );

    assertEquals(
      Set.of(
        new MRoleName("a"),
        new MRoleName("b"),
        new MRoleName("c")),
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
          "(subject (or (with-all-roles X) (with-any-roles Y)))"));
    });

    assertEquals(5, this.errors.size());
  }

  @Test
  public void testMatchObjectError0()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchObject(this.parse("(what x y z)"));
    });

    assertEquals(1, this.errors.size());
  }

  @Test
  public void testMatchObjectError1()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchObject(this.parse("()"));
    });

    assertEquals(1, this.errors.size());
  }

  @Test
  public void testMatchObjectError2()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchObject(this.parse("x"));
    });

    assertEquals(1, this.errors.size());
  }

  @Test
  public void testMatchObjectError3()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchObject(this.parse("[what x y z]"));
    });

    assertEquals(1, this.errors.size());
  }

  @Test
  public void testObjectWithTypeError0()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchObject(this.parse("(object (with-type X))"));
    });

    assertEquals(3, this.errors.size());
  }

  @Test
  public void testObjectWithTypeError1()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchObject(this.parse("(object (with-type ()))"));
    });

    assertEquals(3, this.errors.size());
  }

  @Test
  public void testObjectWithType0()
    throws Exception
  {
    final var r =
      (MMatchObjectWithType) this.createParser()
        .parseMatchObject(this.parse("(object (with-type x))"));

    assertEquals(
      new MTypeName("x"),
      r.type()
    );
  }

  @Test
  public void testMatchObjectsAnd0()
    throws Exception
  {
    final var r =
      (MMatchObjectAnd) this.createParser()
        .parseMatchObject(this.parse(
          "(object (and (with-type x) (with-type a)))"));

    final var x =
      (MMatchObjectWithType) r.subExpressions().get(0);
    final var a =
      (MMatchObjectWithType) r.subExpressions().get(1);

    assertEquals(
      new MTypeName("x"),
      x.type()
    );

    assertEquals(
      new MTypeName("a"),
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
          "(object (and (with-type X) (with-type Y)))"));
    });

    assertEquals(7, this.errors.size());
  }

  @Test
  public void testMatchObjectsOr0()
    throws Exception
  {
    final var r =
      (MMatchObjectOr) this.createParser()
        .parseMatchObject(this.parse(
          "(object (or (with-type x) (with-type a)))"));

    final var x =
      (MMatchObjectWithType) r.subExpressions().get(0);
    final var a =
      (MMatchObjectWithType) r.subExpressions().get(1);

    assertEquals(
      new MTypeName("x"),
      x.type()
    );

    assertEquals(
      new MTypeName("a"),
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
          "(object (or (with-type X) (with-type Y)))"));
    });

    assertEquals(7, this.errors.size());
  }

  @Test
  public void testMatchActionError0()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchAction(this.parse("(what x y z)"));
    });

    assertEquals(1, this.errors.size());
  }

  @Test
  public void testMatchActionError1()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchAction(this.parse("()"));
    });

    assertEquals(1, this.errors.size());
  }

  @Test
  public void testMatchActionError2()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchAction(this.parse("x"));
    });

    assertEquals(1, this.errors.size());
  }

  @Test
  public void testMatchActionError3()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchAction(this.parse("[what x y z]"));
    });

    assertEquals(1, this.errors.size());
  }

  @Test
  public void testActionWithNameError0()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchAction(this.parse("(action (with-name X))"));
    });

    assertEquals(3, this.errors.size());
  }

  @Test
  public void testActionWithNameError1()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseMatchAction(this.parse("(action (with-name ()))"));
    });

    assertEquals(3, this.errors.size());
  }

  @Test
  public void testActionWithName0()
    throws Exception
  {
    final var r =
      (MMatchActionWithName) this.createParser()
        .parseMatchAction(this.parse("(action (with-name x))"));

    assertEquals(
      new MActionName("x"),
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
          "(action (and (with-name x) (with-name a)))"));

    final var x =
      (MMatchActionWithName) r.subExpressions().get(0);
    final var a =
      (MMatchActionWithName) r.subExpressions().get(1);

    assertEquals(
      new MActionName("x"),
      x.name()
    );

    assertEquals(
      new MActionName("a"),
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
          "(action (and (with-name X) (with-name Y)))"));
    });

    assertEquals(7, this.errors.size());
  }

  @Test
  public void testMatchActionsOr0()
    throws Exception
  {
    final var r =
      (MMatchActionOr) this.createParser()
        .parseMatchAction(this.parse(
          "(action (or (with-name x) (with-name a)))"));

    final var x =
      (MMatchActionWithName) r.subExpressions().get(0);
    final var a =
      (MMatchActionWithName) r.subExpressions().get(1);

    assertEquals(
      new MActionName("x"),
      x.name()
    );

    assertEquals(
      new MActionName("a"),
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
          "(action (or (with-name X) (with-name Y)))"));
    });

    assertEquals(7, this.errors.size());
  }

  @Test
  public void testRule0()
    throws Exception
  {
    final var r =
      this.createParser()
        .parseRule(this.parse("""
                                (allow [subject (with-any-roles x)]
                                       [object (with-type t)]
                                       [action (with-name a)])
                                    """));

    assertEquals(
      ALLOW,
      r.conclusion()
    );
    assertEquals(
      new MRoleName("x"),
      ((MMatchSubjectWithRolesAny) r.matchSubject()).requiredRoles().iterator().next()
    );
    assertEquals(
      new MTypeName("t"),
      ((MMatchObjectWithType) r.matchObject()).type()
    );
    assertEquals(
      new MActionName("a"),
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
                                (deny [subject (with-any-roles x)]
                                      [object (with-type t)]
                                      [action (with-name a)])
                                    """));

    assertEquals(
      DENY,
      r.conclusion()
    );
    assertEquals(
      new MRoleName("x"),
      ((MMatchSubjectWithRolesAny) r.matchSubject()).requiredRoles().iterator().next()
    );
    assertEquals(
      new MTypeName("t"),
      ((MMatchObjectWithType) r.matchObject()).type()
    );
    assertEquals(
      new MActionName("a"),
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
                                (allow-immediately [subject (with-any-roles x)]
                                                   [object (with-type t)]
                                                   [action (with-name a)])
                                    """));

    assertEquals(
      ALLOW_IMMEDIATELY,
      r.conclusion()
    );
    assertEquals(
      new MRoleName("x"),
      ((MMatchSubjectWithRolesAny) r.matchSubject()).requiredRoles().iterator().next()
    );
    assertEquals(
      new MTypeName("t"),
      ((MMatchObjectWithType) r.matchObject()).type()
    );
    assertEquals(
      new MActionName("a"),
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
                                (deny-immediately [subject (with-any-roles x)]
                                                  [object (with-type t)]
                                                  [action (with-name a)])
                                    """));

    assertEquals(
      DENY_IMMEDIATELY,
      r.conclusion()
    );
    assertEquals(
      new MRoleName("x"),
      ((MMatchSubjectWithRolesAny) r.matchSubject()).requiredRoles().iterator().next()
    );
    assertEquals(
      new MTypeName("t"),
      ((MMatchObjectWithType) r.matchObject()).type()
    );
    assertEquals(
      new MActionName("a"),
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

    assertEquals(1, this.errors.size());
  }

  @Test
  public void testRuleError1()
    throws Exception
  {
    assertThrows(Exception.class, () -> {
      this.createParser()
        .parseRule(this.parse("(a x y z)"));
    });

    assertEquals(4, this.errors.size());
  }

  @Property
  public void testRoundTripArbitrary(
    @ForAll final MRuleConclusion conclusion,
    @ForAll("actionArbitrary") final MMatchActionType action,
    @ForAll("objectArbitrary") final MMatchObjectType object,
    @ForAll("subjectArbitrary") final MMatchSubjectType subject)
    throws Exception
  {
    this.roundTrip(new MRule(conclusion, subject, object, action));
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
