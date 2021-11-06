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

import com.io7m.medrina.api.MActionName;
import com.io7m.medrina.api.MObject;
import com.io7m.medrina.api.MPolicy;
import com.io7m.medrina.api.MPolicyEvaluator;
import com.io7m.medrina.api.MPolicyEvaluatorType;
import com.io7m.medrina.api.MRule;
import com.io7m.medrina.api.MRuleConclusion;
import com.io7m.medrina.api.MSubject;
import net.jqwik.api.ForAll;
import net.jqwik.api.Property;
import net.jqwik.api.lifecycle.BeforeProperty;
import org.junit.jupiter.api.BeforeEach;

import java.util.List;

import static com.io7m.medrina.api.MMatchActionType.MMatchActionFalse;
import static com.io7m.medrina.api.MMatchActionType.MMatchActionTrue;
import static com.io7m.medrina.api.MMatchObjectType.MMatchObjectFalse;
import static com.io7m.medrina.api.MMatchObjectType.MMatchObjectTrue;
import static com.io7m.medrina.api.MMatchSubjectType.MMatchSubjectFalse;
import static com.io7m.medrina.api.MMatchSubjectType.MMatchSubjectTrue;
import static com.io7m.medrina.api.MPolicyAccess.ACCESS_ALLOWED;
import static com.io7m.medrina.api.MPolicyAccess.ACCESS_DENIED;
import static org.junit.jupiter.api.Assertions.assertEquals;

public final class MPolicyEvaluatorTest
{
  private MPolicyEvaluatorType evaluator;

  @BeforeProperty
  @BeforeEach
  public void setup()
  {
    this.evaluator = MPolicyEvaluator.create();
  }

  /**
   * An empty policy denies everything.
   *
   * @param object     The object
   * @param subject    The subject
   * @param actionName The action
   */

  @Property
  public void testEmpty(
    @ForAll final MObject object,
    @ForAll final MSubject subject,
    @ForAll final MActionName actionName)
  {
    assertEquals(
      ACCESS_DENIED,
      this.evaluator.evaluate(
        new MPolicy(List.of()),
        subject,
        object,
        actionName
      ).accessResult()
    );
  }

  /**
   * A policy that ends in a catch-all allow rule, allows everything.
   *
   * @param object     The object
   * @param subject    The subject
   * @param actionName The action
   */

  @Property
  public void testAllowAll(
    @ForAll final MObject object,
    @ForAll final MSubject subject,
    @ForAll final MActionName actionName)
  {
    assertEquals(
      ACCESS_ALLOWED,
      this.evaluator.evaluate(
        new MPolicy(List.of(
          new MRule(
            MRuleConclusion.ALLOW,
            new MMatchSubjectTrue(),
            new MMatchObjectTrue(),
            new MMatchActionTrue()
          )
        )),
        subject,
        object,
        actionName
      ).accessResult()
    );
  }

  /**
   * An allow-immediately rule that matches dominates a deny rule that
   * matches.
   *
   * @param object     The object
   * @param subject    The subject
   * @param actionName The action
   */

  @Property
  public void testAllowImmediately(
    @ForAll final MObject object,
    @ForAll final MSubject subject,
    @ForAll final MActionName actionName)
  {
    assertEquals(
      ACCESS_ALLOWED,
      this.evaluator.evaluate(
        new MPolicy(List.of(
          new MRule(
            MRuleConclusion.ALLOW_IMMEDIATELY,
            new MMatchSubjectTrue(),
            new MMatchObjectTrue(),
            new MMatchActionTrue()
          ),
          new MRule(
            MRuleConclusion.DENY,
            new MMatchSubjectTrue(),
            new MMatchObjectTrue(),
            new MMatchActionTrue()
          )
        )),
        subject,
        object,
        actionName
      ).accessResult()
    );
  }

  /**
   * A deny-immediately rule that matches dominates an allow rule that
   * matches.
   *
   * @param object     The object
   * @param subject    The subject
   * @param actionName The action
   */

  @Property
  public void testDenyImmediately(
    @ForAll final MObject object,
    @ForAll final MSubject subject,
    @ForAll final MActionName actionName)
  {
    assertEquals(
      ACCESS_DENIED,
      this.evaluator.evaluate(
        new MPolicy(List.of(
          new MRule(
            MRuleConclusion.DENY_IMMEDIATELY,
            new MMatchSubjectTrue(),
            new MMatchObjectTrue(),
            new MMatchActionTrue()
          ),
          new MRule(
            MRuleConclusion.ALLOW,
            new MMatchSubjectTrue(),
            new MMatchObjectTrue(),
            new MMatchActionTrue()
          )
        )),
        subject,
        object,
        actionName
      ).accessResult()
    );
  }

  /**
   * A deny rule that matches dominates an allow rule that
   * doesn't match.
   *
   * @param object     The object
   * @param subject    The subject
   * @param actionName The action
   */

  @Property
  public void testDeny(
    @ForAll final MObject object,
    @ForAll final MSubject subject,
    @ForAll final MActionName actionName)
  {
    assertEquals(
      ACCESS_DENIED,
      this.evaluator.evaluate(
        new MPolicy(List.of(
          new MRule(
            MRuleConclusion.DENY,
            new MMatchSubjectTrue(),
            new MMatchObjectTrue(),
            new MMatchActionTrue()
          ),
          new MRule(
            MRuleConclusion.ALLOW,
            new MMatchSubjectFalse(),
            new MMatchObjectFalse(),
            new MMatchActionFalse()
          )
        )),
        subject,
        object,
        actionName
      ).accessResult()
    );
  }
}
