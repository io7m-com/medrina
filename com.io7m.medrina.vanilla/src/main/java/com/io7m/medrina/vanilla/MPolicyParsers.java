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

package com.io7m.medrina.vanilla;

import com.io7m.anethum.common.ParseException;
import com.io7m.anethum.common.ParseSeverity;
import com.io7m.anethum.common.ParseStatus;
import com.io7m.jeucreader.UnicodeCharacterReader;
import com.io7m.jlexing.core.LexicalPositions;
import com.io7m.jsx.SExpressionType;
import com.io7m.jsx.api.lexer.JSXLexerComment;
import com.io7m.jsx.api.lexer.JSXLexerConfiguration;
import com.io7m.jsx.api.parser.JSXParserConfiguration;
import com.io7m.jsx.api.parser.JSXParserException;
import com.io7m.jsx.api.parser.JSXParserType;
import com.io7m.jsx.lexer.JSXLexer;
import com.io7m.jsx.parser.JSXParser;
import com.io7m.medrina.api.MPolicy;
import com.io7m.medrina.api.MRule;
import com.io7m.medrina.parser.api.MPolicyParserFactoryType;
import com.io7m.medrina.parser.api.MPolicyParserType;
import com.io7m.medrina.vanilla.internal.MExpressionParser;
import com.io7m.medrina.vanilla.internal.MStrings;

import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.UncheckedIOException;
import java.net.URI;
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.List;
import java.util.Locale;
import java.util.Objects;
import java.util.Optional;
import java.util.function.Consumer;

import static java.nio.charset.StandardCharsets.UTF_8;

/**
 * The default provider of policy parsers.
 */

public final class MPolicyParsers implements MPolicyParserFactoryType
{
  private final MStrings strings;

  /**
   * The default provider of policy parsers.
   */

  public MPolicyParsers()
  {
    try {
      this.strings = new MStrings(Locale.getDefault());
    } catch (final IOException e) {
      throw new UncheckedIOException(e);
    }
  }

  @Override
  public MPolicyParserType createParserWithContext(
    final Void context,
    final URI source,
    final InputStream stream,
    final Consumer<ParseStatus> statusConsumer)
  {
    final var lexerConfig =
      new JSXLexerConfiguration(
        true,
        false,
        Optional.of(source),
        EnumSet.of(JSXLexerComment.COMMENT_HASH),
        1
      );

    final var reader =
      new UnicodeCharacterReader(new InputStreamReader(stream, UTF_8));
    final var lexer =
      JSXLexer.newLexer(lexerConfig, reader);
    final JSXParserConfiguration parserConfig =
      new JSXParserConfiguration(true);
    final var parser =
      JSXParser.newParser(parserConfig, lexer);

    return new MPolicyParser(this.strings, parser, stream, statusConsumer);
  }

  private static final class MPolicyParser implements MPolicyParserType
  {
    private final MStrings strings;
    private final JSXParserType parser;
    private final InputStream stream;
    private final Consumer<ParseStatus> statusConsumer;
    private final ArrayList<ParseStatus> errors;
    private int errorCount;
    private boolean failed;

    MPolicyParser(
      final MStrings inStrings,
      final JSXParserType inParser,
      final InputStream inStream,
      final Consumer<ParseStatus> inStatusConsumer)
    {
      this.strings =
        Objects.requireNonNull(inStrings, "inStrings");
      this.parser =
        Objects.requireNonNull(inParser, "parser");
      this.stream =
        Objects.requireNonNull(inStream, "stream");
      this.statusConsumer =
        Objects.requireNonNull(inStatusConsumer, "inStatusConsumer");
      this.errors =
        new ArrayList<>();
      this.errorCount = 0;
    }

    @Override
    public MPolicy execute()
      throws ParseException
    {
      final var expressionParser =
        new MExpressionParser(
          this.strings,
          this.statusConsumer
        );

      final var rules = new ArrayList<MRule>();
      while (this.errorCount < 20) {
        try {
          final Optional<SExpressionType> expressionOpt =
            this.parser.parseExpressionOrEOF();
          if (expressionOpt.isEmpty()) {
            break;
          }

          rules.add(expressionParser.parseRule(expressionOpt.get()));
        } catch (final JSXParserException e) {
          this.publishError(parserExceptionToStatus(e));
        } catch (final IOException e) {
          this.publishError(ioExceptionToStatus(e));
        } catch (final MExpressionParser.ExpressionParseException e) {
          this.failed = true;
          this.errorCount += 1;
        }
      }

      if (!this.failed) {
        return new MPolicy(List.copyOf(rules));
      }

      throw new ParseException("Parse failed.", List.copyOf(this.errors));
    }

    private void publishError(
      final ParseStatus status)
    {
      this.errors.add(status);
      this.failed = true;
      this.errorCount += 1;
      this.statusConsumer.accept(status);
    }

    private static ParseStatus parserExceptionToStatus(
      final JSXParserException e)
    {
      return ParseStatus.builder()
        .setSeverity(ParseSeverity.PARSE_ERROR)
        .setMessage(e.getMessage())
        .setLexical(e.lexical())
        .setErrorCode("malformed-s-expression")
        .build();
    }

    private static ParseStatus ioExceptionToStatus(
      final IOException e)
    {
      return ParseStatus.builder()
        .setSeverity(ParseSeverity.PARSE_ERROR)
        .setMessage(e.getMessage())
        .setLexical(LexicalPositions.zero())
        .setErrorCode("io-error")
        .build();
    }

    @Override
    public void close()
      throws IOException
    {
      this.stream.close();
    }
  }
}
