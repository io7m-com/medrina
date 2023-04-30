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

package com.io7m.medrina.tests;

import com.io7m.medrina.cmdline.MainExitless;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertThrows;

public final class MCommandLineTest
{
  private Path directory;

  @BeforeEach
  public void setup()
    throws IOException
  {
    this.directory = MTestDirectories.createTempDirectory();
  }

  @AfterEach
  public void tearDown()
    throws IOException
  {
    MTestDirectories.deleteDirectory(this.directory);
  }

  @Test
  public void testHelp()
    throws IOException
  {
    MainExitless.main(new String[]{
      "help"
    });
  }

  @Test
  public void testHelpCommands()
    throws IOException
  {
    for (final var command : List.of("help", "version", "parse", "evaluate")) {
      MainExitless.main(new String[]{"help", command});
    }
  }

  @Test
  public void testParse()
    throws IOException
  {
    final var path =
      MTestDirectories.resourceOf(
        MCommandLineTest.class,
        this.directory,
        "example0.mp"
      );

    MainExitless.main(
      new String[]{
        "parse",
        "--file",
        path.toAbsolutePath().toString()
      }
    );
  }

  @Test
  public void testParseUnparseable()
    throws IOException
  {
    final var path =
      this.directory.resolve("x.txt");

    Files.writeString(path, "Hello!");

    assertThrows(IOException.class, () -> {
      MainExitless.main(
        new String[]{
          "parse",
          "--file",
          path.toAbsolutePath().toString()
        }
      );
    });
  }

  @Test
  public void testParseNonexistent()
    throws IOException
  {
    final var path =
      this.directory.resolve("x.txt");

    assertThrows(IOException.class, () -> {
      MainExitless.main(
        new String[]{
          "parse",
          "--file",
          path.toAbsolutePath().toString()
        }
      );
    });
  }

  @Test
  public void testEvaluate()
    throws IOException
  {
    final var path =
      MTestDirectories.resourceOf(
        MCommandLineTest.class,
        this.directory,
        "example0.mp"
      );

    MainExitless.main(
      new String[]{
        "evaluate",
        "--file",
        path.toAbsolutePath().toString(),
        "--object-type",
        "t",
        "--action",
        "read",
        "--subject-role",
        "r"
      }
    );
  }

  @Test
  public void testEvaluateUnparseable()
    throws IOException
  {
    final var path =
      this.directory.resolve("x.txt");

    Files.writeString(path, "Hello!");

    assertThrows(IOException.class, () -> {
      MainExitless.main(
        new String[]{
          "evaluate",
          "--file",
          path.toAbsolutePath().toString(),
          "--object-type",
          "t",
          "--action",
          "read",
          "--subject-role",
          "r"
        }
      );
    });
  }

  @Test
  public void testVersion()
    throws IOException
  {
    MainExitless.main(new String[]{
      "version"
    });
  }
}
