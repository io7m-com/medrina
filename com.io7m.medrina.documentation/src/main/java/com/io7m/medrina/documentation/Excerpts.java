package com.io7m.medrina.documentation;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import static java.nio.charset.StandardCharsets.UTF_8;

public final class Excerpts
{
  private Excerpts()
  {

  }

  private record Excerpt(
    long id,
    String match,
    boolean isProof)
  {

  }

  private record FileLine (String file, String line) {

  }

  public static void main(
    final String[] args)
    throws IOException
  {
    if (args.length != 3) {
      System.err.println("usage: src-directory excerpts.txt out-directory");
      throw new IllegalArgumentException();
    }

    final var srcDirectory =
      Paths.get(args[0])
        .toAbsolutePath();

    final var excerptsFile =
      Paths.get(args[1])
        .toAbsolutePath();

    final var outDirectory =
      Paths.get(args[2])
        .toAbsolutePath();

    final var excerpts = new ArrayList<Excerpt>();
    for (final var line : Files.readAllLines(excerptsFile, UTF_8)) {
      final var trimmed = line.trim();
      if (!trimmed.isEmpty()) {
        final var segments = List.of(trimmed.split("!"));
        final var matchText = segments.get(1).trim();
        final var exNumber = Long.parseUnsignedLong(segments.get(0).trim());
        excerpts.add(
          new Excerpt(
            exNumber,
            matchText,
            matchText.startsWith("Theorem") || matchText.startsWith("Lemma")
          )
        );
      }
    }

    final List<Path> sources;
    try (var stream = Files.walk(srcDirectory)) {
      sources = stream.filter(p -> p.getFileName().toString().endsWith(".v"))
        .collect(Collectors.toList());
    }
    final var lines = new ArrayList<FileLine>(1024);
    for (final var path : sources) {
      lines.addAll(
        Files.readAllLines(path, UTF_8)
          .stream()
          .map(line -> new FileLine(path.getFileName().toString(), line))
          .collect(Collectors.toList())
      );
    }

    Files.createDirectories(outDirectory);
    for (final var excerpt : excerpts) {
      final var output = new ArrayList<String>(32);

      final boolean matched;
      if (excerpt.isProof) {
        matched = matchProof(excerpt, lines, output);
      } else {
        matched = matchDefinition(excerpt, lines, output);
      }

      if (!matched) {
        throw new IllegalStateException(
          String.format(
            "Excerpt %s (%s) did not match anything",
            Long.valueOf(excerpt.id),
            excerpt.match)
        );
      }

      final var outputPath = outDirectory.resolve(excerpt.id + ".txt");
      try (var writer = Files.newBufferedWriter(outputPath, UTF_8)) {
        for (final var line : output) {
          writer.append(line);
          writer.newLine();
        }
      }
    }
  }

  private static boolean matchDefinition(
    final Excerpt excerpt,
    final ArrayList<FileLine> lines,
    final ArrayList<String> output)
  {
    var matching = false;
    for (final var line : lines) {
      final var lineText = line.line;

      if (matching) {
        if (lineText.trim().isEmpty()) {
          return true;
        }
        output.add(lineText);
        continue;
      }

      if (lineText.trim().startsWith(excerpt.match)) {
        matching = true;
        output.add(lineText);
      }
    }
    return false;
  }

  private static boolean matchProof(
    final Excerpt excerpt,
    final ArrayList<FileLine> lines,
    final ArrayList<String> output)
  {
    var matching = false;
    var omitting = false;

    for (final var line : lines) {
      final var lineText = line.line;

      if (matching) {
        final var trimmed = lineText.trim();
        if ("Proof.".equals(trimmed)) {
          output.add(lineText);
          output.add(String.format("  (* Proof omitted for brevity; see %s for proofs. *)", line.file));
          omitting = true;
          continue;
        }
        if ("Qed.".equals(trimmed)) {
          output.add(lineText);
          return true;
        }

        if (!omitting) {
          output.add(lineText);
        }
        continue;
      }

      if (lineText.trim().startsWith(excerpt.match)) {
        matching = true;
        output.add(lineText);
      }
    }
    return false;
  }
}

