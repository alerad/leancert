#!/usr/bin/env python3
"""Compile every Markdown fence labelled `lean` or `lean expect-error`.

Imports are hoisted ahead of the private namespace used for each block. A
regular `lean` fence must compile; `lean expect-error` must be rejected by
Lean. Use `text` only for output, mathematical shapes, and pseudocode.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import dataclasses
import re
import subprocess
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DOCS = ROOT / "docs"
FENCE = re.compile(
    r"^```lean(?P<mode>[ \t]+expect-error)?[ \t]*\n(?P<body>.*?)^```\s*$",
    re.MULTILINE | re.DOTALL,
)
ERROR_LINE = re.compile(
    r"^[^:\n]+:(\d+):\d+: (?:error|error\([^)]*\)):", re.MULTILINE
)


@dataclasses.dataclass(frozen=True)
class Snippet:
    source: Path
    line: int
    ordinal: int
    body: str
    expect_error: bool = False

    @property
    def label(self) -> str:
        return f"{self.source.relative_to(ROOT)}:{self.line} (block {self.ordinal})"


@dataclasses.dataclass
class Batch:
    ordinal: int
    snippets: list[Snippet]


def collect() -> list[Snippet]:
    snippets: list[Snippet] = []
    for source in sorted(DOCS.rglob("*.md")):
        text = source.read_text()
        for ordinal, match in enumerate(FENCE.finditer(text), 1):
            snippets.append(
                Snippet(
                    source=source,
                    line=text[: match.start()].count("\n") + 1,
                    ordinal=ordinal,
                    body=match.group("body"),
                    expect_error=bool(match.group("mode")),
                )
            )
    return snippets


def without_imports(body: str) -> str:
    return "\n".join(
        line for line in body.splitlines() if not line.lstrip().startswith("import ")
    )


def imports(body: str) -> list[str]:
    return [
        line.strip()
        for line in body.splitlines()
        if line.lstrip().startswith("import ")
    ]


def compile_batch(item: tuple[Batch, Path, int]) -> tuple[Batch, list[Snippet], str]:
    batch, work, timeout = item
    module = work / f"Batch{batch.ordinal}.lean"
    lines = [
        "import LeanCert",
        "import LeanCert.Tactic",
        *dict.fromkeys(
            line
            for snippet in batch.snippets
            for line in imports(snippet.body)
        ),
        "",
        "open LeanCert LeanCert.Core LeanCert.ML",
        "",
    ]
    ranges: list[tuple[int, int, Snippet]] = []
    for index, snippet in enumerate(batch.snippets):
        namespace = f"DocsSnippet{batch.ordinal}_{index}"
        lines.extend([f"namespace {namespace}", f"-- {snippet.label}"])
        start = len(lines) + 1
        body_lines = without_imports(snippet.body).splitlines()
        lines.extend(body_lines)
        end = len(lines)
        ranges.append((start, end, snippet))
        lines.extend([f"end {namespace}", ""])
    module.write_text("\n".join(lines) + "\n")
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(module)],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as exc:
        output = (exc.stdout or "") + f"\nTimed out after {timeout}s"
        return batch, list(batch.snippets), output
    if proc.returncode == 0:
        return batch, [], proc.stdout
    error_lines = [int(value) for value in ERROR_LINE.findall(proc.stdout)]
    failed = {
        snippet
        for line in error_lines
        for start, end, snippet in ranges
        if start <= line <= end
    }
    # Namespace-end errors usually mean an unclosed construct in the preceding
    # snippet. Conservatively report the batch if Lean did not identify a body.
    if not failed:
        failed = set(batch.snippets)
    return batch, sorted(failed, key=lambda s: s.label), proc.stdout


def compile_expected_error(
    item: tuple[Snippet, Path, int],
) -> tuple[Snippet, bool, str]:
    snippet, work, timeout = item
    module = work / f"ExpectedError{abs(hash(snippet.label))}.lean"
    module.write_text(
        "\n".join(
            [
                "import LeanCert",
                "import LeanCert.Tactic",
                *imports(snippet.body),
                "",
                "open LeanCert LeanCert.Core LeanCert.ML",
                "",
                without_imports(snippet.body),
                "",
            ]
        )
    )
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(module)],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as exc:
        return snippet, False, (exc.stdout or "") + f"\nTimed out after {timeout}s"
    return snippet, proc.returncode != 0, proc.stdout


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument("--batch-size", type=int, default=20)
    parser.add_argument("--list", action="store_true")
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument("--match", help="only check snippet labels matching this regex")
    args = parser.parse_args()
    snippets = collect()
    if args.match:
        pattern = re.compile(args.match)
        snippets = [snippet for snippet in snippets if pattern.search(snippet.label)]
    if args.list:
        for snippet in snippets:
            print(snippet.label)
        print(f"{len(snippets)} Lean snippets")
        return 0

    normal = [snippet for snippet in snippets if not snippet.expect_error]
    expected_errors = [snippet for snippet in snippets if snippet.expect_error]
    batches = [
        Batch(i, normal[start : start + args.batch_size])
        for i, start in enumerate(range(0, len(normal), args.batch_size))
    ]
    with tempfile.TemporaryDirectory(prefix="leancert-doc-snippets-") as raw:
        work = Path(raw)
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
            results = list(
                pool.map(
                    compile_batch,
                    ((batch, work, args.timeout) for batch in batches),
                )
            )
            expected_results = list(
                pool.map(
                    compile_expected_error,
                    ((snippet, work, args.timeout) for snippet in expected_errors),
                )
            )

    failed: dict[str, tuple[Snippet, str]] = {}
    for _batch, snippets_failed, output in results:
        for snippet in snippets_failed:
            failed[snippet.label] = (snippet, output)
    for snippet, failed_as_expected, output in expected_results:
        if not failed_as_expected:
            failed[snippet.label] = (
                snippet,
                output + "\nExpected Lean to reject this snippet, but it compiled.",
            )
    for label in sorted(failed):
        print(f"FAIL: {label}")
        if args.verbose:
            print(failed[label][1].rstrip())
    print(f"\nCompiled {len(snippets) - len(failed)}/{len(snippets)} Lean snippets.")
    if failed:
        print("Rerun after relabelling schematic fences as `text` or fixing the listed blocks.")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
