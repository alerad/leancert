#!/usr/bin/env python3
"""Validate every Markdown fence labelled `lean` or `lean expect-error`.

Imports are hoisted ahead of the private namespace used for each block. A
regular `lean` fence must compile; `lean expect-error: <regex>` must be
rejected by Lean with a diagnostic matching `<regex>` (a bare exit failure is
not enough — an unrelated breakage such as "unknown tactic" must not satisfy
a negative example). Import-only catalogues are checked against repository
module paths and against the import closure of the Lake targets, so a module
that still exists but is no longer compiled by any target fails here. Their
compilation itself is covered by the functional and downstream contract
targets. Use `text` only for output, mathematical shapes, and pseudocode.
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
MARKDOWN_ROOTS = (ROOT / "README.md", DOCS)
FENCE = re.compile(
    r"^```lean(?P<mode>[ \t]+expect-error(?::[ \t]*(?P<pattern>[^\n]*?))?)?[ \t]*\n"
    r"(?P<body>.*?)^```\s*$",
    re.MULTILINE | re.DOTALL,
)
ERROR_LINE = re.compile(
    r"^[^:\n]+:(\d+):\d+: (?:error|error\([^)]*\)):", re.MULTILINE
)
IMPORT_LINE = re.compile(r"^import\s+([\w.]+)", re.MULTILINE)


@dataclasses.dataclass(frozen=True)
class Snippet:
    source: Path
    line: int
    ordinal: int
    body: str
    expect_error: bool = False
    expected_diagnostic: str | None = None

    @property
    def label(self) -> str:
        return f"{self.source.relative_to(ROOT)}:{self.line} (block {self.ordinal})"


@dataclasses.dataclass
class Batch:
    ordinal: int
    snippets: list[Snippet]


def collect() -> list[Snippet]:
    snippets: list[Snippet] = []
    sources = [MARKDOWN_ROOTS[0], *sorted(MARKDOWN_ROOTS[1].rglob("*.md"))]
    for source in sources:
        text = source.read_text()
        for ordinal, match in enumerate(FENCE.finditer(text), 1):
            pattern = match.group("pattern")
            snippets.append(
                Snippet(
                    source=source,
                    line=text[: match.start()].count("\n") + 1,
                    ordinal=ordinal,
                    body=match.group("body"),
                    expect_error=bool(match.group("mode")),
                    expected_diagnostic=pattern.strip() if pattern else None,
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


def snippet_imports(snippets: list[Snippet]) -> list[str]:
    """Use documented imports, falling back only for context-free fragments."""
    documented = list(
        dict.fromkeys(line for snippet in snippets for line in imports(snippet.body))
    )
    return documented or ["import LeanCert", "import LeanCert.Tactic"]


def is_import_catalogue(snippet: Snippet) -> bool:
    return bool(imports(snippet.body)) and not without_imports(snippet.body).strip()


def timeout_output(exc: subprocess.TimeoutExpired, timeout: int) -> str:
    raw = exc.stdout or b""
    output = raw.decode(errors="replace") if isinstance(raw, bytes) else raw
    return output + f"\nTimed out after {timeout}s"


def module_source(module: str) -> Path:
    return ROOT / Path(*module.split(".")).with_suffix(".lean")


def lake_target_roots() -> list[str]:
    """Every root module of a Lake target declared in lakefile.toml."""
    text = (ROOT / "lakefile.toml").read_text()
    roots = re.findall(r'^root\s*=\s*"([\w.]+)"', text, re.MULTILINE)
    for group in re.findall(r"^roots\s*=\s*\[(.*?)\]", text, re.MULTILINE | re.DOTALL):
        roots.extend(re.findall(r'"([\w.]+)"', group))
    return roots


def built_module_closure() -> set[str]:
    """Modules transitively imported by some Lake target root.

    CI builds every target (manual benchmarks aside), so membership here shows
    a module is still compiled somewhere. A documented module whose source file
    survives but has dropped out of this closure is orphaned: nothing builds it
    any more, and its catalogue must fail rather than pass on file existence.
    """
    seen: set[str] = set()
    stack = lake_target_roots()
    while stack:
        module = stack.pop()
        if module in seen:
            continue
        seen.add(module)
        source = module_source(module)
        if source.is_file():
            stack.extend(IMPORT_LINE.findall(source.read_text()))
    return seen


def validate_import_catalogues(
    snippets: list[Snippet],
) -> list[tuple[Snippet, bool, str]]:
    built = built_module_closure() if snippets else set()
    results = []
    for snippet in snippets:
        problems = []
        for line in imports(snippet.body):
            module = line.removeprefix("import ").split()[0]
            source = module_source(module)
            if not source.is_file():
                problems.append(
                    f"{module}: missing source {source.relative_to(ROOT)}"
                )
            elif module not in built:
                problems.append(
                    f"{module}: source exists but no Lake target imports it, "
                    "so nothing compiles it any more"
                )
        output = (
            "Documented Lean module is not built: " + ", ".join(problems)
            if problems
            else ""
        )
        results.append((snippet, not problems, output))
    return results


def compile_batch(item: tuple[Batch, Path, int]) -> tuple[Batch, list[Snippet], str]:
    batch, work, timeout = item
    module = work / f"Batch{batch.ordinal}.lean"
    lines = [
        *snippet_imports(batch.snippets),
        "",
    ]
    if not any(imports(snippet.body) for snippet in batch.snippets):
        lines.extend(["open LeanCert LeanCert.Core LeanCert.ML", ""])
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
        output = timeout_output(exc, timeout)
        return batch, list(batch.snippets), output
    if proc.returncode == 0:
        return batch, [], proc.stdout
    if not proc.stdout.strip():
        proc.stdout = f"Lean exited with status {proc.returncode} without diagnostics."
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
    if not snippet.expected_diagnostic:
        return snippet, False, (
            "expect-error fences must declare the diagnostic they expect, "
            "e.g. ```lean expect-error: Counter-example FOUND\n"
            "Otherwise any unrelated breakage (unknown tactic, bad import) "
            "would satisfy the negative example."
        )
    try:
        expected = re.compile(snippet.expected_diagnostic)
    except re.error as exc:
        return snippet, False, (
            f"Invalid expect-error regex {snippet.expected_diagnostic!r}: {exc}"
        )
    module = work / f"ExpectedError{abs(hash(snippet.label))}.lean"
    lines = [*snippet_imports([snippet]), ""]
    if not imports(snippet.body):
        lines.extend(["open LeanCert LeanCert.Core LeanCert.ML", ""])
    lines.extend([without_imports(snippet.body), ""])
    module.write_text("\n".join(lines))
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
        return snippet, False, timeout_output(exc, timeout)
    if proc.returncode == 0:
        return snippet, False, (
            proc.stdout + "\nExpected Lean to reject this snippet, but it compiled."
        )
    if not expected.search(proc.stdout):
        return snippet, False, (
            proc.stdout
            + "\nLean rejected this snippet, but not with the documented "
            f"diagnostic (expected match for {snippet.expected_diagnostic!r}). "
            "The failure reason is unrelated to the example."
        )
    return snippet, True, proc.stdout


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--jobs",
        type=int,
        default=2,
        help="parallel Lean processes (kept conservative for CI memory limits)",
    )
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument(
        "--batch-size",
        type=int,
        default=20,
        help="maximum snippets per generated module with an identical import list",
    )
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

    normal = [
        snippet
        for snippet in snippets
        if not snippet.expect_error and not is_import_catalogue(snippet)
    ]
    import_catalogues = [
        snippet
        for snippet in snippets
        if not snippet.expect_error and is_import_catalogue(snippet)
    ]
    expected_errors = [snippet for snippet in snippets if snippet.expect_error]
    # Never hoist imports across unrelated examples: doing so both invalidates
    # narrow-import tests and can construct synthetic modules too large for CI.
    # Snippets with identical imports remain safe to batch for performance.
    groups: dict[tuple[str, ...], list[Snippet]] = {}
    for snippet in normal:
        signature = tuple(snippet_imports([snippet]))
        groups.setdefault(signature, []).append(snippet)
    batches = []
    for signature, snippets_with_same_imports in groups.items():
        for start in range(0, len(snippets_with_same_imports), args.batch_size):
            batches.append(
                Batch(
                    len(batches),
                    snippets_with_same_imports[start : start + args.batch_size],
                )
            )
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
        # Import-only fences are API catalogues rather than programs. Their
        # modules are compiled by the Lake targets CI builds; verify each
        # documented module sits in the import closure of some target root
        # (so it is genuinely still built) without loading heavyweight
        # umbrella environments into another Lean process.
        import_results = validate_import_catalogues(import_catalogues)
        # A worker killed by transient resource pressure produces no source
        # location, so `compile_batch` conservatively reports its whole batch.
        # Lean can also attribute an import/elaboration interaction in a
        # synthetic batch to otherwise-valid snippet source lines. Retry every
        # reported failure after the parallel workers have exited and with no
        # neighbouring snippets. Genuine syntax/elaboration errors still fail
        # the isolated retry, while batch-only failures do not make valid
        # documentation examples flaky in CI.
        retried_results = []
        for batch, snippets_failed, output in results:
            if not snippets_failed:
                retried_results.append((batch, snippets_failed, output))
                continue
            for snippet in snippets_failed:
                isolated = Batch(batch.ordinal, [snippet])
                retried_results.append(
                    compile_batch((isolated, work, args.timeout))
                )
        results = retried_results

    failed: dict[str, tuple[Snippet, str]] = {}
    for _batch, snippets_failed, output in results:
        for snippet in snippets_failed:
            failed[snippet.label] = (snippet, output)
    for snippet, failed_as_expected, output in expected_results:
        if not failed_as_expected:
            failed[snippet.label] = (snippet, output)
    for snippet, built, output in import_results:
        if not built:
            failed[snippet.label] = (snippet, output)
    for label in sorted(failed):
        print(f"FAIL: {label}")
        if args.verbose:
            print(failed[label][1].rstrip())
    if failed and not args.verbose:
        opaque_outputs = {
            output.rstrip()
            for _snippet, output in failed.values()
            if output.strip() and not ERROR_LINE.search(output)
        }
        for output in sorted(opaque_outputs):
            print("\nTop-level Lean failure (rerun with --verbose for all diagnostics):")
            print(output)
    print(f"\nCompiled {len(snippets) - len(failed)}/{len(snippets)} Lean snippets.")
    if failed:
        print("Rerun after relabelling schematic fences as `text` or fixing the listed blocks.")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
