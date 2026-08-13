#!/usr/bin/env python3
"""Bundle LeanCert's dyadic sources and local import closure for an LLM prompt."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
from pathlib import Path
import re
import shutil
import subprocess
import sys


REPO = Path(__file__).resolve().parents[1]
SOURCE_ROOT = REPO / "LeanCert"
IMPORT_RE = re.compile(r"^\s*import\s+(.+?)\s*(?:--.*)?$")
DYADIC_RE = re.compile(r"\b(?:Dyadic|IntervalDyadic|DyadicConfig)\b")


def module_path(module: str) -> Path | None:
    """Resolve a Lean module name to a source file in this repository."""
    candidate = REPO / (module.replace(".", "/") + ".lean")
    return candidate.resolve() if candidate.is_file() else None


def module_name(path: Path) -> str:
    return path.resolve().relative_to(REPO).with_suffix("").as_posix().replace("/", ".")


def imports_of(path: Path) -> list[str]:
    imports: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = IMPORT_RE.match(line)
        if match:
            imports.extend(match.group(1).split())
    return imports


def resolve_root(value: str) -> Path:
    as_path = Path(value)
    candidates = [as_path, REPO / as_path]
    if as_path.suffix != ".lean":
        candidates.extend([as_path.with_suffix(".lean"), (REPO / as_path).with_suffix(".lean")])
    for candidate in candidates:
        if candidate.is_file():
            resolved = candidate.resolve()
            if REPO not in resolved.parents:
                raise ValueError(f"root is outside the repository: {value}")
            return resolved
    resolved = module_path(value)
    if resolved:
        return resolved
    raise ValueError(f"cannot resolve root as a path or Lean module: {value}")


def default_seeds(mode: str, include_tests: bool) -> list[Path]:
    files = sorted(SOURCE_ROOT.rglob("*.lean"))
    if not include_tests:
        files = [path for path in files if "Test" not in path.relative_to(SOURCE_ROOT).parts]
    if mode == "named":
        return [path.resolve() for path in files if "dyadic" in path.name.lower()]
    return [
        path.resolve()
        for path in files
        if DYADIC_RE.search(path.read_text(encoding="utf-8"))
    ]


def import_closure(seeds: list[Path]) -> tuple[list[Path], dict[Path, list[str]]]:
    """Return a dependency-first local closure and imports for every source."""
    state: dict[Path, int] = {}
    order: list[Path] = []
    imports: dict[Path, list[str]] = {}

    def visit(path: Path) -> None:
        status = state.get(path, 0)
        if status == 2:
            return
        if status == 1:
            return  # Lean imports should be acyclic; keep diagnostics usable if not.
        state[path] = 1
        names = imports.setdefault(path, imports_of(path))
        for imported in names:
            dependency = module_path(imported)
            if dependency is not None:
                visit(dependency)
        state[path] = 2
        order.append(path)

    for seed in sorted(seeds, key=module_name):
        visit(seed)
    return order, imports


def render_bundle(seeds: list[Path], files: list[Path], imports: dict[Path, list[str]]) -> str:
    local_set = set(files)
    local_edges: list[tuple[str, str]] = []
    external_edges: list[tuple[str, str]] = []
    for source in files:
        for imported in imports[source]:
            dependency = module_path(imported)
            edge = (module_name(source), imported)
            if dependency in local_set:
                local_edges.append(edge)
            elif dependency is None:
                external_edges.append(edge)

    lines = [
        "# LeanCert dyadic context bundle",
        "",
        f"Generated: {datetime.now(timezone.utc).isoformat()}",
        f"Repository: {REPO}",
        f"Seed files: {len(seeds)}",
        f"Files in local import closure: {len(files)}",
        "",
        "## Seed modules",
        "",
        *(f"- {module_name(path)}" for path in sorted(seeds, key=module_name)),
        "",
        "## Dependency-first source order",
        "",
        *(f"{index}. {module_name(path)}" for index, path in enumerate(files, 1)),
        "",
        "## Local import trace",
        "",
        *(f"- {source} -> {target}" for source, target in sorted(local_edges)),
        "",
        "## External import trace (source not bundled)",
        "",
        *(f"- {source} -> {target}" for source, target in sorted(external_edges)),
        "",
        "## Complete sources",
        "",
    ]
    for path in files:
        relative = path.relative_to(REPO).as_posix()
        lines.extend(
            [
                f"### FILE: {relative}",
                "",
                "```lean",
                path.read_text(encoding="utf-8").rstrip(),
                "```",
                "",
            ]
        )
    return "\n".join(lines)


def clipboard_command() -> list[str] | None:
    if shutil.which("pbcopy"):
        return ["pbcopy"]
    if shutil.which("wl-copy"):
        return ["wl-copy"]
    if shutil.which("xclip"):
        return ["xclip", "-selection", "clipboard"]
    if shutil.which("xsel"):
        return ["xsel", "--clipboard", "--input"]
    return None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--mode",
        choices=("named", "mentions"),
        default="named",
        help="seed from filenames containing 'dyadic' (default), or every source mentioning dyadic types",
    )
    parser.add_argument(
        "--exclude-tests",
        action="store_true",
        help="exclude LeanCert/Test files from automatically discovered seeds",
    )
    parser.add_argument(
        "--root",
        action="append",
        default=[],
        metavar="PATH_OR_MODULE",
        help="use this explicit seed instead of automatic discovery; repeat as needed",
    )
    parser.add_argument("--output", type=Path, help="also write the bundle to this file")
    parser.add_argument("--no-clipboard", action="store_true", help="do not copy the bundle")
    parser.add_argument("--list-files", action="store_true", help="print bundled file paths")
    parser.add_argument(
        "--max-estimated-tokens",
        type=int,
        default=900_000,
        help="refuse an oversized bundle (rough character/4 estimate); use 0 to disable",
    )
    parser.add_argument("--force", action="store_true", help="copy even when the estimate exceeds the limit")
    args = parser.parse_args()

    try:
        seeds = (
            [resolve_root(value) for value in args.root]
            if args.root
            else default_seeds(args.mode, not args.exclude_tests)
        )
    except ValueError as error:
        parser.error(str(error))
    if not seeds:
        parser.error("no dyadic seed files found")

    files, imports = import_closure(seeds)
    bundle = render_bundle(seeds, files, imports)
    byte_count = len(bundle.encode("utf-8"))
    estimated_tokens = len(bundle) // 4

    if args.list_files:
        for path in files:
            print(path.relative_to(REPO))

    if (
        args.max_estimated_tokens > 0
        and estimated_tokens > args.max_estimated_tokens
        and not args.force
    ):
        print(
            f"Refusing bundle: ~{estimated_tokens:,} tokens exceeds "
            f"--max-estimated-tokens={args.max_estimated_tokens:,}. "
            "Use --force, --mode named, --exclude-tests, or explicit --root values.",
            file=sys.stderr,
        )
        return 2

    if args.output:
        destination = args.output if args.output.is_absolute() else REPO / args.output
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(bundle, encoding="utf-8")
        print(f"Wrote {destination}")

    copied = False
    if not args.no_clipboard:
        command = clipboard_command()
        if command is None:
            print(
                "No supported clipboard command found (pbcopy, wl-copy, xclip, or xsel). "
                "Use --output PATH.",
                file=sys.stderr,
            )
            if not args.output:
                return 1
        else:
            subprocess.run(command, input=bundle, text=True, check=True)
            copied = True

    action = "Copied" if copied else "Prepared"
    print(
        f"{action} {len(files)} files from {len(seeds)} seeds: "
        f"{byte_count:,} bytes, approximately {estimated_tokens:,} tokens."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
