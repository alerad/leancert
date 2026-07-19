#!/usr/bin/env python3
"""Discover and prepare updates to the latest stable Mathlib release."""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tomllib
from pathlib import Path


MATHLIB_REMOTE = "https://github.com/leanprover-community/mathlib4.git"
STABLE_TAG = re.compile(r"^v(0|[1-9]\d*)\.(0|[1-9]\d*)\.(0|[1-9]\d*)$")
SEMVER_TAG = re.compile(
    r"^v(0|[1-9]\d*)\.(0|[1-9]\d*)\.(0|[1-9]\d*)"
    r"(?:-(?:0|[1-9]\d*|\d*[A-Za-z-][0-9A-Za-z-]*)"
    r"(?:\.(?:0|[1-9]\d*|\d*[A-Za-z-][0-9A-Za-z-]*))*)?"
    r"(?:\+[0-9A-Za-z-]+(?:\.[0-9A-Za-z-]+)*)?$"
)
TOOLCHAIN = re.compile(r"^leanprover/lean4:(v[^\s]+)$")


def stable_version(tag: str) -> tuple[int, int, int] | None:
    """Parse a strict stable release tag, rejecting prereleases and extra components."""
    match = STABLE_TAG.fullmatch(tag)
    if match is None:
        return None
    return tuple(map(int, match.groups()))


def remote_tags(ls_remote: str) -> list[str]:
    """Extract tag names from `git ls-remote --tags` output."""
    tags: list[str] = []
    for line in ls_remote.splitlines():
        fields = line.split()
        if len(fields) != 2 or not fields[1].startswith("refs/tags/"):
            continue
        tag = fields[1].removeprefix("refs/tags/").removesuffix("^{}")
        tags.append(tag)
    return tags


def select_latest_stable(
    tags: list[str], current_tag: str
) -> tuple[str | None, list[str]]:
    """Return the newest stable tag after `current_tag` and malformed version tags."""
    current = stable_version(current_tag)
    if current is None:
        raise ValueError(f"current toolchain tag is not a stable release: {current_tag}")

    releases: list[tuple[tuple[int, int, int], str]] = []
    malformed: list[str] = []
    for tag in set(tags):
        version = stable_version(tag)
        if version is not None:
            releases.append((version, tag))
        elif tag.startswith("v") and "." in tag and SEMVER_TAG.fullmatch(tag) is None:
            malformed.append(tag)

    newer = [release for release in releases if release[0] > current]
    return (max(newer)[1] if newer else None, sorted(malformed))


def read_toolchain(path: Path) -> str:
    contents = path.read_text(encoding="utf-8").strip()
    match = TOOLCHAIN.fullmatch(contents)
    if match is None:
        raise ValueError(f"unsupported lean-toolchain contents: {contents!r}")
    return match.group(1)


def update_mathlib_pin(path: Path, tag: str) -> None:
    """Update the Mathlib `rev` while preserving the rest of lakefile.toml."""
    data = tomllib.loads(path.read_text(encoding="utf-8"))
    requirements = data.get("require", [])
    matches = [
        requirement
        for requirement in requirements
        if requirement.get("name") == "mathlib"
        and requirement.get("git") == MATHLIB_REMOTE
    ]
    if len(matches) != 1:
        raise ValueError(f"expected exactly one Mathlib requirement, found {len(matches)}")

    lines = path.read_text(encoding="utf-8").splitlines(keepends=True)
    in_requirement = False
    is_mathlib = False
    replaced = False
    for index, line in enumerate(lines):
        stripped = line.strip()
        if stripped == "[[require]]":
            in_requirement = True
            is_mathlib = False
            continue
        if in_requirement and stripped.startswith("[["):
            in_requirement = False
        if in_requirement and re.fullmatch(r'name\s*=\s*"mathlib"', stripped):
            is_mathlib = True
        if in_requirement and is_mathlib and re.fullmatch(r'rev\s*=\s*"[^"]+"', stripped):
            newline = "\n" if line.endswith("\n") else ""
            indent = line[: len(line) - len(line.lstrip())]
            lines[index] = f'{indent}rev = "{tag}"{newline}'
            replaced = True
            break
    if not replaced:
        raise ValueError("could not locate Mathlib rev in lakefile.toml")
    path.write_text("".join(lines), encoding="utf-8")


def write_outputs(path: Path | None, tag: str | None) -> None:
    values = {
        "is-update-available": "true" if tag else "false",
        "new-tags": json.dumps([tag] if tag else []),
    }
    for key, value in values.items():
        print(f"{key}={value}")
    if path is not None:
        with path.open("a", encoding="utf-8") as output:
            for key, value in values.items():
                output.write(f"{key}={value}\n")


def prepare_update(root: Path, tag: str, metadata_dir: Path) -> None:
    update_mathlib_pin(root / "lakefile.toml", tag)
    (root / "lean-toolchain").write_text(f"leanprover/lean4:{tag}\n", encoding="utf-8")
    subprocess.run(
        ["lake", "update"],
        cwd=root,
        env={**os.environ, "MATHLIB_NO_CACHE_ON_UPDATE": "1"},
        check=True,
    )

    destination = metadata_dir / tag
    destination.mkdir(parents=True, exist_ok=True)
    for filename in ("lakefile.toml", "lean-toolchain", "lake-manifest.json"):
        shutil.copy2(root / filename, destination / filename)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--tags-file", type=Path)
    parser.add_argument("--github-output", type=Path)
    parser.add_argument("--prepare-metadata", type=Path)
    args = parser.parse_args()

    if args.tags_file:
        tag_output = args.tags_file.read_text(encoding="utf-8")
    else:
        tag_output = subprocess.run(
            ["git", "ls-remote", "--tags", MATHLIB_REMOTE],
            check=True,
            capture_output=True,
            text=True,
        ).stdout

    current = read_toolchain(args.root / "lean-toolchain")
    latest, malformed = select_latest_stable(remote_tags(tag_output), current)
    for tag in malformed:
        print(f"warning: ignoring malformed version tag {tag!r}", file=sys.stderr)
    if latest:
        print(f"Latest stable Mathlib update: {current} -> {latest}")
        if args.prepare_metadata:
            prepare_update(args.root, latest, args.prepare_metadata)
    else:
        print(f"Mathlib is current at stable release {current}")
    write_outputs(args.github_output, latest)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
