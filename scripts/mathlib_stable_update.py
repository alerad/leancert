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
    contents = path.read_bytes().decode("utf-8")
    # Validate the complete document before locating its textual block.
    tomllib.loads(contents)
    lines = contents.splitlines(keepends=True)

    table_header = re.compile(
        r"^\s*(?:\[[^\[\]\r\n]+\]|\[\[[^\[\]\r\n]+\]\])\s*(?:#.*)?$"
    )
    starts = [
        index for index, line in enumerate(lines) if line.strip() == "[[require]]"
    ]
    matching_blocks: list[tuple[int, int]] = []
    for start in starts:
        end = next(
            (
                index
                for index in range(start + 1, len(lines))
                if table_header.fullmatch(lines[index].rstrip("\r\n"))
            ),
            len(lines),
        )
        block = tomllib.loads("".join(lines[start:end]))["require"][0]
        if block.get("name") == "mathlib" and block.get("git") == MATHLIB_REMOTE:
            matching_blocks.append((start, end))

    if len(matching_blocks) != 1:
        raise ValueError(
            f"expected exactly one Mathlib requirement, found {len(matching_blocks)}"
        )

    start, end = matching_blocks[0]
    rev_line = re.compile(r'^(\s*rev\s*=\s*)"[^"]*"(.*)$')
    for index in range(start + 1, end):
        line = lines[index]
        body = line.rstrip("\r\n")
        newline = line[len(body) :]
        match = rev_line.fullmatch(body)
        if match is not None:
            lines[index] = f'{match.group(1)}"{tag}"{match.group(2)}{newline}'
            path.write_bytes("".join(lines).encode("utf-8"))
            return
    raise ValueError("could not locate Mathlib rev in the matching requirement")


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
    filenames = ("lakefile.toml", "lean-toolchain", "lake-manifest.json")
    originals = {
        filename: (root / filename).read_bytes() if (root / filename).exists() else None
        for filename in filenames
    }
    try:
        update_mathlib_pin(root / "lakefile.toml", tag)
        (root / "lean-toolchain").write_text(
            f"leanprover/lean4:{tag}\n", encoding="utf-8"
        )
        subprocess.run(
            ["lake", "update"],
            cwd=root,
            env={**os.environ, "MATHLIB_NO_CACHE_ON_UPDATE": "1"},
            check=True,
        )

        destination = metadata_dir / tag
        destination.mkdir(parents=True, exist_ok=True)
        for filename in filenames:
            shutil.copy2(root / filename, destination / filename)
    except Exception:
        for filename, contents in originals.items():
            target = root / filename
            if contents is None:
                target.unlink(missing_ok=True)
            else:
                target.write_bytes(contents)
        raise


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
