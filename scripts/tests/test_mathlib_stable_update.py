import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts.mathlib_stable_update import (
    prepare_update,
    resolved_mathlib_commit,
    remote_tags,
    select_latest_stable,
    stable_version,
    update_expected_mathlib_commit,
    update_mathlib_pin,
)


class MathlibStableUpdateTests(unittest.TestCase):
    def test_strict_stable_versions(self) -> None:
        self.assertEqual(stable_version("v4.33.0"), (4, 33, 0))
        self.assertIsNone(stable_version("v4.33.0-rc1"))
        self.assertIsNone(stable_version("v4.30.0.5"))

    def test_malformed_tags_are_ignored(self) -> None:
        latest, malformed = select_latest_stable(
            [
                "v4.31.0",
                "v4.32.0",
                "v4.33.0-rc1",
                "v4.33.0",
                "v4.28.0.1",
                "v4.30.0.5",
            ],
            "v4.32.0",
        )
        self.assertEqual(latest, "v4.33.0")
        self.assertEqual(malformed, ["v4.28.0.1", "v4.30.0.5"])

    def test_no_update_when_current(self) -> None:
        latest, malformed = select_latest_stable(
            ["v4.32.0", "v4.33.0-rc1"], "v4.32.0"
        )
        self.assertIsNone(latest)
        self.assertEqual(malformed, [])

    def test_ls_remote_parser(self) -> None:
        output = "\n".join(
            [
                "abc refs/tags/v4.32.0",
                "def refs/tags/v4.32.0^{}",
                "ghi refs/heads/master",
            ]
        )
        self.assertEqual(remote_tags(output), ["v4.32.0", "v4.32.0"])

    def test_lakefile_pin_is_updated_without_reformatting(self) -> None:
        original = '''name = "Example"

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "old-revision"

[[lean_lib]]
name = "Example"
'''
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "lakefile.toml"
            path.write_text(original, encoding="utf-8")
            update_mathlib_pin(path, "v4.33.0")
            self.assertEqual(
                path.read_text(encoding="utf-8"),
                original.replace('rev = "old-revision"', 'rev = "v4.33.0"'),
            )

    def test_lakefile_pin_does_not_depend_on_field_order(self) -> None:
        original = '''[[require]]
rev = "old-revision"
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
'''
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "lakefile.toml"
            path.write_text(original, encoding="utf-8")
            update_mathlib_pin(path, "v4.33.0")
            self.assertEqual(
                path.read_text(encoding="utf-8"),
                original.replace('rev = "old-revision"', 'rev = "v4.33.0"'),
            )

    def test_lakefile_pin_updates_only_matching_git_requirement(self) -> None:
        original = '''[[require]]
name = "mathlib"
git = "https://example.com/not-mathlib.git"
rev = "leave-this-alone"

[[require]]
rev = "old-revision"
git = "https://github.com/leanprover-community/mathlib4.git"
name = "mathlib"
'''
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "lakefile.toml"
            path.write_text(original, encoding="utf-8")
            update_mathlib_pin(path, "v4.33.0")
            updated = path.read_text(encoding="utf-8")
            self.assertIn('rev = "leave-this-alone"', updated)
            self.assertIn('rev = "v4.33.0"', updated)
            self.assertNotIn('rev = "old-revision"', updated)

    def test_lakefile_pin_preserves_crlf(self) -> None:
        original = (
            b'[[require]]\r\n'
            b'rev = "old-revision"\r\n'
            b'name = "mathlib"\r\n'
            b'git = "https://github.com/leanprover-community/mathlib4.git"\r\n'
        )
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "lakefile.toml"
            path.write_bytes(original)
            update_mathlib_pin(path, "v4.33.0")
            self.assertEqual(
                path.read_bytes(),
                original.replace(b'"old-revision"', b'"v4.33.0"'),
            )

    def test_resolved_commit_and_compatibility_pin_are_synchronized(self) -> None:
        old_commit = "1" * 40
        new_commit = "2" * 40
        manifest = {
            "packages": [
                {"name": "other", "rev": "3" * 40},
                {"name": "mathlib", "rev": new_commit},
            ]
        }
        checker = (
            "def unrelated : String := \"leave me\"\n"
            f'def expectedMathlibCommit : String := "{old_commit}"\n'
        )
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest_path = root / "lake-manifest.json"
            checker_path = root / "CheckCompat.lean"
            manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
            checker_path.write_text(checker, encoding="utf-8")

            commit = resolved_mathlib_commit(manifest_path)
            update_expected_mathlib_commit(checker_path, commit)

            self.assertEqual(commit, new_commit)
            self.assertEqual(
                checker_path.read_text(encoding="utf-8"),
                checker.replace(old_commit, new_commit),
            )

    def test_prepared_artifact_contains_all_update_inputs(self) -> None:
        lakefile = '''name = "Example"

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "old-revision"
'''
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lakefile.toml").write_text(lakefile, encoding="utf-8")
            (root / "lean-toolchain").write_text(
                "leanprover/lean4:v4.32.0\n", encoding="utf-8"
            )
            old_commit = "1" * 40
            new_commit = "2" * 40
            (root / "lake-manifest.json").write_text(
                json.dumps({"packages": [{"name": "mathlib", "rev": old_commit}]}),
                encoding="utf-8",
            )
            checker = root / "LeanCertMathlibPin.lean"
            checker.write_text(
                f'def expectedMathlibCommit : String := "{old_commit}"\n',
                encoding="utf-8",
            )
            metadata = root / "metadata"

            def update_manifest(*args, **kwargs):
                (root / "lake-manifest.json").write_text(
                    json.dumps(
                        {"packages": [{"name": "mathlib", "rev": new_commit}]}
                    ),
                    encoding="utf-8",
                )

            with patch(
                "scripts.mathlib_stable_update.subprocess.run",
                side_effect=update_manifest,
            ) as run:
                prepare_update(root, "v4.33.0", metadata)

            run.assert_called_once()
            prepared = metadata / "v4.33.0"
            self.assertEqual(
                {
                    path.relative_to(prepared).as_posix()
                    for path in prepared.rglob("*")
                    if path.is_file()
                },
                {
                    "lakefile.toml",
                    "lean-toolchain",
                    "lake-manifest.json",
                    "LeanCertMathlibPin.lean",
                },
            )
            self.assertIn('rev = "v4.33.0"', (prepared / "lakefile.toml").read_text())
            self.assertEqual(
                (prepared / "lean-toolchain").read_text(),
                "leanprover/lean4:v4.33.0\n",
            )
            self.assertIn(
                new_commit,
                (prepared / "LeanCertMathlibPin.lean").read_text(),
            )

    def test_prepare_restores_metadata_after_update_failure(self) -> None:
        lakefile = '''[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "old-revision"
'''
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            originals = {
                "lakefile.toml": lakefile.encode(),
                "lean-toolchain": b"leanprover/lean4:v4.32.0\n",
                "lake-manifest.json": b'{"original": true}\n',
                "LeanCertMathlibPin.lean": (
                    b'def expectedMathlibCommit : String := "'
                    + b"1" * 40
                    + b'"\n'
                ),
            }
            for filename, contents in originals.items():
                target = root / filename
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(contents)

            failure = subprocess.CalledProcessError(1, ["lake", "update"])
            with patch(
                "scripts.mathlib_stable_update.subprocess.run", side_effect=failure
            ):
                with self.assertRaises(subprocess.CalledProcessError):
                    prepare_update(root, "v4.33.0", root / "metadata")

            for filename, contents in originals.items():
                self.assertEqual((root / filename).read_bytes(), contents)
            self.assertFalse((root / "metadata").exists())


if __name__ == "__main__":
    unittest.main()
