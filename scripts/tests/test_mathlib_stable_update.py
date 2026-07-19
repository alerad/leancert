import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts.mathlib_stable_update import (
    prepare_update,
    remote_tags,
    select_latest_stable,
    stable_version,
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
            (root / "lake-manifest.json").write_text("{}\n", encoding="utf-8")
            metadata = root / "metadata"

            with patch("scripts.mathlib_stable_update.subprocess.run") as run:
                prepare_update(root, "v4.33.0", metadata)

            run.assert_called_once()
            prepared = metadata / "v4.33.0"
            self.assertEqual(
                {path.name for path in prepared.iterdir()},
                {"lakefile.toml", "lean-toolchain", "lake-manifest.json"},
            )
            self.assertIn('rev = "v4.33.0"', (prepared / "lakefile.toml").read_text())
            self.assertEqual(
                (prepared / "lean-toolchain").read_text(),
                "leanprover/lean4:v4.33.0\n",
            )


if __name__ == "__main__":
    unittest.main()
