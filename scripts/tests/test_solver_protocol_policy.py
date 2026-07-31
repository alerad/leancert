import importlib.util
from pathlib import Path
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
CHECKER = ROOT / "scripts" / "check_solver_protocol_policy.py"
SPEC = importlib.util.spec_from_file_location("solver_protocol_policy", CHECKER)
assert SPEC is not None and SPEC.loader is not None
policy = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(policy)


class SolverProtocolPolicyTests(unittest.TestCase):
    def test_clean_typed_source_passes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Typed.lean").write_text(
                "def solve := proveWithTypedSolver plan attempt\n",
                encoding="utf-8",
            )
            self.assertEqual(policy.violations(root), [])

    def test_retired_identifier_is_reported_with_location(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Legacy.lean"
            path.write_text(
                "def first := true\n"
                "def bad := legacyExceptionAdapter\n",
                encoding="utf-8",
            )
            self.assertEqual(
                policy.violations(root),
                [(path, 2, "legacyExceptionAdapter")],
            )

    def test_unrelated_reported_state_is_allowed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "State.lean").write_text(
                "def autoFallbackReported := true\n",
                encoding="utf-8",
            )
            self.assertEqual(policy.violations(root), [])


if __name__ == "__main__":
    unittest.main()
