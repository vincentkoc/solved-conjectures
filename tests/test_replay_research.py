import contextlib
import io
import json
import runpy
import subprocess
import unittest
from pathlib import Path
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
compile_proof = runpy.run_path(str(ROOT / "scripts/replay-research"))["compile_proof"]


class ReplayAxiomTests(unittest.TestCase):
    def replay(self, *reports):
        output = "\n".join(
            json.dumps({"kind": "other", "severity": "information", "data": report})
            for report in reports
        )
        result = subprocess.CompletedProcess(["lean"], 0, output)
        with patch.object(subprocess, "run", return_value=result), contextlib.redirect_stdout(io.StringIO()):
            compile_proof(Path("Proof.lean"), Path("."), {})

    def test_unexpected_axiom_on_primed_name_after_clean_report(self):
        with self.assertRaisesRegex(SystemExit, "unexpected axioms.*unchecked"):
            self.replay(
                "'ordinary' does not depend on any axioms",
                "'Theta.row_eq_S'' depends on axioms: [propext, unchecked]",
            )

    def test_primed_name_without_axioms(self):
        self.replay("'ordinary''' does not depend on any axioms")
