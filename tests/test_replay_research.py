import contextlib
import io
import json
import runpy
import subprocess
import unittest
from pathlib import Path
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
runner = runpy.run_path(str(ROOT / "scripts/replay-research"))
compile_proof = runner["compile_proof"]


class ReplayKernelTests(unittest.TestCase):
    def test_each_module_runs_in_its_own_checked_process(self):
        sources = [Path("Base.lean"), Path("Derived.lean")]
        env = {"LEAN_PATH": "compiled"}
        with patch.object(subprocess, "run") as run:
            runner["replay_kernel"](sources, env)
        self.assertEqual(
            [(call.args[0], call.kwargs) for call in run.call_args_list],
            [(["leanchecker", "-v", source.stem], {"env": env, "check": True}) for source in sources],
        )


class ReplaySelectionTests(unittest.TestCase):
    def test_requested_roots_only_visit_their_shared_imports(self):
        upstream = ROOT / "upstream"
        a, b, shared, unused = [
            ROOT / "research" / (name + ".lean") for name in ("A", "B", "Shared", "Unused")
        ]
        deps = {
            a: [shared],
            b: [shared],
            shared: [upstream / "FormalConjectures/Source.lean",
                     upstream / ".lake/packages/mathlib/Mathlib.lean"],
        }
        seen = []

        def source_deps(command, **kwargs):
            if command == ["lean", "--deps-json", "--stdin"]:
                headers = []
                for source in map(Path, kwargs["input"].splitlines()):
                    names = [path.stem for path in deps[source]]
                    if source == b:
                        names = ["research.Shared"]
                    imports = [{"module": name} for name in names]
                    headers.append({"errors": [], "result": {"imports": imports}})
                return json.dumps({"imports": headers})
            self.assertEqual(command[:2], ["lean", "--src-deps"])
            seen.append(command[2])
            return "\n".join(map(str, deps[command[2]]))

        with patch.object(subprocess, "check_output", side_effect=source_deps):
            order, targets, aliases = runner["dependency_order"](
                [b, a, b], {a, b, shared, unused}, upstream, {},
            )
        self.assertCountEqual(seen, [a, b, shared])
        self.assertCountEqual(order, [a, b, shared])
        self.assertEqual(aliases, {shared})
        self.assertEqual(order[0], shared)
        self.assertEqual(targets, ["FormalConjectures/Source.lean:olean"])


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
