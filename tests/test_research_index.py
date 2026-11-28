import runpy
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
research_table_errors = runpy.run_path(str(ROOT / "scripts/add-entry"))["research_table_errors"]


class ResearchIndexTests(unittest.TestCase):
    def test_only_overflowing_rows_are_reported(self):
        table = r"""# Notebook

| Problem | Result | What remains |
| --- | --- | --- |
| A | Short row |
| B | `\|A\|` | Open |
C | Full row | Open
| D | `|A|` | Open |
| E | Result | Open | Stray cell |

Unrelated | prose | outside | the table.
"""
        self.assertEqual(research_table_errors(table), [
            "research/README.md:8: 5 cells in a 3-column table",
            "research/README.md:9: 4 cells in a 3-column table",
        ])
