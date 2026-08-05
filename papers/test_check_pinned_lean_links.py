from __future__ import annotations

from pathlib import Path
import subprocess
import tempfile
import unittest

from check_pinned_lean_links import audit_paper


def _run(repo: Path, *arguments: str) -> str:
    result = subprocess.run(
        ("git", *arguments),
        cwd=repo,
        check=True,
        capture_output=True,
        text=True,
    )
    return result.stdout.strip()


class PinnedLeanLinkTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.repo = Path(self.temporary.name)
        _run(self.repo, "init", "--quiet")
        source = self.repo / "lean" / "Example.lean"
        source.parent.mkdir(parents=True)
        source.write_text(
            "namespace Example\n"
            "theorem positive_fixture : True := by trivial\n"
            "end Example\n",
            encoding="utf-8",
        )
        _run(self.repo, "add", "lean/Example.lean")
        _run(
            self.repo,
            "-c",
            "user.name=Link Test",
            "-c",
            "user.email=link-test@example.invalid",
            "commit",
            "--quiet",
            "-m",
            "fixture",
        )
        self.commit = _run(self.repo, "rev-parse", "HEAD")

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def _paper(self, path: str, line: int, name: str) -> Path:
        paper = self.repo / "paper.tex"
        paper.write_text(
            f"\\newcommand{{\\formalcommit}}{{{self.commit}}}\n"
            "\\newcommand{\\leansource}[3]{#3}\n"
            f"\\leansource{{{path}}}{{{line}}}{{{name}}}\n",
            encoding="utf-8",
        )
        return paper

    def _signature_paper(self, path: str, line: int) -> Path:
        paper = self.repo / "paper.tex"
        split = path.rsplit("/", maxsplit=1)
        if len(split) == 2:
            rendered_path = f"{split[0]}/%\n{split[1]}"
        else:
            rendered_path = path
        paper.write_text(
            f"\\newcommand{{\\formalcommit}}{{{self.commit}}}\n"
            "\\newcommand{\\leansignaturelink}[2]{#2}\n"
            f"\\leansignaturelink{{{rendered_path}}}{{{line}}}\n",
            encoding="utf-8",
        )
        return paper

    def test_valid_pinned_declaration_passes(self) -> None:
        checked, failures = audit_paper(
            self.repo,
            self._paper(
                "lean/Example.lean",
                2,
                r"Example.\allowbreak positive\_fixture",
            ),
        )
        self.assertEqual(checked, 1)
        self.assertEqual(failures, [])

    def test_missing_source_and_wrong_declaration_fail(self) -> None:
        _, missing = audit_paper(
            self.repo,
            self._paper("lean/Missing.lean", 1, "missing"),
        )
        self.assertEqual([failure.kind for failure in missing], ["source"])
        _, wrong = audit_paper(
            self.repo,
            self._paper("lean/Example.lean", 2, "wrong_name"),
        )
        self.assertEqual(
            [failure.kind for failure in wrong],
            ["declaration"],
        )

    def test_valid_multiline_signature_link_passes(self) -> None:
        checked, failures = audit_paper(
            self.repo,
            self._signature_paper("lean/Example.lean", 2),
        )
        self.assertEqual(checked, 1)
        self.assertEqual(failures, [])

    def test_signature_link_missing_source_and_range_fail(self) -> None:
        _, missing = audit_paper(
            self.repo,
            self._signature_paper("lean/Missing.lean", 1),
        )
        self.assertEqual(
            [failure.kind for failure in missing],
            ["signature-source"],
        )
        _, outside = audit_paper(
            self.repo,
            self._signature_paper("lean/Example.lean", 99),
        )
        self.assertEqual(
            [failure.kind for failure in outside],
            ["signature-line-range"],
        )


if __name__ == "__main__":
    unittest.main()
