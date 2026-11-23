from pathlib import Path
import hashlib
import json
import os
import re
import subprocess


root = Path(__file__).resolve().parents[2]
evidence = Path(__file__).resolve().parent
overlay = evidence / "checked"
runner = root.parents[2] / "tools/lean_within_memory.sh"
modules = [
    "Mettapedia.GSLT.Dedukti.Interpretation",
    "Mettapedia.GSLT.Dedukti.TypingSubstitution",
    "Mettapedia.GSLT.LanguageDef.ModuleAlgebra.ClosedTermGluing",
    "Mettapedia.GSLT.LanguageDef.ModuleAlgebra.DeduktiTranslationControls",
]
consumers = [
    "Mettapedia.GSLT.LanguageDef.ModuleAlgebra.DeduktiModuleInterpretations",
    "Mettapedia.GSLT.Dedukti.TypedPresentation",
    "Mettapedia.GSLT.Dedukti.LanguageDefExamples",
    "Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation",
    "Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotationControls",
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


start = json.loads((evidence / "qualification-source-start.json").read_text())
before = {path: sha(root / path) for path in start}
if before != start:
    raise SystemExit("source closure changed before final qualification")
compiled_before = {
    path: sha(overlay / Path(path).with_suffix(".olean")) for path in start
}
(evidence / "compiled-before.json").write_text(json.dumps(compiled_before, indent=2) + "\n")
results = []


def check(source, label):
    command = [str(runner), "run", "lake", "env", "python3",
               str(evidence / "lean_check.py"), str(source.relative_to(root)),
               "-DwarningAsError=true"]
    log = evidence / f"strict-{label}.log"
    with log.open("w") as stream:
        result = subprocess.run(command, cwd=root, env={**os.environ,
            "LEAN_RUN_BUDGET_GB": "4", "LEAN_RUN_WAIT_S": "60"},
            stdout=stream, stderr=subprocess.STDOUT)
    row = {"source": str(source.relative_to(root)), "exit": result.returncode,
           "log": log.name, "passed": result.returncode == 0}
    results.append(row)
    print(json.dumps(row), flush=True)
    if not row["passed"]:
        raise SystemExit("strict qualification failed")


for module in modules + consumers:
    source = root / Path(module.replace(".", "/")).with_suffix(".lean")
    check(source, module.rsplit(".", 1)[1])
check(evidence / "Audit.lean", "axioms")
audit = (evidence / "strict-axioms.log").read_text()
summary = re.search(
    r"SUMMARY: (\d+) modules, (\d+) kernel declarations, (\d+) theorems, (\d+) compiler-only names",
    audit,
)
if not summary:
    raise SystemExit("missing complete axiom audit")


def without_comments_and_strings(source):
    result = []
    index = 0
    depth = 0
    quoted = False
    while index < len(source):
        if depth:
            if source.startswith("/-", index):
                depth += 1
                index += 2
            elif source.startswith("-/", index):
                depth -= 1
                index += 2
            else:
                result.append("\n" if source[index] == "\n" else " ")
                index += 1
        elif quoted:
            if source[index] == "\\":
                result.append("  ")
                index += 2
            elif source[index] == '"':
                quoted = False
                result.append(" ")
                index += 1
            else:
                result.append("\n" if source[index] == "\n" else " ")
                index += 1
        elif source.startswith("/-", index):
            depth = 1
            index += 2
        elif source.startswith("--", index):
            end = source.find("\n", index)
            if end < 0:
                break
            result.append("\n")
            index = end + 1
        elif source[index] == '"':
            quoted = True
            result.append(" ")
            index += 1
        else:
            result.append(source[index])
            index += 1
    return "".join(result)


forbidden = re.compile(
    r"(?<![\w.])(?:sorry|admit|axiom|native_decide|unsafe|partial|theorem_wanted)(?![\w?])"
    r"|_wanted\b|set_option\s+(?:maxHeartbeats|maxRecDepth)"
)
owned = [root / Path(module.replace(".", "/")).with_suffix(".lean") for module in modules]
violations = []
for source in owned:
    violations.extend({"source": str(source.relative_to(root)), "text": match.group()}
                      for match in forbidden.finditer(without_comments_and_strings(source.read_text())))
(evidence / "source-scan.json").write_text(json.dumps(violations, indent=2) + "\n")
if violations:
    raise SystemExit("forbidden declaration or proof placeholder")

after = {path: sha(root / path) for path in start}
compiled_after = {
    path: sha(overlay / Path(path).with_suffix(".olean")) for path in start
}
stable = start == after and compiled_before == compiled_after
(evidence / "stability.json").write_text(json.dumps({
    "stable": stable, "local_sources": len(start),
    "compiled_modules": len(compiled_before)}, indent=2) + "\n")
if not stable:
    raise SystemExit("source or compiled dependency changed during qualification")

joined = (evidence / "joined-build.log").read_text()
completed = re.search(r"Build completed successfully \((\d+) jobs\)", joined)
if not completed or not re.search(r"lean_within_memory: exit 0,", joined):
    raise SystemExit("joined Lake build not complete")
prior = root.parents[2] / "scratch/dedukti-priority-audit-20261008/QUALIFICATION.json"
if sha(prior) != "c8b8e909f59eba0dfbe5928f12b16f8dbe79b08efe57ba03ccaeb9061034c65a":
    raise SystemExit("prior priority-audit receipt changed")
receipt = {
    "scope": "Modular typed Dedukti interpretations, verified return laws and authored GSLT-ML controls",
    "sources": {str(source.relative_to(root)): sha(source) for source in owned},
    "local_sources_stable": len(start), "compiled_modules_stable": len(compiled_before),
    "strict_results": results,
    "joined_build": {"jobs": int(completed.group(1)), "exit": 0,
        "dependency_warning_lines": len(re.findall(r"^warning:", joined, re.M)),
        "log": "joined-build.log"},
    "audit": dict(zip(["modules", "kernel_declarations", "theorems", "compiler_only_names"],
                      map(int, summary.groups()))),
    "allowed_transitive_axioms": ["propext", "Classical.choice", "Quot.sound"],
    "source_scan": "source-scan.json", "prior_priority_audit_sha256": sha(prior),
    "evidence": {name: sha(evidence / name) for name in
                 ["Audit.lean", "lean_check.py", "qualification-source-start.json",
                  "compiled-before.json", "strict-axioms.log", "joined-build.log"]},
    "limits": [
        "Four changed modules and named consumers qualified; complete package root not qualified",
        "Quotation and finite token parsing controls are not a complete byte frontend",
        "Partial surface adapter receives an explicit source signature",
        "No arbitrary Dedukti-to-Lean inverse, proof-provenance identity, or generic conservativity",
        "Existing GSLT-ML covered executor applies here to equation-free nonrecursive rules",
        "Full Dedukti recursive premises fail that executor's applicability hypothesis",
        "No new ordered conversion theory or repair of the LeanMinus encoding",
        "Joined dependencies emit warnings; scoped strict checks are warning-free",
    ],
}
(evidence / "results.json").write_text(json.dumps(results, indent=2) + "\n")
(evidence / "QUALIFICATION.json").write_text(json.dumps(receipt, indent=2) + "\n")
print("Qualified: " + sha(evidence / "QUALIFICATION.json"), flush=True)
