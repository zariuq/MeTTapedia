from pathlib import Path
import hashlib
import json
import re
import subprocess

root = Path(__file__).resolve().parents[2]
evidence = Path(__file__).resolve().parent
runner = root.parents[2] / "tools/lean_within_memory.sh"
wrapper = root / "artifacts/upstream-authoring-20261008/lean_check.py"
overlay = root / "artifacts/upstream-authoring-20261008/checked"
modules = [
    "Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation",
    "Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotationControls",
]
sources = [root / Path(module.replace(".", "/")).with_suffix(".lean") for module in modules]


def hashes(paths):
    return {
        str(path.relative_to(root)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sorted(paths)
        if path.exists()
    }


closure = set(sources)
queue = list(sources)
while queue:
    source = queue.pop()
    for name in re.findall(r"^import\s+(Mettapedia\.[A-Za-z0-9_.]+)", source.read_text(), re.M):
        dependency = root / Path(name.replace(".", "/")).with_suffix(".lean")
        if dependency.exists() and dependency not in closure:
            closure.add(dependency)
            queue.append(dependency)
before = hashes(closure)
compiled_dependencies = [overlay / path.relative_to(root).with_suffix(".olean")
                         for path in closure if path not in sources]
compiled_before = hashes(compiled_dependencies)
(evidence / "source-before.json").write_text(json.dumps(before, indent=2) + "\n")
(evidence / "dependencies-before.json").write_text(json.dumps(compiled_before, indent=2) + "\n")
results = []


def check(source, label, expected=0, output=None):
    command = [str(runner), "run", "lake", "env", "python3", str(wrapper),
               str(source.relative_to(root)), "-DwarningAsError=true"]
    if output is not None:
        command += ["-o", str(output.relative_to(root))]
    log = evidence / f"{label}.log"
    with log.open("w") as stream:
        result = subprocess.run(command, cwd=root, stdout=stream, stderr=subprocess.STDOUT)
    text = log.read_text()
    passed = result.returncode == expected
    if expected != 0:
        passed = passed and f"{source.name}:" in text and "error: unexpected " in text
    row = {"source": str(source.relative_to(root)), "exit": result.returncode,
           "expected": expected, "passed": passed, "log": log.name}
    results.append(row)
    print(json.dumps(row), flush=True)
    if not passed:
        raise SystemExit(1)


for name, source in zip(modules, sources):
    check(source, name.rsplit(".", 1)[1],
          output=overlay / Path(name.replace(".", "/")).with_suffix(".olean"))
check(evidence / "Example.lean", "example")
check(evidence / "UnsupportedQuantifier.lean", "unsupported-quantifier", expected=1)
check(evidence / "MissingSentenceBoundary.lean", "missing-sentence-boundary", expected=1)
check(root / "Mettapedia/GSLT/Examples/ScopedPremiseAuthoring.lean", "scoped-premise-consumer")
check(root / "Mettapedia/GSLT/LanguageDef/DerivedHosting.lean", "derived-hosting-consumer")
check(evidence / "Audit.lean", "axioms")

after = hashes(closure)
compiled_after = hashes(compiled_dependencies)
stable = before == after and compiled_before == compiled_after
(evidence / "results.json").write_text(json.dumps(results, indent=2) + "\n")
(evidence / "stability.json").write_text(json.dumps({"stable": stable,
    "local_sources": len(before), "compiled_dependencies": len(compiled_before)}, indent=2) + "\n")
if not stable:
    raise SystemExit("source or compiled dependency changed during qualification")
scan = re.compile(r"\b(sorry|admit|axiom|native_decide|unsafe|partial)\b|_wanted|set_option\s+(maxHeartbeats|maxRecDepth)")
violations = []
for source in sources:
    for number, line in enumerate(source.read_text().splitlines(), 1):
        if scan.search(line) and not line.strip().startswith(("--", "/--", "`", "The")):
            violations.append((str(source.relative_to(root)), number, line))
# The public `admit?` function is a validator, not a proof placeholder.
violations = [row for row in violations if not re.search(r"\badmit\?", row[2])]
(evidence / "source-scan.json").write_text(json.dumps(violations, indent=2) + "\n")
if violations:
    raise SystemExit("unexpected source declaration or proof placeholder")
receipt = {
    "scope": "Sentence-style Lean quotation into existing QuotedTheory/moduleTheory!",
    "sources": hashes(sources), "local_sources_stable": len(before),
    "compiled_dependencies_stable": len(compiled_before), "strict_results": results,
    "named_english_controls": len(re.findall(r"^theorem\s+", sources[1].read_text().split("namespace English\n", 1)[1].split("end English\n", 1)[0], re.M)),
    "axiom_summary": re.findall(r"SUMMARY:.*", (evidence / "axioms.log").read_text()),
    "limits": ["Lean quotation, not a byte parser or source GSLT realization",
               "No implicit prose quantifier or binding-scope inference",
               "Closed theory declarations only; no ordered upstream builder admission",
               "Equations declare a theory, not proofs of external model equations"],
}
(evidence / "QUALIFICATION.json").write_text(json.dumps(receipt, indent=2) + "\n")
print("Qualified: " + hashlib.sha256((evidence / "QUALIFICATION.json").read_bytes()).hexdigest(), flush=True)
