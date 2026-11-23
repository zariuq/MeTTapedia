from pathlib import Path
import hashlib, json, re, subprocess

root = Path(__file__).resolve().parents[2]
evidence = Path(__file__).resolve().parent
runner = root.parents[2] / "tools/lean_within_memory.sh"
modules = [
    "Mettapedia.GSLT.Core.PresentationChange",
    "Mettapedia.GSLT.Parsing.GrammarPresentationTransport",
    "Mettapedia.GSLT.LanguageDef.ModuleAlgebra.PresentationTransport",
    "Mettapedia.GSLT.LanguageDef.ModuleAlgebra.PresentationTransportControls",
    "Mettapedia.GSLT.Parsing.EquationAuthoringPilot",
    "Mettapedia.GSLT.LanguageDef.ModuleAlgebra",
]
files = [root / Path(m.replace(".", "/")).with_suffix(".lean") for m in modules]

def hashes(paths):
    return {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(paths) if p.exists()}

closure = set(files)
todo = list(files)
while todo:
    source = todo.pop()
    for module in re.findall(r"^import\s+(Mettapedia\.[A-Za-z0-9_.]+)", source.read_text(), re.M):
        dep = root / Path(module.replace(".", "/")).with_suffix(".lean")
        if dep.exists() and dep not in closure:
            closure.add(dep)
            todo.append(dep)
before = hashes(closure)
other_oleans = [root / ".lake/build/lib/lean" / p.relative_to(root).with_suffix(".olean")
               for p in closure if p not in files]
compiled_before = hashes(other_oleans)
(evidence / "dependency-source-manifest.json").write_text(json.dumps(before, indent=2) + "\n")
(evidence / "dependency-olean-manifest.json").write_text(json.dumps(compiled_before, indent=2) + "\n")
results = []
for module, source in zip(modules, files):
    log = evidence / (module.rsplit(".", 1)[1] + "-strict.log")
    output = root / ".lake/build/lib/lean" / Path(module.replace(".", "/")).with_suffix(".olean")
    cmd = [str(runner), "file", str(source.relative_to(root)),
           "-DwarningAsError=true", "-o", str(output.relative_to(root))]
    with log.open("w") as out:
        result = subprocess.run(cmd, cwd=root, stdout=out, stderr=subprocess.STDOUT)
    results.append({"module": module, "exit_code": result.returncode, "log": log.name})
    print(module, result.returncode, flush=True)
    if result.returncode:
        print(log.read_text()[-5000:], flush=True)
        break
(evidence / "strict-results.json").write_text(json.dumps(results, indent=2) + "\n")
stable = before == hashes(closure)
compiled_stable = compiled_before == hashes(other_oleans)
(evidence / "source-stability.json").write_text(json.dumps({
    "local_modules": len(closure), "sources_stable": stable,
    "dependency_oleans_stable": compiled_stable,
}, indent=2) + "\n")
print("Source and compiled dependency stability:", stable, compiled_stable, flush=True)
if len(results) != len(modules) or any(r["exit_code"] for r in results) or not stable or not compiled_stable:
    raise SystemExit(1)
log = evidence / "axioms.log"
with log.open("w") as out:
    result = subprocess.run([str(runner), "file", str((evidence / "Audit.lean").relative_to(root)),
                             "-DwarningAsError=true"], cwd=root, stdout=out, stderr=subprocess.STDOUT)
print("Axiom audit:", result.returncode, flush=True)
for line in log.read_text().splitlines():
    if "SUMMARY" in line or "error:" in line:
        print(line, flush=True)
if result.returncode:
    raise SystemExit(result.returncode)
(evidence / "source-manifest.json").write_text(json.dumps(hashes(files), indent=2) + "\n")
print("Strict qualification and transitive axiom audit passed.", flush=True)
