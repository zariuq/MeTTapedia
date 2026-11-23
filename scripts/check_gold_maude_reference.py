#!/usr/bin/env python3
"""Retain native Maude 3.5.1 observations for the two gold source programs.

Ground reachability queries separate conditional reachability, ACU resources
and frozen contexts. This gate does not certify source lowering or the emitted
MeTTa program.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time


ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "metta/gslt/module/gold/Maude/examples"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--maude", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path,
                        help="new directory retaining source, queries and native output")
    args = parser.parse_args()
    binary = args.maude.resolve(strict=True)
    prelude = (binary.parent / "prelude.maude").resolve(strict=True)
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    for source in sorted(EXAMPLES.glob("*.maude")):
        shutil.copyfile(source, output / source.name)
    before = {str(p.relative_to(ROOT)): digest(p) for p in sorted(EXAMPLES.glob("*.maude"))}
    before[str(Path(__file__).resolve().relative_to(ROOT))] = digest(Path(__file__).resolve())
    before["native-binary"] = digest(binary)
    before["native-prelude"] = digest(prelude)
    record = {"passed": False, "compiler_correspondence_qualified": False,
              "source_sha256": before, "cases": [], "checks": []}

    def check(name, condition):
        record["checks"].append({"name": name, "passed": bool(condition)})
        if not condition:
            raise AssertionError(name)

    def run(name, source, commands):
        program = "set show timing off .\n" + commands + "\nquit\n"
        (output / (name + ".commands")).write_text(program)
        started = time.monotonic()
        result = subprocess.run(
            [str(binary), "-no-prelude", "-no-banner", "-no-ansi-color", "-no-wrap",
             str(prelude), str(output / (source + ".maude"))],
            input=program, cwd=output, env={**os.environ, "MAUDE_LIB": str(binary.parent)},
            capture_output=True, text=True, timeout=60)
        elapsed = time.monotonic() - started
        (output / (name + ".stdout")).write_text(result.stdout)
        (output / (name + ".stderr")).write_text(result.stderr)
        record["cases"].append({"name": name, "exit": result.returncode,
                                "elapsed_seconds": elapsed,
                                "commands_sha256": digest(output / (name + ".commands")),
                                "stdout_sha256": digest(output / (name + ".stdout")),
                                "stderr_sha256": digest(output / (name + ".stderr"))})
        check(name + ": exit and diagnostics", result.returncode == 0 and not result.stderr)
        return result.stdout

    def search(name, source, module, start, arrow, target, succeeds):
        result = run(name, source, f"search in {module} : {start} {arrow} {target} .")
        found = bool(re.search(r"^Solution [0-9]+", result, re.M))
        finished = "No more solutions." in result or "No solution." in result
        check(name + ": completed reachability", finished and found == succeeds)

    try:
        version = subprocess.run([str(binary), "--version"], capture_output=True,
                                 text=True, timeout=20)
        record["version"] = version.stdout.strip()
        check("pinned Maude 3.5.1", version.returncode == 0 and not version.stderr
              and version.stdout.strip() == "3.5.1")

        resource = ("resource_protocol", "GOLD-RESOURCE-PROTOCOL")
        permit = "permission(alpha, open)"
        initial = permit + " request(alpha) token"
        search("allocate", *resource, initial, "=>1", permit + " running(alpha)", True)
        search("missing-resource", *resource, permit + " request(alpha)", "=>+", "S:State", False)
        search("failed-guard", *resource, "permission(alpha, closed) request(alpha) token",
               "=>+", "S:State", False)
        search("wrong-job", *resource, permit + " request(beta) token", "=>+", "S:State", False)
        search("equal-resource-occurrences", *resource,
               permit + " request(alpha) request(alpha) token token", "=>*",
               permit + " running(alpha) running(alpha)", True)
        search("resource-exhaustion", *resource,
               permit + " request(alpha) request(alpha) token", "=>*",
               permit + " running(alpha) running(alpha)", False)
        search("permitted-nested-context", *resource, "pool(" + initial + ")", "=>1",
               "pool(" + permit + " running(alpha))", True)
        search("frozen-nested-context", *resource, "sealed(" + initial + ")", "=>+", "S:State", False)
        whole = run("uninterrupted", resource[0],
                    f"rewrite [2] in {resource[1]} : {initial} .")
        resumed = run("resumed", resource[0],
                      f"rewrite [1] in {resource[1]} : {initial} .\ncontinue 1 .")
        whole_results = re.findall(r"^result State: (.+)$", whole, re.M)
        resumed_results = re.findall(r"^result State: (.+)$", resumed, re.M)
        check("native rewrite continuation retains the same final state",
              len(whole_results) == 1 and len(resumed_results) == 2
              and whole_results[-1] == resumed_results[-1])

        workflow = ("nested_workflow", "GOLD-NESTED-WORKFLOW")
        search("condition-needs-two-steps", *workflow, "pending", "=>1", "approved", False)
        search("condition-reachable", *workflow, "pending", "=>+", "approved", True)
        source = "group(permit(alpha, pending) task(alpha))"
        target = "group(permit(alpha, pending) done(alpha))"
        search("conditional-workflow", *workflow, source, "=>1", target, True)
        search("nested-equivalent-presentation", *workflow,
               "group(empty group(task(alpha) permit(alpha, pending)))", "=>1", target, True)
        search("failed-rewrite-condition", *workflow,
               "group(permit(alpha, rejected) task(alpha))", "=>+", "W:Workflow", False)
        search("condition-input-stays-frozen", *workflow,
               "permit(alpha, pending)", "=>+", "W:Workflow", False)
        search("frozen-workflow", *workflow, "sealed(" + source + ")", "=>+", "W:Workflow", False)
        equations = run("equations-and-constructor-control", workflow[0],
                        f"reduce in {workflow[1]} : sealed(group(empty)) == sealed(empty) .\n"
                        f"reduce in {workflow[1]} : group(task(alpha)) == task(alpha) .")
        check("equations still act under frozen contexts; wrappers remain distinct",
              re.findall(r"^result Bool: (.+)$", equations, re.M) == ["true", "false"])
        check("binary and source unchanged",
              all(digest(binary if name == "native-binary" else
                         prelude if name == "native-prelude" else ROOT / name) == value
                  for name, value in before.items()))
        record["passed"] = True
    except Exception as error:
        record["error"] = str(error)
        raise
    finally:
        (output / "result.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({"passed": True, "cases": len(record["cases"]),
                      "checks": len(record["checks"]),
                      "record_sha256": digest(output / "result.json")}))


if __name__ == "__main__":
    main()
