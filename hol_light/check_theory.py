#!/usr/bin/env python3
"""Produce HOL primitive derivations and replay them in CeTTa.

This is an untrusted orchestration tool, not a theorem checker. The existing
ProofTrace and HOLR adapters produce proof requests. CeTTa independently checks
every inference and each source sequent, including the exported roots.
"""

import argparse
import hashlib
import html
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import zipfile


def digest(path):
    result = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            result.update(block)
    return result.hexdigest()


def main():
    mettapedia = Path(__file__).resolve().parents[1]
    workspace = mettapedia.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("theory", type=Path, nargs="+")
    parser.add_argument("--export-from", type=Path, action="append", default=[],
                        help="export roots from these input modules; all inputs remain source-pinned")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--cetta", type=Path, default=workspace / "hyperon/CeTTa/cetta")
    parser.add_argument("--source", type=Path,
                        default=workspace / "repos/itp-curriculum-sources/hol_light")
    parser.add_argument("--source-tools", type=Path,
                        default=workspace / "hyperon/cetta-prime-weights-parallel-20261001/tools")
    parser.add_argument("--stream-archive", type=Path,
                        default=workspace / "GPT-Pro_Responses/MeTTaKernel/hol-native-kernel-20261015.zip")
    parser.add_argument("--library-through", default="meson.ml")
    parser.add_argument("--reuse-export", action="store_true",
                        help="reuse a source export only after verifying its helper, source and artifact hashes")
    args = parser.parse_args()
    for key, value in vars(args).items():
        if isinstance(value, Path):
            setattr(args, key, value.resolve())
    args.theory = [path.resolve() for path in args.theory]
    export_paths = {path.resolve() for path in args.export_from} or set(args.theory)
    if not export_paths.issubset(set(args.theory)):
        raise ValueError("export modules must also be supplied as theory inputs")
    args.output.mkdir(parents=True, exist_ok=True)
    texts = [(path, path.read_text()) for path in args.theory]
    names = [name for path, source_text in texts if path in export_paths
             for name in re.findall(r"^let (TC_[A-Z0-9_]+) = prove\s*$", source_text, re.M)]
    if not names or len(names) != len(set(names)):
        raise ValueError("theory needs distinct named TC_ proof roots")
    if any(re.search(r"\b(new_axiom|mk_thm|CHEAT_TAC)\b", text) for _, text in texts):
        raise ValueError("theory contains a forbidden proof escape")
    helper = mettapedia / "MettaKernel/Curriculum/HOL/HOLLightProofClosure.ml"
    adapter = mettapedia / "MettaKernel/Curriculum/HOL/hol_closure_to_holr.py"
    exporter = args.source_tools / "hol_light_proof_export_v1.py"
    pins = {str(path): digest(path) for path in
            [*args.theory, args.cetta, helper, adapter, exporter, args.stream_archive,
             Path(__file__).resolve()]}
    expected_archive = "b0d13cdf2791893c0b80d8ad04c3077ceed995d51c51f40caf5a7795cf064ac5"
    if digest(args.stream_archive) != expected_archive:
        raise ValueError("HOLR writer archive differs from the qualified source")
    stream_tools = args.output / "stream-tools"
    stream_tools.mkdir(exist_ok=True)
    with zipfile.ZipFile(args.stream_archive) as archive:
        (stream_tools / "holr.py").write_bytes(archive.read("hol-native-kernel/tools/holr.py"))

    stages = []

    def run(label, command, code=0, diagnostic=None):
        result = subprocess.run(list(map(str, command)), text=True, capture_output=True,
                                env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
        (args.output / (label + ".stdout")).write_text(result.stdout)
        (args.output / (label + ".stderr")).write_text(result.stderr)
        stages.append({"name": label, "exit_code": result.returncode})
        if result.returncode != code:
            raise RuntimeError(f"{label}: expected exit {code}, got {result.returncode}; inspect its log")
        if diagnostic and diagnostic not in result.stdout + result.stderr:
            raise RuntimeError(f"{label}: missing refusal diagnostic {diagnostic!r}")
        return result

    source_helper = args.output / "source-helper.ml"
    entries = []
    for path, text in texts:
        for match in re.finditer(r"^let ([A-Za-z_][A-Za-z0-9_]*) = (prove|new_definition|new_recursive_definition)\b", text, re.M):
            name, construction = match.groups()
            if construction == "prove" and path not in export_paths:
                continue
            kind = "Theorem" if construction == "prove" else "Definition"
            entries.append((path.name, kind, name))
    display = args.output / "statements.jsonl"
    display_code = (
        "let tc_display_channel = open_out " + json.dumps(str(display)) + ";;\n" +
        "List.iter (fun (file,kind,name,theorem) -> Printf.fprintf tc_display_channel " +
        '"{\\\"module\\\":%s,\\\"kind\\\":%s,\\\"name\\\":%s,\\\"statement\\\":%s}\\n" ' +
        "(hol_json_string file) (hol_json_string kind) (hol_json_string name) " +
        "(hol_json_string (string_of_thm theorem))) [\n" +
        ";\n".join("(" + ",".join(map(json.dumps, [file, kind, name])) + "," + name + ")"
                  for file, kind, name in entries) + "];;\nclose_out tc_display_channel;;\n")
    source_helper.write_text(
        "loadt " + json.dumps(str(helper)) + ";;\n" +
        # The helper digest now binds the actual authored sources, rather
        # than only paths which an untrusted producer could read later.
        "\n".join(text for _, text in texts) + "\n" +
        "List.iter (fun (n,t) -> if hyp t <> [] then failwith n) [\n" +
        ";\n".join("(" + json.dumps(name) + "," + name + ")" for name in names) + "];;\n" +
        display_code
    )
    source_output = args.output / "source"
    command = [sys.executable, exporter, "--source", args.source,
               "--closure-helper", source_helper, "--output", source_output,
               "--library-through", args.library_through]
    for name in names:
        command += ["--theorem", name]
    if args.reuse_export:
        receipt = json.loads((source_output / "export.json").read_text())
        source_pins = receipt["source"]
        if (receipt.get("library_through") != args.library_through or
                source_pins["closure_helper_sha256"] != digest(source_helper) or
                source_pins["export_adapter_sha256"] != digest(exporter)):
            raise RuntimeError("cached export does not match the requested source/helper/producer")
        for name, pin in source_pins["tracked_sources"].items():
            if digest(args.source / name) != pin:
                raise RuntimeError("cached HOL library source changed: " + name)
        for name, pin in receipt["artifacts"].items():
            if Path(name).name != name or digest(source_output / name) != pin:
                raise RuntimeError("cached source artifact changed: " + name)
        exported = receipt["accounting"]
        stages.append({"name": "export-hashes-verified", "exit_code": 0})
    else:
        exported = json.loads(run("export", command).stdout)
    roots = exported["roots"]
    if [root["name"] for root in roots] != names:
        raise RuntimeError("exported root inventory differs from source")
    prefix = source_output / "closure"
    root_ids = {root["id"] for root in roots}
    seen_roots = set()
    with prefix.with_suffix(".nodes.jsonl").open() as source:
        for line in source:
            node = json.loads(line)
            if node["id"] in root_ids:
                if node["theorem"]["hypotheses"]:
                    raise RuntimeError("a root has undischarged hypotheses")
                seen_roots.add(node["id"])
    if seen_roots != root_ids:
        raise RuntimeError("a requested proof root is absent")
    wire = args.output / "theory.holr"
    common = [sys.executable, adapter, "--stream-tools", stream_tools,
              "--source-tools", args.source_tools, "--prefix", prefix]
    generated = json.loads(run("encode", [*common, "--output", wire,
                                          "--controls-dir", args.output]).stdout)
    native = run("replay", [args.cetta, "--lang", "hol-light", "--profile", "standard", wire])
    lines = native.stdout.splitlines()
    expected_tail = f"(hol:accepted {generated['wire_records']} {len(names)})"
    if (native.stderr.strip() or len(lines) != len(names) + 1 or lines[-1] != expected_tail
            or not all(line.startswith("(thm () ") for line in lines[:-1])):
        raise RuntimeError("replay did not deliver exactly the closed source roots")
    # Exercise the proof handles through ordinary MeTTa, not only the HOLR CLI.
    # This is a consumer of checked proofs, not a replacement inference engine.
    selected = [names[0], names[-1]]
    consumer = args.output / "consume.metta"
    consumer.write_text(
        "!(import! &self holkernel)\n" +
        "!(let* (($k (hol:kernel standard))\n" +
        "        ($_ (hol:replay $k " + json.dumps(str(wire)) + ")))\n" +
        "    (" + " ".join("(hol:sequent (hol:theorem $k " + json.dumps(name) + "))"
                           for name in selected) + "))\n")
    consumed = run("metta-consumer", [args.cetta, "--lang", "he", "--quiet", consumer])
    expected_consumer = "[(" + lines[0] + " " + lines[-2] + ")]"
    if consumed.stderr.strip() or consumed.stdout.strip() != expected_consumer:
        raise RuntimeError("MeTTa did not recover the same checked theorem handles")
    for label, reason in [("changed-root", "expectation failed"), ("extra-axiom", "axiom policy")]:
        path = args.output / (label + ".holr")
        if generated["controls"].get(label) != str(path):
            raise RuntimeError("control artifact inventory mismatch")
        run(label, [args.cetta, "--lang", "hol-light", "--profile", "standard", path],
            code=1, diagnostic=reason)
    truncated = args.output / "truncated.holr"
    truncated.write_bytes(wire.read_bytes()[:-1])
    run("truncated", [args.cetta, "--lang", "hol-light", "--profile", "standard", truncated],
        code=2, diagnostic="truncated")
    if any(digest(Path(path)) != pin for path, pin in pins.items()):
        raise RuntimeError("a theory, producer, or checker changed during qualification")
    statements = [json.loads(row) for row in display.read_text().splitlines()]
    if [(row["module"], row["kind"], row["name"]) for row in statements] != entries:
        raise RuntimeError("readable statement inventory differs from authored definitions/theorems")
    (args.output / "theory.pretty.txt").write_text("\n\n".join(
        f"{row['module']} — {row['kind']} {row['name']}\n{row['statement']}" for row in statements) + "\n")
    cards = "\n".join(
        '<details open><summary>' + html.escape(row['kind'] + ' ' + row['name']) +
        ' <small>' + html.escape(row['module']) + '</small></summary><pre>' +
        html.escape(row['statement']) + '</pre></details>' for row in statements)
    (args.output / "theory.html").write_text(
        '<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width">'
        '<title>Transform calculus in HOL Light</title><style>'
        'body{max-width:1100px;margin:3rem auto;padding:0 1.5rem;font:17px/1.55 system-ui;color:#18232d;background:#fafbf8}'
        'h1{font-size:2rem}input{font:inherit;padding:.6rem;width:95%;margin:1rem 0}details{border-top:1px solid #ccd6ce;padding:1rem 0}'
        'summary{cursor:pointer;font-weight:600}small{font-weight:400;color:#596b62;margin-left:1rem}'
        'pre{white-space:pre-wrap;overflow-wrap:anywhere;font:14px/1.6 monospace;background:white;padding:1rem;border-radius:6px}'
        '</style><h1>Transform calculus in HOL Light</h1>'
        '<p>Definitions and theorems printed by HOL Light. The exported theorem derivations were replayed by CeTTa. '
        'This view is for reading; the HOLR certificate carries the proof evidence.</p>'
        '<p>Notation: <code>!</code> for all; <code>?</code> exists; <code>\\</code> lambda; '
        '<code>/\\</code> and; <code>\\/</code> or; <code>==&gt;</code> implies; <code>&lt;=&gt;</code> iff.</p>'
        '<input id="filter" aria-label="Filter declarations" placeholder="Filter by name, module, or formula…">' + cards +
        '<script>document.getElementById("filter").addEventListener("input",function(){const q=this.value.toLowerCase();'
        'document.querySelectorAll("details").forEach(d=>d.hidden=!d.textContent.toLowerCase().includes(q));});</script></html>')
    report = {"qualified": True, "roots": names, "source_nodes": exported["nodes"],
              "source_axiom_nodes": exported["axiom_nodes"],
              "records": generated["wire_records"], "bytes": wire.stat().st_size,
              "holr_sha256": digest(wire), "input_sha256": pins, "stages": stages,
              "new_nonstandard_axioms": 0, "negative_controls": 3,
              "source_export_reused": args.reuse_export,
              "metta_proof_handle_consumer": True,
              "lean_correspondence_established": False,
              "native_implementation_refinement_established": False}
    (args.output / "qualification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: report[key] for key in
                     ["qualified", "roots", "source_nodes", "records", "bytes", "negative_controls"]}))


if __name__ == "__main__":
    main()
