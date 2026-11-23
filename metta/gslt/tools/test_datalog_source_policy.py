#!/usr/bin/env python3
"""Compare authored Datalog word selection and scalar boundaries with Souffle."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

from packed_source_reader import Commands, LEAN, REPO, build_native_reader, parse_direct_source
from source_io import SOURCE_BINARY, source_command


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--host", type=Path, required=True)
    parser.add_argument("--souffle", type=Path, required=True)
    parser.add_argument("--work", type=Path, required=True)
    args = parser.parse_args()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    commands = Commands(work / "commands")
    commands.run("proof-build", ["lake", "--wfail", "build", "sourceSyntax",
        "Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxQualification",
        "Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogSourcePolicy",
        "Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogFrontend"])
    source_module = REPO / "metta/gslt/module/gold/SouffleDatalog/Syntax.module"
    prefix = source_command(source_module)
    lean_prefix = ["lake", "env", "lean", "-DwarningAsError=true", "--run"]
    grammar = work / "grammar"
    commands.run("export", [*prefix, "export", grammar])
    native, sources = build_native_reader(args.host, work / "native", commands, selections=True)
    # Read the policy through its authored port, using the existing Lean decoder.
    words_driver = work / "Words.lean"
    words_driver.write_text(
        "import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogSourcePolicy\n"
        "import Lean.Data.Json.Printer\n"
        "def main : IO Unit := IO.println (Lean.toJson "
        "Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePolicy.reservedWords).compress\n")
    words = json.loads(commands.run("words", lean_prefix + [words_driver]).read_text())
    tracked = [SOURCE_BINARY, source_module, native, args.souffle.resolve(), *sources, Path(__file__)]
    digest = lambda path: hashlib.sha256(Path(path).read_bytes()).hexdigest()
    before = {str(path): digest(path) for path in tracked}
    results = []
    for ordinal, word in enumerate(words):
        for suffix, name, accepted in (("reserved", word, False), ("extended", word + "X", True)):
            label = f"{ordinal}-{suffix}"
            source = work / (label + ".dl")
            source.write_text(f".decl {name}(x:number)\n{name}(1).\n.output {name}\n")
            status = parse_direct_source(native, grammar, source, work / (label + ".cnf"), commands,
                label, selected=True, result_limit=16)
            reference_output = work / (label + "-reference")
            reference_output.mkdir()
            reference = subprocess.run([str(args.souffle.resolve()), "-D", str(reference_output), str(source)],
                                       capture_output=True, text=True)
            (work / (label + ".reference.log")).write_text(reference.stdout + reference.stderr)
            if status["outcome"] != 0 or (status["semanticResults"] > 0) != accepted or (reference.returncode == 0) != accepted:
                raise RuntimeError(label + ": authored word policy differs from the reference")
            results.append(dict(name=name, accepted=accepted))
    for label, payload, accepted, reference_expected in (
        ("keyword-symbol", b'.decl T(x:symbol)\nT("count").\n.output T\n', True, True),
        ("nul-symbol", b'.decl T(x:symbol)\nT("a\x00b").\n.output T\n', False, False),
        # The reference tolerates this byte between tokens. It is neither
        # identifier data nor whitespace in the declared source profile.
        ("nul-between-tokens", b'.decl N\x00(x:number)\n', False, True)):
        source = work / (label + ".dl")
        source.write_bytes(payload)
        status = parse_direct_source(native, grammar, source, work / (label + ".cnf"), commands,
            label, selected=True, result_limit=16)
        reference_output = work / (label + "-reference")
        reference_output.mkdir()
        reference = subprocess.run([str(args.souffle.resolve()), "-D", str(reference_output), str(source)],
                                   capture_output=True, text=True)
        (work / (label + ".reference.log")).write_text(reference.stdout + reference.stderr)
        if status["outcome"] != 0 or (status["semanticResults"] > 0) != accepted or (reference.returncode == 0) != reference_expected:
            raise RuntimeError(label + ": scalar boundary differs from the reference")
        results.append(dict(case=label, accepted=accepted, reference_accepted=reference_expected,
                            outside_declared_profile=accepted != reference_expected))
    # Propose a raw grammar result which the declared word policy rejects.
    source = work / "0-reserved.dl"
    status = parse_direct_source(native, grammar, source, work / "raw.cnf", commands, "raw", result_limit=16)
    packets = commands.work.joinpath("raw.out").read_text().splitlines()[1:]
    if status["outcome"] != 0 or len(packets) != 1:
        raise RuntimeError("expected one raw grammar packet for the policy discriminator")
    packet = work / "raw.packet"
    packet.write_text(packets[0] + "\n")
    rejected = subprocess.run([*map(str, prefix), "read", str(source), str(packet), str(work / "raw.core")],
                              cwd=LEAN, capture_output=True, text=True)
    (work / "raw-replay.log").write_text(rejected.stdout + rejected.stderr)
    if rejected.returncode == 0 or "violates the declared selection policy" not in rejected.stdout + rejected.stderr:
        raise RuntimeError("raw grammar packet bypassed independent declared-policy replay")
    frontend = work / "Frontend.lean"
    frontend.write_text(
        "import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogFrontend\n"
        "set_option maxRecDepth 32768\n"
        "open Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog\n"
        "def main (args : List String) : IO Unit := do\n"
        "  let [sourcePath, packetPath] := args | throw (IO.userError \"expected source and packet\")\n"
        "  let text ← IO.FS.readFile sourcePath\n"
        "  let .ok [packet] := Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics.readSource (← IO.FS.readFile packetPath)\n"
        "    | throw (IO.userError \"malformed packet\")\n"
        "  match Frontend.read text packet with\n"
        "  | .ok _ => throw (IO.userError \"reserved source accepted\")\n"
        "  | .error reason =>\n"
        "    unless reason == \"source packet violates checked grammar or declared selection\" do\n"
        "      throw (IO.userError reason)\n"
        "    IO.println \"frontend policy refusal checked\"\n")
    commands.run("frontend-policy", lean_prefix + [frontend, source, packet])
    if any(digest(path) != value for path, value in before.items()):
        raise RuntimeError("source-policy qualification inputs changed")
    record = dict(controls=results, reserved_words=len(words), checked_policy_bypass_refused=True,
                  frontend_policy_bypass_refused=True,
                  inputs_stable=True, inputs=before)
    (work / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({"controls": len(results), "reserved_words": len(words), "policy_bypass_refused": True}))


if __name__ == "__main__":
    main()
