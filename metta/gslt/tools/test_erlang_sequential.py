#!/usr/bin/env python3
"""Compare the independent sequential IR machine with Erlang/OTP.

This gate qualifies finite reference comparisons, exact reference-machine
resumption and the included source-model lemmas. It does not qualify source
lowering, the shared emitted backend, or the complete E0 language.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--erlang-bin", type=Path, required=True)
    parser.add_argument("--cetta", type=Path)
    parser.add_argument("--petta-runner", type=Path)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[3]
    lean, gslt = repo / "lean/mettapedia", repo / "metta/gslt"
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    erlang = args.erlang_bin.resolve(strict=True)
    cetta = (args.cetta or repo.parent / "hyperon/cetta-prime-2.0-draft-20260910/cetta").resolve()
    petta = (args.petta_runner or repo.parent / "hyperon/PeTTa/run.sh").resolve()
    version = erlang.parent / "lib/erlang/releases/29/OTP_VERSION"
    if version.read_text().strip() != "29.1.2":
        raise RuntimeError("expected the pinned Erlang/OTP 29.1.2 reference")
    targets = ["Mettapedia.Languages.Erlang.SequentialExamples",
               "Mettapedia.Languages.Erlang.PatternProperties", "Mettapedia.Languages.Erlang.GuardProperties"]
    with (output / "build.log").open("w") as log:
        subprocess.run(["lake", "--wfail", "build", *targets], cwd=lean, stdout=log,
                       stderr=subprocess.STDOUT, check=True)
    generator = gslt / "tools/generate_erlang_sequential_controls.lean"
    sources = gslt / "module/gold/Erlang/examples"
    ordinary = [sources / "core_sequential.erl", sources / "sequential_operations.erl"]
    core = sources / "core_multiple_values.core"
    inputs = {Path(__file__).resolve(), generator, *ordinary, core, version, erlang / "erl", erlang / "erlc", cetta, petta,
              lean / "lean-toolchain", lean / "lakefile.lean", lean / "lake-manifest.json"}
    inputs.update(erlang.parent.glob("lib/erlang/erts-*/bin/beam.smp"))
    inputs.update((petta.parent / "src").rglob("*.pl"))
    for target in targets:
        relative = Path(*target.split("."))
        setup = lean / ".lake/build/ir" / relative.with_suffix(".setup.json")
        inputs.update([setup, lean / relative.with_suffix(".lean"),
                       lean / ".lake/build/lib/lean" / relative.with_suffix(".olean")])
        for dependency, groups in json.loads(setup.read_text())["importArts"].items():
            if dependency.startswith("Mettapedia."):
                inputs.add(lean / Path(*dependency.split(".")).with_suffix(".lean"))
            inputs.update(Path(path) for group in groups for path in group)
    pins = {str(path): sha(path) for path in inputs}

    def save_pins():
        (output / "input-pins.json").write_text(json.dumps(pins, indent=2) + "\n")

    save_pins()
    with (output / "generation.log").open("w") as log:
        subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", "--run", generator, output],
                       cwd=lean, stdout=log, stderr=subprocess.STDOUT, check=True)
    model = json.loads((output / "model.json").read_text())
    cases = model["cases"]
    if len(cases) != 16 or not all(case["resumed"] for case in cases):
        raise RuntimeError("a sequential result or exact resumption check failed")
    native = output / "erlang"
    native.mkdir()
    for name, options in [("compile-beam", []), ("compile-core", ["+to_core"])]:
        with (native / (name + ".log")).open("w") as log:
            subprocess.run([str(erlang / "erlc"), "-Werror", *options, "-o", native, *ordinary],
                           stdout=log, stderr=subprocess.STDOUT, check=True)
    # OTP 29 core_lint returns a per-file warning bucket even when it is
    # empty; warnings_as_errors checks the raw buckets before flattening.
    # Require zero actual warnings explicitly for this Core-input case.
    core_compile = '''
case compile:file(os:getenv("ERLANG_CORE_SOURCE"), [from_core,binary,return_warnings,return_errors]) of
  {ok,Module,Beam,[]} ->
    ok = file:write_file(filename:join(os:getenv("ERLANG_CORE_OUTPUT"), atom_to_list(Module) ++ ".beam"), Beam),
    io:format("CoreCompilation ~w warnings=0~n", [Module]), halt();
  Failure -> io:format("CoreCompilationFailure ~w~n", [Failure]), halt(1)
end.
'''
    with (native / "compile-multiple-values.log").open("w") as log:
        subprocess.run([str(erlang / "erl"), "-noshell", "-eval", core_compile], stdout=log,
                       stderr=subprocess.STDOUT, check=True,
                       env=dict(os.environ, ERLANG_CORE_SOURCE=str(core), ERLANG_CORE_OUTPUT=str(native)))
    expression = '''
{ok,Cases} = file:consult(os:getenv("ERLANG_EXPECTED_TERMS")),
lists:foreach(fun({Name,Expected}) ->
  Observed = try {value,sequential_operations:run_case(Name)}
    catch error:Reason -> {fault,Reason}; Class:Reason -> {raised,Class,Reason} end,
  io:format("ErlangSequentialControl ~s ~w~n", [atom_to_list(Name), Observed =:= Expected]),
  io:format("Observation ~w~n", [{Name,Observed}])
end, Cases), halt().
'''
    started = time.monotonic()
    with (native / "reference.out").open("w") as out, (native / "reference.err").open("w") as err:
        native_result = subprocess.run([str(erlang / "erl"), "-noshell", "-pa", native, "-eval", expression],
                                stdout=out, stderr=err,
                                env=dict(os.environ, ERLANG_EXPECTED_TERMS=str(output / "expected.terms")))
    rows = [line for line in (native / "reference.out").read_text().splitlines()
            if line.startswith("ErlangSequentialControl ")]
    parsed = [re.fullmatch(r"ErlangSequentialControl ([a-z-]+) (true|false)", row) for row in rows]
    native_passed = (native_result.returncode == 0 and not (native / "reference.err").read_bytes()
                     and len(parsed) == len(cases) and all(parsed)
                     and [match[1] for match in parsed] == [case["name"] for case in cases]
                     and all(match[2] == "true" for match in parsed))
    scalar = output / "scalar.metta"
    scalar.write_text("!(println! (ErlangScalarProbe (+ " + str(2**100) + " 5) (* " + str(2**100) +
                      " 3) (< " + str(2**100) + " " + str(2**100 + 1) + ")))\n")
    scalar_expected = f"(ErlangScalarProbe {2**100 + 5} {2**100 * 3} true)\ntrue\n"
    scalar_results = []
    for name, command in [("cetta", [str(cetta), "--lang", "petta", "--quiet", str(scalar)]),
                          ("petta", ["bash", str(petta), "--silent", str(scalar)])]:
        with (output / ("scalar-" + name + ".out")).open("w") as out, (output / ("scalar-" + name + ".err")).open("w") as err:
            result = subprocess.run(command, stdout=out, stderr=err)
        passed = (result.returncode == 0 and (output / ("scalar-" + name + ".out")).read_text() == scalar_expected
                  and not (output / ("scalar-" + name + ".err")).read_bytes())
        scalar_results.append({"engine": name, "passed": passed, "checks": 3,
                               "scope": "raw exact arithmetic samples, not emitted sequential IR"})
    for path in [output / "expected.terms", output / "model.json", scalar, *native.iterdir()]:
        pins[str(path)] = sha(path)
    save_pins()
    changed = [path for path, digest in pins.items() if not Path(path).is_file() or sha(path) != digest]
    qualification = {"native_comparisons": len(cases), "model_exact_resumptions": len(cases),
                     "native_passed": native_passed, "native_exit_code": native_result.returncode,
                     "native_seconds": time.monotonic() - started, "otp_version": version.read_text().strip(),
                     "inputs_current": not changed, "changed_inputs": changed,
                     "scalar_results": scalar_results,
                     "all_passed": native_passed and not changed and all(row["passed"] for row in scalar_results),
                     "source_lowering_qualified": False, "emitted_backend_qualified": False,
                     "full_primitive_profile_qualified": False, "full_E0_qualified": False}
    (output / "qualification.json").write_text(json.dumps(qualification, indent=2) + "\n")
    print(json.dumps(qualification), flush=True)
    if not qualification["all_passed"]:
        raise RuntimeError("the sequential component comparison failed")


if __name__ == "__main__":
    main()
