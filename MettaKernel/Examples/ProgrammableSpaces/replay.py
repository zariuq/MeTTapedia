#!/usr/bin/env python3
"""Replay calibration fixtures through an explicitly supplied CeTTa binary.

Classification: untrusted source adapter. The existing CeTTa Gate launches the
programs, and its existing MM2 reader parses the exact receipt syntax. Expected
observations are authored separately in expectations.json. Passing these finite
controls is runtime evidence, not a compiled-code correctness proof.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
SCHEMA = "programmable-space-native-calibration-v1"
KINDS = {"mm2": 13, "mm2-pending": 1, "demand": 1, "ordinary": 4}
RUNTIME_ADAPTERS = (
    "scripts/test_prime_native_control.py",
    "scripts/test_prime_native_resources.py",
    "tools/mm2_to_metta.py",
    "src/native_space_agenda.c",
)


class CheckFailure(Exception):
    def __init__(self, condition, details=None):
        super().__init__(condition)
        self.condition = condition
        self.details = details


def require(condition, message, details=None):
    if not condition:
        raise CheckFailure(message, details)


def identity(path, label):
    data = path.read_bytes()
    stat = path.stat()
    return {"path": label, "sha256": sha256(data).hexdigest(),
            "bytes": len(data), "mtime_ns": stat.st_mtime_ns}


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None,
            "runtime adapter cannot be loaded", {"name": name})
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def runtime_sources(root):
    result = {root / item for item in RUNTIME_ADAPTERS}
    for directory in ("src", "include"):
        result.update(path for path in (root / directory).rglob("*")
                      if path.is_file() and path.suffix in (".c", ".h", ".inc"))
    return sorted(result)


def named_fields(items, expected, where):
    require(all(isinstance(item, list) and len(item) == 2
                and isinstance(item[0], str) for item in items),
            where + ": malformed fields", items)
    fields = dict(items)
    require(len(fields) == len(items) and set(fields) == set(expected),
            where + ": missing, duplicated or extra fields", items)
    return fields


def one_form(reader, text):
    forms = reader.parse(text)
    require(len(forms) == 1, "expected exactly one source atom", text)
    return forms[0]


def exact_forms(reader, receipt):
    forms = []
    for line in receipt["stdout"].splitlines():
        require(line.startswith("[") and line.endswith("]"),
                receipt["name"] + ": unexpected stdout line", line)
        forms.append(one_form(reader, line[1:-1]))
    return forms


def check_transactions(reader, case, observation):
    records = observation["values"]
    sources = [one_form(reader, item) for item in case["receipt_sources"]]
    counts = case["environment_counts"]
    require(isinstance(records, list) and len(records) == len(sources) == len(counts),
            case["name"] + ": transaction count", records)
    checked = []
    for index, (record, source, count) in enumerate(zip(records, sources, counts)):
        where = case["name"] + ": transaction " + str(index)
        require(isinstance(record, list) and len(record) >= 2
                and record[:2] == ["Committed", ["quote", source]],
                where + ": retained original directive", record)
        fields = named_fields(record[2:],
                              ("environments", "dependencies", "retries", "store", "order"),
                              where)
        require(fields["environments"] == str(count)
                and fields["retries"] == "0"
                and fields["store"] == "set"
                and fields["order"] == "compact-byte",
                where + ": transaction fields", fields)
        dependencies = fields["dependencies"]
        require(isinstance(dependencies, list) and len(dependencies) == 2
                and dependencies[0] == "quote"
                and isinstance(dependencies[1], list)
                and len(dependencies[1]) == count,
                where + ": retained dependency rows", dependencies)
        require(isinstance(source, list) and len(source) == 4
                and source[0] == "exec" and isinstance(source[2], list)
                and source[2] and source[2][0] in (",", "I"),
                where + ": expected native MM2 input", source)
        if source[2][0] == "I":
            require(all(isinstance(factor, list) and len(factor) == 2
                        and factor[0] == "BTM" for factor in source[2][1:]),
                    where + ": unary BTM factors", source)
        premise_count = len(source[2]) - 1
        for row in dependencies[1]:
            require(isinstance(row, list) and len(row) == premise_count,
                    where + ": every ordered premise is retained", row)
            for entry in row:
                require(isinstance(entry, list) and len(entry) == 4
                        and entry[0] == "read" and isinstance(entry[2], str)
                        and entry[2].isdigit(),
                        where + ": physical dependency occurrence", entry)
        expected_positions = case.get("dependency_positions", {}).get(str(index))
        if expected_positions is not None:
            positions = [[int(entry[2]) for entry in row] for row in dependencies[1]]
            require(positions == expected_positions,
                    where + ": physical path positions",
                    {"expected": expected_positions, "actual": positions})
        expected_rows = case.get("dependency_rows", {}).get(str(index))
        if expected_rows is not None:
            expected_rows = [[one_form(reader, entry) for entry in row] for row in expected_rows]
            require(dependencies[1] == expected_rows, where + ": exact dependency entries",
                    {"expected": expected_rows, "actual": dependencies[1]})
        checked.append(fields)
    agenda = observation["agenda"]
    require(isinstance(agenda, list) and agenda and agenda[0] == "SpaceAgenda",
            case["name"] + ": retained agenda", agenda)
    fields = named_fields(agenda[1:],
                          ("phase", "selected", "commits", "retries",
                           "obligation", "waiting", "observation"),
                          case["name"] + ": agenda")
    expected = {"phase": "Select", "selected": ["quote", []],
                "commits": str(len(records)), "retries": "0", "obligation": "Ready",
                "waiting": ["quote", []], "observation": "committed-trace"}
    if case["kind"] == "mm2-pending":
        require(not records, case["name"] + ": unsupported syntax cannot publish")
        expected.update(phase="Wait",
                        selected=["quote", one_form(reader, case["pending_source"])],
                        obligation="UninterpretedExec")
    require(fields == expected, case["name"] + ": agenda completion boundary",
            {"expected": expected, "actual": fields})
    return checked


def check_pause_ownership(gate_module, reader, case, forms, final_observation):
    expected = case["pause_ownership"]
    require(len(forms) >= 2 and isinstance(forms[-2], list)
            and forms[-2] and forms[-2][0] == "PauseOwnership",
            case["name"] + ": ownership phase marker", forms)
    phases = named_fields(forms[-2][1:], ("live", "paused", "resumed"),
                          case["name"] + ": ownership phase")
    paused = phases["paused"]
    require(isinstance(paused, list) and len(paused) >= 2 and paused[0] == "Observation"
            and paused[1] == [], case["name"] + ": no paused publication", paused)
    fields = named_fields(paused[2:],
                          ("satisfied", "closed", "residual", "work", "status", "agenda"),
                          case["name"] + ": paused observation")
    for key, value in expected["observation"].items():
        require(fields[key] == value, case["name"] + ": paused " + key,
                {"expected": value, "actual": fields[key]})
    selected = one_form(reader, expected["selected_source"])
    agenda = fields["agenda"]
    require(isinstance(agenda, list) and agenda and agenda[0] == "SpaceAgenda",
            case["name"] + ": paused agenda", agenda)
    agenda_fields = named_fields(agenda[1:],
                                 ("phase", "selected", "commits", "retries",
                                  "obligation", "waiting", "observation"),
                                 case["name"] + ": paused agenda")
    require(agenda_fields == {"phase": expected["phase"], "selected": ["quote", selected],
                             "commits": "0", "retries": "0", "obligation": "Ready",
                             "waiting": ["quote", []], "observation": "committed-trace"},
            case["name"] + ": original source retained by agenda", agenda_fields)
    live = phases["live"]
    expected_live = [one_form(reader, atom) for atom in expected["live_support"]]
    logical = [one_form(reader, atom) for atom in expected["logical_support"]]
    require(isinstance(live, list) and gate_module.bag(live) == gate_module.bag(expected_live),
            case["name"] + ": exact paused live support", live)
    require(selected not in live, case["name"] + ": selected source moved out of live store", live)
    reconstructed = live + [selected]
    require(gate_module.bag(reconstructed) == gate_module.bag(logical),
            case["name"] + ": live plus owned reconstructs logical support",
            {"expected": logical, "actual": reconstructed})
    require(fields["residual"] == final_observation["residual"],
            case["name"] + ": resumed the same owned handle")
    require(list(gate_module.observations(phases["resumed"])) == [final_observation],
            case["name"] + ": retained resume observation", phases["resumed"])
    return {"live_support": live, "owned_selected": selected,
            "reconstructed_logical_support": reconstructed,
            "paused_observation": {"values": [], **fields},
            "same_residual_handle": True}


def check_case(gate_module, reader, gate, case, fixtures_root):
    source = (fixtures_root / case["fixture"]).read_text(encoding="utf-8")
    _, observations = gate.run(case["name"], source)
    receipt = gate.receipts[-1]
    require(receipt["exit"] == 0, case["name"] + ": exit", receipt["exit"])
    require(receipt["stderr"] == case["expected_stderr"],
            case["name"] + ": stderr", receipt["stderr"])
    result = {"name": case["name"], "kind": case["kind"]}
    if case["kind"] == "ordinary":
        require(receipt["stdout"] == case["expected_stdout"],
                case["name"] + ": stdout",
                {"expected": case["expected_stdout"], "actual": receipt["stdout"]})
        result["independently_expected_stdout"] = case["expected_stdout"]
    else:
        require(observations, case["name"] + ": missing observation")
        observation = observations[-1]
        for field, expected in case["expected_observation"].items():
            require(observation.get(field) == expected,
                    case["name"] + ": observation " + field,
                    {"expected": expected, "actual": observation.get(field)})
        if "expected_work" in case:
            require(observation.get("work") == case["expected_work"],
                    case["name"] + ": exact accepted work", observation)
        result["observation"] = observation
        if case["kind"] == "demand":
            require(observation["values"] == case["expected_values"],
                    case["name"] + ": demand values", observation["values"])
            result["independently_expected"] = case["expected_values"]
        else:
            forms = exact_forms(reader, receipt)
            require(forms and isinstance(forms[-1], list),
                    case["name"] + ": missing final support", forms)
            support = forms[-1]
            expected = [one_form(reader, atom) for atom in case["expected_support"]]
            require(gate_module.bag(support) == gate_module.bag(expected),
                    case["name"] + ": exact support",
                    {"expected": expected, "actual": support})
            if case["readout"] == "all":
                selected = support
            else:
                require(case["readout"] == "pq-facts",
                        case["name"] + ": unknown readout", case["readout"])
                selected = [atom for atom in support
                            if isinstance(atom, list) and len(atom) == 2
                            and atom[0] in ("p", "q")]
            reading = [one_form(reader, atom) for atom in case["expected_reading"]]
            require(gate_module.bag(selected) == gate_module.bag(reading),
                    case["name"] + ": declared readout",
                    {"expected": reading, "actual": selected})
            raw_observations = list(gate_module.observations(forms))
            require(raw_observations, case["name"] + ": exact observation missing")
            raw = raw_observations[-1]
            fields = check_transactions(reader, case, raw)
            if "pause_ownership" in case:
                result["pause_ownership"] = check_pause_ownership(
                    gate_module, reader, case, forms, raw)
            if case.get("no_partial_publication", False):
                require(len(forms) >= 2 and isinstance(forms[-2], list)
                        and len(forms[-2]) == 3 and forms[-2][:2] == ["Split", []],
                        case["name"] + ": no partial publication", forms)
            result.update(support=support, observed=selected,
                          independently_expected=reading,
                          independently_expected_full_support=expected,
                          receipt_fields=fields, exact_observation=raw,
                          native_quiescence=(observation["closed"] == "True"))
    gate.passed_case(case["name"])
    return result


def arguments():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runtime-root", type=Path, required=True)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--binary-sha256", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--fixtures-root", type=Path, default=HERE)
    parser.add_argument("--expectations", type=Path, default=HERE / "expectations.json")
    parser.add_argument("--timeout", type=float, default=15)
    args = parser.parse_args()
    require(sys.flags.optimize == 0, "run without Python optimization; the imported Gate uses assertions")
    require(len(args.binary_sha256) == 64
            and all(char in "0123456789abcdef" for char in args.binary_sha256),
            "--binary-sha256 must be an explicit lowercase SHA-256")
    require(args.timeout > 0, "--timeout must be positive")
    for name in ("runtime_root", "binary", "output", "fixtures_root", "expectations"):
        setattr(args, name, getattr(args, name).resolve())
    return args


def main():
    args = arguments()
    result = {"schema": SCHEMA, "at": datetime.now().astimezone().isoformat(),
              "passed": False, "evidence_kind": "native-replay",
              "runner_classification": "untrusted source adapter",
              "fixture_classification": "calibration fixture",
              "compiled_code_verification_claim": False,
              "runtime_source_to_binary_correspondence_claim": False,
              "expected_binary_sha256": args.binary_sha256,
              "assertions": [], "receipts": [], "passed_cases": 0}
    monitored = []
    before = []
    runtime_paths = []
    gate = None
    output_allowed = False
    try:
        manifest = json.loads(args.expectations.read_text(encoding="utf-8"))
        require(manifest["schema"] == SCHEMA and manifest["classification"] == "calibration fixture"
                and manifest["dialect"] == "prime"
                and manifest["compiled_code_verification_claim"] is False,
                "unexpected calibration manifest")
        cases = manifest["cases"]
        require(Counter(case["kind"] for case in cases) == Counter(KINDS)
                and len({case["name"] for case in cases}) == sum(KINDS.values())
                and len({case["fixture"] for case in cases}) == sum(KINDS.values()),
                "all declared calibration fixtures are required")
        for case in cases:
            relative = Path(case["fixture"])
            require(not relative.is_absolute() and ".." not in relative.parts,
                    "fixture paths must be relative", case["fixture"])
        runtime_paths = runtime_sources(args.runtime_root)
        monitored = [(Path(__file__).resolve(), "driver/replay.py"),
                     (args.expectations, "expectations.json"),
                     (args.binary, "binary/" + args.binary.name)]
        monitored += [(args.fixtures_root / case["fixture"], "fixtures/" + case["fixture"])
                      for case in cases]
        monitored += [(path, "runtime/" + path.relative_to(args.runtime_root).as_posix())
                      for path in runtime_paths]
        require(args.output not in {path.resolve() for path, _ in monitored},
                "evidence output must not overwrite an input")
        output_allowed = True
        before = [identity(path, label) for path, label in monitored]
        result.update(sources_before=before, driver=before[0], binary=before[2])
        require(before[2]["sha256"] == args.binary_sha256, "binary SHA-256 mismatch",
                {"expected": args.binary_sha256, "actual": before[2]["sha256"]})
        gate_module = load_module("programmable_space_cetta_gate",
                                  args.runtime_root / RUNTIME_ADAPTERS[0])
        reader = load_module("programmable_space_mm2_reader",
                             args.runtime_root / "tools/mm2_to_metta.py")
        gate = gate_module.Gate(argparse.Namespace(binary=args.binary, timeout=args.timeout))
        for case in cases:
            result["assertions"].append(check_case(gate_module, reader, gate, case, args.fixtures_root))
        result["passed"] = True
    except Exception as error:
        result["failure"] = {"type": type(error).__name__, "condition": str(error),
                             "details": getattr(error, "details", None)}
    finally:
        if gate is not None:
            result["receipts"] = gate.receipts
            result["passed_cases"] = gate.passed
        if before:
            try:
                after = [identity(path, label) for path, label in monitored]
                drift = [old["path"] for old, new in zip(before, after) if old != new]
                if runtime_sources(args.runtime_root) != runtime_paths:
                    drift.append("runtime/source-inventory")
                result.update(sources_after=after, source_drift=drift)
                if drift:
                    result["passed"] = False
                    result["identity_failure"] = "sources, binary or driver changed during replay"
            except Exception as error:
                result["passed"] = False
                result["identity_failure"] = str(error)
        if output_allowed:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"passed": result["passed"], "cases": result["passed_cases"],
                      "failure": result.get("failure")}))
    return 0 if result["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
