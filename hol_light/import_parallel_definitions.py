#!/usr/bin/env python3
"""Retain the two parallel definitions from an exported HOL proof closure."""

import argparse
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("closure", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    wanted = ["tc_parallel_store", "tc_parallel_present"]
    found = {}
    with args.closure.open() as source:
        for line in source:
            node = json.loads(line)
            if node["rule"] != "DEFINITION":
                continue
            name = node["arguments"][1]
            if name in wanted:
                if name in found:
                    raise ValueError("duplicate definition: " + name)
                found[name] = node
    if set(found) != set(wanted):
        raise ValueError("parallel definition inventory mismatch")

    declarations = []
    interned = {}

    def intern(value):
        key = json.dumps(value, sort_keys=True, ensure_ascii=False)
        if key in interned:
            return interned[key]
        if isinstance(value, str):
            body = "Lean.Json.str " + json.dumps(value, ensure_ascii=False)
        elif isinstance(value, bool):
            body = "Lean.Json.bool " + str(value).lower()
        elif isinstance(value, int) and value >= 0:
            body = "Lean.toJson (" + str(value) + " : Nat)"
        elif value is None:
            body = "Lean.Json.null"
        elif isinstance(value, list):
            body = "Lean.Json.arr #[" + ", ".join(intern(item) for item in value) + "]"
        elif isinstance(value, dict):
            body = "Lean.Json.mkObj [" + ", ".join(
                "(" + json.dumps(name) + ", " + intern(item) + ")" for name, item in value.items()) + "]"
        else:
            raise ValueError("unsupported source JSON value")
        name = "node" + str(len(declarations))
        interned[key] = name
        declarations.append("private def " + name + " : Lean.Json := " + body)
        return name

    records = [intern(found[name]) for name in wanted]
    args.output.write_text(
        "import Lean.Data.Json\n\n"
        "/-! # Received HOL parallel-definition data\n\n"
        "Generated from the independent HOL proof closure. The registered\n"
        "receiver checks these records; this data carries no correctness claim.\n-/\n\n"
        "set_option autoImplicit false\n\n"
        "namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLParallelDefinitionData\n\n"
        + "\n".join(declarations)
        + "\n\ndef records : List Lean.Json := [" + ", ".join(records) + "]\n\n"
        "end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLParallelDefinitionData\n")
    print("retained", len(records), "definitions in", len(declarations), "shared JSON nodes")


if __name__ == "__main__":
    main()
