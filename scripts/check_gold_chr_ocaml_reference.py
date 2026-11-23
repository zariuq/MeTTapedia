#!/usr/bin/env python3
"""Native CHR and OCaml observations for the gold source programs.

The harness inspects native stores and values. It is not a parser, a language
implementation, or a certificate for the coGSLT translation.
"""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import time


ROOT = Path(__file__).resolve().parents[1]
GOLD = ROOT / "metta/gslt/module/gold"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--swipl", required=True, type=Path)
    parser.add_argument("--ocaml", required=True, type=Path)
    parser.add_argument("--ocamlc", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    binaries = {name: getattr(args, name).resolve(strict=True) for name in ("swipl", "ocaml", "ocamlc")}
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    sources = [*sorted((GOLD / "CHR/examples").glob("*.pl")),
               *sorted((GOLD / "OCaml/examples").glob("*.ml"))]
    for source in sources:
        shutil.copyfile(source, output / source.name)
    pins = {str(p.relative_to(ROOT)): digest(p) for p in sources}
    pins[str(Path(__file__).resolve().relative_to(ROOT))] = digest(Path(__file__).resolve())
    record = {"passed": False, "compiler_correspondence_qualified": False,
              "source_sha256": pins, "binary_sha256": {n: digest(p) for n, p in binaries.items()},
              "runs": [], "checks": []}

    def check(name, condition):
        record["checks"].append({"name": name, "passed": bool(condition)})
        if not condition:
            raise AssertionError(name)

    def run(name, engine, arguments):
        started = time.monotonic()
        result = subprocess.run([str(binaries[engine]), *arguments], cwd=output,
                                capture_output=True, text=True, timeout=60)
        (output / (name + ".stdout")).write_text(result.stdout)
        (output / (name + ".stderr")).write_text(result.stderr)
        record["runs"].append({"name": name, "engine": engine, "arguments": arguments,
                               "exit": result.returncode, "elapsed_seconds": time.monotonic() - started,
                               "stdout_sha256": digest(output / (name + ".stdout")),
                               "stderr_sha256": digest(output / (name + ".stderr"))})
        return result

    def chr_case(name, source, goal, expected=True):
        query = f"(({goal})->halt(0);halt(1))"
        (output / (name + ".goal")).write_text(query + "\n")
        result = run(name, "swipl", ["-q", "-s", source + ".pl", "-g", query])
        check(name, result.returncode == (0 if expected else 1) and not result.stderr)

    try:
        swi = run("swipl-version", "swipl", ["--version"])
        ml = run("ocaml-version", "ocaml", ["-version"])
        mlc = run("ocamlc-version", "ocamlc", ["-version"])
        check("pinned SWI-Prolog 10.1.9", swi.returncode == 0 and "10.1.9 " in swi.stdout)
        check("pinned OCaml 5.4.1", ml.returncode == 0 and "5.4.1" in ml.stdout
              and mlc.returncode == 0 and mlc.stdout.strip() == "5.4.1")
        config = run("ocaml-configuration", "ocamlc", ["-config"])
        check("native OCaml configuration recorded", config.returncode == 0)

        store = "gold_resource_scheduler:find_chr_constraint"
        chr_case("equal-workers", "resource_scheduler",
                 f"ready(a,yes),token(worker),token(worker),request(a),request(a),"
                 f"findall(P,{store}(receipt(a,P)),Rs),msort(Rs,[primary,primary]),"
                 f"findall(P,{store}(reported(a,P)),Ps),msort(Ps,[primary,primary]),"
                 f"{store}(ready(a,yes)),\\+{store}(token(_)),\\+{store}(request(_))")
        chr_case("exhausted-workers", "resource_scheduler",
                 f"ready(a,yes),token(worker),request(a),request(a),"
                 f"findall(J,{store}(request(J)),[a]),findall(P,{store}(receipt(a,P)),[primary])")
        chr_case("ordered-resource-choice", "resource_scheduler",
                 f"ready(a,yes),token(backup),token(worker),request(a),"
                 f"{store}(receipt(a,primary)),{store}(token(backup)),\\+{store}(token(worker))")
        chr_case("backup-resource", "resource_scheduler",
                 f"ready(a,yes),token(backup),request(a),{store}(receipt(a,backup))")
        chr_case("failed-guard", "resource_scheduler",
                 f"ready(a,no),token(worker),request(a),{store}(request(a)),"
                 f"{store}(token(worker)),\\+{store}(receipt(_,_))")
        chr_case("missing-permission", "resource_scheduler",
                 f"token(worker),request(a),{store}(request(a)),\\+{store}(receipt(_,_))")
        chr_case("binding-wakes-suspended-constraints", "resource_scheduler",
                 f"ready(a,Flag),token(worker),request(a),\\+{store}(receipt(_,_)),"
                 f"unify_with_occurs_check(Flag,yes),{store}(receipt(a,primary)),\\+{store}(request(_))")
        chr_case("propagation-history-survives-wakeup", "resource_scheduler",
                 f"receipt(J,primary),findall(K,{store}(reported(K,primary)),Before),length(Before,1),"
                 f"unify_with_occurs_check(J,a),findall(K,{store}(reported(K,primary)),[a]),"
                 f"receipt(a,primary),findall(K,{store}(reported(K,primary)),[a,a])")

        values = "gold_finite_terms:find_chr_constraint"
        chr_case("finite-term-propagation", "finite_terms",
                 f"wire(a,b),wire(b,c),value(a,pair(X,z)),value(c,pair(x,z)),X==x,"
                 f"{values}(value(b,pair(x,z))),{values}(value(c,pair(x,z)))")
        chr_case("equal-validation-evidence", "finite_terms",
                 f"value(a,pair(x,z)),value(a,pair(x,z)),"
                 f"findall(V,{values}(value(a,V)),[pair(x,z)])")
        chr_case("wrong-conclusion", "finite_terms", "value(a,x),value(a,y)", False)
        chr_case("occurs-check", "finite_terms", "same(X,node(X))", False)
        chr_case("missing-wire", "finite_terms",
                 f"value(a,x),\\+{values}(value(b,_))")

        for source in ("task_ranking", "tree_list"):
            interface = run(source + "-types", "ocamlc", ["-i", source + ".ml"])
            check(source + ": native type inference", interface.returncode == 0 and not interface.stderr)

        driver = '''#use "task_ranking.ml";;
let tasks = [Task ("a",7,true); Task ("b",9,false); Task ("c",7,true);
             Task ("d",1,true); Task ("e",8,true)];;
assert (names (rank tasks) = ["e";"a";"c";"d"]);;
assert (names (top 3 tasks) = ["e";"a";"c"]);;
assert (top 0 tasks = [] && top (-2) tasks = []);;
assert (names (rank [Task ("same",1,true);Task ("same",1,true)]) = ["same";"same"]);;
assert (names (rank [Task ("low",-3,true);Task ("high",-1,true)]) = ["high";"low"]);;
let threshold = 7;;
let above = score_above threshold;;
let threshold = "shadow";;
assert (above (Task (threshold,8,true)) && not (above (Task (threshold,7,true))));;
print_endline "ranking:6";;
#use "tree_list.ml";;
let tree = Node (Node (Empty,1,Empty),2,Node (Empty,3,Empty));;
assert (flatten (map_tree (fun value -> value + 10) tree) = [11;12;13]);;
assert (flatten (map_tree (fun _ -> true) tree) = [true;true;true]);;
assert (map_list (fun _ -> "ok") [1;2] = ["ok";"ok"]);;
assert (append [true;false] [true] = [true;false;true]);;
assert (shape (Node (Empty,"leaf",Empty)) = "leaf" && shape tree = "branch");;
assert (shape Empty = "empty" && flatten Empty = []);;
assert (use_polymorphic_identity () = (7,true,"task"));;
print_endline "trees:7";;
'''
        (output / "observations.ml").write_text(driver)
        observed = run("ocaml-observations", "ocaml", ["-noinit", "observations.ml"])
        check("OCaml: thirteen value and binding controls", observed.returncode == 0
              and not observed.stderr and observed.stdout.splitlines() == ["ranking:6", "trees:7"])
        for name, text, diagnostic in (
                ("wrong-list-type", "let values = [1; true]\n", "Error:"),
                ("wrong-argument-type", "let value = (fun x -> x + 1) true\n", "Error:")):
            (output / (name + ".ml")).write_text(text)
            rejected = run(name, "ocamlc", ["-i", name + ".ml"])
            check(name + ": rejected", rejected.returncode != 0 and diagnostic in rejected.stderr)
        (output / "zero-division.ml").write_text("let value = 1 / 0\n")
        fault = run("zero-division", "ocaml", ["-noinit", "zero-division.ml"])
        check("integer division preserves a fault", fault.returncode != 0 and "Division_by_zero" in fault.stderr)
        check("programs, harness and binaries unchanged",
              all(digest(ROOT / name) == value for name, value in pins.items())
              and all(digest(binaries[name]) == value for name, value in record["binary_sha256"].items()))
        record["passed"] = True
    except Exception as error:
        record["error"] = str(error)
        raise
    finally:
        (output / "result.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({"passed": True, "runs": len(record["runs"]),
                      "checks": len(record["checks"]), "ocaml_value_controls": 13,
                      "record_sha256": digest(output / "result.json")}))


if __name__ == "__main__":
    main()
