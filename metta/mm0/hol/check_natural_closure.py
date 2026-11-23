#!/usr/bin/env python3
"""Check the HOL closure proofs against their typed reference and native MM0.

MM1 and the syntax emitter are untrusted producers. Both a separately built
upstream verifier and CeTTa check the compiled artifact against a separate
specification. No proof search or new logical checker is implemented here.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import resource
import subprocess
import time


NAMES = ["naturalClosureZero", "naturalClosureSuccessor", "naturalClosureElimination"]
CARRIER_NAMES = ["infiniteSuccessorT", "infiniteSuccessorInjective", "infiniteSuccessorNotOnto",
                 "infiniteZeroT", "infiniteZeroNoPreimage", "infiniteZeroNotSuccessor"]
NATURAL_TYPE_NAMES = ["holZeroT", "holSuccessorT", "holZeroNotSuccessor", "holSuccessorInjective",
                      "holNaturalInduction", "holNaturalInfinity"]

RECURSION_NAMES = ["holRecursionGraphElimination", "holRecursionGraphZero",
                   "holRecursionGraphSuccessor", "holRecursionGraphExists",
                   "holRecursionGraphZeroUnique", "holRecursionGraphSuccessorInverse",
                   "holRecursionGraphFunctional", "holRecursorT", "holRecursorGraph",
                   "holRecursorZero", "holRecursorSuccessor", "holNaturalRecursion"]


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cetta", required=True, type=Path)
    parser.add_argument("--compiler", required=True, type=Path)
    parser.add_argument("--reference", required=True, type=Path, help="upstream mm0-c verifier")
    parser.add_argument("--expected", required=True, type=Path,
                        help="JSON from the selected MM0 natural-fact emitter")
    parser.add_argument("--module", choices=["NaturalClosure", "NaturalInduction", "NaturalCarrier", "NaturalType", "NaturalRecursion"],
                        default="NaturalClosure")
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    source = Path(__file__).resolve().parent
    induction = args.module != "NaturalClosure"
    recursion = args.module == "NaturalRecursion"
    natural_type = args.module in ["NaturalType", "NaturalRecursion"]
    carrier = args.module in ["NaturalCarrier", "NaturalType", "NaturalRecursion"]
    names = (NAMES + (["naturalClosureInduction"] if induction else []) +
             (CARRIER_NAMES if carrier else []) + (NATURAL_TYPE_NAMES if natural_type else []) +
             (RECURSION_NAMES if recursion else []))
    statistics = {"NaturalClosure": "3 35 137", "NaturalInduction": "3 36 146",
                  "NaturalCarrier": "3 41 164", "NaturalType": "3 46 192", "NaturalRecursion": "3 48 207"}[args.module]
    proof_source = source / f"{args.module}.mm1"
    specification_source = source / f"{args.module}.mm0"
    workspace = source.parents[3]
    core = workspace / "repos/mm0/examples/hol.mm0"
    core_proofs = core.with_suffix(".mm1")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    cetta, compiler, reference = (path.resolve() for path in
                                   [args.cetta, args.compiler, args.reference])
    inputs = [source / "NaturalClosure.mm0", source / "NaturalClosure.mm1", core, core_proofs,
              cetta, cetta.parent / "lib/mm0kernel.metta", compiler, reference,
              args.expected.resolve(), Path(__file__).resolve()]
    proof_sources = [source / "NaturalClosure.mm1"]
    if induction:
        inputs += [source / "NaturalInduction.mm1", source / "NaturalInduction.mm0"]
        proof_sources.append(source / "NaturalInduction.mm1")
    if carrier:
        inputs += [source / "NaturalCarrier.mm1", source / "NaturalCarrier.mm0"]
        proof_sources.append(source / "NaturalCarrier.mm1")
    if natural_type:
        inputs += [source / "NaturalType.mm1", source / "NaturalType.mm0"]
        proof_sources.append(source / "NaturalType.mm1")
    if recursion:
        inputs += [proof_source, specification_source]
        proof_sources.append(proof_source)
    before = {str(path): sha256(path) for path in inputs}
    expected = json.loads(args.expected.read_text())
    for path in proof_sources:
        if re.search(r"^\s*(axiom|term|sort)\b", path.read_text(), re.M):
            raise RuntimeError("the source extension must contain only definitions and proofs")
    if any(name not in expected for name in names):
        raise RuntimeError("the selected reference is missing a public theorem")
    if "type_definition_axiom" not in expected:
        raise RuntimeError("the reference is missing the HOL type-definition boundary")

    started = time.monotonic()
    process_costs = []

    def run(command, label, stdin=None):
        stage_started = time.monotonic()
        result = subprocess.run(list(map(str, command)), input=stdin, capture_output=True,
                                text=True, cwd=workspace, timeout=120)
        (output / f"{label}.stdout").write_text(result.stdout)
        (output / f"{label}.stderr").write_text(result.stderr)
        process_costs.append(dict(stage=label, returncode=result.returncode,
                                  seconds=round(time.monotonic() - stage_started, 6)))
        return result

    artifact = output / "natural-closure.mmb"
    run([compiler, "compile", "-W", proof_source, artifact], "compile").check_returncode()
    published = output / "published.mm0"
    joined = run([compiler, "join", specification_source], "join")
    joined.check_returncode()
    published.write_text(joined.stdout)
    core_joined = run([compiler, "join", core], "core-join")
    core_joined.check_returncode()
    typed_reference = output / "typed-reference.mm0"
    typed_reference.write_text(core_joined.stdout + "\n" + expected["specification"])
    changed_body = output / "changed-definition.mm0"
    body_pattern = "(app p n)"
    if expected["definition_body"].count(body_pattern) != 1:
        raise RuntimeError("the reference body must retain exactly the submitted number occurrence")
    changed_body.write_text(typed_reference.read_text().replace(body_pattern, "(app p z)", 1))
    changed_claim = output / "changed-conclusion.mm0"
    pattern = "$ G |- naturalClosure A z s z $"
    if typed_reference.read_text().count(pattern) != 1:
        raise RuntimeError("ambiguous zero conclusion in reference")
    changed_claim.write_text(typed_reference.read_text().replace(pattern, "$ G |- F $", 1))
    reverted_type_definition = output / "reverted-type-definition.mm0"
    type_definition_equation = "$ G; a: tydef P |- =[tydef P] abs P @ (rep P @ a) = a $;"
    if typed_reference.read_text().count(type_definition_equation) != 1:
        raise RuntimeError("the supplied HOL abstraction/representation equation has an unexpected type")
    reverted_type_definition.write_text(typed_reference.read_text().replace(
        type_definition_equation, type_definition_equation.replace("=[tydef P]", "=[A]"), 1))
    extra_mutations = [("reverted-type-definition", reverted_type_definition, False)]
    if induction:
        altered_strengthening = output / "changed-strengthening.mm0"
        body = expected["strengthening_body"]
        if typed_reference.read_text().count(body) != 1:
            raise RuntimeError("ambiguous strengthened-predicate definition")
        altered_strengthening.write_text(typed_reference.read_text().replace(
            body, "(lam n A (app p n))", 1))
        extra_mutations.append(("changed-strengthening", altered_strengthening, False))
    if carrier:
        mutation_bodies = [
            ("changed-injection", expected["infiniteInjection_body"],
             expected["infiniteInjection_body"].replace("(andc ", "(orc ", 1), False),
            ("changed-zero", expected["infiniteZero_body"],
             "(app (sel (ind)) (rangePredicate (ind) (infiniteSuccessor)))", False),
            ("lost-no-confusion", "~(=[ind] infiniteZero = infiniteSuccessor @ n)",
             "(=[ind] infiniteZero = infiniteSuccessor @ n)", False),
            ("wrong-zero-type", "$ G |- infiniteZero: ind $;",
             "$ G |- infiniteZero: bool $;", False)]
        for label, original, replacement, should_pass in mutation_bodies:
            if original == replacement or typed_reference.read_text().count(original) != 1:
                raise RuntimeError(f"ambiguous carrier mutation {label}")
            mutation = output / f"{label}.mm0"
            mutation.write_text(typed_reference.read_text().replace(original, replacement, 1))
            extra_mutations.append((label, mutation, should_pass))
    if natural_type:
        mutations = [
            ("changed-natural-predicate", expected["holNaturalPredicate_body"], "(lam n (ind) (T))"),
            ("wrong-natural-equality", "~(=[holNatural] holZero = holSuccessor @ n)",
             "~(=[ind] holZero = holSuccessor @ n)"),
            ("missing-natural-step", " $ G |- !k: holNatural. p @ k ==> p @ (holSuccessor @ k) $ >", ""),
            ("changed-pullback", expected["holPullback_body"], "(lam n (ind) (app p n))")]
        for label, original, replacement in mutations:
            if original == replacement or typed_reference.read_text().count(original) != 1:
                raise RuntimeError(f"ambiguous natural-subtype mutation {label}")
            mutation = output / f"{label}.mm0"
            mutation.write_text(typed_reference.read_text().replace(original, replacement, 1))
            extra_mutations.append((label, mutation, False))
    if recursion:
        mutations = [
            ("changed-graph-output", expected["holRecursionGraph_body"],
             expected["holRecursionGraph_body"].replace("(app (app r n) v)", "(app (app r n) a)", 1)),
            ("reversed-graph-method", expected["holRecursionGraph_body"],
             expected["holRecursionGraph_body"].replace("(app (app f w) k)", "(app (app f k) w)", 1)),
            ("changed-recursive-selection", expected["holRecursor_body"],
             expected["holRecursor_body"].replace("a f number value)", "a f value number)", 1)),
            ("missing-second-graph", "$ (im G (thm (holRecursionGraph A a f n w))) $ >\n ", ""),
            ("reversed-recursion-method", "(app (app f (app g n)) n)", "(app (app f n) (app g n))")]
        for label, original, replacement in mutations:
            if original == replacement or typed_reference.read_text().count(original) != 1:
                raise RuntimeError(f"ambiguous recursion mutation {label}")
            mutation = output / f"{label}.mm0"
            mutation.write_text(typed_reference.read_text().replace(original, replacement, 1))
            extra_mutations.append((label, mutation, False))
    truncated = output / "truncated.mmb"
    truncated.write_bytes(artifact.read_bytes()[:32])

    reference_results = []
    for label, specification, should_pass in [
        ("published", published, True), ("typed", typed_reference, True),
        ("changed-definition", changed_body, False), ("changed-conclusion", changed_claim, False),
    ] + extra_mutations:
        result = run([reference, artifact], f"reference-{label}", specification.read_text())
        if (result.returncode == 0) != should_pass:
            raise RuntimeError(f"upstream verifier disagrees on {label}")
        reference_results.append(dict(case=label, returncode=result.returncode))

    run([compiler, "doc", "--only", ",".join(names), "--src", "-",
         proof_source, output / "upstream-doc"], "dependencies").check_returncode()
    dependencies = {}
    permitted = set("id syl ian anl anr appT lamT appTR1 appTR2 appTR22 eqT thmR refl aeq leq beta eqmp ded cbvv inst".split())
    if carrier:
        permitted |= {"eta", "selT", "ax_sel", "inf"}
    if natural_type:
        permitted |= {"absT", "repT", "abs_rep", "rep_abs"}
    for name in names:
        page = (output / "upstream-doc/thms" / f"{name}.html").read_text()
        marker = '<h2 class="axioms">Axiom use</h2>'
        if page.count(marker) != 1:
            raise RuntimeError(f"missing dependency section for {name}")
        used = re.findall(r'<a class="ax" href="[^"]+">([^<]+)</a>', page.split(marker)[1])
        if not used or set(used) - permitted or "sorry" in page.split(marker)[1]:
            raise RuntimeError(f"unexpected proof assumptions for {name}: {used}")
        dependencies[name] = used

    native = []
    for dialect in ["he", "petta", "prime"]:
        queries = []

        def query(expression):
            text = '!(import! &self mm0kernel)\n!(' + expression + ')\n'
            label = f"{dialect}-{len(queries):02}"
            (output / f"{label}.metta").write_text(text)
            profile = [] if dialect == "prime" else ["--profile", "extended"]
            result = run([cetta, "--lang", dialect, *profile, "--quiet", "-e", text], label)
            result.check_returncode()
            if result.stderr.strip():
                raise RuntimeError(f"native diagnostics in {label}: {result.stderr}")
            lines = result.stdout.splitlines()
            if len(lines) != (2 if dialect == "petta" else 1):
                raise RuntimeError(f"unexpected output in {label}: {result.stdout!r}")
            value = lines[-1]
            if dialect != "petta" and value.startswith("[") and value.endswith("]"):
                value = value[1:-1]
            queries.append(dict(label=label, value=value))
            return value

        def equal(expression, target):
            actual = query(expression)
            if actual != target:
                raise RuntimeError(f"{dialect}: expected {target!r}, got {actual!r}")

        def refuses(expression, statuses=("REFUSED",)):
            actual = query(expression)
            if not actual.startswith(("(mm0:refused ", "(mm0:error ")) or not any(
                    f'"{status}"' in actual for status in statuses):
                raise RuntimeError(f"{dialect}: expected completed refusal, got {actual!r}")

        def loaded(expression, extra=""):
            return ('let* (($th (mm0:theory)) ($_ (mm0:load-mmb $th '
                    + json.dumps(str(artifact)) + ' ' + json.dumps(str(typed_reference))
                    + '))' + extra + ') ' + expression)

        def data(value):
            return f"(quote {value})" if dialect == "prime" else value

        for specification in [published, typed_reference]:
            equal(f'mm0:check-mmb {json.dumps(str(artifact))} {json.dumps(str(specification))}',
                  f"(mm0:verified {statistics})")
        for name in names:
            equal(loaded(f"(mm0:statement (mm0:theorem $th {name}))"), expected[name])
        equal(loaded("(mm0:statement (mm0:theorem $th abs_rep))"), expected["type_definition_axiom"])

        statement = expected[names[0]].replace(names[0], "closure_zero_replay", 1)
        rows = ("((Mm0Row 0 (hyp 0) ()) (Mm0Row 1 (hyp 1) ()) "
                "(Mm0Row 2 (thm naturalClosureZero (G A z s)) (0 1)))")

        def prove(claim=statement, proof=rows):
            return f"(mm0:prove $th {data(claim)} {data('()')} {data(proof)} 2)"

        equal(loaded(f"(mm0:statement {prove()})"), statement)
        wrong = statement.replace("(thm (naturalClosure A z s z))", "(thm (F))")
        refuses(loaded(prove(wrong)))
        refuses(loaded(prove(proof=rows.replace("(0 1)))", "(1 0)))"))))
        missing = statement.replace(" (im G (ty s (fun A A)))", "")
        refuses(loaded(prove(missing)))
        equal(loaded("(let (Mm0Stats $s $t $n $bytes) (mm0:stats $th) ($s $t $n))",
                     f" ($failed {prove(wrong)})"), f"({statistics})")
        refuses(loaded("(mm0:theorem $th closure_zero_replay)", f" ($failed {prove(wrong)})"),
                ("MALFORMED",))
        if induction:
            induction_claim = expected["naturalClosureInduction"].replace(
                "naturalClosureInduction", "closure_induction_replay", 1)
            induction_rows = "(" + " ".join(
                f"(Mm0Row {index} (hyp {index}) ())" for index in range(7)) + (
                " (Mm0Row 7 (thm naturalClosureInduction (G A z s n p k)) (0 1 2 3 4 5 6)))")

            def induction_prove(claim=induction_claim, proof=induction_rows):
                return f"(mm0:prove $th {data(claim)} {data('()')} {data(proof)} 7)"

            equal(loaded(f"(mm0:statement {induction_prove()})"), induction_claim)
            wrong_guard = expected["naturalClosureElimination"].replace(
                "naturalClosureElimination", "closure_induction_replay", 1)
            refuses(loaded(induction_prove(wrong_guard)))
            missing_closure = induction_claim.replace(
                " (im G (thm (naturalClosure A z s n)))", "")
            if missing_closure == induction_claim:
                raise RuntimeError("missing closure premise in induction reference")
            refuses(loaded(induction_prove(missing_closure)))
            refuses(loaded(induction_prove(proof=induction_rows.replace(
                "(0 1 2 3 4 5 6)))", "(0 1 2 3 5 4 6)))"))))
        if carrier:
            carrier_claim = expected["infiniteZeroNotSuccessor"].replace(
                "infiniteZeroNotSuccessor", "selected_zero_replay", 1)
            carrier_rows = ("((Mm0Row 0 (hyp 0) ()) "
                            "(Mm0Row 1 (thm infiniteZeroNotSuccessor (G n)) (0)))")

            def carrier_prove(claim=carrier_claim, proof=carrier_rows):
                return f"(mm0:prove $th {data(claim)} {data('()')} {data(proof)} 1)"

            equal(loaded(f"(mm0:statement {carrier_prove()})"), carrier_claim)
            # Build the sign mutation by its full conclusion to keep balanced syntax.
            old_conclusion = "(thm (notc (eqc (ind) (infiniteZero) (app (infiniteSuccessor) n))))"
            new_conclusion = "(thm (eqc (ind) (infiniteZero) (app (infiniteSuccessor) n)))"
            if carrier_claim.count(old_conclusion) != 1:
                raise RuntimeError("carrier replay has an unexpected no-confusion conclusion")
            refuses(loaded(carrier_prove(carrier_claim.replace(old_conclusion, new_conclusion, 1))))
            missing_type = carrier_claim.replace("(im G (ty n (ind)))", "", 1)
            if missing_type == carrier_claim:
                raise RuntimeError("carrier replay lost its typed argument")
            refuses(loaded(carrier_prove(missing_type)))
            refuses(loaded(carrier_prove(proof=carrier_rows.replace("(0)))", "()))"))))
        if natural_type:
            natural_claim = expected["holNaturalInduction"].replace(
                "holNaturalInduction", "natural_induction_replay", 1)
            natural_rows = "(" + " ".join(
                f"(Mm0Row {i} (hyp {i}) ())" for i in range(4)) + (
                " (Mm0Row 4 (thm holNaturalInduction (G n p k)) (0 1 2 3)))")

            def natural_prove(claim=natural_claim, proof=natural_rows):
                return f"(mm0:prove $th {data(claim)} {data('()')} {data(proof)} 4)"

            equal(loaded(f"(mm0:statement {natural_prove()})"), natural_claim)
            missing_base = natural_claim.replace("(im G (thm (app p (holZero))))", "", 1)
            if missing_base == natural_claim:
                raise RuntimeError("natural induction replay has no base premise")
            refuses(loaded(natural_prove(missing_base)))
            wrong_domain = natural_claim.replace("(allc k (holNatural) ", "(allc k (ind) ", 1)
            if wrong_domain == natural_claim:
                raise RuntimeError("natural induction replay has no natural step domain")
            refuses(loaded(natural_prove(wrong_domain)))
            refuses(loaded(natural_prove(proof=natural_rows.replace(
                "(0 1 2 3)))", "(0 1 3 2)))"))))
        for specification in [changed_body, changed_claim] + [row[1] for row in extra_mutations]:
            refuses(f'mm0:check-mmb {json.dumps(str(artifact))} {json.dumps(str(specification))}')
        refuses(f'mm0:check-mmb {json.dumps(str(truncated))} {json.dumps(str(typed_reference))}',
                ("MALFORMED", "REFUSED"))
        if recursion:
            recursion_zero = expected["holRecursorZero"].replace(
                "holRecursorZero", "recursion_zero_replay", 1)
            zero_rows = ("((Mm0Row 0 (hyp 0) ()) (Mm0Row 1 (hyp 1) ()) "
                         "(Mm0Row 2 (thm holRecursorZero (G A a f)) (0 1)))")

            def recursion_zero_prove(claim=recursion_zero, proof=zero_rows):
                return f"(mm0:prove $th {data(claim)} {data('()')} {data(proof)} 2)"

            equal(loaded(f"(mm0:statement {recursion_zero_prove()})"), recursion_zero)
            refuses(loaded(recursion_zero_prove(proof=zero_rows.replace("(0 1)))", "(1 0)))"))))
            missing_method = recursion_zero.replace("(im G (ty f (fun A (fun (holNatural) A))))", "", 1)
            if missing_method == recursion_zero:
                raise RuntimeError("the recursion replay lost its typed method")
            refuses(loaded(recursion_zero_prove(missing_method)))
            wrong_base = recursion_zero.replace(
                "(eqc A (app (holRecursor A a f) (holZero)) a)",
                "(eqc A (app (holRecursor A a f) (app (holSuccessor) (holZero))) a)", 1)
            if wrong_base == recursion_zero:
                raise RuntimeError("the recursion replay lost its zero equation")
            refuses(loaded(recursion_zero_prove(wrong_base)))
            recursion_claim = expected["holNaturalRecursion"].replace(
                "holNaturalRecursion", "natural_recursion_replay", 1)
            recursion_rows = "((Mm0Row 0 (thm holNaturalRecursion (G A a f g n)) ()))"

            def recursion_prove(claim=recursion_claim, proof=recursion_rows):
                return f"(mm0:prove $th {data(claim)} {data('()')} {data(proof)} 0)"

            equal(loaded(f"(mm0:statement {recursion_prove()})"), recursion_claim)
            swapped = recursion_claim.replace("(app (app f (app g n)) n)", "(app (app f n) (app g n))", 1)
            if swapped == recursion_claim:
                raise RuntimeError("the recursion statement has an unexpected method order")
            refuses(loaded(recursion_prove(swapped)))
            refuses(loaded("(mm0:theorem $th natural_recursion_replay)",
                            f" ($failed {recursion_prove(swapped)})"), ("MALFORMED",))
        native.append(dict(dialect=dialect, controls=len(queries), results=queries))

    after = {str(path): sha256(path) for path in inputs}
    if before != after:
        raise RuntimeError("an input changed during qualification")
    profile = ("HOL natural subtype: primitive recursion from a total functional graph"
               if recursion else "HOL natural subtype: constructor laws, induction and infinity"
               if natural_type else "HOL selected pointed injection from choice and infinity, with natural closure and induction"
               if carrier else "HOL natural closure: zero, successor, elimination, closure-premised induction"
               if induction else
               "HOL natural closure: zero, successor, elimination")
    report = dict(qualified=True, profile=profile,
                  source_axioms_added=0, native=native, reference_checks=reference_results,
                  upstream_proof_dependencies=dependencies, input_sha256=after,
                  artifact_sha256=sha256(artifact), artifact_bytes=artifact.stat().st_size,
                  typed_reference_sha256=sha256(typed_reference),
                  seconds=round(time.monotonic() - started, 3),
                  process_costs=process_costs,
                  child_maxrss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
                  cost_scope="subprocess wall times, including parsing/loading/IPC; aggregate child peak RSS",
                  remaining=[("full same-source Nat-fact comparison" if recursion else
                              "primitive recursion and full same-source Nat-fact transport" if natural_type else
                              "natural subtype, recursion and full Nat-fact transport" if carrier else
                              "primitive recursion, no-confusion and infinity transport"),
                             "general source-to-native checker refinement",
                             "full HOL-presentation adequacy and proof-local base extraction"])
    (output / "qualification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: report[key] for key in ["qualified", "artifact_bytes", "seconds"]}))
    print(json.dumps({row["dialect"]: row["controls"] for row in native}))


if __name__ == "__main__":
    main()
