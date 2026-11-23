#!/usr/bin/env python3
"""Differential check of the Lean mainline MM2 model against the MORK kernel binary.

Each program of a generated corpus, plus named fixtures, runs on the kernel binary
(`mork run`) and through the model (`Runner.lean`, which calls
`Mainline.Reference.runProgram`).  The final spaces are compared as sets of printed atoms;
a kernel panic is compared with the model's fault.

Outcome classes per program:
  agree          same final space, or both abort
  differ         different final spaces, or only one side aborts
  abstain        the model reports a fault it uses for kernel behaviour that depends on
                 trie order or byte keys (extremaDuplicate, misKeyedAggregate); recorded,
                 not counted as agreement or difference
  diverge        the kernel times out and the model runs out of fuel
  unchecked      the program uses something the comparison cannot normalize (hash bytes)
  environmental  the kernel crashed on a signal in a run with more than one `U` sink: each `U`
                 sink reserves 8 GiB of address space and never releases it, so the outcome
                 depends on the address-space limit, which the model does not take
  external       the model reports a missing file that the kernel found: the program reads an
                 ACT file left by another run

Usage:
  mm2_differential.py --mork BIN --lean-root DIR --out DIR [--count N] [--seed S]
                      [--fixtures DIR ...] [--shrink]
"""

import argparse
import json
import os
import random
import resource
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
RUNNER = HERE / "Runner.lean"
WRAPPER_ENV = "LEAN_WRAPPER"
ABSTAIN = {"extremaDuplicate", "misKeyedAggregate"}

# Kernel panic messages and the model faults that correspond to them.
PANIC_CLASSES = [
    ("unrecognized sink", {"unrecognizedSink", "missingFeature"}),
    ("not yet implemented", {"unimplementedPureShape"}),
    ("act not the right shape", {"malformed"}),
    ("internal error: entered unreachable code", {"unrecognizedSource", "missingFeature"}),
    ("comparator not implemented", {"unrecognizedSource"}),
    ("assertion", {"extremaDuplicate"}),
    ("range end index", {"antiUnifySingleRow"}),
]


# --------------------------------------------------------------------------- generation

SYMBOLS = ["a", "b", "c"]
NUMBERS = ["1", "2", "3", "5", "8"]
DYADICS = ["0.5", "1.5", "2", "2.25", "-1", "3.75", "0.125"]
CHARS = ["a", "b", "c", "q", "w"]


class Gen:
    """Random programs over a small vocabulary, organized by the feature they exercise."""

    def __init__(self, rng):
        self.rng = rng
        self.uses_u = False

    def var(self):
        return "$" + self.rng.choice(["x", "y", "z"])

    def term(self, var_rate=0.2, depth=0):
        r = self.rng.random()
        if r < var_rate:
            return self.var()
        if depth < 1 and r < var_rate + 0.12:
            return "(" + self.rng.choice(["f", "g"]) + " " + self.term(var_rate, depth + 1) + ")"
        return self.rng.choice(SYMBOLS)

    def fact(self, var_rate=0.15):
        pred, arity = self.rng.choice([("p", 1), ("q", 1), ("r", 2), ("s", 2)])
        args = " ".join(self.term(var_rate) for _ in range(arity))
        return f"({pred} {args})"

    def pattern(self):
        pred, arity = self.rng.choice([("p", 1), ("q", 1), ("r", 2), ("s", 2)])
        args = " ".join(self.term(0.6) for _ in range(arity))
        return f"({pred} {args})"

    def location(self):
        return self.rng.choice(["0", "1", "2", "(0 a)", "(1 b)", "z", "()"])

    def data(self, k=None):
        k = k if k is not None else self.rng.randint(1, 5)
        return [self.fact() for _ in range(k)]

    def vars_of(self, text):
        out = []
        for token in text.replace("(", " ").replace(")", " ").split():
            if token.startswith("$") and token not in out:
                out.append(token)
        return out

    def template(self, bound):
        pick = self.rng.random()
        pool = bound + (["$w"] if self.rng.random() < 0.2 else [])
        if not pool:
            return "(" + self.rng.choice(["t", "u"]) + " " + self.rng.choice(SYMBOLS) + ")"
        args = " ".join(self.rng.choice(pool) for _ in range(self.rng.randint(1, 2)))
        head = "t" if pick < 0.5 else "u"
        return f"({head} {args})"

    def sink(self, bound):
        kinds = ["+", "+", "-", "head", "tail", "count", "AU"]
        if not self.uses_u:
            kinds.append("U")
        kind = self.rng.choice(kinds)
        tmpl = self.template(bound)
        if kind == "+":
            return f"(+ {tmpl})"
        if kind == "-":
            # remove a data fact or a template instance
            target = self.pattern_from(bound) if self.rng.random() < 0.6 else tmpl
            return f"(- {target})"
        if kind in ("head", "tail"):
            return f"({kind} {self.rng.randint(1, 3)} {tmpl})"
        if kind == "count":
            payload = self.rng.choice(bound) if bound else "x"
            return f"(count (cnt $k) $k {payload})"
        if kind == "U":
            self.uses_u = True
            return f"(U {tmpl})"
        return f"(AU {tmpl})"

    def pattern_from(self, bound):
        pred, arity = self.rng.choice([("p", 1), ("q", 1), ("r", 2), ("s", 2)])
        pool = bound + SYMBOLS
        args = " ".join(self.rng.choice(pool) for _ in range(arity))
        return f"({pred} {args})"

    def input(self):
        if self.rng.random() < 0.7:
            n = self.rng.choice([0, 1, 1, 1, 2, 2])
            pats = [self.pattern() for _ in range(n)]
            return "(, " + " ".join(pats) + ")" if pats else "(,)"
        factors = []
        for _ in range(self.rng.randint(1, 2)):
            r = self.rng.random()
            if r < 0.5:
                factors.append(f"(BTM {self.pattern()})")
            elif r < 0.75:
                factors.append(f"(== {self.pattern()} {self.pattern()})")
            else:
                factors.append(f"(!= {self.pattern()} {self.pattern()})")
        return "(I " + " ".join(factors) + ")"

    def output(self, bound):
        if self.rng.random() < 0.25:
            return "(, " + " ".join(self.template(bound) for _ in range(self.rng.randint(1, 2))) + ")"
        return "(O " + " ".join(self.sink(bound) for _ in range(self.rng.randint(1, 3))) + ")"

    def exec_(self):
        inp = self.input()
        bound = self.vars_of(inp)
        return f"(exec {self.location()} {inp} {self.output(bound)})"

    # --- families -------------------------------------------------------------------

    def random_program(self):
        self.uses_u = False
        atoms = self.data()
        for _ in range(self.rng.randint(1, 3)):
            atoms.append(self.exec_())
        if self.rng.random() < 0.15:
            # an executable that writes an executable
            inner = self.exec_()
            atoms.append(f"(exec {self.location()} (,) (O (+ {inner})))")
        return atoms

    def numeric_program(self):
        """sum, fsum/fmin/fmax/fprod and and over grouped payloads."""
        atoms = []
        for name in self.rng.sample(["k1", "k2", "k3", "k4"], self.rng.randint(1, 4)):
            group = self.rng.choice(["g", "h"])
            atoms.append(f"(num {group} {name} {self.rng.choice(NUMBERS)})")
            atoms.append(f"(flt {group} {name} {self.rng.choice(DYADICS)})")
            atoms.append(f"(chr {group} {name} {self.rng.choice(CHARS)})")
        sink = self.rng.choice([
            "(sum (sm $g $s) $s $v)",
            "(fsum (fs $g $s) $s $f)", "(fmin (fn $g $s) $s $f)",
            "(fmax (fx $g $s) $s $f)", "(fprod (fp $g $s) $s $f)",
            "(and (an $g $s) $s $c)",
            "(count (ct $g $s) $s $k)",
        ])
        atoms.append(f"(exec 0 (, (num $g $k $v) (flt $g $k $f) (chr $g $k $c)) (O {sink}))")
        return atoms

    def pure_program(self):
        atoms = [f"(arg {self.rng.choice(NUMBERS)})", f"(arg {self.rng.choice(['x', '7', '12'])})",
                 f"(word {self.rng.choice(['abc', 'hello', 'mork'])})"]
        call = self.rng.choice([
            "(i32_to_string (sum_i32 (i32_from_string $a) (i32_from_string 1)))",
            "(i32_to_string (product_i32 (i32_from_string $a) (i32_from_string 3)))",
            "(i32_to_string (sub_i32 (i32_from_string $a) (i32_from_string 10)))",
        ])
        atoms.append(f"(exec 0 (, (arg $a)) (O (pure (res $a $r) $r {call})))")
        wcall = self.rng.choice([
            "(reverse_symbol $w)", "(explode_symbol $w)", "(tuple $w $w)",
            "(collapse_symbol (tuple $w $w))", "(tuple $w (quote (lit $w)))",
        ])
        atoms.append(f"(exec 1 (, (word $w)) (O (pure (wres $r) $r {wcall})))")
        if self.rng.random() < 0.5:
            atoms.append("(exec 2 (, (res $a $b)) (O (+ (seen $b)) (pure (also $r) $r (tuple $b))))")
        return atoms

    def act_program(self):
        """An ACT file written and read in one run (a fixed file name, rewritten each time)."""
        atoms = self.data(3)
        tmpl = self.template(["$x"])
        atoms.append(f"(exec 0 (, (p $x)) (O (ACT h2act {tmpl})))")
        atoms.append(f"(exec 1 (I (ACT h2act ($h $y))) (O (+ (read $h $y))))")
        return atoms

    def order_program(self):
        """Adds against finalized sinks on overlapping instances."""
        atoms = self.data(3)
        sinks = ["(+ (p $x))", "(- (p $x))", "(+ (q $x))", "(- (q $x))", "(head 1 (p $x))",
                 "(tail 1 (q $x))", "(count (n $k) $k $x)"]
        chosen = self.rng.sample(sinks, self.rng.randint(2, 4))
        atoms.append(f"(exec 0 (, (p $x)) (O {' '.join(chosen)}))")
        if self.rng.random() < 0.5:
            atoms.append("(exec 1 (, (q $y)) (O (- (q $y)) (+ (moved $y))))")
        return atoms

    def reflective_program(self):
        """Executables reading executables, and themselves."""
        atoms = self.data(2)
        atoms.append("(exec 0 (, (exec $l $i $o)) (O (+ (sawexec $l))))")
        atoms.append(f"(exec 1 (, {self.pattern()}) (O (+ (late))))")
        if self.rng.random() < 0.5:
            atoms.append("(exec 2 (, ($h $v)) (O (+ (any $h))))")
        return atoms

    def unify_program(self):
        """Stored atoms with variables, repeated variables and nested terms, read by
        patterns that mix constants and variables: the kernel unifies."""
        atoms = []
        for _ in range(self.rng.randint(2, 5)):
            pred, arity = self.rng.choice([("p", 1), ("r", 2), ("s", 2)])
            args = []
            for _ in range(arity):
                r = self.rng.random()
                if r < 0.35:
                    args.append(self.rng.choice(["$a", "$b"]))
                elif r < 0.55:
                    args.append("(f " + self.rng.choice(["$a", "a", "b"]) + ")")
                else:
                    args.append(self.rng.choice(SYMBOLS))
            atoms.append(f"({pred} {' '.join(args)})")
        first = self.pattern()
        second = self.pattern() if self.rng.random() < 0.5 else ""
        inp = "(, " + first + (" " + second if second else "") + ")"
        bound = self.vars_of(inp)
        atoms.append(f"(exec 0 {inp} (O {self.sink(bound)} (+ {self.template(bound)})))")
        return atoms


def fault_fixtures():
    return {
        "fault_unknown_sink": ["(p a)", "(exec 0 (, (p $x)) (O (bogus $x)))"],
        "fault_unknown_source": ["(p a)", "(exec 0 (I (FOO (p $x))) (O (+ (r $x))))"],
        "fault_unit_input": ["(p a)", "(exec 0 () (O (+ (r))))"],
        "fault_bad_functor": ["(p a)", "(exec 0 (X (p $x)) (O (+ (r $x))))"],
        "fault_pure_literal_result": ["(exec 0 (,) (O (pure (g $r) a (tuple a))))"],
        "fault_sum_non_decimal": ["(v a x)", "(exec 0 (, (v $k $n)) (O (sum (sm $s) $s $n)))"],
        "fault_z3_default": ["(exec 0 (,) (O (z3 s (assert true))))"],
        "fault_wasm_default": ["(exec 0 (,) (O (wasm prog (x))))"],
        "fault_act_missing": ["(exec 0 (I (ACT h2missing (foo $x))) (O (+ (got $x))))"],
        "fault_act_bare_variable": ["(exec 0 (,) (O (ACT h2act (a))))",
                                    "(exec 1 (I (ACT h2act $x)) (O (+ (got $x))))"],
        "pure_fresh_result": ["(exec 0 (,) (O (pure (g $q) $r (tuple a))))"],
        "pure_error_skips": ["(arg 3) (arg x)",
                             "(exec 0 (, (arg $a)) (O (pure (h $a $r) $r (i32_to_string (sum_i32 (i32_from_string $a) (i32_from_string 1))))))"],
        "steps_two_execs": ["(exec 0 (,) (O (+ (one))))", "(exec 1 (,) (O (+ (two))))"],
        "generated_exec_below": ["(exec 1 (,) (O (+ (exec 0 (,) (O (+ (gen)))))))",
                                 "(exec 2 (, (gen)) (O (+ (after))))"],
        "self_read": ["(exec 0 (, (exec 0 $i $o)) (O (+ (me $i))))"],
        "unify_sink": ["(p a b) (p $x b)", "(exec 0 (, (p $u $v)) (O (U (both $u $v))))"],
        "unify_conflict": ["(p a) (p b)", "(exec 0 (, (p $u)) (O (U (one $u))))"],
        "antiunify_sink": ["(p (f a) b) (p (f c) b) (p (g a) b)", "(exec 0 (, (p $u $v)) (O (AU (gen $u $v))))"],
        "count_literal_guard": ["(p a) (p b)", "(exec 0 (, (p $x)) (O (count (exactly-two) 2 $x)))"],
        "count_var_first": ["(p a) (p b)", "(exec 0 (, (p $x)) (O (count ($c all) $c $x)))"],
        "head_duplicate": ["(p a 1) (p b 1) (p c 2)", "(exec 0 (, (p $x $v)) (O (head 1 (m $v))))"],
        "neq_levels": ["(p $a) (q $b $b)", "(exec 0 (I (!= (p $x) (q $y $z))) (, (ne1 $x $y $z)))"],
        "eq_copy": ["(foo $q)", "(exec 0 (I (== (foo $x) (foo a))) (, (eq1 $x)))"],
        "stored_var_constant": ["(foo $q)", "(exec 0 (, (foo a)) (, (hit)))"],
        "occurs_check": ["(foo $q (f $q))", "(exec 0 (, (foo $x $x)) (, (cyc $x)))"],
        "bare_variable_fact": ["$v", "(exec 0 (, (p a)) (, (hit)))"],
        "remove_nonground": ["(foo a) (foo $q)", "(exec 0 (,) (O (- (foo $x))))"],
        "add_nonground": ["(exec 0 (,) (O (+ (bar $x))))"],
        "comma_template_verbatim": ["(p a)", "(exec 0 (, (p $x)) (, (- (p $x)) (r $x)))"],
        "remove_then_add": ["(exec 0 (,) (O (- (x)) (+ (x))))"],
        "edge_add_first": ["(edge a b) (edge b c)", "(exec (0 overlap) (, (edge $x $y)) (O (+ $x) (- $y)))"],
        "edge_remove_first": ["(edge a b) (edge b c)", "(exec (0 overlap) (, (edge $x $y)) (O (- $y) (+ $x)))"],
        "head_then_remove": ["(p 1) (p 2) (p 3)", "(exec 0 (, (p $x)) (O (head 2 (top $x)) (- (top 1))))"],
    }


# --------------------------------------------------------------------------- running

def limit_memory():
    gib24 = 24 * 1024 ** 3
    resource.setrlimit(resource.RLIMIT_AS, (gib24, gib24))


def run_kernel(binary, corpus_dir, name, timeout):
    path = corpus_dir / f"{name}.mm2"
    try:
        proc = subprocess.run([str(binary), "run", path.name], cwd=corpus_dir, capture_output=True,
                              timeout=timeout, preexec_fn=limit_memory)
    except subprocess.TimeoutExpired:
        return {"status": "timeout"}
    stdout = proc.stdout.decode("utf-8", "replace")
    stderr = proc.stderr.decode("utf-8", "replace")
    if proc.returncode != 0:
        return {"status": "panic", "code": proc.returncode, "stderr": stderr[-2000:]}
    if "result:" not in stdout:
        return {"status": "noresult", "stdout": stdout[-2000:]}
    lines = [line.rstrip() for line in stdout.split("result:", 1)[1].split("\n")]
    return {"status": "ok", "atoms": sorted(line for line in lines if line)}


def run_model(lean_root, programs_file, fuel, wrapper):
    command = ["lake", "env", "lean", "--run", str(RUNNER), str(programs_file), str(fuel)]
    if wrapper:
        command = [wrapper, "run"] + command
    proc = subprocess.run(command, cwd=lean_root, capture_output=True, text=True, timeout=3600)
    results = {}
    current = None
    for line in proc.stdout.split("\n"):
        if line.startswith("=== "):
            current = line[4:]
            results[current] = []
        elif current is not None:
            results[current].append(line)
    out = {}
    for name, lines in results.items():
        lines = [line.rstrip() for line in lines if line.strip()]
        if lines and lines[0].startswith("FAULT "):
            out[name] = {"status": "fault", "fault": lines[0][6:]}
        elif lines and lines[0] == "FUEL":
            out[name] = {"status": "fuel"}
        elif lines and lines[0].startswith("PARSE "):
            out[name] = {"status": "parse", "message": lines[0]}
        else:
            out[name] = {"status": "ok", "atoms": sorted(lines)}
    if proc.returncode != 0 and not out:
        sys.exit("model runner failed:\n" + proc.stderr[-4000:])
    return out


def panic_class(stderr):
    for needle, faults in PANIC_CLASSES:
        if needle in stderr:
            return needle, faults
    return None, set()


def classify(kernel, model, program_text):
    if model.get("status") == "fault" and model["fault"] in ABSTAIN:
        return "abstain"
    if "(hash " in program_text:
        return "unchecked"
    ks, ms = kernel["status"], model["status"]
    if ks == "panic" and kernel["code"] < 0 and program_text.count("(U ") > 1:
        return "environmental"
    if ks == "ok" and ms == "fault" and model["fault"] == "missingFile":
        return "external"
    if ks == "panic" and ms == "parse":
        return "agree"
    if ks == "timeout" and ms == "fuel":
        return "diverge"
    if ks == "panic" and ms == "fault":
        needle, faults = panic_class(kernel["stderr"])
        return "agree" if (needle is None or model["fault"] in faults) else "agree-fault-class-differs"
    if ks == "ok" and ms == "ok":
        return "agree" if kernel["atoms"] == model["atoms"] else "differ"
    return "differ"


def write_corpus(programs, corpus_dir, programs_file):
    corpus_dir.mkdir(parents=True, exist_ok=True)
    with open(programs_file, "w") as handle:
        for name, atoms in programs.items():
            text = "\n".join(atoms) + "\n"
            (corpus_dir / f"{name}.mm2").write_text(text)
            handle.write(f"=== {name}\n{text}")


def evaluate(programs, binary, lean_root, out_dir, fuel, timeout, wrapper, tag):
    corpus_dir = out_dir / f"corpus-{tag}"
    programs_file = out_dir / f"programs-{tag}.txt"
    write_corpus(programs, corpus_dir, programs_file)
    model = run_model(lean_root, programs_file, fuel, wrapper)
    report = {}
    for name, atoms in programs.items():
        kernel = run_kernel(binary, corpus_dir, name, timeout)
        result = model.get(name, {"status": "missing"})
        report[name] = {"class": classify(kernel, result, "\n".join(atoms)), "kernel": kernel,
                        "model": result, "program": atoms}
    return report


def shrink(name, atoms, binary, lean_root, out_dir, fuel, timeout, wrapper):
    """Drop top-level atoms while the difference persists."""
    current = list(atoms)
    while True:
        candidates = {}
        for index in range(len(current)):
            candidate = current[:index] + current[index + 1:]
            if candidate:
                candidates[f"{name}-drop{index}"] = candidate
        if not candidates:
            return current
        report = evaluate(candidates, binary, lean_root, out_dir, fuel, timeout, wrapper, f"shrink-{name}")
        still = [n for n, r in report.items() if r["class"] == "differ"]
        if not still:
            return current
        current = candidates[still[0]]


def split_atoms(text):
    """Top-level atoms of a program text."""
    atoms, depth, start = [], 0, None
    i = 0
    while i < len(text):
        c = text[i]
        if c == "(":
            if depth == 0:
                start = i
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0 and start is not None:
                atoms.append(text[start:i + 1])
                start = None
        elif depth == 0 and not c.isspace():
            j = i
            while j < len(text) and not text[j].isspace() and text[j] not in "()":
                j += 1
            atoms.append(text[i:j])
            i = j - 1
        i += 1
    return atoms


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--mork", required=True, type=Path)
    parser.add_argument("--lean-root", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--count", type=int, default=400)
    parser.add_argument("--seed", type=int, default=20261016)
    parser.add_argument("--fuel", type=int, default=200)
    parser.add_argument("--timeout", type=float, default=10.0)
    parser.add_argument("--fixtures", type=Path, nargs="*", default=[])
    parser.add_argument("--shrink", action="store_true")
    args = parser.parse_args()
    wrapper = os.environ.get(WRAPPER_ENV)

    rng = random.Random(args.seed)
    gen = Gen(rng)
    programs = {}
    for name, atoms in fault_fixtures().items():
        programs[f"fixture-{name}"] = atoms
    for directory in args.fixtures:
        for path in sorted(directory.glob("*.mm2")):
            programs[f"probe-{path.stem}"] = split_atoms(path.read_text())
    families = [gen.random_program] * 5 + [gen.numeric_program, gen.pure_program, gen.act_program,
                                          gen.order_program, gen.reflective_program,
                                          gen.unify_program, gen.unify_program]
    for index in range(args.count):
        family = families[index % len(families)]
        programs[f"gen-{index:04d}-{family.__name__}"] = family()

    args.out.mkdir(parents=True, exist_ok=True)
    report = evaluate(programs, args.mork, args.lean_root, args.out, args.fuel, args.timeout, wrapper, "main")
    if args.shrink:
        for name, entry in report.items():
            if entry["class"] == "differ":
                entry["shrunk"] = shrink(name, entry["program"], args.mork, args.lean_root, args.out,
                                         args.fuel, args.timeout, wrapper)
    counts = {}
    for entry in report.values():
        counts[entry["class"]] = counts.get(entry["class"], 0) + 1
    (args.out / "report.json").write_text(json.dumps(report, indent=1, sort_keys=True))
    (args.out / "summary.json").write_text(json.dumps({"programs": len(report), "classes": counts,
                                                       "seed": args.seed}, indent=1))
    print(json.dumps({"programs": len(report), "classes": counts}, indent=1))
    for name, entry in sorted(report.items()):
        if entry["class"] in ("differ", "agree-fault-class-differs"):
            print(f"--- {name} [{entry['class']}]")
            print("    program: " + " ".join(entry.get("shrunk", entry["program"])))
            print("    kernel:  " + json.dumps(entry["kernel"])[:400])
            print("    model:   " + json.dumps(entry["model"])[:400])


if __name__ == "__main__":
    main()
