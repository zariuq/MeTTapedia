import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# PeTTa Answer Type

PeTTa's evaluation is nondeterministic: a single expression can reduce to
multiple values simultaneously (like Prolog's nondeterminism, or MeTTa's
`superpose`). We model this as `List Pattern` — an ordered list of answers.

## Design

- `Answers := List Pattern` — the nondeterministic result of evaluating a
  PeTTa expression. Order is deterministic (clause order, depth-first).
- `superpose alts` — inject a list of alternatives as answers.
- `collapse f alts` — flatMap: apply `f` to each alternative and collect
  all results (models Prolog's `findall/3` or MeTTa's `collapse`).
- `emptyAnswer` — failure / no solutions.
- `pureAnswer p` — exactly one answer.

## Alignment with MeTTa Spec and PeTTa Implementation

- MeTTa spec models answers as `List (Atom, Bindings)` pairs;
  for the type-free fragment we simplify to `List Pattern` with bindings
  already applied.
- PeTTa (Prolog transpiler): `superpose` → Prolog disjunction (`;`),
  `collapse` → `findall(X, Goal, Xs)`, `superpose` + `collapse` together
  implement nondeterminism.
- HE MeTTa: `superpose-bind` is the primitive nondeterminism instruction.

## References

- MeTTa spec: `trueagi-io.github.io/hyperon-experimental/metta/` §superpose
- PeTTa transpiler: `hyperon/PeTTa/transpiler.pl` (superpose_goals/findall)
-/

namespace Mettapedia.OSLF.PeTTa

open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Answer Type -/

/-- The nondeterministic result of evaluating a PeTTa expression.
    An ordered list of alternative values (deterministic order: clause order × depth-first). -/
abbrev Answers := List Pattern

/-! ## Basic Constructors -/

/-- No answers: failure / empty nondeterminism. -/
def emptyAnswer : Answers := []

/-- Exactly one answer. -/
def pureAnswer (p : Pattern) : Answers := [p]

/-- Inject a list of alternatives as answers.
    Models MeTTa's `superpose` / PeTTa's Prolog disjunction. -/
def superpose (alts : List Pattern) : Answers := alts

/-- Apply `f` to each answer and collect all results (flatMap).
    Models MeTTa's `collapse` / PeTTa's `findall`. -/
def collapse (f : Pattern → Answers) (alts : Answers) : Answers :=
  alts.flatMap f

/-! ## Basic Properties

All proofs are definitional (unfold to List operations). -/

@[simp]
theorem emptyAnswer_eq : emptyAnswer = ([] : List Pattern) := rfl

@[simp]
theorem pureAnswer_eq (p : Pattern) : pureAnswer p = [p] := rfl

@[simp]
theorem superpose_eq (alts : List Pattern) : superpose alts = alts := rfl

@[simp]
theorem collapse_eq (f : Pattern → Answers) (alts : Answers) :
    collapse f alts = alts.flatMap f := rfl

/-- Collapsing empty answers yields empty. -/
@[simp]
theorem collapse_empty (f : Pattern → Answers) : collapse f [] = [] := rfl

/-- Collapsing a pure answer applies `f` once. -/
@[simp]
theorem collapse_pure (f : Pattern → Answers) (p : Pattern) :
    collapse f [p] = f p := by simp [collapse]

/-- Membership in `collapse f alts` iff membership in some `f a`. -/
theorem mem_collapse {f : Pattern → Answers} {alts : Answers} {q : Pattern} :
    q ∈ collapse f alts ↔ ∃ a ∈ alts, q ∈ f a :=
  List.mem_flatMap

/-- Membership in `superpose alts` iff membership in `alts`. -/
@[simp]
theorem mem_superpose {alts : Answers} {q : Pattern} :
    q ∈ superpose alts ↔ q ∈ alts := Iff.rfl

/-- Any element of `alts` is an answer in `superpose alts`. -/
theorem mem_superpose_of_mem {alts : Answers} {p : Pattern} (h : p ∈ alts) :
    p ∈ superpose alts := h

/-- Superpose of nil is empty. -/
@[simp]
theorem superpose_nil : superpose [] = ([] : List Pattern) := rfl

/-- Superpose of cons: first element is always an answer. -/
theorem mem_superpose_head (p : Pattern) (ps : List Pattern) :
    p ∈ superpose (p :: ps) := List.mem_cons_self

/-! ## Summary

**0 sorries. 0 axioms.**

- `Answers := List Pattern` — nondeterministic answer set
- `emptyAnswer`, `pureAnswer`, `superpose`, `collapse` — core operations
- All operations reduce to `List` operations (definitionally transparent)
- `mem_collapse`, `mem_superpose` — membership characterizations
-/

end Mettapedia.OSLF.PeTTa
