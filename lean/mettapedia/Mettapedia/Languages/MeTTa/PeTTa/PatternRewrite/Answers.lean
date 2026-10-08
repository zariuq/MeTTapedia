import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Ordered results for the selected Pattern rewrite view

`RewriteResults` is the existing list-of-Pattern observation algebra, moved
from the core answer module. It preserves selection order and duplicate
occurrences. Its list constructors and collection laws describe the rewrite
view; the semantics of PeTTa's `superpose` and `collapse` is in
`DeclarativeSpec` and `Eval`, over `OSLFCore.Atom`.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.PatternRewrite

open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Answer Type -/

/-- Ordered results of the selected Pattern rewrite view.
    An ordered list of Pattern values, retaining duplicate occurrences. -/
abbrev RewriteResults := List Pattern

/-! ## Basic Constructors -/

/-- No answers: failure / empty nondeterminism. -/
def emptyAnswer : RewriteResults := []

/-- Exactly one answer. -/
def pureAnswer (p : Pattern) : RewriteResults := [p]

/-- Inject a list of alternatives as answers.
    This is the list algebra of the rewrite view, with no evaluation of its elements. -/
def alternatives (alts : List Pattern) : RewriteResults := alts

/-- Apply `f` to each answer and collect all results (flatMap).
    This operation concatenates result lists; guest `collapse` is specified by the whole-program judgment. -/
def collectResults (f : Pattern → RewriteResults) (alts : RewriteResults) : RewriteResults :=
  alts.flatMap f

/-! ## Basic Properties

All proofs are definitional (unfold to List operations). -/

@[simp]
theorem emptyAnswer_eq : emptyAnswer = ([] : List Pattern) := rfl

@[simp]
theorem pureAnswer_eq (p : Pattern) : pureAnswer p = [p] := rfl

@[simp]
theorem alternatives_eq (alts : List Pattern) : alternatives alts = alts := rfl

@[simp]
theorem collectResults_eq (f : Pattern → RewriteResults) (alts : RewriteResults) :
    collectResults f alts = alts.flatMap f := rfl

/-- Collapsing empty answers yields empty. -/
@[simp]
theorem collectResults_empty (f : Pattern → RewriteResults) : collectResults f [] = [] := rfl

/-- Collapsing a pure answer applies `f` once. -/
@[simp]
theorem collectResults_pure (f : Pattern → RewriteResults) (p : Pattern) :
    collectResults f [p] = f p := by simp [collectResults]

/-- Membership in `collectResults f alts` iff membership in some `f a`. -/
theorem mem_collectResults {f : Pattern → RewriteResults} {alts : RewriteResults} {q : Pattern} :
    q ∈ collectResults f alts ↔ ∃ a ∈ alts, q ∈ f a :=
  List.mem_flatMap

/-- Membership in `alternatives alts` iff membership in `alts`. -/
@[simp]
theorem mem_alternatives {alts : RewriteResults} {q : Pattern} :
    q ∈ alternatives alts ↔ q ∈ alts := Iff.rfl

/-- Any element of `alts` is an answer in `alternatives alts`. -/
theorem mem_alternatives_of_mem {alts : RewriteResults} {p : Pattern} (h : p ∈ alts) :
    p ∈ alternatives alts := h

/-- Superpose of nil is empty. -/
@[simp]
theorem alternatives_nil : alternatives [] = ([] : List Pattern) := rfl

/-- Superpose of cons: first element is always an answer. -/
theorem mem_alternatives_head (p : Pattern) (ps : List Pattern) :
    p ∈ alternatives (p :: ps) := List.mem_cons_self

end Mettapedia.Languages.MeTTa.PeTTa.PatternRewrite
