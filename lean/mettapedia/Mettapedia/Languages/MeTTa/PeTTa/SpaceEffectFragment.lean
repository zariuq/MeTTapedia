import Mettapedia.Languages.ProcessCalculi.MORK.ExecutionBoundary
import Mettapedia.Languages.ProcessCalculi.MORK.MatchSpec
import Mettapedia.Languages.MeTTa.PeTTa.Effects

/-!
# PeTTa Space-Effect Fragment → MORK Source Rules

Defines MORK `SourceExecRule`s for `add-atom` and `remove-atom`, the two
stateful space operations that PeTTa exposes through `PeTTaCmd`.

These rules map the MeTTa-level commands to MORK sink templates:

- `(add-atom &self X)` → `[.remove cmd, .add X, .add ()]`
- `(remove-atom &self X)` → `[.remove cmd, .remove X, .add ()]`

The MORK execution infrastructure (sinks, `applySink`, `fireExecFact`) handles
these templates natively. The only gap that remains is the `matchAtom`
round-trip for compound patterns, which is an MM2 compiler invariant.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.SpaceEffectFragment

open Mettapedia.Languages.MeTTa.Core (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.MeTTa.PeTTa (unitAtom)

private abbrev ILPattern := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern

/-! ## Ground atoms -/

/-- The MORK atom for `()` (unit return value). -/
abbrev unitMorkAtom : Atom := morkPatternToAtom unitAtom

/-- `unitMorkAtom` is ground. -/
theorem unitMorkAtom_ground : isGroundAtom unitMorkAtom = true := by
  decide

/-! ## add-atom source rule -/

/-- The command pattern `(add-atom &self $x)` as a MORK atom with variable `x`. -/
abbrev addAtomCmdAtom : Atom :=
  morkPatternToAtom (.apply "add-atom" [.apply "&self" [], .fvar "x"])

/-- MORK source exec rule for `(add-atom &self X)`.

Template: remove the command expression, add the argument, add `()`.
This is structurally a degenerate unfold step: `[.remove, .add, .add]`. -/
def addAtomSourceExecRule : SourceExecRule where
  priority := 40
  name     := "add-atom"
  input    := .explicit [.btm addAtomCmdAtom]
  guards   := []
  tmpl     := mkTemplate [mkRemove addAtomCmdAtom,
                           mkAdd (morkPatternToAtom (.fvar "x")),
                           mkAdd unitMorkAtom]

theorem addAtomSourceExecRule_guards : addAtomSourceExecRule.guards = [] := rfl

/-! ## remove-atom source rule -/

/-- The command pattern `(remove-atom &self $x)` as a MORK atom with variable `x`. -/
abbrev removeAtomCmdAtom : Atom :=
  morkPatternToAtom (.apply "remove-atom" [.apply "&self" [], .fvar "x"])

/-- MORK source exec rule for `(remove-atom &self X)`.

Template: remove the command expression, remove the argument, add `()`.
The argument removal is the space-mutation side effect. -/
def removeAtomSourceExecRule : SourceExecRule where
  priority := 40
  name     := "remove-atom"
  input    := .explicit [.btm removeAtomCmdAtom]
  guards   := []
  tmpl     := mkTemplate [mkRemove removeAtomCmdAtom,
                           mkRemove (morkPatternToAtom (.fvar "x")),
                           mkAdd unitMorkAtom]

theorem removeAtomSourceExecRule_guards : removeAtomSourceExecRule.guards = [] := rfl

/-! ## matchAtom round-trip theorems

These prove the compound-pattern matching gap: `matchAtom` successfully matches
the command-pattern atoms against concrete command expressions, producing the
expected substitution. This was previously an MM2 compiler invariant expressed
as a hypothesis; now it's a proven theorem.

Strategy: construct explicit `MatchAtomRel` derivations (expr_cons / symbol /
var_fresh) and apply `matchAtom_complete`. -/

/-- `matchAtom` matches `addAtomCmdAtom` against `(add-atom &self p)`,
    binding `"x"` to `morkPatternToAtom p`. -/
theorem matchAtom_addAtomCmdAtom (p : ILPattern) :
    matchAtom [] addAtomCmdAtom
      (morkPatternToAtom (.apply "add-atom" [.apply "&self" [], p])) =
      some [("x", morkPatternToAtom p)] := by
  -- Unfold to concrete MORK atoms so MatchAtomRel can be constructed
  simp only [addAtomCmdAtom, morkPatternToAtom, morkPatternToAtom.morkPatternToAtomList]
  -- .expression [.symbol "add-atom", .expression [.symbol "&self"], .var "x"]
  -- vs
  -- .expression [.symbol "add-atom", .expression [.symbol "&self"], morkPatternToAtom p]
  exact matchAtom_complete
    (MatchAtomRel.expr_cons MatchAtomRel.symbol
      (MatchAtomRel.expr_cons
        (MatchAtomRel.expr_cons MatchAtomRel.symbol MatchAtomRel.expr_nil)
        (MatchAtomRel.expr_cons (MatchAtomRel.var_fresh rfl) MatchAtomRel.expr_nil)))

/-- `matchAtom` matches `removeAtomCmdAtom` against `(remove-atom &self p)`,
    binding `"x"` to `morkPatternToAtom p`. -/
theorem matchAtom_removeAtomCmdAtom (p : ILPattern) :
    matchAtom [] removeAtomCmdAtom
      (morkPatternToAtom (.apply "remove-atom" [.apply "&self" [], p])) =
      some [("x", morkPatternToAtom p)] := by
  simp only [removeAtomCmdAtom, morkPatternToAtom, morkPatternToAtom.morkPatternToAtomList]
  exact matchAtom_complete
    (MatchAtomRel.expr_cons MatchAtomRel.symbol
      (MatchAtomRel.expr_cons
        (MatchAtomRel.expr_cons MatchAtomRel.symbol MatchAtomRel.expr_nil)
        (MatchAtomRel.expr_cons (MatchAtomRel.var_fresh rfl) MatchAtomRel.expr_nil)))

/-! ## Source-rule firing theorems

These lift the matchAtom round-trips to the full `fireSourceRule` level:
when the command atom is in the workspace, the source rule fires and produces
the expected workspace transformation via `applySinks`. -/

/-- `(add-atom &self p)` fires at the source-rule level: when the command
    atom is in the workspace, `addAtomSourceExecRule` fires and produces
    the `applySinks` result with binding `"x" ↦ morkPatternToAtom p`. -/
theorem addAtom_fireSourceRule_mem (p : ILPattern)
    {workspace : Space}
    (hcmd_in : morkPatternToAtom (.apply "add-atom" [.apply "&self" [], p]) ∈ workspace) :
    applySinks workspace [("x", morkPatternToAtom p)] addAtomSourceExecRule.tmpl ∈
      fireSourceRule workspace addAtomSourceExecRule := by
  rw [fireSourceRule_no_guards _ _ addAtomSourceExecRule_guards]
  rw [List.mem_map]
  refine ⟨([("x", morkPatternToAtom p)],
    {morkPatternToAtom (.apply "add-atom" [.apply "&self" [], p])}), ?_, rfl⟩
  -- Show membership in matchInputSpec
  simp only [addAtomSourceExecRule, matchInputSpec, matchSourceFactors]
  -- Unfold the single-factor go
  show _ ∈ matchSourceFactors.go workspace [.btm addAtomCmdAtom] [] ∅
  simp only [matchSourceFactors.go, matchSourceFactor, Finset.sdiff_empty]
  apply List.mem_flatMap.mpr
  exact ⟨([("x", morkPatternToAtom p)],
    morkPatternToAtom (.apply "add-atom" [.apply "&self" [], p])),
    matchOneInSpace_mem [] addAtomCmdAtom workspace _ hcmd_in _
      (matchAtom_addAtomCmdAtom p),
    by simp⟩

/-- `(remove-atom &self p)` fires at the source-rule level. -/
theorem removeAtom_fireSourceRule_mem (p : ILPattern)
    {workspace : Space}
    (hcmd_in : morkPatternToAtom (.apply "remove-atom" [.apply "&self" [], p]) ∈ workspace) :
    applySinks workspace [("x", morkPatternToAtom p)] removeAtomSourceExecRule.tmpl ∈
      fireSourceRule workspace removeAtomSourceExecRule := by
  rw [fireSourceRule_no_guards _ _ removeAtomSourceExecRule_guards]
  rw [List.mem_map]
  refine ⟨([("x", morkPatternToAtom p)],
    {morkPatternToAtom (.apply "remove-atom" [.apply "&self" [], p])}), ?_, rfl⟩
  simp only [removeAtomSourceExecRule, matchInputSpec, matchSourceFactors]
  show _ ∈ matchSourceFactors.go workspace [.btm removeAtomCmdAtom] [] ∅
  simp only [matchSourceFactors.go, matchSourceFactor, Finset.sdiff_empty]
  apply List.mem_flatMap.mpr
  exact ⟨([("x", morkPatternToAtom p)],
    morkPatternToAtom (.apply "remove-atom" [.apply "&self" [], p])),
    matchOneInSpace_mem [] removeAtomCmdAtom workspace _ hcmd_in _
      (matchAtom_removeAtomCmdAtom p),
    by simp⟩

/-! ## Canaries -/

section Canaries
#check @addAtomSourceExecRule
#check @removeAtomSourceExecRule
#check @unitMorkAtom_ground
#check @addAtomSourceExecRule_guards
#check @removeAtomSourceExecRule_guards
#check @matchAtom_addAtomCmdAtom
#check @matchAtom_removeAtomCmdAtom
#check @addAtom_fireSourceRule_mem
#check @removeAtom_fireSourceRule_mem
end Canaries

/-! ## Axiom audit -/

section AxiomAudit
#print axioms matchAtom_addAtomCmdAtom
#print axioms matchAtom_removeAtomCmdAtom
#print axioms addAtom_fireSourceRule_mem
#print axioms removeAtom_fireSourceRule_mem
end AxiomAudit

end Mettapedia.Languages.MeTTa.PeTTa.SpaceEffectFragment
