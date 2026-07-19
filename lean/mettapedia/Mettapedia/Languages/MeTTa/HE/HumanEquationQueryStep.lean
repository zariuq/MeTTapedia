import Mettapedia.Languages.MeTTa.HE.HumanMatchSolutionTheory

/-!
# Executable-independent equation-query steps

`HumanEquationQueryStep` is the human-specification boundary for one selected,
hygienically freshened equation rule.  It describes the match, ambient-binding
merge, and emitted right-hand-side observation.  It deliberately stops at the
work-item boundary: it neither claims nor assumes recursive evaluation of the
emitted atom.

The relation mentions neither executable matcher nor executable merger.  An
engine-specific conformance theorem is responsible for proving that its rule
selection and alpha-renaming produce the `freshPattern` and `freshRhs` supplied
here.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open LeaTTaBridge (HEBindingSatisfied applyClassSolution)

/-- One successful equation-query step from a selected, freshened rule.

`emitted` is observationally the freshened rule RHS under every model of the
merged human binding set.  This is the complete semantic content of the work
item produced by a successful query step; recursive evaluation belongs to a
separate evaluator-conformance judgment. -/
def HumanEquationQueryStep
    (query freshPattern : Atom)
    (incoming output : Bindings)
    (freshRhs emitted : Metta.Atom) : Prop :=
  ∃ matched : Bindings,
    LeaTTaBridge.VarsDisjoint query freshPattern ∧
      HumanMatchMergeSpec.MatchRel
        HumanMatchMergeSpec.equalityGroundedSemantic
        query freshPattern matched ∧
      HumanMatchMergeSpec.MergeRel
        HumanMatchMergeSpec.equalityGroundedSemantic
        incoming matched output ∧
      (∃ valuation : String → Metta.Atom,
        HEBindingSatisfied valuation output) ∧
      ∀ valuation : String → Metta.Atom,
        HEBindingSatisfied valuation output →
          applyClassSolution valuation emitted =
            applyClassSolution valuation freshRhs

/-! ## Boundary examples -/

/-- Positive: an equal-symbol rule can emit its unchanged RHS from empty
bindings. -/
example :
    HumanEquationQueryStep
      (.symbol "a") (.symbol "a")
      Bindings.empty Bindings.empty (.sym "result") (.sym "result") := by
  refine ⟨Bindings.empty,
    (by simp [LeaTTaBridge.VarsDisjoint, LeaTTaBridge.toLeaTTaAtom,
      Metta.Atom.vars]),
    HumanMatchMergeSpec.MatchRel.symSym "a"
      HumanMatchMergeSpec.semanticLoopFree_empty, ?_, ?_, ?_⟩
  · exact HumanMatchMergeSpec.MergeRel.mk
      (by simp [HumanMatchMergeSpec.constraints, Bindings.empty])
      HumanMatchMergeSpec.MergeConstraintsRel.nil
  · exact ⟨fun name => .var name, by
      simp [HEBindingSatisfied, Bindings.empty]⟩
  · intro valuation _
    rfl

/-- Negative: a successful equation-query step cannot disguise a mismatch
between distinct symbol heads. -/
theorem symbol_mismatch_not_humanEquationQueryStep
    {left right : String} (hne : left ≠ right)
    (incoming output : Bindings) (freshRhs emitted : Metta.Atom) :
    ¬HumanEquationQueryStep
      (.symbol left) (.symbol right)
      incoming output freshRhs emitted := by
  rintro ⟨matched, _hygienic, hmatch, _hmerge, _hsatisfiable, _hemitted⟩
  exact HumanMatchMergeSpec.symbol_mismatch_not_match
    hne matched hmatch

end Mettapedia.Languages.MeTTa.HE
