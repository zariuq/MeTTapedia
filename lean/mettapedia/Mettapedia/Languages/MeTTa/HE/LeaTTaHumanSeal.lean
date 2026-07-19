import Mettapedia.Languages.MeTTa.HE.LeaTTaQueryObservationalAnchor

/-!
# Repaired LeaTTa human-spec seal

This module exposes the composed public boundary proved in the repaired
LeaTTa conformance tranche:

* matcher soundness and completeness against the executable-independent human
  matcher relation;
* merge soundness inside a reachable query state; and
* soundness of one successful equation-query work-item step.

The seal intentionally stops before recursive evaluation of the emitted work
item.  Recursive evaluator/call conformance is a separately named future
layer, not an implicit premise or conclusion of this theorem.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaHumanConformance

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open LeaTTaBridge

/-- **Composed repaired-LeaTTa human-spec seal.**  The first component is the
bidirectional observational matcher seal.  The second component says that
every work item emitted by one selected, capture-avoiding LeaTTa equation rule
realizes an executable-independent human equation-query step and preserves the
reachable binding invariant.

This statement covers matcher, merge, and equation-query-step conformance.  It
does not claim recursive evaluator or completed-call conformance. -/
theorem repairedLeaTTa_match_merge_equationQueryStep_seal
    (query pattern : Atom) :
    ((∀ {leaOut : Metta.Bindings},
        leaOut ∈ Metta.matchAtoms
            (toLeaTTaAtom pattern) (toLeaTTaAtom query) →
          ∃ humanOut,
            HumanMatchMergeSpec.MatchRel
                HumanMatchMergeSpec.equalityGroundedSemantic
                query pattern humanOut ∧
              LeaBindingSolutionTheoryEquiv humanOut leaOut) ∧
      (∀ {humanOut : Bindings},
        HumanMatchMergeSpec.MatchRel
            HumanMatchMergeSpec.equalityGroundedSemantic
            query pattern humanOut →
          VarsDisjoint query pattern →
            ∃ leaOut,
              leaOut ∈ Metta.matchAtoms
                  (toLeaTTaAtom pattern) (toLeaTTaAtom query) ∧
                LeaBindingSolutionTheoryEquiv humanOut leaOut)) ∧
    ∀ {humanIncoming : Bindings} {incoming : Metta.Bindings}
      {prev : Metta.Minimal.Stack} {counter : Nat}
      {rawLhs rawRhs : Metta.Atom} {item : Metta.Minimal.Item},
      LeaQueryOpBindingInvariant humanIncoming incoming →
      (Metta.Minimal.freshenRuleAvoiding counter
        (Metta.Minimal.queryOpAvoid prev (toLeaTTaAtom query) incoming)
        rawLhs rawRhs).1.1 = toLeaTTaAtom pattern →
      item ∈ Metta.Minimal.queryOpItemsOfRule
        prev (toLeaTTaAtom query) incoming counter (rawLhs, rawRhs) →
        ∃ merged humanMerged freshRhs,
          freshRhs =
              (Metta.Minimal.freshenRuleAvoiding counter
                (Metta.Minimal.queryOpAvoid prev
                  (toLeaTTaAtom query) incoming)
                rawLhs rawRhs).1.2 ∧
            item = Metta.Minimal.evalResult prev
              (Metta.instantiate merged freshRhs) merged ∧
            HumanEquationQueryStep query pattern humanIncoming humanMerged
              freshRhs (Metta.instantiate merged freshRhs) ∧
            LeaQueryOpBindingInvariant humanMerged merged := by
  refine ⟨humanLeaMatch_observational_conformance query pattern, ?_⟩
  intro humanIncoming incoming prev counter rawLhs rawRhs item
    hinvariant hfreshPattern hitem
  exact queryOpItemsOfRule_humanEquationQueryStep_sound
    hinvariant hfreshPattern hitem

end Mettapedia.Languages.MeTTa.HE.LeaTTaHumanConformance
