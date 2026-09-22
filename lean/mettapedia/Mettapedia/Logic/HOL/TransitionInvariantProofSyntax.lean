import Mettapedia.Logic.HOL.TransitionInvariant
import Mettapedia.Logic.HOL.ProofSyntaxStructural

/-!
# Retained proof syntax for relation-refinement invariants

The semantic invariant theorem has a proposition-valued derivation.  This
module gives the corresponding proof tree explicitly, retaining its rule
nodes and its four hypothesis occurrences.  Consumers can therefore inspect,
compile, or transport the evidence without reconstructing an arbitrary tree
from proof-irrelevant derivability.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.TransitionInvariantProofSyntax

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.TransitionInvariant

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}
variable {Γ : Ctx Base} {σ : Ty Base}

/-- The retained proof tree for preservation transported along a refinement.
Its four local hypotheses are selected by position, so repeated formulas do
not introduce an implicit proof-search choice. -/
def preservationOfRefinement
    (source target : Const (σ ⇒ σ ⇒ .prop)) (predicate : Const (σ ⇒ .prop)) :
    ProofSyntax Const
      [refinementFormula (Γ := Γ) (.const source) (.const target),
        preservationFormula (.const target) (.const predicate)]
      (preservationFormula (.const source) (.const predicate)) := by
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  apply ProofSyntax.impI
  let localHypotheses : List (Formula Const (σ :: σ :: Γ)) :=
    [.app (.const predicate) (.var (.vs .vz)),
      .app (.app (.const source) (.var (.vs .vz))) (.var .vz)] ++
      weakenHyps (weakenHyps
        [refinementFormula (.const source) (.const target),
          preservationFormula (.const target) (.const predicate)])
  change ProofSyntax Const localHypotheses (.app (.const predicate) (.var .vz))
  have sourceHypothesis : ProofSyntax Const localHypotheses
      (.app (.app (.const source) (.var (.vs .vz))) (.var .vz)) := by
    simpa [localHypotheses] using
      (ProofSyntax.hyp (Const := Const) (Δ := localHypotheses)
        (⟨1, by simp [localHypotheses]⟩ : Fin localHypotheses.length))
  have predicateHypothesis : ProofSyntax Const localHypotheses
      (.app (.const predicate) (.var (.vs .vz))) := by
    simpa [localHypotheses] using
      (ProofSyntax.hyp (Const := Const) (Δ := localHypotheses)
        (⟨0, by simp [localHypotheses]⟩ : Fin localHypotheses.length))
  have refinement : ProofSyntax Const localHypotheses
      (refinementFormula (.const source) (.const target)) := by
    simpa [localHypotheses, weakenHyps, refinementFormula, weaken, rename,
      Rename.lift, Rename.weaken] using
      (ProofSyntax.hyp (Const := Const) (Δ := localHypotheses)
        (⟨2, by simp [localHypotheses, weakenHyps]⟩ : Fin localHypotheses.length))
  have preservation : ProofSyntax Const localHypotheses
      (preservationFormula (.const target) (.const predicate)) := by
    simpa [localHypotheses, weakenHyps, preservationFormula, weaken, rename,
      Rename.lift, Rename.weaken] using
      (ProofSyntax.hyp (Const := Const) (Δ := localHypotheses)
        (⟨3, by simp [localHypotheses, weakenHyps]⟩ : Fin localHypotheses.length))
  have refinementAtSource := ProofSyntax.allE
    (.var (.vs .vz) : Term Const (σ :: σ :: Γ) σ) refinement
  have refinementAtPair : ProofSyntax Const localHypotheses
      (.imp (.app (.app (.const source) (.var (.vs .vz))) (.var .vz))
        (.app (.app (.const target) (.var (.vs .vz))) (.var .vz))) := by
    simpa [refinementFormula, instantiate, subst, Subst.single, Subst.lift,
      weaken, rename, Rename.lift, Rename.weaken] using
      (ProofSyntax.allE (.var .vz) refinementAtSource)
  have preservationAtSource := ProofSyntax.allE
    (.var (.vs .vz) : Term Const (σ :: σ :: Γ) σ) preservation
  have preservationAtPair : ProofSyntax Const localHypotheses
      (.imp (.app (.app (.const target) (.var (.vs .vz))) (.var .vz))
        (.imp (.app (.const predicate) (.var (.vs .vz)))
          (.app (.const predicate) (.var .vz)))) := by
    simpa [preservationFormula, instantiate, subst, Subst.single, Subst.lift,
      weaken, rename, Rename.lift, Rename.weaken] using
      (ProofSyntax.allE (.var .vz) preservationAtSource)
  exact .impE (.impE preservationAtPair (.impE refinementAtPair sourceHypothesis))
    predicateHypothesis

/-- Erasure proves the same indexed extensional judgment as the earlier
proposition-valued theorem.  This is deliberately not a claim that erasure
retains the proof tree: structural retention is witnessed by `nodeCount` and
the explicit construction above. -/
theorem preservationOfRefinement_erases
    (source target : Const (σ ⇒ σ ⇒ .prop)) (predicate : Const (σ ⇒ .prop)) :
    (preservationOfRefinement (Γ := Γ) source target predicate).erase =
      ExtDerivation.ofBase
        (preservation_of_refinement (Γ := Γ) source target predicate) :=
  Subsingleton.elim _ _

/-- The outer rule is retained as data and can be inspected without reducing
the formulas or reconstructing a proof from derivability. -/
theorem preservationOfRefinement_root
    (source target : Const (σ ⇒ σ ⇒ .prop)) (predicate : Const (σ ⇒ .prop)) :
    (preservationOfRefinement (Γ := Γ) source target predicate).rootObservation =
      ⟨ProofSyntax.RuleTag.allI, none⟩ := rfl

/-- A hypothesis leaf cannot masquerade as the retained invariant proof's
root rule. -/
theorem preservationOfRefinement_root_not_hyp
    (source target : Const (σ ⇒ σ ⇒ .prop)) (predicate : Const (σ ⇒ .prop)) :
    (preservationOfRefinement (Γ := Γ) source target predicate).rootObservation ≠
      ⟨ProofSyntax.RuleTag.hyp, none⟩ := by
  rw [preservationOfRefinement_root]
  decide

#print axioms preservationOfRefinement
#print axioms preservationOfRefinement_erases
#print axioms preservationOfRefinement_root
#print axioms preservationOfRefinement_root_not_hyp

end Mettapedia.Logic.HOL.TransitionInvariantProofSyntax
