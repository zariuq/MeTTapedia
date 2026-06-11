import Mettapedia.Logic.ConceptOntology.ConstructionBaseInheritance
import Mettapedia.Logic.InheritanceIntegration

/-!
# Construction-Base Inference Bridge

This module connects the construction-base `That’s All` / `Open World`
inheritance vocabulary to the exact concept-native PLN induction/abduction
bridges.

The point is narrow and theoremic:

* `inheritanceOpenWorld` is lifted to explicit disagreement in the exact
  inheritance-strength inputs consumed by the induction/abduction formulas.
* `inheritanceThatsAll`, together with prior agreement, yields gate-invariant
  concept-native induction/abduction strengths.
-/

namespace Mettapedia.Logic.ConceptOntology

open Mettapedia.Logic
open Mettapedia.Logic.WMPLNJustifiedTruthFunctions

universe u v w z

section GatewiseInference

variable {Carrier : Type u} {Obj : Type v} {Attr : Type w} {Gate : Type z}
variable [Fintype Gate] [Nonempty Gate] [Fintype Obj]

/-- `Open World` on an inheritance edge is exactly disagreement somewhere in the
strength inputs consumed by the concept-native inference bridge. -/
theorem inheritanceOpenWorld_iff_exists_strength_disagreement
    (J : Gate → AbstractInheritance.Interpretation Carrier Obj Attr)
    (sub super : Carrier) :
    inheritanceOpenWorld J sub super ↔
      ∃ g h : Gate,
        (Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV (J g) sub super).strength ≠
          (Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV (J h) sub super).strength := by
  classical
  constructor
  · intro hOpen
    have hNotAll :
        ¬ ∀ g h : Gate,
            Mettapedia.Logic.ExtensionalIntensionalDivergence.fullInheritanceStrength (J g) sub super =
              Mettapedia.Logic.ExtensionalIntensionalDivergence.fullInheritanceStrength (J h) sub super :=
      (inheritanceOpenWorld_iff_not_all_gates_agree (J := J) (sub := sub) (super := super)).1 hOpen
    by_contra hNo
    apply hNotAll
    intro g h
    by_contra hneq
    exact hNo ⟨g, h, by
      simpa [Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV,
        Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceWTV] using hneq⟩
  · rintro ⟨g, h, hneq⟩
    have hNotAll :
        ¬ ∀ g h : Gate,
            Mettapedia.Logic.ExtensionalIntensionalDivergence.fullInheritanceStrength (J g) sub super =
              Mettapedia.Logic.ExtensionalIntensionalDivergence.fullInheritanceStrength (J h) sub super := by
      intro hAll
      exact hneq (by
        simpa [Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV,
          Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceWTV] using hAll g h)
    exact
      (inheritanceOpenWorld_iff_not_all_gates_agree (J := J) (sub := sub) (super := super)).2
        hNotAll

/-- `That’s All` on an inheritance edge lifts directly to agreement of the exact
inheritance-strength TV inputs consumed by the concept-native inference bridge. -/
theorem inheritanceThatsAll_iff_all_strength_inputs_agree
    (J : Gate → AbstractInheritance.Interpretation Carrier Obj Attr)
    (sub super : Carrier) :
    inheritanceThatsAll J sub super ↔
      ∀ g h : Gate,
        (Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV (J g) sub super).strength =
          (Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV (J h) sub super).strength := by
  constructor
  · intro hAll g h
    simpa [Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV,
      Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceWTV] using
      (inheritanceThatsAll_iff_all_gates_agree (J := J) (sub := sub) (super := super)).1 hAll g h
  · intro hAll
    refine (inheritanceThatsAll_iff_all_gates_agree (J := J) (sub := sub) (super := super)).2 ?_
    intro g h
    simpa [Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV,
      Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceWTV] using hAll g h

/-- If the two premise inheritance edges are already gate-precise (`That’s All`)
and the three concept priors agree across gates, then the exact concept-native
induction strength is gate-invariant. This makes the induction readout genuinely
precise rather than merely pointwise. -/
theorem inheritanceTV_truthInduction_strength_gateInvariant_of_inheritanceThatsAll_and_priorAgreement
    (J : Gate → AbstractInheritance.Interpretation Carrier Obj Attr)
    (sub mid super : Carrier)
    (hAB : inheritanceThatsAll J sub mid)
    (hBC : inheritanceThatsAll J mid super)
    (hA : ∀ g h : Gate,
      Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J g) sub =
        Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J h) sub)
    (hB : ∀ g h : Gate,
      Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J g) mid =
        Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J h) mid)
    (hC : ∀ g h : Gate,
      Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J g) super =
        Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J h) super) :
    ∀ g h : Gate,
      (truthInduction
        (Mettapedia.Logic.ExtensionalIntensionalDivergence.stvToWMTruthValue
          (Mettapedia.Logic.ExtensionalIntensionalDivergence.conceptPriorTV (J g) sub))
        (Mettapedia.Logic.ExtensionalIntensionalDivergence.stvToWMTruthValue
          (Mettapedia.Logic.ExtensionalIntensionalDivergence.conceptPriorTV (J g) mid))
        (Mettapedia.Logic.ExtensionalIntensionalDivergence.stvToWMTruthValue
          (Mettapedia.Logic.ExtensionalIntensionalDivergence.conceptPriorTV (J g) super))
        (Mettapedia.Logic.ExtensionalIntensionalDivergence.stvToWMTruthValue
          (Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV (J g) sub mid))
        (Mettapedia.Logic.ExtensionalIntensionalDivergence.stvToWMTruthValue
          (Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV (J g) mid super))).s =
      (truthInduction
        (Mettapedia.Logic.ExtensionalIntensionalDivergence.stvToWMTruthValue
          (Mettapedia.Logic.ExtensionalIntensionalDivergence.conceptPriorTV (J h) sub))
        (Mettapedia.Logic.ExtensionalIntensionalDivergence.stvToWMTruthValue
          (Mettapedia.Logic.ExtensionalIntensionalDivergence.conceptPriorTV (J h) mid))
        (Mettapedia.Logic.ExtensionalIntensionalDivergence.stvToWMTruthValue
          (Mettapedia.Logic.ExtensionalIntensionalDivergence.conceptPriorTV (J h) super))
        (Mettapedia.Logic.ExtensionalIntensionalDivergence.stvToWMTruthValue
          (Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV (J h) sub mid))
        (Mettapedia.Logic.ExtensionalIntensionalDivergence.stvToWMTruthValue
          (Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV (J h) mid super))).s := by
  intro g h
  rw [Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV_truthInduction_strength_eq_conceptPrior
      (I := J g) (sub := sub) (mid := mid) (super := super)]
  rw [Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV_truthInduction_strength_eq_conceptPrior
      (I := J h) (sub := sub) (mid := mid) (super := super)]
  rw [(inheritanceThatsAll_iff_all_strength_inputs_agree (J := J) (sub := sub) (super := mid)).1 hAB g h]
  rw [(inheritanceThatsAll_iff_all_strength_inputs_agree (J := J) (sub := mid) (super := super)).1 hBC g h]
  rw [hA g h, hB g h, hC g h]

/-- The exact concept-native abduction strength is likewise gate-invariant once
the two explanatory inheritance edges are already precise and the three concept
priors agree across admissible gates. -/
theorem inheritanceTV_truthAbduction_strength_gateInvariant_of_inheritanceThatsAll_and_priorAgreement
    (J : Gate → AbstractInheritance.Interpretation Carrier Obj Attr)
    (left common right : Carrier)
    (hLeft : inheritanceThatsAll J left common)
    (hRight : inheritanceThatsAll J right common)
    (hA : ∀ g h : Gate,
      Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J g) left =
        Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J h) left)
    (hB : ∀ g h : Gate,
      Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J g) common =
        Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J h) common)
    (hC : ∀ g h : Gate,
      Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J g) right =
        Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J h) right) :
    ∀ g h : Gate,
      (truthAbduction
        (Mettapedia.Logic.ExtensionalIntensionalDivergence.stvToWMTruthValue
          (Mettapedia.Logic.ExtensionalIntensionalDivergence.conceptPriorTV (J g) left))
        (Mettapedia.Logic.ExtensionalIntensionalDivergence.stvToWMTruthValue
          (Mettapedia.Logic.ExtensionalIntensionalDivergence.conceptPriorTV (J g) common))
        (Mettapedia.Logic.ExtensionalIntensionalDivergence.stvToWMTruthValue
          (Mettapedia.Logic.ExtensionalIntensionalDivergence.conceptPriorTV (J g) right))
        (Mettapedia.Logic.ExtensionalIntensionalDivergence.stvToWMTruthValue
          (Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV (J g) left common))
        (Mettapedia.Logic.ExtensionalIntensionalDivergence.stvToWMTruthValue
          (Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV (J g) right common))).s =
      (truthAbduction
        (Mettapedia.Logic.ExtensionalIntensionalDivergence.stvToWMTruthValue
          (Mettapedia.Logic.ExtensionalIntensionalDivergence.conceptPriorTV (J h) left))
        (Mettapedia.Logic.ExtensionalIntensionalDivergence.stvToWMTruthValue
          (Mettapedia.Logic.ExtensionalIntensionalDivergence.conceptPriorTV (J h) common))
        (Mettapedia.Logic.ExtensionalIntensionalDivergence.stvToWMTruthValue
          (Mettapedia.Logic.ExtensionalIntensionalDivergence.conceptPriorTV (J h) right))
        (Mettapedia.Logic.ExtensionalIntensionalDivergence.stvToWMTruthValue
          (Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV (J h) left common))
        (Mettapedia.Logic.ExtensionalIntensionalDivergence.stvToWMTruthValue
          (Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV (J h) right common))).s := by
  intro g h
  rw [Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV_truthAbduction_strength_eq_conceptPrior
      (I := J g) (left := left) (common := common) (right := right)]
  rw [Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV_truthAbduction_strength_eq_conceptPrior
      (I := J h) (left := left) (common := common) (right := right)]
  rw [(inheritanceThatsAll_iff_all_strength_inputs_agree (J := J) (sub := left) (super := common)).1 hLeft g h]
  rw [(inheritanceThatsAll_iff_all_strength_inputs_agree (J := J) (sub := right) (super := common)).1 hRight g h]
  rw [hA g h, hB g h, hC g h]

end GatewiseInference

end Mettapedia.Logic.ConceptOntology
