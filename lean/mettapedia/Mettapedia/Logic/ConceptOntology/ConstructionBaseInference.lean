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
    exact hNo ⟨g, h, hneq⟩
  · rintro ⟨g, h, hneq⟩
    have hNotAll :
        ¬ ∀ g h : Gate,
            Mettapedia.Logic.ExtensionalIntensionalDivergence.fullInheritanceStrength (J g) sub super =
              Mettapedia.Logic.ExtensionalIntensionalDivergence.fullInheritanceStrength (J h) sub super := by
      intro hAll
      exact hneq (hAll g h)
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
    exact
      (inheritanceThatsAll_iff_all_gates_agree (J := J) (sub := sub) (super := super)).1 hAll g h
  · intro hAll
    refine (inheritanceThatsAll_iff_all_gates_agree (J := J) (sub := sub) (super := super)).2 ?_
    intro g h
    exact hAll g h

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

/-- Abduction asymmetry at the construction-base layer.

If the left explanatory edge is genuinely open-world, while the right
explanatory edge and the common/right priors are already gate-precise, then
abduction still inherits gate-disagreement provided the right explanatory edge
is not merely reproducing the common background rate. This is the exact
nondegenerate regime where abduction structurally lives in `Open World`. -/
theorem inheritanceTV_truthAbduction_strength_disagreement_of_left_openWorld_right_thatsAll_and_right_nonbackground
    (J : Gate → AbstractInheritance.Interpretation Carrier Obj Attr)
    (left common right : Carrier)
    (hLeftOpen : inheritanceOpenWorld J left common)
    (hRight : inheritanceThatsAll J right common)
    (hB : ∀ g h : Gate,
      Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J g) common =
        Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J h) common)
    (hC : ∀ g h : Gate,
      Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J g) right =
        Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J h) right)
    (hNondeg : ∃ g : Gate,
      Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J g) right ≠ 0 ∧
      Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J g) common ≠ 0 ∧
      Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J g) common ≠ 1 ∧
      (Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV (J g) right common).strength ≠
        Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J g) common) :
    ∃ g h : Gate,
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
          (Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV (J g) right common))).s
      ≠
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
  rcases
      (inheritanceOpenWorld_iff_exists_strength_disagreement (J := J) (sub := left) (super := common)).1
        hLeftOpen with
    ⟨g, h, hLeftNe⟩
  rcases hNondeg with ⟨g₀, hC0, hB0, hB1, hRightNonbackground⟩
  have hRightAll :
      ∀ g h : Gate,
        (Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV (J g) right common).strength =
          (Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV (J h) right common).strength :=
    (inheritanceThatsAll_iff_all_strength_inputs_agree (J := J) (sub := right) (super := common)).1 hRight
  have hCh_ne0 :
      Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J h) right ≠ 0 := by
    intro hz
    apply hC0
    calc
      Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J g₀) right
          =
        Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J h) right := hC g₀ h
      _ = 0 := hz
  have hBh_ne0 :
      Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J h) common ≠ 0 := by
    intro hz
    apply hB0
    calc
      Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J g₀) common
          =
        Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J h) common := hB g₀ h
      _ = 0 := hz
  have hBh_ne1 :
      Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J h) common ≠ 1 := by
    intro hz
    apply hB1
    calc
      Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J g₀) common
          =
        Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J h) common := hB g₀ h
      _ = 1 := hz
  have hRightNonbackground_h :
      (Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV (J h) right common).strength ≠
        Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J h) common := by
    intro hEq
    apply hRightNonbackground
    calc
      (Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV (J g₀) right common).strength
          =
        (Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV (J h) right common).strength :=
          hRightAll g₀ h
      _ =
        Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J h) common := hEq
      _ =
        Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J g₀) common := by
          symm
          exact hB g₀ h
  refine ⟨g, h, ?_⟩
  rw [Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV_truthAbduction_strength_eq_conceptPrior
      (I := J g) (left := left) (common := common) (right := right)]
  rw [Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV_truthAbduction_strength_eq_conceptPrior
      (I := J h) (left := left) (common := common) (right := right)]
  rw [hRightAll g h, hB g h, hC g h]
  exact
    Mettapedia.Logic.PLN.plnAbductionStrength_ne_of_left_strength_ne_of_nonbackground
      (s_AB₁ := (Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV (J g) left common).strength)
      (s_AB₂ := (Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV (J h) left common).strength)
      (s_CB := (Mettapedia.Logic.ExtensionalIntensionalDivergence.inheritanceTV (J h) right common).strength)
      (s_A₁ := Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J g) left)
      (s_A₂ := Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J h) left)
      (s_B := Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J h) common)
      (s_C := Mettapedia.Logic.IntensionalInheritance.Interpretation.finitePriorProb (J h) right)
      hBh_ne0 hBh_ne1 hCh_ne0 hRightNonbackground_h hLeftNe

end GatewiseInference

end Mettapedia.Logic.ConceptOntology
