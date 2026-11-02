import Mettapedia.Languages.Metamath.MM0Transfer.Identification

/-!
# Source distinctness projection and identification controls

The positive control derives a statement from an original mixed-distinctness
axiom and then identifies its two regular parameters. Negative controls
retain mixed/bound exclusions and expose the necessity of the axiom and
essential-hypothesis profiles. These are source-judgment controls, not a
concrete database or Haskell-converter qualification.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM0Transfer.Controls

open _root_.Metamath
open Mettapedia.Languages.Metamath.InferenceSemanticFiniteSupport
  (renameFormula TypePreserving)
open DistinctnessProjection Identification

def boundSort (sort : CN) : Prop := sort = "setvar"
instance (sort : CN) : Decidable (boundSort sort) := inferInstanceAs (Decidable (sort = "setvar"))
def boundX : VR := ⟨"setvar", 0⟩
def boundY : VR := ⟨"setvar", 1⟩
def regularA : VR := ⟨"wff", 0⟩
def regularB : VR := ⟨"wff", 1⟩

def base : Statement :=
  ⟨⟨[], DJ.mk' [(boundX, regularA)]⟩,
    ("|-", [.var boundX, .var regularA, .var regularB])⟩

def baseAxioms (statement : Statement) : Prop := statement = base

def sourceContext : Context :=
  ⟨[], DJ.mk' [(boundX, regularA), (regularA, regularB)]⟩

theorem base_profile : AxiomProfile boundSort baseAxioms where
  noBoundConclusion := by
    intro statement accepted
    cases accepted
    decide
  distinctHasBound := by
    intro statement accepted left right pair
    cases accepted
    rcases pair.2 with present | present
    · have same := Prod.mk.inj (List.mem_singleton.mp present)
      rcases same with ⟨rfl, rfl⟩
      exact .inl rfl
    · have same := Prod.mk.inj (List.mem_singleton.mp present)
      rcases same with ⟨rfl, rfl⟩
      exact .inr rfl
  mandatoryDistinct := by
    intro statement accepted left right pair
    cases accepted
    rcases pair.2 with present | present
    · have same := Prod.mk.inj (List.mem_singleton.mp present)
      rcases same with ⟨rfl, rfl⟩
      change boundX ∈ [boundX, regularA, regularB] ∧ regularA ∈ [boundX, regularA, regularB]
      simp
    · have same := Prod.mk.inj (List.mem_singleton.mp present)
      rcases same with ⟨rfl, rfl⟩
      change regularA ∈ [boundX, regularA, regularB] ∧ boundX ∈ [boundX, regularA, regularB]
      simp

theorem source_derivation : Provable baseAxioms sourceContext base.fmla := by
  apply Provable.mono (Γ₁ := base.ctx) (Γ₂ := sourceContext) (fun _ => id)
    ⟨fun _ => id, ?_⟩ (Provable.ax_self baseAxioms rfl)
  intro left right pair
  refine ⟨pair.1, ?_⟩
  rcases pair.2 with present | present
  · exact .inl (List.mem_cons.mpr (.inl (List.mem_singleton.mp present)))
  · exact .inr (List.mem_cons.mpr (.inl (List.mem_singleton.mp present)))

def identifyRegular (reference : VR) : VR :=
  if reference.type = "wff" then regularA else reference

theorem identification_type_preserving : TypePreserving identifyRegular := by
  intro reference
  by_cases regular : reference.type = "wff"
  · simp [identifyRegular, regular, regularA]
  · simp [identifyRegular, regular]

theorem regular_parameters_identified : identifyRegular regularA = identifyRegular regularB :=
  rfl

theorem original_partition_refused :
    checkPartition [(boundX, regularA), (regularA, regularB)] identifyRegular = false := by
  decide

theorem retained_partition_accepted :
    checkPartition [(boundX, regularA)] identifyRegular = true := by
  decide

theorem projected_partition_valid :
    Valid (projectDJ boundSort sourceContext.dj) identifyRegular := by
  intro left right pair
  rcases pair.1.2 with present | present
  · rcases List.mem_cons.mp present with mixed | regular
    · rcases Prod.mk.inj mixed with ⟨rfl, rfl⟩
      decide
    · rcases Prod.mk.inj (List.mem_singleton.mp regular) with ⟨rfl, rfl⟩
      exact False.elim (by simpa [boundSort, regularA, regularB] using pair.2)
  · rcases List.mem_cons.mp present with mixed | regular
    · rcases Prod.mk.inj mixed with ⟨rfl, rfl⟩
      decide
    · rcases Prod.mk.inj (List.mem_singleton.mp regular) with ⟨rfl, rfl⟩
      exact False.elim (by simpa [boundSort, regularA, regularB] using pair.2)

/-- An original base proof, not a newly admitted axiom, supplies the identified
derived schema instance. Its mixed dependency remains present. -/
theorem actual_derived_identification_instance :
    Provable baseAxioms
      (imageContext (projectContext boundSort sourceContext)
        identifyRegular projected_partition_valid)
      (renameFormula identifyRegular base.fmla) :=
  derived_partition_instance base_profile (by intro formula present; cases present)
    source_derivation identifyRegular identification_type_preserving projected_partition_valid

theorem mixed_pair_retained :
    projectDJ boundSort sourceContext.dj boundX regularA := by
  exact ⟨⟨by decide, .inl (by simp)⟩, .inl rfl⟩

theorem mixed_pair_cannot_be_identified :
    ¬ Valid (projectDJ boundSort sourceContext.dj) (fun _ => boundX) := by
  intro valid
  exact valid _ _ mixed_pair_retained rfl

theorem bound_pair_cannot_be_identified :
    checkPartition [(boundX, boundY)] (fun _ => boundX) = false := by
  decide

/-- Deleting a regular/regular restriction on a base axiom is not licensed by
the projection theorem's syntactic premise. -/
def regularRestrictedAxiom : Statement :=
  ⟨⟨[], DJ.mk' [(regularA, regularB)]⟩,
    ("|-", [.var regularA, .var regularB])⟩

theorem regular_restricted_base_refused :
    ¬ AxiomProfile boundSort (fun statement => statement = regularRestrictedAxiom) := by
  intro profile
  have pair : regularRestrictedAxiom.ctx.dj regularA regularB := by
    exact ⟨by decide, .inl (by simp)⟩
  have bound := profile.distinctHasBound regularRestrictedAxiom rfl _ _ pair
  simp [boundSort, regularA, regularB] at bound

def falseBoundHypothesis : Formula := ("setvar", [.const "not-a-variable"])
def falseBoundContext : Context := ⟨[falseBoundHypothesis], DJ.mk' []⟩

theorem bound_hypothesis_is_derivable :
    Provable (fun _ => False) falseBoundContext falseBoundHypothesis :=
  .hyp _ (by simp [falseBoundContext])

theorem bound_hypothesis_is_not_variable :
    ¬ ∃ reference : VR, falseBoundHypothesis = reference.vhyp := by
  rintro ⟨reference, same⟩
  have symbols := congrArg Prod.snd same
  cases symbols

/-- Bound-sort atomicity really needs the essential-hypothesis premise. -/
theorem essential_hypothesis_profile_necessary :
    boundSort falseBoundHypothesis.1 ∧
      Provable (fun _ => False) falseBoundContext falseBoundHypothesis ∧
      ¬ ∃ reference : VR, falseBoundHypothesis = reference.vhyp :=
  ⟨rfl, bound_hypothesis_is_derivable, bound_hypothesis_is_not_variable⟩

end Mettapedia.Languages.Metamath.MM0Transfer.Controls
