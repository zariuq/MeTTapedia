import Mettapedia.GSLT.Distinction.SpecSpace.ChuWitnessTopology
import Mettapedia.Logic.StoneGunkDuality
import Mathlib.Topology.Sets.Opens

/-!
# Formal locale of observable specification properties and Stone/gunk lift

A point-set space of syntactic specifications cannot by itself capture infinite or
ambient semantic profiles that are only ever probed through finite discriminator
observations. Passing to the **frame (locale) of witness-open sets**
`WitnessLocale C := TopologicalSpace.Opens (S, witnessTopology C)` makes finite
observations primary:

* `localePointOfSpec`: every concrete specification `s : S` determines a
  **completely prime filter** of witness-open sets (preserving finite meets and
  arbitrary joins).
* `localePoint_eq_iff_sameWitnesses`: two specifications define the same locale point
  iff they satisfy the exact same discriminator witnesses.
* `atomless_witnessAlgebra_perfect_stoneSpace`: importing
  `Mettapedia.Foundations.Gunk.isGunky_iff_perfect_stoneSpace`, whenever a Boolean
  algebra `B` of finitary specification properties is atomless (every finite spec
  description admits a further nontrivial distinction refinement), its Stone space
  `StoneSpace B` has **no isolated points** — no single finite witness conjunction
  isolates a maximal ambient specification.
* `symmetric_spec_automorphisms_nontrivial`: on a symmetric witness space, non-identity
  automorphisms preserve every open set's topological structure while moving individual
  specifications, witnessing connected-not-contractible symmetry inside spec space.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.SpecSpace

open TopologicalSpace
open Mettapedia.Foundations.Gunk

universe uS uW uB

/-! ## Completely prime filters (locale points) of the witness frame -/

section WitnessLocale

variable {S : Type uS} {W : Type uW} (C : SpecChuSpace S W)

/-- The **locale point** (completely prime filter of opens) induced by a concrete
specification `s : S` in the witness-open frame. -/
def localePointOfSpec (s : S) : Set (@Opens S (witnessTopology C)) :=
  {U | s ∈ (U : Set S)}

/-- A locale point contains the top open (`univ`). -/
theorem top_mem_localePoint (s : S) :
    (⊤ : @Opens S (witnessTopology C)) ∈ localePointOfSpec C s :=
  trivial

/-- A locale point is closed under binary meets (finite conjunctions of open properties). -/
theorem inf_mem_localePoint (s : S) (U V : @Opens S (witnessTopology C)) :
    U ⊓ V ∈ localePointOfSpec C s ↔
      U ∈ localePointOfSpec C s ∧ V ∈ localePointOfSpec C s :=
  Iff.rfl

/-- A locale point is **completely prime**: it contains an arbitrary join `sSup 𝒮` iff
it contains some member of `𝒮`. -/
theorem sSup_mem_localePoint (s : S) (𝒮 : Set (@Opens S (witnessTopology C))) :
    sSup 𝒮 ∈ localePointOfSpec C s ↔ ∃ U ∈ 𝒮, U ∈ localePointOfSpec C s := by
  let _ := witnessTopology C
  change s ∈ (sSup 𝒮 : Opens S) ↔ ∃ U ∈ 𝒮, s ∈ (U : Opens S)
  exact Opens.mem_sSup

/-- A locale point is upward-closed under open refinement. -/
theorem mono_localePoint (s : S) {U V : @Opens S (witnessTopology C)}
    (hle : U ≤ V) (hU : U ∈ localePointOfSpec C s) :
    V ∈ localePointOfSpec C s :=
  hle hU

/-- Two specifications induce the exact same locale point iff they realize the exact same
witnesses. -/
theorem localePoint_eq_iff_sameWitnesses (s₁ s₂ : S) :
    localePointOfSpec C s₁ = localePointOfSpec C s₂ ↔
      (∀ w : W, C.pass s₁ w ↔ C.pass s₂ w) := by
  let _ := witnessTopology C
  rw [← indistinguishable_iff_sameWitnesses C s₁ s₂]
  constructor
  · intro heq U hU
    have hmem : (⟨U, hU⟩ : Opens S) ∈ localePointOfSpec C s₁ ↔
        (⟨U, hU⟩ : Opens S) ∈ localePointOfSpec C s₂ := by
      rw [heq]
    exact hmem
  · intro hind
    ext U
    exact hind U.1 U.2

/-- A capability witness `w` defines an element of the witness locale. -/
def capabilityElement (w : W) : @Opens S (witnessTopology C) :=
  let _ := witnessTopology C
  ⟨capabilityOpen C w, isOpen_capabilityOpen C w⟩

theorem capabilityElement_mem_localePoint_iff (s : S) (w : W) :
    capabilityElement C w ∈ localePointOfSpec C s ↔ C.pass s w :=
  Iff.rfl

end WitnessLocale

/-! ## Stone duality & gunky (indefinitely refinable) specification algebras -/

section StoneLift

variable (B : Type uB) [BooleanAlgebra B]

/-- **Stone representation of a finitary witness algebra**: every Boolean algebra `B` of
decidable specification properties is order-isomorphic to the clopen algebra of its
Stone space `StoneSpace B`. -/
noncomputable def witnessAlgebraStoneRepr : B ≃o Clopens (StoneSpace B) :=
  stoneRepr B

/-- **Indefinite-refinement (gunk) boundary theorem**:
A Boolean algebra `B` of finitary specification properties is atomless (`IsGunky B` —
every consistent finite specification description admits a strictly finer consistent
split) if and only if its Stone space `StoneSpace B` is perfect (contains no isolated
specification point). -/
theorem atomless_witnessAlgebra_iff_perfect_stoneSpace :
    IsGunky B ↔ PerfectSpace (StoneSpace B) :=
  isGunky_iff_perfect_stoneSpace

/-- In an atomless finitary witness algebra, no single maximal specification is isolated
by a finite clopen neighborhood. -/
theorem no_isolated_spec_of_atomless (hgunk : IsGunky B) (p : StoneSpace B) :
    ¬ IsOpen ({p} : Set (StoneSpace B)) := by
  have hperf : PerfectSpace (StoneSpace B) := isGunky_iff_perfect_stoneSpace.mp hgunk
  have hnotIso := (perfectSpace_iff_forall_not_isolated.mp hperf) p
  rw [Filter.neBot_iff, Ne, ← isOpen_singleton_iff_punctured_nhds] at hnotIso
  exact hnotIso

end StoneLift

/-! ## Connected-not-contractible symmetry control on a witness space -/

namespace Controls

/-- A symmetric two-specification Chu space with two symmetric witnesses (`w₀`, `w₁`). -/
def symmetricChu : SpecChuSpace Bool Bool where
  pass s w := s = w

/-- The non-identity involution swapping both specs and witnesses is a Chu automorphism. -/
def swapChuAut : ChuTransform symmetricChu symmetricChu where
  onSpec := Bool.not
  onWitness := Bool.not
  adjoint s w := by
    change ((!s) = w) ↔ (s = (!w))
    cases s <;> cases w <;> decide

/-- **Nontrivial symmetry control**: `swapChuAut` is continuous, involutive (hence a
homeomorphism of the witness topology), and distinct from the identity Chu transform. -/
theorem symmetric_spec_automorphism_nontrivial :
    @Continuous Bool Bool (witnessTopology symmetricChu) (witnessTopology symmetricChu)
      swapChuAut.onSpec ∧
    (∀ s, swapChuAut.onSpec (swapChuAut.onSpec s) = s) ∧
    swapChuAut.onSpec ≠ (ChuTransform.id symmetricChu).onSpec := by
  refine ⟨chuTransform_continuous swapChuAut, Bool.not_not, ?_⟩
  intro heq
  have h := congrFun heq true
  exact Bool.noConfusion h

end Controls

end Mettapedia.GSLT.Distinction.SpecSpace
