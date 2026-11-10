import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Dispatch
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFibre

/-!
# Licenses compose

For maps of frame instances `Φ : X → Y` and `Ψ : Y → Z` and their composite
`ContextualDependentFibre.FrameMap.comp Φ Ψ`:

* **reflection composes** (`reflects_comp`);
* **licenses compose** (`LicensedAt.comp`): `Φ` licensed at `K` and `Ψ` licensed at the translated
  store `Φ.store K` give the composite licensed at `K`. The factoring clause is stated for answers
  relative to a set of terms exactly so that the image of a source answer, which is most general only
  on the image, can be handed to the next license;
* **covering composes** (`CoversAt.comp`);
* on classes of stores (`LicensedOn.comp`) and on every store (`Licensed.comp`);
* so a chain of licensed edges dispatches to its cheapest end (`dispatch_admits_iff_comp`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)
open ContextualDependentFibre (FrameMap.comp)

universe uO uT uH uO' uT' uH' uO'' uT'' uH'' uOcc uS uF

namespace Translation.FrameMap

variable {Obj : Type uO} {Tm₁ : Obj → Type uT} {Hom₁ : Obj → Obj → Type uH}
  {Obj' : Type uO'} {Tm₂ : Obj' → Type uT'} {Hom₂ : Obj' → Obj' → Type uH'}
  {Obj'' : Type uO''} {Tm₃ : Obj'' → Type uT''} {Hom₃ : Obj'' → Obj'' → Type uH''}
  {X : Frames Tm₁ Hom₁} {Y : Frames Tm₂ Hom₂} {Z : Frames Tm₃ Hom₃}
  {Φ : FrameMap X Y} {Ψ : FrameMap Y Z}

theorem comp_store {a : Obj} (K : EquationStore (Tm₁ a)) :
    (FrameMap.comp Φ Ψ).store K = Ψ.store (Φ.store K) := by
  simp only [FrameMap.store, List.map_map]
  rfl

/-- **Reflection composes.** -/
theorem reflects_comp (first : Φ.Reflects) (second : Ψ.Reflects) : (FrameMap.comp Φ Ψ).Reflects :=
  fun same => first (second same)

/-- **Licenses compose.** -/
theorem LicensedAt.comp {a : Obj} {K : EquationStore (Tm₁ a)} (first : Φ.LicensedAt K)
    (second : Ψ.LicensedAt (Φ.store K)) : (FrameMap.comp Φ Ψ).LicensedAt K where
  factors := by
    intro T m answer solves factors
    have middle := first.factors T solves factors
    have last := second.factors _ (Φ.models solves) middle
    rw [Set.image_image] at last
    rw [comp_store]
    exact last
  reflects_solvable := by
    intro solvable
    rw [comp_store] at solvable
    exact first.reflects_solvable (second.reflects_solvable solvable)

/-- **Covering composes.** -/
theorem CoversAt.comp {a : Obj} {K : EquationStore (Tm₁ a)} (first : Φ.CoversAt K)
    (second : Ψ.CoversAt (Φ.store K)) : (FrameMap.comp Φ Ψ).CoversAt K := by
  intro b ρ solved
  rw [comp_store] at solved
  obtain ⟨c', g, r, gSolves, gThrough⟩ := second b ρ solved
  obtain ⟨c, f, r', fSolves, fThrough⟩ := first c' g gSolves
  refine ⟨c, f, Z.comp r (Ψ.hom r'), fSolves, fun t => ?_⟩
  have outer := gThrough (Φ.tm t)
  rw [Z.act_comp] at outer
  have inner : Z.E (Z.act (Ψ.hom g) (Ψ.tm (Φ.tm t)))
      (Z.act (Ψ.hom r') (Z.act (Ψ.hom (Φ.hom f)) (Ψ.tm (Φ.tm t)))) :=
    (Z.equivalence _).trans ((Z.equivalence _).symm (Ψ.act g (Φ.tm t)))
      ((Z.equivalence _).trans (Ψ.preserves (fThrough t)) (Ψ.tm_act_comp r' (Φ.hom f) (Φ.tm t)))
  show Z.E (Z.act ρ (Ψ.tm (Φ.tm t))) (Z.act (Z.comp (Z.comp r (Ψ.hom r')) (Ψ.hom (Φ.hom f)))
    (Ψ.tm (Φ.tm t)))
  rw [Z.act_comp, Z.act_comp]
  exact (Z.equivalence b).trans outer (Z.preserves r inner)

/-- **Licenses on classes compose**, when the first map sends the first class into the second. -/
theorem LicensedOn.comp {D : (a : Obj) → EquationStore (Tm₁ a) → Prop}
    {D' : (b : Obj') → EquationStore (Tm₂ b) → Prop} (first : Φ.LicensedOn D)
    (second : Ψ.LicensedOn D') (into : ∀ a K, D a K → D' (Φ.obj a) (Φ.store K)) :
    (FrameMap.comp Φ Ψ).LicensedOn D :=
  fun a K inside => (first a K inside).comp (second _ _ (into a K inside))

/-- **Licenses on every store compose.** -/
theorem Licensed.comp (first : Φ.Licensed) (second : Ψ.Licensed) : (FrameMap.comp Φ Ψ).Licensed :=
  fun a K => (first a K).comp (second _ _)

section Step

variable {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}

/-- **Dispatch along a chain of two licensed edges**: a step over the top `Z` whose firing is the
image of a store of the bottom `X` is decided by the bottom, through the middle's license on the
translated store. -/
theorem dispatch_admits_iff_comp (first : Φ.Reflects) (second : Ψ.Reflects)
    (P : Step Z O State Firing) [P.Guarded] {s : State} {f : Firing s} (d : (FrameMap.comp Φ Ψ).Dispatched P f)
    (licensedFirst : Φ.LicensedAt d.problem) (licensedSecond : Ψ.LicensedAt (Φ.store d.problem))
    (decides : X.Decides d.problem) :
    P.Admits f ↔ P.Shapes f ∧
      Enabled (fun _ : O => ()) (P.present s) ((P.selection f).commit (T := Unit)) ∧
      X.Solvable d.problem ∧ X.Entails d.problem (fun _ g => X.Models g d.guards) :=
  dispatch_admits_iff (reflects_comp first second) P d (licensedFirst.comp licensedSecond) decides

end Step

end Translation.FrameMap

#print axioms Translation.FrameMap.comp_store
#print axioms Translation.FrameMap.reflects_comp
#print axioms Translation.FrameMap.LicensedAt.comp
#print axioms Translation.FrameMap.CoversAt.comp
#print axioms Translation.FrameMap.LicensedOn.comp
#print axioms Translation.FrameMap.Licensed.comp
#print axioms Translation.FrameMap.dispatch_admits_iff_comp

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
