import Mettapedia.TypeTheory.Models.RevisionedFamilies.ObservationSpaceBoundary
import Mettapedia.OSLF.Framework.WMCalculusBehavioralFamilyTransport

/-!
# Extensional type-space support is a strict quotient of WM observation

The staged-reflective candidate reads a type as a `Pattern → Prop` space.
For the multiplicity WM reading, its support projection factors through the
WM observational quotient and is surjective. It is not injective: two
different multiplicity observations may support the same extensional type.
Consequently dependent transport over candidate type spaces is strictly
weaker than dependent transport over the WM observational state quotient.
-/

open Mettapedia.TypeTheory.Calculi.StagedScopedReflective
set_option autoImplicit false

namespace Mettapedia.TypeTheory.Models.RevisionedFamilies.SupportQuotient

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Dynamics.SpaceQueryAlgebra
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusObservationalQuotient
open Mettapedia.OSLF.Framework.WMCalculusBehavioralFamilyTransport
open Mettapedia.PLN.WorldModel.WMCalculusAdditiveReading
open Mettapedia.PLN.WorldModel.WMCalculusNativeSpace
open Mettapedia.TypeTheory.Models.RevisionedFamilies.ObservationSpaceBoundary

/-- Forget multiplicity through the actual observational quotient, not by
choosing representatives of hidden WM states. -/
noncomputable def supportOnObsState
    (world : String → MSpace Pattern) (query : String → List Pattern) :
    ObsState (additiveReading (Ev := ℕ) world query) → Space :=
  Quotient.lift support
    (fun first second agree =>
      wmAgree_implies_same_support world query first second agree)

/-- Factoring through the quotient recovers the original support of every
concrete multiplicity state. -/
theorem supportOnObsState_classOf
    (world : String → MSpace Pattern) (query : String → List Pattern)
    (space : MSpace Pattern) :
    supportOnObsState world query
      (classOf (additiveReading (Ev := ℕ) world query) space) =
        support space :=
  rfl

/-- Every candidate extensional type space has a zero-or-one WM
representative; surjectivity does not preserve additive revision. -/
theorem supportOnObsState_surjective
    (world : String → MSpace Pattern) (query : String → List Pattern) :
    Function.Surjective (supportOnObsState world query) := by
  intro typeSpace
  refine ⟨classOf (additiveReading (Ev := ℕ) world query)
    (zeroOneLift typeSpace), ?_⟩
  simpa only [supportOnObsState_classOf] using
    support_zeroOneLift typeSpace

/-- The support projection discards a genuine, query-visible multiplicity
distinction even after WM states are quotiented by all their answers. -/
theorem supportOnObsState_not_injective
    (world : String → MSpace Pattern) (query : String → List Pattern) :
    ¬ Function.Injective (supportOnObsState world query) := by
  obtain ⟨first, second, sameSupport, notAgreeSpecial⟩ :=
    same_support_not_wmAgree
  have distinct : first ≠ second := by
    intro equal
    apply notAgreeSpecial
    rw [equal]
    exact (additiveReading (Ev := ℕ)
      (fun _ => first) (fun _ => ([] : List Pattern))).agree_refl .state second
  intro injective
  have sameClasses :
      classOf (additiveReading (Ev := ℕ) world query) first =
        classOf (additiveReading (Ev := ℕ) world query) second :=
    injective (by
      simpa only [supportOnObsState_classOf] using sameSupport)
  exact distinct ((spaceAgree_iff_eq world query first second).1
    ((classOf_eq_iff_agree (additiveReading (Ev := ℕ) world query)
      first second).1 sameClasses))

/-- A shared candidate type-space support can transport every family over
that support while failing to transport all families over the richer WM
observational quotient. -/
theorem supportFamilyTransport_not_reflecting_observation
    (world : String → MSpace Pattern) (query : String → List Pattern) :
    ∃ first second : MSpace Pattern,
      Nonempty (∀ P : Space → Type,
        P (support first) → P (support second)) ∧
      ¬ Nonempty (∀ P : ObsState (additiveReading (Ev := ℕ) world query) → Type,
        P (classOf (additiveReading (Ev := ℕ) world query) first) →
          P (classOf (additiveReading (Ev := ℕ) world query) second)) := by
  obtain ⟨first, second, sameSupport, notAgreeSpecial⟩ :=
    same_support_not_wmAgree
  have distinct : first ≠ second := by
    intro equal
    apply notAgreeSpecial
    rw [equal]
    exact (additiveReading (Ev := ℕ)
      (fun _ => first) (fun _ => ([] : List Pattern))).agree_refl .state second
  refine ⟨first, second,
    (all_raw_families_transport_iff_eq (support first) (support second)).2
      sameSupport, ?_⟩
  intro quotientTransport
  have agree := (agree_iff_all_quotient_families_transport
    (additiveReading (Ev := ℕ) world query) first second).2
      quotientTransport
  exact distinct ((spaceAgree_iff_eq world query first second).1 agree)

end Mettapedia.TypeTheory.Models.RevisionedFamilies.SupportQuotient
