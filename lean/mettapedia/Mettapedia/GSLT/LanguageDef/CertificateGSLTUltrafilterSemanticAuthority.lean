import Mettapedia.GSLT.LanguageDef.CertificateGSLTHeterogeneousAuthority
import Mettapedia.Logic.Metaphysics.UltrainfinitismCore

/-!
# Ultrafilter-relative semantic authorities for CertificateGSLTs

A proof checker remains finitary even when its selected meaning is evaluated
from an ultrafilter perspective.  This module supplies the missing semantic
weld.  A `PerspectivePresentation` gives every ground judgment a proposition
at every coordinate and proves each primitive rule sound coordinatewise.
Because every rule has a finite ordered premise list, filter closure combines
the almost-everywhere premise meanings into simultaneous premise meaning.
Coordinatewise rule soundness therefore lifts to `UltraTrue` rule soundness at
any selected ultrafilter.

The resulting `SemanticPresentation` is consumed by the ordinary heterogeneous
NIK authority generator.  The checker and certificate language do not inspect
the ultrafilter; only the independently supplied meaning face changes.  A
selected perspective is thus semantic authority data, not an operational
heuristic and not a definition of derivability.

This construction is deliberately one-way.  Coordinatewise soundness is a
strong sufficient condition for soundness at every ultrafilter.  Some rules
may instead be valid only at one non-principal perspective; those require a
direct proof of `RulesSound` for that selected meaning and are not mislabeled
as coordinatewise sound here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLTUltrafilterSemanticAuthority

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLTAuthorityFunctor
open Mettapedia.GSLT.LanguageDef.CertificateGSLTHeterogeneousAuthority
open Mettapedia.Logic.Metaphysics

universe uIndex

/-- Meaning of a judgment relative to one coordinate. -/
abbrev CoordinateMeaning (Index : Type uIndex) :=
  Index → Pattern → Prop

/-- Ultrafilter-relative meaning: the coordinate interpretation holds almost
everywhere in the selected perspective. -/
def UltraMeaning {Index : Type uIndex} (view : Ultrafilter Index)
    (meaningAt : CoordinateMeaning Index) (claim : Pattern) : Prop :=
  UltraTrue view (fun index => meaningAt index claim)

/-- Pull a coordinate semantics back along a reindexing map.  Claims are not
translated here; only the coordinate at which their independent meaning is
read changes. -/
def reindexMeaning {Source Target : Type uIndex}
    (coordinate : Source → Target) (meaningAt : CoordinateMeaning Target) :
    CoordinateMeaning Source :=
  fun source claim => meaningAt (coordinate source) claim

@[simp] theorem reindexMeaning_id {Index : Type uIndex}
    (meaningAt : CoordinateMeaning Index) :
    reindexMeaning id meaningAt = meaningAt :=
  rfl

@[simp] theorem reindexMeaning_comp
    {First Middle Last : Type uIndex}
    (first : First → Middle) (second : Middle → Last)
    (meaningAt : CoordinateMeaning Last) :
    reindexMeaning first (reindexMeaning second meaningAt) =
      reindexMeaning (second ∘ first) meaningAt :=
  rfl

/-- Selecting meaning commutes with reindexing the coordinate atlas.  This is
the naturality law that prevents a change of coordinates from changing an
ultrafilter-relative verdict. -/
theorem ultraMeaning_map
    {Source Target : Type uIndex} (coordinate : Source → Target)
    (view : Ultrafilter Source) (meaningAt : CoordinateMeaning Target)
    (claim : Pattern) :
    UltraMeaning (view.map coordinate) meaningAt claim ↔
      UltraMeaning view (reindexMeaning coordinate meaningAt) claim :=
  ultraTrue_map coordinate view (fun index => meaningAt index claim)

/-- Ultrafilter-relative meaning depends only on the eventually-equivalent
coordinate verdict. -/
theorem ultraMeaning_congr
    {Index : Type uIndex} (view : Ultrafilter Index)
    (first second : CoordinateMeaning Index) (claim : Pattern)
    (agreement : ∀ᶠ index in view,
      first index claim ↔ second index claim) :
    UltraMeaning view first claim ↔ UltraMeaning view second claim :=
  Filter.eventually_congr agreement

/-- At the free hyperfilter, changing a coordinate semantics on only finitely
many indices cannot change the selected meaning.  This is a semantic tail law,
not a claim that the free-ultrafilter verdict is computably decidable. -/
theorem ultraMeaning_hyperfilter_congr_of_finite_disagreement
    {Index : Type uIndex} [Infinite Index]
    (first second : CoordinateMeaning Index) (claim : Pattern)
    (finiteDisagreement :
      {index | ¬ (first index claim ↔ second index claim)}.Finite) :
    UltraMeaning (Filter.hyperfilter Index) first claim ↔
      UltraMeaning (Filter.hyperfilter Index) second claim := by
  classical
  apply ultraMeaning_congr
  have agreementSet := finiteDisagreement.compl_mem_hyperfilter
  have setsEqual :
      {index | ¬ (first index claim ↔ second index claim)}ᶜ =
        {index | first index claim ↔ second index claim} := by
    ext index
    simp
  rw [setsEqual] at agreementSet
  exact agreementSet

/-- A principal perspective recovers exactly its selected coordinate
semantics. -/
@[simp] theorem ultraMeaning_pure {Index : Type uIndex} (index : Index)
    (meaningAt : CoordinateMeaning Index) (claim : Pattern) :
    UltraMeaning (pure index) meaningAt claim ↔ meaningAt index claim :=
  ultraTrue_pure index (fun coordinate => meaningAt coordinate claim)

/-- All ultrafilter perspectives validate a claim exactly when every
coordinate validates it.  This is the robust, perspective-independent
envelope; it is stronger than validity at one selected view. -/
theorem all_ultraMeaning_iff {Index : Type uIndex}
    (meaningAt : CoordinateMeaning Index) (claim : Pattern) :
    (∀ view : Ultrafilter Index, UltraMeaning view meaningAt claim) ↔
      ∀ index, meaningAt index claim :=
  ultraTrue_all_iff (fun index => meaningAt index claim)

/-- Finitely many almost-everywhere facts hold simultaneously almost
everywhere.  Ordered premise occurrences are retained in the statement even
though semantic conjunction is proposition-valued. -/
theorem ultraTrue_forall_mem {Index : Type uIndex}
    (view : Ultrafilter Index) (meaningAt : CoordinateMeaning Index)
    (claims : List Pattern)
    (allTrue : ∀ claim, claim ∈ claims →
      UltraMeaning view meaningAt claim) :
    UltraTrue view
      (fun index => ∀ claim, claim ∈ claims → meaningAt index claim) := by
  induction claims with
  | nil =>
      exact Filter.Eventually.of_forall (by simp)
  | cons head tail inductionHypothesis =>
      have headTrue : UltraTrue view (fun index => meaningAt index head) :=
        allTrue head (by simp)
      have tailTrue :
          UltraTrue view
            (fun index => ∀ claim, claim ∈ tail → meaningAt index claim) :=
        inductionHypothesis (by
          intro claim membership
          exact allTrue claim (by simp [membership]))
      exact (headTrue.and tailTrue).mono (by
        rintro index ⟨headAt, tailAt⟩ claim membership
        rcases List.mem_cons.mp membership with rfl | tailMembership
        · exact headAt
        · exact tailAt claim tailMembership)

/-- Every primitive rule application preserves the coordinate semantics at
each coordinate. -/
abbrev CoordinateRulesSound {Index : Type uIndex}
    (object : CertificateGSLT.Object)
    (meaningAt : CoordinateMeaning Index) : Prop :=
  ∀ ruleInstance premises conclusion,
    RuleApplication object.definition ruleInstance premises conclusion →
      ∀ index,
        (∀ premise, premise ∈ premises → meaningAt index premise) →
          meaningAt index conclusion

/-- Coordinatewise rule soundness lifts to rule soundness at every selected
ultrafilter.  Finiteness enters only through the authored premise list. -/
theorem CoordinateRulesSound.ultra
    {Index : Type uIndex} {object : CertificateGSLT.Object}
    {meaningAt : CoordinateMeaning Index}
    (coordinateSound : CoordinateRulesSound object meaningAt)
    (view : Ultrafilter Index) :
    RulesSound object (UltraMeaning view meaningAt) := by
  intro ruleInstance premises conclusion application premisesMeaning
  have premisesTogether :=
    ultraTrue_forall_mem view meaningAt premises premisesMeaning
  exact premisesTogether.mono (by
    intro index premisesAt
    exact coordinateSound ruleInstance premises conclusion application index
      premisesAt)

/-- One CertificateGSLT presentation with an independently authored family of
coordinate semantics. -/
structure PerspectivePresentation (Index : Type uIndex) where
  object : CertificateGSLT.Object
  meaningAt : CoordinateMeaning Index
  rulesSoundAt : CoordinateRulesSound object meaningAt

namespace PerspectivePresentation

/-- Select one ultrafilter perspective and obtain a semantic presentation
accepted by the heterogeneous NIK authority generator. -/
def select {Index : Type uIndex} (presentation : PerspectivePresentation Index)
    (view : Ultrafilter Index) : SemanticPresentation where
  object := presentation.object
  Meaning := UltraMeaning view presentation.meaningAt
  rulesSound := presentation.rulesSoundAt.ultra view

/-- The selected presentation exposes precisely `UltraMeaning`; generated
derivability does not define this field. -/
@[simp] theorem select_Meaning {Index : Type uIndex}
    (presentation : PerspectivePresentation Index)
    (view : Ultrafilter Index) (claim : Pattern) :
    (presentation.select view).Meaning claim ↔
      UltraMeaning view presentation.meaningAt claim :=
  Iff.rfl

/-- At a principal view the selected presentation reduces to the named
coordinate semantics. -/
@[simp] theorem select_pure_Meaning {Index : Type uIndex}
    (presentation : PerspectivePresentation Index)
    (index : Index) (claim : Pattern) :
    (presentation.select (pure index)).Meaning claim ↔
      presentation.meaningAt index claim :=
  ultraMeaning_pure index presentation.meaningAt claim

end PerspectivePresentation

#print axioms ultraTrue_forall_mem
#print axioms ultraMeaning_map
#print axioms ultraMeaning_hyperfilter_congr_of_finite_disagreement
#print axioms CoordinateRulesSound.ultra
#print axioms PerspectivePresentation.select

end Mettapedia.GSLT.LanguageDef.CertificateGSLTUltrafilterSemanticAuthority
