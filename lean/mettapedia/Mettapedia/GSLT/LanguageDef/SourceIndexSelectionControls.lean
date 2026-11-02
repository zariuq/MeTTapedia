import Mettapedia.Logic.HOL.IndexedContainerIndexPrograms
import Mettapedia.Logic.HOL.OrderedConstructorSelectedExistence
import Mettapedia.GSLT.LanguageDef.DirectPositionSelectionControls

/-!
# Source index beta and selected existential child controls

The mixed List/Vector code keeps its outer data index across both shape
binders and its inner data binder. All four actual compiled index programs
produce retained beta evidence. A wrong outer/inner index is refused in the
independent natural model. The admitted Cons example uses generated source
selection and retains child evidence under that same existential slot.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.SourceIndexSelectionControls

open Mettapedia.Logic.HOL
open IndexedContainerPositionTerms FiniteConstructorEncoding CurriedPredicates OrderedPositionPrograms SuccessorOrder

namespace Mixed

open IndexedContainerPositionTermsControls
open DirectPositionSelectionControls.Mixed (context substitution arguments assumptions principle onePositive)

def program (ordinal : Nat) (inside : ordinal < (Reading.directFlags mixedCode).length) :=
  (reading.compile mixedCode substitution).get ⟨ordinal, by rw [Reading.compile_length]; exact inside⟩

def beta (ordinal : Nat) (inside : ordinal < (Reading.directFlags mixedCode).length) :
    ProofSyntax Symbol [] (.eq (applyFields _ (program ordinal inside).2 arguments)
      (Reading.sourceIndex (reading := reading) mixedCode substitution arguments ordinal inside)) :=
  (Reading.segmentIndexEvidence (reading := reading) mixedCode substitution arguments ordinal (program ordinal inside)
    (List.getElem?_eq_getElem _) _ (Reading.sourceIndexAt_sourceIndex (reading := reading) mixedCode substitution arguments ordinal inside)).val

theorem beta_free (ordinal : Nat) (inside : ordinal < (Reading.directFlags mixedCode).length) :
    (beta ordinal inside).FunctionExtensionalityFree :=
  (Reading.segmentIndexEvidence (reading := reading) mixedCode substitution arguments ordinal (program ordinal inside)
    (List.getElem?_eq_getElem _) _ (Reading.sourceIndexAt_sourceIndex (reading := reading) mixedCode substitution arguments ordinal inside)).property

def firstBeta := beta 0 (by decide)
def listBeta := beta 1 (by decide)
def vectorBeta := beta 2 (by decide)
def lastBeta := beta 3 (by decide)

theorem exact_source_indices :
    [Reading.sourceIndexAt (reading := reading) mixedCode substitution arguments 0,
      Reading.sourceIndexAt (reading := reading) mixedCode substitution arguments 1,
      Reading.sourceIndexAt (reading := reading) mixedCode substitution arguments 2,
      Reading.sourceIndexAt (reading := reading) mixedCode substitution arguments 3] =
    [some (.var (.vs (.vs (.vs .vz)))), some (.var (.vs (.vs (.vs .vz)))),
      some (.var (.vs (.vs (.vs .vz)))), some (.var (.vs .vz))] := rfl

theorem missing_source_segment : Reading.sourceIndexAt (reading := reading) mixedCode substitution arguments 4 = none := rfl

def first := Reading.directSourceSelectedExists (reading := reading) mixedCode substitution arguments 0
  (by decide) zero successor principle onePositive
def last := Reading.directSourceSelectedExists (reading := reading) mixedCode substitution arguments 3
  (by decide) zero successor principle onePositive

theorem first_free : first.FunctionExtensionalityFree := by
  apply Reading.directSourceSelectedExists_free
  · trivial
  · exact lessNext_free _ _

theorem last_free : last.FunctionExtensionalityFree := by
  apply Reading.directSourceSelectedExists_free
  · trivial
  · exact lessNext_free _ _

def world : model.Valuation context
  | _, .vz => ULift.up 23
  | _, .vs .vz => ULift.up 7
  | _, .vs (.vs .vz) => ULift.up 11
  | _, .vs (.vs (.vs .vz)) => ULift.up 3

theorem first_beta_valid : (model.denote
    (.eq (applyFields _ (program 0 (by decide)).2 arguments)
      (Reading.sourceIndex (reading := reading) mixedCode substitution arguments 0 (by decide))) world).down :=
  Soundness.extDerivation_sound firstBeta.erase (model.functionsRespectEqv_of_fullDomains full)
    (by intro type index; exact full type (world index)) (by intro _ impossible; nomatch impossible)

theorem wrong_inner_index_refused : ¬ Nonempty (ProofSyntax Symbol []
    (.eq (applyFields _ (program 0 (by decide)).2 arguments) (.var (.vs .vz)))) := by
  rintro ⟨proof⟩
  have incorrect := Soundness.extDerivation_sound proof.erase (M := model) (ρ := @world)
    (model.functionsRespectEqv_of_fullDomains full)
    (by intro type index; exact full type (world index)) (by intro _ impossible; nomatch impossible)
  have correct := first_beta_valid
  change _ = ULift.up (7 : Nat) at incorrect
  change _ = ULift.up (3 : Nat) at correct
  have impossible : (3 : Nat) = 7 := congrArg ULift.down (correct.symm.trans incorrect)
  omega

end Mixed

namespace Cons

open AdmittedContainerHOL AdmittedContainerGeneratedControls
open AdmittedContainerInductionControls (initial bottom ctor motive)
open AdmittedChildPremiseControls (context zero successor constructors plans sourceArguments arguments children target
  assumptions peano conditionProof allowed)

noncomputable section

def sourceFormula : Formula Symbol context := selectedExists zero successor 0
  (fieldTerms _ (reading.compile (codeAt reading (codes block registered) consOccurrence) initial) Subst.id sourceArguments)
  Subst.id (Reading.directSourceIndex (reading := reading)
    (codeAt reading (codes block registered) consOccurrence) initial sourceArguments 0 (by decide))

def sourceSelected : ProofSyntax Symbol assumptions sourceFormula :=
  Reading.directSourceSelectedExists (reading := reading)
    (codeAt reading (codes block registered) consOccurrence) initial sourceArguments 0 (by decide)
    zero successor peano.induction (lessNext successor target)

theorem sourceSelected_free : sourceSelected.FunctionExtensionalityFree := by
  apply Reading.directSourceSelectedExists_free
  · exact AdmittedChildPremiseControls.peano_free.2.2
  · exact lessNext_free _ _

def present : ProofSyntax Symbol assumptions
    (selectedExists zero successor 0 (fieldTerms _ (plans consOccurrence) Subst.id arguments) Subst.id target) := by
  have same : sourceFormula = selectedExists zero successor 0
      (fieldTerms _ (plans consOccurrence) Subst.id arguments) Subst.id target :=
    eq_of_heq (stagedHEq% sourceFormula, selectedExists zero successor 0
      (fieldTerms _ (plans consOccurrence) Subst.id arguments) Subst.id target)
  exact ProofSyntax.castIndices rfl same sourceSelected

theorem present_free : present.FunctionExtensionalityFree := by
  unfold present
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact sourceSelected_free

def child := IndexedConstructorGuards.PositionPrograms.selectedChildExistsFromLookup
  constructors zero successor plans bottom ctor motive consOccurrence arguments children 0 target
  peano conditionProof allowed present

theorem child_free : child.FunctionExtensionalityFree := by
  apply IndexedConstructorGuards.PositionPrograms.selectedChildExistsFromLookup_free
  · exact AdmittedChildPremiseControls.peano_free
  · exact AdmittedChildPremiseControls.conditionProof_free
  · exact AdmittedChildPremiseControls.allowed_free
  · exact present_free

theorem child_valid : (model.denote
    (IndexedConstructorGuards.PositionPrograms.selectedChildExists
      constructors zero successor plans bottom ctor motive consOccurrence arguments children 0 target)
    AdmittedChildPremiseModelControls.world).down :=
  Soundness.extDerivation_sound child.erase (model.functionsRespectEqv_of_fullDomains full)
    (by intro type index; exact full type (AdmittedChildPremiseModelControls.world index))
    AdmittedChildPremiseModelControls.assumptions_realizable

end
end Cons

#print axioms Mixed.beta_free
#print axioms Mixed.wrong_inner_index_refused
#print axioms Cons.child_free
#print axioms Cons.child_valid

end Mettapedia.GSLT.LanguageDef.SourceIndexSelectionControls
