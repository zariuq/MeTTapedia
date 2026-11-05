import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeSourceLogicalRows
import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorEvidenceModel
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorAllEvidence

/-!
# Complete-source case application controls

The supplied case variables retain the full eight- and ten-binder source
contexts. Actual source-domain checks reject reordered argument carriers;
omitting All-W leaves a function rather than a completed result. The
nonvacuity model retains natural indices, Boolean fields, lists and tree
evidence and the independently realized original computation operations.
Case functions remain explicitly supplied inputs, not installed eliminators.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeSourceCaseControls
open Mettapedia.Logic Mettapedia.Logic.HOL Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation TypedEquality.Annotated AnnotatedPredicateReading
open IndexedVectorTreeNativeSourceCaseApplication
open Native
namespace Rows
export IndexedVectorTreeNativeSourceLogicalRows
  (solvedAmbient branchFields branchLength branchAmbient fieldCarrier branch_all_domain
    solved_field_domain vector_field_domain length_field_domain
    solved_original_ambient_telescope branch_original_ambient_telescope)
end Rows

def reorderedBranch : VariablePositions branchCarrier :=
  [⟨N,branchLengthIndex⟩,⟨W,branchAllIndex⟩,⟨V,branchVectorIndex⟩]
def missingAll : VariablePositions branchCarrier := [⟨N,branchLengthIndex⟩,⟨V,branchVectorIndex⟩]

private theorem branch_none_of_empty (roots : List (ClosedFormula Const))
    (positions : VariablePositions branchCarrier) (carrier : Ty Base)
    (refused : SuppliedArguments.readVariables? [] branchContext positions branchType carrier = none) :
    SuppliedArguments.readVariables? roots branchContext positions branchType carrier = none := by
  cases received : SuppliedArguments.readVariables? roots branchContext positions branchType carrier with
  | none => rfl
  | some value =>
      have emptyPresent := SuppliedArguments.readVariables?_complete (roots := []) value.shape
      rw [refused] at emptyPresent
      contradiction

theorem reordered_branch_refused (roots : List (ClosedFormula Const)) :
    SuppliedArguments.readVariables? roots branchContext reorderedBranch branchType (N ⇒ V ⇒ W ⇒ W) = none :=
  branch_none_of_empty roots _ _ (by decide +kernel)
theorem changed_case_carrier_refused (roots : List (ClosedFormula Const)) :
    SuppliedArguments.readVariables? roots branchContext branchPositions branchType (E ⇒ V ⇒ W ⇒ W) = none :=
  branch_none_of_empty roots _ _ (by decide +kernel)

def prefixResult := SuppliedArguments.readVariables? [] branchContext missingAll branchType (N ⇒ V ⇒ W ⇒ W)
theorem prefix_received : prefixResult.isSome = true := by decide +kernel
theorem prefix_carrier : (prefixResult.get prefix_received).resultCarrier = (W ⇒ W) := by decide +kernel
theorem prefix_is_not_complete : (prefixResult.get prefix_received).resultCarrier ≠ W := by
  rw [prefix_carrier]
  decide +kernel

def solvedCode : Term Const solvedCarrier W := .app (.var solvedCaseIndex) (.var solvedFieldIndex)
def branchCode : Term Const branchCarrier W :=
  .app (.app (.app (.var branchCaseIndex) (.var branchLengthIndex)) (.var branchVectorIndex)) (.var branchAllIndex)

theorem solved_application_term (roots : List (ClosedFormula Const)) :
    (solvedApplication roots).term = solvedCode :=
  Reader.term_unique (solvedApplication roots).termRead (.application (.var solvedCaseIndex) (.var solvedFieldIndex))
theorem branch_application_term (roots : List (ClosedFormula Const)) :
    (branchApplication roots).term = branchCode :=
  Reader.term_unique (branchApplication roots).termRead
    (.application (.application (.application (.var branchCaseIndex) (.var branchLengthIndex))
      (.var branchVectorIndex)) (.var branchAllIndex))

namespace Realized
noncomputable section
open PredicateContexts
def model : HenkinModel.{0,0,0} Base Const := IndexedContainerNativeVectorEvidenceModel.model
def emptyValues : model.Valuation [] := fun index => nomatch index
abbrev Tree := IndexedContainerNativeVectorEvidenceModel.Tree
def trueValue : Ty.denote.{0,0} model.Carrier E := ULift.up true
def evidenceValue : Ty.denote.{0,0} model.Carrier W := ULift.up (.refl : Tree)
def answerValue : Ty.denote.{0,0} model.Carrier (E ⇒ .prop) := fun x => ULift.up (x = trueValue)
def familyValue : Ty.denote.{0,0} model.Carrier (E ⇒ .prop) := fun _ => ULift.up True
def motiveValue : Ty.denote.{0,0} model.Carrier (E ⇒ W ⇒ .prop) := fun x _ => ULift.up (x = trueValue)
def answerValues : model.Valuation [E ⇒ .prop] := model.extend emptyValues answerValue
def familyValues : model.Valuation [E ⇒ .prop,E ⇒ .prop] := model.extend answerValues familyValue
def motiveValues : model.Valuation [E ⇒ W ⇒ .prop,E ⇒ .prop,E ⇒ .prop] := model.extend familyValues motiveValue
def solvedConstructorValues : model.Valuation [E ⇒ E,E ⇒ W ⇒ .prop,E ⇒ .prop,E ⇒ .prop] :=
  model.extend (σ := E ⇒ E) motiveValues (fun (_ : Ty.denote.{0,0} model.Carrier E) => trueValue)
def branchConstructorValues : model.Valuation [N ⇒ V ⇒ E,E ⇒ E,E ⇒ W ⇒ .prop,E ⇒ .prop,E ⇒ .prop] := model.extend (σ := N ⇒ V ⇒ E) solvedConstructorValues
  (fun (_ : Ty.denote.{0,0} model.Carrier N) (_ : Ty.denote.{0,0} model.Carrier V) => trueValue)
def solvedCaseValues : model.Valuation [E ⇒ W,N ⇒ V ⇒ E,E ⇒ E,E ⇒ W ⇒ .prop,E ⇒ .prop,E ⇒ .prop] :=
  model.extend (σ := E ⇒ W) branchConstructorValues (fun (_ : Ty.denote.{0,0} model.Carrier E) => evidenceValue)
def ambientValues : model.Valuation IndexedVectorTreeNativeSourceReading.ambient :=
  model.extend (σ := N ⇒ V ⇒ W ⇒ W) solvedCaseValues
    (fun (_ : Ty.denote.{0,0} model.Carrier N) (_ : Ty.denote.{0,0} model.Carrier V) (_ : Ty.denote.{0,0} model.Carrier W) => evidenceValue)

private def motiveGuard : Term Const [E ⇒ .prop,E ⇒ .prop] ((E ⇒ W ⇒ .prop) ⇒ .prop) :=
  match IndexedVectorTreeNativeSourceReading.ambientContext.telescope with
  | .snoc (.snoc (.snoc (.snoc (.snoc _ predicate) _) _) _) _ => predicate
private def solvedConstructorGuard : Term Const [E ⇒ W ⇒ .prop,E ⇒ .prop,E ⇒ .prop] ((E ⇒ E) ⇒ .prop) :=
  match IndexedVectorTreeNativeSourceReading.ambientContext.telescope with
  | .snoc (.snoc (.snoc (.snoc _ predicate) _) _) _ => predicate
private def branchConstructorGuard : Term Const [E ⇒ E,E ⇒ W ⇒ .prop,E ⇒ .prop,E ⇒ .prop] ((N ⇒ V ⇒ E) ⇒ .prop) :=
  match IndexedVectorTreeNativeSourceReading.ambientContext.telescope with
  | .snoc (.snoc (.snoc _ predicate) _) _ => predicate
private def solvedCaseGuard : Term Const [N ⇒ V ⇒ E,E ⇒ E,E ⇒ W ⇒ .prop,E ⇒ .prop,E ⇒ .prop] ((E ⇒ W) ⇒ .prop) :=
  match IndexedVectorTreeNativeSourceReading.ambientContext.telescope with
  | .snoc (.snoc _ predicate) _ => predicate
private def branchCaseGuard : Term Const [E ⇒ W,N ⇒ V ⇒ E,E ⇒ E,E ⇒ W ⇒ .prop,E ⇒ .prop,E ⇒ .prop]
    ((N ⇒ V ⇒ W ⇒ W) ⇒ .prop) :=
  match IndexedVectorTreeNativeSourceReading.ambientContext.telescope with
  | .snoc _ predicate => predicate

private theorem ambient_telescope : IndexedVectorTreeNativeSourceReading.ambientContext.telescope =
    .snoc (.snoc (.snoc (.snoc (.snoc (.snoc (.snoc .nil
      (PredicateProducts.full (E ⇒ .prop))) (PredicateProducts.full (E ⇒ .prop))) motiveGuard)
        solvedConstructorGuard) branchConstructorGuard) solvedCaseGuard) branchCaseGuard := by
  with_unfolding_all rfl

theorem ambient_satisfies : IndexedVectorTreeNativeSourceReading.ambientContext.telescope.Satisfies model ambientValues := by
  rw [ambient_telescope]
  apply (Telescope.satisfies_snoc model _ _ _ _).mpr
  constructor
  · apply (Telescope.satisfies_snoc model _ _ _ _).mpr
    constructor
    · apply (Telescope.satisfies_snoc model _ _ _ _).mpr
      constructor
      · apply (Telescope.satisfies_snoc model _ _ _ _).mpr
        constructor
        · apply (Telescope.satisfies_snoc model _ _ _ _).mpr
          constructor
          · apply (Telescope.satisfies_snoc model _ _ _ _).mpr
            constructor
            · apply (Telescope.satisfies_snoc model _ _ _ _).mpr
              constructor
              · intro formula impossible; cases impossible
              · trivial
            · trivial
          · with_unfolding_all intro x _ _; trivial
        · with_unfolding_all intro x _ _; trivial
      · with_unfolding_all intro n _ _ vector _ _; trivial
    · with_unfolding_all intro x _ _; rfl
  · with_unfolding_all intro n _ _ vector _ _ evidence _ _; rfl

private theorem telescope_rebuild {Γ : Ctx Base} {carrier : Ty Base}
    (context : GuardedContext Source.theory lex (carrier :: Γ)) :
    context.telescope = context.previous.telescope.snoc context.lastPredicate :=
  (congrArg (fun value => value.telescope) context.rebuild).symm

def familyCode : ClosedTerm Const (E ⇒ .prop) := .lam .top
def motiveCode : ClosedTerm Const (E ⇒ W ⇒ .prop) :=
  .lam (.lam (.eq (.var (.vs .vz)) (weakenCtx _ (IndexedContainerNativeVectorMethodReading.parameter 20 E))))
def nilVector : ClosedTerm Const V := .app (NativeVectorAll.Reading.operations original selection).nilCode familyCode
def nilEvidence : ClosedTerm Const W :=
  .app (StructuralProfile.reflexivityCode witness N) original.zero

def nilAll := NativeVectorAll.Evidence.nil_value original pairs witness selection familyCode motiveCode
  IndexedContainerNativeVectorEvidenceModel.allPremises.choice
  IndexedContainerNativeVectorEvidenceModel.allPremises.recursion

theorem nil_all_holds :
    (model.denote (.app (NativeVectorAll.Reading.allCode original pairs witness selection familyCode motiveCode
      original.zero nilVector) nilEvidence) emptyValues).down :=
  IndexedContainerNativeVectorEvidenceModel.sound nilAll

def solvedValues : model.Valuation solvedCarrier := model.extend (σ := E) ambientValues trueValue
def lengthValues : model.Valuation (N :: IndexedVectorTreeNativeSourceReading.ambient) :=
  model.extend (σ := N) ambientValues (ULift.up 0)
def vectorValues : model.Valuation Rows.fieldCarrier := model.extend (σ := V) lengthValues (ULift.up [])
def branchValues : model.Valuation branchCarrier := model.extend (σ := W) vectorValues evidenceValue

private def trueCode : ClosedTerm Const E := IndexedContainerNativeVectorMethodReading.parameter 20 E
private def answerCode : ClosedTerm Const (E ⇒ .prop) := .lam (.eq (.var .vz) (weaken trueCode))
private def solvedConstructorCode : ClosedTerm Const (E ⇒ E) := .lam (weaken trueCode)
private def branchConstructorCode : ClosedTerm Const (N ⇒ V ⇒ E) := .lam (.lam (weaken (weaken trueCode)))
private def solvedCaseCode : ClosedTerm Const (E ⇒ W) := .lam (weaken witness)
private def branchCaseCode : ClosedTerm Const (N ⇒ V ⇒ W ⇒ W) := .lam (.lam (.lam (weaken (weaken (weaken witness)))))
private def ambientImages : Subst Const IndexedVectorTreeNativeSourceReading.ambient [] :=
  Subst.cons branchCaseCode (Subst.cons solvedCaseCode (Subst.cons branchConstructorCode
    (Subst.cons solvedConstructorCode (Subst.cons motiveCode (Subst.cons familyCode
      (Subst.cons answerCode (fun {type} (index : Var [] type) => nomatch index)))))))
private def fieldImages : Subst Const Rows.fieldCarrier [] :=
  Subst.cons nilVector (Subst.cons original.zero ambientImages)

private theorem field_values :
    (Soundness.substVal model fieldImages emptyValues : model.Valuation Rows.fieldCarrier) =
      (fun {_type} => vectorValues : model.Valuation Rows.fieldCarrier) := by
  funext type index
  cases index with
  | vz => with_unfolding_all rfl
  | vs index =>
    cases index with
    | vz => with_unfolding_all rfl
    | vs index =>
      cases index with
      | vz => with_unfolding_all rfl
      | vs index =>
        cases index with
        | vz => with_unfolding_all rfl
        | vs index =>
          cases index with
          | vz => with_unfolding_all rfl
          | vs index =>
            cases index with
            | vz => with_unfolding_all rfl
            | vs index =>
              cases index with
              | vz => with_unfolding_all rfl
              | vs index =>
                cases index with
                | vz => with_unfolding_all rfl
                | vs index =>
                  cases index with
                  | vz => with_unfolding_all rfl
                  | vs index => cases index

private theorem bundle_subst : subst fieldImages IndexedVectorTreeNativeSourceLogicalRows.bundlePredicate =
    NativeVectorAll.Reading.allCode original pairs witness selection familyCode motiveCode original.zero nilVector := by
  rw [IndexedVectorTreeNativeSourceLogicalRows.bundlePredicate,NativeVectorAll.Reading.subst_allCode]
  with_unfolding_all rfl

private theorem nil_evidence_value : model.denote nilEvidence emptyValues = evidenceValue := by
  with_unfolding_all rfl

theorem solved_satisfies : solvedContext.telescope.Satisfies model solvedValues := by
  rw [telescope_rebuild]
  apply (Telescope.satisfies_snoc model _ _ _ _).mpr
  constructor
  · change Rows.solvedAmbient.telescope.Satisfies model ambientValues
    rw [Rows.solved_original_ambient_telescope]
    exact ambient_satisfies
  · rw [Rows.solved_field_domain]
    rfl

theorem length_satisfies : Rows.branchLength.telescope.Satisfies model lengthValues := by
  rw [telescope_rebuild]
  apply (Telescope.satisfies_snoc model _ _ _ _).mpr
  constructor
  · change Rows.branchAmbient.telescope.Satisfies model ambientValues
    rw [Rows.branch_original_ambient_telescope]
    exact ambient_satisfies
  · rw [Rows.length_field_domain]
    trivial

theorem vector_satisfies : Rows.branchFields.telescope.Satisfies model vectorValues := by
  rw [telescope_rebuild]
  apply (Telescope.satisfies_snoc model _ _ _ _).mpr
  constructor
  · exact length_satisfies
  · rw [Rows.vector_field_domain]
    have member := NativeVectorComputationRows.GuardedFamily.nil_member
      (Γ := []) (Δ := []) (NativeVectorAll.Reading.operations original selection) familyCode
    have sound := Soundness.extDerivation_sound member.erase (M := model) (ρ := emptyValues)
      (model.functionsRespectEqv_of_fullDomains IndexedContainerNativeVectorEvidenceModel.full)
      (fun _ => trivial) (by intro formula impossible; cases impossible)
    with_unfolding_all exact sound

private theorem bundle_at_source (point : Ty.denote.{0,0} model.Carrier W) :
    (model.denote IndexedVectorTreeNativeSourceLogicalRows.bundlePredicate vectorValues point).down =
      (model.denote (NativeVectorAll.Reading.allCode original pairs witness selection familyCode motiveCode
        original.zero nilVector) emptyValues point).down := by
  have natural := Soundness.denote_subst model fieldImages IndexedVectorTreeNativeSourceLogicalRows.bundlePredicate emptyValues
  rw [bundle_subst,field_values] at natural
  exact congrArg (fun predicate => (predicate point).down) natural.symm

private theorem nil_all_at_source :
    (model.denote IndexedVectorTreeNativeSourceLogicalRows.bundlePredicate vectorValues evidenceValue).down =
      (model.denote (.app (NativeVectorAll.Reading.allCode original pairs witness selection familyCode motiveCode
        original.zero nilVector) nilEvidence) emptyValues).down := by
  change _ = (model.denote (NativeVectorAll.Reading.allCode original pairs witness selection familyCode motiveCode
    original.zero nilVector) emptyValues (model.denote nilEvidence emptyValues)).down
  rw [nil_evidence_value]
  exact bundle_at_source evidenceValue

theorem branch_satisfies : branchContext.telescope.Satisfies model branchValues := by
  rw [telescope_rebuild]
  apply (Telescope.satisfies_snoc model _ _ _ _).mpr
  constructor
  · exact vector_satisfies
  · rw [Rows.branch_all_domain]
    rw [nil_all_at_source]
    exact nil_all_holds

theorem solved_application_holds :
    (model.denote solvedResultPredicate solvedValues (model.denote solvedCode solvedValues)).down := by
  have result := (solvedApplication []).satisfies model
    (model.functionsRespectEqv_of_fullDomains IndexedContainerNativeVectorEvidenceModel.full)
    solvedValues (fun _ => trivial)
    (by simpa only [GuardedContext.hypotheses, assumptions, List.map_nil, List.nil_append, Telescope.Satisfies] using solved_satisfies)
  rw [solved_application_predicate,solved_application_term] at result
  exact result

theorem branch_application_holds :
    (model.denote branchResultPredicate branchValues (model.denote branchCode branchValues)).down := by
  have result := (branchApplication []).satisfies model
    (model.functionsRespectEqv_of_fullDomains IndexedContainerNativeVectorEvidenceModel.full)
    branchValues (fun _ => trivial)
    (by simpa only [GuardedContext.hypotheses, assumptions, List.map_nil, List.nil_append, Telescope.Satisfies] using branch_satisfies)
  rw [branch_application_predicate,branch_application_term] at result
  exact result

def falseValues : model.Valuation solvedCarrier := model.extend (σ := E) ambientValues (ULift.up false)
theorem false_source_field_refused : ¬ solvedContext.telescope.Satisfies model falseValues := by
  rw [telescope_rebuild]
  intro satisfies
  have guard := ((Telescope.satisfies_snoc (type := E) model _ _ ambientValues (ULift.up false)).mp satisfies).2
  rw [Rows.solved_field_domain] at guard
  have impossible : false = true := congrArg ULift.down guard
  cases impossible

def badEvidence : ClosedTerm Const W := PredicateSigma.pair pairs witness witness
def badNilFormula : ClosedFormula Const :=
  .app (NativeVectorAll.Reading.allCode original pairs witness selection familyCode motiveCode original.zero nilVector)
    badEvidence
def badNilDecoded := NativeVectorAll.Evidence.nil_decode original pairs witness selection familyCode motiveCode
  (IndexedContainerNativeVectorEvidenceModel.allPremises.choice.prepend badNilFormula)
  (IndexedContainerNativeVectorEvidenceModel.allPremises.recursion.prepend badNilFormula)
  badEvidence (.hyp ⟨0,by decide +kernel⟩)

theorem invalid_nil_bundle_refused : ¬ (model.denote badNilFormula emptyValues).down := by
  intro supplied
  have holds : Soundness.SatisfiesHyps model emptyValues
      (badNilFormula :: IndexedContainerNativeVectorEvidenceModel.assumptions) := by
    intro formula present
    rcases List.mem_cons.mp present with rfl | present
    · exact supplied
    · exact IndexedContainerNativeVectorEvidenceModel.assumptions_realizable formula present
  have same := Soundness.extDerivation_sound badNilDecoded.erase (M := model) (ρ := emptyValues)
    (model.functionsRespectEqv_of_fullDomains IndexedContainerNativeVectorEvidenceModel.full)
    (fun _ => trivial) holds
  have impossible : PredicateSigma.Controls.Evidence.pair .refl .refl = .refl := congrArg ULift.down same
  cases impossible

def badBranchValues : model.Valuation branchCarrier :=
  model.extend (σ := W) vectorValues (model.denote badEvidence emptyValues)

theorem invalid_source_bundle_refused : ¬ branchContext.telescope.Satisfies model badBranchValues := by
  rw [telescope_rebuild]
  intro satisfies
  have guard := ((Telescope.satisfies_snoc (type := W) model _ _ vectorValues
    (model.denote badEvidence emptyValues)).mp satisfies).2
  rw [Rows.branch_all_domain,bundle_at_source] at guard
  exact invalid_nil_bundle_refused guard

end
end Realized

#print axioms reordered_branch_refused
#print axioms prefix_is_not_complete
#print axioms Realized.ambient_satisfies
#print axioms Realized.branch_satisfies
#print axioms Realized.false_source_field_refused
#print axioms Realized.invalid_source_bundle_refused

end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeSourceCaseControls
