import Mettapedia.Logic.HOL.FiniteConstructorPayloadMapComputations
import Mettapedia.Logic.HOL.ConstructorFieldRepresentationControls
import Mettapedia.Logic.HOL.FiniteConstructorPayloadRetraction
import Mettapedia.Logic.HOL.FiniteConstructorSeparation

/-!
# Heterogeneous finite-payload map controls

The first constructor carries a number and a Boolean source field; the
second is nullary. The stored field program uses the original number as its
constructor marker, so field mapping retains a genuine prior-field dependency.
Its target row reorders and duplicates fields as `[E,N,E]`.
The decoder and its source selection/injectivity premises are the existing
recursive-space provider.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.FiniteConstructorPayloadMapControls
open FiniteConstructorEncoding CurriedPredicates
open ConstructorFieldRepresentationControls
open Mettapedia.Languages.HOLLight

def sourceSignature : List (List (Ty Base)) := [[N,A],[]]
def targetSignature : List (List (Ty Base)) := [[E,N,E],[]]

def firstBody (element : Ty Base) : FieldBody Const [] [N,element] N := fun _ arguments => arguments.1
theorem firstBody_natural (element : Ty Base) : NaturalFieldBody (firstBody element) := by
  intro Ξ Ω first later arguments
  rfl

def storeBody : FieldBody Const [] [N,A] E := fun _ arguments =>
  ConstructorFieldRepresentation.value (.const .construct) arguments.1 (.lam (.const .bottom)) arguments.2.1
theorem storeBody_natural : NaturalFieldBody storeBody := by
  intro Ξ Ω first later arguments
  simp only [storeBody,ConstructorFieldRepresentation.value_subst,HOL.subst,substituteArguments]

def middleBody : FieldBody Const [] [E,N,E] N := fun _ arguments => arguments.2.1
theorem middleBody_natural : NaturalFieldBody middleBody := by
  intro Ξ Ω first later arguments
  rfl

def readBody : FieldBody Const [] [E,N,E] A := fun _ arguments =>
  .app (ConstructorFieldRepresentation.decoder (.const .construct) (.const .payloadSelection) (.const .fieldSelection)) arguments.1
theorem readBody_natural : NaturalFieldBody readBody := by
  intro Ξ Ω first later arguments
  simp only [readBody,HOL.subst,ConstructorFieldRepresentation.decoder_subst,substituteArguments]

def firstProgram (element : Ty Base) : ClosedTerm Const (FunctionType [N,element] N) := abstractFields [N,element] (firstBody element)
def storeProgram : ClosedTerm Const (FunctionType [N,A] E) := abstractFields [N,A] storeBody
def middleProgram : ClosedTerm Const (FunctionType [E,N,E] N) := abstractFields [E,N,E] middleBody
def readProgram : ClosedTerm Const (FunctionType [E,N,E] A) := abstractFields [E,N,E] readBody

def forwardRow : FieldMaps Const [] [N,A] [E,N,E] where
  output index := match index with
    | .vz => storeProgram
    | .vs .vz => firstProgram A
    | .vs (.vs .vz) => storeProgram
    | .vs (.vs (.vs impossible)) => nomatch impossible

def backwardRow : FieldMaps Const [] [E,N,E] [N,A] where
  output index := match index with
    | .vz => middleProgram
    | .vs .vz => readProgram
    | .vs (.vs impossible) => nomatch impossible

def nullary : FieldMaps Const [] [] [] where
  output index := nomatch index

def forward : InventoryMaps Const [] sourceSignature targetSignature := .cons forwardRow (.cons nullary .nil)
def backward : InventoryMaps Const [] targetSignature sourceSignature := .cons backwardRow (.cons nullary .nil)

def sourceConditions : ConstructorDataPredicates.Conditions Const [] sourceSignature
  | ⟨0,_⟩ => CurriedPredicates.constant [N,A] .top
  | ⟨1,_⟩ => .top
  | ⟨index + 2,bound⟩ => False.elim (by change index + 2 < 2 at bound; omega)

def firstComputation {Γ : Ctx Base} {Δ : List (Formula Const Γ)} (element : Ty Base)
    (images : Subst Const [] Γ) (number : Term Const Γ N) (field : Term Const Γ element) :
    ProofSyntax Const Δ (.eq (applyFields [N,element] (HOL.subst images (firstProgram element)) (number,field,PUnit.unit)) number) := by
  apply ProofSyntax.castIndices rfl ?_ (abstractFields_beta [N,element]
    (fun _ arguments => arguments.1) (by intro Ξ Ω first later arguments; rfl) (number,field,PUnit.unit))
  rw [firstProgram,abstractFields_subst _ _ _ (firstBody_natural element)]
  rfl

def storedComputation {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    (images : Subst Const [] Γ) (number : Term Const Γ N) (field : Term Const Γ A) :
    ProofSyntax Const Δ (.eq (applyFields [N,A] (HOL.subst images storeProgram) (number,field,PUnit.unit))
      (ConstructorFieldRepresentation.value (.const .construct) number (.lam (.const .bottom)) field)) := by
  apply ProofSyntax.castIndices rfl ?_ (abstractFields_beta [N,A]
    (fun _ arguments => ConstructorFieldRepresentation.value (.const .construct) arguments.1 (.lam (.const .bottom)) arguments.2.1)
    (by intro Ξ Ω first later arguments; simp only [ConstructorFieldRepresentation.value_subst,HOL.subst,substituteArguments])
    (number,field,PUnit.unit))
  rw [storeProgram,abstractFields_subst _ _ _ storeBody_natural]
  rfl

def middleComputation {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    (images : Subst Const [] Γ) (first : Term Const Γ E) (number : Term Const Γ N) (second : Term Const Γ E) :
    ProofSyntax Const Δ (.eq (applyFields [E,N,E] (HOL.subst images middleProgram) (first,number,second,PUnit.unit)) number) := by
  apply ProofSyntax.castIndices rfl ?_ (abstractFields_beta [E,N,E]
    (fun _ arguments => arguments.2.1) (by intro Ξ Ω earlier later arguments; rfl) (first,number,second,PUnit.unit))
  rw [middleProgram,abstractFields_subst _ _ _ middleBody_natural]
  rfl

def readComputation {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    (images : Subst Const [] Γ) (first : Term Const Γ E) (number : Term Const Γ N) (second : Term Const Γ E) :
    ProofSyntax Const Δ (.eq (applyFields [E,N,E] (HOL.subst images readProgram) (first,number,second,PUnit.unit))
      (.app (ConstructorFieldRepresentation.decoder (.const .construct) (.const .payloadSelection) (.const .fieldSelection)) first)) := by
  apply ProofSyntax.castIndices rfl ?_ (abstractFields_beta [E,N,E]
    (fun _ arguments => .app (ConstructorFieldRepresentation.decoder (.const .construct) (.const .payloadSelection) (.const .fieldSelection)) arguments.1)
    (by intro Ξ Ω earlier later arguments; simp only [HOL.subst,ConstructorFieldRepresentation.decoder_subst,substituteArguments])
    (first,number,second,PUnit.unit))
  rw [readProgram,abstractFields_subst _ _ _ readBody_natural]
  rfl

private theorem selection_subst {Γ Ξ : Ctx Base} {type : Ty Base}
    (images : Subst Const Γ Ξ) (selection : Term Const Γ (SelectionProofs.Selection type)) :
    HOL.subst images (SelectionProofs.principle selection) = SelectionProofs.principle (HOL.subst images selection) := by
  simp only [SelectionProofs.principle,HOL.subst,SelectionProofs.subst_instanceFormula,subst_weaken,Subst.lift]

def storedFieldRecovery {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    (images : Subst Const [] Γ) (transport : ProofSyntax.OccurrenceMap (premises.map (HOL.subst images)) Δ)
    (number : Term Const Γ N) (field : Term Const Γ A) :
    ProofSyntax Const Δ (.eq
      (.app (ConstructorFieldRepresentation.decoder (.const .construct) (.const .payloadSelection) (.const .fieldSelection))
        (ConstructorFieldRepresentation.value (.const .construct) number (.lam (.const .bottom)) field)) field) := by
  have payloadChoice : ProofSyntax Const Δ (SelectionProofs.principle (.const .payloadSelection)) := by
    apply ProofSyntax.castIndices rfl ?_
      (((ProofSyntax.hyp ⟨0,by simp [premises]⟩ : ProofSyntax Const premises (SelectionProofs.principle selectPayload)).subst images).mono transport)
    exact selection_subst images selectPayload
  have fieldChoice : ProofSyntax Const Δ (SelectionProofs.principle (.const .fieldSelection)) := by
    apply ProofSyntax.castIndices rfl ?_
      (((ProofSyntax.hyp ⟨1,by simp [premises]⟩ : ProofSyntax Const premises (SelectionProofs.principle selectField)).subst images).mono transport)
    exact selection_subst images selectField
  have injectivity : ProofSyntax Const Δ (ConstructorProjections.fieldInjective (.const .construct)) := by
    apply ProofSyntax.castIndices rfl ?_
      (((ProofSyntax.hyp ⟨2,by simp [premises]⟩ : ProofSyntax Const premises (ConstructorProjections.fieldInjective raw)).subst images).mono transport)
    exact ConstructorProjections.subst_fieldInjective images raw
  let decoding : Term Const Γ (E ⇒ A) :=
    ConstructorFieldRepresentation.decoder (.const .construct) (.const .payloadSelection) (.const .fieldSelection)
  exact .eqTrans (.eqAppArg decoding (.eqSymm
    (ConstructorFieldRepresentation.embedding_apply (.const .construct) number (.lam (.const .bottom)) field)))
    (ConstructorFieldRepresentation.roundtrip (.const .construct) number (.lam (.const .bottom))
      (.const .payloadSelection) (.const .fieldSelection) field payloadChoice fieldChoice injectivity)

def rowRecovery : InventoryMaps.RowRecovery premises forward backward sourceConditions := by
  intro Γ images assumptions transport index arguments _allowed type fieldIndex
  rcases index with ⟨index,bound⟩
  cases index with
  | zero =>
      rcases arguments with ⟨number,field,⟨⟩⟩
      let stored := applyFields [N,A] (HOL.subst images storeProgram) (number,field,PUnit.unit)
      let kept := applyFields [N,A] (HOL.subst images (firstProgram A)) (number,field,PUnit.unit)
      cases fieldIndex with
      | vz =>
          apply ProofSyntax.castIndices rfl ?_
            (.eqTrans (middleComputation images stored kept stored) (firstComputation A images number field))
          rfl
      | vs fieldIndex =>
          cases fieldIndex with
          | vz =>
              let decoding : Term Const Γ (E ⇒ A) :=
                ConstructorFieldRepresentation.decoder (.const .construct) (.const .payloadSelection) (.const .fieldSelection)
              apply ProofSyntax.castIndices rfl ?_
                (.eqTrans (readComputation images stored kept stored)
                  (.eqTrans (.eqAppArg decoding (storedComputation images number field))
                    (storedFieldRecovery images transport number field)))
              rfl
          | vs impossible => nomatch impossible
  | succ index =>
      cases index with
      | zero => nomatch fieldIndex
      | succ index => exact False.elim (by change index + 1 + 1 < 2 at bound; omega)

def guardedRecovery (payload : ClosedTerm Const (payloadType sourceSignature))
    (present : ProofSyntax Const premises (ConstructorDataPredicates.guard sourceSignature sourceConditions payload)) :
    ProofSyntax Const premises (.eq (backward.mapPayload (forward.mapPayload payload)) payload) :=
  forward.guardedRoundtrip backward sourceConditions rowRecovery payload present

def selectedField : ClosedTerm Const A := .app selectField (.lam .top)
def fieldPayload : ClosedTerm Const (payloadType sourceSignature) :=
  encode sourceSignature ⟨0,by decide⟩ (.const .zero,selectedField,PUnit.unit)
def nullaryPayload : ClosedTerm Const (payloadType sourceSignature) :=
  encode sourceSignature ⟨1,by decide⟩ PUnit.unit

def fieldAdmitted : ProofSyntax Const premises (ConstructorDataPredicates.guard sourceSignature sourceConditions fieldPayload) :=
  ConstructorDataPredicates.introduce sourceSignature sourceConditions ⟨0,by decide⟩
    (.const .zero,selectedField,PUnit.unit)
    (CurriedPredicates.constant_intro [N,A] (.const .zero,selectedField,PUnit.unit) .topI)

def nullaryAdmitted : ProofSyntax Const premises (ConstructorDataPredicates.guard sourceSignature sourceConditions nullaryPayload) :=
  ConstructorDataPredicates.introduce sourceSignature sourceConditions ⟨1,by decide⟩ PUnit.unit .topI

def fieldRoundtrip : ProofSyntax Const premises
    (.eq (backward.mapPayload (forward.mapPayload fieldPayload)) fieldPayload) := guardedRecovery fieldPayload fieldAdmitted
def nullaryRoundtrip : ProofSyntax Const premises
    (.eq (backward.mapPayload (forward.mapPayload nullaryPayload)) nullaryPayload) := guardedRecovery nullaryPayload nullaryAdmitted

def distinctOccurrences : ProofSyntax Const premises (.not (.eq fieldPayload nullaryPayload)) :=
  .notI (separate_occurrences sourceSignature ⟨0,by decide⟩ ⟨1,by decide⟩ (by decide)
    (.const .zero,selectedField,PUnit.unit) PUnit.unit (.hyp 0))

theorem field_roundtrip_holds :
    model.denote (backward.mapPayload (forward.mapPayload fieldPayload)) values = model.denote fieldPayload values := by
  have result := Soundness.extDerivation_sound fieldRoundtrip.erase (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => trivial) assumptions_realizable
  exact model.eq_of_eqv_of_fullDomains full result

theorem nullary_roundtrip_holds :
    model.denote (backward.mapPayload (forward.mapPayload nullaryPayload)) values = model.denote nullaryPayload values := by
  have result := Soundness.extDerivation_sound nullaryRoundtrip.erase (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => trivial) assumptions_realizable
  exact model.eq_of_eqv_of_fullDomains full result

theorem distinct_source_payloads : model.denote fieldPayload values ≠ model.denote nullaryPayload values := by
  have result := Soundness.extDerivation_sound distinctOccurrences.erase (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => trivial) assumptions_realizable
  intro same
  exact result ((model.eqv_iff_eq_of_fullDomains full _ _).mpr same)

private def composedEncoded {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {sourceRow targetRow : List (Ty Base)} {sourceRest targetRest : List (List (Ty Base))}
    (lower : InventoryMaps Const Γ (sourceRow :: sourceRest) (targetRow :: targetRest))
    (raise : InventoryMaps Const Γ (targetRow :: targetRest) (sourceRow :: sourceRest))
    (arguments : Arguments Const Γ sourceRow) :
    ProofSyntax Const Δ (.eq (raise.mapPayload (lower.mapPayload
      (encode (sourceRow :: sourceRest) ⟨0,by simp⟩ arguments)))
      (encode (sourceRow :: sourceRest) ⟨0,by simp⟩
        ((raise.row ⟨0,by simp⟩).apply ((lower.row ⟨0,by simp⟩).apply arguments)))) :=
  .eqTrans (raise.mapPayload_congr _ _ (lower.mapPayload_encode ⟨0,by simp⟩ arguments))
    (raise.mapPayload_encode ⟨0,by simp⟩ ((lower.row ⟨0,by simp⟩).apply arguments))

def wrongReadBody : FieldBody Const [] [E,N,E] A := fun _ _ => .app (.const .fieldSelection) (.lam .top)
theorem wrongReadBody_natural : NaturalFieldBody wrongReadBody := by
  intro Ξ Ω first later arguments
  rfl
def wrongReadProgram : ClosedTerm Const (FunctionType [E,N,E] A) := abstractFields [E,N,E] wrongReadBody
def wrongBackwardRow : FieldMaps Const [] [E,N,E] [N,A] where
  output index := match index with
    | .vz => middleProgram
    | .vs .vz => wrongReadProgram
    | .vs (.vs impossible) => nomatch impossible
def wrongBackward : InventoryMaps Const [] targetSignature sourceSignature := .cons wrongBackwardRow (.cons nullary .nil)

def wrongReadComputation {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    (images : Subst Const [] Γ) (first : Term Const Γ E) (number : Term Const Γ N) (second : Term Const Γ E) :
    ProofSyntax Const Δ (.eq (applyFields [E,N,E] (HOL.subst images wrongReadProgram) (first,number,second,PUnit.unit))
      (HOL.subst images selectedField)) := by
  apply ProofSyntax.castIndices rfl ?_ (abstractFields_beta [E,N,E]
    (fun _ _ => Term.app (.const .fieldSelection) (.lam .top))
    (by intro Ξ Ω earlier later arguments; rfl) (first,number,second,PUnit.unit))
  rw [wrongReadProgram,abstractFields_subst _ _ _ wrongReadBody_natural]
  rfl

def openImages : Subst Const [] [A] := fun index => nomatch index
def openInput : Term Const [A] (payloadType sourceSignature) :=
  encode sourceSignature ⟨0,by decide⟩ (.const .zero,.var .vz,PUnit.unit)
def wrongComposite : Term Const [A] (payloadType sourceSignature) :=
  (wrongBackward.subst openImages).mapPayload ((forward.subst openImages).mapPayload openInput)
def wrongOutput : Term Const [A] (payloadType sourceSignature) :=
  encode sourceSignature ⟨0,by decide⟩ (.const .zero,HOL.subst openImages selectedField,PUnit.unit)

def openConditions : ConstructorDataPredicates.Conditions Const [A] sourceSignature :=
  fun index => HOL.subst openImages (sourceConditions index)

def openInputAdmitted : ProofSyntax Const ([] : List (Formula Const [A]))
    (ConstructorDataPredicates.guard sourceSignature openConditions openInput) := by
  apply ConstructorDataPredicates.introduce sourceSignature openConditions ⟨0,by decide⟩
    (.const .zero,.var .vz,PUnit.unit)
  apply ProofSyntax.castIndices rfl ?_
    (CurriedPredicates.constant_intro [N,A] (.const .zero,.var .vz,PUnit.unit) .topI)
  change applyArguments [N,A] (CurriedPredicates.constant [N,A] .top) _ =
    applyArguments [N,A] (HOL.subst openImages (CurriedPredicates.constant [N,A] .top)) _
  rw [CurriedPredicates.constant_subst]
  rfl

def wrongCompositeComputation : ProofSyntax Const ([] : List (Formula Const [A])) (.eq wrongComposite wrongOutput) := by
  let number : Term Const [A] N := .const .zero
  let field : Term Const [A] A := .var .vz
  let stored := applyFields [N,A] (HOL.subst openImages storeProgram) (number,field,PUnit.unit)
  let kept := applyFields [N,A] (HOL.subst openImages (firstProgram A)) (number,field,PUnit.unit)
  refine .eqTrans (composedEncoded (forward.subst openImages) (wrongBackward.subst openImages)
    (number,field,PUnit.unit)) ?_
  apply encode_congr sourceSignature ⟨0,by decide⟩
  intro type index
  cases index with
  | vz =>
      apply ProofSyntax.castIndices rfl ?_
        (.eqTrans (middleComputation openImages stored kept stored) (firstComputation A openImages number field))
      rfl
  | vs index =>
      cases index with
      | vz =>
          apply ProofSyntax.castIndices rfl ?_ (wrongReadComputation openImages stored kept stored)
          rfl
      | vs impossible => nomatch impossible

noncomputable def selectedValue : Element := model.denote selectedField values
noncomputable def otherValue : Element := ULift.up (!selectedValue.down)
noncomputable def otherValues : model.Valuation [A] := model.extend (σ := A) values otherValue

theorem wrong_input_admitted :
    (model.denote (ConstructorDataPredicates.guard sourceSignature openConditions openInput) otherValues).down :=
  Soundness.extDerivation_sound openInputAdmitted.erase (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => full _ _) (by intro _ impossible; cases impossible)

theorem other_ne_selected : otherValue ≠ selectedValue := by
  intro same
  have bits := congrArg ULift.down same
  change (!selectedValue.down) = selectedValue.down at bits
  cases bit : selectedValue.down <;> simp_all

abbrev SourcePayloadValue := (Number → Element → ULift.{1,0} Prop) → ULift.{1,0} Prop → ULift.{1,0} Prop

theorem wrong_field_roundtrip_refused : model.denote wrongComposite otherValues ≠ model.denote openInput otherValues := by
  have checked := Soundness.extDerivation_sound (M := model) (ρ := otherValues) wrongCompositeComputation.erase
    (model.functionsRespectEqv_of_fullDomains full) (fun _ => full _ _) (by intro _ impossible; cases impossible)
  have computed : model.denote wrongComposite otherValues = model.denote wrongOutput otherValues :=
    model.eq_of_eqv_of_fullDomains full checked
  intro same
  let observer : Number → Element → ULift.{1,0} Prop := fun _ field => ULift.up (field = selectedValue)
  have observed := congrArg (fun payload : SourcePayloadValue => (payload observer (ULift.up False)).down) (computed.symm.trans same)
  change (selectedValue = selectedValue) = (otherValue = selectedValue) at observed
  exact other_ne_selected (Eq.mp observed rfl)

def outsidePayload : ClosedTerm Const (payloadType targetSignature) :=
  encode targetSignature ⟨0,by decide⟩ (.const .bottom,.const .zero,.const .bottom,PUnit.unit)
def outsideComposite : ClosedTerm Const (payloadType targetSignature) :=
  forward.mapPayload (backward.mapPayload outsidePayload)
def outsideCompositeComputation : ProofSyntax Const ([] : List (ClosedFormula Const))
    (.eq outsideComposite (encode targetSignature ⟨0,by decide⟩
      ((forward.row ⟨0,by decide⟩).apply ((backward.row ⟨0,by decide⟩).apply
        (.const .bottom,.const .zero,.const .bottom,PUnit.unit))))) :=
  composedEncoded backward forward (.const .bottom,.const .zero,.const .bottom,PUnit.unit)

theorem stored_program_not_bottom (number : Number) (field : Element) :
    model.denote storeProgram values number field ≠ RecursiveSpaceSemantics.bottom filler := by
  change RecursiveSpaceSemantics.construct filler number.down (fun handler => handler number field number)
    (fun _ => RecursiveSpaceSemantics.bottom filler) ≠ RecursiveSpaceSemantics.bottom filler
  exact RecursiveSpaceSemantics.construct_ne_bottom filler _ _ _

abbrev TargetPayloadValue := (Space → Number → Space → ULift.{1,0} Prop) → ULift.{1,0} Prop → ULift.{1,0} Prop

theorem outside_roundtrip_refused : model.denote outsideComposite values ≠ model.denote outsidePayload values := by
  have checked := Soundness.extDerivation_sound (M := model) (ρ := values) outsideCompositeComputation.erase
    (model.functionsRespectEqv_of_fullDomains full) (fun _ => full _ _) (by intro _ impossible; cases impossible)
  have computed := model.eq_of_eqv_of_fullDomains full checked
  intro same
  let observer : Space → Number → Space → ULift.{1,0} Prop :=
    fun stored _ _ => ULift.up (stored = RecursiveSpaceSemantics.bottom filler)
  have observed := congrArg (fun payload : TargetPayloadValue => (payload observer (ULift.up False)).down)
    (computed.symm.trans same)
  let bottom := RecursiveSpaceSemantics.bottom filler
  let number := model.denote middleProgram values bottom (ULift.up 0) bottom
  let field := model.denote readProgram values bottom (ULift.up 0) bottom
  change (model.denote storeProgram values number field = bottom) = (bottom = bottom) at observed
  exact stored_program_not_bottom number field (Eq.mpr observed rfl)

private theorem denotation_congr {Γ : Ctx Base} {source target : List (List (Ty Base))}
    (maps : InventoryMaps Const Γ source target) (first second : Term Const Γ (payloadType source))
    (valuation : model.Valuation Γ) (same : model.denote first valuation = model.denote second valuation) :
    model.denote (maps.mapPayload first) valuation = model.denote (maps.mapPayload second) valuation := by
  have proof : ProofSyntax Const [.eq first second] (.eq (maps.mapPayload first) (maps.mapPayload second)) :=
    maps.mapPayload_congr first second (.hyp 0)
  have hypotheses : Soundness.SatisfiesHyps model valuation [.eq first second] := by
    intro formula present
    simp only [List.mem_singleton] at present
    subst formula
    exact (model.eqv_iff_eq_of_fullDomains full _ _).mpr same
  exact model.eq_of_eqv_of_fullDomains full (Soundness.extDerivation_sound proof.erase
    (model.functionsRespectEqv_of_fullDomains full) (fun _ => full _ _) hypotheses)

theorem distinct_target_payloads : model.denote (forward.mapPayload fieldPayload) values ≠
    model.denote (forward.mapPayload nullaryPayload) values := by
  intro same
  have recovered := denotation_congr backward (forward.mapPayload fieldPayload) (forward.mapPayload nullaryPayload) values same
  exact distinct_source_payloads (field_roundtrip_holds.symm.trans (recovered.trans nullary_roundtrip_holds))

theorem outside_checked_image (payload : ClosedTerm Const (payloadType sourceSignature))
    (present : ProofSyntax Const premises (ConstructorDataPredicates.guard sourceSignature sourceConditions payload)) :
    model.denote (forward.mapPayload payload) values ≠ model.denote outsidePayload values := by
  have checked := Soundness.extDerivation_sound (guardedRecovery payload present).erase
    (model.functionsRespectEqv_of_fullDomains full) (fun _ => trivial) assumptions_realizable
  have recovered := model.eq_of_eqv_of_fullDomains full checked
  intro same
  have backwards := denotation_congr backward (forward.mapPayload payload) outsidePayload values same
  have sourceSame := recovered.symm.trans backwards
  have forwards := denotation_congr forward payload (backward.mapPayload outsidePayload) values sourceSame
  exact outside_roundtrip_refused (forwards.symm.trans same)

def emptyConditions : ConstructorDataPredicates.Conditions Const [] [] := fun index => Fin.elim0 index
theorem empty_guard_refused :
    ¬ (model.denote (ConstructorDataPredicates.guard [] emptyConditions (.top : ClosedFormula Const)) values).down := by
  change ¬ False
  exact not_false

#print axioms storedComputation
#print axioms rowRecovery
#print axioms guardedRecovery
#print axioms field_roundtrip_holds
#print axioms nullary_roundtrip_holds
#print axioms distinct_source_payloads
#print axioms wrong_field_roundtrip_refused
#print axioms wrong_input_admitted
#print axioms distinct_target_payloads
#print axioms outside_roundtrip_refused
#print axioms outside_checked_image
#print axioms empty_guard_refused
end Mettapedia.Logic.HOL.FiniteConstructorPayloadMapControls
