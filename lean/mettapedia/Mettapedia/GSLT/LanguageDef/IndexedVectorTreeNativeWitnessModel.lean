import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeSourceReading
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreePayloadRealizationControls
import Mettapedia.Logic.HOL.ConstructorFunctionPairs
import Mettapedia.Logic.HOL.VectorTabulationPrograms
import Mettapedia.Logic.HOL.SuccessorOrderArithmetic

/-!
# A typed native witness world with independent original payloads

Original payloads are natural numbers. The common stored carrier is the
existing recursive-space model of the complete natural-payload signature.
Vectors are indexed natural-position functions. The evidence type remains a
distinct HOL base type even when its semantic carrier is that same Space.

Only the displayed typed constant entries receive their declared meanings;
other parameter/type pairs receive constructed inhabitants. This is a model
of the selected native interface, not a source-universe interpretation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeWitnessModel

open Mettapedia.Logic Mettapedia.Logic.HOL Mettapedia.TypeTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open FiniteConstructorEncoding

namespace Native
export IndexedContainerNativeVectorMethodReading (Base Const N E V W parameter original pairs witness selection)
end Native

noncomputable section

abbrev Number := ULift.{1} Nat
abbrev RawPayload := IndexedVectorTreePayloadRealizationControls.PayloadValue Nat
abbrev filler := IndexedVectorTreePayloadRealizationControls.filler Nat
abbrev Space := IndexedVectorTreePayloadRealizationControls.Space Nat
abbrev P : Ty Native.Base := payloadType [[Native.N],[Native.N,Native.N]]
abbrev Raw : Ty Native.Base := ConstructorProjections.Constructor Native.N P (Native.N ⇒ Native.E) Native.E

def carrier : Native.Base → Type 1
  | .number => Number
  | .element => Space
  | .vector => Number → Space
  | .evidence => Space

def bottomValue : Space := RecursiveSpaceSemantics.bottom filler

def baseInhabitant : (base : Native.Base) → carrier base
  | .number => .up 0
  | .element => bottomValue
  | .vector => fun _ => bottomValue
  | .evidence => bottomValue

def inhabitant : (type : Ty Native.Base) → Ty.denote.{0,0} carrier type
  | .base base => baseInhabitant base
  | .prop => .up False
  | .arr _ result => fun _ => inhabitant result

structure Entry where
  name : Nat
  type : Ty Native.Base
  value : Ty.denote.{0,0} carrier type

def lookup : List Entry → (name : Nat) → (type : Ty Native.Base) → Option (Ty.denote.{0,0} carrier type)
  | [],_,_ => none
  | entry :: rest,name,type =>
      if entry.name = name then
        if same : entry.type = type then some (cast (congrArg (Ty.denote carrier) same) entry.value)
        else lookup rest name type
      else lookup rest name type

def choose (type : Ty Native.Base) : Ty.denote.{0,0} carrier (SelectionProofs.Selection type) :=
  HOLLightStandardTheory.selectionOperation carrier baseInhabitant type

def elementSelection : ClosedTerm Native.Const (SelectionProofs.Selection (Native.N ⇒ Native.E)) := Native.parameter 16 _
def arraySelection : ClosedTerm Native.Const (SelectionProofs.Selection (Native.N ⇒ Native.V ⇒ Native.N ⇒ Native.E)) := Native.parameter 17 _

def arrays : VectorChildArrays.Operations Native.Const where
  number := Native.N
  element := Native.E
  vector := Native.V
  zero := Native.original.zero
  successor := Native.original.successor
  nil := Native.original.nil
  cons := Native.original.cons
  head := Native.original.head
  tail := Native.original.tail
  elementSelection := elementSelection
  arraySelection := arraySelection

def shiftedSelection : ClosedTerm Native.Const (VectorTabulation.Shifted.Selection arrays.toSignature) := Native.parameter 32 _
def offsetSelection : ClosedTerm Native.Const (VectorTabulation.Offset.Selection arrays.toSignature) := Native.parameter 33 _

def coreTable : List Entry :=
  [⟨0,Native.N,.up 0⟩,
   ⟨1,Native.N ⇒ Native.N,fun n => .up (n.down+1)⟩,
   ⟨2,Native.V,fun _ => bottomValue⟩,
   ⟨3,Native.N ⇒ Native.E ⇒ Native.V ⇒ Native.V,
      fun _ first rest position => if position.down = 0 then first else rest (.up (position.down-1))⟩,
   ⟨4,Native.V ⇒ Native.E,fun vector => vector (.up 0)⟩,
   ⟨5,Native.V ⇒ Native.V,fun vector position => vector (.up (position.down+1))⟩,
   ⟨6,SelectionProofs.Selection (Native.N ⇒ Native.V ⇒ Native.W),choose _⟩,
   ⟨10,Native.W,bottomValue⟩,
   ⟨11,SelectionProofs.Selection (Native.N ⇒ Native.V ⇒ Native.W ⇒ .prop),choose _⟩,
   ⟨12,Raw,fun tag payload children => RecursiveSpaceSemantics.construct filler tag.down payload (fun n => children (.up n))⟩,
   ⟨13,Native.E,bottomValue⟩,
   ⟨14,SelectionProofs.Selection P,choose _⟩,
   ⟨15,SelectionProofs.Selection Native.N,choose _⟩,
   ⟨16,SelectionProofs.Selection (Native.N ⇒ Native.E),choose _⟩,
   ⟨17,SelectionProofs.Selection (Native.N ⇒ Native.V ⇒ Native.N ⇒ Native.E),choose _⟩,
   ⟨18,Native.N ⇒ .prop,fun n => .up (0 < n.down)⟩,
   ⟨32,VectorTabulation.Shifted.Selection arrays.toSignature,choose (Native.N ⇒ VectorTabulation.Shifted.Result arrays.toSignature)⟩,
   ⟨33,VectorTabulation.Offset.Selection arrays.toSignature,choose (Native.N ⇒ VectorTabulation.Offset.Result arrays.toSignature)⟩]

private def interpretation (tail : List Entry) : {type : Ty Native.Base} → Native.Const type → Ty.denote.{0,0} carrier type
  | _,.parameter name type => (lookup (coreTable ++ tail) name type).getD (inhabitant type)

private def modelWith (tail : List Entry) : HenkinModel.{0,0,0} Native.Base Native.Const :=
  .standard carrier (interpretation tail)
private def emptyWith (tail : List Entry) : (modelWith tail).Valuation [] := fun index => nomatch index
private theorem fullWith (tail : List Entry) : (modelWith tail).FullDomains := HenkinModel.fullDomains_standard _ _

def raw : ClosedTerm Native.Const Raw := Native.parameter 12 _
def bottom : ClosedTerm Native.Const Native.E := Native.parameter 13 _
def payloadSelection : ClosedTerm Native.Const (SelectionProofs.Selection P) := Native.parameter 14 _
def fieldSelection : ClosedTerm Native.Const (SelectionProofs.Selection Native.N) := Native.parameter 15 _
def originalPredicate : ClosedTerm Native.Const (Native.N ⇒ .prop) := Native.parameter 18 _
def numbers : ClosedTerm Native.Const (Native.N ⇒ .prop) := PredicateProducts.full Native.N
def one : ClosedTerm Native.Const Native.N := .app Native.original.successor Native.original.zero
def numeral : Nat → ClosedTerm Native.Const Native.N
  | 0 => Native.original.zero
  | n+1 => .app Native.original.successor (numeral n)

def input : VectorTreeFieldEmbedding.Inputs Native.Const [] Native.N Native.N Native.E where
  raw := raw
  zero := Native.original.zero
  children := .lam (weaken bottom)
  payloadSelection := payloadSelection
  fieldSelection := fieldSelection

private theorem choiceWith (tail : List Entry) (type : Ty Native.Base)
    (name : Nat)
    (meaning : (modelWith tail).denote (Native.parameter name (SelectionProofs.Selection type)) (emptyWith tail) = choose type) :
    (modelWith tail).models (SelectionProofs.principle (Native.parameter name (SelectionProofs.Selection type))) := by
  intro predicate _ field _ present
  change (predicate ((modelWith tail).denote (Native.parameter name (SelectionProofs.Selection type))
    (emptyWith tail) predicate)).down
  exact (congrArg (fun selection => (predicate (selection predicate)).down) meaning).mpr
    (HOLLightStandardTheory.selectionOperation_specified carrier baseInhabitant type predicate ⟨field,present⟩)

private theorem recursionWith (tail : List Entry) (result : Ty Native.Base) :
    (modelWith tail).models (NaturalRecursionProofs.statement Native.original.zero Native.original.successor result) := by
  intro initial _ step _
  let sequence : Number → Ty.denote carrier result := fun n => Nat.rec initial (fun k previous => step previous (.up k)) n.down
  refine ⟨sequence,trivial,?_,?_⟩
  · exact (modelWith tail).eqv_refl (fullWith tail _ _)
  · intro n _
    rcases n with ⟨n⟩
    exact (modelWith tail).eqv_refl (fullWith tail _ _)

private theorem headWith (tail : List Entry) : (modelWith tail).models arrays.headLaw := by
  intro n _ first _ rest _
  rfl

private theorem tailWith (tail : List Entry) : (modelWith tail).models arrays.tailLaw := by
  intro n _ first _ rest _
  change (fun position : Number => if position.down+1 = 0 then first else rest (.up (position.down+1-1))) = rest
  funext position
  simp only [Nat.add_one_ne_zero,if_false,Nat.add_sub_cancel]

private theorem arrayWith (tail : List Entry) :
    Soundness.SatisfiesHyps (modelWith tail) (emptyWith tail) (arrays.assumptions []) := by
  intro formula present
  simp only [VectorChildArrays.Operations.assumptions,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ((modelWith tail).models_iff_denote_closed _ (emptyWith tail)).mp (choiceWith tail _ 16 rfl)
  · exact ((modelWith tail).models_iff_denote_closed _ (emptyWith tail)).mp (recursionWith tail Native.E)
  · exact ((modelWith tail).models_iff_denote_closed _ (emptyWith tail)).mp (choiceWith tail _ 17 rfl)
  · exact ((modelWith tail).models_iff_denote_closed _ (emptyWith tail)).mp (recursionWith tail (Native.V ⇒ Native.N ⇒ Native.E))
  · exact ((modelWith tail).models_iff_denote_closed _ (emptyWith tail)).mp (headWith tail)
  · exact ((modelWith tail).models_iff_denote_closed _ (emptyWith tail)).mp (tailWith tail)

def separationLaw := NaturalNumeralProofs.separation Native.original.zero Native.original.successor
def injectivityLaw := NaturalNumeralProofs.injectivity Native.original.successor
def inductionLaw := NaturalRecursionProofs.inductionPrinciple Native.original.zero Native.original.successor
def assumptions : List (ClosedFormula Native.Const) := separationLaw :: injectivityLaw :: inductionLaw :: arrays.assumptions []

private theorem assumptionsWith (tail : List Entry) :
    Soundness.SatisfiesHyps (modelWith tail) (emptyWith tail) assumptions := by
  intro formula present
  simp only [assumptions,List.mem_cons] at present
  rcases present with rfl | rfl | rfl | inherited
  · intro n _ same
    have impossible : n.down+1 = (0:Nat) := congrArg ULift.down same
    exact Nat.noConfusion impossible
  · intro n _ m _
    constructor
    · intro same
      have down := Nat.succ.inj (congrArg ULift.down same)
      cases n; cases m
      cases down
      rfl
    · intro same; cases same; rfl
  · intro predicate _ clauses n _
    rcases n with ⟨n⟩
    induction n with
    | zero => exact clauses.1
    | succ n previous => exact clauses.2 (.up n) trivial (previous trivial)
  · exact arrayWith tail _ inherited

private theorem rawWith (tail : List Entry) :
    (modelWith tail).models (ConstructorProjections.fieldInjective raw) := by
  intro tag _ payload _ children _ otherTag _ otherPayload _ otherChildren _ same
  obtain ⟨_,data,child⟩ := (RecursiveSpaceSemantics.construct_injective filler otherTag.down otherPayload
    (fun n => otherChildren (.up n)) tag.down payload (fun n => children (.up n))).mp same
  constructor
  · cases data
    exact (modelWith tail).eqv_refl (fullWith tail _ _)
  · intro n _
    rcases n with ⟨n⟩
    exact congrFun child n

private def pairInput : ConstructorFunctionPairs.Inputs arrays P where
  raw := raw
  tag := numeral 2
  payload := encode [[Native.N],[Native.N,Native.N]]
    ⟨1,by change 1 < 2; decide⟩ (Native.original.zero,Native.original.zero,PUnit.unit)
  bottom := bottom

private def pairAssumptions : List (ClosedFormula Native.Const) :=
  [ConstructorProjections.fieldInjective raw,
   VectorChildArrays.Operations.selectionLaw (Native.N ⇒ Native.E) elementSelection,
   arrays.recursionLaw Native.E]

private def pairPremises : pairInput.Premises pairAssumptions where
  choice := .hyp ⟨1,by simp [pairAssumptions]⟩
  recursion := .hyp ⟨2,by simp [pairAssumptions]⟩
  injectivity := .hyp ⟨0,by simp [pairAssumptions]⟩

private theorem pairAssumptionsWith (tail : List Entry) :
    Soundness.SatisfiesHyps (modelWith tail) (emptyWith tail) pairAssumptions := by
  intro formula present
  simp only [pairAssumptions,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl | rfl
  · exact ((modelWith tail).models_iff_denote_closed _ (emptyWith tail)).mp (rawWith tail)
  · exact ((modelWith tail).models_iff_denote_closed _ (emptyWith tail)).mp (choiceWith tail _ 16 rfl)
  · exact ((modelWith tail).models_iff_denote_closed _ (emptyWith tail)).mp (recursionWith tail Native.E)

private theorem evaluatedPairFirst :
    (modelWith []).models (PredicateSigma.firstLaw pairInput.operations) := by
  apply ((modelWith []).models_iff_denote_closed _ (emptyWith [])).mpr
  exact Soundness.extDerivation_sound (pairInput.first_law pairPremises).erase
    ((modelWith []).functionsRespectEqv_of_fullDomains (fullWith []))
    (fun _ => trivial) (pairAssumptionsWith [])

private theorem evaluatedPairSecond :
    (modelWith []).models (PredicateSigma.secondLaw pairInput.operations) := by
  apply ((modelWith []).models_iff_denote_closed _ (emptyWith [])).mpr
  exact Soundness.extDerivation_sound (pairInput.second_law pairPremises).erase
    ((modelWith []).functionsRespectEqv_of_fullDomains (fullWith []))
    (fun _ => trivial) (pairAssumptionsWith [])

private def pairTable : List Entry :=
  [⟨7,Native.W ⇒ Native.W ⇒ Native.W,
      (modelWith []).denote (τ := Native.E ⇒ Native.E ⇒ Native.E) pairInput.operations.pair (emptyWith [])⟩,
   ⟨8,Native.W ⇒ Native.W,
      (modelWith []).denote (τ := Native.E ⇒ Native.E) pairInput.operations.first (emptyWith [])⟩,
   ⟨9,Native.W ⇒ Native.W,
      (modelWith []).denote (τ := Native.E ⇒ Native.E) pairInput.operations.second (emptyWith [])⟩]

/-- The final selected Native4 world includes the actual pair programme
meanings. The private pre-interpretation above only evaluates their closed
dependencies; it is not offered as an interpretation of Native.pairs. -/
def model : HenkinModel.{0,0,0} Native.Base Native.Const := modelWith pairTable
def values : model.Valuation [] := emptyWith pairTable
theorem full : model.FullDomains := fullWith pairTable

theorem assumptions_realizable : Soundness.SatisfiesHyps model values assumptions := assumptionsWith pairTable

def arithmetic : SuccessorOrder.PeanoEvidence Native.original.successor Native.original.zero assumptions :=
  ⟨.hyp ⟨0,by simp [assumptions]⟩,.hyp ⟨1,by simp [assumptions]⟩,.hyp ⟨2,by simp [assumptions]⟩⟩
def premises : arrays.ComputationPremises assumptions :=
  ((arrays.assumptionPremises.prepend inductionLaw).prepend injectivityLaw).prepend separationLaw
theorem arithmetic_free : arithmetic.Free := by trivial
theorem premises_free : premises.FunctionExtensionalityFree :=
  ((arrays.assumptionPremises.prepend inductionLaw).prepend injectivityLaw).prepend_free separationLaw
    ((arrays.assumptionPremises.prepend inductionLaw).prepend_free injectivityLaw
      (arrays.assumptionPremises.prepend_free inductionLaw arrays.assumptionPremises_free))

def numericRecognition : ProofSyntax Native.Const assumptions (.all (.app (weaken numbers) (.var .vz))) :=
  .allI (.impE (.eqPropER (.beta (.var .vz) .top)) .topI)
theorem numericRecognition_free : numericRecognition.FunctionExtensionalityFree := by trivial
theorem numericRecognition_holds : (model.denote (.all (.app (weaken numbers) (.var .vz))) values).down :=
  Soundness.extDerivation_sound numericRecognition.erase (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => trivial) assumptions_realizable

theorem recursion_holds (result : Ty Native.Base) :
    model.models (NaturalRecursionProofs.statement Native.original.zero Native.original.successor result) :=
  recursionWith pairTable result

theorem payload_selection_holds : model.models (SelectionProofs.principle payloadSelection) := choiceWith pairTable _ 14 rfl
theorem field_selection_holds : model.models (SelectionProofs.principle fieldSelection) := choiceWith pairTable _ 15 rfl
theorem element_selection_holds : model.models (SelectionProofs.principle elementSelection) := choiceWith pairTable _ 16 rfl
theorem array_selection_holds : model.models (SelectionProofs.principle arraySelection) := choiceWith pairTable _ 17 rfl
theorem original_selection_holds : model.models (SelectionProofs.principle Native.original.selection) := choiceWith pairTable _ 6 rfl
theorem reader_selection_holds : model.models (SelectionProofs.principle Native.selection) := choiceWith pairTable _ 11 rfl
theorem shifted_selection_holds : model.models (SelectionProofs.principle shiftedSelection) := choiceWith pairTable _ 32 rfl
theorem offset_selection_holds : model.models (SelectionProofs.principle offsetSelection) := choiceWith pairTable _ 33 rfl
theorem raw_injective_holds : model.models (ConstructorProjections.fieldInjective raw) := rawWith pairTable

theorem pair_first_holds : model.models (PredicateSigma.firstLaw Native.pairs) := by
  intro first _ second _
  change (modelWith []).denote pairInput.operations.first (emptyWith [])
    ((modelWith []).denote pairInput.operations.pair (emptyWith []) first second) = first
  exact evaluatedPairFirst first trivial second trivial

theorem pair_second_holds : model.models (PredicateSigma.secondLaw Native.pairs) := by
  intro first _ second _
  change (modelWith []).denote pairInput.operations.second (emptyWith [])
    ((modelWith []).denote pairInput.operations.pair (emptyWith []) first second) = second
  exact evaluatedPairSecond first trivial second trivial

theorem zero_meaning : model.denote Native.original.zero values = (.up 0 : Number) := rfl
theorem successor_meaning (n : Number) : model.denote Native.original.successor values n = .up (n.down+1) := rfl
theorem numeral_meaning (n : Nat) : model.denote (numeral n) values = (.up n : Number) := by
  induction n with
  | zero => rfl
  | succ n previous => change ULift.up ((model.denote (numeral n) values).down+1) = ULift.up (n+1); rw [previous]

theorem witness_meaning : model.denote Native.witness values = bottomValue := rfl
theorem evidence_type_distinct : Native.W ≠ Native.E := by decide +kernel
theorem original_payload_type_distinct : Native.N ≠ Native.E := by decide +kernel

#print axioms assumptions_realizable
#print axioms numericRecognition_holds
#print axioms recursion_holds
#print axioms pair_first_holds
#print axioms pair_second_holds

#print axioms assumptionsWith
#print axioms rawWith

end
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeWitnessModel
