import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeChildConditions
import Mettapedia.Logic.HOL.VectorTreeSuccessorFixture

/-!
# A function-vector profile over the actual recursive-space carrier

The original scalar and recursive-space carriers and provider meanings are
retained. A vector is an ordered function from natural positions to space
values; its separate source index remains explicit. Nil is constant bottom,
cons prepends, and head/tail observe zero/successor. Bare functions need not
reflect the length when padding is a stored value. This profile makes no
unindexed length-reflection or list-representation comparison claim.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeFunctionVectorFixture
open Mettapedia.Logic Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open FiniteConstructorFieldEmbeddingControls (Base N A E P Number Element Space carriers inhabitants filler)
open VectorTreeFieldEmbedding
abbrev V : Ty Base := N ⇒ E

inductive Const : Ty Base → Type where
  | old {type : Ty Base} : VectorTreeSuccessorFixture.Const type → Const type
  | nil : Const V
  | cons : Const (N ⇒ E ⇒ V ⇒ V)
  | head : Const (V ⇒ E)
  | tail : Const (V ⇒ V)
  | selection (type : Ty Base) : Const (SelectionProofs.Selection type)

noncomputable def meaning : {type : Ty Base} → Const type → Ty.denote.{0,0} carriers type
  | _,.old constant => VectorTreeSuccessorFixture.meaning constant
  | _,.nil => fun _ => Mettapedia.Languages.HOLLight.RecursiveSpaceSemantics.bottom filler
  | _,.cons => fun _ first rest position => if position.down = 0 then first else rest (ULift.up (position.down-1))
  | _,.head => fun vector => vector (ULift.up 0)
  | _,.tail => fun vector position => vector (ULift.up (position.down+1))
  | _,.selection type => HOLLightStandardTheory.selectionOperation carriers inhabitants type

noncomputable def model : HenkinModel.{0,0,0} Base Const := .standard carriers meaning
def values : model.Valuation [] := fun index => nomatch index
theorem full : model.FullDomains := HenkinModel.fullDomains_standard _ _

def embed {Γ : Ctx Base} {type : Ty Base} (term : Term VectorTreeSuccessorFixture.Const Γ type) : Term Const Γ type :=
  mapConst Const.old term

def given : Inputs Const [] N A E where
  raw := embed VectorTreeSuccessorFixture.given.raw
  zero := embed VectorTreeSuccessorFixture.given.zero
  children := embed VectorTreeSuccessorFixture.given.children
  payloadSelection := embed VectorTreeSuccessorFixture.given.payloadSelection
  fieldSelection := embed VectorTreeSuccessorFixture.given.fieldSelection

def zero : ClosedTerm Const N := embed VectorTreeSuccessorFixture.zero
def successor : ClosedTerm Const (N ⇒ N) := embed VectorTreeSuccessorFixture.successor
def one : ClosedTerm Const N := .app successor zero
def numeral : Nat → ClosedTerm Const N
  | 0 => zero
  | n+1 => .app successor (numeral n)
def bottom : ClosedTerm Const E := embed (.const (.old .bottom))
def onlyTrue : ClosedTerm Const (A ⇒ .prop) := embed VectorTreeSuccessorFixture.onlyTrue
def numbers : ClosedTerm Const (N ⇒ .prop) := .lam .top

def original : NativeVectorComputationRows.Operations Base Const where
  number := N
  element := E
  vector := V
  result := E
  zero := zero
  successor := successor
  nil := .const .nil
  cons := .const .cons
  head := .const .head
  tail := .const .tail
  selection := .const (.selection (N ⇒ V ⇒ E))

def elementSelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ E)) := .const (.selection _)
def arraySelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ V ⇒ N ⇒ E)) := .const (.selection _)
def readerSelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ V ⇒ E ⇒ .prop)) := .const (.selection _)
def ops := IndexedVectorTreeNativeChildConditions.ReaderGuard.arrays original elementSelection arraySelection

theorem zero_meaning : model.denote zero values = ULift.up 0 := rfl
theorem successor_meaning (n : Number) : model.denote successor values n = ULift.up (n.down+1) := rfl
theorem numeral_meaning (n : Nat) : model.denote (numeral n) values = ULift.up n := by
  induction n with
  | zero => rfl
  | succ n previous => change ULift.up ((model.denote (numeral n) values).down+1) = ULift.up (n+1); rw [previous]

theorem payload_selection_holds : model.models (SelectionProofs.principle given.payloadSelection) :=
  VectorTreeSuccessorFixture.payload_selection_holds
theorem field_selection_holds : model.models (SelectionProofs.principle given.fieldSelection) :=
  VectorTreeSuccessorFixture.field_selection_holds
theorem raw_injective_holds : model.models (ConstructorProjections.fieldInjective given.raw) :=
  VectorTreeSuccessorFixture.constructor_injective_holds

theorem choice_holds (type : Ty Base) : model.models (SelectionProofs.principle (.const (.selection type))) := by
  intro predicate _ point _ present
  exact HOLLightStandardTheory.selectionOperation_specified carriers inhabitants type predicate ⟨point,present⟩

theorem element_recursion_holds : model.models (ops.recursionLaw E) := by
  intro initial _ step _
  let sequence : Number → Space := fun n => Nat.rec initial (fun k previous => step previous (ULift.up k)) n.down
  refine ⟨sequence,trivial,?_,?_⟩
  · rfl
  · intro n _; rfl

theorem array_recursion_holds : model.models (ops.recursionLaw (V ⇒ N ⇒ E)) := by
  intro initial _ step _
  let sequence : Number → ((Number → Space) → Number → Space) :=
    fun n => Nat.rec initial (fun k previous => step previous (ULift.up k)) n.down
  refine ⟨sequence,trivial,?_,?_⟩
  · intro vector _ position _; rfl
  · intro n _ vector _ position _; rfl

theorem head_holds : model.models ops.headLaw := by
  intro n _ first _ rest _
  rfl

theorem tail_holds : model.models ops.tailLaw := by
  intro n _ first _ rest _ position _
  change (if position.down+1 = 0 then first else rest (ULift.up (position.down+1-1))) = rest position
  simp only [Nat.add_one_ne_zero,if_false,Nat.add_sub_cancel]
  cases position
  rfl

theorem array_assumptions_realizable : Soundness.SatisfiesHyps model values (ops.assumptions []) := by
  intro formula present
  simp only [VectorChildArrays.Operations.assumptions,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (model.models_iff_denote_closed _ values).mp (choice_holds _)
  · exact (model.models_iff_denote_closed _ values).mp element_recursion_holds
  · exact (model.models_iff_denote_closed _ values).mp (choice_holds _)
  · exact (model.models_iff_denote_closed _ values).mp array_recursion_holds
  · exact (model.models_iff_denote_closed _ values).mp head_holds
  · exact (model.models_iff_denote_closed _ values).mp tail_holds

def separationLaw := NaturalNumeralProofs.separation zero successor
def injectivityLaw := NaturalNumeralProofs.injectivity successor
def inductionLaw := NaturalRecursionProofs.inductionPrinciple zero successor
def assumptions : List (ClosedFormula Const) := separationLaw :: injectivityLaw :: inductionLaw :: ops.assumptions []
def arithmetic : SuccessorOrder.PeanoEvidence successor zero assumptions :=
  ⟨.hyp ⟨0,by decide⟩,.hyp ⟨1,by decide⟩,.hyp ⟨2,by decide⟩⟩
def premises : ops.ComputationPremises assumptions :=
  ((ops.assumptionPremises.prepend inductionLaw).prepend injectivityLaw).prepend separationLaw
theorem arithmetic_free : arithmetic.Free := by trivial
theorem premises_free : premises.FunctionExtensionalityFree :=
  ((ops.assumptionPremises.prepend inductionLaw).prepend injectivityLaw).prepend_free _
    ((ops.assumptionPremises.prepend inductionLaw).prepend_free _ (ops.assumptionPremises.prepend_free _ ops.assumptionPremises_free))

theorem assumptions_realizable : Soundness.SatisfiesHyps model values assumptions := by
  intro formula present
  simp only [assumptions,List.mem_cons] at present
  rcases present with rfl | rfl | rfl | present
  · intro n _ same
    have impossible : n.down+1 = (0:Nat) := congrArg ULift.down same
    exact Nat.noConfusion impossible
  · intro n _ m _
    constructor
    · intro same; apply ULift.ext; exact Nat.succ.inj (congrArg ULift.down same)
    · intro same; cases same; rfl
  · intro predicate _ clauses n _
    rcases n with ⟨n⟩
    induction n with
    | zero => exact clauses.1
    | succ n previous => exact clauses.2 (ULift.up n) trivial (previous trivial)
  · exact array_assumptions_realizable _ present

def paddedCons : ClosedTerm Const V := ops.toSignature.consValue zero bottom ops.nil

/-- The source index is essential: bare functions can erase an additional
bottom entry. This is not an unindexed vector representation theorem. -/
theorem erased_length_collision : model.denote paddedCons values = model.denote ops.nil values := by
  funext position
  change (if position.down = 0 then model.denote bottom values else model.denote bottom values) = model.denote bottom values
  simp only [ite_self]

theorem distinct_indices : model.denote zero values ≠ model.denote one values := by
  intro same
  exact Nat.noConfusion (congrArg ULift.down same).symm

def unrestricted : ClosedTerm Const (E ⇒ .prop) := .lam .top
def bottomMember : ProofSyntax Const [] (.app unrestricted bottom) :=
  .impE (.eqPropER (.beta bottom .top)) .topI
def paddedMember : ProofSyntax Const [] (ops.toSignature.member unrestricted one paddedCons) :=
  ops.toSignature.cons_member unrestricted zero bottom ops.nil bottomMember (ops.toSignature.nil_member unrestricted)

theorem paddedMember_free : paddedMember.FunctionExtensionalityFree := by
  exact ops.toSignature.cons_member_free _ _ _ _ _ _ (by trivial) (ops.toSignature.nil_member_free _)

theorem padded_member_holds : (model.denote (ops.toSignature.member unrestricted one paddedCons) values).down :=
  Soundness.extDerivation_sound paddedMember.erase (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => trivial) (by intro formula impossible; cases impossible)

#print axioms assumptions_realizable
#print axioms raw_injective_holds
#print axioms premises_free
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeFunctionVectorFixture
