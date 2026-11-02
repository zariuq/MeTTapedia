import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorAllEvidence
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorAllInterpretation
import Mettapedia.Logic.HOL.PredicateSigmaControls
import Mettapedia.Logic.HOL.HOLLightStandardTheory

/-!
# A realizable All profile and list-indexed evidence production

Natural indices, Boolean elements, Boolean lists and tree evidence realize all
recursor and pair-projection commitments. A retained proof is produced for every
Boolean list. Independent semantic controls reject a swapped head projection
and a leaf presented as a cons bundle. No native C refinement is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.EvidenceControls

open Mettapedia.Logic
open Reading
local infixr:60 " ⇒ " => HOL.Ty.arr

inductive Base where
  | number | element | vector | evidence
  deriving DecidableEq

abbrev N : HOL.Ty Base := .base .number
abbrev E : HOL.Ty Base := .base .element
abbrev V : HOL.Ty Base := .base .vector
abbrev W : HOL.Ty Base := .base .evidence
abbrev Tree := HOL.PredicateSigma.Controls.Evidence

inductive Const : HOL.Ty Base → Type where
  | zero : Const N
  | successor : Const (N ⇒ N)
  | nil : Const V
  | cons : Const (N ⇒ E ⇒ V ⇒ V)
  | head : Const (V ⇒ E)
  | tail : Const (V ⇒ V)
  | element (value : Bool) : Const E
  | pair : Const (W ⇒ W ⇒ W)
  | first : Const (W ⇒ W)
  | second : Const (W ⇒ W)
  | witness : Const W
  | oldSelection : Const (HOL.SelectionProofs.Selection (N ⇒ V ⇒ W))
  | selection : Const (HOL.SelectionProofs.Selection (N ⇒ V ⇒ W ⇒ .prop))

def original : NativeVectorComputationRows.Operations Base Const where
  number := N
  element := E
  vector := V
  result := W
  zero := .const .zero
  successor := .const .successor
  nil := .const .nil
  cons := .const .cons
  head := .const .head
  tail := .const .tail
  selection := .const .oldSelection

def pairs : HOL.PredicateSigma.Operations Const W where
  pair := .const .pair
  first := .const .first
  second := .const .second

def witness : HOL.ClosedTerm Const W := .const .witness
def selection : HOL.ClosedTerm Const (HOL.SelectionProofs.Selection (N ⇒ V ⇒ W ⇒ .prop)) := .const .selection
def ops := operations original selection
def carrier : Base → Type 1
  | .number => ULift.{1} Nat
  | .element => ULift.{1} Bool
  | .vector => ULift.{1} (List Bool)
  | .evidence => ULift.{1} Tree

def inhabitant : (base : Base) → carrier base
  | .number => ULift.up 0
  | .element => ULift.up false
  | .vector => ULift.up []
  | .evidence => ULift.up .refl

noncomputable def meaning : {type : HOL.Ty Base} → Const type → HOL.Ty.denote.{0,0} carrier type
  | _, .zero => ULift.up 0
  | _, .successor => fun n => ULift.up (n.down + 1)
  | _, .nil => ULift.up []
  | _, .cons => fun _ h t => ULift.up (h.down :: t.down)
  | _, .head => fun values => ULift.up (values.down.headD false)
  | _, .tail => fun values => ULift.up values.down.tail
  | _, .element value => ULift.up value
  | _, .pair => fun h t => ULift.up (.pair h.down t.down)
  | _, .first => fun point => ULift.up point.down.first
  | _, .second => fun point => ULift.up point.down.second
  | _, .witness => ULift.up .refl
  | _, .oldSelection => HOL.HOLLightStandardTheory.selectionOperation carrier inhabitant (N ⇒ V ⇒ W)
  | _, .selection => HOL.HOLLightStandardTheory.selectionOperation carrier inhabitant (N ⇒ V ⇒ W ⇒ .prop)

noncomputable def model : HOL.HenkinModel.{0,0,0} Base Const := .standard carrier meaning
def emptyValues : model.Valuation [] := fun index => nomatch index

theorem selection_holds : model.models (HOL.SelectionProofs.principle selection) := by
  intro predicate _ witness _ member
  exact HOL.HOLLightStandardTheory.selectionOperation_specified carrier inhabitant (N ⇒ V ⇒ W ⇒ .prop)
    predicate ⟨witness, member⟩

theorem recursion_holds : model.models
    (HOL.NaturalRecursionProofs.statement original.zero original.successor (V ⇒ W ⇒ .prop)) := by
  intro initial _ step _
  let values : ULift.{1} Nat → (ULift.{1} (List Bool) → ULift.{1} Tree → ULift Prop) :=
    fun n => Nat.rec initial (fun k previous => step previous (ULift.up k)) n.down
  refine ⟨values, trivial, ?_, ?_⟩
  · intro value _ point _; rfl
  · intro n _ value _ point _; rfl

theorem head_holds : model.models (ops.headLaw (Γ := [])) := by
  intro n _ h _ t _
  rfl

theorem tail_holds : model.models (ops.tailLaw (Γ := [])) := by
  intro n _ h _ t _
  rfl

theorem pair_first_holds : model.models (HOL.PredicateSigma.firstLaw pairs) := by
  rw [HOL.PredicateSigma.firstLaw_denote]
  intro h _ t _
  cases h; cases t
  rfl

theorem pair_second_holds : model.models (HOL.PredicateSigma.secondLaw pairs) := by
  rw [HOL.PredicateSigma.secondLaw_denote]
  intro h _ t _
  cases h; cases t
  rfl

def assumptions : List (HOL.ClosedFormula Const) := ops.assumptions []

theorem assumptions_realizable : HOL.Soundness.SatisfiesHyps model emptyValues assumptions := by
  intro formula member
  simp only [assumptions, NativeVectorComputationRows.Operations.assumptions,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact selection_holds
  · exact recursion_holds
  · exact head_holds
  · exact tail_holds

def choice : HOL.ProofSyntax Const assumptions (HOL.SelectionProofs.principle selection) := .hyp ⟨0, by decide +kernel⟩
def recursion : HOL.ProofSyntax Const assumptions
    (HOL.NaturalRecursionProofs.statement original.zero original.successor (V ⇒ W ⇒ .prop)) := .hyp ⟨1, by decide +kernel⟩
def headLaw : HOL.ProofSyntax Const assumptions (ops.headLaw (Γ := [])) := .hyp ⟨2, by decide +kernel⟩
def tailLaw : HOL.ProofSyntax Const assumptions (ops.tailLaw (Γ := [])) := .hyp ⟨3, by decide +kernel⟩

def A : HOL.ClosedTerm Const (E ⇒ .prop) := HOL.PredicateProducts.full E
def pointPredicate : HOL.ClosedTerm Const (W ⇒ .prop) := .lam (.eq (.var .vz) (HOL.weaken witness))
def predicate : HOL.ClosedTerm Const (E ⇒ W ⇒ .prop) := .lam (HOL.weaken pointPredicate)

def head_member (value : HOL.ClosedTerm Const E) :
    HOL.ProofSyntax Const assumptions (.app (.app predicate value) witness) :=
  .impE (.eqPropER (.eqTrans (.eqApp witness (.beta value (HOL.weaken pointPredicate)))
    (.beta witness (.eq (.var .vz) (HOL.weaken witness))))) (.eqRefl witness)

def numberCode : Nat → HOL.ClosedTerm Const N
  | 0 => original.zero
  | n + 1 => .app original.successor (numberCode n)

def vectorCode : List Bool → HOL.ClosedTerm Const V
  | [] => .app ops.nilCode A
  | value :: rest => .app (.app (.app (.app ops.consCode A) (numberCode rest.length)) (.const (.element value))) (vectorCode rest)

def evidenceCode : List Bool → HOL.ClosedTerm Const W
  | [] => .app (ParameterizedPiSigmaId.AnnotatedPredicateReading.StructuralProfile.reflexivityCode witness N) original.zero
  | _ :: rest => HOL.PredicateSigma.pair pairs witness (evidenceCode rest)

def allProof : (values : List Bool) → HOL.ProofSyntax Const assumptions
    (.app (allCode original pairs witness selection A predicate (numberCode values.length) (vectorCode values)) (evidenceCode values))
  | [] => Evidence.nil_value original pairs witness selection A predicate choice recursion
  | value :: rest => Evidence.cons_value original pairs witness selection A predicate choice recursion
      (numberCode rest.length) (.const (.element value)) (vectorCode rest) headLaw tailLaw
      witness (evidenceCode rest) (head_member _) (allProof rest)

theorem allProof_free (values : List Bool) : (allProof values).FunctionExtensionalityFree := by
  induction values with
  | nil => exact Evidence.nil_value_free original pairs witness selection A predicate choice recursion True.intro True.intro
  | cons value rest previous =>
      apply Evidence.cons_value_free
      · trivial
      · trivial
      · trivial
      · trivial
      · simp [head_member, HOL.ProofSyntax.FunctionExtensionalityFree]
      · exact previous

theorem generated_evidence_holds (values : List Bool) :
    (model.denote (.app (allCode original pairs witness selection A predicate (numberCode values.length) (vectorCode values))
      (evidenceCode values)) emptyValues).down :=
  HOL.Soundness.extDerivation_sound (allProof values).erase
    (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
    (fun _ => trivial) assumptions_realizable

def packed : HOL.ClosedTerm Const W := HOL.PredicateSigma.pair pairs witness (HOL.PredicateSigma.pair pairs witness witness)

theorem first_projection_holds :
    (model.denote (.app (.app predicate (.const (.element true))) (HOL.PredicateSigma.first pairs packed)) emptyValues).down := by
  rfl

theorem swapped_projection_refused :
    ¬ (model.denote (.app (.app predicate (.const (.element true))) (HOL.PredicateSigma.second pairs packed)) emptyValues).down := by
  intro same
  have impossible := congrArg ULift.down same
  cases impossible

theorem nonpair_bundle_refused :
    ¬ (model.denote (allCode original pairs witness selection A predicate
      (numberCode 1) (vectorCode [true])) emptyValues (ULift.up (HOL.PredicateSigma.Controls.Evidence.refl))).down := by
  intro member
  have interpreted := Interpretation.cons_denote original pairs witness selection A predicate choice recursion
    model emptyValues (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
    (fun _ => trivial) assumptions_realizable (numberCode 0) (.const (.element true)) (vectorCode []) headLaw tailLaw
    (ULift.up (HOL.PredicateSigma.Controls.Evidence.refl)) (model.base_mem .evidence _)
  obtain ⟨first, _, second, _, wrong, _, _⟩ := interpreted.mp member
  change (ULift.up (HOL.PredicateSigma.Controls.Evidence.pair first.down second.down) : ULift.{1} Tree) =
    ULift.up HOL.PredicateSigma.Controls.Evidence.refl at wrong
  have impossible := congrArg ULift.down wrong
  cases impossible

#print axioms assumptions_realizable
#print axioms generated_evidence_holds
#print axioms nonpair_bundle_refused

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.EvidenceControls
