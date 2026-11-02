import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorSourceGuards
import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorInactivePadding
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorAllExistence
import Mettapedia.Logic.HOL.PredicateSigmaControls
import Mettapedia.Logic.HOL.HOLLightStandardTheory

/-!
# One model of the original array and All computation profiles

Natural indices, Boolean elements, lists and tree evidence interpret the
original symbols. The element, array and All selections are distinct typed
operations. This realizes their computation premises; it is not a model of
an installed outer datatype constructor.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorEvidenceModel
open Mettapedia.Logic Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open IndexedContainerNativeVectorMethodReading (Base Const N E V W original pairs witness selection parameter)
open IndexedContainerNativeVectorInactivePadding

abbrev Tree := PredicateSigma.Controls.Evidence
def carrier : Base → Type 1
  | .number => ULift.{1} Nat
  | .element => ULift.{1} Bool
  | .vector => ULift.{1} (List Bool)
  | .evidence => ULift.{1} Tree
def inhabitant : (type : Base) → carrier type
  | .number => ULift.up 0
  | .element => ULift.up false
  | .vector => ULift.up []
  | .evidence => ULift.up .refl
def defaultValue : (type : Ty Base) → Ty.denote.{0,0} carrier type
  | .base type => inhabitant type
  | .prop => ULift.up False
  | .arr _ result => fun _ => defaultValue result
abbrev Assignment := {type : Ty Base} → Const type → Ty.denote.{0,0} carrier type
def assign {type : Ty Base} (name : Nat) (value : Ty.denote.{0,0} carrier type) (previous : Assignment) : Assignment :=
  fun {other} symbol => match symbol with
    | .parameter actual _ => if actual = name then
        if same : other = type then same.symm ▸ value else previous symbol
      else previous symbol

def elementSelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ E)) := parameter 12 _
def arraySelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ V ⇒ N ⇒ E)) := parameter 13 _
def ops := arrayOperations elementSelection arraySelection

noncomputable def meaning : Assignment :=
  assign 0 (type := N) (ULift.up 0)
    (assign 1 (type := N ⇒ N) (fun n => ULift.up (n.down+1))
      (assign 2 (type := V) (ULift.up [])
        (assign 3 (type := N ⇒ E ⇒ V ⇒ V) (fun _ h t => ULift.up (h.down :: t.down))
          (assign 4 (type := V ⇒ E) (fun v => ULift.up (v.down.headD false))
            (assign 5 (type := V ⇒ V) (fun v => ULift.up v.down.tail)
              (assign 6 (type := SelectionProofs.Selection (N ⇒ V ⇒ W))
                (HOLLightStandardTheory.selectionOperation carrier inhabitant (N ⇒ V ⇒ W))
                (assign 7 (type := W ⇒ W ⇒ W) (fun h t => ULift.up (.pair h.down t.down))
                  (assign 8 (type := W ⇒ W) (fun e => ULift.up e.down.first)
                    (assign 9 (type := W ⇒ W) (fun e => ULift.up e.down.second)
                      (assign 10 (type := W) (ULift.up .refl)
                        (assign 11 (type := SelectionProofs.Selection (N ⇒ V ⇒ W ⇒ .prop))
                          (HOLLightStandardTheory.selectionOperation carrier inhabitant (N ⇒ V ⇒ W ⇒ .prop))
                          (assign 12 (type := SelectionProofs.Selection (N ⇒ E))
                            (HOLLightStandardTheory.selectionOperation carrier inhabitant (N ⇒ E))
                            (assign 13 (type := SelectionProofs.Selection (N ⇒ V ⇒ N ⇒ E))
                              (HOLLightStandardTheory.selectionOperation carrier inhabitant (N ⇒ V ⇒ N ⇒ E))
                              (assign 20 (type := E) (ULift.up true) (fun {type} _ => defaultValue type)))))))))))))))

noncomputable def model : HenkinModel.{0,0,0} Base Const := .standard carrier meaning
def values : model.Valuation [] := fun entry => nomatch entry
theorem full : model.FullDomains := HenkinModel.fullDomains_standard _ _

theorem elementSelection_holds : model.models (SelectionProofs.principle elementSelection) := by
  intro predicate _ value _ present
  exact HOLLightStandardTheory.selectionOperation_specified carrier inhabitant (N ⇒ E) predicate ⟨value,present⟩
theorem arraySelection_holds : model.models (SelectionProofs.principle arraySelection) := by
  intro predicate _ value _ present
  exact HOLLightStandardTheory.selectionOperation_specified carrier inhabitant (N ⇒ V ⇒ N ⇒ E) predicate ⟨value,present⟩
theorem allSelection_holds : model.models (SelectionProofs.principle selection) := by
  intro predicate _ value _ present
  exact HOLLightStandardTheory.selectionOperation_specified carrier inhabitant (N ⇒ V ⇒ W ⇒ .prop) predicate ⟨value,present⟩

theorem elementRecursion_holds : model.models (ops.recursionLaw E) := by
  intro initial _ step _
  let f : ULift.{1} Nat → ULift.{1} Bool := fun n => Nat.rec initial (fun k r => step r (ULift.up k)) n.down
  refine ⟨f,trivial,?_,?_⟩
  · rfl
  · intro n _; rfl
theorem arrayRecursion_holds : model.models (ops.recursionLaw (V ⇒ N ⇒ E)) := by
  intro initial _ step _
  let f : ULift.{1} Nat → (ULift.{1} (List Bool) → ULift.{1} Nat → ULift.{1} Bool) :=
    fun n => Nat.rec initial (fun k r => step r (ULift.up k)) n.down
  refine ⟨f,trivial,?_,?_⟩
  · intro vector _ slot _; rfl
  · intro n _ vector _ slot _; rfl
theorem allRecursion_holds : model.models (NaturalRecursionProofs.statement original.zero original.successor (V ⇒ W ⇒ .prop)) := by
  intro initial _ step _
  let f : ULift.{1} Nat → (ULift.{1} (List Bool) → ULift.{1} Tree → ULift Prop) :=
    fun n => Nat.rec initial (fun k r => step r (ULift.up k)) n.down
  refine ⟨f,trivial,?_,?_⟩
  · intro vector _ evidence _; rfl
  · intro n _ vector _ evidence _; rfl
theorem head_holds : model.models ops.headLaw := by intro n _ h _ t _; rfl
theorem tail_holds : model.models ops.tailLaw := by intro n _ h _ t _; rfl
theorem induction_holds : model.models (NaturalRecursionProofs.inductionPrinciple original.zero original.successor) := by
  intro predicate _ clauses n _
  rcases n with ⟨n⟩
  induction n with
  | zero => exact clauses.1
  | succ n previous => exact clauses.2 (ULift.up n) trivial (previous trivial)

def allAssumptions : List (ClosedFormula Const) :=
  [SelectionProofs.principle selection, NaturalRecursionProofs.statement original.zero original.successor (V ⇒ W ⇒ .prop),
    (NativeVectorAll.Reading.operations original selection).headLaw, (NativeVectorAll.Reading.operations original selection).tailLaw]
def inductionLaw := NaturalRecursionProofs.inductionPrinciple original.zero original.successor
def assumptions : List (ClosedFormula Const) := inductionLaw :: (ops.assumptions [] ++ allAssumptions)

def inductionProof : ProofSyntax Const assumptions inductionLaw := .hyp ⟨0,by decide⟩
def arrayPremises : ops.ComputationPremises assumptions where
  elementChoice := .hyp ⟨1,by decide⟩
  elementRecursion := .hyp ⟨2,by decide⟩
  arrayChoice := .hyp ⟨3,by decide⟩
  arrayRecursion := .hyp ⟨4,by decide⟩
  head := .hyp ⟨5,by decide⟩
  tail := .hyp ⟨6,by decide⟩
def allPremises : NativeVectorAll.Existence.ComputationPremises original selection assumptions where
  choice := .hyp ⟨7,by decide⟩
  recursion := .hyp ⟨8,by decide⟩
  head := .hyp ⟨9,by decide⟩
  tail := .hyp ⟨10,by decide⟩
theorem inductionProof_free : inductionProof.FunctionExtensionalityFree := by trivial
theorem arrayPremises_free : arrayPremises.FunctionExtensionalityFree := by trivial
theorem allPremises_free : allPremises.FunctionExtensionalityFree := by trivial

theorem arrayAssumptions_realizable : Soundness.SatisfiesHyps model values (ops.assumptions []) := by
  intro formula present
  simp only [VectorChildArrays.Operations.assumptions,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl | rfl | rfl | rfl | rfl
  · exact elementSelection_holds
  · exact elementRecursion_holds
  · exact arraySelection_holds
  · exact arrayRecursion_holds
  · exact head_holds
  · exact tail_holds
theorem allAssumptions_realizable : Soundness.SatisfiesHyps model values allAssumptions := by
  intro formula present
  simp only [allAssumptions,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl | rfl | rfl
  · exact allSelection_holds
  · exact allRecursion_holds
  · exact head_holds
  · exact tail_holds
theorem assumptions_realizable : Soundness.SatisfiesHyps model values assumptions := by
  intro formula present
  simp only [assumptions,List.mem_cons,List.mem_append] at present
  rcases present with rfl | present | present
  · exact induction_holds
  · exact arrayAssumptions_realizable _ present
  · exact allAssumptions_realizable _ present
theorem sound {formula : ClosedFormula Const} (proof : ProofSyntax Const assumptions formula) : (model.denote formula values).down :=
  Soundness.extDerivation_sound proof.erase (model.functionsRespectEqv_of_fullDomains full) (fun _ => trivial) assumptions_realizable

#print axioms assumptions_realizable
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorEvidenceModel
