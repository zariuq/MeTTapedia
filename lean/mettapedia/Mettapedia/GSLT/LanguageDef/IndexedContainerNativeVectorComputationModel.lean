import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorEvidenceModel

/-!
# Natural indices, arbitrary elements and nontrivial evidence

The original primitive and array/All profiles share one standard model for
any inhabited element carrier. An explicit residual constant assignment
interprets further source operations; the displayed primitive assignments
take precedence. Tree evidence retains its pair structure.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorComputationModel
open Mettapedia.Logic Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open IndexedContainerNativeVectorMethodReading (Base Const N E V W original pairs witness selection)
open IndexedContainerNativeVectorEvidenceModel (Tree elementSelection arraySelection ops allAssumptions assumptions)

def carrier (Element : Type) : Base → Type 1
  | .number => ULift.{1} Nat
  | .element => ULift.{1} Element
  | .vector => ULift.{1} (List Element)
  | .evidence => ULift.{1} Tree

variable {Element : Type}
def inhabitant (defaultElement : Element) : (type : Base) → carrier Element type
  | .number => .up 0
  | .element => .up defaultElement
  | .vector => .up []
  | .evidence => .up .refl
def defaultValue (defaultElement : Element) : (type : Ty Base) → Ty.denote.{0,0} (carrier Element) type
  | .base type => inhabitant defaultElement type
  | .prop => .up False
  | .arr _ result => fun _ => defaultValue defaultElement result
abbrev Assignment (Element : Type) := {type : Ty Base} → Const type → Ty.denote.{0,0} (carrier Element) type
def assign {type : Ty Base} (name : Nat) (value : Ty.denote.{0,0} (carrier Element) type)
    (previous : Assignment Element) : Assignment Element :=
  fun {other} symbol => match symbol with
    | .parameter actual _ => if actual = name then
        if same : other = type then same.symm ▸ value else previous symbol
      else previous symbol

noncomputable def meaning (defaultElement : Element) (extra : Assignment Element) : Assignment Element :=
  assign 0 (type := N) (.up 0)
    (assign 1 (type := N ⇒ N) (fun n => .up (n.down+1))
      (assign 2 (type := V) (.up [])
        (assign 3 (type := N ⇒ E ⇒ V ⇒ V) (fun _ head tail => .up (head.down :: tail.down))
          (assign 4 (type := V ⇒ E) (fun vector => .up (vector.down.headD defaultElement))
            (assign 5 (type := V ⇒ V) (fun vector => .up vector.down.tail)
              (assign 6 (type := SelectionProofs.Selection (N ⇒ V ⇒ W))
                (HOLLightStandardTheory.selectionOperation (carrier Element) (inhabitant defaultElement) (N ⇒ V ⇒ W))
                (assign 7 (type := W ⇒ W ⇒ W) (fun head tail => .up (.pair head.down tail.down))
                  (assign 8 (type := W ⇒ W) (fun evidence => .up evidence.down.first)
                    (assign 9 (type := W ⇒ W) (fun evidence => .up evidence.down.second)
                      (assign 10 (type := W) (.up .refl)
                        (assign 11 (type := SelectionProofs.Selection (N ⇒ V ⇒ W ⇒ .prop))
                          (HOLLightStandardTheory.selectionOperation (carrier Element) (inhabitant defaultElement) (N ⇒ V ⇒ W ⇒ .prop))
                          (assign 12 (type := SelectionProofs.Selection (N ⇒ E))
                            (HOLLightStandardTheory.selectionOperation (carrier Element) (inhabitant defaultElement) (N ⇒ E))
                            (assign 13 (type := SelectionProofs.Selection (N ⇒ V ⇒ N ⇒ E))
                              (HOLLightStandardTheory.selectionOperation (carrier Element) (inhabitant defaultElement) (N ⇒ V ⇒ N ⇒ E)) extra)))))))))))))

noncomputable def model (defaultElement : Element) (extra : Assignment Element) : HenkinModel.{0,0,0} Base Const :=
  .standard (carrier Element) (meaning defaultElement extra)

variable (defaultElement : Element) (extra : Assignment Element)
local notation "M" => model defaultElement extra
def values : (model defaultElement extra).Valuation [] := fun entry => nomatch entry
theorem full : (model defaultElement extra).FullDomains := HenkinModel.fullDomains_standard _ _

theorem elementSelection_holds : (model defaultElement extra).models (SelectionProofs.principle elementSelection) := by
  intro question _ value _ present
  exact HOLLightStandardTheory.selectionOperation_specified (carrier Element) (inhabitant defaultElement)
    (N ⇒ E) question ⟨value,present⟩
theorem arraySelection_holds : (model defaultElement extra).models (SelectionProofs.principle arraySelection) := by
  intro question _ value _ present
  exact HOLLightStandardTheory.selectionOperation_specified (carrier Element) (inhabitant defaultElement)
    (N ⇒ V ⇒ N ⇒ E) question ⟨value,present⟩
theorem allSelection_holds : (model defaultElement extra).models (SelectionProofs.principle selection) := by
  intro question _ value _ present
  exact HOLLightStandardTheory.selectionOperation_specified (carrier Element) (inhabitant defaultElement)
    (N ⇒ V ⇒ W ⇒ .prop) question ⟨value,present⟩

theorem elementRecursion_holds : (model defaultElement extra).models (ops.recursionLaw E) := by
  intro initial _ step _
  let function : ULift.{1} Nat → ULift.{1} Element :=
    fun n => Nat.rec initial (fun index result => step result (.up index)) n.down
  exact ⟨function,trivial,rfl,fun _ _ => rfl⟩
theorem arrayRecursion_holds : (model defaultElement extra).models (ops.recursionLaw (V ⇒ N ⇒ E)) := by
  intro initial _ step _
  let function : ULift.{1} Nat → (ULift.{1} (List Element) → ULift.{1} Nat → ULift.{1} Element) :=
    fun n => Nat.rec initial (fun index result => step result (.up index)) n.down
  exact ⟨function,trivial,(fun _ _ _ _ => rfl),(fun _ _ _ _ _ _ => rfl)⟩
theorem allRecursion_holds : (model defaultElement extra).models (NaturalRecursionProofs.statement original.zero original.successor (V ⇒ W ⇒ .prop)) := by
  intro initial _ step _
  let function : ULift.{1} Nat → (ULift.{1} (List Element) → ULift.{1} Tree → ULift Prop) :=
    fun n => Nat.rec initial (fun index result => step result (.up index)) n.down
  refine ⟨function,trivial,?_,?_⟩
  · intro vector _ evidence _; rfl
  · intro n _ vector _ evidence _; rfl
theorem head_holds : (model defaultElement extra).models ops.headLaw := by intro n _ head _ tail _; rfl
theorem tail_holds : (model defaultElement extra).models ops.tailLaw := by intro n _ head _ tail _; rfl
theorem induction_holds : (model defaultElement extra).models (NaturalRecursionProofs.inductionPrinciple original.zero original.successor) := by
  intro predicate _ clauses n _
  rcases n with ⟨n⟩
  induction n with
  | zero => exact clauses.1
  | succ n previous => exact clauses.2 (.up n) trivial (previous trivial)

theorem separation_holds : (model defaultElement extra).models
    (NaturalNumeralProofs.separation original.zero original.successor) := by
  intro n _ same
  exact Nat.noConfusion (show n.down+1 = (0:Nat) from congrArg ULift.down same)
theorem injectivity_holds : (model defaultElement extra).models
    (NaturalNumeralProofs.injectivity original.successor) := by
  intro n _ m _
  constructor
  · intro same; apply ULift.ext; exact Nat.succ.inj (congrArg ULift.down same)
  · intro same; cases same; rfl

theorem arrayAssumptions_realizable : Soundness.SatisfiesHyps M (values defaultElement extra) (ops.assumptions []) := by
  intro formula present
  simp only [VectorChildArrays.Operations.assumptions,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl | rfl | rfl | rfl | rfl
  · exact elementSelection_holds defaultElement extra
  · exact elementRecursion_holds defaultElement extra
  · exact arraySelection_holds defaultElement extra
  · exact arrayRecursion_holds defaultElement extra
  · exact head_holds defaultElement extra
  · exact tail_holds defaultElement extra
theorem allAssumptions_realizable : Soundness.SatisfiesHyps M (values defaultElement extra) allAssumptions := by
  intro formula present
  simp only [IndexedContainerNativeVectorEvidenceModel.allAssumptions,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl | rfl | rfl
  · exact allSelection_holds defaultElement extra
  · exact allRecursion_holds defaultElement extra
  · exact head_holds defaultElement extra
  · exact tail_holds defaultElement extra
theorem assumptions_realizable : Soundness.SatisfiesHyps M (values defaultElement extra) assumptions := by
  intro formula present
  simp only [IndexedContainerNativeVectorEvidenceModel.assumptions,List.mem_cons,List.mem_append] at present
  rcases present with rfl | present | present
  · exact induction_holds defaultElement extra
  · exact arrayAssumptions_realizable defaultElement extra _ present
  · exact allAssumptions_realizable defaultElement extra _ present

#print axioms assumptions_realizable
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorComputationModel
