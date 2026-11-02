import Mettapedia.Logic.HOL.MixedConstructorPayloadMaps
import Mettapedia.TypeTheory.FiniteConstructorMaps

/-!
# The retained mixed-payload map denotes the general payload map

The source and target keep their number fields and map the middle element
field. The theorem relates the actual HOL lambda program to the general
constructor payload functor at every valuation. It is a denotation law, not
a native C-refinement or source-parser adequacy theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.MixedConstructorPayloadMaps
open FiniteConstructorEncoding
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    {number source target : Ty Base}

theorem handler_denote (model : HenkinModel.{u,v,w} Base Const)
    (fieldMap : Term Const Γ (source ⇒ target)) (targetHandler : Term Const Γ (handlerType [number,target,number]))
    (values : model.Valuation Γ) (index : Ty.denote model.Carrier number)
    (element : Ty.denote model.Carrier source) (shape : Ty.denote model.Carrier number) :
    model.denote (handler fieldMap targetHandler) values index element shape =
      model.denote targetHandler values index (model.denote fieldMap values element) shape := by
  have compared := abstractArguments_denote model [number,source,number] (handlerBody fieldMap targetHandler)
    (fun values arguments => model.denote targetHandler values arguments.1
      (model.denote fieldMap values arguments.2.1) arguments.2.2.1)
    (by
      intro Ξ images arguments later
      change model.denote (HOL.subst images targetHandler) later (model.denote arguments.1 later)
        (model.denote (HOL.subst images fieldMap) later (model.denote arguments.2.1 later))
        (model.denote arguments.2.2.1 later) = _
      exact congrArg₂ (fun function mapped => function (model.denote arguments.1 later)
        (mapped (model.denote arguments.2.1 later)) (model.denote arguments.2.2.1 later))
        (Soundness.denote_subst model images targetHandler later) (Soundness.denote_subst model images fieldMap later))
    values (index,element,shape,PUnit.unit)
  exact compared

inductive FieldLabel where | number | element
  deriving DecidableEq
def fieldSignature : Mettapedia.TypeTheory.FiniteConstructorEncoding.Signature (SortCode := FieldLabel) :=
  [[.number,.element,.number]]
def fieldValues (model : HenkinModel.{u,v,w} Base Const) (number element : Ty Base) :
    FieldLabel → Type (max (u+1) w)
  | .number => Ty.denote model.Carrier number
  | .element => Ty.denote model.Carrier element
def semanticFieldMap (model : HenkinModel.{u,v,w} Base Const)
    (function : Ty.denote model.Carrier (source ⇒ target)) :
    ∀ label, fieldValues model number source label → fieldValues model number target label
  | .number => fun value => value
  | .element => function

theorem mapPayload_denote (model : HenkinModel.{u,v,w} Base Const)
    (fieldMap : Term Const Γ (source ⇒ target)) (payload : Term Const Γ (Payload number source))
    (values : model.Valuation Γ) :
    model.denote (mapPayload fieldMap payload) values =
      Mettapedia.TypeTheory.FiniteConstructorEncoding.mapPayload
        (semanticFieldMap (number := number) model (model.denote fieldMap values)) fieldSignature (model.denote payload values) := by
  funext targetHandler
  change (model.denote (weaken payload) (model.extend values targetHandler))
    (model.denote (handler (weaken fieldMap) (.var .vz)) (model.extend values targetHandler)) =
      model.denote payload values (fun index element shape => targetHandler index (model.denote fieldMap values element) shape)
  rw [Soundness.denote_weaken]
  apply congrArg (model.denote payload values)
  funext index element shape
  rw [handler_denote,Soundness.denote_weaken]
  rfl

#print axioms handler_denote
#print axioms mapPayload_denote

namespace Controls
open Mettapedia.TypeTheory.FiniteConstructorEncoding
abbrev SourceValues : FieldLabel → Type := fun _ => Nat
abbrev TargetValues : FieldLabel → Type
  | .number => Nat
  | .element => Bool
def lowerFields : ∀ label, SourceValues label → TargetValues label
  | .number => fun value => value
  | .element => fun value => value != 0
def raiseFields : ∀ label, TargetValues label → SourceValues label
  | .number => fun value => value
  | .element => fun value => if value then 1 else 0
def validFields : ∀ label, SourceValues label → Prop
  | .number => fun _ => True
  | .element => fun value => value < 2
theorem fieldRecovery (label : FieldLabel) (value : SourceValues label) (valid : validFields label value) :
    raiseFields label (lowerFields label value) = value := by
  cases label with
  | number => rfl
  | element =>
      change value < 2 at valid
      cases value with
      | zero => rfl
      | succ predecessor =>
          have bounded : predecessor ≤ 0 := Nat.le_of_succ_le_succ (Nat.le_of_lt_succ valid)
          have only : predecessor = 0 := Nat.eq_zero_of_le_zero bounded
          subst predecessor
          rfl
def one : Mettapedia.TypeTheory.FiniteConstructorEncoding.Data SourceValues fieldSignature :=
  ⟨⟨0,Nat.zero_lt_succ 0⟩,(0:Nat),(1:Nat),(0:Nat),PUnit.unit⟩
def two : Mettapedia.TypeTheory.FiniteConstructorEncoding.Data SourceValues fieldSignature :=
  ⟨⟨0,Nat.zero_lt_succ 0⟩,(0:Nat),(2:Nat),(0:Nat),PUnit.unit⟩
theorem admitted_middle_roundtrip :
    Mettapedia.TypeTheory.FiniteConstructorEncoding.mapPayload raiseFields fieldSignature
      (Mettapedia.TypeTheory.FiniteConstructorEncoding.mapPayload lowerFields fieldSignature
        (Mettapedia.TypeTheory.FiniteConstructorEncoding.encode SourceValues fieldSignature one)) =
      Mettapedia.TypeTheory.FiniteConstructorEncoding.encode SourceValues fieldSignature one := by
  apply mapPayload_roundtrip lowerFields raiseFields validFields fieldRecovery
  exact ⟨one,by change True ∧ (1:Nat) < 2 ∧ True ∧ True; decide +kernel,rfl⟩
theorem excluded_middle_collapses :
    Mettapedia.TypeTheory.FiniteConstructorEncoding.mapPayload lowerFields fieldSignature
      (Mettapedia.TypeTheory.FiniteConstructorEncoding.encode SourceValues fieldSignature one) =
    Mettapedia.TypeTheory.FiniteConstructorEncoding.mapPayload lowerFields fieldSignature
      (Mettapedia.TypeTheory.FiniteConstructorEncoding.encode SourceValues fieldSignature two) := by
  rw [mapPayload_encode,mapPayload_encode]
  rfl
theorem original_middles_distinct :
    Mettapedia.TypeTheory.FiniteConstructorEncoding.encode SourceValues fieldSignature one ≠
      Mettapedia.TypeTheory.FiniteConstructorEncoding.encode SourceValues fieldSignature two := by
  intro same
  have fields := Sigma.mk.inj (Mettapedia.TypeTheory.FiniteConstructorEncoding.encode_injective SourceValues fieldSignature same)
  have impossible : (1:Nat) = 2 := congrArg (fun data => data.2.1) (eq_of_heq fields.2)
  cases impossible
end Controls

#print axioms Controls.admitted_middle_roundtrip
#print axioms Controls.original_middles_distinct
end Mettapedia.Logic.HOL.MixedConstructorPayloadMaps
