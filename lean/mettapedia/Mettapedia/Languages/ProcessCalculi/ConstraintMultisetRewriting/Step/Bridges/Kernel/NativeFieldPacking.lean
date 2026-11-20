import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeFieldMeaning
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.SourceProducts

/-!
# Source product packing of the ten native fields

The nine products use the actual pair and projection symbols at the actual
field types. Their interpretation is obtained from exact source projection
and reconstruction readings in one accepted history. No representation of a
source product as Lean pairs, or atomicity of an arbitrary source operator,
is assumed.

Equal packed states then determine equal semantic field values. This is a
boundary lemma for successive calls, not a certificate-ingress procedure,
a record-stream execution theorem or a native memory-layout refinement.
Concrete projection-law reads remain separate from these conditional results.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeFieldPacking

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution TypeFamilySemantics NativeClauseData NativeFieldSchema

universe w

def productSignature (ops : Operations) (first second pair : Ty) : SourceProducts.Signature where
  first := first.toHOL
  second := second.toHOL
  pair := pair.toHOL
  constructor := .const (.constant ops.c4 (.function first (.function second pair))
    (by simp only [Ty.toHOL_function]))
  left := .const (.constant ops.c51 (.function pair first)
    (by simp only [Ty.toHOL_function]))
  right := .const (.constant ops.c52 (.function pair second)
    (by simp only [Ty.toHOL_function]))

/-- The outer product comes first; the final product holds drops and policy. -/
def products (ops : Operations) : Fin 9 → SourceProducts.Signature :=
  ![productSignature ops (t1 ops) (t21 ops) (t22 ops),
    productSignature ops (t4 ops) (t20 ops) (t21 ops),
    productSignature ops (t8 ops) (t19 ops) (t20 ops),
    productSignature ops (t11 ops) (t18 ops) (t19 ops),
    productSignature ops (t8 ops) (t17 ops) (t18 ops),
    productSignature ops (t12 ops) (t16 ops) (t17 ops),
    productSignature ops (t13 ops) (t15 ops) (t16 ops),
    productSignature ops (t13 ops) (t14 ops) (t15 ops),
    productSignature ops (t12 ops) (t5 ops) (t14 ops)]

structure Indices where
  first : Nat
  second : Nat
  pair : Nat

def readProduct? (signature : SourceProducts.Signature) (state : Registered.State)
    (indices : Indices) : Option (SourceProducts.Readings signature state) := do
  return ⟨← ExactFormulaReadback.read? state indices.first signature.firstLaw,
    ← ExactFormulaReadback.read? state indices.second signature.secondLaw,
    ← ExactFormulaReadback.read? state indices.pair signature.pairLaw⟩

structure Readings (ops : Operations) (state : Registered.State) where
  laws : (index : Fin 9) → SourceProducts.Readings (products ops index) state

abbrev Fields (ops : Operations) (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :=
  (field : Field) → HOL.Ty.denote.{0,w+1} model.Carrier (field.type ops)

noncomputable def denoteFields {ops : Operations}
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) {context : HOL.Ctx AtomicTy}
    (fields : (field : Field) → HOL.Term Symbol context (field.type ops))
    (values : model.Valuation context) : Fields ops model :=
  fun field => model.denote (fields field) @values

noncomputable def semanticPack (ops : Operations)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (fields : Fields ops model) : (signature ops).State model :=
  (products ops 0).construct model (fields .context)
    ((products ops 1).construct model (fields .names)
      ((products ops 2).construct model (fields .typeRows)
        ((products ops 3).construct model (fields .termRows)
          ((products ops 4).construct model (fields .dbRows)
            ((products ops 5).construct model (fields .theoremRows)
              ((products ops 6).construct model (fields .nameMap)
                ((products ops 7).construct model (fields .typeMap)
                  ((products ops 8).construct model (fields .drops) (fields .policy)))))))))

theorem pack_denote (ops : Operations)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) {context : HOL.Ctx AtomicTy}
    (fields : (field : Field) → HOL.Term Symbol context (field.type ops))
    (values : model.Valuation context) :
    model.denote (pack ops fields) @values = semanticPack ops model (denoteFields model fields @values) := by
  rfl

theorem received_constructor_injective (product : SourceProducts.Signature)
    (commands : List Registered.Command) (state : Registered.State)
    (accepted : Registered.replayFrom SourceProfileModels.policy
      (Registered.empty SourceProfile.primitiveContext) commands = some state)
    (readings : SourceProducts.Readings product state)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    let model := (SourceProfileModels.sourceReplayFrame commands state accepted).frame.model other assignment
    ∀ first second otherFirst otherSecond,
      product.construct model first second = product.construct model otherFirst otherSecond →
        first = otherFirst ∧ second = otherSecond := by
  dsimp only
  let equivalence := SourceProducts.receivedEquivalence product commands state accepted readings other assignment
  intro first second otherFirst otherSecond same
  change equivalence.symm (first, second) = equivalence.symm (otherFirst, otherSecond) at same
  have pairs := equivalence.symm.injective same
  exact ⟨congrArg Prod.fst pairs, congrArg Prod.snd pairs⟩

theorem semanticPack_injective (ops : Operations)
    (commands : List Registered.Command) (state : Registered.State)
    (accepted : Registered.replayFrom SourceProfileModels.policy
      (Registered.empty SourceProfile.primitiveContext) commands = some state)
    (readings : Readings ops state)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    let model := (SourceProfileModels.sourceReplayFrame commands state accepted).frame.model other assignment
    Function.Injective (semanticPack ops model) := by
  dsimp only
  intro first second same
  unfold semanticPack at same
  have context := received_constructor_injective (products ops 0) commands state accepted
    (readings.laws 0) other assignment _ _ _ _ same
  have names := received_constructor_injective (products ops 1) commands state accepted
    (readings.laws 1) other assignment _ _ _ _ context.2
  have typeRows := received_constructor_injective (products ops 2) commands state accepted
    (readings.laws 2) other assignment _ _ _ _ names.2
  have termRows := received_constructor_injective (products ops 3) commands state accepted
    (readings.laws 3) other assignment _ _ _ _ typeRows.2
  have dbRows := received_constructor_injective (products ops 4) commands state accepted
    (readings.laws 4) other assignment _ _ _ _ termRows.2
  have theoremRows := received_constructor_injective (products ops 5) commands state accepted
    (readings.laws 5) other assignment _ _ _ _ dbRows.2
  have nameMap := received_constructor_injective (products ops 6) commands state accepted
    (readings.laws 6) other assignment _ _ _ _ theoremRows.2
  have typeMap := received_constructor_injective (products ops 7) commands state accepted
    (readings.laws 7) other assignment _ _ _ _ nameMap.2
  have drops := received_constructor_injective (products ops 8) commands state accepted
    (readings.laws 8) other assignment _ _ _ _ typeMap.2
  funext field
  cases field
  · exact context.1
  · exact names.1
  · exact typeRows.1
  · exact termRows.1
  · exact dbRows.1
  · exact theoremRows.1
  · exact nameMap.1
  · exact typeMap.1
  · exact drops.1
  · exact drops.2

theorem pack_fields_iff (ops : Operations)
    (commands : List Registered.Command) (state : Registered.State)
    (accepted : Registered.replayFrom SourceProfileModels.policy
      (Registered.empty SourceProfile.primitiveContext) commands = some state)
    (readings : Readings ops state)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    let model := (SourceProfileModels.sourceReplayFrame commands state accepted).frame.model other assignment
    ∀ {firstContext secondContext : HOL.Ctx AtomicTy}
      (first : (field : Field) → HOL.Term Symbol firstContext (field.type ops))
      (second : (field : Field) → HOL.Term Symbol secondContext (field.type ops))
      (firstValues : model.Valuation firstContext) (secondValues : model.Valuation secondContext),
      model.denote (pack ops first) @firstValues = model.denote (pack ops second) @secondValues ↔
        ∀ field, model.denote (first field) @firstValues = model.denote (second field) @secondValues := by
  dsimp only
  intro firstContext secondContext first second firstValues secondValues
  rw [pack_denote, pack_denote]
  constructor
  · intro same field
    exact congrFun (semanticPack_injective ops commands state accepted readings other assignment same) field
  · intro same
    exact congrArg (semanticPack ops _) (funext same)

theorem different_field_refused (ops : Operations)
    (commands : List Registered.Command) (state : Registered.State)
    (accepted : Registered.replayFrom SourceProfileModels.policy
      (Registered.empty SourceProfile.primitiveContext) commands = some state)
    (readings : Readings ops state)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    let model := (SourceProfileModels.sourceReplayFrame commands state accepted).frame.model other assignment
    ∀ {firstContext secondContext : HOL.Ctx AtomicTy}
      (first : (field : Field) → HOL.Term Symbol firstContext (field.type ops))
      (second : (field : Field) → HOL.Term Symbol secondContext (field.type ops))
      (firstValues : model.Valuation firstContext) (secondValues : model.Valuation secondContext)
      (field : Field),
      model.denote (first field) @firstValues ≠ model.denote (second field) @secondValues →
        model.denote (pack ops first) @firstValues ≠ model.denote (pack ops second) @secondValues := by
  dsimp only
  intro firstContext secondContext first second firstValues secondValues field different same
  exact different ((pack_fields_iff ops commands state accepted readings other assignment
    first second firstValues secondValues).mp same field)

/-- An equality at a successive-call state boundary transports every actual
field label. The target frame and knowledge have not been reset here. -/
theorem successive_call_cells (ops : Operations) (table : Fin 29 → Syntax ops)
    (commands : List Registered.Command) (state : Registered.State)
    (accepted : Registered.replayFrom SourceProfileModels.policy
      (Registered.empty SourceProfile.primitiveContext) commands = some state)
    (readings : Readings ops state)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    let model := (SourceProfileModels.sourceReplayFrame commands state accepted).frame.model other assignment
    ∀ (first second : Fin 29)
      (firstValues : model.Valuation ((table first).locals.map Ty.toHOL))
      (secondValues : model.Valuation ((table second).locals.map Ty.toHOL)),
      model.denote (pack ops (table first).after) @firstValues =
        model.denote (pack ops (table second).before) @secondValues →
      ∀ field, cell table model (table first).after field @firstValues =
        cell table model (table second).before field @secondValues := by
  dsimp only
  intro first second firstValues secondValues same field
  have fields := (pack_fields_iff ops commands state accepted readings other assignment
    (table first).after (table second).before firstValues secondValues).mp same field
  simp only [cell, fields]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeFieldPacking
