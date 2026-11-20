import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeInstanceFields
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeFieldPacking
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.SourceProofSuffix
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeProductClosure

/-!
# Native readback in one explicitly carried source frame

The frame is an input throughout. Exact source facts are interpreted in this
one model, including facts earned by a proof-only suffix. No fresh replay-frame
choice is made between the instance, field and product meanings.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeReceivedFrame

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution TypeFamilySemantics NativeClauseData NativeFieldSchema

universe w

theorem meanings {state : Registered.State} (profile : SourceProfileModels.ProfileFrame.{w} state)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    ReferenceBooleanSemantics.Meanings (profile.frame.model other assignment) :=
  ReferenceBooleanSemantics.meanings_of_invariant _ profile.invariant other assignment

theorem instance_meaning {state : Registered.State} (profile : SourceProfileModels.ProfileFrame.{w} state)
    {native : NativeClauseReadback.Signature} (contract : NativeInstanceReadback.Signature native)
    (reading : NativeInstanceReadback.Reading contract state)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    let model := profile.frame.model other assignment
    ∀ allow source record effect target, contract.instanceValue model allow source record effect target ↔
      native.stepValue model source record target ∧
      target = contract.resultValue model source record effect ∧ (allow source record effect).down := by
  exact (contract.equation_meaning (profile.frame.model other assignment)
    (profile.frame.model_fullDomains other assignment) (meanings profile other assignment)).mp
    (ExactFormulaReadback.read_models profile.frame other assignment _ reading.equation)

theorem cases_meaning {state : Registered.State} (profile : SourceProfileModels.ProfileFrame.{w} state)
    (native : NativeClauseReadback.Signature) (clauses : List native.Clause)
    (reading : NativeClauseReadback.Reading native clauses state)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    let model := profile.frame.model other assignment
    ∀ source record target, native.stepValue model source record target ↔
      ∃ clause ∈ clauses, native.admitsClause model clause source record target := by
  have disjunction := SourceDisjunction.equation_meaning native.disjunction
    (profile.frame.model other assignment) (profile.frame.model_fullDomains other assignment)
    (meanings profile other assignment)
    (ExactFormulaReadback.read_models profile.frame other assignment _ reading.disjunction)
  exact (native.equation_meaning (profile.frame.model other assignment)
    (profile.frame.model_fullDomains other assignment) (meanings profile other assignment)
    disjunction clauses).mp
    (ExactFormulaReadback.read_models profile.frame other assignment _ reading.fact)

theorem field_cases {state : Registered.State} (profile : SourceProfileModels.ProfileFrame.{w} state)
    (ops : Operations) (logical : NativeFieldMeaning.LogicalOperations ops) (table : Fin 29 → Syntax ops)
    (reading : NativeClauseReadback.Reading (signature ops) (NativeFieldMeaning.clauses table) state)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    let model := profile.frame.model other assignment
    ∀ source record target, (signature ops).stepValue model source record target ↔
      ∃ index values, NativeFieldMeaning.Realizes model (table index) source record target values := by
  dsimp only
  intro source record target
  rw [cases_meaning profile (signature ops) (NativeFieldMeaning.clauses table) reading other assignment]
  constructor
  · rintro ⟨clause, member, holds⟩
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    exact ⟨index, (NativeFieldMeaning.sourceClause_meaning (profile.frame.model other assignment)
      logical (profile.frame.model_fullDomains other assignment) (meanings profile other assignment)
      (table index) source record target).mp holds⟩
  · rintro ⟨index, values, holds⟩
    exact ⟨(table index).sourceClause, List.mem_ofFn.mpr ⟨index, rfl⟩,
      (NativeFieldMeaning.sourceClause_meaning (profile.frame.model other assignment)
        logical (profile.frame.model_fullDomains other assignment) (meanings profile other assignment)
        (table index) source record target).mpr ⟨values, holds⟩⟩

theorem prepared_instance {state : Registered.State} (profile : SourceProfileModels.ProfileFrame.{w} state)
    {ops : Operations} (table : Fin 29 → Syntax ops)
    (contract : NativeInstanceReadback.Signature (signature ops))
    (logical : NativeFieldMeaning.LogicalOperations ops)
    (cases : NativeClauseReadback.Reading (signature ops) (NativeFieldMeaning.clauses table) state)
    (reading : NativeInstanceReadback.Reading contract state)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) (generation : Field → Nat) :
    let model := profile.frame.model other assignment
    let domains := NativeFieldExecution.sourceDomains profile.frame other assignment
    ∀ allow source record effect target, contract.instanceValue model allow source record effect target ↔
      NativeInstanceFields.preparedAdmits table contract model domains
        (NativeInstanceFields.sourcePacks table model) allow generation source record effect target := by
  dsimp only
  intro allow source record effect target
  rw [instance_meaning profile contract reading other assignment]
  rw [field_cases profile ops logical table cases other assignment]
  exact NativeInstanceFields.adapter_admission_iff table contract _ _
    (NativeInstanceFields.sourcePacks table _) allow generation source record effect target

theorem product_models {state : Registered.State} (profile : SourceProfileModels.ProfileFrame.{w} state)
    (product : SourceProducts.Signature) (reading : SourceProducts.Readings product state)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    let model := profile.frame.model other assignment
    model.models product.firstLaw ∧ model.models product.secondLaw ∧ model.models product.pairLaw :=
  ⟨ExactFormulaReadback.read_models profile.frame other assignment _ reading.first,
    ExactFormulaReadback.read_models profile.frame other assignment _ reading.second,
    ExactFormulaReadback.read_models profile.frame other assignment _ reading.pair⟩

theorem constructor_injective {state : Registered.State} (profile : SourceProfileModels.ProfileFrame.{w} state)
    (product : SourceProducts.Signature) (reading : SourceProducts.Readings product state)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    let model := profile.frame.model other assignment
    ∀ first second otherFirst otherSecond,
      product.construct model first second = product.construct model otherFirst otherSecond →
        first = otherFirst ∧ second = otherSecond := by
  dsimp only
  have laws := product_models profile product reading other assignment
  let equivalence := product.equivalence (profile.frame.model other assignment)
    (profile.frame.model_fullDomains other assignment) (meanings profile other assignment)
    laws.1 laws.2.1 laws.2.2
  intro first second otherFirst otherSecond same
  change equivalence.symm (first, second) = equivalence.symm (otherFirst, otherSecond) at same
  have pairs := equivalence.symm.injective same
  exact ⟨congrArg Prod.fst pairs, congrArg Prod.snd pairs⟩

noncomputable def productFrame {before : Registered.State} {ops : Operations}
    (profile : SourceProfileModels.ProfileFrame.{w} before) (result : NativeProductClosure.Result before ops) :
    SourceProfileModels.ProfileFrame.{w} result.after :=
  SourceProofSuffix.carry profile result.instances result.nodes result.replayed

theorem productFrame_model {before : Registered.State} {ops : Operations}
    (profile : SourceProfileModels.ProfileFrame.{w} before) (result : NativeProductClosure.Result before ops)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    (productFrame profile result).frame.model other assignment = profile.frame.model other assignment :=
  SourceProofSuffix.carry_model profile result.instances result.nodes result.replayed other assignment

noncomputable def retainInstance {before : Registered.State} {ops : Operations}
    (result : NativeProductClosure.Result before ops) {native : NativeClauseReadback.Signature}
    (contract : NativeInstanceReadback.Signature native) (reading : NativeInstanceReadback.Reading contract before) :
    NativeInstanceReadback.Reading contract result.after where
  equation := SourceProofSuffix.retain_read result.instances result.nodes result.replayed reading.equation
  effect := SourceProofSuffix.retain_read result.instances result.nodes result.replayed reading.effect

noncomputable def retainCases {before : Registered.State} {ops : Operations}
    (result : NativeProductClosure.Result before ops) (native : NativeClauseReadback.Signature)
    (clauses : List native.Clause) (reading : NativeClauseReadback.Reading native clauses before) :
    NativeClauseReadback.Reading native clauses result.after where
  disjunction := SourceProofSuffix.retain_read result.instances result.nodes result.replayed reading.disjunction
  fact := SourceProofSuffix.retain_read result.instances result.nodes result.replayed reading.fact

theorem prepared_after_products {before : Registered.State}
    (profile : SourceProfileModels.ProfileFrame.{w} before) {ops : Operations}
    (result : NativeProductClosure.Result before ops) (table : Fin 29 → Syntax ops)
    (contract : NativeInstanceReadback.Signature (signature ops))
    (logical : NativeFieldMeaning.LogicalOperations ops)
    (cases : NativeClauseReadback.Reading (signature ops) (NativeFieldMeaning.clauses table) before)
    (reading : NativeInstanceReadback.Reading contract before)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) (generation : Field → Nat) :
    let final := productFrame profile result
    let model := final.frame.model other assignment
    let domains := NativeFieldExecution.sourceDomains final.frame other assignment
    ∀ allow source record effect target, contract.instanceValue model allow source record effect target ↔
      NativeInstanceFields.preparedAdmits table contract model domains
        (NativeInstanceFields.sourcePacks table model) allow generation source record effect target :=
  prepared_instance (productFrame profile result) table contract logical
    (retainCases result (signature ops) (NativeFieldMeaning.clauses table) cases)
    (retainInstance result contract reading) other assignment generation

theorem packing_injective {state : Registered.State} (profile : SourceProfileModels.ProfileFrame.{w} state)
    (ops : Operations) (readings : NativeFieldPacking.Readings ops state)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    Function.Injective (NativeFieldPacking.semanticPack ops (profile.frame.model other assignment)) := by
  intro first second same
  unfold NativeFieldPacking.semanticPack at same
  have context := constructor_injective profile (NativeFieldPacking.products ops 0)
    (readings.laws 0) other assignment _ _ _ _ same
  have names := constructor_injective profile (NativeFieldPacking.products ops 1)
    (readings.laws 1) other assignment _ _ _ _ context.2
  have typeRows := constructor_injective profile (NativeFieldPacking.products ops 2)
    (readings.laws 2) other assignment _ _ _ _ names.2
  have termRows := constructor_injective profile (NativeFieldPacking.products ops 3)
    (readings.laws 3) other assignment _ _ _ _ typeRows.2
  have dbRows := constructor_injective profile (NativeFieldPacking.products ops 4)
    (readings.laws 4) other assignment _ _ _ _ termRows.2
  have theoremRows := constructor_injective profile (NativeFieldPacking.products ops 5)
    (readings.laws 5) other assignment _ _ _ _ dbRows.2
  have nameMap := constructor_injective profile (NativeFieldPacking.products ops 6)
    (readings.laws 6) other assignment _ _ _ _ theoremRows.2
  have typeMap := constructor_injective profile (NativeFieldPacking.products ops 7)
    (readings.laws 7) other assignment _ _ _ _ nameMap.2
  have drops := constructor_injective profile (NativeFieldPacking.products ops 8)
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

theorem packing_after_products {before : Registered.State}
    (profile : SourceProfileModels.ProfileFrame.{w} before) {ops : Operations}
    (result : NativeProductClosure.Result before ops)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    Function.Injective (NativeFieldPacking.semanticPack ops
      ((productFrame profile result).frame.model other assignment)) :=
  packing_injective (productFrame profile result) ops result.readings other assignment

noncomputable section

/-- Semantic values and the meaning they realize are indexed by the same
actual frame. A second frame requires an explicit transport. -/
structure CallView {state : Registered.State} (profile : SourceProfileModels.ProfileFrame.{w} state)
    (native : NativeClauseReadback.Signature) (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    {ops : Operations} (table : Fin 29 → Syntax ops)
    (packs : NativeInstanceFields.PackAdapter native table (profile.frame.model other assignment))
    (index : Fin 29) where
  source : native.State (profile.frame.model other assignment)
  record : native.Record (profile.frame.model other assignment)
  target : native.State (profile.frame.model other assignment)
  locals : (profile.frame.model other assignment).Valuation ((table index).locals.map Ty.toHOL)
  realizes : source = packs.before index locals ∧ record = packs.record index locals ∧
    target = packs.after index locals ∧
    ((profile.frame.model other assignment).denote (table index).guard locals).down

def actualCallView {state : Registered.State} (profile : SourceProfileModels.ProfileFrame.{w} state)
    {ops : Operations} (table : Fin 29 → Syntax ops) (index : Fin 29)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) : Type (w+1) :=
  CallView profile (signature ops) other assignment table
    (NativeInstanceFields.sourcePacks table (profile.frame.model other assignment)) index

end

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeReceivedFrame
