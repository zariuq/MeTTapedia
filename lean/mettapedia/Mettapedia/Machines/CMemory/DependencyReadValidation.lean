import Mettapedia.Machines.CMemory.ReadBlock
import Mettapedia.Machines.CMemory.DependencyValidationOperands

/-!
# Source-linked first validation on physical memory

The first preparation loop retains input indexing, null/self rejection,
existing-link membership and eager newness accumulation. Scoped locals are
restored even on return. The specification observes independent membership,
not the interpreter's own result. Allocation and the second collection loop
are not executed by this read-only fragment.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace Mettapedia.Machines.CMemory.DependencyReadValidation

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open ReadExpressions DependencyExpressionReads DependencyValidationOperands
open Lift CellPermission
open OrderedDependencyCPreparationScan (oldArray oldLimit needle)
open OrderedDependencyCPreparationCollection (inputExpression invalidCondition)
open OrderedDependencyCPreparationValidation
  (iterationSyntax loopSyntax actualLoop quotedLoop outerCondition hasMissing missing_cons)

universe u

def frame (reader array : Ptr) (index count : UInt32) (newness : Bool)
    (base : ReadExpressions.Environment) : ReadExpressions.Environment := fun name =>
  if name = "importer".toList then some (.ptr (some reader))
  else if name = "dependencies".toList then some (.ptr (some array))
  else if name = "i".toList then some (.u32 index)
  else if name = "count".toList then some (.u32 count)
  else if name = "has_new".toList then some (.bool newness) else base name

theorem frame_updates_newness (reader array : Ptr) (index count : UInt32)
    (before after : Bool) (base : ReadExpressions.Environment) :
    Function.update (frame reader array index count before base) "has_new".toList
      (some (.bool after)) = frame reader array index count after base := by
  funext name
  by_cases same : name = "has_new".toList
  · subst name
    simp [frame]
  · rw [Function.update_of_ne same]
    simp only [frame, if_neg same]

theorem frame_updates_index (reader array : Ptr) (index after count : UInt32)
    (newness : Bool) (base : ReadExpressions.Environment) :
    Function.update (frame reader array index count newness base) "i".toList
      (some (.u32 after)) = frame reader array after count newness base := by
  funext name
  by_cases same : name = "i".toList
  · subst name
    simp [frame]
  · rw [Function.update_of_ne same]
    simp only [frame, if_neg same]

theorem outer_condition_reads_current_locals (layout : ReadExpressions.Layout)
    (reader array : Ptr) (index count : UInt32) (newness : Bool)
    (base : ReadExpressions.Environment) :
    expression layout (frame reader array index count newness base) outerCondition =
      pure (.bool (decide (index < count))) := by
  simp [outerCondition, expression, expressionWith_equation, frame, resolved, binary, word]

theorem outer_increment_executes_actual_step (reader array : Ptr) (index count : UInt32)
    (newness : Bool) (base : ReadExpressions.Environment) :
    ReadLoops.increment (frame reader array index count newness base)
      OrderedDependencyCPreparationLoop.outerStep =
      pure (frame reader array (index + 1) count newness base) := by
  change (pure (Function.update (frame reader array index count newness base) "i".toList
    (some (.u32 (index + 1)))) : CProg CVal ReadExpressions.Environment) = _
  rw [frame_updates_index]

theorem restore_iteration_locals (environment : ReadExpressions.Environment)
    (value : CVal) (seen newness : Bool) :
    ReadBlock.restore "dependency".toList (environment "dependency".toList)
      (ReadBlock.restore IdentityScan.flag (environment IdentityScan.flag)
        (.finished (.next (Function.update
          (Function.update (Function.update environment "dependency".toList (some value))
            IdentityScan.flag (some (.bool seen))) "has_new".toList (some (.bool newness)))))) =
      .finished (.next (Function.update environment "has_new".toList
        (some (.bool newness)))) := by
  simp only [ReadBlock.restore]
  have previous : (Function.update environment "dependency".toList (some value))
      IdentityScan.flag = environment IdentityScan.flag :=
    Function.update_of_ne (by decide) _ _
  rw [← previous]
  rw [ReadBlock.scope_restoration_keeps_other_assignment _ IdentityScan.flag
    "has_new".toList _ _ (by decide)]
  rw [ReadBlock.scope_restoration_keeps_other_assignment _ "dependency".toList
    "has_new".toList _ _ (by decide)]

theorem accumulation_retains_eager_boolean_or (layout : ReadExpressions.Layout)
    (environment : ReadExpressions.Environment) (newness matched : Bool)
    (newnessRead : environment "has_new".toList = some (.bool newness))
    (seenRead : environment IdentityScan.flag = some (.bool matched)) :
    ReadBlock.assign layout environment OrderedDependencyCPreparationValidation.accumulation =
      pure (Function.update environment "has_new".toList (some (.bool (newness || !matched)))) := by
  change ReadBlock.booleanOrAssignment layout environment "has_new".toList
    (.unary .not (.identifier IdentityScan.flag)) = _
  have rhsRead : expression layout environment (.unary .not (.identifier IdentityScan.flag)) =
      (pure (CVal.bool (!matched)) : CProg CVal CVal) := by
    change (resolved (environment IdentityScan.flag) >>= fun actual => truth actual >>= fun value =>
      pure (CVal.bool (!value))) = _
    rw [seenRead]
    rfl
  unfold ReadBlock.booleanOrAssignment
  rw [newnessRead, rhsRead]
  rfl

section GenericIteration

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]

theorem valid_iteration_from_current_reads {P : Heap L → Prop}
    (layout : ReadExpressions.Layout) (environment : ReadExpressions.Environment)
    (loopFuel : Nat) (source : Ptr) (newness matched : Bool)
    (newnessRead : environment "has_new".toList = some (.bool newness))
    (inputRead : CTriple P (expression layout environment inputExpression)
      (fun result σ => result = .ptr (some source) ∧ P σ))
    (guardRead : CTriple P
      (expression layout (Function.update environment "dependency".toList
        (some (.ptr (some source)))) invalidCondition)
      (fun result σ => result = .bool false ∧ P σ))
    (membershipRead : CTriple P
      (ReadLoops.counted layout loopFuel
        (Function.update (Function.update environment "dependency".toList
          (some (.ptr (some source)))) IdentityScan.flag (some (.bool false)))
        (IdentityScan.scanStatement oldArray oldLimit needle))
      (fun result σ => result = .finished
        (Function.update (Function.update environment "dependency".toList
          (some (.ptr (some source)))) IdentityScan.flag (some (.bool matched))) ∧ P σ)) :
    CTriple P (ReadBlock.execute layout loopFuel 8 environment iterationSyntax)
      (fun result σ => result = .finished (.next (Function.update environment "has_new".toList
        (some (.bool (newness || !matched))))) ∧ P σ) := by
  rw [iterationSyntax, ReadBlock.declaration_retains_actual_read_and_scope]
  refine triple_bind _ inputRead fun value => ?_
  apply triple_pure
  intro same
  subst value
  simp only [ReadBlock.declared_pointer_retains_nullable_value,
    Prog.pure_eq, Prog.bind_eq, Prog.ret_bind]
  rw [ReadBlock.branch_retains_selected_body_and_continuation]
  simp only [Prog.bind_eq, Prog.bind_assoc]
  refine triple_bind _ guardRead fun value => ?_
  apply triple_pure
  intro same
  subst value
  simp only [truth, Prog.pure_eq, Prog.ret_bind, Bool.false_eq_true, ↓reduceIte,
    ReadBlock.empty_body_is_normal_completion, ReadBlock.resume]
  rw [ReadBlock.declaration_retains_actual_read_and_scope]
  simp only [expression, expressionWith_equation, ReadBlock.declared_boolean_retains_value,
    Prog.pure_eq, Prog.bind_eq, Prog.ret_bind]
  rw [IdentityScan.scanStatement, ReadBlock.nested_loop_retains_supplied_header_and_body]
  simp only [Prog.bind_eq, Prog.bind_assoc]
  refine triple_bind _ membershipRead fun result => ?_
  apply triple_pure
  intro same
  subst result
  dsimp only
  rw [OrderedDependencyCPreparationValidation.accumulation,
    ReadBlock.compound_assignment_retains_supplied_operands]
  rw [← OrderedDependencyCPreparationValidation.accumulation,
    accumulation_retains_eager_boolean_or layout
      (Function.update (Function.update environment "dependency".toList
        (some (.ptr (some source)))) IdentityScan.flag (some (.bool matched))) newness matched
    (by simp only [Function.update_of_ne (by decide : "has_new".toList ≠ IdentityScan.flag),
      Function.update_of_ne (by decide : "has_new".toList ≠ "dependency".toList), newnessRead])
    (Function.update_self _ _ _)]
  simp only [Prog.pure_eq, Prog.bind_eq, Prog.ret_bind,
    ReadBlock.empty_body_is_normal_completion,
    Function.update_of_ne (by decide : IdentityScan.flag ≠ "dependency".toList)]
  rw [restore_iteration_locals]
  exact triple_pre _ (fun _ held => ⟨rfl, held⟩) (triple_ret _ _ _)

theorem invalid_iteration_from_current_reads {P : Heap L → Prop}
    (layout : ReadExpressions.Layout) (environment : ReadExpressions.Environment)
    (loopFuel : Nat) (value : Option Ptr)
    (inputRead : CTriple P (expression layout environment inputExpression)
      (fun result σ => result = .ptr value ∧ P σ))
    (guardRead : CTriple P
      (expression layout (Function.update environment "dependency".toList
        (some (.ptr value))) invalidCondition)
      (fun result σ => result = .bool true ∧ P σ)) :
    CTriple P (ReadBlock.execute layout loopFuel 8 environment iterationSyntax)
      (fun result σ => result = .finished (.returned environment (some (.bool false))) ∧ P σ) := by
  rw [iterationSyntax, ReadBlock.declaration_retains_actual_read_and_scope]
  refine triple_bind _ inputRead fun result => ?_
  apply triple_pure
  intro same
  subst result
  simp only [ReadBlock.declared_pointer_retains_nullable_value,
    Prog.pure_eq, Prog.bind_eq, Prog.ret_bind]
  rw [ReadBlock.branch_retains_selected_body_and_continuation]
  simp only [Prog.bind_eq, Prog.bind_assoc]
  refine triple_bind _ guardRead fun result => ?_
  apply triple_pure
  intro same
  subst result
  change CTriple P (pure (ReadBlock.Result.finished (.returned
    (Function.update (Function.update environment "dependency".toList (some (.ptr value)))
      "dependency".toList (environment "dependency".toList)) (some (.bool false))))) _
  rw [Function.update_idem, Function.update_eq_self]
  exact triple_pre _ (fun _ held => ⟨rfl, held⟩) (triple_ret _ _ _)

theorem no_new_returns_before_arbitrary_continuation (layout : ReadExpressions.Layout)
    (environment : ReadExpressions.Environment) (loopFuel fuel : Nat) (rest : List CStatement)
    (notNew : environment "has_new".toList = some (.bool false)) :
    ReadBlock.execute layout loopFuel (fuel + 2) environment
      (OrderedDependencyCPreparationValidation.noNewSyntax :: rest) =
      pure (.finished (.returned environment (some (.bool true)))) := by
  have test : expression layout environment (.unary .not (.identifier "has_new".toList)) =
      (pure (CVal.bool true) : CProg CVal CVal) := by
    change (resolved (environment "has_new".toList) >>= fun value => truth value >>= fun selected =>
      pure (CVal.bool (!selected))) = _
    rw [notNew]
    rfl
  rw [OrderedDependencyCPreparationValidation.noNewSyntax,
    ReadBlock.branch_retains_selected_body_and_continuation, test]
  simp only [truth, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, ↓reduceIte]
  have returned : ReadBlock.execute layout loopFuel (fuel + 1) environment
      [.return (some (.bool true))] = pure (.finished (.returned environment (some (.bool true)))) := rfl
  rw [returned]
  simp only [Prog.pure_eq, Prog.ret_bind, ReadBlock.resume_return_does_not_enter_continuation]

theorem new_input_keeps_actual_continuation (layout : ReadExpressions.Layout)
    (environment : ReadExpressions.Environment) (loopFuel fuel : Nat) (rest : List CStatement)
    (isNew : environment "has_new".toList = some (.bool true)) :
    ReadBlock.execute layout loopFuel (fuel + 1) environment
      (OrderedDependencyCPreparationValidation.noNewSyntax :: rest) =
      ReadBlock.execute layout loopFuel fuel environment rest := by
  have test : expression layout environment (.unary .not (.identifier "has_new".toList)) =
      (pure (CVal.bool false) : CProg CVal CVal) := by
    change (resolved (environment "has_new".toList) >>= fun value => truth value >>= fun selected =>
      pure (CVal.bool (!selected))) = _
    rw [isNew]
    rfl
  rw [OrderedDependencyCPreparationValidation.noNewSyntax,
    ReadBlock.branch_retains_selected_body_and_continuation, test]
  simp only [truth, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, Bool.false_eq_true, ↓reduceIte,
    ReadBlock.empty_body_is_normal_completion, ReadBlock.resume_normal_completion_enters_continuation]

end GenericIteration

section StoreIteration

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]
variable {Id : Type} [DecidableEq Id] (addr : Id → Ptr)

theorem valid_iteration_refines_physical_input (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) {reader source : Id} (readerIn : reader ∈ D) (sourceIn : source ∈ D)
    (different : source ≠ reader)
    (closed : ∀ identity ∈ (H.forward reader).active, identity ∈ D)
    (within : (H.forward reader).count.toNat ≤ (H.forward reader).slots.length)
    (array : Ptr) (capacity : Nat) (inputs : List (Option Id)) (index : UInt32)
    (inside : index.toNat < inputs.length) (loaded : inputs[index.toNat] = some source)
    (environment : ReadExpressions.Environment) (newness : Bool)
    (importerRead : environment "importer".toList = some (.ptr (some (addr reader))))
    (arrayRead : environment "dependencies".toList = some (.ptr (some array)))
    (indexRead : environment "i".toList = some (.u32 index))
    (newnessRead : environment "has_new".toList = some (.bool newness)) (F : Heap L → Prop) :
    CTriple (InputState addr layout D H array capacity inputs F)
      (ReadBlock.execute (fields layout) (H.forward reader).active.length 8 environment iterationSyntax)
      (fun result σ => result = .finished (.next (Function.update environment "has_new".toList
        (some (.bool (newness || !decide (source ∈ (H.forward reader).active)))))) ∧
          InputState addr layout D H array capacity inputs F σ) := by
  have inputRead := input_expression_refines_nullable_identity (D := D) addr layout H array capacity inputs
    environment index inside arrayRead indexRead F
  rw [loaded] at inputRead
  have guardRead := invalid_expression_refines_null_or_self (L := L) (D := D) (reader := reader)
    addr layout H readerIn (some source)
    (by intro identity same; have equal := Option.some.inj same; rw [← equal]; exact sourceIn)
    (Function.update environment "dependency".toList (some (.ptr (some (addr source)))))
    (by rw [Function.update_of_ne (by decide : "importer".toList ≠ "dependency".toList)];
        exact importerRead) (by exact Function.update_self _ _ _)
    (DynArray (some array) capacity (inputValues addr inputs) ∗ F)
  simp only [reduceCtorEq, false_or, Option.some.injEq, decide_eq_false different] at guardRead
  have scanReads := extended_scan_operands (L := L) (D := D) addr layout H readerIn sourceIn closed
    (Function.update environment "dependency".toList (some (.ptr (some (addr source)))))
    (by rw [Function.update_of_ne (by decide : "importer".toList ≠ "dependency".toList)];
        exact importerRead) (by exact Function.update_self _ _ _)
    (DynArray (some array) capacity (inputValues addr inputs) ∗ F)
  have extent : (H.forward reader).count.toNat = (H.forward reader).active.length := by
    simpa only [List.length_map] using (Lift.active_length (spacePtr ∘ addr) within).symm
  have membershipRead := DependencyReadScan.counted_scan_refines_outer_scope scanReads extent false
  simp only [Bool.false_eq_true, false_or] at membershipRead
  exact valid_iteration_from_current_reads (fields layout) environment _ (addr source) newness
    (decide (source ∈ (H.forward reader).active)) newnessRead inputRead guardRead membershipRead

theorem invalid_iteration_refines_physical_input (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) {reader : Id} (readerIn : reader ∈ D)
    (array : Ptr) (capacity : Nat) (inputs : List (Option Id)) (index : UInt32)
    (inside : index.toNat < inputs.length) (value : Option Id) (loaded : inputs[index.toNat] = value)
    (invalid : value = none ∨ value = some reader)
    (environment : ReadExpressions.Environment) (loopFuel : Nat)
    (importerRead : environment "importer".toList = some (.ptr (some (addr reader))))
    (arrayRead : environment "dependencies".toList = some (.ptr (some array)))
    (indexRead : environment "i".toList = some (.u32 index)) (F : Heap L → Prop) :
    CTriple (InputState addr layout D H array capacity inputs F)
      (ReadBlock.execute (fields layout) loopFuel 8 environment iterationSyntax)
      (fun result σ => result = .finished (.returned environment (some (.bool false))) ∧
        InputState addr layout D H array capacity inputs F σ) := by
  have inputRead := input_expression_refines_nullable_identity (D := D) addr layout H array capacity inputs
    environment index inside arrayRead indexRead F
  rw [loaded] at inputRead
  have sourceIn : ∀ identity, value = some identity → identity ∈ D := by
    intro identity same
    rcases invalid with null | self
    · simp [null] at same
    · have identityIsReader : identity = reader := Option.some.inj (same.symm.trans self)
      simpa [identityIsReader] using readerIn
  have guardRead := invalid_expression_refines_null_or_self (L := L) (D := D) (reader := reader)
    addr layout H readerIn value sourceIn
    (Function.update environment "dependency".toList (some (.ptr (value.map addr))))
    (by rw [Function.update_of_ne (by decide : "importer".toList ≠ "dependency".toList)];
        exact importerRead) (by exact Function.update_self _ _ _)
    (DynArray (some array) capacity (inputValues addr inputs) ∗ F)
  simp only [decide_eq_true invalid] at guardRead
  exact invalid_iteration_from_current_reads (fields layout) environment loopFuel (value.map addr)
    inputRead guardRead

theorem physical_loop_validates_every_counted_input (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) {reader : Id} (readerIn : reader ∈ D)
    (closed : ∀ identity ∈ (H.forward reader).active, identity ∈ D)
    (within : (H.forward reader).count.toNat ≤ (H.forward reader).slots.length)
    (array : Ptr) (capacity : Nat) (prior remaining : List Id) (spare : List (Option Id))
    (index count : UInt32) (newness : Bool) (base : ReadExpressions.Environment)
    (position : index.toNat = prior.length) (extent : count.toNat = (prior ++ remaining).length)
    (valid : ∀ source ∈ remaining, source ≠ reader)
    (represented : ∀ source ∈ remaining, source ∈ D) (F : Heap L → Prop) :
    CTriple (InputState addr layout D H array capacity ((prior ++ remaining).map some ++ spare) F)
      (ReadBlock.loop (fields layout) (H.forward reader).active.length 8 outerCondition
        OrderedDependencyCPreparationLoop.outerStep iterationSyntax remaining.length
        (frame (addr reader) array index count newness base))
      (fun result σ => result = .finished (.next (frame (addr reader) array count count
        (newness || hasMissing (H.forward reader).active remaining) base)) ∧
          InputState addr layout D H array capacity ((prior ++ remaining).map some ++ spare) F σ) := by
  induction remaining generalizing prior index newness with
  | nil =>
    have ending : prior.length = count.toNat := by simpa using extent.symm
    have final : index = count := UInt32.toNat_inj.mp (position.trans ending)
    subst index
    rw [ReadBlock.loop.eq_def, outer_condition_reads_current_locals]
    have halted : ¬ count < count := by rw [UInt32.lt_iff_toNat_lt]; exact Nat.lt_irrefl _
    simp only [decide_eq_false halted, truth, Prog.pure_eq, Prog.bind_eq,
      Prog.ret_bind, Bool.false_eq_true, ↓reduceIte]
    have notMissing : hasMissing (H.forward reader).active [] = false := rfl
    rw [notMissing, Bool.or_false]
    exact triple_pre _ (fun _ held => ⟨rfl, held⟩) (triple_ret _ _ _)
  | cons source rest ih =>
    have active : index < count := by
      rw [UInt32.lt_iff_toNat_lt]
      simp only [List.length_append, List.length_cons] at extent
      omega
    have exactIncrement : (index + 1).toNat = index.toNat + 1 :=
      OrderedDependencyCPreparationLoop.bounded_increment_is_exact index count active
    have inside : index.toNat < ((prior ++ source :: rest).map some ++ spare).length := by
      simp only [List.length_append, List.length_map, List.length_cons]
      omega
    have loaded : ((prior ++ source :: rest).map some ++ spare)[index.toNat]'inside = some source := by
      rw [List.getElem_append_left (by simp [position])]
      rw [List.getElem_map, List.getElem_append_right (by omega)]
      simp [position]
    have nextPosition : (index + 1).toNat = (prior ++ [source]).length := by
      simp [exactIncrement, position]
    have nextExtent : count.toNat = ((prior ++ [source]) ++ rest).length := by
      simpa only [List.append_assoc, List.singleton_append] using extent
    have following := ih (prior ++ [source]) (index + 1)
      (newness || !decide (source ∈ (H.forward reader).active)) nextPosition nextExtent
      (fun identity member => valid identity (by simp [member]))
      (fun identity member => represented identity (by simp [member]))
    rw [ReadBlock.loop.eq_def, outer_condition_reads_current_locals]
    simp only [decide_eq_true active, truth, Prog.pure_eq, Prog.bind_eq,
      Prog.ret_bind, ↓reduceIte]
    have bodyRead := valid_iteration_refines_physical_input addr layout H readerIn
      (represented source (by simp)) (valid source (by simp)) closed within array capacity
      ((prior ++ source :: rest).map some ++ spare) index inside loaded
      (frame (addr reader) array index count newness base) newness
      (by rfl) (by rfl) (by rfl) (by rfl) F
    refine triple_bind _ bodyRead fun result => ?_
    apply triple_pure
    intro same
    subst result
    rw [frame_updates_newness]
    dsimp only
    rw [outer_increment_executes_actual_step]
    simp only [Prog.pure_eq, Prog.ret_bind]
    simpa only [List.append_assoc, List.singleton_append, missing_cons, Bool.or_assoc] using following

def executeNode (layout : ReadExpressions.Layout) (innerFuel fuel : Nat)
    (environment : ReadExpressions.Environment) : Option CStatement → CProg CVal ReadBlock.Result
  | some statement => ReadBlock.counted layout innerFuel 8 fuel environment statement
  | none => CProg.undefined

def quotedNoNew : Option CStatement :=
  (declaratorFunctionText? OrderedDependencyCPreparationSource.typeNames
    OrderedDependencyCPreparationSource.preparationSource.toList).bind fun function => function.body[4]?

theorem quoted_no_new_return_is_actual :
    quotedNoNew = OrderedDependencyCPreparationValidation.actualNoNew := by
  rw [quotedNoNew, OrderedDependencyCPreparationSource.complete_preparation_source_admitted]
  rfl

def executePrefix (layout : ReadExpressions.Layout) (innerFuel loopFuel decisionFuel : Nat)
    (environment : ReadExpressions.Environment) (loopNode decisionNode : Option CStatement)
    (rest : List CStatement) : CProg CVal ReadBlock.Result :=
  executeNode layout innerFuel loopFuel environment loopNode >>=
    ReadBlock.resume (fun updated => match decisionNode with
      | some decision => ReadBlock.execute layout innerFuel decisionFuel updated (decision :: rest)
      | none => CProg.undefined)

theorem quoted_prefix_retains_actual_decision (layout : ReadExpressions.Layout)
    (innerFuel loopFuel decisionFuel : Nat) (environment : ReadExpressions.Environment)
    (rest : List CStatement) :
    executePrefix layout innerFuel loopFuel decisionFuel environment quotedLoop quotedNoNew rest =
      (executeNode layout innerFuel loopFuel environment quotedLoop >>=
        ReadBlock.resume (fun updated => ReadBlock.execute layout innerFuel decisionFuel updated
          (OrderedDependencyCPreparationValidation.noNewSyntax :: rest))) := by
  rw [executePrefix, quoted_no_new_return_is_actual,
    OrderedDependencyCPreparationValidation.no_new_return_is_retained]

theorem quoted_validation_refines_physical_newness (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) {reader : Id} (readerIn : reader ∈ D)
    (closed : ∀ identity ∈ (H.forward reader).active, identity ∈ D)
    (within : (H.forward reader).count.toNat ≤ (H.forward reader).slots.length)
    (array : Ptr) (capacity : Nat) (inputs : List Id) (spare : List (Option Id))
    (savedIndex count : UInt32) (newness : Bool) (base : ReadExpressions.Environment)
    (extent : count.toNat = inputs.length) (valid : ∀ source ∈ inputs, source ≠ reader)
    (represented : ∀ source ∈ inputs, source ∈ D) (F : Heap L → Prop) :
    CTriple (InputState addr layout D H array capacity (inputs.map some ++ spare) F)
      (executeNode (fields layout) (H.forward reader).active.length inputs.length
        (frame (addr reader) array savedIndex count newness base) quotedLoop)
      (fun result σ => result = .finished (.next (frame (addr reader) array savedIndex count
        (newness || hasMissing (H.forward reader).active inputs) base)) ∧
          InputState addr layout D H array capacity (inputs.map some ++ spare) F σ) := by
  rw [OrderedDependencyCPreparationValidation.quoted_validation_loop_is_actual,
    OrderedDependencyCPreparationValidation.validation_loop_is_retained,
    executeNode, loopSyntax, ReadBlock.counted_retains_initializer_and_outer_scope,
    frame_updates_index]
  have complete := physical_loop_validates_every_counted_input addr layout H readerIn closed within
    array capacity [] inputs spare 0 count newness base rfl (by simpa using extent) valid represented F
  simp only [List.nil_append] at complete
  refine triple_bind _ complete fun result => ?_
  apply triple_pure
  intro same
  subst result
  simp only [ReadBlock.restore]
  have saved : frame (addr reader) array savedIndex count newness base "i".toList =
      some (.u32 savedIndex) := rfl
  rw [saved, frame_updates_index]
  exact triple_pre _ (fun _ held => ⟨rfl, held⟩) (triple_ret _ _ _)

theorem physical_invalid_input_returns_without_increment (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) {reader : Id} (readerIn : reader ∈ D)
    (array : Ptr) (capacity : Nat) (inputs : List (Option Id)) (index count : UInt32)
    (newness : Bool) (base : ReadExpressions.Environment) (loopFuel fuel : Nat)
    (inside : index.toNat < inputs.length) (value : Option Id) (loaded : inputs[index.toNat] = value)
    (invalid : value = none ∨ value = some reader) (active : index < count) (F : Heap L → Prop) :
    CTriple (InputState addr layout D H array capacity inputs F)
      (ReadBlock.loop (fields layout) loopFuel 8 outerCondition
        OrderedDependencyCPreparationLoop.outerStep iterationSyntax (fuel + 1)
        (frame (addr reader) array index count newness base))
      (fun result σ => result = .finished (.returned
        (frame (addr reader) array index count newness base) (some (.bool false))) ∧
          InputState addr layout D H array capacity inputs F σ) := by
  rw [ReadBlock.loop.eq_def, outer_condition_reads_current_locals]
  simp only [decide_eq_true active, truth, Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, ↓reduceIte]
  have failed := invalid_iteration_refines_physical_input addr layout H readerIn array capacity
    inputs index inside value loaded invalid (frame (addr reader) array index count newness base)
    loopFuel (by rfl) (by rfl) (by rfl) F
  refine triple_bind _ failed fun result => ?_
  apply triple_pure
  intro same
  subst result
  dsimp only
  exact triple_pre _ (fun _ held => ⟨rfl, held⟩) (triple_ret _ _ _)

theorem physical_invalid_suffix_preserves_prefix_newness (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) {reader : Id} (readerIn : reader ∈ D)
    (closed : ∀ identity ∈ (H.forward reader).active, identity ∈ D)
    (within : (H.forward reader).count.toNat ≤ (H.forward reader).slots.length)
    (array : Ptr) (capacity : Nat) (prior consumed : List Id) (value : Option Id)
    (suffix : List (Option Id)) (index count : UInt32) (newness : Bool)
    (base : ReadExpressions.Environment) (position : index.toNat = prior.length)
    (active : (prior ++ consumed).length < count.toNat)
    (valid : ∀ source ∈ consumed, source ≠ reader)
    (represented : ∀ source ∈ consumed, source ∈ D)
    (invalid : value = none ∨ value = some reader) (F : Heap L → Prop) :
    CTriple (InputState addr layout D H array capacity
      ((prior ++ consumed).map some ++ value :: suffix) F)
      (ReadBlock.loop (fields layout) (H.forward reader).active.length 8 outerCondition
        OrderedDependencyCPreparationLoop.outerStep iterationSyntax (consumed.length + 1)
        (frame (addr reader) array index count newness base))
      (fun result σ => ∃ stopped,
        stopped.toNat = (prior ++ consumed).length ∧
        result = .finished (.returned (frame (addr reader) array stopped count
          (newness || hasMissing (H.forward reader).active consumed) base) (some (.bool false))) ∧
        InputState addr layout D H array capacity
          ((prior ++ consumed).map some ++ value :: suffix) F σ) := by
  induction consumed generalizing prior index newness with
  | nil =>
    have inside : index.toNat < ((prior ++ []).map some ++ value :: suffix).length := by
      simp only [List.append_nil, List.length_append, List.length_map, List.length_cons]
      omega
    have loaded : ((prior ++ []).map some ++ value :: suffix)[index.toNat]'inside = value := by
      rw [List.getElem_append_right (by simpa using position.ge)]
      simp [position]
    have stillActive : index < count := by
      rw [UInt32.lt_iff_toNat_lt]
      simpa [position] using active
    have failed := physical_invalid_input_returns_without_increment addr layout H readerIn array
      capacity ((prior ++ []).map some ++ value :: suffix) index count newness base
      (H.forward reader).active.length 0 inside value loaded invalid stillActive F
    refine triple_post _ failed ?_
    rintro result σ ⟨rfl, holds⟩
    exact ⟨index, by simpa using position, by simp [hasMissing], holds⟩
  | cons source rest ih =>
    have currentActive : index < count := by
      rw [UInt32.lt_iff_toNat_lt]
      simp only [List.length_append, List.length_cons] at active
      omega
    have exactIncrement : (index + 1).toNat = index.toNat + 1 :=
      OrderedDependencyCPreparationLoop.bounded_increment_is_exact index count currentActive
    have inside : index.toNat < ((prior ++ source :: rest).map some ++ value :: suffix).length := by
      simp only [List.length_append, List.length_map, List.length_cons]
      omega
    have loaded : ((prior ++ source :: rest).map some ++ value :: suffix)[index.toNat]'inside =
        some source := by
      rw [List.getElem_append_left (by simp [position]), List.getElem_map,
        List.getElem_append_right (by omega)]
      simp [position]
    have following := ih (prior ++ [source]) (index + 1)
      (newness || !decide (source ∈ (H.forward reader).active))
      (by simp [exactIncrement, position])
      (by simpa only [List.append_assoc, List.singleton_append] using active)
      (fun identity member => valid identity (by simp [member]))
      (fun identity member => represented identity (by simp [member]))
    rw [ReadBlock.loop.eq_def, outer_condition_reads_current_locals]
    simp only [decide_eq_true currentActive, truth, Prog.pure_eq, Prog.bind_eq,
      Prog.ret_bind, ↓reduceIte]
    have bodyRead := valid_iteration_refines_physical_input addr layout H readerIn
      (represented source (by simp)) (valid source (by simp)) closed within array capacity
      ((prior ++ source :: rest).map some ++ value :: suffix) index inside loaded
      (frame (addr reader) array index count newness base) newness
      (by rfl) (by rfl) (by rfl) (by rfl) F
    refine triple_bind _ bodyRead fun result => ?_
    apply triple_pure
    intro same
    subst result
    rw [frame_updates_newness]
    dsimp only
    rw [outer_increment_executes_actual_step]
    simp only [Prog.pure_eq, Prog.ret_bind]
    simpa only [List.length_cons, Nat.succ_add, List.append_assoc, List.singleton_append,
      missing_cons, Bool.or_assoc] using following

theorem quoted_invalid_suffix_returns_false_and_restores_index (layout : SpaceLayout)
    {D : List Id} (H : SplitHeap Id) {reader : Id} (readerIn : reader ∈ D)
    (closed : ∀ identity ∈ (H.forward reader).active, identity ∈ D)
    (within : (H.forward reader).count.toNat ≤ (H.forward reader).slots.length)
    (array : Ptr) (capacity : Nat) (consumed : List Id) (value : Option Id)
    (suffix : List (Option Id)) (savedIndex count : UInt32) (newness : Bool)
    (base : ReadExpressions.Environment) (active : consumed.length < count.toNat)
    (valid : ∀ source ∈ consumed, source ≠ reader)
    (represented : ∀ source ∈ consumed, source ∈ D)
    (invalid : value = none ∨ value = some reader) (F : Heap L → Prop) :
    CTriple (InputState addr layout D H array capacity (consumed.map some ++ value :: suffix) F)
      (executeNode (fields layout) (H.forward reader).active.length (consumed.length + 1)
        (frame (addr reader) array savedIndex count newness base) quotedLoop)
      (fun result σ => result = .finished (.returned (frame (addr reader) array savedIndex count
        (newness || hasMissing (H.forward reader).active consumed) base) (some (.bool false))) ∧
          InputState addr layout D H array capacity (consumed.map some ++ value :: suffix) F σ) := by
  rw [OrderedDependencyCPreparationValidation.quoted_validation_loop_is_actual,
    OrderedDependencyCPreparationValidation.validation_loop_is_retained,
    executeNode, loopSyntax, ReadBlock.counted_retains_initializer_and_outer_scope,
    frame_updates_index]
  have failed := physical_invalid_suffix_preserves_prefix_newness addr layout H readerIn closed within
    array capacity [] consumed value suffix 0 count newness base rfl (by simpa using active)
    valid represented invalid F
  simp only [List.nil_append] at failed
  refine triple_bind _ failed fun result => ?_
  apply triple_exists
  intro stopped
  apply triple_pure
  intro position
  apply triple_pure
  intro same
  subst result
  simp only [ReadBlock.restore]
  have saved : frame (addr reader) array savedIndex count newness base "i".toList =
      some (.u32 savedIndex) := rfl
  rw [saved, frame_updates_index]
  exact triple_pre _ (fun _ held => ⟨rfl, held⟩) (triple_ret _ _ _)

theorem all_existing_returns_before_remaining_preparation (layout : SpaceLayout) {D : List Id}
    (H : SplitHeap Id) {reader : Id} (readerIn : reader ∈ D)
    (closed : ∀ identity ∈ (H.forward reader).active, identity ∈ D)
    (within : (H.forward reader).count.toNat ≤ (H.forward reader).slots.length)
    (array : Ptr) (capacity : Nat) (inputs : List Id) (spare : List (Option Id))
    (savedIndex count : UInt32) (base : ReadExpressions.Environment) (decisionFuel : Nat)
    (rest : List CStatement) (extent : count.toNat = inputs.length)
    (valid : ∀ source ∈ inputs, source ≠ reader)
    (represented : ∀ source ∈ inputs, source ∈ D)
    (old : ∀ source ∈ inputs, source ∈ (H.forward reader).active) (F : Heap L → Prop) :
    CTriple (InputState addr layout D H array capacity (inputs.map some ++ spare) F)
      (executePrefix (fields layout) (H.forward reader).active.length inputs.length (decisionFuel + 2)
        (frame (addr reader) array savedIndex count false base) quotedLoop quotedNoNew rest)
      (fun result σ => result = .finished (.returned
        (frame (addr reader) array savedIndex count false base) (some (.bool true))) ∧
          InputState addr layout D H array capacity (inputs.map some ++ spare) F σ) := by
  have notMissing : hasMissing (H.forward reader).active inputs = false := by
    cases present : hasMissing (H.forward reader).active inputs with
    | false => rfl
    | true =>
      obtain ⟨source, member, absent⟩ :=
        (OrderedDependencyCPreparationValidation.missing_is_independent_membership _ _).mp present
      exact False.elim (absent (old source member))
  rw [quoted_prefix_retains_actual_decision]
  have complete := quoted_validation_refines_physical_newness addr layout H readerIn closed within
    array capacity inputs spare savedIndex count false base extent valid represented F
  rw [notMissing, Bool.false_or] at complete
  refine triple_bind _ complete fun result => ?_
  apply triple_pure
  intro same
  subst result
  rw [ReadBlock.resume_normal_completion_enters_continuation]
  rw [no_new_returns_before_arbitrary_continuation (fields layout)
    (frame (addr reader) array savedIndex count false base) _ decisionFuel rest (by rfl)]
  exact triple_pre _ (fun _ held => ⟨rfl, held⟩) (triple_ret _ _ _)

theorem invalid_suffix_cannot_enter_remaining_preparation (layout : SpaceLayout)
    {D : List Id} (H : SplitHeap Id) {reader : Id} (readerIn : reader ∈ D)
    (closed : ∀ identity ∈ (H.forward reader).active, identity ∈ D)
    (within : (H.forward reader).count.toNat ≤ (H.forward reader).slots.length)
    (array : Ptr) (capacity : Nat) (consumed : List Id) (value : Option Id)
    (suffix : List (Option Id)) (savedIndex count : UInt32) (newness : Bool)
    (base : ReadExpressions.Environment) (decisionFuel : Nat) (decisionNode : Option CStatement)
    (rest : List CStatement) (active : consumed.length < count.toNat)
    (valid : ∀ source ∈ consumed, source ≠ reader)
    (represented : ∀ source ∈ consumed, source ∈ D)
    (invalid : value = none ∨ value = some reader) (F : Heap L → Prop) :
    CTriple (InputState addr layout D H array capacity (consumed.map some ++ value :: suffix) F)
      (executePrefix (fields layout) (H.forward reader).active.length (consumed.length + 1)
        decisionFuel (frame (addr reader) array savedIndex count newness base)
        quotedLoop decisionNode rest)
      (fun result σ => result = .finished (.returned (frame (addr reader) array savedIndex count
        (newness || hasMissing (H.forward reader).active consumed) base) (some (.bool false))) ∧
          InputState addr layout D H array capacity (consumed.map some ++ value :: suffix) F σ) := by
  rw [executePrefix]
  have failed := quoted_invalid_suffix_returns_false_and_restores_index addr layout H readerIn closed
    within array capacity consumed value suffix savedIndex count newness base active valid represented
    invalid F
  refine triple_bind _ failed fun result => ?_
  apply triple_pure
  intro same
  subst result
  rw [ReadBlock.resume_return_does_not_enter_continuation]
  exact triple_pre _ (fun _ held => ⟨rfl, held⟩) (triple_ret _ _ _)

end StoreIteration

namespace Controls

def base : ReadExpressions.Environment := fun _ => none

theorem zero_count_skips_input_and_existing_memory (layout : ReadExpressions.Layout)
    (reader array : Ptr) (savedIndex : UInt32) (innerFuel fuel : Nat) :
    executeNode layout innerFuel fuel (frame reader array savedIndex 0 false base) quotedLoop =
      pure (.finished (.next (frame reader array savedIndex 0 false base))) := by
  rw [OrderedDependencyCPreparationValidation.quoted_validation_loop_is_actual,
    OrderedDependencyCPreparationValidation.validation_loop_is_retained,
    executeNode, loopSyntax, ReadBlock.counted_retains_initializer_and_outer_scope,
    frame_updates_index, ReadBlock.loop.eq_def, outer_condition_reads_current_locals]
  simp only [show decide ((0 : UInt32) < 0) = false from rfl, truth,
    Prog.pure_eq, Prog.bind_eq, Prog.ret_bind, Bool.false_eq_true, ↓reduceIte, ReadBlock.restore]
  rw [show frame reader array savedIndex 0 false base "i".toList =
    some (.u32 savedIndex) from rfl, frame_updates_index]

theorem zero_count_returns_before_unavailable_continuation (layout : ReadExpressions.Layout)
    (reader array : Ptr) (savedIndex : UInt32) (innerFuel fuel decisionFuel : Nat)
    (rest : List CStatement) :
    executePrefix layout innerFuel fuel (decisionFuel + 2)
      (frame reader array savedIndex 0 false base) quotedLoop quotedNoNew rest =
      pure (.finished (.returned (frame reader array savedIndex 0 false base) (some (.bool true)))) := by
  rw [quoted_prefix_retains_actual_decision, zero_count_skips_input_and_existing_memory]
  simp only [Prog.pure_eq, Prog.bind_eq, Prog.ret_bind,
    ReadBlock.resume_normal_completion_enters_continuation]
  exact no_new_returns_before_arbitrary_continuation layout _ innerFuel decisionFuel rest rfl

theorem validation_body_fuel_exhaustion_is_not_false_return (layout : ReadExpressions.Layout)
    (environment : ReadExpressions.Environment) (innerFuel : Nat) :
    ReadBlock.execute layout innerFuel 0 environment iterationSyntax = pure .exhausted := rfl

theorem validation_loop_fuel_exhaustion_does_not_read_input (layout : ReadExpressions.Layout)
    (reader array : Ptr) (innerFuel : Nat) :
    ReadBlock.loop layout innerFuel 8 outerCondition OrderedDependencyCPreparationLoop.outerStep
      iterationSyntax 0 (frame reader array 0 1 true base) = pure .exhausted := by
  rw [ReadBlock.loop.eq_def, outer_condition_reads_current_locals]
  rfl

section UnsafeInput

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L]
  [CellPermission L (Option CVal)]

theorem indeterminate_input_is_not_null_rejection (layout : ReadExpressions.Layout)
    (environment : ReadExpressions.Environment) (array : Ptr) (index : UInt32)
    (innerFuel : Nat) (σ : Heap L)
    (arrayRead : environment "dependencies".toList = some (.ptr (some array)))
    (indexRead : environment "i".toList = some (.u32 index))
    (indeterminate : read ((σ (array + index.toNat).block).2
      (array + index.toNat).offset) = some none) :
    ¬ (ReadBlock.execute layout innerFuel 8 environment iterationSyntax).Safe act σ := by
  rw [iterationSyntax, ReadBlock.declaration_retains_actual_read_and_scope,
    input_expression_is_physical_load layout environment array index arrayRead indexRead]
  intro safe
  have inputSafe := (Prog.safe_bind _ _ _ _).mp safe |>.1
  have typedSafe := (Prog.safe_bind _ _ _ _).mp inputSafe |>.1
  have loadSafe := (Prog.safe_bind _ _ _ _).mp typedSafe |>.1
  obtain ⟨value, current⟩ := loadSafe.1
  rw [indeterminate] at current
  cases current

theorem null_short_circuit_does_not_compare_importer_lifetime
    (layout : ReadExpressions.Layout) (environment : ReadExpressions.Environment) (reader : Ptr)
    (importerRead : environment "importer".toList = some (.ptr (some reader)))
    (sourceRead : environment "dependency".toList = some (.ptr none)) :
    CTriple (fun _ : Heap L => True) (expression layout environment invalidCondition)
      (fun result _ => result = .bool true) := by
  rw [invalid_expression_retains_short_circuit layout environment reader none importerRead sourceRead]
  refine triple_bind _ (ptrEq_rule (fun _ _ => ⟨trivial, trivial⟩)) fun isNull => ?_
  apply triple_pure
  intro same
  subst isNull
  simp only [decide_true, ↓reduceIte]
  exact triple_pre act (P' := fun _ : Heap L => True) (fun _ _ => rfl)
    (triple_ret act (CVal.bool true) (fun result _ => result = CVal.bool true))

end UnsafeInput

end Controls

end Mettapedia.Machines.CMemory.DependencyReadValidation
