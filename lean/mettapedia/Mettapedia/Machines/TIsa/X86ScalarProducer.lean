import Mettapedia.Machines.TIsa.CheckedAdmission
import Mettapedia.Machines.TIsa.X86BinaryCallbackContract

/-!
# Native scalar producers and guarded resource admission

The five U64 callback bodies produce actual bytes in their output buffer.
Reading those bytes gives exactly the result admitted by the existing scalar
algebra and control/data resource step. The source guard is computed from the
selected operation and actual input cells. It accepts no supplied correctness
proof. Input keys may coincide with each other or with the output key.

The equivalence covers arbitrary source words and native states satisfying
the original body-entry observations. A constructive realization supplies a
native state for every supported source step. Controls exercise aliasing,
overflow, wrong results, missing cells, wrong control points and extra inputs.

Machine execution starts at offset four of the deployed callback, after its
ENDBR64 prefix. Host buffer preparation, invocation and resource commit retain
their own refinement obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86ScalarProducer
open Cells CellEffects Control X86CanonicalSpan
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary
abbrev Operation := X86BinaryCallbackBody.Operation
universe u
variable {Key : Type u} [DecidableEq Key]

def readback? (state : State) (entry : SharedDataEntry) : Option Word :=
  (List.range 8).foldlM (fun current index =>
    (state.mem.get? (physicalKey (entry.output + BitVec.ofNat 64 index))).map
      (fun byte => Sail.BitVec.updateSubrange' current (8 * index) 8 byte)) (0#64)

private theorem readback_fold (items : List Nat) (state : State) (entry : SharedDataEntry)
    (value current : Word)
    (present : ∀ index ∈ items,
      state.mem.get? (physicalKey (entry.output + BitVec.ofNat 64 index)) =
        some (value.extractLsb' (8 * index) 8)) :
    items.foldlM (fun current index =>
      (state.mem.get? (physicalKey (entry.output + BitVec.ofNat 64 index))).map
        (fun byte => Sail.BitVec.updateSubrange' current (8 * index) 8 byte)) current =
      some (items.foldl (fun current index =>
        Sail.BitVec.updateSubrange' current (8 * index) 8 (value.extractLsb' (8 * index) 8)) current) := by
  induction items generalizing current with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.foldlM_cons, present first (by simp), Option.map_some,
      List.foldl_cons]
    exact ih _ (fun index member => present index (by simp [member]))

theorem readback_exact (state : State) (entry : SharedDataEntry) (value : Word)
    (present : ∀ index < 8,
      state.mem.get? (physicalKey (entry.output + BitVec.ofNat 64 index)) =
        some (value.extractLsb' (8 * index) 8)) : readback? state entry = some value := by
  unfold readback?
  rw [readback_fold _ _ _ value _ (fun index member => present index (List.mem_range.mp member))]
  exact congrArg some (X86ReadWords.assembled_exact value)

def recipe (operation : Operation) (left right destination : Key) : Recipe Key where
  inputs := [left,right]
  outputs := [destination]
  guard := fun inputs outputs => match outputs with
    | [value] => (Scalar.binary (X86BinaryCallbackBody.binary operation)).evaluate inputs == some value
    | _ => false

def edge (operation : Operation) (left right destination : Key)
    (activation : Nat) (point next : Word) : Edge Key :=
  ⟨activation,point,next,recipe operation left right destination⟩

def candidate (before : Location Key → Word) (destination : Key) (value : Word) : Key → Word :=
  Function.update (fun key => before (.inr key)) destination value

theorem guard_candidate (operation : Operation) (left right destination : Key)
    (before : Location Key → Word) (value : Word) :
    (recipe operation left right destination).guard
      ((recipe operation left right destination).inputs.map (fun key => before (.inr key)))
      ((recipe operation left right destination).outputs.map (candidate before destination value)) = true ↔
      value = X86BinaryCallbackBody.evaluate operation (before (.inr left)) (before (.inr right)) := by
  simp only [recipe,List.map_cons,List.map_nil,candidate,Function.update_self,Scalar.evaluate,
    beq_iff_eq,Option.some.injEq]
  exact eq_comm

theorem eligible_iff (operation : Operation) (left right destination : Key)
    (activation : Nat) (point next : Word) (keys : Finset (Location Key))
    (before : Location Key → Word) (value : Word) :
    CheckedAdmission.eligible (edge operation left right destination activation point next) keys before
      (candidate before destination value) ↔
      (edge operation left right destination activation point next).recipe.support ⊆ keys ∧
      before (.inl activation) = point ∧
      value = X86BinaryCallbackBody.evaluate operation (before (.inr left)) (before (.inr right)) := by
  simp only [CheckedAdmission.eligible,edge]
  rw [guard_candidate]

theorem checked_iff (operation : Operation) (left right destination : Key)
    (activation : Nat) (point next : Word) (keys : Finset (Location Key))
    (before : Location Key → Word) (value : Word) :
    let selected := edge operation left right destination activation point next
    let proposed := candidate before destination value
    CheckedAdmission.step? [selected] 0 keys before proposed =
      some (CheckedAdmission.commit selected before proposed) ↔
      selected.recipe.support ⊆ keys ∧ before (.inl activation) = point ∧
      value = X86BinaryCallbackBody.evaluate operation (before (.inr left)) (before (.inr right)) := by
  dsimp only
  rw [← eligible_iff]
  simp [CheckedAdmission.step?]

theorem observes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : Operation) (state : State) (entry : SharedDataEntry)
    (facts : X86BinaryCallbackContract.BodyFacts state operation entry) :
    letI : OtherOpcodeHandlers := X86BinaryCallbackBody.handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 6).run state = .ok () after ∧
      X86StateFrame.Frame X86BinaryCallbackBody.clobbers
        (X86BinaryCallbackBody.outputWrites (narrow entry.output)) state after ∧
      readback? after entry = some (X86BinaryCallbackBody.evaluate operation facts.left facts.right) ∧
      lookup after 0 = some (1#64) ∧ lookup after 4 = some (entry.stack + (8#64)) ∧
      after.regs.get? .rip = some entry.target := by
  let : OtherOpcodeHandlers := X86BinaryCallbackBody.handlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,run,frame,value,stack,target,output,_,_⟩ :=
    X86BinaryCallbackContract.executes other vector operation state entry facts
  exact ⟨after,run,frame,readback_exact after entry _ output,value,stack,target⟩

theorem observed_exact (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : Operation) (state after : State) (entry : SharedDataEntry)
    (facts : X86BinaryCallbackContract.BodyFacts state operation entry) (value : Word) :
    letI : OtherOpcodeHandlers := X86BinaryCallbackBody.handlers other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 6).run state = .ok () after →
    readback? after entry = some value →
    value = X86BinaryCallbackBody.evaluate operation facts.left facts.right := by
  let : OtherOpcodeHandlers := X86BinaryCallbackBody.handlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨actual,run,_,output,_⟩ := observes other vector operation state entry facts
  intro executed observed
  have same := X86FuelPrefix.fetches_deterministic 6 state actual after run executed
  rw [same,observed] at output
  exact Option.some.inj output

theorem checked_iff_observed (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : Operation) (left right destination : Key) (activation : Nat) (point next : Word)
    (keys : Finset (Location Key)) (before : Location Key → Word)
    (state : State) (entry : SharedDataEntry)
    (facts : X86BinaryCallbackContract.BodyFacts state operation entry)
    (leftKnown : facts.left = before (.inr left)) (rightKnown : facts.right = before (.inr right))
    (included : (edge operation left right destination activation point next).recipe.support ⊆ keys)
    (atPoint : before (.inl activation) = point) (value : Word) :
    letI : OtherOpcodeHandlers := X86BinaryCallbackBody.handlers other
    letI : VectorOpcodeHandlers := vector
    let selected := edge operation left right destination activation point next
    let proposed := candidate before destination value
    CheckedAdmission.step? [selected] 0 keys before proposed =
      some (CheckedAdmission.commit selected before proposed) ↔
      ∃ after, (X86FuelPrefix.fetches 6).run state = .ok () after ∧ readback? after entry = some value := by
  let : OtherOpcodeHandlers := X86BinaryCallbackBody.handlers other
  let : VectorOpcodeHandlers := vector
  dsimp only
  have equivalent := checked_iff operation left right destination activation point next keys before value
  dsimp only at equivalent
  rw [equivalent]
  constructor
  · rintro ⟨_,_,rfl⟩
    obtain ⟨after,run,_,output,_⟩ := observes other vector operation state entry facts
    exact ⟨after,run,by simpa only [leftKnown,rightKnown] using output⟩
  · rintro ⟨after,run,output⟩
    refine ⟨included,atPoint,?_⟩
    simpa only [leftKnown,rightKnown] using
      (observed_exact other vector operation state after entry facts value run output)

theorem observed_resource_step (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : Operation) (left right destination : Key) (activation : Nat) (point next : Word)
    (keys : Finset (Location Key)) (before : Location Key → Word)
    (state after : State) (entry : SharedDataEntry)
    (facts : X86BinaryCallbackContract.BodyFacts state operation entry)
    (leftKnown : facts.left = before (.inr left)) (rightKnown : facts.right = before (.inr right))
    (included : (edge operation left right destination activation point next).recipe.support ⊆ keys)
    (atPoint : before (.inl activation) = point) (value : Word) :
    letI : OtherOpcodeHandlers := X86BinaryCallbackBody.handlers other
    letI : VectorOpcodeHandlers := vector
    let selected := edge operation left right destination activation point next
    let proposed := candidate before destination value
    (X86FuelPrefix.fetches 6).run state = .ok () after → readback? after entry = some value →
      (edgeProgram [selected]).theory.rewrites (encode keys before)
        (encode keys (CheckedAdmission.commit selected before proposed)) := by
  let : OtherOpcodeHandlers := X86BinaryCallbackBody.handlers other
  let : VectorOpcodeHandlers := vector
  dsimp only
  intro run output
  have equivalent := checked_iff_observed other vector operation left right destination activation point next
    keys before state entry facts leftKnown rightKnown included atPoint value
  dsimp only at equivalent ⊢
  exact CheckedAdmission.step_sound _ 0 keys before _ _ (equivalent.mpr ⟨after,run,output⟩)

theorem commit_eq_update (operation : Operation) (left right destination : Key)
    (activation : Nat) (point next : Word) (before : Location Key → Word) (value : Word) :
    CheckedAdmission.commit (edge operation left right destination activation point next) before
      (candidate before destination value) =
      Function.update (Function.update before (.inl activation) next) (.inr destination) value := by
  funext location
  cases location with
  | inl control =>
    by_cases same : control = activation
    · subst control; simp [CheckedAdmission.commit,Edge.finish,edge]
    · simp [CheckedAdmission.commit,Edge.finish,edge,same]
  | inr key =>
    by_cases same : key = destination
    · subst key; simp [CheckedAdmission.commit,CheckedAdmission.proposal,Edge.finish,edge,overwrite,
        Recipe.writes,recipe,candidate]
    · simp [CheckedAdmission.commit,Edge.finish,edge,overwrite,Recipe.writes,recipe,same]

theorem realized (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (operation : Operation) (left right destination : Key) (activation : Nat) (point next : Word)
    (keys : Finset (Location Key)) (before : Location Key → Word)
    (included : (edge operation left right destination activation point next).recipe.support ⊆ keys)
    (atPoint : before (.inl activation) = point) :
    letI : OtherOpcodeHandlers := X86BinaryCallbackBody.handlers other
    letI : VectorOpcodeHandlers := vector
    let entry := X86BinaryCallbackContract.Controls.entry
    let value := X86BinaryCallbackBody.evaluate operation (before (.inr left)) (before (.inr right))
    ∃ state after, (X86FuelPrefix.fetches 6).run state = .ok () after ∧
      readback? after entry = some value ∧
      (edgeProgram [edge operation left right destination activation point next]).theory.rewrites
        (encode keys before)
        (encode keys (Function.update (Function.update before (.inl activation) next) (.inr destination) value)) := by
  let : OtherOpcodeHandlers := X86BinaryCallbackBody.handlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨state,facts,leftKnown,rightKnown⟩ := X86BinaryCallbackContract.Controls.inhabited operation
    (before (.inr left)) (before (.inr right))
  obtain ⟨after,run,_,output,_⟩ := observes other vector operation state _ facts
  have rewritten := observed_resource_step other vector operation left right destination activation point next
    keys before state after _ facts leftKnown rightKnown included atPoint
    (X86BinaryCallbackBody.evaluate operation facts.left facts.right) run output
  dsimp only
  refine ⟨state,after,run,?_,?_⟩
  · simpa only [leftKnown,rightKnown] using output
  · simpa only [commit_eq_update,leftKnown,rightKnown] using rewritten

namespace Controls
private def before : Location Nat → Word
  | .inl 0 => 7
  | .inl _ => 99
  | .inr 0 => -1
  | .inr _ => 77
private def keys : Finset (Location Nat) := {.inl 0,.inr 0,.inl 1,.inr 1}

theorem aliased_scope : (edge (.inl .add) 0 0 0 0 7 8).recipe.support ⊆ keys := by decide
theorem aliased_correct : CheckedAdmission.step? [edge (.inl .add) 0 0 0 0 7 8] 0 keys before
    (candidate before 0 (-2#64)) =
      some (CheckedAdmission.commit (edge (.inl .add) 0 0 0 0 7 8) before (candidate before 0 (-2#64))) := by
  apply (checked_iff _ _ _ _ _ _ _ _ _ _).mpr
  exact ⟨aliased_scope,rfl,rfl⟩

theorem wrong_result_refused : CheckedAdmission.step? [edge (.inl .add) 0 0 0 0 7 8] 0 keys before
    (candidate before 0 (-1#64)) = none := by decide

theorem wrong_point_refused : CheckedAdmission.step? [edge (.inl .add) 0 0 0 0 6 8] 0 keys before
    (candidate before 0 (-2#64)) = none := by decide

theorem missing_output_refused : CheckedAdmission.step? [edge (.inl .add) 0 0 0 0 7 8] 0
    ({.inl 0} : Finset (Location Nat)) before (candidate before 0 (-2#64)) = none := by decide

theorem missing_input_refused : CheckedAdmission.step? [edge (.inl .add) 0 1 2 0 7 8] 0
    ({.inl 0,.inr 0,.inr 2} : Finset (Location Nat)) before (candidate before 2 (76#64)) = none := by decide

theorem extra_operand_refused : (recipe (.inl .add) (0 : Nat) 1 2).guard [1,2,3] [3] = false := by decide

theorem unrelated_cells_preserved :
    CheckedAdmission.commit (edge (.inl .add) 0 0 0 0 7 8) before (candidate before 0 (-2#64)) (.inl 1) = 99 ∧
    CheckedAdmission.commit (edge (.inl .add) 0 0 0 0 7 8) before (candidate before 0 (-2#64)) (.inr 1) = 77 := by
  exact ⟨rfl,rfl⟩

theorem aliased_native (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86BinaryCallbackBody.handlers other
    letI : VectorOpcodeHandlers := vector
    ∃ state after, (X86FuelPrefix.fetches 6).run state = .ok () after ∧
      readback? after X86BinaryCallbackContract.Controls.entry = some (-2#64) ∧
      (edgeProgram [edge (.inl .add) 0 0 0 0 7 8]).theory.rewrites (encode keys before)
        (encode keys (Function.update (Function.update before (.inl 0) 8) (.inr 0) (-2#64))) := by
  have output : X86BinaryCallbackBody.evaluate (.inl .add) (before (.inr 0)) (before (.inr 0)) = (-2#64) := by decide
  have witness := realized other vector (.inl .add) 0 0 0 0 7 8 keys before aliased_scope rfl
  dsimp only at witness
  rw [output] at witness
  exact witness
end Controls

#print axioms readback_exact
#print axioms checked_iff_observed
#print axioms observed_resource_step
#print axioms realized
#print axioms Controls.aliased_native

end Mettapedia.Machines.TIsa.X86ScalarProducer
