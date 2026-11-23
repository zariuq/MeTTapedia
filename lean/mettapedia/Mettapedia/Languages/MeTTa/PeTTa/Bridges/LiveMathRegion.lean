import Mettapedia.Languages.MeTTa.PeTTa.ProgramReplay

/-!
# Integer selection in a live space

Ordinary selected MeTTa bodies of the form `(if (<= $a $b) $a $b)` (or
`>=`) admit a single comparison and return on captured integers. The active
space supplies the call and its alternatives. The region interprets the
selected body and returns to the same caller with the same store and I/O.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.LiveMathRegion

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.GSLT (GSLT)
open Eval ProgramReplay

inductive Operation where
  | minimum
  | maximum
  deriving DecidableEq

def Operation.head : Operation → String
  | .minimum => "<="
  | .maximum => ">="

def Operation.leftWins : Operation → Int → Int → Bool
  | .minimum, left, right => decide (left ≤ right)
  | .maximum, left, right => decide (right ≤ left)

def Operation.run (operation : Operation) (left right : Int) : Int :=
  if operation.leftWins left right then left else right

theorem Operation.run_swap (operation : Operation) (a b : Int) :
    operation.run a b = operation.run b a := by
  cases operation <;> unfold Operation.run Operation.leftWins <;>
    by_cases left : a ≤ b <;> by_cases right : b ≤ a <;> simp [left, right] <;> omega

structure Selection where
  operation : Operation
  left : String
  right : String

def Selection.body (selection : Selection) : Atom :=
  .expression [.symbol "if",
    .expression [.symbol selection.operation.head, .var selection.left, .var selection.right],
    .var selection.left, .var selection.right]

def Selection.ofBody? : (body : Atom) → Option {selection : Selection // selection.body = body}
  | .expression [.symbol "if", .expression [.symbol head, .var left, .var right],
      .var yes, .var no] =>
    if hy : left = yes then
      if hn : right = no then
        if hm : head = "<=" then
          some ⟨⟨.minimum, left, right⟩, by simp [Selection.body, Operation.head, hy, hn, hm]⟩
        else if hm : head = ">=" then
          some ⟨⟨.maximum, left, right⟩, by simp [Selection.body, Operation.head, hy, hn, hm]⟩
        else none
      else none
    else none
  | _ => none

inductive Term where
  | pending (left right : Int)
  | returned (value : Int)

inductive Transition (operation : Operation) : Term → Term → Prop where
  | left (a b : Int) (wins : operation.leftWins a b = true) :
      Transition operation (.pending a b) (.returned a)
  | right (a b : Int) (wins : operation.leftWins a b = false) :
      Transition operation (.pending a b) (.returned b)

def theory (operation : Operation) : GSLT where
  Term := Term
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Transition operation
  rewrites_resp_left := by
    rintro _ _ _ rfl firing
    exact ⟨_, firing, rfl⟩
  rewrites_resp_right := by
    rintro _ _ _ firing rfl
    exact firing

theorem region_exact (operation : Operation) (a b answer : Int) :
    (theory operation).Step (.pending a b) (.returned answer) ↔
      operation.run a b = answer := by
  change Transition operation (.pending a b) (.returned answer) ↔ _
  constructor
  · intro firing
    cases firing <;> simp_all [Operation.run]
  · rintro rfl
    cases wins : operation.leftWins a b with
    | true => simpa [Operation.run, wins] using Transition.left a b wins
    | false => simpa [Operation.run, wins] using Transition.right a b wins

private def changeControl (base : Configuration) (control : Control) : Configuration :=
  {base with control}

private def intAtom (value : Int) : Atom := .grounded (.int value)

private theorem advance_next (fuel : Nat) (source target : Configuration)
    (stepped : LiveRegistry.step source = some target) :
    LiveRegistry.advance (fuel + 1) source = LiveRegistry.advance fuel target := by
  simp only [LiveRegistry.advance, stepped]

private theorem capture_variable (base : Configuration) (bindings : Subst) (head name : String)
    (remaining values : List Atom) (index : Nat)
    (strict : argumentIsRaw (SpaceSemantics.index base.state.core) head index = false) :
    LiveRegistry.advance 4
      (changeControl base (.arguments bindings (.function head) (.var name :: remaining) values index)) =
      {base with
        control := .arguments bindings (.function head) remaining
          (values ++ [applySubst bindings (.var name)]) (index + 1)
        frames := .sequence [] [] :: base.frames} := by
  simp only [LiveRegistry.advance, LiveRegistry.step_eq_indexed, changeControl, Eval.step,
    strict, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil]

private theorem leftWins_evaluate (selection : Selection) (a b : Int)
    (base : Configuration) (bindings : Subst)
    (left : applySubst bindings (.var selection.left) = intAtom a)
    (right : applySubst bindings (.var selection.right) = intAtom b) :
    LiveRegistry.advance 14
      (changeControl base (.evaluate bindings (.expression
        [.symbol selection.operation.head, .var selection.left, .var selection.right]))) =
      changeControl base (.returned [Effects.boolean (selection.operation.leftWins a b)]) := by
  rcases selection with ⟨operation, x, y⟩
  let selection : Selection := ⟨operation, x, y⟩
  let head := selection.operation.head
  have entered : LiveRegistry.step
      (changeControl base (.evaluate bindings (.expression
        [.symbol head, .var selection.left, .var selection.right]))) =
      some (changeControl base (.arguments bindings (.function head)
        [.var selection.left, .var selection.right] [] 0)) := by
    rw [LiveRegistry.step_eq_indexed]
    cases operation <;> rfl
  have strict (world : Effects.State) (index : Nat) :
      argumentIsRaw (SpaceSemantics.index world.core) head index = false := by
    cases operation <;> rfl
  have computed : LiveRegistry.step
      {base with
        control := .arguments bindings (.function head) [] [intAtom a, intAtom b] 2
        frames := .sequence [] [] :: .sequence [] [] :: base.frames} =
      some {base with
        control := .returned [Effects.boolean (selection.operation.leftWins a b)]
        frames := .sequence [] [] :: .sequence [] [] :: base.frames} := by
    rw [LiveRegistry.step_eq_indexed]
    cases operation <;> rfl
  rw [advance_next 13 _ _ entered, show 13 = 4 + 9 by rfl, ← LiveRegistry.advance_split,
    capture_variable _ _ _ _ _ _ _ (strict _ _)]
  simp only [List.nil_append]
  change applySubst bindings (.var selection.left) = intAtom a at left
  change applySubst bindings (.var selection.right) = intAtom b at right
  rw [left]
  let first : Configuration := {base with frames := .sequence [] [] :: base.frames}
  change LiveRegistry.advance 9
    (changeControl first (.arguments bindings (.function head) [.var selection.right] [intAtom a] 1)) = _
  rw [show 9 = 4 + 5 by rfl, ← LiveRegistry.advance_split,
    capture_variable first bindings head selection.right [] [intAtom a] 1 (strict base.state 1)]
  rw [right]
  exact (advance_next 4 _ _ computed).trans rfl

private theorem body_last (selection : Selection) (a b : Int)
    (base : Configuration) (bindings : Subst)
    (left : applySubst bindings (.var selection.left) = intAtom a)
    (right : applySubst bindings (.var selection.right) = intAtom b) :
    LiveRegistry.advance 19 (changeControl base (.evaluate bindings selection.body)) =
      changeControl base (.sequence [] [intAtom (selection.operation.run a b)]) := by
  let branch : Configuration :=
    {base with frames := .branch bindings (.var selection.left) (.var selection.right) :: base.frames}
  let condition : Atom := .expression
    [.symbol selection.operation.head, .var selection.left, .var selection.right]
  have entered : LiveRegistry.step (changeControl base (.evaluate bindings selection.body)) =
      some (changeControl branch (.evaluate bindings condition)) := by
    rw [LiveRegistry.step_eq_indexed]
    rfl
  rw [advance_next 18 _ _ entered, show 18 = 14 + 4 by rfl, ← LiveRegistry.advance_split,
    leftWins_evaluate selection a b branch bindings left right]
  have branch_returns (chosen : String) (value : Int)
      (bound : applySubst bindings (.var chosen) = intAtom value) :
      LiveRegistry.advance 3 (changeControl base (.sequence [.evaluate bindings (.var chosen)] [])) =
        changeControl base (.sequence [] [intAtom value]) := by
    simp only [LiveRegistry.advance, LiveRegistry.step_eq_indexed, changeControl, Eval.step,
      bound, List.nil_append]
  cases won : selection.operation.leftWins a b with
  | false =>
    have chosen : LiveRegistry.step (changeControl branch (.returned [Effects.boolean false])) =
        some (changeControl base (.sequence [.evaluate bindings (.var selection.right)] [])) := by
      rw [LiveRegistry.step_eq_indexed]
      rfl
    rw [advance_next 3 _ _ chosen, branch_returns _ _ right]
    simp [Operation.run, won]
  | true =>
    have chosen : LiveRegistry.step (changeControl branch (.returned [Effects.boolean true])) =
        some (changeControl base (.sequence [.evaluate bindings (.var selection.left)] [])) := by
      rw [LiveRegistry.step_eq_indexed]
      rfl
    rw [advance_next 3 _ _ chosen, branch_returns _ _ left]
    simp [Operation.run, won]

theorem body_cost (selection : Selection) (a b : Int) (base : Configuration) (bindings : Subst)
    (left : applySubst bindings (.var selection.left) = intAtom a)
    (right : applySubst bindings (.var selection.right) = intAtom b) :
    LiveRegistry.advance 20 (changeControl base (.evaluate bindings selection.body)) =
      changeControl base (.returned [intAtom (selection.operation.run a b)]) := by
  rw [show 20 = 19 + 1 by rfl, ← LiveRegistry.advance_split, body_last _ _ _ _ _ left right,
    LiveRegistry.advance, LiveRegistry.step_eq_indexed]
  rfl

private structure PreparedBody (selected : Control) where
  comparison : Selection
  bindings : Subst
  body : selected = .sequence [.evaluate bindings comparison.body] []
  left : Int
  right : Int
  leftValue : applySubst bindings (.var comparison.left) = intAtom left
  rightValue : applySubst bindings (.var comparison.right) = intAtom right

private def PreparedBody.recognize (selected : Control) : Option (PreparedBody selected) := do
  match control : selected with
  | .sequence [.evaluate bindings body] [] =>
    let query ← Selection.ofBody? body
    match left : applySubst bindings (.var query.val.left),
          right : applySubst bindings (.var query.val.right) with
    | .grounded (.int a), .grounded (.int b) =>
      return ⟨query.val, bindings, by rw [control, query.property], a, b, left, right⟩
    | _, _ => none
  | _ => none

private def PreparedBody.reply {selected : Control} (body : PreparedBody selected) : Control :=
  .returned [intAtom (body.comparison.operation.run body.left body.right)]

structure Entry (source : Configuration) where
  selected : Configuration
  selectionStep : LiveRegistry.step source = some selected
  prepared : PreparedBody selected.control

private def ready (source : Configuration) : Bool :=
  match source.control with
  | .arguments _ (.function head) [] _ _ => !(ioHead head || StdLib.known head)
  | _ => false

/-- Check the selected body at the call site. Multiple selected alternatives
and noninteger or unevaluated bindings retain ordinary evaluation. -/
private def admit (source selected : Configuration)
    (stepped : LiveRegistry.step source = some selected) : Option (Entry source) :=
  if ready source then
    (PreparedBody.recognize selected.control).map (⟨selected, stepped, ·⟩)
  else none

def prepare (source : Configuration) : Option (Entry source) :=
  match stepped : LiveRegistry.step source with
  | some selected => admit source selected stepped
  | none => none

def Entry.finish {source : Configuration} (entry : Entry source) : Configuration :=
  changeControl entry.selected entry.prepared.reply

theorem Entry.region_fires {source : Configuration} (entry : Entry source) :
    (theory entry.prepared.comparison.operation).Step (.pending entry.prepared.left entry.prepared.right)
      (.returned (entry.prepared.comparison.operation.run entry.prepared.left entry.prepared.right)) :=
  (region_exact _ _ _ _).mpr rfl

private theorem Entry.beforeReturn {source : Configuration} (entry : Entry source) :
    LiveRegistry.advance 23 source = changeControl entry.selected
      (.sequence [] [intAtom (entry.prepared.comparison.operation.run
        entry.prepared.left entry.prepared.right)]) := by
  let candidate := entry.prepared
  let control := Control.evaluate candidate.bindings candidate.comparison.body
  let body : Configuration := {entry.selected with frames := .sequence [] [] :: entry.selected.frames}
  have openBody : LiveRegistry.step entry.selected = some (changeControl body control) := by
    simp only [LiveRegistry.step_eq_indexed, Eval.step, candidate.body, control, body, changeControl]
  rw [LiveRegistry.advance, entry.selectionStep]
  change LiveRegistry.advance 22 entry.selected = _
  rw [LiveRegistry.advance, openBody]
  change LiveRegistry.advance 21 (changeControl body control) = _
  rw [show 21 = 20 + 1 by rfl, ← LiveRegistry.advance_split,
    body_cost candidate.comparison candidate.left candidate.right body candidate.bindings
      candidate.leftValue candidate.rightValue,
    LiveRegistry.advance, LiveRegistry.step_eq_indexed]
  rfl

/-- The source needs 24 dispatch transitions from the ready call to its
reply. At 23 transitions it still has the enclosing clause sequence to close. -/
theorem Entry.source_cost {source : Configuration} (entry : Entry source) :
    LiveRegistry.advance 24 source = entry.finish ∧
      (LiveRegistry.advance 23 source).control ≠ entry.finish.control := by
  refine ⟨?_, ?_⟩
  · rw [show 24 = 23 + 1 by rfl, ← LiveRegistry.advance_split, entry.beforeReturn,
      LiveRegistry.advance, LiveRegistry.step_eq_indexed]
    rfl
  · rw [entry.beforeReturn]
    intro early
    exact Control.noConfusion early

/-- Against the established 24-transition reference, price one retained
dispatch, one regional comparison and return, and any extra validation per
batch. The abstract transition count gives a budget for those prices. -/
theorem region_work_less_iff (calls dispatch region validation : Nat) :
    validation + calls * (dispatch + region) < calls * (24 * dispatch) ↔
      validation + calls * region < calls * (23 * dispatch) := by
  rw [Nat.mul_add, show 24 * dispatch = dispatch + 23 * dispatch by omega, Nat.mul_add]
  omega

private theorem advance_path (fuel : Nat) (source : Configuration) :
    LiveRegistry.theory.MultiStep source (LiveRegistry.advance fuel source) := by
  induction fuel generalizing source with
  | zero => exact .refl _
  | succ fuel ih =>
    cases stepped : LiveRegistry.step source with
    | none => simpa [LiveRegistry.advance, stepped] using
        (GSLT.MultiStep.refl (S := LiveRegistry.theory) source)
    | some next =>
      exact .step ((LiveRegistry.step_exact _ _).mp stepped)
        (by simpa [LiveRegistry.advance, stepped] using ih next)

def attempt (source : Configuration) : Option Configuration := (prepare source).map Entry.finish

private theorem reply_of_selection (source selected : Configuration)
    (entered : ready source = true) (stepped : LiveRegistry.step source = some selected) :
    (attempt source).map Configuration.control =
      (PreparedBody.recognize selected.control).map PreparedBody.reply := by
  unfold attempt prepare
  split
  · rename_i other same
    have equal := Option.some.inj (stepped.symm.trans same)
    subst other
    simp only [admit, entered, ↓reduceIte, Option.map_map, Function.comp_def, Entry.finish, changeControl]
  · simp_all

/-- At a ready call, the ordered alternatives for its head are the only
authored dependency. Argument demand has already been settled. In
particular, adding an import with the same supported view need not change
region admission or its reply. -/
theorem ready_reply_agrees (first second : Configuration) (head : String) (values : List Atom)
    (bindings : Subst) (index : Nat) (ordinary : ioHead head = false)
    (authored : StdLib.known head = false)
    (same : application (SpaceSemantics.index first.state.core) head values =
      application (SpaceSemantics.index second.state.core) head values) :
    (attempt (changeControl first (.arguments bindings (.function head) [] values index))).map
        Configuration.control =
      (attempt (changeControl second (.arguments bindings (.function head) [] values index))).map
        Configuration.control := by
  let entry := Control.arguments bindings (.function head) [] values index
  let selected (world : Configuration) :=
    application (SpaceSemantics.index world.state.core) head values
  have entered (world : Configuration) : ready (changeControl world entry) = true := by
    simp [ready, changeControl, entry, ordinary, authored]
  have stepped (world : Configuration) :
      LiveRegistry.step (changeControl world entry) = some (changeControl world (selected world)) := by
    simp only [LiveRegistry.step_eq_indexed, changeControl, Eval.step, entry, ordinary,
      authored, Bool.false_eq_true, ↓reduceIte, selected]
  rw [reply_of_selection _ _ (entered first) (stepped first),
    reply_of_selection _ _ (entered second) (stepped second)]
  change selected first = selected second at same
  change (PreparedBody.recognize (selected first)).map PreparedBody.reply =
    (PreparedBody.recognize (selected second)).map PreparedBody.reply
  rw [same]

theorem attempt_sound (source target : Configuration) (executed : attempt source = some target) :
    LiveRegistry.theory.MultiStep source target := by
  obtain ⟨entry, _, rfl⟩ := Option.map_eq_some_iff.mp executed
  rw [← entry.source_cost.1]
  exact advance_path _ _

/-- Fall back to the ordinary step already taken when recognition fails. -/
def acceleratedStep (source : Configuration) : Option Configuration :=
  match stepped : LiveRegistry.step source with
  | none => none
  | some selected =>
    some (((admit source selected stepped).map Entry.finish).getD selected)

theorem acceleratedStep_agrees (source : Configuration) :
    acceleratedStep source = (attempt source).orElse (fun _ => LiveRegistry.step source) := by
  unfold acceleratedStep attempt prepare
  split
  · rename_i stopped
    split <;> simp_all
  · rename_i selected stepped
    split
    · rename_i other same
      have equal := Option.some.inj (stepped.symm.trans same)
      subst other
      cases admit source selected stepped <;> simp [stepped]
    · simp_all

theorem acceleratedStep_sound (source target : Configuration)
    (executed : acceleratedStep source = some target) :
    LiveRegistry.theory.MultiStep source target := by
  rw [acceleratedStep_agrees] at executed
  cases admitted : attempt source with
  | none =>
    have stepped : LiveRegistry.step source = some target := by simpa [admitted] using executed
    exact .step ((LiveRegistry.step_exact _ _).mp stepped) (.refl _)
  | some next =>
    have same : next = target := by simpa [admitted] using executed
    exact same ▸ attempt_sound _ _ admitted

def advance : Nat → Configuration → Configuration
  | 0, source => source
  | fuel + 1, source =>
    match acceleratedStep source with
    | some next => advance fuel next
    | none => source

theorem advance_sound (fuel : Nat) (source : Configuration) :
    LiveRegistry.theory.MultiStep source (advance fuel source) := by
  induction fuel generalizing source with
  | zero => exact .refl _
  | succ fuel ih =>
    cases stepped : acceleratedStep source with
    | none => simpa [advance, stepped] using (GSLT.MultiStep.refl (S := LiveRegistry.theory) source)
    | some next =>
      have initial := acceleratedStep_sound _ _ stepped
      have compose {first mid last : LiveRegistry.theory.Term} :
          LiveRegistry.theory.MultiStep first mid → LiveRegistry.theory.MultiStep mid last →
          LiveRegistry.theory.MultiStep first last := by
        intro path suffix
        induction path with
        | refl => exact suffix
        | step firing _ append => exact .step firing (append suffix)
      simpa [advance, stepped] using compose initial (ih next)

/-- The returned control of a saturated native remainder instruction is
independent of the authored registry and the stored rows. -/
theorem ready_remainder (base : Configuration) (bindings : Subst) (a b : Int) (index : Nat) :
    LiveRegistry.step (changeControl base (.arguments bindings (.function "%") []
        [intAtom a, intAtom b] index)) =
      some (changeControl base (if b = 0 then .fault .zeroDivisor
        else .returned [intAtom (a.fmod b)])) := by
  rw [LiveRegistry.step_eq_indexed]
  change (match ((if b = 0 then .error .zeroDivisor
      else .ok (base.state, [intAtom (a.fmod b)])) : Except Effects.Fault (Effects.State × List Atom)) with
    | .ok (state, answers) => some {base with state, control := .returned answers}
    | .error fault => some (changeControl base (.fault fault))) = _
  by_cases zero : b = 0
  · simp only [if_pos zero]
  · simp only [if_neg zero, changeControl]

#print axioms Operation.run_swap
#print axioms region_exact
#print axioms body_cost
#print axioms Entry.source_cost
#print axioms region_work_less_iff
#print axioms ready_reply_agrees
#print axioms attempt_sound
#print axioms acceleratedStep_agrees
#print axioms advance_sound
#print axioms ready_remainder

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.LiveMathRegion
