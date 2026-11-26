import Mettapedia.GSLT.Compilation.Uniform.StateRulesOnTheStep

/-!
# Read-only scheduling and continuation consumption on Transform

A task may ask for scheduling from its own data, or ask at the present
context when the plan depends on that view. A return asks only about
the nearest frame and the returned data. All three rules retain the
world, context, outer continuation, and publication history structurally.
A world operation uses the same forms but supplies a new world explicitly.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.Uniform.PureContinuationRules

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax.Presentation.Schematic (Tm inst)
open RuleSyntax.Machines (unknowns)
open RuleSyntax.ComputedConditions (Condition Relations RelationStep RuleWithCondition)
open Mettapedia.GSLT.Compilation.RootRewritesOnTheStep (appTerm symTerm inst_appTerm)
open StateRulesOnTheStep (fields packet pattern packet_eq_iff instantiate_packet instantiate_fields instance_var)

inductive Mode where
  | work (tag : Nat)
  | schedule (tag : Nat)
  | consume

inductive Input where
  | work (tag : Nat)
  | schedule (tag : Nat)
  | returned (frame : Expr)

def Input.mode : Input → Mode
  | .work tag => .work tag
  | .schedule tag => .schedule tag
  | .returned _ => .consume

def Mode.tag : Mode → Nat
  | .work tag | .schedule tag => tag
  | .consume => 2

inductive Width where
  | direct
  | one
  | two

def Width.slots : Width → List Nat
  | .direct => []
  | .one => [8]
  | .two => [8, 9]

theorem width_of_length {A : Type} {xs : List A} (bound : xs.length ≤ 1) :
    ∃ width : Width, xs.length = width.slots.length := by
  cases xs with
  | nil => exact ⟨.direct, rfl⟩
  | cons first tail =>
    cases tail with
    | nil => exact ⟨.one, rfl⟩
    | cons second rest => simp at bound

theorem width_of_length_le_two {A : Type} {xs : List A} (bound : xs.length ≤ 2) :
    ∃ width : Width, xs.length = width.slots.length := by
  cases xs with
  | nil => exact ⟨.direct, rfl⟩
  | cons first tail =>
    cases tail with
    | nil => exact ⟨.one, rfl⟩
    | cons second rest =>
      cases rest with
      | nil => exact ⟨.two, rfl⟩
      | cons third rest => simp at bound

structure Ambient where
  world : Expr
  scope : Expr
  stack : Expr
  parents : Expr
  history : Expr
  value : Expr

def Input.message (input : Input) (a : Ambient) : Expr :=
  let seenStack := match input with
    | .work _ | .schedule _ => a.stack
    | .returned frame => Expr.app frame a.stack
  packet input.mode.tag [a.world, a.scope, seenStack, a.parents, a.history, a.value]

def Input.arguments (input : Input) (a : Ambient) : List Expr :=
  match input with
  | .work _ => [a.world, a.scope, a.value]
  | .schedule _ => [a.value]
  | .returned frame => [frame, a.value]

def outcome (a : Ambient) (tag tail : Expr) (front : List Expr) : Expr :=
  .app tag ([a.world, a.scope, front.foldr Expr.app a.stack, a.parents, a.history].foldr Expr.app tail)

private def vars (xs : List Nat) : List Tm := xs.map .var

private def input (mode : Mode) : Tm :=
  pattern mode.tag [.var 0, .var 1, (match mode with
    | .work _ | .schedule _ => .var 2
    | .consume => appTerm (.var 10) (.var 2)), .var 3, .var 4, .var 5]

private def output (width : Width) (worldSlot : Nat := 0) : Tm :=
  appTerm (.var 6)
    (([.var worldSlot, .var 1, (vars width.slots).foldr appTerm (.var 2), .var 3, .var 4] : List Tm).foldr appTerm (.var 7))

private def ask (mode : Mode) (port : Nat) (width : Width) (worldSlots : List Nat := []) : Condition Nat Tm :=
  { name := port,
    arguments := vars (match mode with | .work _ => [0, 1, 5] | .schedule _ => [5] | .consume => [10, 5]),
    value := (vars (worldSlots ++ 6 :: 7 :: width.slots)).foldr appTerm (symTerm 0) }

def rule (mode : Mode) (port : Nat) (width : Width) : RuleWithCondition Nat Tm :=
  StateRulesOnTheStep.rule (input mode) (output width) [ask mode port width]

def worldRule (mode : Mode) (port : Nat) (width : Width) : RuleWithCondition Nat Tm :=
  StateRulesOnTheStep.rule (input mode) (output width 11) [ask mode port width [11]]

theorem asks_port (mode : Mode) (port : Nat) (width : Width) (c : Condition Nat Tm)
    (within : c ∈ (rule mode port width).conditions) : c.name = port := by
  obtain rfl : c = ask mode port width := List.mem_singleton.mp within
  rfl

theorem world_asks_port (mode : Mode) (port : Nat) (width : Width) (c : Condition Nat Tm)
    (within : c ∈ (worldRule mode port width).conditions) : c.name = port := by
  obtain rfl : c = ask mode port width [11] := List.mem_singleton.mp within
  rfl

theorem input_tag {rel : Relations} {mode : Mode} {port : Nat} {width : Width}
    {tag : Nat} {items : List Expr} {after : Multiset Expr}
    (step : RelationStep rel (rule mode port width) {packet tag items} after) : mode.tag = tag :=
  StateRulesOnTheStep.input_tag step

theorem world_input_tag {rel : Relations} {mode : Mode} {port : Nat} {width : Width}
    {tag : Nat} {items : List Expr} {after : Multiset Expr}
    (step : RelationStep rel (worldRule mode port width) {packet tag items} after) : mode.tag = tag :=
  StateRulesOnTheStep.input_tag step

theorem no_consume_empty (rel : Relations) (port : Nat) (width : Width)
    (world scope parents history value : Expr) (after : Multiset Expr) :
    ¬ RelationStep rel (rule .consume port width) {packet 2 [world, scope, .sym 0, parents, history, value]} after := by
  rw [rule, StateRulesOnTheStep.instance_iff]
  rintro ⟨_, matches', _, _⟩
  simp [input, Mode.tag, instantiate_packet, instance_var, packet_eq_iff] at matches'

theorem rule_restricted (mode : Mode) (port : Nat) (width : Width) :
    (rule mode port width).RangeRestrictedWith := by
  apply StateRulesOnTheStep.restricted
  intro x present
  let written := unknowns (output width)
  let bound := unknowns (input mode) ++ unknowns (ask mode port width).value
  have proved : written.all bound.contains = true := by cases mode <;> cases width <;> rfl
  have occurs : x ∈ bound := List.contains_iff_mem.mp ((List.all_eq_true.mp proved) x present)
  rcases List.mem_append.mp occurs with found | furnished
  · exact Or.inl found
  · exact Or.inr ⟨ask mode port width, List.mem_cons_self, furnished⟩

theorem world_rule_restricted (mode : Mode) (port : Nat) (width : Width) :
    (worldRule mode port width).RangeRestrictedWith := by
  apply StateRulesOnTheStep.restricted
  intro x present
  let written := unknowns (output width 11)
  let bound := unknowns (input mode) ++ unknowns (ask mode port width [11]).value
  have proved : written.all bound.contains = true := by cases mode <;> cases width <;> rfl
  have occurs : x ∈ bound := List.contains_iff_mem.mp ((List.all_eq_true.mp proved) x present)
  rcases List.mem_append.mp occurs with found | furnished
  · exact Or.inl found
  · exact Or.inr ⟨ask mode port width [11], List.mem_cons_self, furnished⟩

private theorem inst_vars (v : Nat → Expr) (slots : List Nat) :
    (vars slots).map (inst v) = slots.map v := by
  induction slots with
  | nil => rfl
  | cons a b ih =>
    simp only [vars, List.map_cons, instance_var] at ih ⊢
    rw [ih]

private theorem inst_stack (v : Nat → Expr) (slots : List Nat) :
    inst v ((vars slots).foldr appTerm (.var 2)) = (slots.map v).foldr Expr.app (v 2) := by
  induction slots with
  | nil => rfl
  | cons a b ih =>
    simp only [vars, List.map_cons, List.foldr_cons, inst_appTerm, instance_var] at ih ⊢
    rw [ih]

private theorem inputs_exact (source : Input) (a : Ambient) (v : Nat → Expr)
    (matched : inst v (input source.mode) = source.message a) :
    v 0 = a.world ∧ v 1 = a.scope ∧ v 2 = a.stack ∧ v 3 = a.parents ∧ v 4 = a.history ∧ v 5 = a.value ∧
      (∀ frame, source = .returned frame → v 10 = frame) := by
  cases source with
  | work tag | schedule tag =>
    simp only [input, Input.mode, Input.message, Mode.tag, instantiate_packet, instance_var,
      List.map_cons, List.map_nil, packet_eq_iff, true_and, List.cons.injEq, and_true] at matched
    obtain ⟨w, s, k, p, h, x⟩ := matched
    exact ⟨w, s, k, p, h, x, fun _ bad => by cases bad⟩
  | returned frame =>
    simp only [input, Input.mode, Input.message, Mode.tag, instantiate_packet, instance_var, inst_appTerm,
      List.map_cons, List.map_nil, packet_eq_iff, true_and, List.cons.injEq, and_true, Expr.app.injEq] at matched
    obtain ⟨w, s, ⟨f, k⟩, p, h, x⟩ := matched
    exact ⟨w, s, k, p, h, x, fun _ same => (Input.returned.inj same) ▸ f⟩

private def assigned (source : Input) (a : Ambient) (tag tail nextWorld : Expr) (front : List Expr)
    (n : Nat) : Expr :=
  if n = 10 then (match source with | .returned frame => frame | .work _ | .schedule _ => .sym 0)
  else if n = 11 then nextWorld
  else ([a.world, a.scope, a.stack, a.parents, a.history, a.value, tag, tail] ++ front)[n]?.getD (.sym 0)

private theorem assigned_frames (source : Input) (a : Ambient) (tag tail nextWorld : Expr) (front : List Expr)
    (width : Width) (size : front.length = width.slots.length) :
    width.slots.map (assigned source a tag tail nextWorld front) = front := by
  cases width with
  | direct =>
    obtain rfl := List.length_eq_zero_iff.mp (show front.length = 0 from size)
    rfl
  | one =>
    cases front with
    | nil => cases size
    | cons first rest =>
      obtain rfl := List.length_eq_zero_iff.mp (Nat.succ.inj size)
      rfl
  | two =>
    cases front with
    | nil => cases size
    | cons first rest =>
      cases rest with
      | nil => cases size
      | cons second rest =>
        obtain rfl := List.length_eq_zero_iff.mp (Nat.succ.inj (Nat.succ.inj size))
        rfl

theorem step_exact (rel : Relations) (source : Input) (port : Nat) (width : Width) (a : Ambient)
    (after : Multiset Expr) :
    RelationStep rel (rule source.mode port width) {source.message a} after ↔
      ∃ tag tail front, front.length = width.slots.length ∧
        rel port (source.arguments a) (fields (tag :: tail :: front)) ∧
        after = {outcome a tag tail front} := by
  rw [rule, StateRulesOnTheStep.instance_iff]
  constructor
  · rintro ⟨v, matched, asked, made⟩
    obtain ⟨w, s, k, p, h, x, f⟩ := inputs_exact source a v matched
    have read := asked (ask source.mode port width) List.mem_cons_self
    have invoked : rel port (source.arguments a) (fields (v 6 :: v 7 :: width.slots.map v)) := by
      cases source with
      | work tag =>
        simpa only [ask, Input.mode, instantiate_fields, inst_vars, Input.arguments, List.nil_append, List.map_cons, List.map_nil,
          w, s, x] using read
      | schedule tag =>
        simpa only [ask, Input.mode, instantiate_fields, inst_vars, Input.arguments, List.nil_append, List.map_cons, List.map_nil,
          x] using read
      | returned frame =>
        simpa only [ask, Input.mode, instantiate_fields, inst_vars, Input.arguments, List.nil_append, List.map_cons, List.map_nil,
          x, f frame rfl] using read
    refine ⟨v 6, v 7, width.slots.map v, List.length_map _, invoked, ?_⟩
    simpa only [output, inst_appTerm, instance_var, List.foldr_cons, List.foldr_nil, inst_stack, w, s, k, p, h, outcome]
      using made
  · rintro ⟨tag, tail, front, size, positive, rfl⟩
    let v := assigned source a tag tail a.world front
    have encoded : width.slots.map v = front := assigned_frames source a tag tail a.world front width size
    refine ⟨v, ?_, ?_, ?_⟩
    · cases source <;> rfl
    · intro condition member
      obtain rfl : condition = ask source.mode port width := List.mem_singleton.mp member
      simp only [ask, instantiate_fields, inst_vars, List.nil_append, List.map_cons, encoded]
      cases source <;> exact positive
    · simp only [output, outcome, inst_appTerm, instance_var, List.foldr_cons, List.foldr_nil, inst_stack, encoded]
      rfl

/-- The old world is available only through the selected input arguments.
The replacement world comes from the same evidence as the next task;
the scope, enclosing continuations and history still come from the input. -/
theorem world_step_exact (rel : Relations) (source : Input) (port : Nat) (width : Width) (a : Ambient)
    (after : Multiset Expr) :
    RelationStep rel (worldRule source.mode port width) {source.message a} after ↔
      ∃ nextWorld tag tail front, front.length = width.slots.length ∧
        rel port (source.arguments a) (fields (nextWorld :: tag :: tail :: front)) ∧
        after = {outcome { a with world := nextWorld } tag tail front} := by
  rw [worldRule, StateRulesOnTheStep.instance_iff]
  constructor
  · rintro ⟨v, matched, asked, made⟩
    obtain ⟨w, s, k, p, h, x, f⟩ := inputs_exact source a v matched
    have read := asked (ask source.mode port width [11]) List.mem_cons_self
    have invoked : rel port (source.arguments a) (fields (v 11 :: v 6 :: v 7 :: width.slots.map v)) := by
      cases source with
      | work tag =>
        simpa only [ask, Input.mode, instantiate_fields, inst_vars, Input.arguments, List.singleton_append,
          List.map_cons, List.map_nil, w, s, x] using read
      | schedule tag =>
        simpa only [ask, Input.mode, instantiate_fields, inst_vars, Input.arguments, List.singleton_append,
          List.map_cons, List.map_nil, x] using read
      | returned frame =>
        simpa only [ask, Input.mode, instantiate_fields, inst_vars, Input.arguments, List.singleton_append,
          List.map_cons, List.map_nil, x, f frame rfl] using read
    refine ⟨v 11, v 6, v 7, width.slots.map v, List.length_map _, invoked, ?_⟩
    simpa only [output, inst_appTerm, instance_var, List.foldr_cons, List.foldr_nil, inst_stack, s, k, p, h, outcome]
      using made
  · rintro ⟨nextWorld, tag, tail, front, size, positive, rfl⟩
    let v := assigned source a tag tail nextWorld front
    have encoded : width.slots.map v = front := assigned_frames source a tag tail nextWorld front width size
    refine ⟨v, ?_, ?_, ?_⟩
    · cases source <;> rfl
    · intro condition member
      obtain rfl : condition = ask source.mode port width [11] := List.mem_singleton.mp member
      simp only [ask, instantiate_fields, inst_vars, List.singleton_append, List.map_cons, encoded]
      cases source <;> exact positive
    · simp only [output, outcome, inst_appTerm, instance_var, List.foldr_cons, List.foldr_nil, inst_stack, encoded]
      rfl

end Mettapedia.GSLT.Compilation.Uniform.PureContinuationRules
