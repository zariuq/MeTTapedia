import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRProgramCodec

/-! The module-value transport retains every CHR IR constructor, including
nested tuples, signed integers, rule order and repeated declarations/goals.
This is an IR transport roundtrip, not a Prolog-source printing theorem. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRProgramCodec

open Mettapedia.Languages

@[simp] theorem natural_roundtrip (index : Nat) : natural? (.integer index) = some index := by
  have nonnegative : ¬ (index : Int) < 0 := by omega
  simp [natural?, nonnegative]

private theorem map_roundtrip {α β : Type} (encode : α → β) (decode : β → Option α)
    (inputs : List α) (each : ∀ input ∈ inputs, decode (encode input) = some input) :
    (inputs.map encode).mapM decode = some inputs := by
  induction inputs with
  | nil => rfl
  | cons first rest ih =>
      have head := each first List.mem_cons_self
      have tail := ih (fun input member => each input (List.mem_cons_of_mem first member))
      simp [List.mapM_cons, head, tail]

theorem value_roundtrip (source : CHR.Value) : value? (value source) = some source := by
  cases source with
  | integer number => simp only [value, node, value?, integer?]; rfl
  | atom text => simp only [value, node, value?]
  | tuple fields =>
      simp only [value, node, value?]
      rw [map_roundtrip value value? fields (fun field _ => value_roundtrip field)]
      rfl
termination_by sizeOf source

theorem term_roundtrip (source : CHR.Term) : term? (term source) = some source := by
  cases source with
  | value datum => simp only [term, term?, node, value_roundtrip]; rfl
  | var index => simp [term, term?, node]
  | tuple fields =>
      simp only [term, node, term?]
      rw [map_roundtrip term term? fields (fun field _ => term_roundtrip field)]
      rfl
termination_by sizeOf source

theorem head_roundtrip (source : CHR.Head) : head? (head source) = some source := by
  have fields := map_roundtrip term term? source.arguments (fun field _ => term_roundtrip field)
  change ((source.arguments.map term).mapM term?).bind
    (fun arguments => some (CHR.Head.mk source.name arguments)) = some source
  rw [fields]
  rfl

theorem operation_roundtrip (operator : CHR.IntOperator) : operation? (operation operator) = some operator := by
  cases operator <;> rfl

theorem expression_roundtrip (source : CHR.IntExpr) : expression? (expression source) = some source := by
  cases source with
  | literal number => rfl
  | index index => simp [expression, expression?, node]
  | operation operator left right =>
      have first := expression_roundtrip left
      have second := expression_roundtrip right
      cases operator <;> simp [expression, expression?, operation, operation?, node, first, second]
termination_by sizeOf source

theorem comparison_roundtrip (source : CHR.Comparison) : comparison? (comparison source) = some source := by
  cases source <;> rfl

theorem guard_roundtrip (source : CHR.Guard) : guard? (guard source) = some source := by
  cases source <;> simp [guard, guard?, node, node?, term_roundtrip, expression_roundtrip, comparison_roundtrip]

theorem goal_roundtrip (source : CHR.Goal) : goal? (goal source) = some source := by
  cases source <;> simp [goal, goal?, node, node?, head_roundtrip, expression_roundtrip]

theorem rule_roundtrip (source : CHR.Rule) : rule? (rule source) = some source := by
  have kept := map_roundtrip head head? source.kept (fun field _ => head_roundtrip field)
  have removed := map_roundtrip head head? source.removed (fun field _ => head_roundtrip field)
  have guards := map_roundtrip guard guard? source.guards (fun field _ => guard_roundtrip field)
  have goals := map_roundtrip goal goal? source.body (fun field _ => goal_roundtrip field)
  cases source
  simp only [rule, rule?, node, node?, values?, kept, removed, guards, goals, bind, pure,
    Option.bind_some]

theorem declaration_roundtrip (source : CHR.Declaration) : declaration? (declaration source) = some source := by
  cases source
  simp [declaration, declaration?, node, node?]

theorem program_roundtrip (source : CHR.Program) : program? (program source) = some source := by
  have declarations := map_roundtrip declaration declaration? source.declarations (fun field _ => declaration_roundtrip field)
  have rules := map_roundtrip rule rule? source.rules (fun field _ => rule_roundtrip field)
  cases source
  simp only [program, program?, node, node?, values?, declarations, rules, bind, pure,
    Option.bind_some]

theorem program_injective : Function.Injective program := by
  intro first second same
  have recovered := congrArg program? same
  simpa only [program_roundtrip, Option.some.injEq] using recovered

theorem wire_roundtrip (source : CHR.Program) :
    (Value.Wire.decode? (Value.Wire.encode (program source))).bind program? = some source := by
  rw [Value.Wire.decode_encode]
  exact program_roundtrip source

example : declaration? (node "ChrDeclare" [.string "p",.integer (-1)]) = none := by decide
example : value? (node "ChrInt" [.string "7"]) = none := by simp [value?, node, integer?]

#print axioms value_roundtrip
#print axioms term_roundtrip
#print axioms program_roundtrip
#print axioms program_injective
#print axioms wire_roundtrip

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRProgramCodec
