import Mettapedia.Languages.MeTTa.PeTTa.LambdaLifting
import Mettapedia.Languages.MeTTa.PeTTa.ConstructorDataHeads

/-!
# Reservation and recursive preparation of ordinary private lambdas

The outer name is reserved before its body is visited. Nested clauses can
therefore be installed first without reusing the outer name or rewinding the
ordinal supply. Quotation and held arguments do not visit their payloads.

Data-head decisions are retained through quotation or native list construction.
This remains a preparation phase: full escaping-error/prefix reflection, eta
expansion, computed static heads, overloaded typed alternatives, translator
hooks and functional-pattern staging still need their separate connections.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.LambdaStaging

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open LambdaLifting (Table Lifted)
open SpaceSemantics (Program)

structure Reservation where
  table : Table
  ordinal : Nat
  arguments : List Atom
  captured : List String

def reserve (table : Table) (registry : Program) (foreign : Finset String)
    (arguments : List Atom) (body : Atom) : Reservation :=
  let ordinal := Mettapedia.FirstFreshName.choose LambdaLifting.name
    LambdaLifting.name_injective (LambdaLifting.occupied table registry foreign) (table.cursor + 1)
  ⟨{table with
      cursor := ordinal
      occupied := insert (LambdaLifting.name ordinal) (LambdaLifting.occupied table registry foreign)},
    ordinal,arguments,LambdaLifting.captures arguments body⟩

def finish (reserved : Reservation) (afterBody : Table) (body : Atom) : Lifted :=
  let installed := LambdaLifting.equation (LambdaLifting.name reserved.ordinal)
    reserved.arguments body reserved.captured
  ⟨{afterBody with code := afterBody.code ++ [installed]},reserved.ordinal,
    reserved.captured,installed,LambdaLifting.value (LambdaLifting.name reserved.ordinal) reserved.captured⟩

theorem reserve_keeps_code (table : Table) (registry : Program) (foreign : Finset String)
    (arguments : List Atom) (body : Atom) :
    (reserve table registry foreign arguments body).table.code = table.code := rfl

theorem reserve_advances (table : Table) (registry : Program) (foreign : Finset String)
    (arguments : List Atom) (body : Atom) :
    table.cursor < (reserve table registry foreign arguments body).table.cursor := by
  have lower := (Mettapedia.FirstFreshName.choose_spec LambdaLifting.name
    LambdaLifting.name_injective (LambdaLifting.occupied table registry foreign) (table.cursor + 1)).1
  exact lower

theorem reserve_is_fresh (table : Table) (registry : Program) (foreign : Finset String)
    (arguments : List Atom) (body : Atom) :
    LambdaLifting.name (reserve table registry foreign arguments body).ordinal ∉
      LambdaLifting.occupied table registry foreign :=
  (Mettapedia.FirstFreshName.choose_spec LambdaLifting.name LambdaLifting.name_injective
    (LambdaLifting.occupied table registry foreign) (table.cursor + 1)).2

theorem finish_keeps_later_supply (reserved : Reservation) (afterBody : Table) (body : Atom) :
    (finish reserved afterBody body).table.cursor = afterBody.cursor ∧
      (finish reserved afterBody body).table.occupied = afterBody.occupied := ⟨rfl,rfl⟩

theorem finish_without_nested_compilation (table : Table) (registry : Program) (foreign : Finset String)
    (arguments : List Atom) (originalBody compiledBody : Atom) :
    let reserved := reserve table registry foreign arguments originalBody
    finish reserved reserved.table compiledBody =
      LambdaLifting.lift table registry foreign arguments originalBody compiledBody := rfl

/-- Independent first-name and capture rules for the reservation boundary. -/
inductive ReservationRel (table : Table) (registry : Program) (foreign : Finset String)
    (arguments : List Atom) (body : Atom) : Reservation → Prop where
  | chosen {ordinal captured} :
      table.cursor + 1 ≤ ordinal →
      LambdaLifting.name ordinal ∉ LambdaLifting.occupied table registry foreign →
      (∀ earlier, table.cursor + 1 ≤ earlier → earlier < ordinal →
        LambdaLifting.name earlier ∈ LambdaLifting.occupied table registry foreign) →
      LambdaLifting.CaptureScan
        (Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars (.expression arguments)) []
        (Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars body) captured →
      ReservationRel table registry foreign arguments body
        ⟨{table with
            cursor := ordinal
            occupied := insert (LambdaLifting.name ordinal) (LambdaLifting.occupied table registry foreign)},
          ordinal,arguments,captured⟩

theorem reservation_source (table : Table) (registry : Program) (foreign : Finset String)
    (arguments : List Atom) (body : Atom) :
    ReservationRel table registry foreign arguments body (reserve table registry foreign arguments body) := by
  have chosen := Mettapedia.FirstFreshName.choose_spec LambdaLifting.name
    LambdaLifting.name_injective (LambdaLifting.occupied table registry foreign) (table.cursor + 1)
  exact .chosen chosen.1 chosen.2
    (Mettapedia.FirstFreshName.choose_minimal LambdaLifting.name LambdaLifting.name_injective
      (LambdaLifting.occupied table registry foreign) (table.cursor + 1))
    (LambdaLifting.captureScan_of_computed _ _ _)

theorem reservation_iff (table : Table) (registry : Program) (foreign : Finset String)
    (arguments : List Atom) (body : Atom) (reserved : Reservation) :
    ReservationRel table registry foreign arguments body reserved ↔
      reserve table registry foreign arguments body = reserved := by
  constructor
  · intro source
    cases source with
    | chosen lower fresh earlier captured =>
        have ordinal := (Mettapedia.FirstFreshName.choose_eq_iff LambdaLifting.name
          LambdaLifting.name_injective (LambdaLifting.occupied table registry foreign)
          (table.cursor + 1) _).mpr ⟨lower,fresh,earlier⟩
        have captures := LambdaLifting.captureScan_computes captured
        simp only [reserve,ordinal,LambdaLifting.captures,captures]
  · rintro rfl
    exact reservation_source table registry foreign arguments body

structure Result where
  table : Table
  expression : Atom

structure Arguments where
  table : Table
  values : List Atom

/-- The written match template is translated after selection, unlike its
native runtime-dispatch template value. The pattern itself stays held. -/
def heldArgument (registry : Program) (head : Atom) (index : Nat) : Bool :=
  match head with
  | .symbol "match" => index == 1
  | .symbol name =>
      Eval.argumentIsRaw registry name index &&
        (Eval.ioHead name || StdLib.known name || registry.equations.any (·.head == name))
  | _ => false

def visitArguments (visit : Table → Atom → Option Result) (held : Nat → Bool) :
    Table → Nat → List Atom → Option Arguments
  | table, _, [] => some ⟨table,[]⟩
  | table, index, first :: rest => do
      let entry ← if held index then some ⟨table,first⟩ else visit table first
      let tail ← visitArguments visit held entry.table (index + 1) rest
      pure ⟨tail.table,entry.expression :: tail.values⟩

inductive ArgumentsRel (child : Table → Atom → Result → Prop) (held : Nat → Bool) :
    Table → Nat → List Atom → Arguments → Prop where
  | nil {table index} : ArgumentsRel child held table index [] ⟨table,[]⟩
  | held {table index first rest tail} :
      held index = true → ArgumentsRel child held table (index + 1) rest tail →
      ArgumentsRel child held table index (first :: rest) ⟨tail.table,first :: tail.values⟩
  | translated {table index first rest entry tail} :
      held index = false → child table first entry →
      ArgumentsRel child held entry.table (index + 1) rest tail →
      ArgumentsRel child held table index (first :: rest) ⟨tail.table,entry.expression :: tail.values⟩

theorem visitArguments_sound (visit : Table → Atom → Option Result)
    (child : Table → Atom → Result → Prop)
    (sound : ∀ table input result, visit table input = some result → child table input result)
    (held : Nat → Bool) (table : Table) (index : Nat) (input : List Atom) (result : Arguments)
    (computed : visitArguments visit held table index input = some result) :
    ArgumentsRel child held table index input result := by
  induction input generalizing table index result with
  | nil =>
      simp only [visitArguments,Option.some.injEq] at computed
      subst result
      exact .nil
  | cons first rest ih =>
      cases demand : held index
      · simp only [visitArguments,demand,Bool.false_eq_true,↓reduceIte,bind,pure,
          Option.bind_eq_some_iff,Option.some.injEq] at computed
        obtain ⟨entry,entryComputed,tail,tailComputed,rfl⟩ := computed
        exact .translated demand (sound _ _ _ entryComputed) (ih _ _ _ tailComputed)
      · simp only [visitArguments,demand,↓reduceIte,bind,pure,Option.bind_some,
          Option.bind_eq_some_iff,Option.some.injEq] at computed
        obtain ⟨tail,tailComputed,rfl⟩ := computed
        exact .held demand (ih _ _ _ tailComputed)

theorem visitArguments_complete (visit : Table → Atom → Option Result)
    (child : Table → Atom → Result → Prop)
    (complete : ∀ table input result, child table input result → visit table input = some result)
    {held : Nat → Bool} {table : Table} {index : Nat} {input : List Atom} {result : Arguments}
    (source : ArgumentsRel child held table index input result) :
    visitArguments visit held table index input = some result := by
  induction source with
  | nil => rfl
  | held demand _ ih => simp only [visitArguments,demand,↓reduceIte,bind,pure,Option.bind_some,ih]
  | translated demand edge _ ih =>
      simp only [visitArguments,demand,Bool.false_eq_true,↓reduceIte,bind,pure,complete _ _ _ edge,
        Option.bind_some,ih]

def rowParts : Atom → Option (Atom × Atom)
  | .expression [pattern,body] => some (pattern,body)
  | _ => none

def visitRows (visit : Table → Atom → Option Result) : Table → List Atom → Option Arguments
  | table, [] => some ⟨table,[]⟩
  | table, first :: rest =>
      match rowParts first with
      | none => do
          let tail ← visitRows visit table rest
          pure ⟨tail.table,first :: tail.values⟩
      | some (pattern,body) => do
          let compiled ← visit table body
          let tail ← visitRows visit compiled.table rest
          pure ⟨tail.table,.expression [pattern,compiled.expression] :: tail.values⟩

inductive RowsRel (child : Table → Atom → Result → Prop) : Table → List Atom → Arguments → Prop where
  | nil {table} : RowsRel child table [] ⟨table,[]⟩
  | raw {table first rest tail} : rowParts first = none → RowsRel child table rest tail →
      RowsRel child table (first :: rest) ⟨tail.table,first :: tail.values⟩
  | pair {table first rest pattern body compiled tail} : rowParts first = some (pattern,body) →
      child table body compiled → RowsRel child compiled.table rest tail →
      RowsRel child table (first :: rest) ⟨tail.table,.expression [pattern,compiled.expression] :: tail.values⟩

theorem visitRows_sound (visit : Table → Atom → Option Result) (child : Table → Atom → Result → Prop)
    (sound : ∀ table input result, visit table input = some result → child table input result)
    (table : Table) (input : List Atom) (result : Arguments)
    (computed : visitRows visit table input = some result) : RowsRel child table input result := by
  induction input generalizing table result with
  | nil =>
      simp only [visitRows,Option.some.injEq] at computed
      subst result
      exact .nil
  | cons first rest ih =>
      cases parts : rowParts first with
      | none =>
          simp only [visitRows,parts,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
          obtain ⟨tail,tailComputed,rfl⟩ := computed
          exact .raw parts (ih _ _ tailComputed)
      | some pair =>
          rcases pair with ⟨pattern,body⟩
          simp only [visitRows,parts,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
          obtain ⟨compiled,bodyComputed,tail,tailComputed,rfl⟩ := computed
          exact .pair parts (sound _ _ _ bodyComputed) (ih _ _ tailComputed)

theorem visitRows_complete (visit : Table → Atom → Option Result) (child : Table → Atom → Result → Prop)
    (complete : ∀ table input result, child table input result → visit table input = some result)
    {table : Table} {input : List Atom} {result : Arguments} (source : RowsRel child table input result) :
    visitRows visit table input = some result := by
  induction source with
  | nil => rfl
  | raw parts _ ih => simp only [visitRows,parts,bind,pure,ih,Option.bind_some]
  | pair parts edge _ ih =>
      simp only [visitRows,parts,bind,pure,complete _ _ _ edge,Option.bind_some,ih]

/-- A view of the same source Atom, not a second public syntax. -/
inductive Shape where
  | value (expression : Atom)
  | quoted (payload : Atom)
  | lambda (arguments : List Atom) (body : Atom)
  | alternatives (values : List Atom)
  | first (expression : Atom)
  | binding (pattern initializer body : Atom)
  | bindings (rows : List Atom) (body : Atom)
  | selection (key : Atom) (rows : List Atom)
  | application (head : Atom) (arguments : List Atom)

def classify : Atom → Shape
  | .expression [.symbol "|->",.expression arguments,body] => .lambda arguments body
  | .expression [.symbol "quote",payload] => .quoted payload
  | .expression [.symbol "superpose",.expression alternatives] => .alternatives alternatives
  | .expression [.symbol "once",expression] => .first expression
  | .expression [.symbol "let",pattern,initializer,body] => .binding pattern initializer body
  | .expression [.symbol "let*",.expression rows,body] => .bindings rows body
  | .expression [.symbol "case",key,.expression rows] => .selection key rows
  | .expression (head :: arguments) => .application head arguments
  | expression => .value expression

def perform (registry : Program) (foreign : Finset String)
    (visit : Table → Atom → Option Result) (table : Table) : Shape → Option Result
  | .lambda arguments body => do
      let reserved := reserve table registry foreign arguments body
      let translated ← visit reserved.table body
      let completed := finish reserved translated.table translated.expression
      pure ⟨completed.table,completed.closure⟩
  | .quoted payload => some ⟨table,.expression [.symbol "quote",payload]⟩
  | .alternatives alternatives => do
      let translated ← visitArguments visit (fun _ => false) table 0 alternatives
      pure ⟨translated.table,.expression [.symbol "superpose",.expression translated.values]⟩
  | .first expression => do
      let translated ← visit table expression
      pure ⟨translated.table,.expression [.symbol "once",translated.expression]⟩
  | .binding pattern initializer body => do
      let value ← visit table initializer
      let continuation ← visit value.table body
      pure ⟨continuation.table,.expression [.symbol "let",pattern,value.expression,continuation.expression]⟩
  | .bindings rows body => do
      let initializers ← visitRows visit table rows
      let continuation ← visit initializers.table body
      pure ⟨continuation.table,.expression [.symbol "let*",.expression initializers.values,continuation.expression]⟩
  | .selection key rows => do
      let selector ← visit table key
      let branches ← visitRows visit selector.table rows
      pure ⟨branches.table,.expression [.symbol "case",selector.expression,.expression branches.values]⟩
  | .application head [] => do
      let callee ← visit table head
      pure ⟨callee.table,ConstructorDataHeads.emit
        (Unifying.codeRegistry registry callee.table.code) callee.expression []⟩
  | .application head (first :: rest) => do
      let callee ← visit table head
      let translated ← visitArguments visit
        (heldArgument (Unifying.codeRegistry registry callee.table.code) callee.expression)
        callee.table 0 (first :: rest)
      pure ⟨translated.table,ConstructorDataHeads.emit
        (Unifying.codeRegistry registry translated.table.code) callee.expression translated.values⟩
  | .value expression => some ⟨table,expression⟩

inductive Layer (registry : Program) (foreign : Finset String)
    (child : Table → Atom → Result → Prop) : Table → Shape → Result → Prop where
  | value {table expression} : Layer registry foreign child table (.value expression) ⟨table,expression⟩
  | quoted {table payload} :
      Layer registry foreign child table (.quoted payload) ⟨table,.expression [.symbol "quote",payload]⟩
  | lambda {table arguments body reserved translated} :
      ReservationRel table registry foreign arguments body reserved →
      child reserved.table body translated →
      Layer registry foreign child table (.lambda arguments body)
        ⟨(finish reserved translated.table translated.expression).table,
          (finish reserved translated.table translated.expression).closure⟩
  | alternatives {table values translated} :
      ArgumentsRel child (fun _ => false) table 0 values translated →
      Layer registry foreign child table (.alternatives values)
        ⟨translated.table,.expression [.symbol "superpose",.expression translated.values]⟩
  | first {table expression translated} :
      child table expression translated →
      Layer registry foreign child table (.first expression)
        ⟨translated.table,.expression [.symbol "once",translated.expression]⟩
  | binding {table pattern initializer body value continuation} :
      child table initializer value → child value.table body continuation →
      Layer registry foreign child table (.binding pattern initializer body)
        ⟨continuation.table,.expression [.symbol "let",pattern,value.expression,continuation.expression]⟩
  | bindings {table rows body initializers continuation} :
      RowsRel child table rows initializers → child initializers.table body continuation →
      Layer registry foreign child table (.bindings rows body)
        ⟨continuation.table,.expression [.symbol "let*",.expression initializers.values,continuation.expression]⟩
  | selection {table key rows selector branches} :
      child table key selector → RowsRel child selector.table rows branches →
      Layer registry foreign child table (.selection key rows)
        ⟨branches.table,.expression [.symbol "case",selector.expression,.expression branches.values]⟩
  | nullary {table head callee emitted} :
      child table head callee →
      ConstructorDataHeads.Emission (Unifying.codeRegistry registry callee.table.code)
        callee.expression [] emitted →
      Layer registry foreign child table (.application head []) ⟨callee.table,emitted⟩
  | application {table head first rest callee translated emitted} :
      child table head callee →
      ArgumentsRel child (heldArgument (Unifying.codeRegistry registry callee.table.code) callee.expression)
        callee.table 0 (first :: rest) translated →
      ConstructorDataHeads.Emission (Unifying.codeRegistry registry translated.table.code)
        callee.expression translated.values emitted →
      Layer registry foreign child table (.application head (first :: rest))
        ⟨translated.table,emitted⟩

/-- The bound is staging depth, not evaluator fuel. Siblings use the same
depth allowance and preserve a single left-to-right name/code inventory. -/
def prepare (registry : Program) (foreign : Finset String) :
    Nat → Table → Atom → Option Result
  | 0, _, _ => none
  | depth + 1, table, expression =>
      perform registry foreign (prepare registry foreign depth) table (classify expression)

theorem perform_sound (registry : Program) (foreign : Finset String)
    (visit : Table → Atom → Option Result) (child : Table → Atom → Result → Prop)
    (sound : ∀ table input result, visit table input = some result → child table input result)
    (table : Table) (shape : Shape) (result : Result)
    (computed : perform registry foreign visit table shape = some result) :
    Layer registry foreign child table shape result := by
  cases shape with
  | value expression =>
      simp only [perform,Option.some.injEq] at computed
      subst result
      exact .value
  | quoted payload =>
      simp only [perform,Option.some.injEq] at computed
      subst result
      exact .quoted
  | lambda arguments body =>
      simp only [perform,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
      obtain ⟨translated,edge,rfl⟩ := computed
      exact .lambda (reservation_source table registry foreign arguments body) (sound _ _ _ edge)
  | alternatives values =>
      simp only [perform,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
      obtain ⟨translated,edge,rfl⟩ := computed
      exact .alternatives (visitArguments_sound visit child sound _ _ _ _ _ edge)
  | first expression =>
      simp only [perform,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
      obtain ⟨translated,edge,rfl⟩ := computed
      exact .first (sound _ _ _ edge)
  | binding pattern initializer body =>
      simp only [perform,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
      obtain ⟨value,valueComputed,continuation,bodyComputed,rfl⟩ := computed
      exact .binding (sound _ _ _ valueComputed) (sound _ _ _ bodyComputed)
  | bindings rows body =>
      simp only [perform,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
      obtain ⟨initializers,rowsComputed,continuation,bodyComputed,rfl⟩ := computed
      exact .bindings (visitRows_sound visit child sound _ _ _ rowsComputed) (sound _ _ _ bodyComputed)
  | selection key rows =>
      simp only [perform,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
      obtain ⟨selector,keyComputed,branches,rowsComputed,rfl⟩ := computed
      exact .selection (sound _ _ _ keyComputed) (visitRows_sound visit child sound _ _ _ rowsComputed)
  | application head arguments =>
      cases arguments with
      | nil =>
          simp only [perform,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
          obtain ⟨callee,headEdge,rfl⟩ := computed
          exact .nullary (sound _ _ _ headEdge) (ConstructorDataHeads.emit_source _ _ _)
      | cons first rest =>
          simp only [perform,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
          obtain ⟨callee,headEdge,translated,argumentEdges,rfl⟩ := computed
          exact .application (sound _ _ _ headEdge)
            (visitArguments_sound visit child sound _ _ _ _ _ argumentEdges)
            (ConstructorDataHeads.emit_source _ _ _)

theorem perform_complete (registry : Program) (foreign : Finset String)
    (visit : Table → Atom → Option Result) (child : Table → Atom → Result → Prop)
    (complete : ∀ table input result, child table input result → visit table input = some result)
    {table : Table} {shape : Shape} {result : Result}
    (source : Layer registry foreign child table shape result) :
    perform registry foreign visit table shape = some result := by
  cases source with
  | value | quoted => rfl
  | @lambda arguments body reserved translated reservedSource bodySource =>
      have reservation := (reservation_iff _ registry foreign arguments body reserved).mp reservedSource
      simp only [perform,reservation,bind,pure,complete _ _ _ bodySource,Option.bind_some]
  | alternatives arguments =>
      simp only [perform,bind,pure,visitArguments_complete visit child complete arguments,Option.bind_some]
  | first edge => simp only [perform,bind,pure,complete _ _ _ edge,Option.bind_some]
  | binding value continuation =>
      simp only [perform,bind,pure,complete _ _ _ value,Option.bind_some,complete _ _ _ continuation]
  | bindings rows continuation =>
      simp only [perform,bind,pure,visitRows_complete visit child complete rows,Option.bind_some,
        complete _ _ _ continuation]
  | selection key rows =>
      simp only [perform,bind,pure,complete _ _ _ key,Option.bind_some,
        visitRows_complete visit child complete rows]
  | nullary head emitted =>
      simp only [perform,bind,pure,complete _ _ _ head,Option.bind_some,
        (ConstructorDataHeads.emission_iff _ _ _ _).mp emitted]
  | application head arguments emitted =>
      simp only [perform,bind,pure,complete _ _ _ head,Option.bind_some,
        visitArguments_complete visit child complete arguments,
        (ConstructorDataHeads.emission_iff _ _ _ _).mp emitted]

/-- Bounded derivations describe the staging rules. The bound is syntactic
recursion depth; it is unrelated to source evaluation or its interruption. -/
def StageAt (registry : Program) (foreign : Finset String) :
    Nat → Table → Atom → Result → Prop
  | 0, _, _, _ => False
  | depth + 1, table, expression, result =>
      Layer registry foreign (StageAt registry foreign depth) table (classify expression) result

theorem prepare_iff (registry : Program) (foreign : Finset String) :
    ∀ depth table expression result,
    prepare registry foreign depth table expression = some result ↔
      StageAt registry foreign depth table expression result := by
  intro depth
  induction depth with
  | zero => intro table expression result; simp [prepare,StageAt]
  | succ depth ih =>
      intro table expression result
      constructor
      · exact perform_sound registry foreign _ _ (fun table input result edge =>
          (ih table input result).mp edge) table (classify expression) result
      · exact perform_complete registry foreign _ _ (fun table input result edge =>
          (ih table input result).mpr edge)

def Staged (registry : Program) (foreign : Finset String)
    (table : Table) (expression : Atom) (result : Result) : Prop :=
  ∃ depth, StageAt registry foreign depth table expression result

theorem staged_iff_computed (registry : Program) (foreign : Finset String)
    (table : Table) (expression : Atom) (result : Result) :
    Staged registry foreign table expression result ↔
      ∃ depth, prepare registry foreign depth table expression = some result := by
  exact exists_congr (fun depth => (prepare_iff registry foreign depth table expression result).symm)

def rowBodies : List Atom → List Atom
  | [] => []
  | first :: rest =>
      match rowParts first with
      | none => rowBodies rest
      | some (_,body) => body :: rowBodies rest

theorem rowParts_shape {row pattern body : Atom} (parts : rowParts row = some (pattern,body)) :
    row = .expression [pattern,body] := by
  unfold rowParts at parts
  split at parts
  · cases parts; rfl
  · cases parts

theorem mem_rowBodies (rows : List Atom) (body : Atom) :
    body ∈ rowBodies rows ↔ ∃ row ∈ rows, ∃ pattern, rowParts row = some (pattern,body) := by
  induction rows with
  | nil => simp [rowBodies]
  | cons first rest ih =>
      cases parts : rowParts first with
      | none => simp [rowBodies,parts,ih]
      | some pair =>
          rcases pair with ⟨pattern,value⟩
          simp [rowBodies,parts,ih,eq_comm]

def Shape.children : Shape → List Atom
  | .value _ | .quoted _ => []
  | .lambda _ body => [body]
  | .alternatives values => values
  | .first expression => [expression]
  | .binding _ initializer body => [initializer,body]
  | .bindings rows body => body :: rowBodies rows
  | .selection key rows => key :: rowBodies rows
  | .application head arguments => head :: arguments

def depthOf : Atom → Nat
  | .expression items => list items + 1
  | _ => 0
where
  list : List Atom → Nat
    | [] => 0
    | first :: rest => max (depthOf first) (list rest)

private theorem child_depth_bounded (items : List Atom) (child : Atom) (member : child ∈ items) :
    depthOf child ≤ depthOf.list items := by
  induction items with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact Nat.le_max_left _ _
      · exact (ih member).trans (Nat.le_max_right _ _)

private theorem expression_child_smaller (items : List Atom) (child : Atom) (member : child ∈ items) :
    depthOf child < depthOf (Atom.expression items) := by
  have smaller := child_depth_bounded items child member
  simp only [depthOf]
  omega

theorem row_bodies_smaller (rows : List Atom) (child : Atom) (member : child ∈ rowBodies rows) :
    depthOf child < depthOf (.expression rows) := by
  obtain ⟨row,rowMember,pattern,parts⟩ := (mem_rowBodies rows child).mp member
  have smaller : depthOf child < depthOf row := by
    rw [rowParts_shape parts]
    apply expression_child_smaller
    simp
  exact smaller.trans (expression_child_smaller rows row rowMember)

theorem classify_children_smaller (expression child : Atom)
    (member : child ∈ (classify expression).children) : depthOf child < depthOf expression := by
  unfold classify at member
  split at member
  · simp only [Shape.children,List.mem_singleton] at member
    subst child
    apply expression_child_smaller
    simp
  · simp only [Shape.children,List.not_mem_nil] at member
  · simp only [Shape.children] at member
    exact (expression_child_smaller _ _ member).trans (expression_child_smaller _ _ (by simp))
  · simp only [Shape.children,List.mem_singleton] at member
    subst child
    apply expression_child_smaller
    simp
  · simp only [Shape.children,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> apply expression_child_smaller <;> simp
  · simp only [Shape.children,List.mem_cons] at member
    rcases member with rfl | body
    · apply expression_child_smaller; simp
    · exact (row_bodies_smaller _ _ body).trans (expression_child_smaller _ _ (by simp))
  · simp only [Shape.children,List.mem_cons] at member
    rcases member with rfl | body
    · apply expression_child_smaller; simp
    · exact (row_bodies_smaller _ _ body).trans (expression_child_smaller _ _ (by simp))
  · simp only [Shape.children] at member
    exact expression_child_smaller _ _ member
  · simp only [Shape.children,List.not_mem_nil] at member

theorem visitArguments_exists (visit : Table → Atom → Option Result) (held : Nat → Bool)
    (input : List Atom)
    (complete : ∀ expression ∈ input, ∀ table, ∃ result, visit table expression = some result) :
    ∀ table index, ∃ result, visitArguments visit held table index input = some result := by
  induction input with
  | nil => intro table index; exact ⟨_,rfl⟩
  | cons first rest ih =>
      intro table index
      have tailComplete : ∀ expression ∈ rest, ∀ table, ∃ result, visit table expression = some result :=
        fun expression member => complete expression (List.mem_cons_of_mem first member)
      cases demand : held index
      · obtain ⟨entry,entryComputed⟩ := complete first (by simp) table
        obtain ⟨tail,tailComputed⟩ := ih tailComplete entry.table (index + 1)
        exact ⟨⟨tail.table,entry.expression :: tail.values⟩,
          by simp [visitArguments,demand,entryComputed,tailComputed,bind,pure]⟩
      · obtain ⟨tail,tailComputed⟩ := ih tailComplete table (index + 1)
        exact ⟨⟨tail.table,first :: tail.values⟩,
          by simp [visitArguments,demand,tailComputed,bind,pure]⟩

theorem visitRows_exists (visit : Table → Atom → Option Result) (rows : List Atom)
    (complete : ∀ row ∈ rows, ∀ pattern body, rowParts row = some (pattern,body) →
      ∀ table, ∃ result, visit table body = some result) :
    ∀ table, ∃ result, visitRows visit table rows = some result := by
  induction rows with
  | nil => intro table; exact ⟨_,rfl⟩
  | cons first rest ih =>
      intro table
      have restComplete := fun row member => complete row (List.mem_cons_of_mem first member)
      cases parts : rowParts first with
      | none =>
          obtain ⟨tail,tailComputed⟩ := ih restComplete table
          exact ⟨⟨tail.table,first :: tail.values⟩,by simp [visitRows,parts,tailComputed,bind,pure]⟩
      | some pair =>
          rcases pair with ⟨pattern,body⟩
          obtain ⟨compiled,bodyComputed⟩ := complete first (by simp) pattern body parts table
          obtain ⟨tail,tailComputed⟩ := ih restComplete compiled.table
          exact ⟨⟨tail.table,.expression [pattern,compiled.expression] :: tail.values⟩,
            by simp [visitRows,parts,bodyComputed,tailComputed,bind,pure]⟩

theorem prepare_exists (registry : Program) (foreign : Finset String) :
    ∀ depth table expression, depthOf expression < depth →
      ∃ result, prepare registry foreign depth table expression = some result := by
  intro depth
  induction depth with
  | zero => intro table expression bound; omega
  | succ depth ih =>
      intro table expression bound
      have childComplete : ∀ child ∈ (classify expression).children, ∀ table,
          ∃ result, prepare registry foreign depth table child = some result := by
        intro child member table
        exact ih table child (by have := classify_children_smaller expression child member; omega)
      simp only [prepare]
      cases shape : classify expression with
      | value value => exact ⟨_,rfl⟩
      | quoted payload => exact ⟨_,rfl⟩
      | lambda arguments body =>
          obtain ⟨translated,edge⟩ := childComplete body (by simp [shape,Shape.children])
            (reserve table registry foreign arguments body).table
          exact ⟨⟨(finish (reserve table registry foreign arguments body) translated.table translated.expression).table,
            (finish (reserve table registry foreign arguments body) translated.table translated.expression).closure⟩,
            by simp [perform,edge,bind,pure]⟩
      | alternatives values =>
          obtain ⟨translated,edges⟩ := visitArguments_exists (prepare registry foreign depth)
            (fun _ => false) values (by simpa only [shape,Shape.children] using childComplete) table 0
          exact ⟨⟨translated.table,.expression [.symbol "superpose",.expression translated.values]⟩,
            by simp [perform,edges,bind,pure]⟩
      | first expression =>
          obtain ⟨translated,edge⟩ := childComplete expression (by simp [shape,Shape.children]) table
          exact ⟨⟨translated.table,.expression [.symbol "once",translated.expression]⟩,
            by simp [perform,edge,bind,pure]⟩
      | binding pattern initializer body =>
          obtain ⟨value,valueComputed⟩ := childComplete initializer (by simp [shape,Shape.children]) table
          obtain ⟨continuation,bodyComputed⟩ := childComplete body (by simp [shape,Shape.children]) value.table
          exact ⟨⟨continuation.table,.expression [.symbol "let",pattern,value.expression,continuation.expression]⟩,
            by simp [perform,valueComputed,bodyComputed,bind,pure]⟩
      | bindings rows body =>
          have rowsComplete := fun row member pattern value parts before =>
            childComplete value (by
              simp only [shape,Shape.children,List.mem_cons]
              exact Or.inr ((mem_rowBodies rows value).mpr ⟨row,member,pattern,parts⟩)) before
          obtain ⟨initializers,rowsComputed⟩ := visitRows_exists (prepare registry foreign depth) rows rowsComplete table
          obtain ⟨continuation,bodyComputed⟩ := childComplete body (by simp [shape,Shape.children]) initializers.table
          exact ⟨⟨continuation.table,.expression [.symbol "let*",.expression initializers.values,continuation.expression]⟩,
            by simp [perform,rowsComputed,bodyComputed,bind,pure]⟩
      | selection key rows =>
          obtain ⟨selector,keyComputed⟩ := childComplete key (by simp [shape,Shape.children]) table
          have rowsComplete := fun row member pattern value parts before =>
            childComplete value (by
              simp only [shape,Shape.children,List.mem_cons]
              exact Or.inr ((mem_rowBodies rows value).mpr ⟨row,member,pattern,parts⟩)) before
          obtain ⟨branches,rowsComputed⟩ := visitRows_exists (prepare registry foreign depth) rows rowsComplete selector.table
          exact ⟨⟨branches.table,.expression [.symbol "case",selector.expression,.expression branches.values]⟩,
            by simp [perform,keyComputed,rowsComputed,bind,pure]⟩
      | application head arguments =>
          obtain ⟨callee,headEdge⟩ := childComplete head (by simp [shape,Shape.children]) table
          cases arguments with
          | nil =>
              exact ⟨⟨callee.table,ConstructorDataHeads.emit
                (Unifying.codeRegistry registry callee.table.code) callee.expression []⟩,
                by simp [perform,headEdge,bind,pure]⟩
          | cons first rest =>
              have argumentsComplete : ∀ child ∈ first :: rest, ∀ table,
                  ∃ result, prepare registry foreign depth table child = some result := by
                intro child member
                apply childComplete child
                simp [shape,Shape.children,member]
              obtain ⟨translated,edges⟩ := visitArguments_exists (prepare registry foreign depth)
                (heldArgument (Unifying.codeRegistry registry callee.table.code) callee.expression)
                (first :: rest) argumentsComplete callee.table 0
              exact ⟨⟨translated.table,ConstructorDataHeads.emit
                (Unifying.codeRegistry registry translated.table.code) callee.expression translated.values⟩,
                by simp [perform,headEdge,edges,bind,pure]⟩

/-- Every finite input has a staging derivation. This does not assert that
the preparation phase alone implements the whole source translator. -/
theorem staged_exists (registry : Program) (foreign : Finset String) (table : Table) (expression : Atom) :
    ∃ result, Staged registry foreign table expression result := by
  obtain ⟨result,computed⟩ := prepare_exists registry foreign (depthOf expression + 1) table expression (by omega)
  exact ⟨result,staged_iff_computed registry foreign table expression result |>.mpr ⟨_,computed⟩⟩

/-- A total interface computes a structural depth and prepares once.
The existence proof is erased; the depth scan still has its own cost. -/
def stage (registry : Program) (foreign : Finset String) (table : Table) (expression : Atom) : Result :=
  (prepare registry foreign (depthOf expression + 1) table expression).get
    (Option.isSome_iff_exists.mpr (prepare_exists registry foreign (depthOf expression + 1)
      table expression (by omega)))

theorem stage_computed (registry : Program) (foreign : Finset String) (table : Table) (expression : Atom) :
    prepare registry foreign (depthOf expression + 1) table expression =
      some (stage registry foreign table expression) := (Option.some_get _).symm

theorem stage_source (registry : Program) (foreign : Finset String) (table : Table) (expression : Atom) :
    Staged registry foreign table expression (stage registry foreign table expression) :=
  (staged_iff_computed registry foreign table expression _).mpr ⟨_,stage_computed _ _ _ _⟩

structure Extension (before after : Table) : Prop where
  code : ∃ added, after.code = before.code ++ added
  cursor : before.cursor ≤ after.cursor
  occupied : before.occupied ⊆ after.occupied

theorem Extension.refl (table : Table) : Extension table table :=
  ⟨⟨[],by simp⟩,Nat.le_refl _,Finset.Subset.refl _⟩

theorem Extension.trans {first second third : Table}
    (left : Extension first second) (right : Extension second third) : Extension first third := by
  obtain ⟨added,leftCode⟩ := left.code
  obtain ⟨later,rightCode⟩ := right.code
  exact ⟨⟨added ++ later,by rw [rightCode,leftCode,List.append_assoc]⟩,
    left.cursor.trans right.cursor,Finset.Subset.trans left.occupied right.occupied⟩

theorem reserve_extension (table : Table) (registry : Program) (foreign : Finset String)
    (arguments : List Atom) (body : Atom) :
    Extension table (reserve table registry foreign arguments body).table := by
  refine ⟨⟨[],by simp [reserve]⟩,Nat.le_of_lt (reserve_advances _ _ _ _ _),?_⟩
  intro key member
  apply Finset.mem_insert_of_mem
  simp [LambdaLifting.occupied,member]

theorem finish_extension (reserved : Reservation) (afterBody : Table) (body : Atom) :
    Extension afterBody (finish reserved afterBody body).table :=
  ⟨⟨_,rfl⟩,Nat.le_refl _,Finset.Subset.refl _⟩

theorem ArgumentsRel.extension (child : Table → Atom → Result → Prop)
    (preserves : ∀ table input result, child table input result → Extension table result.table)
    {held : Nat → Bool} {table : Table} {index : Nat} {input : List Atom} {result : Arguments}
    (source : ArgumentsRel child held table index input result) : Extension table result.table := by
  induction source with
  | nil => exact Extension.refl _
  | held _ _ ih => exact ih
  | translated _ edge _ ih => exact (preserves _ _ _ edge).trans ih

theorem RowsRel.extension (child : Table → Atom → Result → Prop)
    (preserves : ∀ table input result, child table input result → Extension table result.table)
    {table : Table} {input : List Atom} {result : Arguments} (source : RowsRel child table input result) :
    Extension table result.table := by
  induction source with
  | nil => exact Extension.refl _
  | raw _ _ ih => exact ih
  | pair _ edge _ ih => exact (preserves _ _ _ edge).trans ih

theorem Layer.extension (registry : Program) (foreign : Finset String)
    (child : Table → Atom → Result → Prop)
    (preserves : ∀ table input result, child table input result → Extension table result.table)
    {table : Table} {shape : Shape} {result : Result}
    (source : Layer registry foreign child table shape result) : Extension table result.table := by
  cases source with
  | value | quoted => exact Extension.refl _
  | @lambda arguments body reserved translated reservation edge =>
      have exactReservation := (reservation_iff _ registry foreign arguments body reserved).mp reservation
      have reservedExtends : Extension table reserved.table := by
        rw [← exactReservation]
        exact reserve_extension _ _ _ _ _
      exact reservedExtends.trans ((preserves _ _ _ edge).trans (finish_extension _ _ _))
  | alternatives edges => exact edges.extension child preserves
  | @first expression translated edge => exact preserves table expression translated edge
  | @binding pattern initializer body value continuation valueEdge continuationEdge =>
      exact (preserves table initializer value valueEdge).trans
        (preserves value.table body continuation continuationEdge)
  | @bindings rows body initializers continuation rowsEdge continuationEdge =>
      exact (rowsEdge.extension child preserves).trans
        (preserves initializers.table body continuation continuationEdge)
  | selection key rows => exact (preserves _ _ _ key).trans (rows.extension child preserves)
  | @nullary head callee emitted edge _ => exact preserves table head callee edge
  | application head arguments _ => exact (preserves _ _ _ head).trans (arguments.extension child preserves)

theorem StageAt.extension (registry : Program) (foreign : Finset String) :
    ∀ depth table expression result, StageAt registry foreign depth table expression result →
      Extension table result.table := by
  intro depth
  induction depth with
  | zero => intro table expression result impossible; exact False.elim impossible
  | succ depth ih =>
      intro table expression result source
      exact Layer.extension registry foreign (StageAt registry foreign depth) ih source

theorem prepare_extension (registry : Program) (foreign : Finset String)
    (depth : Nat) (table : Table) (expression : Atom) (result : Result)
    (computed : prepare registry foreign depth table expression = some result) :
    Extension table result.table :=
  StageAt.extension registry foreign depth table expression result
    ((prepare_iff registry foreign depth table expression result).mp computed)

end Mettapedia.Languages.MeTTa.PeTTa.LambdaStaging
