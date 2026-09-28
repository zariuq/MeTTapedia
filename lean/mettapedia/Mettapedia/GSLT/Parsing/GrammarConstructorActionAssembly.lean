import Mettapedia.GSLT.Parsing.GrammarConstructorActions

/-!
# Assembly of typed grammar constructor actions

Each parser-emittable production occurrence has one slot whose type is fixed by
that production's compiled child sorts and result sort. Registration rejects a
second action for the same occurrence, regardless of whether it is identical or
conflicting. Finalization constructs the executable `Templates` family only
when every occurrence has been supplied. Equal source rows at different
positions remain different occurrences, as in the grammar algebra.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.GrammarConstructorActionAssembly

open Mettapedia.GSLT.LanguageDef.ConstructionProvenance
open Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted
open Mettapedia.GSLT.Parsing.LanguageDefGrammarAlgebra
open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler
open Mettapedia.GSLT.Parsing.GrammarConstructorActions

/-- The exact action type of one compiled production occurrence. -/
abbrev RowAction (rules : List CompiledRule)
    (target : ManySortedConstructionAlgebra.{0, 0, 0, 0})
    (sortMap : String → target.Kind) (index : Fin rules.length) : Type :=
  OpenConstructionRoute target
    ((childSorts rules[index].atoms).map sortMap)
    (sortMap rules[index].source.category)

/-- A partial, occurrence-indexed interpretation under construction. -/
structure Assembly (rules : List CompiledRule)
    (target : ManySortedConstructionAlgebra.{0, 0, 0, 0})
    (sortMap : String → target.Kind) where
  slots : (index : Fin rules.length) → Option (RowAction rules target sortMap index)

/-- Initially no production has an action. -/
def Assembly.empty (rules : List CompiledRule)
    (target : ManySortedConstructionAlgebra.{0, 0, 0, 0})
    (sortMap : String → target.Kind) : Assembly rules target sortMap where
  slots := fun _ => none

/-- Register exactly one typed action at an occurrence. Re-registration is an
error even when the proposed action is extensionally the same. -/
def Assembly.register? {rules : List CompiledRule}
    {target : ManySortedConstructionAlgebra.{0, 0, 0, 0}}
    {sortMap : String → target.Kind}
    (assembly : Assembly rules target sortMap) (index : Fin rules.length)
    (action : RowAction rules target sortMap index) :
    Option (Assembly rules target sortMap) :=
  if (assembly.slots index).isSome then none
  else some ⟨fun current =>
    if same : index = current then
      same ▸ some action
    else assembly.slots current⟩

/-- Successful registration fills its index with precisely the supplied
action, so a subsequent registration there is rejected. -/
theorem Assembly.register?_same_index_rejected {rules : List CompiledRule}
    {target : ManySortedConstructionAlgebra.{0, 0, 0, 0}}
    {sortMap : String → target.Kind}
    (assembly : Assembly rules target sortMap) (index : Fin rules.length)
    (action replacement : RowAction rules target sortMap index)
    (next : Assembly rules target sortMap)
    (registered : assembly.register? index action = some next) :
    next.register? index replacement = none := by
  unfold Assembly.register? at registered
  split at registered
  · contradiction
  · cases registered
    simp [Assembly.register?]

/-- Finalization has no fallback action: a missing row makes the whole
interpretation unavailable. The successful result is the actual total,
executable constructor-action family. -/
def Assembly.finish? {rules : List CompiledRule}
    {target : ManySortedConstructionAlgebra.{0, 0, 0, 0}}
    {sortMap : String → target.Kind}
    (assembly : Assembly rules target sortMap) : Option (Templates rules target) :=
  if complete : ∀ index : Fin rules.length, (assembly.slots index).isSome = true then
    some ⟨sortMap, fun index => (assembly.slots index).get (complete index)⟩
  else none

/-- Any missing parser-emittable occurrence prevents finalization. -/
theorem Assembly.finish?_none_of_missing {rules : List CompiledRule}
    {target : ManySortedConstructionAlgebra.{0, 0, 0, 0}}
    {sortMap : String → target.Kind}
    (assembly : Assembly rules target sortMap) (index : Fin rules.length)
    (missing : assembly.slots index = none) : assembly.finish? = none := by
  unfold Assembly.finish?
  split
  · rename_i complete
    have present := complete index
    simp [missing] at present
  · rfl

/-- A complete typed family finalizes to an actual `Templates` value. -/
theorem Assembly.finish?_some_of_complete {rules : List CompiledRule}
    {target : ManySortedConstructionAlgebra.{0, 0, 0, 0}}
    {sortMap : String → target.Kind}
    (assembly : Assembly rules target sortMap)
    (complete : ∀ index : Fin rules.length, (assembly.slots index).isSome = true) :
    ∃ templates : Templates rules target, assembly.finish? = some templates := by
  unfold Assembly.finish?
  split
  · exact ⟨_, rfl⟩
  · contradiction

/-- Successful finalization exposes exactly the registered action at every
parser-emittable occurrence. -/
theorem Assembly.finish?_action {rules : List CompiledRule}
    {target : ManySortedConstructionAlgebra.{0, 0, 0, 0}}
    {sortMap : String → target.Kind}
    (assembly : Assembly rules target sortMap) (templates : Templates rules target)
    (finished : assembly.finish? = some templates) (index : Fin rules.length) :
    HEq (assembly.slots index) (some (templates.action index)) := by
  unfold Assembly.finish? at finished
  split at finished
  · rename_i complete
    cases finished
    cases result : assembly.slots index with
    | none =>
        have present := complete index
        simp [result] at present
    | some action =>
        change HEq (some action) (some ((assembly.slots index).get (complete index)))
        simp [result]
  · contradiction

/-! Small executable controls. The first row has one `Expr` child; the second
is nullary. Thus even these fixtures exercise differing indexed action types. -/

private def testAlgebra : ManySortedConstructionAlgebra where
  Kind := String
  Object := fun _ => Unit
  Source := fun _ => Unit
  Operation := fun _ _ => Empty
  interpretSource := fun _ => ()
  interpretOperation := fun impossible _ => nomatch impossible

private def testEncoding : ConstructorEncoding testAlgebra where
  value := fun _ _ => .symbol "unit"
  head := fun impossible => nomatch impossible
  operation_exact := fun impossible _ => nomatch impossible

private def testRules : List CompiledRule :=
  [{ source := { label := "child", category := "Expr", params := [.simple "x" (.base "Expr")], syntaxPattern := [.nonTerminal "x"] },
     atoms := [.nonterminal "x" "Expr" "Expr"],
     body := .node "child" (compileSequence [.nonterminal "x" "Expr" "Expr"]) },
   { source := { label := "leaf", category := "Expr", params := [], syntaxPattern := [] },
     atoms := [], body := .node "leaf" .epsilon }]

private def testBinding : Binding where
  literalRef := fun _ => none
  lexicalSortRef := fun _ => none
  categoryRef := id
  ruleRef := id

/-- The example rows are genuine outputs of the existing structural compiler. -/
theorem test_rows_are_compiled :
    testRules.map (fun rule => compileRule? testBinding rule.source) =
      testRules.map some := by
  rfl

private def testInitial : Assembly testRules testAlgebra id :=
  Assembly.empty testRules testAlgebra id

private def testFirst : Option (Assembly testRules testAlgebra id) :=
  testInitial.register? ⟨0, by decide⟩ (.input .here)

private def testComplete : Option (Assembly testRules testAlgebra id) := do
  let first ← testFirst
  first.register? ⟨1, by decide⟩ (.source ())

/-- Both differently typed rows assemble into a total interpretation. -/
theorem complete_two_row_interpretation :
    (testComplete.bind Assembly.finish?).isSome = true := by
  rfl

/-- Finalization supplies an executable parser action, not merely a coverage
flag. The nonterminal child occupies structural parser slot zero. -/
theorem assembled_first_parser_action :
    (testComplete.bind (fun assembly =>
      (assembly.finish?).map (fun templates =>
        templates.exportParserAction testEncoding ⟨0, by decide⟩))) =
      some (.application "pa-slot" [encodeIndex 0]) := by
  rfl

/-- A second registration of the first occurrence cannot overwrite it. -/
theorem duplicate_row_rejected :
    (testFirst.bind (fun assembly =>
      assembly.register? ⟨0, by decide⟩ (.input .here))).isNone = true := by
  decide

/-- Finalization refuses an omitted parser-emittable occurrence. -/
theorem missing_row_rejected :
    (testFirst.bind Assembly.finish?).isNone = true := by
  decide

end Mettapedia.GSLT.Parsing.GrammarConstructorActionAssembly
