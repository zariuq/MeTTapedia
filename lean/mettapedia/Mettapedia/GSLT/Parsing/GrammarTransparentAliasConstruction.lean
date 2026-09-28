import Mettapedia.GSLT.Parsing.GrammarConstructorActionAssembly
import Mettapedia.GSLT.Parsing.MeTTaAtomActionCompiler

/-!
# Typed transparent unary productions

A grammar production with exactly one nonterminal and no terminals may be
interpreted as a transparent wrapper when its child's semantic sort equals its
result sort. This is an optional interpretation law, not a default action:
productions of other shapes or sorts remain unfilled. A caller must decide
whether this quotient is appropriate for the source language's observation.

An existing action at the same occurrence is accepted only when its compiled
program is identical to the transparent action. The generic compiler theorem
then establishes equality of their values on all well-sorted child inputs.
Finalization still requires actions for every remaining production.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Mettapedia.GSLT.Parsing.GrammarTransparentAliasConstruction

open LanguageDefSyntaxCompiler (CompiledRule StructuralAtom)
open LanguageDefGrammarAlgebra (childSorts)
open Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted
open MeTTaAtomConstruction (Kind Value Action algebra)
open GrammarConstructorActionAssembly (Assembly RowAction)

/-- One exact structural reference, with no punctuation or lexical terminal. -/
def child? : List StructuralAtom → Option String
  | [.nonterminal _ sort _] => some sort
  | _ => none

theorem child?_no_terminal {atoms : List StructuralAtom} {sort : String}
    (found : child? atoms = some sort) : childSorts atoms = [sort] := by
  cases atoms with
  | nil => simp [child?] at found
  | cons first rest =>
      cases first with
      | terminal token parserRef =>
          cases rest <;> simp [child?] at found
      | nonterminal parameter child parserRef =>
          cases rest with
          | nil =>
              simp only [child?, Option.some.injEq] at found
              subst sort
              rfl
          | cons second tail => simp [child?] at found

/-- The action type is obtained from the actual compiled child context;
no guessed child index or default value is available. -/
def action? (rules : List CompiledRule) (sortMap : String → Kind)
    (row : Fin rules.length) :
    Option (RowAction rules algebra sortMap row) :=
  match found : child? rules[row].atoms with
  | none => none
  | some child =>
      if same : sortMap child = sortMap rules[row].source.category then
        let context : (childSorts rules[row].atoms).map sortMap =
            [sortMap rules[row].source.category] := by
          rw [child?_no_terminal found]
          simp [same]
        let candidate : RowAction rules algebra sortMap row := by
          change Action ((childSorts rules[row].atoms).map sortMap)
            (sortMap rules[row].source.category)
          rw [context]
          exact .input .here
        some candidate
      else none

theorem action?_available (rules : List CompiledRule)
    (sortMap : String → Kind) (row : Fin rules.length) (child : String)
    (found : child? rules[row].atoms = some child)
    (same : sortMap child = sortMap rules[row].source.category) :
    (action? rules sortMap row).isSome = true := by
  unfold action?
  split
  · rename_i absent
    have impossible : none = some child := absent.symm.trans found
    cases impossible
  · rename_i selected selectedEq
    have identified : selected = child :=
      Option.some.inj (selectedEq.symm.trans found)
    subst selected
    simp [same]

theorem action?_refuses_mismatched_sort (rules : List CompiledRule)
    (sortMap : String → Kind) (row : Fin rules.length) (child : String)
    (found : child? rules[row].atoms = some child)
    (different : sortMap child ≠ sortMap rules[row].source.category) :
    action? rules sortMap row = none := by
  unfold action?
  split
  · rfl
  · rename_i selected selectedEq
    have identified : selected = child :=
      Option.some.inj (selectedEq.symm.trans found)
    subst selected
    simp
    exact different

theorem action?_refuses_nonalias (rules : List CompiledRule)
    (sortMap : String → Kind) (row : Fin rules.length)
    (notAlias : child? rules[row].atoms = none) :
    action? rules sortMap row = none := by
  unfold action?
  split
  · rfl
  · rename_i selected selectedEq
    have impossible : some selected = none := selectedEq.symm.trans notAlias
    cases impossible

/-- The native-facing program is compiled from the registered typed route
using the parser row's real terminal-inclusive slot positions. -/
def compiledAt (rules : List CompiledRule) (sortMap : String → Kind)
    (row : Fin rules.length) (route : RowAction rules algebra sortMap row) :
    MeTTaAtomActionCompiler.CompiledAction :=
  MeTTaAtomActionCompiler.compileWithSlots
    (GrammarConstructorActions.parserSlot sortMap rules[row].atoms) route

/-- Equal compiled programs compute the same typed value on every valid
child tuple. This follows from the generic compiler's execution theorem and
injectivity of the typed value encoding, not from sample agreement. -/
theorem compiledAt_equal_values (rules : List CompiledRule)
    (sortMap : String → Kind) (row : Fin rules.length)
    (first second : RowAction rules algebra sortMap row)
    (same : compiledAt rules sortMap row first = compiledAt rules sortMap row second)
    (values : FamilyList Value ((childSorts rules[row].atoms).map sortMap)) :
    Action.run first values = Action.run second values := by
  let terminalValue : String → String →
      Mettapedia.Languages.MeTTa.OSLFCore.Atom := fun _ _ => .symbol "terminal"
  have firstExec := MeTTaAtomActionCompiler.compile_parserAtomSlots_executes
    sortMap terminalValue rules[row].atoms values first
  have secondExec := MeTTaAtomActionCompiler.compile_parserAtomSlots_executes
    sortMap terminalValue rules[row].atoms values second
  have programEqual := congrArg
    (MeTTaAtomActionCompiler.execute
      (MeTTaAtomActionCompiler.parserAtomValues sortMap terminalValue
        rules[row].atoms values)) same
  dsimp only [compiledAt] at programEqual
  have encoded :
      MeTTaAtomActionCompiler.encodeValue
          (sortMap rules[row].source.category) (Action.run first values) =
        MeTTaAtomActionCompiler.encodeValue
          (sortMap rules[row].source.category) (Action.run second values) := by
    exact Option.some.inj (firstExec.symm.trans (programEqual.trans secondExec))
  exact (MeTTaAtomActionCompiler.encodeValue_injective
    (sortMap rules[row].source.category) _ _).mp encoded

/-- Wire equality is decidable because it is equality of host atoms. The
existing decoder proves that this check reflects compiled-program equality. -/
theorem encoded_program_equal_values (rules : List CompiledRule)
    (sortMap : String → Kind) (row : Fin rules.length)
    (first second : RowAction rules algebra sortMap row)
    (same : MeTTaAtomActionCompiler.encodeAction
        (compiledAt rules sortMap row first) =
      MeTTaAtomActionCompiler.encodeAction
        (compiledAt rules sortMap row second))
    (values : FamilyList Value ((childSorts rules[row].atoms).map sortMap)) :
    Action.run first values = Action.run second values := by
  have decoded := congrArg MeTTaAtomActionCompiler.decodeAction same
  have programs : compiledAt rules sortMap row first =
      compiledAt rules sortMap row second := by
    simpa only [MeTTaAtomActionCompiler.decodeAction_encodeAction,
      Option.some.injEq] using decoded
  exact compiledAt_equal_values rules sortMap row first second programs values

/-- Install every source-transparent row. Existing registrations must compile
to the same action; a conflict rejects the assembly rather than overriding it. -/
def registerAt? {rules : List CompiledRule} {sortMap : String → Kind}
    (assembly : Assembly rules algebra sortMap) (row : Fin rules.length) :
    Option (Assembly rules algebra sortMap) :=
  match action? rules sortMap row with
  | none => some assembly
  | some identity =>
      match assembly.slots row with
      | none => assembly.register? row identity
      | some existing =>
          if MeTTaAtomActionCompiler.encodeAction
                (compiledAt rules sortMap row existing) =
              MeTTaAtomActionCompiler.encodeAction
                (compiledAt rules sortMap row identity) then
            some assembly
          else none

/-- Successful overlap admission is a semantic agreement, not simply a
nonempty slot or a sample comparison. -/
theorem registered_alias_overlap_agrees {rules : List CompiledRule}
    {sortMap : String → Kind} (assembly : Assembly rules algebra sortMap)
    (row : Fin rules.length)
    (identity existing : RowAction rules algebra sortMap row)
    (identityFound : action? rules sortMap row = some identity)
    (alreadyRegistered : assembly.slots row = some existing)
    (accepted : (registerAt? assembly row).isSome = true)
    (values : FamilyList Value ((childSorts rules[row].atoms).map sortMap)) :
    Action.run existing values = Action.run identity values := by
  have sameWire : MeTTaAtomActionCompiler.encodeAction
      (compiledAt rules sortMap row existing) =
      MeTTaAtomActionCompiler.encodeAction
        (compiledAt rules sortMap row identity) := by
    by_contra different
    simp [registerAt?, identityFound, alreadyRegistered, different] at accepted
  exact encoded_program_equal_values rules sortMap row existing identity sameWire values

def registerAll? {rules : List CompiledRule} {sortMap : String → Kind}
    (assembly : Assembly rules algebra sortMap) :
    Option (Assembly rules algebra sortMap) :=
  (List.finRange rules.length).foldlM registerAt? assembly

/-- A language may assign lexical rows to a separate lexical construction.
Selection is explicit; unselected rows retain their current slots and remain
obligations of the whole-language finalizer. -/
def registerSelected? {rules : List CompiledRule} {sortMap : String → Kind}
    (admit : Fin rules.length → Bool)
    (assembly : Assembly rules algebra sortMap) :
    Option (Assembly rules algebra sortMap) :=
  (List.finRange rules.length).foldlM (fun current row =>
    if admit row then registerAt? current row else some current) assembly

example : child? [.nonterminal "x" "Formula" "Formula"] = some "Formula" := rfl
example : child? [.terminal "~" "tilde", .nonterminal "x" "Formula" "Formula"] = none := rfl
example : child? ([] : List StructuralAtom) = none := rfl

#print axioms child?_no_terminal
#print axioms action?_available
#print axioms action?_refuses_mismatched_sort
#print axioms action?_refuses_nonalias
#print axioms compiledAt_equal_values
#print axioms encoded_program_equal_values
#print axioms registered_alias_overlap_agrees

end Mettapedia.GSLT.Parsing.GrammarTransparentAliasConstruction
