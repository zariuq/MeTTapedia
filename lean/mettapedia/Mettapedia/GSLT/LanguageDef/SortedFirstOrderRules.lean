import Mettapedia.GSLT.LanguageDef.FirstOrderRules
import Mettapedia.GSLT.LanguageDef.WellSorted
import Mettapedia.OSLF.MeTTaIL.ContextSubstitution
import Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation

/-!
# Many-sorted first-order inference rules

The rule rows are the existing named `FORule` schemas. Each formal has a
declared type, and every rule instance checks its complete argument vector
against those types in the actual ambient context. Local assumptions are
separate from globally available rules.

The ordinary schema fragment consists of declared named metavariables and
constructor applications. Numbering the formals is a representation change:
named instantiation agrees with the shared context-substitution action.
Object binders, collection forms and implicit computation are other fragments.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open FirstOrderRules WellSorted

mutual
  /-- Ordinary named schemas, with every metavariable in the formal inventory. -/
  inductive Schema (names : List String) : Pattern → Prop where
    | metavariable {name : String} : name ∈ names → Schema names (.fvar name)
    | constructor {name : String} {arguments : List Pattern} :
        Schemas names arguments → Schema names (.apply name arguments)

  inductive Schemas (names : List String) : List Pattern → Prop where
    | nil : Schemas names []
    | cons {pattern : Pattern} {patterns : List Pattern} :
        Schema names pattern → Schemas names patterns →
        Schemas names (pattern :: patterns)
end

/- Ordinary first-order schemas contain no binding constructors. -/
mutual
  theorem Schema.binderFree {names : List String} {pattern : Pattern}
      (schema : Schema names pattern) : binderFree pattern = true := by
    cases schema with
    | metavariable => rfl
    | constructor arguments => exact Schemas.binderFree arguments
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem Schemas.binderFree {names : List String} {patterns : List Pattern}
      (schemas : Schemas names patterns) : binderFreeList patterns = true := by
    cases schemas with
    | nil => rfl
    | cons first rest => simp only [binderFreeList, Schema.binderFree first, Schemas.binderFree rest, Bool.and_self]
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-- Every premise retains its schema admission, including repeated occurrences. -/
theorem Schemas.member {names : List String} {patterns : List Pattern}
    (schemas : Schemas names patterns) {pattern : Pattern} (member : pattern ∈ patterns) :
    Schema names pattern := by
  induction patterns with
  | nil => cases member
  | cons head patterns ih =>
      cases schemas with
      | cons first rest =>
          rcases List.mem_cons.mp member with rfl | member
          · exact first
          · exact ih rest member

mutual
  def checkSchema (names : List String) : Pattern → Bool
    | .fvar name => names.contains name
    | .apply _ arguments => checkSchemas names arguments
    | _ => false
  termination_by pattern => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  def checkSchemas (names : List String) : List Pattern → Bool
    | [] => true
    | pattern :: patterns => checkSchema names pattern && checkSchemas names patterns
  termination_by patterns => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

mutual
  theorem checkSchema_iff (names : List String) (pattern : Pattern) :
      checkSchema names pattern = true ↔ Schema names pattern := by
    cases pattern with
    | fvar name =>
        simp only [checkSchema, List.contains_iff_mem]
        exact ⟨Schema.metavariable, fun proof => by cases proof; assumption⟩
    | apply name arguments =>
        rw [checkSchema, checkSchemas_iff]
        exact ⟨Schema.constructor, fun proof => by cases proof; assumption⟩
    | _ =>
        constructor
        · intro impossible; simp [checkSchema] at impossible
        · intro impossible; cases impossible
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem checkSchemas_iff (names : List String) (patterns : List Pattern) :
      checkSchemas names patterns = true ↔ Schemas names patterns := by
    cases patterns with
    | nil => exact ⟨fun _ => .nil, fun _ => by simp [checkSchemas]⟩
    | cons pattern patterns =>
        rw [checkSchemas, Bool.and_eq_true, checkSchema_iff, checkSchemas_iff]
        exact ⟨fun ⟨first, rest⟩ => .cons first rest,
          fun proof => by cases proof; exact ⟨‹_›, ‹_›⟩⟩
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-- Positional names remain available beside their numbered schema names. -/
def numberedBindings (names : List String) : Bindings :=
  names.zip ((List.range names.length).map Pattern.bvar)

def numbered (names : List String) (pattern : Pattern) : Pattern :=
  applyBindings (numberedBindings names) pattern

/-- A total action whose relevant positions are supplied by the argument vector. -/
def argumentAt (arguments : List Pattern) (index : Nat) : Pattern :=
  arguments[index]?.getD (.bvar index)

theorem find?_zip {names : List String} {arguments : List Pattern}
    (distinct : names.Nodup) {index : Nat} {name : String} {argument : Pattern}
    (variableLookup : names[index]? = some name)
    (argumentLookup : arguments[index]? = some argument) :
    (names.zip arguments).find? (fun entry => entry.1 == name) = some (name, argument) := by
  induction names generalizing arguments index with
  | nil => simp at variableLookup
  | cons first names ih =>
      cases arguments with
      | nil => simp at argumentLookup
      | cons argumentHead arguments =>
          cases index with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at variableLookup argumentLookup
              subst name
              subst argument
              simp
          | succ index =>
              simp only [List.getElem?_cons_succ] at variableLookup argumentLookup
              have different : first ≠ name := by
                intro same
                exact (List.nodup_cons.mp distinct).1
                  (same.symm ▸ List.mem_of_getElem? variableLookup)
              simpa [different] using ih distinct.tail variableLookup argumentLookup

theorem numberedBindings_lookup {names : List String} (distinct : names.Nodup)
    {index : Nat} {name : String} (lookup : names[index]? = some name) :
    (numberedBindings names).find? (fun entry => entry.1 == name) =
      some (name, .bvar index) := by
  apply find?_zip distinct lookup
  have bound : index < names.length := (List.getElem?_eq_some_iff.mp lookup).1
  simp [bound]

mutual
  /-- Named substitution and numbered context substitution have identical instances. -/
  theorem Schema.instantiate_numbered {names : List String} {pattern : Pattern}
      (schema : Schema names pattern) (distinct : names.Nodup)
      (arguments : List Pattern) (arity : arguments.length = names.length) :
      applyBindings (names.zip arguments) pattern =
        Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute (argumentAt arguments)
          (numbered names pattern) := by
    cases schema with
    | @metavariable name member =>
        have nameLookup := List.getElem?_idxOf member
        have bound : names.idxOf name < arguments.length := by
          rw [arity]
          exact List.idxOf_lt_length_iff.mpr member
        have argumentLookup : arguments[names.idxOf name]? =
            some arguments[names.idxOf name] := List.getElem?_eq_getElem bound
        simp [numbered, applyBindings, numberedBindings_lookup distinct nameLookup,
          find?_zip distinct nameLookup argumentLookup,
          Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute, argumentAt, argumentLookup]
    | constructor children =>
        simpa only [numbered, applyBindings,
          Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute,
          Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substituteList_eq_map,
          List.map_map, Function.comp_def] using
          congrArg (Pattern.apply _) (children.instantiate_numbered distinct arguments arity)
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem Schemas.instantiate_numbered {names : List String} {patterns : List Pattern}
      (schemas : Schemas names patterns) (distinct : names.Nodup)
      (arguments : List Pattern) (arity : arguments.length = names.length) :
      patterns.map (applyBindings (names.zip arguments)) =
        patterns.map (fun pattern =>
          Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute (argumentAt arguments)
            (numbered names pattern)) := by
    cases schemas with
    | nil => rfl
    | cons first rest =>
        simp only [List.map_cons, first.instantiate_numbered distinct arguments arity,
          rest.instantiate_numbered distinct arguments arity]
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

mutual
  /-- Numbered schemas stay in the existing first-order compiler fragment. -/
  theorem Schema.numbered_firstOrder {names : List String} {pattern : Pattern}
      (schema : Schema names pattern) (distinct : names.Nodup) :
      isMatchCorrectAux (numbered names pattern) = true := by
    cases schema with
    | metavariable member =>
        have lookup := numberedBindings_lookup distinct (List.getElem?_idxOf member)
        simp [numbered, applyBindings, lookup, isMatchCorrectAux]
    | @constructor name arguments children =>
        have corrected := children.numbered_firstOrder distinct
        have mapping : arguments.map (numbered names) =
            arguments.map (applyBindings (numberedBindings names)) :=
          List.map_congr_left fun _ _ => rfl
        rw [mapping] at corrected
        simpa only [numbered, applyBindings, isMatchCorrectAux] using corrected
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem Schemas.numbered_firstOrder {names : List String} {patterns : List Pattern}
      (schemas : Schemas names patterns) (distinct : names.Nodup) :
      isMatchCorrectListAux (patterns.map (numbered names)) = true := by
    cases schemas with
    | nil => rfl
    | cons first rest =>
        simp only [List.map_cons, isMatchCorrectListAux, Bool.and_eq_true]
        exact ⟨first.numbered_firstOrder distinct, rest.numbered_firstOrder distinct⟩
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-- Types refine an existing rule row; names, premise order and conclusion stay intact. -/
structure Rule where
  row : FORule
  variableTypes : List TypeExpr
  deriving Repr, DecidableEq

/-- A source statement has an authored judgment sort, independently of any backend. -/
def Statement (language : LanguageDef) (judgmentSorts : List String)
    (context : List TypeExpr) (pattern : Pattern) : Prop :=
  ∃ name, name ∈ judgmentSorts ∧
    HasType language FreeTypeContext.empty context pattern (.base name)

/-- Admission checks all schemas and formal sorts, not only the final goal. -/
structure Rule.WellFormed (language : LanguageDef) (judgmentSorts : List String)
    (rule : Rule) : Prop where
  distinctNames : rule.row.vars.Nodup
  arity : rule.variableTypes.length = rule.row.vars.length
  declaredTypes : ∀ type ∈ rule.variableTypes,
    ∃ name, type = .base name ∧ name ∈ language.typeNames
  premiseSchemas : Schemas rule.row.vars rule.row.premises
  conclusionSchema : Schema rule.row.vars rule.row.conclusion
  hypotheses : ∀ pattern ∈ rule.row.premises,
    Statement language judgmentSorts rule.variableTypes (numbered rule.row.vars pattern)
  conclusion : Statement language judgmentSorts rule.variableTypes
    (numbered rule.row.vars rule.row.conclusion)

theorem Rule.WellFormed.instPremises_numbered {language : LanguageDef}
    {judgmentSorts : List String} {rule : Rule}
    (formed : rule.WellFormed language judgmentSorts)
    (arguments : List Pattern) (arity : arguments.length = rule.row.vars.length) :
    rule.row.instPremises arguments =
      Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substituteList (argumentAt arguments)
        (rule.row.premises.map (numbered rule.row.vars)) := by
  have same := formed.premiseSchemas.instantiate_numbered formed.distinctNames arguments arity
  simpa only [FORule.instPremises, FORule.bindings,
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substituteList_eq_map,
    List.map_map, Function.comp_def] using same

theorem Rule.WellFormed.instConclusion_numbered {language : LanguageDef}
    {judgmentSorts : List String} {rule : Rule}
    (formed : rule.WellFormed language judgmentSorts)
    (arguments : List Pattern) (arity : arguments.length = rule.row.vars.length) :
    rule.row.instConclusion arguments =
      Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute (argumentAt arguments)
        (numbered rule.row.vars rule.row.conclusion) :=
  formed.conclusionSchema.instantiate_numbered formed.distinctNames arguments arity

/-- Source derivability checks argument types at every application. -/
inductive Derives (language : LanguageDef) (rules : List Rule)
    (context : List TypeExpr) (hypotheses : List Pattern) : Pattern → Prop where
  | hypothesis {pattern : Pattern} : pattern ∈ hypotheses →
      Derives language rules context hypotheses pattern
  | rule {rule : Rule} : rule ∈ rules → (arguments : List Pattern) →
      arguments.length = rule.row.vars.length →
      List.Forall₂ (fun argument type =>
        HasType language FreeTypeContext.empty context argument type)
        arguments rule.variableTypes →
      (∀ argument ∈ arguments,
        isMatchCorrectAux argument = true) →
      (∀ premise ∈ rule.row.instPremises arguments,
        Derives language rules context hypotheses premise) →
      Derives language rules context hypotheses (rule.row.instConclusion arguments)

example : checkSchema ["ph"] (.apply "imp" [.fvar "ph", .fvar "ph"]) = true := by
  simp [checkSchema, checkSchemas]
example : checkSchema ["ph"] (.apply "imp" [.fvar "ph", .fvar "ps"]) = false := by
  simp [checkSchema, checkSchemas]
example : checkSchema ["ph"] (.bvar 0) = false := by simp [checkSchema]

end Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
