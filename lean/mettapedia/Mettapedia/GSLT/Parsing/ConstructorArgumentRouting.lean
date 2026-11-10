import Mettapedia.OSLF.Framework.GrammarDerives
import Mathlib.Data.List.Basic

/-! # Routing syntax occurrences to declared constructor parameters

Syntax occurrence order and declared parameter order need not agree. Routing
supports permutations and repeated syntax occurrences; repeated occurrences
of one parameter must agree. A missing value or wrong occurrence count is not
filled by a default. Binding-name interpretation is a separate layer; equality
here is equality of the supplied values, after any required normalization.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ConstructorArgumentRouting

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GrammarDerives

variable {α : Type} [DecidableEq α]

def valuesFor (name : String) : List (String × α) → List α
  | [] => []
  | (key, value) :: rest =>
      if key = name then value :: valuesFor name rest else valuesFor name rest

def agreed (name : String) (bindings : List (String × α)) : Option α :=
  match valuesFor name bindings with
  | [] => none
  | value :: rest => if rest.all (fun other => decide (other = value)) then some value else none

def ordered (names : List String) (bindings : List (String × α)) : Option (List α) :=
  match names with
  | [] => some []
  | name :: rest => do return (← agreed name bindings) :: (← ordered rest bindings)

def route (parameters occurrences : List String) (values : List α) : Option (List α) :=
  if occurrences.length = values.length then ordered parameters (occurrences.zip values) else none

omit [DecidableEq α] in
theorem valuesFor_zip_absent {name : String} {names : List String}
    (absent : name ∉ names) (values : List α) : valuesFor name (names.zip values) = [] := by
  induction names generalizing values with
  | nil => rfl
  | cons first rest ih =>
      have different : first ≠ name := fun same => absent (same ▸ List.mem_cons_self)
      have tail : name ∉ rest := fun member => absent (List.mem_cons_of_mem _ member)
      cases values with
      | nil => rfl
      | cons value values => simp only [List.zip_cons_cons, valuesFor, if_neg different, ih tail]

theorem ordered_ignore {key : String} {names : List String} (absent : key ∉ names)
    (value : α) (bindings : List (String × α)) :
    ordered names ((key, value) :: bindings) = ordered names bindings := by
  induction names with
  | nil => rfl
  | cons first rest ih =>
      have different : key ≠ first := fun same => absent (same ▸ List.mem_cons_self)
      have tail : key ∉ rest := fun member => absent (List.mem_cons_of_mem _ member)
      simp only [ordered, agreed, valuesFor, if_neg different, ih tail]

theorem ordered_zip {names : List String} (unique : names.Nodup) (values : List α)
    (lengths : names.length = values.length) : ordered names (names.zip values) = some values := by
  induction names generalizing values with
  | nil =>
      cases values with
      | nil => rfl
      | cons _ _ => simp at lengths
  | cons name names ih =>
      cases values with
      | nil => simp at lengths
      | cons value values =>
          have nodup := List.nodup_cons.mp unique
          have tailLength : names.length = values.length := Nat.succ.inj lengths
          rw [List.zip_cons_cons, ordered]
          have head : agreed name ((name, value) :: names.zip values) = some value := by
            simp [agreed, valuesFor, valuesFor_zip_absent nodup.1 values]
          rw [head, ordered_ignore nodup.1, ih nodup.2 values tailLength]
          rfl

/-- Direct layouts need no routing pass. The hypotheses are about the
representation, not global restrictions on admissible syntax layouts. -/
theorem route_direct {names : List String} (unique : names.Nodup) (values : List α)
    (lengths : names.length = values.length) : route names names values = some values := by
  rw [route, if_pos lengths]
  exact ordered_zip unique values lengths

def occurrenceNames : List SyntaxItem → List String
  | [] => []
  | .nonTerminal name :: rest => name :: occurrenceNames rest
  | _ :: rest => occurrenceNames rest

def DirectOrder (rule : GrammarRule) : Prop :=
  occurrenceNames rule.syntaxPattern = rule.params.map TermParam.bodyName ∧
    (rule.params.map TermParam.bodyName).Nodup

instance (rule : GrammarRule) : Decidable (DirectOrder rule) :=
  inferInstanceAs (Decidable (_ ∧ _))

def routeRule (rule : GrammarRule) (children : List α) : Option (List α) :=
  route (rule.params.map TermParam.bodyName) (occurrenceNames rule.syntaxPattern) children

theorem routeRule_direct {rule : GrammarRule} (direct : DirectOrder rule) (children : List α)
    (lengths : (occurrenceNames rule.syntaxPattern).length = children.length) :
    routeRule rule children = some children := by
  unfold routeRule
  rw [direct.1]
  exact route_direct direct.2 children (direct.1 ▸ lengths)

/-- The declared AST is related to the syntax-order AST by actual routing at
all nodes. Source trees and their spans may be retained separately. -/
inductive Routed (language : LanguageDef) : Pattern → Pattern → Prop where
  | node (rule : GrammarRule) (member : rule ∈ language.terms)
      (syntaxChildren children arguments : List Pattern)
      (subtrees : List.Forall₂ (Routed language) syntaxChildren children)
      (routed : routeRule rule children = some arguments) :
      Routed language (.apply rule.label syntaxChildren) (.apply rule.label arguments)

theorem derives_routed_self {language : LanguageDef}
    (direct : ∀ rule ∈ language.terms, DirectOrder rule)
    {sort : String} {tokens : List String} {tree : Pattern}
    (derived : Derives language sort tokens tree) : Routed language tree tree := by
  induction derived using Derives.rec
      (motive_2 := fun _ items _ children _ =>
        List.Forall₂ (Routed language) children children ∧
          (occurrenceNames items).length = children.length) with
  | rule rule member _ _ _ children _ ih =>
      exact .node rule member children children children ih.1
        (routeRule_direct (direct rule member) children ih.2)
  | nil => exact ⟨.nil, rfl⟩
  | terminal _ _ _ _ _ _ ih => exact ih
  | nonTerminal _ _ _ _ _ _ _ _ _ _ _ ihHead ihRest =>
      exact ⟨.cons ihHead ihRest.1, congrArg Nat.succ ihRest.2⟩

namespace Controls

theorem same_sort_permutation : route ["left", "right"] ["right", "left"] ([2, 1] : List Nat) =
    some [1, 2] := by decide +kernel

theorem repeated_agreement : route ["x"] ["x", "x"] ([7, 7] : List Nat) = some [7] := by decide +kernel

theorem repeated_disagreement : route ["x"] ["x", "x"] ([7, 8] : List Nat) = none := by decide +kernel

theorem missing_parameter : route ["x", "y"] ["x"] ([7] : List Nat) = none := by decide +kernel

theorem wrong_occurrence_count : route ["x"] ["x", "x"] ([7] : List Nat) = none := by decide +kernel

end Controls

#print axioms route_direct
#print axioms derives_routed_self

end Mettapedia.GSLT.Parsing.ConstructorArgumentRouting
