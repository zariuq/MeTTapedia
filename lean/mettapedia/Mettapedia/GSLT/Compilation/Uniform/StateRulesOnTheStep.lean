import Mettapedia.GSLT.Compilation.RootRewritesOnTheStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.GraphRelations

/-!
# Tagged state terms and one-term rules on Transform

A rule of this form replaces one state term. Its conditions can inspect
named primitive relations, but matching and all unchanged fields are
part of the rule itself. The theorem for a singleton multiset accounts
for the whole firing, in both directions.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.Uniform.StateRulesOnTheStep

open Mettapedia.GSLT.Compilation.RootRewritesOnTheStep (appTerm symTerm inst_appTerm inst_symTerm)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax.Presentation.Schematic (Tm inst equationsOf written)
open RuleSyntax.Machines (rowRule row_of_singleton unknowns mem_unknowns vars_of_mem_unknowns)
open RuleSyntax.ComputedConditions (Condition RuleWithCondition Relations RelationStep)

def fields (items : List Expr) : Expr := items.foldr Expr.app (.sym 0)

theorem fields_append (prefixFields tailFields : List Expr) :
    fields (prefixFields ++ tailFields) = prefixFields.foldr Expr.app (fields tailFields) := by
  simp only [fields, List.foldr_append]

theorem fields_injective : Function.Injective fields := by
  intro first
  induction first with
  | nil => intro other equal; cases other <;> simp_all [fields]
  | cons item rest ih =>
    intro other equal
    cases other with
    | nil => simp [fields] at equal
    | cons next remaining =>
      have same := Expr.app.inj (show Expr.app item (fields rest) = Expr.app next (fields remaining) from equal)
      exact congrArg₂ List.cons same.1 (ih same.2)

def spine {A : Type} (encode : A → Expr) (entries : List A) : Expr := fields (entries.map encode)

@[simp] theorem spine_nil {A : Type} (encode : A → Expr) : spine encode [] = .sym 0 := rfl

@[simp] theorem spine_cons {A : Type} (encode : A → Expr) (first : A) (rest : List A) :
    spine encode (first :: rest) = .app (encode first) (spine encode rest) := rfl

theorem spine_injective {A : Type} {encode : A → Expr} (separates : Function.Injective encode) :
    Function.Injective (spine encode) :=
  fun _ _ eq => (List.map_injective_iff.mpr separates) (fields_injective eq)

def packet (tag : Nat) (items : List Expr) : Expr := .app (.sym tag) (fields items)

def pattern (tag : Nat) (items : List Tm) : Tm :=
  appTerm (symTerm tag) (items.foldr appTerm (symTerm 0))

theorem packet_eq_iff (tag other : Nat) (items more : List Expr) :
    packet tag items = packet other more ↔ tag = other ∧ items = more := by
  simp only [packet, Expr.app.injEq, Expr.sym.injEq, fields_injective.eq_iff]

theorem instantiate_fields (values : Nat → Expr) (items : List Tm) :
    inst values (items.foldr appTerm (symTerm 0)) = fields (items.map (inst values)) := by
  induction items with
  | nil => rfl
  | cons head tail ih => simp [List.foldr_cons, fields] at ih ⊢; exact ih

theorem instantiate_packet (values : Nat → Expr) (tag : Nat) (items : List Tm) :
    inst values (pattern tag items) = packet tag (items.map (inst values)) := by
  simp [pattern, packet, instantiate_fields]

theorem instance_var (values : Nat → Expr) (name : Nat) : inst values (.var name) = values name := rfl

def rule (taken made : Tm) (asks : List (Condition Nat Tm)) : RuleWithCondition Nat Tm :=
  ⟨rowRule taken made, asks⟩

theorem restricted (taken made : Tm) (asks : List (Condition Nat Tm))
    (sources : ∀ x ∈ unknowns made,
      x ∈ unknowns taken ∨ ∃ ask ∈ asks, x ∈ unknowns ask.value) :
    (rule taken made asks).RangeRestrictedWith := by
  intro term member x free
  obtain rfl : term = made := by simpa [rule, rowRule, written] using member
  rcases sources x (mem_unknowns _ free) with input | ⟨ask, part, computed⟩
  · exact Or.inl ⟨taken, List.mem_cons_self, vars_of_mem_unknowns _ input⟩
  · exact Or.inr ⟨ask, part, vars_of_mem_unknowns _ computed⟩

theorem unconditional_restricted (taken made : Tm) (sources : unknowns made ⊆ unknowns taken) :
    (rule taken made []).RangeRestrictedWith :=
  restricted taken made [] (fun _ present => Or.inl (sources present))

theorem instance_iff (ops : Relations) (taken made : Tm) (asks : List (Condition Nat Tm))
    (before : Expr) (after : Multiset Expr) :
    RelationStep ops (rule taken made asks) {before} after ↔
      ∃ values : Nat → Expr, inst values taken = before ∧
        (∀ ask ∈ asks, ops ask.name (ask.arguments.map (inst values)) (inst values ask.value)) ∧
        after = {inst values made} := by
  constructor
  · rintro ⟨values, rest, split, _, _, conditions, out⟩
    obtain ⟨matched, rfl⟩ := row_of_singleton split
    exact ⟨values, matched, conditions, by simpa only [rule, rowRule, List.map_singleton,
      add_zero, Multiset.coe_singleton] using out⟩
  · rintro ⟨values, matched, conditions, rfl⟩
    exact ⟨values, 0, by simp [rule, rowRule, matched], by simp [rule, rowRule],
      by simp [rule, rowRule, equationsOf], conditions, by simp [rule, rowRule]⟩

theorem input_tag {ops : Relations} {writtenTag seenTag : Nat} {slots : List Tm} {made : Tm}
    {asks : List (Condition Nat Tm)} {items : List Expr} {after : Multiset Expr}
    (step : RelationStep ops (rule (pattern writtenTag slots) made asks) {packet seenTag items} after) :
    writtenTag = seenTag := by
  obtain ⟨values, enters, _, _⟩ := (instance_iff _ _ _ _ _ _).mp step
  rw [instantiate_packet] at enters
  exact ((packet_eq_iff _ _ _ _).mp enters).1

/-- A rule cannot detect any change outside the relations it asks. This
lets independent primitive interpretations share one program. -/
theorem operations_iff (first second : Relations) (r : RuleWithCondition Nat Tm)
    (same : ∀ ask ∈ r.conditions, ∀ inputs result, first ask.name inputs result ↔ second ask.name inputs result)
    (before after : Multiset Expr) : RelationStep first r before after ↔ RelationStep second r before after := by
  constructor
  · rintro ⟨values, rest, taken, reads, equations, conditions, made⟩
    exact ⟨values, rest, taken, reads, equations,
      fun ask member => (same ask member _ _).mp (conditions ask member), made⟩
  · rintro ⟨values, rest, taken, reads, equations, conditions, made⟩
    exact ⟨values, rest, taken, reads, equations,
      fun ask member => (same ask member _ _).mpr (conditions ask member), made⟩

end Mettapedia.GSLT.Compilation.Uniform.StateRulesOnTheStep
