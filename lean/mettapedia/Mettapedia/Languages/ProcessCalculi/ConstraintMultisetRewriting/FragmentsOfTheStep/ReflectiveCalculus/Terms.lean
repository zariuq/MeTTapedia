import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.IndexedOccurrences
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReaction

/-!
# The terms, the knowledge and the three rule schemas

The source is the reflective higher-order calculus already in the tree, read on closed processes
modulo its equations (`LanguageDefGSLT.rhoLanguageDefGSLT`): communication synchronizes up to name
equivalence, substitutes semantically (`semanticCommSubst`: a dropped received name becomes the
received process, quoted processes are sealed), and reduction is closed under the equations. This
module defines the step's side only; no process calculus is defined here.

* `Tm`: the terms of the step. A literal is a pattern of the source carrier; an unknown belongs to
  one rule instance and one port; `input` and `output` build prime processes around unknowns;
  `react body payload` is the communication contractum, read as the canonical form of the semantic
  substitution of the payload into the body; `split` and `rest` take a bag apart.
* `action`: two terms are equal in the knowledge when they mean the same pattern under every
  grounding of the unknowns. Substitution of unknowns preserves this by construction
  (`eval_bind`), so it is a substitution action, and solving an equation store is grounding it
  (`consistent_iff`).
* `comm`, `heat`, `clear`: the three schemas, opened at a natural number. `Rules` holds every
  instance and nothing else; it mentions no process (`rules_iff`, `schema_renaming`).

The continuation is an unknown whose meaning is an input body, open in the bound name: the input
former captures it (`Tm.eval` at `input`), so matching binds it exactly, and the bound name is
consumed by `react`, never by instantiation of the unknown.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus

/-! ## Terms -/

/-- The ports of the rule schemas. -/
inductive Port where
  | channel
  | body
  | payload
  | first
  | others
  deriving DecidableEq, Repr

/-- An unknown of the knowledge: the rule instance that opened it, and its port. -/
structure Unknown where
  index : Nat
  port : Port
  deriving DecidableEq, Repr

/-- Terms of the step. -/
inductive Tm where
  | lit (pattern : Pattern)
  | var (unknown : Unknown)
  | input (channel body : Tm)
  | output (channel payload : Tm)
  | react (body payload : Tm)
  | split (first others : Tm)
  | rest (others : Tm)
  deriving DecidableEq

/-- The null process of the source carrier. -/
def zeroPattern : Pattern := .apply "PZero" []

/-- The components of a parallel bag. -/
def bagElements : Pattern → Option (List Pattern)
  | .collection .hashBag elements none => some elements
  | _ => none

theorem bagElements_bag (elements : List Pattern) :
    bagElements (.collection .hashBag elements none) = some elements := rfl

theorem eq_of_bagElements : ∀ {pattern : Pattern} {elements : List Pattern},
    bagElements pattern = some elements → pattern = .collection .hashBag elements none
  | .collection .hashBag found none, elements, found_eq => by
      simp only [bagElements, Option.some.injEq] at found_eq
      rw [found_eq]
  | .collection .hashBag _ (some _), _, found_eq => by simp [bagElements] at found_eq
  | .collection .vec _ _, _, found_eq => by simp [bagElements] at found_eq
  | .collection .hashSet _ _, _, found_eq => by simp [bagElements] at found_eq
  | .bvar _, _, found_eq => by simp [bagElements] at found_eq
  | .fvar _, _, found_eq => by simp [bagElements] at found_eq
  | .apply _ _, _, found_eq => by simp [bagElements] at found_eq
  | .lambda _ _, _, found_eq => by simp [bagElements] at found_eq
  | .multiLambda _ _ _, _, found_eq => by simp [bagElements] at found_eq
  | .subst _ _, _, found_eq => by simp [bagElements] at found_eq

/-- A bag with a chosen first component; anything else is sent to a dangling index, which no
closed process is. -/
def consBag (first others : Pattern) : Pattern :=
  match bagElements others with
  | some elements => .collection .hashBag (first :: elements) none
  | none => .bvar 0

/-- The canonical form of the remaining components of a bag. -/
def restBag (others : Pattern) : Pattern :=
  match bagElements others with
  | some elements => Canonical.canonicalize (.collection .hashBag elements none)
  | none => others

theorem consBag_eq_bag {first others : Pattern} {elements : List Pattern}
    (same : consBag first others = .collection .hashBag elements none) :
    ∃ tail, others = .collection .hashBag tail none ∧ elements = first :: tail := by
  unfold consBag at same
  cases found : bagElements others with
  | none => rw [found] at same; cases same
  | some tail =>
      rw [found] at same
      simp only [Pattern.collection.injEq, true_and, and_true] at same
      exact ⟨tail, eq_of_bagElements found, same.symm⟩

theorem restBag_bag (elements : List Pattern) :
    restBag (.collection .hashBag elements none) =
      Canonical.canonicalize (.collection .hashBag elements none) := rfl

namespace Tm

/-- The meaning of a term under a grounding of its unknowns. -/
def eval (g : Unknown → Pattern) : Tm → Pattern
  | lit pattern => pattern
  | var unknown => g unknown
  | input channel body => CanonicalReaction.input (channel.eval g) (body.eval g)
  | output channel payload => CanonicalReaction.output (channel.eval g) (payload.eval g)
  | react body payload => Canonical.canonicalize (semanticCommSubst (body.eval g) (payload.eval g))
  | split first others => consBag (first.eval g) (others.eval g)
  | rest others => restBag (others.eval g)

/-- Substitution of unknowns by terms. -/
def bind (σ : Unknown → Tm) : Tm → Tm
  | lit pattern => lit pattern
  | var unknown => σ unknown
  | input channel body => input (channel.bind σ) (body.bind σ)
  | output channel payload => output (channel.bind σ) (payload.bind σ)
  | react body payload => react (body.bind σ) (payload.bind σ)
  | split first others => split (first.bind σ) (others.bind σ)
  | rest others => rest (others.bind σ)

theorem eval_bind (σ : Unknown → Tm) (g : Unknown → Pattern) :
    ∀ t : Tm, (t.bind σ).eval g = t.eval (fun unknown => (σ unknown).eval g)
  | lit _ => rfl
  | var _ => rfl
  | input channel body => by
      simp only [bind, eval, eval_bind σ g channel, eval_bind σ g body]
  | output channel payload => by
      simp only [bind, eval, eval_bind σ g channel, eval_bind σ g payload]
  | react body payload => by
      simp only [bind, eval, eval_bind σ g body, eval_bind σ g payload]
  | split first others => by
      simp only [bind, eval, eval_bind σ g first, eval_bind σ g others]
  | rest others => by
      simp only [bind, eval, eval_bind σ g others]

theorem bind_var : ∀ t : Tm, t.bind var = t
  | lit _ => rfl
  | var _ => rfl
  | input channel body => by simp only [bind, bind_var channel, bind_var body]
  | output channel payload => by simp only [bind, bind_var channel, bind_var payload]
  | react body payload => by simp only [bind, bind_var body, bind_var payload]
  | split first others => by simp only [bind, bind_var first, bind_var others]
  | rest others => by simp only [bind, bind_var others]

theorem bind_bind (outer inner : Unknown → Tm) :
    ∀ t : Tm, (t.bind inner).bind outer = t.bind (fun unknown => (inner unknown).bind outer)
  | lit _ => rfl
  | var _ => rfl
  | input channel body => by
      simp only [bind, bind_bind outer inner channel, bind_bind outer inner body]
  | output channel payload => by
      simp only [bind, bind_bind outer inner channel, bind_bind outer inner payload]
  | react body payload => by
      simp only [bind, bind_bind outer inner body, bind_bind outer inner payload]
  | split first others => by
      simp only [bind, bind_bind outer inner first, bind_bind outer inner others]
  | rest others => by
      simp only [bind, bind_bind outer inner others]

/-- The rule instances whose unknowns a term mentions. -/
def indices : Tm → Finset Nat
  | lit _ => ∅
  | var unknown => {unknown.index}
  | input channel body => channel.indices ∪ body.indices
  | output channel payload => channel.indices ∪ payload.indices
  | react body payload => body.indices ∪ payload.indices
  | split first others => first.indices ∪ others.indices
  | rest others => others.indices

/-- A term's meaning depends only on the unknowns it mentions. -/
theorem eval_congr {g g' : Unknown → Pattern} :
    ∀ t : Tm, (∀ unknown, unknown.index ∈ t.indices → g unknown = g' unknown) →
      t.eval g = t.eval g'
  | lit _, _ => rfl
  | var unknown, agree => agree unknown (by simp [indices])
  | input channel body, agree => by
      simp only [eval,
        eval_congr channel (fun u member => agree u (by simp [indices, member])),
        eval_congr body (fun u member => agree u (by simp [indices, member]))]
  | output channel payload, agree => by
      simp only [eval,
        eval_congr channel (fun u member => agree u (by simp [indices, member])),
        eval_congr payload (fun u member => agree u (by simp [indices, member]))]
  | react body payload, agree => by
      simp only [eval,
        eval_congr body (fun u member => agree u (by simp [indices, member])),
        eval_congr payload (fun u member => agree u (by simp [indices, member]))]
  | split first others, agree => by
      simp only [eval,
        eval_congr first (fun u member => agree u (by simp [indices, member])),
        eval_congr others (fun u member => agree u (by simp [indices, member]))]
  | rest others, agree => by
      simp only [eval, eval_congr others (fun u member => agree u (by simp [indices, member]))]

end Tm

/-! ## The knowledge -/

/-- Equality in the knowledge: the same meaning under every grounding. -/
def action : SubstitutionAction Tm (Unknown → Tm) where
  E left right := ∀ g, left.eval g = right.eval g
  equivalence := ⟨fun _ _ => rfl, fun same g => (same g).symm,
    fun first second g => (first g).trans (second g)⟩
  apply σ t := t.bind σ
  identity := Tm.var
  compose outer inner := fun unknown => (inner unknown).bind outer
  apply_identity := Tm.bind_var
  apply_compose outer inner t := (Tm.bind_bind outer inner t).symm
  preserves σ {left right} same := fun g => by
    rw [Tm.eval_bind, Tm.eval_bind]
    exact same _

/-- A grounding solves every equation of a store. -/
def Holds (g : Unknown → Pattern) (store : EquationStore Tm) : Prop :=
  ∀ equation ∈ store, equation.1.eval g = equation.2.eval g

@[simp] theorem holds_nil (g : Unknown → Pattern) : Holds g [] := by
  simp [Holds]

@[simp] theorem holds_cons (g : Unknown → Pattern) (equation : Equation Tm)
    (store : EquationStore Tm) :
    Holds g (equation :: store) ↔ equation.1.eval g = equation.2.eval g ∧ Holds g store := by
  simp [Holds]

@[simp] theorem holds_append (g : Unknown → Pattern) (first second : EquationStore Tm) :
    Holds g (first ++ second) ↔ Holds g first ∧ Holds g second := by
  simp only [Holds, List.mem_append]
  constructor
  · intro all
    exact ⟨fun e member => all e (.inl member), fun e member => all e (.inr member)⟩
  · rintro ⟨one, two⟩ e (member | member)
    · exact one e member
    · exact two e member

/-- Every solution of the knowledge yields a grounding that solves it. -/
theorem holds_of_models {σ : Unknown → Tm} {store : EquationStore Tm}
    (models : action.Models σ store) (g : Unknown → Pattern) :
    Holds (fun unknown => (σ unknown).eval g) store := by
  intro equation member
  have solved : (equation.1.bind σ).eval g = (equation.2.bind σ).eval g := models equation member g
  rwa [Tm.eval_bind, Tm.eval_bind] at solved

/-- Every grounding that solves the store is a solution, read as literals. -/
theorem models_of_holds {g : Unknown → Pattern} {store : EquationStore Tm}
    (holds : Holds g store) : action.Models (fun unknown => Tm.lit (g unknown)) store := by
  intro equation member g'
  change (equation.1.bind _).eval g' = (equation.2.bind _).eval g'
  rw [Tm.eval_bind, Tm.eval_bind]
  exact holds equation member

/-- **Solvability is grounding.** -/
theorem consistent_iff (store : EquationStore Tm) :
    action.Consistent store ↔ ∃ g, Holds g store := by
  constructor
  · rintro ⟨σ, models⟩
    exact ⟨_, holds_of_models models (fun _ => zeroPattern)⟩
  · rintro ⟨g, holds⟩
    exact ⟨_, models_of_holds holds⟩

/-- The rule instances an equation store mentions. -/
def storeIndices : EquationStore Tm → Finset Nat
  | [] => ∅
  | equation :: store => equation.1.indices ∪ equation.2.indices ∪ storeIndices store

theorem indices_subset_storeIndices : ∀ {store : EquationStore Tm} {equation : Equation Tm},
    equation ∈ store →
      equation.1.indices ⊆ storeIndices store ∧ equation.2.indices ⊆ storeIndices store
  | [], _, member => by simp at member
  | head :: store, equation, member => by
      rcases List.mem_cons.mp member with rfl | member
      · constructor <;> intro index found <;> simp [storeIndices, found]
      · obtain ⟨left, right⟩ := indices_subset_storeIndices member
        constructor <;> intro index found <;> simp only [storeIndices, Finset.mem_union]
        · exact .inr (left found)
        · exact .inr (right found)

/-- Ground one rule instance's unknowns, keeping every other unknown. -/
def extend (g : Unknown → Pattern) (index : Nat) (values : Port → Pattern) : Unknown → Pattern :=
  fun unknown => if unknown.index = index then values unknown.port else g unknown

theorem eval_extend_of_fresh (g : Unknown → Pattern) {index : Nat} (values : Port → Pattern)
    {t : Tm} (fresh : index ∉ t.indices) : t.eval (extend g index values) = t.eval g := by
  apply Tm.eval_congr
  intro unknown member
  have different : unknown.index ≠ index := fun same => fresh (same ▸ member)
  simp [extend, different]

theorem holds_extend_of_fresh {g : Unknown → Pattern} {store : EquationStore Tm}
    (holds : Holds g store) {index : Nat} (fresh : index ∉ storeIndices store)
    (values : Port → Pattern) : Holds (extend g index values) store := by
  intro equation member
  obtain ⟨left, right⟩ := indices_subset_storeIndices member
  rw [eval_extend_of_fresh g values (fun found => fresh (left found)),
    eval_extend_of_fresh g values (fun found => fresh (right found))]
  exact holds equation member

/-! ## The three schemas -/

/-- The unknown of rule instance `index` at `port`. -/
def unknown (index : Nat) (port : Port) : Tm := .var ⟨index, port⟩

@[simp] theorem eval_unknown_extend (g : Unknown → Pattern) (index : Nat)
    (values : Port → Pattern) (port : Port) :
    (unknown index port).eval (extend g index values) = values port := by
  simp [unknown, Tm.eval, extend]

/-- **Communication.** Take an input and an output whose channels are one unknown; make the
contractum of the continuation at the payload. -/
def comm (index : Nat) : RuleInstance Tm where
  take := [.input (unknown index .channel) (unknown index .body),
    .output (unknown index .channel) (unknown index .payload)]
  read := []
  tell := []
  checks := []
  produce := [.react (unknown index .body) (unknown index .payload)]

/-- **Heating.** Take a bag; make its first component and the rest. -/
def heat (index : Nat) : RuleInstance Tm where
  take := [.split (unknown index .first) (unknown index .others)]
  read := []
  tell := []
  checks := []
  produce := [unknown index .first, .rest (unknown index .others)]

/-- **Clearing.** Take the null process; make nothing. -/
def clear (_index : Nat) : RuleInstance Tm where
  take := [.lit zeroPattern]
  read := []
  tell := []
  checks := []
  produce := []

/-- The schemas: three, fixed before any process is given. -/
inductive Schema where
  | comm
  | heat
  | clear
  deriving DecidableEq, Repr

instance : Fintype Schema :=
  ⟨{.comm, .heat, .clear}, by intro schema; cases schema <;> simp⟩

/-- A schema opened at a rule-instance number. -/
def Schema.rule : Schema → Nat → RuleInstance Tm
  | .comm => ReflectiveCalculus.comm
  | .heat => ReflectiveCalculus.heat
  | .clear => ReflectiveCalculus.clear

/-- **The rule set**: the instances of the three schemas. -/
def Rules (rule : RuleInstance Tm) : Prop :=
  ∃ (schema : Schema) (index : Nat), rule = schema.rule index

theorem schema_count : Fintype.card Schema = 3 := by decide

theorem rules_iff (rule : RuleInstance Tm) :
    Rules rule ↔ ∃ index, rule = comm index ∨ rule = heat index ∨ rule = clear index := by
  constructor
  · rintro ⟨schema, index, rfl⟩
    cases schema
    · exact ⟨index, .inl rfl⟩
    · exact ⟨index, .inr (.inl rfl)⟩
    · exact ⟨index, .inr (.inr rfl)⟩
  · rintro ⟨index, rfl | rfl | rfl⟩
    · exact ⟨.comm, index, rfl⟩
    · exact ⟨.heat, index, rfl⟩
    · exact ⟨.clear, index, rfl⟩

/-- Renaming the unknowns of instance `0` to those of instance `index`. -/
def renameTo (index : Nat) (u : Unknown) : Tm := .var ⟨index, u.port⟩

/-- **Every instance is a renaming of one schema.** The rule set is three schemas and their
renamings; no rule depends on a process. -/
theorem schema_renaming (schema : Schema) (index : Nat) :
    schema.rule index = (schema.rule 0).map (Tm.bind (renameTo index)) := by
  cases schema <;> rfl

/-- Controls: the three schemas are different rules. -/
theorem schemas_differ (first second : Nat) :
    comm first ≠ heat second ∧ heat first ≠ clear second ∧ comm first ≠ clear second := by
  refine ⟨fun same => ?_, fun same => ?_, fun same => ?_⟩
  · have lengths := congrArg (fun rule : RuleInstance Tm => rule.take.length) same
    simp [comm, heat] at lengths
  · have lengths := congrArg (fun rule : RuleInstance Tm => rule.produce.length) same
    simp [heat, clear] at lengths
  · have lengths := congrArg (fun rule : RuleInstance Tm => rule.take.length) same
    simp [comm, clear] at lengths

/-! ## The step with this rule set -/

/-- Occurrences carry their immutable label. -/
abbrev Occ := IndexedOccurrences.Occurrence Tm

/-- Stores of the step. -/
abbrev Store := Configuration Tm Occ

/-- The label of an occurrence. -/
abbrev label : Occ → Tm := IndexedOccurrences.label

/-- One firing of the first-order step with the given rule instance. -/
def Fires (rule : RuleInstance Tm) (before after : Store) : Prop :=
  ConstraintMultisetRewriting.Step action label rule before after

/-- A communication firing. -/
def Communicates (before after : Store) : Prop := ∃ index, Fires (comm index) before after

/-- An administrative firing: heating or clearing. -/
def Administers (before after : Store) : Prop :=
  ∃ index, Fires (heat index) before after ∨ Fires (clear index) before after

/-- Every firing of the rule set is a communication or administrative. -/
theorem rules_fire_iff (before after : Store) :
    (∃ rule, Rules rule ∧ Fires rule before after) ↔
      Communicates before after ∨ Administers before after := by
  constructor
  · rintro ⟨rule, member, fires⟩
    obtain ⟨index, rfl | rfl | rfl⟩ := (rules_iff rule).mp member
    · exact .inl ⟨index, fires⟩
    · exact .inr ⟨index, .inl fires⟩
    · exact .inr ⟨index, .inr fires⟩
  · rintro (⟨index, fires⟩ | ⟨index, fires | fires⟩)
    · exact ⟨_, (rules_iff _).mpr ⟨index, .inl rfl⟩, fires⟩
    · exact ⟨_, (rules_iff _).mpr ⟨index, .inr (.inl rfl)⟩, fires⟩
    · exact ⟨_, (rules_iff _).mpr ⟨index, .inr (.inr rfl)⟩, fires⟩

#print axioms consistent_iff
#print axioms schema_renaming
#print axioms rules_fire_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus
