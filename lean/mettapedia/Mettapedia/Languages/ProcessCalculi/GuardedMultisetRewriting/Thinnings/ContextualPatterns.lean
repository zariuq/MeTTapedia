import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Patterns
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Step
import Mettapedia.GSLT.LanguageDef.ScopedABTApplication

/-!
# Contextual occurrences in the common guarded rewriting term layer

The syntax remains `TreePat`. Each metavariable occurrence carries its parameter
scope and explicit argument spine. Assignments store bodies in that parameter
scope; the existing simultaneous graft places them at their occurrences.
The outer wrapper retains the scope of the complete pattern.

This layer is used by the ordinary `GuardedMultisetRewriting.Step`. Scope refusal is part
of instantiation, including when all variables have assigned values. There is
no proof evaluator or guest-specific term constructor.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.ScopedApplication
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

variable {Head V : Type}

/-- Metadata at one occurrence of an existing pattern variable. -/
structure Occurrence (Head V : Type) where
  name : V
  arity : Nat
  arguments : List (Term Head)
  deriving DecidableEq

/-- A view of the existing pattern tree with its enclosing context retained. -/
structure Pattern (Head V : Type) where
  scope : Nat
  tree : TreePat Head (Occurrence Head V)

namespace Pattern

variable [DecidableEq Head] [DecidableEq V]

def vars (p : Pattern Head V) : Finset V := p.tree.vars.image Occurrence.name

/-- Assignments are bodies over formal parameters, not unscoped textual replacements. -/
def atOccurrence (σ : Subst V (Term Head)) (occurrence : Occurrence Head V) : Option (Term Head) :=
  (σ occurrence.name).bind (graft occurrence.arity occurrence.arguments)

def inst (σ : Subst V (Term Head)) (p : Pattern Head V) : Option (Term Head) := do
  let result ← p.tree.inst (atOccurrence σ)
  if Term.supportedAt p.scope result then some result else none

omit [DecidableEq Head] [DecidableEq V] in
theorem inst_iff (σ : Subst V (Term Head)) (p : Pattern Head V) (result : Term Head) :
    p.inst σ = some result ↔
      p.tree.inst (atOccurrence σ) = some result ∧ Term.supportedAt p.scope result = true := by
  unfold inst
  cases raw : p.tree.inst (atOccurrence σ) with
  | none => simp
  | some t =>
    change (if Term.supportedAt p.scope t = true then some t else none) = some result ↔
      some t = some result ∧ Term.supportedAt p.scope result = true
    by_cases scopedResult : Term.supportedAt p.scope t = true
    · simp only [if_pos scopedResult, Option.some.injEq]
      exact ⟨fun same => ⟨same, same ▸ scopedResult⟩, And.left⟩
    · simp only [if_neg scopedResult, reduceCtorEq, Option.some.injEq]
      exact ⟨False.elim, fun ⟨same, valid⟩ => scopedResult (same ▸ valid)⟩

omit [DecidableEq Head] [DecidableEq V] in
theorem inst_supported {σ : Subst V (Term Head)} {p : Pattern Head V} {result : Term Head}
    (applied : p.inst σ = some result) : Term.supportedAt p.scope result = true :=
  ((inst_iff σ p result).mp applied).2

omit [DecidableEq Head] [DecidableEq V] in
theorem atOccurrence_bound {σ : Subst V (Term Head)} {occurrence : Occurrence Head V}
    (applied : (atOccurrence σ occurrence).isSome) : (σ occurrence.name).isSome := by
  cases assigned : σ occurrence.name <;> simp_all [atOccurrence]

theorem inst_bound (σ : Subst V (Term Head)) (p : Pattern Head V)
    (applied : (p.inst σ).isSome) : ∀ v ∈ p.vars, (σ v).isSome := by
  obtain ⟨result, success⟩ := Option.isSome_iff_exists.mp applied
  have raw := ((inst_iff σ p result).mp success).1
  intro v member
  obtain ⟨occurrence, occurs, rfl⟩ := Finset.mem_image.mp member
  apply atOccurrence_bound (occurrence := occurrence)
  exact (TreePat.inst_isSome (atOccurrence σ) p.tree).mp (by rw [raw]; rfl) occurrence occurs

theorem inst_local (σ τ : Subst V (Term Head)) (p : Pattern Head V)
    (same : ∀ v ∈ p.vars, σ v = τ v) : p.inst σ = p.inst τ := by
  have raw : p.tree.inst (atOccurrence σ) = p.tree.inst (atOccurrence τ) := by
    apply TreePat.inst_local
    intro occurrence member
    unfold atOccurrence
    rw [same occurrence.name (Finset.mem_image.mpr ⟨occurrence, member, rfl⟩)]
  simp only [inst, raw]

/-- Exact contextual assignment admissibility, independent of the outer scope check. -/
def AssignmentsScoped (σ : Subst V (Term Head)) (p : Pattern Head V) : Prop :=
  ∀ occurrence ∈ p.tree.vars, ∃ body,
    σ occurrence.name = some body ∧ occurrence.arguments.length = occurrence.arity ∧
      Term.supportedAt occurrence.arity body = true

theorem raw_defined_iff (σ : Subst V (Term Head)) (p : Pattern Head V) :
    (p.tree.inst (atOccurrence σ)).isSome ↔ p.AssignmentsScoped σ := by
  rw [TreePat.inst_isSome]
  constructor
  · intro defined occurrence member
    have bound := atOccurrence_bound (defined occurrence member)
    obtain ⟨body, assigned⟩ := Option.isSome_iff_exists.mp bound
    refine ⟨body, assigned, ?_⟩
    have applied := defined occurrence member
    simp only [atOccurrence, assigned, Option.bind_some, graft] at applied
    split at applied
    · assumption
    · cases applied
  · intro qualified occurrence member
    obtain ⟨body, assigned, count, bodyScoped⟩ := qualified occurrence member
    simp [atOccurrence, assigned, graft, count, bodyScoped]

theorem inst_assignments_scoped {σ : Subst V (Term Head)} {p : Pattern Head V}
    {result : Term Head} (applied : p.inst σ = some result) : p.AssignmentsScoped σ := by
  apply (raw_defined_iff σ p).mp
  rw [((inst_iff σ p result).mp applied).1]
  rfl

omit [DecidableEq Head] [DecidableEq V] in
/-- Changing an occurrence's actual arguments uses the existing capture-free graft law. -/
theorem occurrence_substitution (σ : Subst V (Term Head)) (occurrence : Occurrence Head V)
    (τ : Nat → Term Head) :
    atOccurrence σ { occurrence with arguments := occurrence.arguments.map (Term.substituteMany τ) } =
      (atOccurrence σ occurrence).map (Term.substituteMany τ) := by
  cases assigned : σ occurrence.name with
  | none => simp [atOccurrence, assigned]
  | some body =>
    simp only [atOccurrence, assigned, Option.bind_some]
    by_cases count : occurrence.arguments.length = occurrence.arity
    · by_cases bodyScoped : Term.supportedAt occurrence.arity body = true
      · exact graft_substitution occurrence.arguments body count bodyScoped τ
      · simp [graft, bodyScoped]
    · simp [graft, count]

end Pattern

variable [DecidableEq Head] [DecidableEq V]

/-- Contextual patterns participate in the same term-layer and step interfaces. -/
def layer : TermLayer V (Term Head) (Pattern Head V) where
  E := (· = ·)
  equivalence := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
  vars := Pattern.vars
  inst σ p := p.inst σ
  inst_bound := Pattern.inst_bound
  inst_local := Pattern.inst_local
  inst_congr σ τ p related := by
    have same : ∀ v ∈ p.vars, σ v = τ v := by
      intro v member
      rcases optionRel_iff.mp (related v member) with ⟨a, b⟩ | ⟨s, t, a, b, e⟩
      · rw [a, b]
      · rw [a, b, show s = t from e]
    rw [Pattern.inst_local σ τ p same]
    cases p.inst τ with
    | none => exact .none
    | some t => exact .some rfl

theorem solves_iff (σ : Subst V (Term Head)) (p : Pattern Head V) (t : Term Head) :
    (layer (Head := Head) (V := V)).Solves σ p t ↔ p.inst σ = some t := by
  constructor
  · rintro ⟨u, applied, same⟩
    exact (show p.inst σ = some u from applied).trans (congrArg some same)
  · intro applied
    exact ⟨t, applied, rfl⟩

/-- A matched core premise retains both its ambient scope and every hole's interface. -/
theorem solved_supported {σ : Subst V (Term Head)} {p : Pattern Head V} {t : Term Head}
    (solved : (layer (Head := Head) (V := V)).Solves σ p t) :
    Term.supportedAt p.scope t = true ∧ p.AssignmentsScoped σ := by
  have applied := (solves_iff σ p t).mp solved
  exact ⟨Pattern.inst_supported applied, Pattern.inst_assignments_scoped applied⟩

namespace Controls

def hole (scope arity : Nat) (arguments : List (Term Nat)) : Pattern Nat Nat :=
  ⟨scope, .mvar ⟨0, arity, arguments⟩⟩

def assignment : Subst Nat (Term Nat) := fun v => if v = 0 then some (.idx 0) else none
def escaped : Subst Nat (Term Nat) := fun v => if v = 0 then some (.idx 1) else none
def seven : Term Nat := .node 7 .nil

theorem permitted_body_applies : (hole 1 1 [.idx 0]).inst assignment = some (.idx 0) := by decide
theorem undeclared_body_refused : (hole 1 1 [.idx 0]).inst escaped = none := by decide
theorem outer_scope_checked : (hole 0 1 [.idx 0]).inst assignment = none := by decide
theorem compound_application : (hole 0 1 [seven]).inst assignment = some seven := by decide

/-- Scope checks are substantive even when the single schematic variable is bound. -/
theorem contextual_layer_not_total : ¬(layer (Head := Nat) (V := Nat)).Total := by
  intro total
  have refused := total escaped (hole 1 1 [.idx 0]) (by
    intro v member
    have same : v = 0 := by simpa [layer, Pattern.vars, hole, TreePat.vars] using member
    subst v
    rfl)
  change ((hole 1 1 [.idx 0]).inst escaped).isSome = true at refused
  rw [undeclared_body_refused] at refused
  cases refused

def specialize : Rule Nat (Term Nat) (Pattern Nat Nat) where
  take := []
  read := [hole 1 1 [.idx 0]]
  checks := []
  produce := [hole 0 1 [seven]]

/-- The ordinary guarded rewriting step reads an open contextual value and makes its closed application. -/
theorem specialize_step :
    Step layer specialize {Term.idx 0} {Term.idx 0, seven} := by
  refine ⟨assignment, 0, 0, {Term.idx 0}, [seven], ?_, ?_, ?_, by simp, ?_, ?_, by simp⟩
  · intro v outside
    have neq : v ≠ 0 := by
      intro equal
      subst v
      exact outside (hole 1 1 [.idx 0]) (by simp [specialize]) (by
        simp [layer, Pattern.vars, hole, TreePat.vars])
    simp [assignment, neq]
  · exact ⟨[], .nil, rfl⟩
  · refine ⟨[Term.idx 0], .cons ?_ .nil, le_rfl, ?_⟩
    · exact (solves_iff _ _ _).mpr permitted_body_applies
    · intro t member
      simpa using member
  · intro check member
    simp [specialize] at member
  · change instTemplate layer assignment [hole 0 1 [seven]] = some [seven]
    simp [instTemplate, layer, compound_application]

end Controls

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns
