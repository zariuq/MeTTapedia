import Mettapedia.Machines.TIsa.Derivation.StepAdequacy
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreSyntax
import Mettapedia.Logic.LP.Matching

/-!
# First-order terms: the existing matcher and its laws

The evaluator's matcher for the step theory's first-order profile (`FirstOrder.action`, terms of an
LP signature with their substitutions). Patterns are matched against ground terms by the existing
binding collector (`collectBindings`), with its repeated-variable check (`bindingsConsistent?`);
bindings are lists of variables with ground terms.

* `semantics`: the laws of `Derivation.Semantics`, from the collector's soundness and completeness
  (`collectBindingsList_sound`, `collectBindingsList_complete`). Through it, every theorem of
  `Derivation.StepAdequacy` holds for first-order rules.
* `rangeRestricted_of_scoped`: a rule whose tells, checks, collect patterns and produced terms
  mention only variables of its premises is range restricted.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.FirstOrderTerms

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

variable {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols]

instance groundTermDecidableEq : DecidableEq (GroundTerm σ) := GroundTerm.decEq

/-- Bindings: variables with ground terms. -/
abbrev Bindings (σ : LPSignature) := List (σ.vars × GroundTerm σ)

/-- **Matching under bindings**: collect the pattern's bindings, and keep them when every variable
is bound to one term. -/
def extend (θ : Bindings σ) (p : Term σ) (v : GroundTerm σ) : Option (Bindings σ) :=
  match collectBindings p v with
  | none => none
  | some new => if bindingsConsistent? (θ ++ new) then some (θ ++ new) else none

/-- The ground term of a variable. -/
def lookup (θ : Bindings σ) (x : σ.vars) : Option (GroundTerm σ) :=
  (θ.find? (fun b => b.1 == x)).map Prod.snd

/-- **Instantiation under bindings**, when every variable is bound. -/
def instantiate (θ : Bindings σ) : Term σ → Option (GroundTerm σ)
  | .var x => lookup θ x
  | .const c => some (.const c)
  | .app f ts =>
      if defined : (List.finRange (σ.functionArity f)).all (fun i => (instantiate θ (ts i)).isSome) then
        some (.app f fun i => (instantiate θ (ts i)).get
          ((List.all_eq_true.mp defined) i (List.mem_finRange i)))
      else none

/-- **The first-order matcher.** -/
def matcher : Matcher (Term σ) (GroundTerm σ) (Bindings σ) := ⟨[], extend, instantiate⟩

/-- Bindings denote the substitutions agreeing with them. -/
def Denotes (θ : Bindings σ) (τ : Subst σ) : Prop := ∀ x g, (x, g) ∈ θ → τ x = g.toTerm

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem lookup_some {θ : Bindings σ} {x : σ.vars} {g : GroundTerm σ} (found : lookup θ x = some g) :
    (x, g) ∈ θ := by
  unfold lookup at found
  obtain ⟨b, located, rfl⟩ := Option.map_eq_some_iff.mp found
  have same : b.1 = x := by simpa using List.find?_some located
  have inside := List.mem_of_find?_eq_some located
  rw [← same]
  exact inside

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem lookup_isSome {θ : Bindings σ} {x : σ.vars} (bound : ∃ g, (x, g) ∈ θ) :
    (lookup θ x).isSome := by
  obtain ⟨g, inside⟩ := bound
  unfold lookup
  cases located : θ.find? (fun b => b.1 == x) with
  | none =>
      have absent := List.find?_eq_none.mp located (x, g) inside
      simp at absent
  | some b => rfl

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem consistent_of_denotes {θ : Bindings σ} {τ : Subst σ} (denoted : Denotes θ τ) :
    BindingsConsistent θ := fun x left right inLeft inRight =>
  GroundTerm.toTerm_injective ((denoted x left inLeft).symm.trans (denoted x right inRight))

theorem extend_some {θ θ' : Bindings σ} {p : Term σ} {v : GroundTerm σ}
    (extended : extend θ p v = some θ') :
    ∃ new, collectBindings p v = some new ∧ BindingsConsistent (θ ++ new) ∧ θ' = θ ++ new := by
  unfold extend at extended
  cases collected : collectBindings p v with
  | none => simp [collected] at extended
  | some new =>
      rw [collected] at extended
      simp only at extended
      split_ifs at extended with consistent
      · cases extended
        exact ⟨new, rfl, (bindingsConsistent?_eq_true _).mp consistent, rfl⟩

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem instantiate_sound (θ : Bindings σ) (τ : Subst σ) (denoted : Denotes θ τ) :
    ∀ (t : Term σ) (g : GroundTerm σ), instantiate θ t = some g → τ.applyTerm t = g.toTerm
  | .var x, g, inst => denoted x g (lookup_some inst)
  | .const c, g, inst => by
      simp only [instantiate, Option.some.injEq] at inst
      subst inst
      rfl
  | .app f ts, g, inst => by
      simp only [instantiate] at inst
      split_ifs at inst with defined
      cases inst
      simp only [Subst.applyTerm, GroundTerm.toTerm, Term.app.injEq, heq_eq_eq, true_and]
      funext i
      exact instantiate_sound θ τ denoted (ts i) _ (Option.some_get _).symm

/-- **The laws of the first-order matcher** over the step theory's first-order action. -/
def semantics : Semantics (FirstOrder.action σ) (matcher (σ := σ)) where
  embed := GroundTerm.toTerm
  reflects a b := ⟨fun same => GroundTerm.toTerm_injective same, fun same => same ▸ rfl⟩
  fixed τ a := FirstOrder.ground_fixed τ a.toTerm (GroundTerm.toTerm_isGround a)
  Denotes := Denotes
  denotes_empty τ := by
    intro x g inside
    cases inside
  extend_iff θ p a τ := by
    change (∃ θ', extend θ p a = some θ' ∧ Denotes θ' τ) ↔ Denotes θ τ ∧ τ.applyTerm p = a.toTerm
    constructor
    · rintro ⟨θ', extended, denoted⟩
      obtain ⟨new, collected, _, rfl⟩ := extend_some extended
      refine ⟨fun x g inside => denoted x g (List.mem_append_left _ inside), ?_⟩
      have sound := collectBindingsList_sound [p] [a] new collected τ
        (fun x g inside => denoted x g (List.mem_append_right _ inside))
      simpa using sound
    · rintro ⟨denoted, solved⟩
      obtain ⟨new, collected, agree⟩ := collectBindingsList_complete [p] [a] τ (by simp [solved])
      have both : Denotes (θ ++ new) τ := by
        intro x g inside
        rcases List.mem_append.mp inside with old | fresh
        · exact denoted x g old
        · exact agree x g fresh
      refine ⟨θ ++ new, ?_, both⟩
      have checked := (bindingsConsistent?_eq_true (θ ++ new)).mpr (consistent_of_denotes both)
      simp [extend, collectBindings, collected, checked]
  extend_inhabited θ p a θ' extended := by
    obtain ⟨new, _, consistent, rfl⟩ := extend_some extended
    exact ⟨bindingsToSubst (θ ++ new), fun x g inside => bindingsToSubst_mem _ x g inside consistent⟩
  instantiate_sound θ t a τ inst denoted := instantiate_sound θ τ denoted t a inst

/-! ## Range restriction from scoped variables -/

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem instantiate_isSome (θ : Bindings σ) :
    ∀ t : Term σ, (∀ x ∈ t.freeVars, ∃ g, (x, g) ∈ θ) → (instantiate θ t).isSome
  | .var x, bound => lookup_isSome (bound x (by simp [Term.freeVars]))
  | .const c, _ => rfl
  | .app f ts, bound => by
      have each : ∀ i, (instantiate θ (ts i)).isSome := fun i =>
        instantiate_isSome θ (ts i) fun x inside =>
          bound x (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, inside⟩)
      have defined : (List.finRange (σ.functionArity f)).all (fun i => (instantiate θ (ts i)).isSome) :=
        List.all_eq_true.mpr fun i _ => each i
      simp [instantiate, defined]

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem ground_ne_var (g : GroundTerm σ) (x : σ.vars) : g.toTerm ≠ Term.var x := by
  cases g <;> simp [GroundTerm.toTerm]

/-- **An accepted match binds every variable of its pattern.** -/
theorem extend_binds {θ θ' : Bindings σ} {p : Term σ} {v : GroundTerm σ}
    (extended : extend θ p v = some θ') : ∀ x ∈ p.freeVars, ∃ g, (x, g) ∈ θ' := by
  intro x mentions
  by_contra unbound
  obtain ⟨new, collected, consistent, rfl⟩ := extend_some extended
  let τ₁ := bindingsToSubst (θ ++ new)
  have agree₁ : ∀ y h, (y, h) ∈ θ ++ new → τ₁ y = h.toTerm :=
    fun y h inside => bindingsToSubst_mem _ y h inside consistent
  let other : Term σ := if τ₁ x = Term.var x then v.toTerm else Term.var x
  have differs : other ≠ τ₁ x := by
    by_cases identity : τ₁ x = Term.var x
    · simp only [other, identity, if_true]
      exact ground_ne_var v x
    · simp only [other, identity, if_false]
      exact fun same => identity same.symm
  let τ₂ : Subst σ := fun y => if y = x then other else τ₁ y
  have agree₂ : ∀ y h, (y, h) ∈ θ ++ new → τ₂ y = h.toTerm := by
    intro y h inside
    by_cases same : y = x
    · subst same
      exact absurd ⟨h, inside⟩ unbound
    · simp only [τ₂, same, if_false]
      exact agree₁ y h inside
  have sound₁ := collectBindingsList_sound [p] [v] new collected τ₁
    (fun y h inside => agree₁ y h (List.mem_append_right _ inside))
  have sound₂ := collectBindingsList_sound [p] [v] new collected τ₂
    (fun y h inside => agree₂ y h (List.mem_append_right _ inside))
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at sound₁ sound₂
  have same := RuleSyntax.SetStoreSyntax.agree_of_apply_eq τ₁ τ₂ p (sound₁.trans sound₂.symm) x mentions
  simp only [τ₂, if_true] at same
  exact differs same.symm

/-- Accepted premises keep earlier bindings and bind every variable of their patterns. -/
theorem attemptAll_binds (role : Role) :
    ∀ (ps : List (Term σ)) (m m' : Match (GroundTerm σ) (Bindings σ)) (xs : List (ℕ × GroundTerm σ)),
      attemptAll (matcher (σ := σ)) role ps m xs = some m' →
      (∀ y g, (y, g) ∈ m.bindings → (y, g) ∈ m'.bindings) ∧
        ∀ p ∈ ps, ∀ x ∈ p.freeVars, ∃ g, (x, g) ∈ m'.bindings
  | [], m, m', xs, accepted => by
      cases xs with
      | nil =>
          simp only [attemptAll, Option.some.injEq] at accepted
          subst accepted
          exact ⟨fun _ _ inside => inside, by simp⟩
      | cons _ _ => simp [attemptAll] at accepted
  | p :: ps, m, m', xs, accepted => by
      cases xs with
      | nil => simp [attemptAll] at accepted
      | cons x xs =>
          simp only [attemptAll] at accepted
          cases tried : attempt (matcher (σ := σ)) role p m x with
          | none => simp [tried] at accepted
          | some m₁ =>
              rw [tried, Option.bind_some] at accepted
              obtain ⟨_, θ, extended, rfl⟩ := (attempt_some_iff role p m _ x).mp tried
              have bound : (m.select role x.1 θ).bindings = θ := by cases role <;> rfl
              obtain ⟨keeps, binds⟩ := attemptAll_binds role ps _ m' xs accepted
              rw [bound] at keeps
              obtain ⟨new, _, _, rfl⟩ := extend_some extended
              refine ⟨fun y g inside => keeps y g (List.mem_append_left _ inside), ?_⟩
              intro q member y mentions
              rcases List.mem_cons.mp member with rfl | later
              · obtain ⟨g, inside⟩ := extend_binds extended y mentions
                exact ⟨g, keeps y g inside⟩
              · exact binds q later y mentions

/-- **Range restriction from scoped variables**: if every term a rule must determine mentions only
variables of its premises, the rule is range restricted. -/
theorem rangeRestricted_of_scoped (r : Rule (Term σ))
    (inScope : ∀ t ∈ groundedTerms r, ∀ x ∈ t.freeVars,
      x ∈ RuleSyntax.SetStoreSyntax.varsIn (r.body.take ++ r.body.read)) :
    RangeRestricted (matcher (σ := σ)) r := by
  rintro θ ⟨xs, ys, m₁, m₂, takes, reads, rfl⟩ t inside
  obtain ⟨_, takeBinds⟩ := attemptAll_binds .take r.body.take _ m₁ xs takes
  obtain ⟨keeps, readBinds⟩ := attemptAll_binds .read r.body.read m₁ m₂ ys reads
  apply instantiate_isSome
  intro x mentions
  obtain ⟨p, member, inP⟩ := (RuleSyntax.SetStoreSyntax.mem_variables _ x).mp (inScope t inside x mentions)
  rcases List.mem_append.mp member with taken | read
  · obtain ⟨g, bound⟩ := takeBinds p taken x inP
    exact ⟨g, keeps x g bound⟩
  · exact readBinds p read x inP

end Mettapedia.Machines.TIsa.Derivation.FirstOrderTerms
