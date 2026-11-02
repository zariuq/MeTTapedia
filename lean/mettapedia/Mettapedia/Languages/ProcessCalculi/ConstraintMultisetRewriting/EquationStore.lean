import Mathlib.Data.List.Basic

/-!
# Equation stores for constraint multiset rewriting

Terms are supplied by an existing syntax. Both sides of an equation are
interpreted by the same substitution. No direction of matching, choice of a
unification algorithm, or finiteness of a complete set of answers is assumed.

An equation store denotes all of its solutions. Adding equations refines this
set; a solver may change the representation only while preserving that set.
The substitution action is also used to state principality and residualization.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

universe uT uS

/-- A substitution action on an existing term syntax, modulo its declared
equality. The laws concern substitution, not a particular solver. -/
structure SubstitutionAction (T : Type uT) (S : Type uS) where
  E : T → T → Prop
  equivalence : Equivalence E
  apply : S → T → T
  identity : S
  compose : S → S → S
  apply_identity : ∀ t, apply identity t = t
  apply_compose : ∀ outer inner t,
    apply (compose outer inner) t = apply outer (apply inner t)
  preserves : ∀ σ {s t}, E s t → E (apply σ s) (apply σ t)

abbrev Equation (T : Type uT) := T × T
abbrev EquationStore (T : Type uT) := List (Equation T)

namespace SubstitutionAction

variable {T : Type uT} {S : Type uS} (A : SubstitutionAction T S)

def Solves (σ : S) (e : Equation T) : Prop :=
  A.E (A.apply σ e.1) (A.apply σ e.2)

def Models (σ : S) (store : EquationStore T) : Prop :=
  ∀ e ∈ store, A.Solves σ e

def Consistent (store : EquationStore T) : Prop := ∃ σ, A.Models σ store

/-- A stronger store has fewer possible solutions. -/
def Refines (stronger weaker : EquationStore T) : Prop :=
  ∀ σ, A.Models σ stronger → A.Models σ weaker

def Equivalent (one two : EquationStore T) : Prop :=
  ∀ σ, A.Models σ one ↔ A.Models σ two

/-- An ask observes every remaining solution and adds no binding. -/
def Entails (store : EquationStore T) (observation : S → Prop) : Prop :=
  ∀ σ, A.Models σ store → observation σ

/-- The terms have no common instance compatible with the current store. -/
def Apart (store : EquationStore T) (s t : T) : Prop :=
  ¬ A.Consistent (store ++ [(s, t)])

@[simp] theorem models_nil (σ : S) : A.Models σ [] := by
  simp [Models]

@[simp] theorem models_cons (σ : S) (e : Equation T) (store : EquationStore T) :
    A.Models σ (e :: store) ↔ A.Solves σ e ∧ A.Models σ store := by
  simp [Models]

@[simp] theorem models_append (σ : S) (one two : EquationStore T) :
    A.Models σ (one ++ two) ↔ A.Models σ one ∧ A.Models σ two := by
  constructor
  · intro all
    exact ⟨fun e member => all e (List.mem_append_left _ member),
      fun e member => all e (List.mem_append_right _ member)⟩
  · rintro ⟨first, second⟩ e member
    exact (List.mem_append.mp member).elim (first e) (second e)

theorem models_compose {σ : S} {store : EquationStore T}
    (solves : A.Models σ store) (later : S) :
    A.Models (A.compose later σ) store := by
  intro e member
  simpa [Solves, A.apply_compose] using A.preserves later (solves e member)

theorem refines_refl (store : EquationStore T) : A.Refines store store :=
  fun _ h => h

theorem refines_trans {one two three : EquationStore T}
    (first : A.Refines one two) (second : A.Refines two three) :
    A.Refines one three := fun σ h => second σ (first σ h)

theorem append_refines (store extra : EquationStore T) :
    A.Refines (store ++ extra) store :=
  fun _ h => (A.models_append _ _ _).mp h |>.1

theorem entails_of_refines {stronger weaker : EquationStore T}
    (refinement : A.Refines stronger weaker) {observation : S → Prop}
    (entailed : A.Entails weaker observation) : A.Entails stronger observation :=
  fun σ h => entailed σ (refinement σ h)

theorem apart_of_refines {stronger weaker : EquationStore T}
    (refinement : A.Refines stronger weaker) {s t : T}
    (apart : A.Apart weaker s t) : A.Apart stronger s t := by
  rintro ⟨σ, solved⟩
  obtain ⟨current, equation⟩ := (A.models_append _ _ _).mp solved
  exact apart ⟨σ, (A.models_append _ _ _).mpr ⟨refinement σ current, equation⟩⟩

/-- A principal answer is a solution through which every solution factors,
up to the declared equality on every term. -/
structure Principal (store : EquationStore T) (answer : S) : Prop where
  sound : A.Models answer store
  factors : ∀ δ, A.Models δ store → ∃ residual,
    ∀ t, A.E (A.apply δ t) (A.apply (A.compose residual answer) t)

def applyStore (σ : S) (store : EquationStore T) : EquationStore T :=
  store.map fun e => (A.apply σ e.1, A.apply σ e.2)

/-- Residual equations are interpreted after the answer, in that order. -/
theorem models_applyStore (outer inner : S) (store : EquationStore T) :
    A.Models outer (A.applyStore inner store) ↔
      A.Models (A.compose outer inner) store := by
  constructor
  · intro solved e member
    simpa only [Solves, A.apply_compose] using
      solved _ (List.mem_map.mpr ⟨e, member, rfl⟩)
  · intro solved e member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    simpa only [Solves, A.apply_compose] using solved original present

/-- Principal answers solve the old store for every residual substitution. -/
theorem Principal.extension_models {store : EquationStore T} {answer : S}
    (principal : A.Principal store answer) (residual : S) :
    A.Models (A.compose residual answer) store :=
  A.models_compose principal.sound residual

/-- Solving an old store, then its residual new equations, gives a principal
solution of the combined problem. The residual equations are explicit data. -/
theorem Principal.compose {old extra : EquationStore T} {first second : S}
    (oldPrincipal : A.Principal old first)
    (residualPrincipal : A.Principal (A.applyStore first extra) second) :
    A.Principal (old ++ extra) (A.compose second first) := by
  refine ⟨(A.models_append _ _ _).mpr ⟨Principal.extension_models A oldPrincipal second,
    (A.models_applyStore second first extra).mp residualPrincipal.sound⟩, ?_⟩
  intro candidate candidateSolves
  obtain ⟨oldSolved, extraSolved⟩ := (A.models_append _ _ _).mp candidateSolves
  obtain ⟨middle, throughFirst⟩ := oldPrincipal.factors candidate oldSolved
  have residualSolved : A.Models middle (A.applyStore first extra) := by
    apply (A.models_applyStore middle first extra).mpr
    intro e member
    exact A.equivalence.trans (A.equivalence.symm (throughFirst e.1))
      (A.equivalence.trans (extraSolved e member) (throughFirst e.2))
  obtain ⟨last, throughSecond⟩ := residualPrincipal.factors middle residualSolved
  refine ⟨last, fun term => ?_⟩
  have secondTerm := throughSecond (A.apply first term)
  simp only [A.apply_compose] at secondTerm ⊢
  exact A.equivalence.trans (by simpa only [A.apply_compose] using throughFirst term) secondTerm

/-- A representation change is valid exactly when its models agree. In
particular, a residual store must not silently discard an unresolved equation. -/
theorem equivalent_consistent {one two : EquationStore T}
    (same : A.Equivalent one two) : A.Consistent one ↔ A.Consistent two := by
  constructor
  · rintro ⟨σ, h⟩
    exact ⟨σ, (same σ).mp h⟩
  · rintro ⟨σ, h⟩
    exact ⟨σ, (same σ).mpr h⟩

end SubstitutionAction

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
