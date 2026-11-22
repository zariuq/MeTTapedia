import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ThroughRead
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepth

/-!
# Stores that meet a declaration mentioning a solved unknown: solve in phases

The reader of `ThroughRead` strips a later declaration only when no equation meets it. A store can meet a declaration
`y : X` whose type mentions an unknown `X` that another equation solves: the equations on `y` are read by no piece until
`X` is known (`y : X` is no universe family). Such stores are decided **in phases**:

* the equations that strengthen past the newest declaration are decided first, over the older telescope (recursively,
  so through every later declaration they do not meet);
* their finished update is lifted past the newest declaration, which it instantiates, and the other equations are
  instantiated by its answer (`Update.lift`, `Update.keepLeft`);
* the instantiated equations are put in η-long form (`expandStore`, with exactly the same solutions) and decided over
  the instantiated telescope.

When neither applies, the two newest declarations are exchanged if the newer does not depend on the older, and the
exchanged store is decided in phases. A refutation of the first phase refutes the store, since every solution restricts
to the older telescope; a refutation of the second phase refutes it along the update. The base decision is any
decision procedure, for instance a run of a solver that finishes (`Decided.ofRun`); several can be tried in turn. The
procedure returns a finished update or a refutation as data (`Decided`), so it is sound by construction, and every store
it decides is settled (`phases_settles`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

variable {Head L : Type} [UniverseLevel.LevelOrder L]

section Decided

variable {S : Setting Head L}

/-- **A decided store, as data**: a finished update, or no solution. -/
inductive Decided {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Type
  | solved (update : Update S.levels problem) (finished : update.remaining = [])
  | refuted (absent : ¬ (frames S.levels).Solvable problem)

/-- A decided store is settled. -/
theorem Decided.settles {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} :
    Decided problem → Settles problem
  | .solved update finished => .inl ⟨update, finished⟩
  | .refuted absent => .inr absent

/-- A run of a solver that finishes, as a decided store. -/
def Decided.ofRun (solver : ContextualDependentWorklist.Solver S.levels) (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Option (Decided problem) :=
  match run solver problem fuel with
  | .solved state finished => some (.solved state finished)
  | .refuted absent => some (.refuted absent)
  | _ => none

/-- A store is decided after an update when the update's residual store is. -/
def Decided.after {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (first : Update S.levels problem) :
    Decided first.remaining → Decided problem
  | .solved update finished => .solved (first.then update) finished
  | .refuted absent => .refuted fun solvable => absent (first.solvable_iff.mp solvable)

/-- A store is decided when an equivalent store is. -/
def Decided.equivalent {Θ : Context S.R} {problem other : EquationStore (TotalTerm Θ)}
    (same : (frames S.levels).Equivalent problem other) : Decided other → Decided problem
  | .solved update finished => .solved (update.rephrase same) finished
  | .refuted absent => .refuted fun ⟨Δ, σ, models⟩ => absent ⟨Δ, σ, (same Δ σ).mp models⟩

/-- Decide at the newest declaration of a context. -/
def decideNewest {Θ : Context S.R} (view : Newest Θ) (problem : EquationStore (TotalTerm Θ))
    (decide : {Γ : Context S.R} → (type : TypeOver Γ) → (stored : EquationStore (TotalTerm (extend Γ type))) →
      Option (Decided stored)) :
    Option (Decided problem) := by
  rcases view with ⟨base, type, same⟩
  subst same
  exact decide type problem

/-- Decide at the two newest declarations of a context. -/
def decideTwo {Θ : Context S.R} (outer : Newest Θ) (inner : Newest outer.base) (problem : EquationStore (TotalTerm Θ))
    (decide : {Γ₀ : Context S.R} → (older : TypeOver Γ₀) → (newer : TypeOver (extend Γ₀ older)) →
      (stored : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) → Option (Decided stored)) :
    Option (Decided problem) := by
  cases outer with
  | mk base newer same =>
      cases inner with
      | mk base₀ older same₀ =>
          change base = extend base₀ older at same₀
          subst same₀
          subst same
          exact decide older newer problem

end Decided

section Phases

variable {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

/-- **Two phases at the newest declaration**: decide the equations that strengthen past it; lift their finished update
past it, instantiating it and the other equations; decide the instantiated equations in η-long form. -/
def phaseAt (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ) (stored : EquationStore (TotalTerm (extend Γ type)))
    (decide : {Θ : Context S.R} → (problem : EquationStore (TotalTerm Θ)) → Option (Decided problem)) :
    Option (Decided stored) :=
  let parts := ContextualDependentInPlace.separation facts roots heads algebra declared choices reducer fuel type stored
  match decide parts.val.1 with
  | none => none
  | some (.refuted absent) => some (.refuted fun ⟨Δ, σ, models⟩ =>
      absent ⟨Δ, σ ≫ projectionHom Γ type,
        (Frames.models_applyStore (X := frames S.levels) (projectionHom Γ type) σ parts.val.1).mp
          ((Frames.models_append (X := frames S.levels) σ parts.val.2 _).mp ((parts.property Δ σ).mp models)).2⟩)
  | some (.solved update _) =>
      let lifted := ((update.lift type).keepLeft parts.val.2).rephrase parts.property
      (decide (ContextualDependentEtaDepth.expandStore facts lifted.remaining)).map fun rest =>
        Decided.after lifted (Decided.equivalent (ContextualDependentEtaDepth.expand_equivalent facts _) rest)

/-- **Exchange the two newest declarations** when the newer does not depend on the older, and decide the exchanged
store. -/
def exchangeAt (fuel : Nat) {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    (stored : EquationStore (TotalTerm (extend (extend Γ₀ older) newer)))
    (decide : {Θ : Context S.R} → (problem : EquationStore (TotalTerm Θ)) → Option (Decided problem)) :
    Option (Decided stored) :=
  match (ContextualDependentInPlace.strengthenCode (n := Γ₀.arity) newer.code).map Subtype.val with
  | none => none
  | some code =>
      match ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Γ₀ code with
      | none => none
      | some next =>
          if same : newer.code = (ContextualDependentParameterExchange.second older next.val).code ∧
              newer.level = (ContextualDependentParameterExchange.second older next.val).level then by
            have independent : newer = ContextualDependentParameterExchange.second older next.val :=
              TypeOver.ext same.1 same.2
            subst independent
            exact (decide (ContextualDependentPrune.exchange S.levels older next.val stored).remaining).map
              (Decided.after (ContextualDependentPrune.exchange S.levels older next.val stored))
          else none

variable (base : ∀ {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)), Option (Decided problem))

/-- **Decide in phases**, with a budget of steps: the base decision; or two phases at the newest declaration; or the
two newest declarations exchanged; each decided again in phases. -/
def phases (fuel : Nat) : (depth : Nat) → {Θ : Context S.R} → (problem : EquationStore (TotalTerm Θ)) →
    Option (Decided problem)
  | 0, _, problem => base problem
  | depth + 1, Θ, problem =>
      match base problem with
      | some found => some found
      | none =>
          match newestOf facts roots heads algebra declared choices reducer fuel Θ with
          | none => none
          | some outer =>
              match decideNewest outer problem (fun type stored =>
                  phaseAt facts roots heads algebra declared choices reducer fuel type stored (phases fuel depth)) with
              | some found => some found
              | none =>
                  match newestOf facts roots heads algebra declared choices reducer fuel outer.base with
                  | none => none
                  | some inner => decideTwo outer inner problem fun older newer stored =>
                      exchangeAt facts roots heads algebra declared choices reducer fuel older newer stored
                        (phases fuel depth)

/-- **Every store decided in phases is settled**: a principal answer over the instantiated telescope, or no
solution. -/
theorem phases_settles {fuel depth : Nat} {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (found : (phases facts roots heads algebra declared choices reducer base fuel depth problem).isSome = true) :
    Settles problem :=
  ((phases facts roots heads algebra declared choices reducer base fuel depth problem).get found).settles

end Phases

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
