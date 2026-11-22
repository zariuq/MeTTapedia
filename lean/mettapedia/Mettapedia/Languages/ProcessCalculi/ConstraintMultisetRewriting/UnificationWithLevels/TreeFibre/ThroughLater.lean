import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainArrows
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUpdateLifting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPrune

/-!
# Unknowns met by a store, mentioned by later declarations: the instantiated, reordered telescope

The solvers of arrow codes ask that no declaration mention an unknown they meet, because their answer keeps the
telescope (narrowed). A declaration `y : X` after `X` breaks this: `X := t` is an answer only over a telescope where
`y : t`. The tree builds that telescope:

* **The answer lifted past a later declaration** (`ContextualDependentUpdate.Update.lift`): an update of a store over `Γ`
  is an update of the same store read over `Γ, A`, with target `Γ', A[answer]`: the later declaration instantiated by
  the answer. A finished update stays finished (`settles_later`).
* **Two newest declarations exchanged** (`ContextualDependentPrune.exchange`), when the newer does not depend on the
  older: an update with no loss and no choice. So a declaration that mentions an unknown can be moved after the
  unknowns a store meets, which are declared at universes and depend on nothing.

**The fragment** (`Through`): the stores of a fragment `Q`; a store read past a later declaration (which may mention
any of its unknowns); an equivalent store; and a store whose two newest declarations, exchanged, give a store of the
fragment. **Every store of `Through Q` is settled when every store of `Q` is** (`through_settles`): it has a finished
update, hence a principal answer over the instantiated, reordered telescope, or no solution. For the arrow codes with
codomains (`throughArrows_settles`), the solver of arrow codes decides the store before the later declarations.
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

section Settles

variable {S : Setting Head L}

/-- **Settled**: a finished update (a principal answer), or no solution. -/
def Settles {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  (∃ update : Update S.levels problem, update.remaining = []) ∨ ¬ (frames S.levels).Solvable problem

/-- A settled store has a principal answer or no solution. -/
theorem Settles.principal_or_unsolvable {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (settled : Settles problem) :
    (∃ (Δ : Context S.R) (answer : Δ ⟶ Θ), (frames S.levels).Principal problem answer) ∨
      ¬ (frames S.levels).Solvable problem := by
  rcases settled with ⟨update, finished⟩ | absent
  · exact .inl ⟨update.target, update.answer, update.completed finished⟩
  · exact .inr absent

/-- **Read past a later declaration**: the finished update lifted, the later declaration instantiated by its answer;
or no solution, since every solution restricts to the older telescope. -/
theorem settles_later {Γ : Context S.R} (A : TypeOver Γ) {problem : EquationStore (TotalTerm Γ)}
    (settled : Settles problem) : Settles ((frames S.levels).applyStore (projectionHom Γ A) problem) := by
  rcases settled with ⟨update, finished⟩ | absent
  · refine .inl ⟨update.lift A, ?_⟩
    change (frames S.levels).applyStore (projectionHom update.target (A.reindex update.answer)) update.remaining = []
    rw [finished]
    rfl
  · refine .inr fun ⟨Δ, f, solved⟩ => absent ⟨Δ, f ≫ projectionHom Γ A, ?_⟩
    exact (Frames.models_applyStore (X := frames S.levels) (projectionHom Γ A) f problem).mp solved

/-- **The lifted answer's telescope**: the later declaration instantiated by the answer. -/
theorem later_target {Γ : Context S.R} (A : TypeOver Γ) {problem : EquationStore (TotalTerm Γ)}
    (update : Update S.levels problem) :
    (update.lift A).target.raw = .snoc update.target.raw (Presentation.subst update.answer.substitution A.code) :=
  Update.lift_target_type update A

/-- Settled stores stay settled along an equivalence. -/
theorem Settles.equivalent {Θ : Context S.R} {problem other : EquationStore (TotalTerm Θ)}
    (same : (frames S.levels).Equivalent problem other) (settled : Settles other) : Settles problem := by
  rcases settled with ⟨update, finished⟩ | absent
  · exact .inl ⟨update.rephrase same, finished⟩
  · exact .inr fun ⟨Δ, f, solved⟩ => absent ⟨Δ, f, (same Δ f).mp solved⟩

/-- A store is settled when an update of it leaves a settled store. -/
theorem Settles.after {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (first : Update S.levels problem)
    (settled : Settles first.remaining) : Settles problem := by
  rcases settled with ⟨update, finished⟩ | absent
  · exact .inl ⟨first.then update, finished⟩
  · exact .inr fun solvable => absent (first.solvable_iff.mp solvable)

end Settles

/-! ## Through later declarations -/

section Through

variable {S : Setting Head L}

/-- **Stores decided through later declarations**: a store of `Q`; a store read past a later declaration, which may
mention any of its unknowns; an equivalent store; a store whose two newest declarations, exchanged, give such a
store. -/
inductive Through (Q : ∀ {Γ : Context S.R}, EquationStore (TotalTerm Γ) → Prop) :
    ∀ {Θ : Context S.R}, EquationStore (TotalTerm Θ) → Prop
  | base {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)} : Q problem → Through Q problem
  | later {Γ : Context S.R} (A : TypeOver Γ) {problem : EquationStore (TotalTerm Γ)} :
      Through Q problem → Through Q ((frames S.levels).applyStore (projectionHom Γ A) problem)
  | equivalent {Θ : Context S.R} {problem other : EquationStore (TotalTerm Θ)} :
      (frames S.levels).Equivalent problem other → Through Q other → Through Q problem
  | exchange {Γ : Context S.R} (first next : TypeOver Γ)
      {problem : EquationStore (TotalTerm (ContextualDependentParameterExchange.context first next))} :
      Through Q (ContextualDependentPrune.exchange S.levels first next problem).remaining → Through Q problem

/-- **Every store through later declarations is settled when every store of the fragment is.** -/
theorem through_settles {Q : ∀ {Γ : Context S.R}, EquationStore (TotalTerm Γ) → Prop}
    (decide : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, Q problem → Settles problem) :
    ∀ {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}, Through Q problem → Settles problem
  | _, _, .base inside => decide inside
  | _, _, .later A inner => settles_later A (through_settles decide inner)
  | _, _, .equivalent same inner => (through_settles decide inner).equivalent same
  | _, _, .exchange first next inner =>
      Settles.after (ContextualDependentPrune.exchange S.levels first next _) (through_settles decide inner)

end Through

/-! ## Arrow codes with codomains through later declarations -/

section Arrows

variable {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
  [DecidableRel S.R.headEq]
variable (choices : ExecutableChecking.HeadChoices S.R) (glb : Head → Head → Option Head)
  (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (declared : DeclaredTypesFormed S.R)
  (strengthening : ContextualDependentIntersectionGeneral.EqualStrengthening S.R)
  (total : ∀ {a b : Head}, S.R.isUniverse a → S.R.isUniverse b → ∃ g, glb a b = some g)

include facts roots heads algebra rigid complete headTypingUnique declared strengthening spec total in
/-- **The fragment of arrow codes is settled**, by a run of its solver. -/
theorem arrows_settles {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (inside : InArrowsCod choices problem) : Settles problem := by
  obtain ⟨fuel, decided⟩ := arrowsCod_decided choices glb spec facts roots heads algebra rigid complete
    headTypingUnique declared strengthening total inside
  rcases (decided fuel le_rfl).2 with ⟨state, finished, _, _⟩ | ⟨absent, _⟩
  · exact .inl ⟨state, finished⟩
  · exact .inr absent

include facts roots heads algebra rigid complete headTypingUnique declared strengthening spec total in
/-- **Equations between arrow codes through later declarations are decided**: the solver of arrow codes runs on the
store before the later declarations; its answer is lifted past them, each instantiated by it, and carried through the
exchanges. Every such store has a principal answer over the instantiated, reordered telescope, or no solution. -/
theorem throughArrows_settles {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (inside : Through (InArrowsCod choices) problem) : Settles problem :=
  through_settles (fun inside => arrows_settles choices glb spec facts roots heads algebra rigid complete
    headTypingUnique declared strengthening total inside) inside

include facts roots heads algebra rigid complete headTypingUnique declared strengthening spec total in
theorem throughArrows_principal_or_unsolvable {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (inside : Through (InArrowsCod choices) problem) :
    (∃ (Δ : Context S.R) (answer : Δ ⟶ Θ), (frames S.levels).Principal problem answer) ∨
      ¬ (frames S.levels).Solvable problem :=
  (throughArrows_settles choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
    strengthening total inside).principal_or_unsolvable

end Arrows

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
