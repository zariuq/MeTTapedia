import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.Consistency

/-!
# Root steps in the set tower: controls

A set model asks a root step to preserve values at every environment of a context in which
the premises required of the step hold (`SetModel.steps`); a step that requires none must
preserve values at every environment of every context. The value of a declared constant
that computes is a trace function, which gives the empty set outside its domain
(`traceApp_eq_empty_of_not_mem`). So no root step whose left side applies such a constant
can preserve values at an environment that puts the argument outside the declared domain;
only its typed instances can, and a step that requires its argument typed is read at them
alone.

* **The δ-step of the identity on `U₀`** (`deltaPackage`, the annotation of the candidate
  package `deltaRules`): `idU : Π (X : U₀). U₀` with the root step `idU X ⟶ X`. It has no set
  model in the tower (`deltaPackage_no_setModel`): at the environment sending `X` to the
  universe `U₀` itself, the left side denotes `∅` and the right side `U₀`.
* **At its typed instances the step is valid** (`delta_valid_at_typed`): with `idU` the traced
  identity on `U₀`, a value in the declared type (`idValue_typed`), the two sides have one value
  wherever the argument lies in `U₀`.
* **With its premise the step has a set model** (`typedDeltaPackage`,
  `typedDeltaPackage_setModel`): the same step, requiring its argument typed in `U₀`, is
  read only where the argument is typed, and every derivation of the package holds in the
  tower (`typedDelta_sound`).
* **The value of a dependent function type does not determine its domain**
  (`tracePiSet_domain_invisible`): over every domain, the trace functions into the true truth
  value `{∅}` form the one set `{∅}`. So a typing at a dependent function type that holds in
  the model says nothing of the domain the function was declared with, and an equation of
  dependent function types that holds in the model says nothing of their domains: the facts a
  typed instance needs cannot be read off values.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace ComputationControls

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInterpretation (universeSet universeSet_closed seed_mem_universeSet)
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open ZFSetTraceUniverseInterpretation (interpretHead)
open ZFSetDependentProducts (graph)
open ZFSetTraceProducts (traceLam traceApp tracePiSet traceApp_graph_beta
  mem_tracePiSet_subterminal_iff)

universe u

/-- The name of the identity on `U₀`. -/
def idName : DeclName := `idU

/-- Its declared type, `Π (X : U₀). U₀`. -/
def idType : CTm Tower.Head 0 := .pi U0 U0

/-- **The δ-step of the identity on `U₀`**: `idU X ⟶ X`, at every argument. -/
def deltaStep {n : Nat} (l r : CTm Tower.Head n) : Prop :=
  ∃ X, l = .app (.const idName) X ∧ r = X

/-- The candidate's universe package with the identity on `U₀` declared, and its δ-step
`idU X ⟶ X` on candidate terms. -/
def deltaRules : Rules Tower.Head :=
  { Tower.rules with
    constantType := fun c => if c = idName then some idType.erase else none
    computation :=
      { step := fun l r => ∃ X, l = .app (.const idName) X ∧ r = X
        rename := by
          rintro n m ρ _ X ⟨_, rfl, rfl⟩
          exact ⟨Presentation.rename ρ X, rfl, rfl⟩
        substitute := by
          rintro n m σ _ X ⟨_, rfl, rfl⟩
          exact ⟨Presentation.subst σ X, rfl, rfl⟩ } }

/-- The universe package with the identity on `U₀` declared, and its δ-step: the annotation
of `deltaRules`. -/
def deltaPackage : ChurchRules deltaRules where
  constantType := fun c => if c = idName then some idType else none
  computation :=
    { step := deltaStep
      rename := by
        rintro n m ρ _ X ⟨_, rfl, rfl⟩
        exact ⟨X.rename ρ, rfl, rfl⟩
      substitute := by
        rintro n m σ _ X ⟨_, rfl, rfl⟩
        exact ⟨X.subst σ, rfl, rfl⟩ }
  erase_constantType := fun c => by
    show (if c = idName then some idType else none).map CTm.erase =
      if c = idName then some idType.erase else none
    by_cases hc : c = idName
    · rw [if_pos hc, if_pos hc]
      rfl
    · rw [if_neg hc, if_neg hc]
      rfl
  erase_step := by
    rintro n _ X ⟨_, rfl, rfl⟩
    exact ⟨X.erase, rfl, rfl⟩

theorem deltaPackage_idName : deltaPackage.constantType idName = some idType := by
  show (if idName = idName then some idType else none) = some idType
  exact if_pos rfl

/-- **The δ-package has no set model in the tower**: its root step requires no premises, so it
would preserve values at every environment of every context. At a variable of the next
universe sent to `U₀` itself, outside the declared domain `U₀`, the left side denotes the
empty set and the right side `U₀`. -/
theorem deltaPackage_no_setModel (h : CofinalInaccessibles.{u}) (consts : DeclName → ZFSet.{u}) :
    ¬ SetModel (interpretHead h ∅ ∅ (fun _ => 0)) consts deltaPackage := by
  intro model
  have typed : consts idName ∈ tracePiSet (universeSet h ∅ (Tower.zero.eval fun _ => 0))
      (fun _ => universeSet h ∅ (Tower.zero.eval fun _ => 0)) :=
    model.constants deltaPackage_idName
  have above : universeSet h ∅ (Tower.zero.eval fun _ => 0) ∈
      universeSet h ∅ ((LevelExpr.succ Tower.zero).eval fun _ => 0) :=
    model.universes.headTyping_mem (.sort Tower.zero)
  have sat : Sat (interpretHead h ∅ ∅ (fun _ => 0)) consts
      (.snoc .nil (.head (.sort (.succ Tower.zero))))
      (extend Fin.elim0 (universeSet h ∅ (Tower.zero.eval fun _ => 0))) :=
    (sat_snoc _ consts).mpr ⟨sat_nil _ consts _, above⟩
  have step := model.steps (l := .app (.const idName) (.var 0)) (r := .var 0)
    ⟨.var 0, rfl, rfl⟩ rfl (fun _ member => absurd member List.not_mem_nil) _ sat
  change traceApp (consts idName) (universeSet h ∅ (Tower.zero.eval fun _ => 0)) =
    universeSet h ∅ (Tower.zero.eval fun _ => 0) at step
  rw [traceApp_eq_empty_of_not_mem typed (ZFSet.mem_irrefl _)] at step
  have member := (universeSet_closed h ∅ (Tower.zero.eval fun _ => 0)).empty_mem
    (seed_mem_universeSet h ∅ _)
  rw [← step] at member
  exact ZFSet.notMem_empty _ member

/-- The value of the identity on `U₀`: the traced graph of the identity. -/
noncomputable def idValue (h : CofinalInaccessibles.{u}) : ZFSet.{u} :=
  traceLam (graph (universeSet h ∅ (Tower.zero.eval fun _ => 0)) fun x => x)

/-- The identity's value lies in its declared type: only the root step fails. -/
theorem idValue_typed (h : CofinalInaccessibles.{u}) :
    idValue h ∈ ev (interpretHead h ∅ ∅ (fun _ => 0)) (fun _ => idValue h) idType Fin.elim0 :=
  traceLam_graph_mem fun _ hx => hx

/-- **The δ-step is valid at its typed instances**: the two sides have one value wherever the
argument lies in the declared domain `U₀`. -/
theorem delta_valid_at_typed (h : CofinalInaccessibles.{u}) {n : Nat} (X : CTm Tower.Head n)
    (ρ : Env.{u} n)
    (typed : ev (interpretHead h ∅ ∅ (fun _ => 0)) (fun _ => idValue h) X ρ ∈
      universeSet h ∅ (Tower.zero.eval fun _ => 0)) :
    ev (interpretHead h ∅ ∅ (fun _ => 0)) (fun _ => idValue h) (.app (.const idName) X) ρ =
      ev (interpretHead h ∅ ∅ (fun _ => 0)) (fun _ => idValue h) X ρ := by
  change traceApp (idValue h) _ = _
  exact traceApp_graph_beta (fun x => x) typed

/-! ## The δ-step with its premise -/

/-- **The δ-step with its premise**: the same step `idU X ⟶ X`, requiring its argument typed
in `U₀`. -/
def typedDeltaPackage : ChurchRules deltaRules where
  constantType := deltaPackage.constantType
  computation :=
    { step := deltaStep
      rename := deltaPackage.computation.rename
      substitute := deltaPackage.computation.substitute
      requires := fun l _ premises =>
        ∃ X, l = .app (.const idName) X ∧ premises = [.typing X (.head (.sort Tower.zero))]
      requires_rename := by
        rintro n m ρ _ _ _ ⟨X, rfl, rfl⟩
        exact ⟨X.rename ρ, rfl, rfl⟩
      requires_substitute := by
        rintro n m σ _ _ _ ⟨X, rfl, rfl⟩
        exact ⟨X.subst σ, rfl, rfl⟩ }
  erase_constantType := deltaPackage.erase_constantType
  erase_step := deltaPackage.erase_step

/-- **Positive: with its premise, the δ-package has a set model in the tower**, the identity
read as the traced identity on `U₀`. The step is read only in the contexts in which its
argument is typed, and there its two sides have one value (`delta_valid_at_typed`). -/
theorem typedDeltaPackage_setModel (h : CofinalInaccessibles.{u}) :
    SetModel (interpretHead h ∅ ∅ (fun _ => 0)) (fun _ => idValue h) typedDeltaPackage where
  universes := { (standardTowerModel h).universes with }
  headEq := (standardTowerModel h).headEq
  constants := by
    intro c T declared
    change (if c = idName then some idType else none) = some T at declared
    by_cases hc : c = idName
    · rw [if_pos hc] at declared
      cases declared
      exact idValue_typed h
    · rw [if_neg hc] at declared
      cases declared
  steps := by
    rintro n Γ _ _ premises ⟨X, rfl, rfl⟩ ⟨X', same, rfl⟩ holds ρ sat
    injection same with _ _ sameArgument
    subst sameArgument
    exact delta_valid_at_typed h _ ρ (holds _ (List.mem_singleton_self _) ρ sat)

/-- **The typed δ-step is an equality that holds in the tower**: `idU X ≡ X : U₀` is derivable
for every `X : U₀`, and its two sides have one value at every environment of the context. -/
theorem typedDelta_sound (h : CofinalInaccessibles.{u}) {n : Nat} {Γ : CCtx Tower.Head n}
    {X : CTm Tower.Head n}
    (typed : CTyped typedDeltaPackage Γ X (.head (.sort Tower.zero)))
    (applied : CTyped typedDeltaPackage Γ (.app (.const idName) X) (.head (.sort Tower.zero))) :
    Holds (interpretHead h ∅ ∅ (fun _ => 0)) (fun _ => idValue h)
      (.equality Γ (.app (.const idName) X) X (.head (.sort Tower.zero))) :=
  CDerivable.sound (typedDeltaPackage_setModel h)
    (.root (P := typedDeltaPackage) ⟨X, rfl, rfl⟩ ⟨X, rfl, rfl⟩
      (fun _ member => by
        rw [List.mem_singleton.1 member]
        exact typed) applied typed)

/-- **The value of a dependent function type does not determine its domain**: over every
domain, the trace functions into the true truth value `{∅}` form one set. -/
theorem tracePiSet_domain_invisible (a a' : ZFSet.{u}) :
    tracePiSet a (fun _ => ({∅} : ZFSet.{u})) = tracePiSet a' (fun _ => {∅}) := by
  apply ZFSet.ext
  intro t
  rw [mem_tracePiSet_subterminal_iff (fun _ _ => fun _ hz => hz),
    mem_tracePiSet_subterminal_iff (fun _ _ => fun _ hz => hz)]
  exact ⟨fun ⟨e, _⟩ => ⟨e, fun _ _ => ZFSet.mem_singleton.mpr rfl⟩,
    fun ⟨e, _⟩ => ⟨e, fun _ _ => ZFSet.mem_singleton.mpr rfl⟩⟩

/-- In particular the empty set is a trace function from `∅` and from `{∅}`, two different
domains, into `{∅}`. -/
theorem empty_mem_two_domains :
    (∅ : ZFSet.{u}) ∈ tracePiSet (∅ : ZFSet.{u}) (fun _ => {∅}) ∧
      (∅ : ZFSet.{u}) ∈ tracePiSet ({∅} : ZFSet.{u}) (fun _ => {∅}) ∧
      (∅ : ZFSet.{u}) ≠ {∅} := by
  refine ⟨(mem_tracePiSet_subterminal_iff (fun _ _ => fun _ hz => hz)).mpr
      ⟨rfl, fun _ _ => ZFSet.mem_singleton.mpr rfl⟩,
    (mem_tracePiSet_subterminal_iff (fun _ _ => fun _ hz => hz)).mpr
      ⟨rfl, fun _ _ => ZFSet.mem_singleton.mpr rfl⟩, fun e => ?_⟩
  have member : (∅ : ZFSet.{u}) ∈ ({∅} : ZFSet.{u}) := ZFSet.mem_singleton.mpr rfl
  rw [← e] at member
  exact ZFSet.notMem_empty _ member

end ComputationControls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
