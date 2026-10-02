import Mettapedia.GSLT.Core.IndexedOperational
import Mettapedia.GSLT.Scope.UpdateSquares
import Mettapedia.GSLT.Logic.HennessyMilnerAdequacy
import Mettapedia.TypeTheory.MaterialSets.Hypersets.Finality

/-!
# Simulations and bisimulations as scope changes

A transition system `step : X → X → Prop` is a GSLT with syntactic equations
(`transitionSystem`), and a view `view : X → Y` into a second system
`step' : Y → Y → Prop` is a change of scope.  This module identifies the
operational equipment's arrows between such systems with the standard notions
of process theory, modal logic and abstract interpretation.

**Simulation (forth only).**  A view preserves transitions
(`PreservesEdges`) exactly when it is the term map of a step-preserving
operational translation (`exists_operationalTranslation_iff`).  Negation-free
Hennessy–Milner formulas transfer from a state to its image
(`psat_of_preservesEdges`).  Such a view never misses a transition of the
first system, but the second may have transitions the first cannot make.

**Bisimulation (forth and back).**  A view that also reflects transitions
(`ReflectsEdges`) is a bounded morphism (`IsBoundedMorphism`), also called a
zig-zag morphism or p-morphism in modal logic, a functional bisimulation in
process theory, and a coalgebra homomorphism for the powerset functor.  It is
exactly the term map of a covered operational translation
(`exists_coveredTranslation_iff`), and every Hennessy–Milner formula has the
same truth value at a state and at its image
(`sat_iff_of_isBoundedMorphism`).
* Nondeterministic support (`RelSupports`) is exactly the existence of an
  abstract step relation making the view a bounded morphism
  (`relSupports_iff_exists_isBoundedMorphism`), equivalently a covered
  translation (`relSupports_iff_exists_coveredTranslation`); by
  `relSupports_iff` this holds exactly when the kernel of the view is a
  bisimulation (`kernelBisimulation_iff_isBisimulation`).
* **Control separating the two**: from a state without transitions into a
  state with a loop, the identity preserves transitions and does not reflect
  them (`Spurious.simulation`, `Spurious.not_bisimulation`); the formula
  "no transition" holds at the first state and fails at its image
  (`Spurious.formula_separates`).
* Control from the observer stages: observation by evaluation admits no
  covered translation for root β-reduction
  (`eliminators_no_coveredTranslation`).

**Deterministic updates.**  For the graphs of `f : X → X` and
`f' : Y → Y`, forth implies back, and both say that the update square
commutes, `view ∘ f = f' ∘ view` (`isBoundedMorphism_update_iff`,
`preservesEdges_update_iff`, `square_iff_exists_operationalTranslation`).
In abstract interpretation this equation is *completeness* of the abstraction
for `f`: R. Giacobazzi, F. Ranzato and F. Scozzari (*Making abstract
interpretations complete*, J. ACM 47(2), 2000) define `⟨A, f♯⟩` to be
complete for `f` when `α ∘ f = f♯ ∘ α`.  Later work calls this backward
completeness and contrasts it with forward completeness,
`f ∘ γ = γ ∘ f♯` (R. Giacobazzi and E. Quintarelli, SAS 2001; F. Ranzato and
F. Tapparo, ESOP 2004).  On the collecting semantics:
* the image abstraction is backward complete for the image of `f` exactly
  when `view ∘ f` is constant on the fibres of `view`
  (`backwardComplete_iff_constantOnFibers`), with the best correct
  approximation as witness; a supported update is backward complete
  (`Supports.backwardComplete`), and for a surjective view the converse holds
  (`supports_iff_backwardComplete`);
* the partition abstraction of a view is forward complete for the
  predecessor transformer exactly when the kernel of the view is a
  bisimulation (`forwardCompletePre_iff_kernelBisimulation`), the partition
  case of strong preservation read as completeness.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Scope

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u

/-! ## Transition systems as GSLTs -/

/-- A transition system as a GSLT whose equations are syntactic equality. -/
def transitionSystem {X : Type u} (step : X → X → Prop) : GSLT.{u} where
  Term := X
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := step
  rewrites_resp_left := by
    intro source source' target equal moved
    exact ⟨target, (show source = source' from equal) ▸ moved, rfl⟩
  rewrites_resp_right := by
    intro source target target' moved equal
    exact (show target = target' from equal) ▸ moved

/-- The transition system of a deterministic update: one transition from each
state, to its update. -/
def updateSystem {X : Type u} (f : X → X) : GSLT.{u} :=
  transitionSystem fun x x' => f x = x'

variable {X Y : Type u}

@[simp] theorem transitionSystem_step (step : X → X → Prop) (x x' : X) :
    (transitionSystem step).Step x x' ↔ step x x' :=
  Iff.rfl

/-! ## Simulation: forth only -/

section Simulation

variable {step : X → X → Prop} {step' : Y → Y → Prop} {view : X → Y}

/-- A transition-preserving view is a step-preserving operational
translation. -/
def operationalOfPreserves (preserves : PreservesEdges step step' view) :
    OperationalTranslation (transitionSystem step) (transitionSystem step') where
  mapTerm := view
  mapEquiv := fun equal => congrArg view equal
  mapStep := fun moved => preserves moved

@[simp] theorem operationalOfPreserves_mapTerm (preserves : PreservesEdges step step' view) :
    (operationalOfPreserves preserves).mapTerm = view :=
  rfl

/-- **A view is a functional simulation exactly when it is the term map of an
operational translation.** -/
theorem exists_operationalTranslation_iff :
    (∃ τ : OperationalTranslation (transitionSystem step) (transitionSystem step'),
        τ.mapTerm = view) ↔ PreservesEdges step step' view := by
  constructor
  · rintro ⟨τ, rfl⟩ x x' moved
    exact τ.mapStep moved
  · intro preserves
    exact ⟨operationalOfPreserves preserves, rfl⟩

end Simulation

/-! ## Bisimulation: forth and back -/

section Bisimulation

variable {step : X → X → Prop} {step' : Y → Y → Prop} {view : X → Y}

/-- A bounded morphism is a covered operational translation. -/
def coveredOfBoundedMorphism (bounded : IsBoundedMorphism step step' view) :
    CoveredTranslation (transitionSystem step) (transitionSystem step') where
  mapTerm := view
  mapEquiv := fun equal => congrArg view equal
  cover := ⟨fun moved => bounded.map moved, fun moved => bounded.lift moved⟩

/-- **A view is a functional bisimulation exactly when it is the term map of a
covered operational translation.** -/
theorem exists_coveredTranslation_iff :
    (∃ τ : CoveredTranslation (transitionSystem step) (transitionSystem step'),
        τ.mapTerm = view) ↔ IsBoundedMorphism step step' view := by
  constructor
  · rintro ⟨τ, rfl⟩
    exact ⟨fun _ _ moved => τ.cover.mapStep moved, fun _ _ moved => τ.cover.liftStep moved⟩
  · intro bounded
    exact ⟨coveredOfBoundedMorphism bounded, rfl⟩

/-- A covered translation forgets to a functional simulation. -/
theorem IsBoundedMorphism.preservesEdges (bounded : IsBoundedMorphism step step' view) :
    PreservesEdges step step' view :=
  bounded.map

/-- **Nondeterministic support is the existence of an abstract system for which
the view is a bounded morphism.** -/
theorem relSupports_iff_exists_isBoundedMorphism :
    RelSupports view step ↔ ∃ step' : Y → Y → Prop, IsBoundedMorphism step step' view := by
  constructor
  · rintro ⟨step', forth, back⟩
    exact ⟨step', ⟨fun x x' moved => forth x x' moved, fun x y' moved => back x y' moved⟩⟩
  · rintro ⟨step', bounded⟩
    exact ⟨step', fun _ _ moved => bounded.map moved, fun _ _ moved => bounded.lift moved⟩

/-- **Nondeterministic support is the existence of a covered operational
translation over the view.** -/
theorem relSupports_iff_exists_coveredTranslation :
    RelSupports view step ↔ ∃ step' : Y → Y → Prop,
      ∃ τ : CoveredTranslation (transitionSystem step) (transitionSystem step'),
        τ.mapTerm = view := by
  rw [relSupports_iff_exists_isBoundedMorphism]
  exact exists_congr fun _ => exists_coveredTranslation_iff.symm

/-- **The kernel condition of the scope algebra is bisimulation of the
kernel.** -/
theorem kernelBisimulation_iff_isBisimulation :
    KernelBisimulation view step ↔ IsBisimulation step step fun x x' => view x = view x' := by
  constructor
  · intro kernel x x' same
    refine ⟨fun y moved => ?_, fun y' moved => ?_⟩
    · obtain ⟨z, moved', sameView⟩ := kernel same moved
      exact ⟨z, moved', sameView.symm⟩
    · obtain ⟨z, moved', sameView⟩ := kernel same.symm moved
      exact ⟨z, moved', sameView⟩
  · intro bisimulation x₀ x same x₀' moved
    obtain ⟨x', moved', sameView⟩ := (bisimulation same).1 x₀' moved
    exact ⟨x', moved', sameView.symm⟩

/-- A supported nondeterministic update: every state is bisimilar to every
state with the same view. -/
theorem KernelBisimulation.bisimilar (kernel : KernelBisimulation view step) {x x' : X}
    (same : view x = view x') : Bisimilar step step x x' :=
  (kernelBisimulation_iff_isBisimulation.mp kernel).bisimilar same

end Bisimulation

/-! ## Deterministic updates: complete abstraction -/

section Deterministic

variable {view : X → Y} {f : X → X} {f' : Y → Y}

/-- **For deterministic updates, a functional simulation is the commuting
update square.** -/
theorem preservesEdges_update_iff :
    PreservesEdges (fun x x' => f x = x') (fun y y' => f' y = y') view ↔
      ∀ x, view (f x) = f' (view x) := by
  constructor
  · intro preserves x
    exact (preserves (rfl : f x = f x)).symm
  · rintro commutes x _ rfl
    exact (commutes x).symm

/-- **For deterministic updates, forth implies back**: the commuting square
is already a bounded morphism. -/
theorem isBoundedMorphism_update_iff :
    IsBoundedMorphism (fun x x' => f x = x') (fun y y' => f' y = y') view ↔
      ∀ x, view (f x) = f' (view x) := by
  constructor
  · intro bounded
    exact preservesEdges_update_iff.mp bounded.map
  · intro commutes
    refine ⟨preservesEdges_update_iff.mpr commutes, ?_⟩
    rintro x _ rfl
    exact ⟨f x, rfl, commutes x⟩

/-- **A view supports a deterministic update exactly when the view is a
bounded morphism onto some deterministic abstract system.** -/
theorem supports_iff_exists_isBoundedMorphism :
    Supports view f ↔ ∃ f' : Y → Y,
      IsBoundedMorphism (fun x x' => f x = x') (fun y y' => f' y = y') view :=
  (squareCloses_iff view view f).trans
    (exists_congr fun _ => isBoundedMorphism_update_iff.symm)

/-! ### Completeness on the collecting semantics -/

/-- **Backward completeness** of the image abstraction for the image of `f`:
some abstract transformer `f♯` on sets of views satisfies
`α (f '' S) = f♯ (α S)` for every set of states, where `α S = view '' S`. -/
def BackwardComplete (view : X → Y) (f : X → X) : Prop :=
  ∃ abstract : Set Y → Set Y, ∀ S : Set X, view '' (f '' S) = abstract (view '' S)

/-- The best correct approximation `α ∘ f ∘ γ`, with `γ` the preimage. -/
def bestApproximation (view : X → Y) (f : X → X) (T : Set Y) : Set Y :=
  view '' (f '' (view ⁻¹' T))

/-- The image of a singleton, without the classical `Set.image_singleton`. -/
theorem image_singleton_eq {α β : Type*} (g : α → β) (a : α) :
    g '' ({a} : Set α) = {g a} :=
  Set.ext fun _ => ⟨fun ⟨_, (member : _ = a), image⟩ => image.symm.trans (congrArg g member),
    fun (member : _ = g a) => ⟨a, rfl, member.symm⟩⟩

/-- **Backward completeness is fibre constancy of the updated view**, with
the best correct approximation as witness; both directions are
constructive. -/
theorem backwardComplete_iff_constantOnFibers :
    BackwardComplete view f ↔ ConstantOnFibers view fun x => view (f x) := by
  constructor
  · rintro ⟨abstract, complete⟩ x x' same
    have images : view '' ({x} : Set X) = view '' {x'} := by
      rw [image_singleton_eq, image_singleton_eq, same]
    have member : view (f x) ∈ view '' (f '' {x'}) := by
      rw [complete, ← images, ← complete]
      exact ⟨f x, ⟨x, rfl, rfl⟩, rfl⟩
    obtain ⟨_, ⟨z, (atPoint : z = x'), rfl⟩, equal⟩ := member
    subst atPoint
    exact equal.symm
  · intro constant
    refine ⟨bestApproximation view f, fun S => ?_⟩
    ext y
    constructor
    · rintro ⟨_, ⟨x, member, rfl⟩, rfl⟩
      exact ⟨f x, ⟨x, ⟨x, member, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, ⟨s, member, same⟩, rfl⟩, rfl⟩
      exact ⟨f s, ⟨s, member, rfl⟩, constant s x same⟩

/-- **A supported update is backward complete.** -/
theorem Supports.backwardComplete (supported : Supports view f) : BackwardComplete view f :=
  backwardComplete_iff_constantOnFibers.mpr supported.constantOnFibers

/-- **For a surjective view, support is backward completeness.**  The
converse direction chooses representatives, through `squareCloses_iff_constant`. -/
theorem supports_iff_backwardComplete (surjective : Function.Surjective view) :
    Supports view f ↔ BackwardComplete view f :=
  (squareCloses_iff_constant surjective view f).trans
    backwardComplete_iff_constantOnFibers.symm

/-- The predecessor transformer of a transition relation. -/
def pre (step : X → X → Prop) (S : Set X) : Set X :=
  {x | ∃ x', step x x' ∧ x' ∈ S}

/-- A set of states is a union of fibres of the view. -/
def FibreClosed (view : X → Y) (S : Set X) : Prop :=
  ∀ ⦃x x'⦄, view x = view x' → x ∈ S → x' ∈ S

/-- **Forward completeness of the partition abstraction for the predecessor
transformer**: unions of fibres are sent to unions of fibres. -/
def ForwardCompletePre (view : X → Y) (step : X → X → Prop) : Prop :=
  ∀ S, FibreClosed view S → FibreClosed view (pre step S)

/-- **The partition abstraction is forward complete for the predecessor
transformer exactly when the kernel of the view is a bisimulation.** -/
theorem forwardCompletePre_iff_kernelBisimulation {step : X → X → Prop} :
    ForwardCompletePre view step ↔ KernelBisimulation view step := by
  constructor
  · intro complete x₀ x same x₀' moved
    have closed : FibreClosed view {z | view z = view x₀'} :=
      fun a b sameView (member : view a = view x₀') =>
        show view b = view x₀' from sameView.symm.trans member
    obtain ⟨x', moved', sameView⟩ := complete _ closed same ⟨x₀', moved, rfl⟩
    exact ⟨x', moved', sameView⟩
  · rintro kernel S closed x x' same ⟨z, moved, member⟩
    obtain ⟨z', moved', sameView⟩ := kernel same moved
    exact ⟨z', moved', closed sameView.symm member⟩

end Deterministic

/-! ## Modal invariance -/

section Modal

open Mettapedia.GSLT.HennessyMilner

/-- The Hennessy–Milner system of a transition system: one label and no
atomic observations. -/
def hmSystem (step : X → X → Prop) : System.{0, 0} (transitionSystem step) where
  Atom := PEmpty
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := Unit
  act _ := step
  act_resp_left := by
    intro _ left right target equal moved
    exact ⟨target, (show left = right from equal) ▸ moved, rfl⟩
  act_resp_right := by
    intro _ source target target' moved equal
    exact (show target = target' from equal) ▸ moved

variable {step : X → X → Prop} {step' : Y → Y → Prop} {view : X → Y}

/-- **Bounded morphisms preserve and reflect every Hennessy–Milner formula.** -/
theorem sat_iff_of_isBoundedMorphism (bounded : IsBoundedMorphism step step' view) :
    ∀ (formula : Formula PEmpty Unit) (x : X),
      (hmSystem step).sat formula x ↔ (hmSystem step').sat formula (view x)
  | .top, _ => Iff.rfl
  | .atom atom, _ => atom.elim
  | .conj left right, x =>
      and_congr (sat_iff_of_isBoundedMorphism bounded left x)
        (sat_iff_of_isBoundedMorphism bounded right x)
  | .neg inner, x => not_congr (sat_iff_of_isBoundedMorphism bounded inner x)
  | .dia _ inner, x => by
      constructor
      · rintro ⟨x', moved, holds⟩
        exact ⟨view x', bounded.map moved, (sat_iff_of_isBoundedMorphism bounded inner x').mp holds⟩
      · rintro ⟨y', moved, holds⟩
        obtain ⟨x', moved', rfl⟩ := bounded.lift moved
        exact ⟨x', moved', (sat_iff_of_isBoundedMorphism bounded inner x').mpr holds⟩

/-- **Functional simulations transfer every negation-free formula forward.** -/
theorem psat_of_preservesEdges (preserves : PreservesEdges step step' view) :
    ∀ (formula : PosFormula PEmpty Unit) (x : X),
      (hmSystem step).psat formula x → (hmSystem step').psat formula (view x)
  | .top, _, _ => trivial
  | .bot, _, holds => holds
  | .atom atom, _, _ => atom.elim
  | .conj left right, x, ⟨holdsLeft, holdsRight⟩ =>
      ⟨psat_of_preservesEdges preserves left x holdsLeft,
        psat_of_preservesEdges preserves right x holdsRight⟩
  | .disj left right, x, holds => holds.elim
      (fun holdsLeft => Or.inl (psat_of_preservesEdges preserves left x holdsLeft))
      (fun holdsRight => Or.inr (psat_of_preservesEdges preserves right x holdsRight))
  | .dia _ inner, _, ⟨x', moved, holds⟩ =>
      ⟨view x', preserves moved, psat_of_preservesEdges preserves inner x' holds⟩

end Modal

/-! ### Control: a spurious mind transition -/

namespace Spurious

open Mettapedia.GSLT.HennessyMilner

/-- The world state has no transition; the mind state has a loop. -/
abbrev world : PUnit.{1} → PUnit.{1} → Prop :=
  HSet.isolated

/-- The mind's loop. -/
abbrev mind : PUnit.{1} → PUnit.{1} → Prop :=
  HSet.selfLoop

/-- **The identity is a functional simulation of the world by the mind.** -/
theorem simulation : PreservesEdges world mind id :=
  HSet.preservesEdges_isolatedToLoop

/-- It is the term map of an operational translation. -/
theorem operational :
    ∃ τ : OperationalTranslation (transitionSystem world) (transitionSystem mind),
      τ.mapTerm = id :=
  exists_operationalTranslation_iff.mpr simulation

/-- **It is not a bisimulation**: the mind's loop is not a world transition. -/
theorem not_bisimulation : ¬ IsBoundedMorphism world mind id :=
  HSet.not_isBoundedMorphism_isolatedToLoop

/-- Hence no covered translation has the identity as its term map. -/
theorem not_covered :
    ¬ ∃ τ : CoveredTranslation (transitionSystem world) (transitionSystem mind),
      τ.mapTerm = id :=
  fun covered => not_bisimulation (exists_coveredTranslation_iff.mp covered)

/-- "No transition": the negation of the diamond of truth. -/
def stuck : Formula PEmpty Unit :=
  .neg (.dia () .top)

/-- **The formula "no transition" holds at the world state and fails at its
image**: simulation does not transfer negative formulas. -/
theorem formula_separates :
    (hmSystem world).sat stuck PUnit.unit ∧ ¬ (hmSystem mind).sat stuck PUnit.unit :=
  ⟨fun ⟨_, moved, _⟩ => moved, fun holds => holds ⟨PUnit.unit, trivial, trivial⟩⟩

end Spurious

/-! ## Update squares are operational translations -/

section Square

variable {view : X → Y} {f : X → X} {f' : Y → Y}

/-- **An update square commutes exactly when the view is the term map of an
operational translation between the two update systems.** -/
theorem square_iff_exists_operationalTranslation :
    (∀ x, view (f x) = f' (view x)) ↔
      ∃ τ : OperationalTranslation (updateSystem f) (updateSystem f'), τ.mapTerm = view :=
  preservesEdges_update_iff.symm.trans exists_operationalTranslation_iff.symm

end Square

/-! ### Control from the observer stages -/

section Controls

open Mettapedia.GSLT.EliminatorObservers
open Mettapedia.GSLT.AdmissibleContextCongruence

/-- **Observation by evaluation admits no covered translation for root
β-reduction**: the eliminator stage view of booleans is not a bounded
morphism onto any abstract system. -/
theorem eliminators_no_coveredTranslation :
    ¬ ∃ step' : _ → _ → Prop,
      ∃ τ : CoveredTranslation (transitionSystem RootBeta) (transitionSystem step'),
        τ.mapTerm = AdmissibleClass.stageClass observations eliminators :=
  fun covered => Eliminators.eliminators_not_relSupports_rootBeta
    (relSupports_iff_exists_coveredTranslation.mpr covered)

end Controls

end Mettapedia.GSLT.Scope
