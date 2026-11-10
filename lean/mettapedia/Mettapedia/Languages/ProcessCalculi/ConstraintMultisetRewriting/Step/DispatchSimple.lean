import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Dispatch
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentPacking

/-!
# Dispatch from the dependent helper step to its simple fibre

**The edge** (`Frames.inclusion`): a full sub-instance included in the whole instance. Terms and
morphisms are kept; what changes is that the source quantifies only over the frames inside, so a
source answer is a claim about fewer solutions. The inclusion reflects the equivalence.

**When it is licensed.**
* **At a store with a principal answer inside** (`inclusion_coversAt_of_principal`): every solution
  factors through that answer, which is a source solution.
* **At every store, when every frame has a retract inside** (`inclusion_coversAt_of_retracts`,
  `inclusion_licensed_of_retracts`): a solution into any frame is the retraction of a solution into
  a frame inside.

**The simple fibre** (`simpleInclusion`): the simple frames inside the dependent frames. A firing
of the simple step is a dispatched firing of the dependent helper step (`simpleDispatched`), so:
* along helper runs, where the knowledge keeps a principal answer at a simple frame, the helper
  step's admission is decided in the simple fibre (`helper_admits_iff_simple_of_principalInside`);
* when the universe heads have joins, the inclusion is licensed on every store
  (`simpleInclusion_licensed_of_joins`), the helper step's admission is decided in the simple fibre
  for every store (`helper_admits_iff_simple_of_joins`), and a principal answer found in the simple
  fibre gives the helper step's admission by its guards (`helper_admits_iff_of_simple_principal`).

Controls over `Consumer.tiny`, whose universe has joins: the consumer's first firing is admitted
from the simple fibre's own principal answer (`Consumer.first_dispatched`); the simple fibre's
refutation of an ill-typed equation is a refutation in the dependent frames
(`Consumer.illTyped_dispatched`), and a firing from the state that knows it is refused by dispatch
(`Consumer.illFiring_refused`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)

universe uO uT uH

namespace Frames

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

variable (X : Frames Tm Hom) (Inside : Obj → Prop) in
/-- **The inclusion of a full sub-instance** into the whole instance. -/
def inclusion : Translation.FrameMap (X.restrict Inside) X where
  obj a := a.1
  tm t := t
  hom f := f
  act _ _ := (X.equivalence _).refl _
  preserves same := same

variable {X : Frames Tm Hom} {Inside : Obj → Prop}

theorem inclusion_reflects : (X.inclusion Inside).Reflects := fun same => same

theorem inclusion_store {a : {a : Obj // Inside a}} (K : EquationStore (Tm a.1)) :
    (X.inclusion Inside).store K = K := by
  simp [Translation.FrameMap.store, inclusion]

/-- **A principal answer inside covers.** -/
theorem inclusion_coversAt_of_principal {a : {a : Obj // Inside a}} {K : EquationStore (Tm a.1)}
    {m : Obj} (inside : Inside m) {answer : Hom a.1 m} (principal : X.Principal K answer) :
    (X.inclusion Inside).CoversAt K := by
  intro b τ solved
  rw [inclusion_store] at solved
  obtain ⟨residual, through⟩ := principal.factors b τ solved
  exact ⟨⟨m, inside⟩, answer, residual, principal.sound, through⟩

theorem retract_factor {a b c : Obj} (τ : Hom a b) {down : Hom b c} {up : Hom c b}
    (retract : ∀ t : Tm b, X.E (X.act (X.comp up down) t) t) (t : Tm a) :
    X.E (X.act τ t) (X.act (X.comp up (X.comp down τ)) t) := by
  rw [X.act_comp, X.act_comp, ← X.act_comp up down]
  exact (X.equivalence b).symm (retract (X.act τ t))

/-- **Retracts everywhere cover every store.** -/
theorem inclusion_coversAt_of_retracts (retracts : ∀ b, HasRetract X Inside b)
    {a : {a : Obj // Inside a}} (K : EquationStore (Tm a.1)) : (X.inclusion Inside).CoversAt K := by
  intro b τ solved
  rw [inclusion_store] at solved
  obtain ⟨c, inside, down, up, retract⟩ := retracts b
  exact ⟨⟨c, inside⟩, X.comp down τ, up, models_comp solved down,
    fun t => retract_factor (a := a.1) τ retract t⟩

/-- **With retracts everywhere the inclusion is licensed on every store.** -/
theorem inclusion_licensed_of_retracts (retracts : ∀ b, HasRetract X Inside b) :
    (X.inclusion Inside).Licensed :=
  fun _ K => (inclusion_coversAt_of_retracts retracts K).licensedAt

end Frames

namespace Dependent

open _root_.CategoryTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveContextual

variable {Head : Type} {rules : Rules Head} {O : Type} [DecidableEq O]

variable (rules) in
/-- **The simple fibre inside the dependent frames.** -/
abbrev simpleInclusion := (frames rules).inclusion Simple

/-- **A simple firing is a dispatched firing of the dependent helper step.** -/
def simpleDispatched {s : SimpleState rules O} (f : SimpleFiring s) :
    (simpleInclusion rules).Dispatched (helperStep (rules := rules) (O := O)).toStep f.firing where
  source := ⟨extend s.state.frame f.firing.helper, f.simple_after⟩
  frame := rfl
  problem := f.firing.information
  guards := (frames rules).applyStore (projectionHom s.state.frame f.firing.helper) f.firing.guards
  information := by
    intro b g
    show (frames rules).Models g f.firing.information ↔ (frames rules).Models g
      ((simpleInclusion rules).store (a := ⟨extend s.state.frame f.firing.helper, f.simple_after⟩)
        f.firing.information)
    rw [Frames.inclusion_store]
  holds := by
    intro b g
    show (frames rules).Models ((frames rules).comp g (projectionHom s.state.frame f.firing.helper))
        f.firing.guards ↔ (frames rules).Models g
      ((simpleInclusion rules).store (a := ⟨extend s.state.frame f.firing.helper, f.simple_after⟩)
        ((frames rules).applyStore (projectionHom s.state.frame f.firing.helper) f.firing.guards))
    rw [Frames.inclusion_store]
    exact (Frames.models_applyStore (X := frames rules) _ g _).symm

/-- **Along helper runs the simple fibre decides admission**: when the knowledge has a principal
answer at a simple frame, the helper step admits a simple firing exactly when the simple fibre
finds its information solvable and asks its guards. -/
theorem helper_admits_iff_simple_of_principalInside {s : SimpleState rules O} (f : SimpleFiring s)
    (principal : PrincipalInside s.state) :
    (helperStep (rules := rules)).Admits f.firing ↔ f.firing.selection.made.Nodup ∧
      Enabled (fun _ : O => ()) s.state.present (f.firing.selection.commit (T := Unit)) ∧
      (simpleFrames rules).Solvable (a := ⟨extend _ f.firing.helper, f.simple_after⟩)
        f.firing.information ∧
      (simpleFrames rules).Entails (a := ⟨extend _ f.firing.helper, f.simple_after⟩)
        f.firing.information (fun _ g => (simpleFrames rules).Models g
          ((frames rules).applyStore (projectionHom s.state.frame f.firing.helper) f.firing.guards)) := by
  obtain ⟨M, m, simple, answer⟩ := principal
  exact Translation.FrameMap.dispatch_admits_iff_of_coversAt Frames.inclusion_reflects _
    (simpleDispatched f)
    (Frames.inclusion_coversAt_of_principal simple (principal_definition f.firing.value answer))

section Joins

variable (joins : ∀ {u v : Head}, rules.isUniverse u → rules.isUniverse v →
  ∃ w, rules.join u v w ∧ rules.isUniverse w)

include joins

/-- **With joins the simple fibre is licensed on every store.** -/
theorem simpleInclusion_licensed_of_joins : (simpleInclusion rules).Licensed :=
  Frames.inclusion_licensed_of_retracts (simple_retracts joins)

/-- **With joins the simple fibre decides the helper step's admission for every store.** -/
theorem helper_admits_iff_simple_of_joins {s : SimpleState rules O} (f : SimpleFiring s) :
    (helperStep (rules := rules)).Admits f.firing ↔ f.firing.selection.made.Nodup ∧
      Enabled (fun _ : O => ()) s.state.present (f.firing.selection.commit (T := Unit)) ∧
      (simpleFrames rules).Solvable (a := ⟨extend _ f.firing.helper, f.simple_after⟩)
        f.firing.information ∧
      (simpleFrames rules).Entails (a := ⟨extend _ f.firing.helper, f.simple_after⟩)
        f.firing.information (fun _ g => (simpleFrames rules).Models g
          ((frames rules).applyStore (projectionHom s.state.frame f.firing.helper) f.firing.guards)) :=
  Translation.FrameMap.dispatch_admits_iff_of_coversAt Frames.inclusion_reflects _
    (simpleDispatched f) (Frames.inclusion_coversAt_of_retracts (simple_retracts joins) _)

/-- **A principal answer of the simple fibre gives the helper step's admission**: its guards at
the answer. -/
theorem helper_admits_iff_of_simple_principal {s : SimpleState rules O} (f : SimpleFiring s)
    {m : {Γ : Context rules // Simple Γ}} {answer : m.1 ⟶ extend s.state.frame f.firing.helper}
    (principal : (simpleFrames rules).Principal (a := ⟨extend _ f.firing.helper, f.simple_after⟩)
      (m := m) f.firing.information answer) :
    (helperStep (rules := rules)).Admits f.firing ↔ f.firing.selection.made.Nodup ∧
      Enabled (fun _ : O => ()) s.state.present (f.firing.selection.commit (T := Unit)) ∧
      (frames rules).Models answer
        ((frames rules).applyStore (projectionHom s.state.frame f.firing.helper) f.firing.guards) :=
  Translation.FrameMap.dispatch_admits_iff_of_principal Frames.inclusion_reflects _
    (simpleDispatched f) (simpleInclusion_licensed_of_joins joins _ _) principal

end Joins

/-! ## Controls -/

namespace Consumer

/-- **Commit control**: the consumer's first firing is admitted by the helper step, from the simple
fibre's own principal answer: no knowledge, a definition, at simple frames only. -/
theorem first_dispatched : (helperStep (rules := tiny)).Admits first := by
  have principal := principal_definition first.value (principal_nil (empty tiny))
  have inside := Frames.Principal.restrict (Inside := Simple)
    (a := ⟨extend _ simpleFirst.firing.helper, simpleFirst.simple_after⟩) simple_empty principal
  refine (helper_admits_iff_of_simple_principal tiny_joins simpleFirst inside).mpr
    ⟨List.nodup_singleton _, (enabled_iff first).mpr (by decide), Frames.models_nil _⟩

/-- The frame `y : g` is simple. -/
theorem ground_simple : Simple (extend (empty tiny) groundType) := by
  have same : groundType.reindex (toEmpty (empty tiny)) = groundType :=
    ((TypeOver.reindex_id groundType).symm.trans (congrArg groundType.reindex (toEmpty_unique _ _))).symm
  have simple := simple_extend simple_empty groundType
  rw [same] at simple
  exact simple

/-- The ill-typed equation `y ≐ λx.x` at the frame `y : g`. -/
def illStore : EquationStore (Entry (extend (empty tiny) groundType)) :=
  [(Entry.last (empty tiny) groundType, identityEntry.reindex (projectionHom _ groundType))]

/-- **Refutation control**: the simple fibre refutes the ill-typed equation, and the license turns
that refutation into a refutation in the dependent frames. -/
theorem illTyped_dispatched :
    ¬ (simpleFrames tiny).Solvable (a := ⟨_, ground_simple⟩) illStore ∧
      ¬ (frames tiny).Solvable ((simpleInclusion tiny).store (a := ⟨_, ground_simple⟩) illStore) := by
  have refuted : ¬ (simpleFrames tiny).Solvable (a := ⟨_, ground_simple⟩) illStore :=
    fun solvable => illTyped_unsolvable (Frames.restrict_solvable solvable)
  exact ⟨refuted,
    (simpleInclusion_licensed_of_joins tiny_joins ⟨_, ground_simple⟩ illStore).refutes refuted⟩

/-- The simple state at the frame `y : g` that knows the ill-typed equation. -/
def illState : SimpleState tiny Nat := ⟨⟨extend (empty tiny) groundType, illStore, ∅⟩, ground_simple⟩

/-- A simple firing there: it makes occurrence `7` and a helper `x : g → g`, valued `λx.x`. -/
def illFiring : SimpleFiring illState :=
  ⟨⟨7, arrowType.reindex (toEmpty _), ⟨.lam (.var 0), identity_typed _⟩, []⟩, arrowType, rfl⟩

/-- **Refutation control at the step**: the simple fibre refutes the firing's information, and
dispatch refuses the firing in the helper step. -/
theorem illFiring_refused : ¬ (helperStep (rules := tiny)).Admits illFiring.firing :=
  Translation.FrameMap.dispatch_refused _ (simpleDispatched illFiring)
    (simpleInclusion_licensed_of_joins tiny_joins _ _)
    fun solvable => illTyped_unsolvable (knowledge_solvable illFiring.firing (Frames.restrict_solvable solvable))

end Consumer

end Dependent

#print axioms Frames.inclusion
#print axioms Frames.inclusion_reflects
#print axioms Frames.inclusion_store
#print axioms Frames.inclusion_coversAt_of_principal
#print axioms Frames.inclusion_coversAt_of_retracts
#print axioms Frames.inclusion_licensed_of_retracts
#print axioms Dependent.simpleDispatched
#print axioms Dependent.helper_admits_iff_simple_of_principalInside
#print axioms Dependent.simpleInclusion_licensed_of_joins
#print axioms Dependent.helper_admits_iff_simple_of_joins
#print axioms Dependent.helper_admits_iff_of_simple_principal
#print axioms Dependent.Consumer.first_dispatched
#print axioms Dependent.Consumer.ground_simple
#print axioms Dependent.Consumer.illTyped_dispatched
#print axioms Dependent.Consumer.illFiring_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
