import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentControls

/-!
# The non-dependent fibre of the dependent helper step

**A full sub-instance** (`Frames.restrict`): the frames satisfying a predicate, with all judged
terms and morphisms between them, form a category of frames with the same action and equivalence.
Solvability and asks are taken over the frames inside only. A principal answer inside is principal
for the sub-instance (`Frames.Principal.restrict`), so at a store with a principal answer inside,
solvability and asks of equality guards are the same in the sub-instance and in the whole instance
(`restrict_solvable_iff_of_principal`, `restrict_entails_models_iff_of_principal`).

**Simple frames** (`Simple`): telescopes none of whose types mention a variable. A helper of a
closed type keeps a simple frame simple (`simple_extend`). The **simple step** (`simpleStep`) is the
helper step restricted to simple frames and closed helper types, with its admission computed in the
simple sub-instance.

**The fibre theorem** (`simpleStep_admits_iff`): a firing of the simple step is admitted exactly
when its underlying dependent firing is admitted, whenever the knowledge has a principal answer at
a simple frame. That hypothesis holds at a simple frame with no knowledge (`principalInside_nil`) and
is kept by every helper firing (`principalInside_after`), so along every run from such a state the
simple fibre decides admission exactly as the dependent step does (`admits_iff_along`).

Controls: the consumer's firings have closed types and are admitted in the fibre
(`Consumer.first_fibre`); the dependent firing `y : Id (g → g) x x` leaves the fibre: the frame it
makes is not simple (`Consumer.dependent_leaves_fibre`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)

namespace Frames

universe uO uT uH

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

variable (X : Frames Tm Hom) (Inside : Obj → Prop) in
/-- **The full sub-instance on the frames inside.** -/
def restrict : Frames (fun a : {a : Obj // Inside a} => Tm a.1) (fun a b => Hom a.1 b.1) where
  E s t := X.E s t
  equivalence a := X.equivalence a.1
  act f t := X.act f t
  id a := X.id a.1
  comp g f := X.comp g f
  act_id t := X.act_id t
  act_comp g f t := X.act_comp g f t
  preserves := @fun _ _ f _ _ same => X.preserves f same

variable {X : Frames Tm Hom} {Inside : Obj → Prop}

theorem restrict_solvable {a : {a : Obj // Inside a}} {store : EquationStore (Tm a.1)}
    (solvable : (X.restrict Inside).Solvable (a := a) store) : X.Solvable store := by
  obtain ⟨b, f, solved⟩ := solvable
  exact ⟨b.1, f, solved⟩

/-- An ask over every frame is an ask over the frames inside. -/
theorem Entails.restrict {a : {a : Obj // Inside a}} {store : EquationStore (Tm a.1)}
    {observation : (b : Obj) → Hom a.1 b → Prop} (asked : X.Entails store observation) :
    (X.restrict Inside).Entails (a := a) store (fun b f => observation b.1 f) :=
  fun b f solved => asked b.1 f solved

/-- **A principal answer inside is principal for the sub-instance.** -/
theorem Principal.restrict {a : {a : Obj // Inside a}} {m : Obj} (inside : Inside m)
    {store : EquationStore (Tm a.1)} {answer : Hom a.1 m} (principal : X.Principal store answer) :
    (X.restrict Inside).Principal (a := a) (m := ⟨m, inside⟩) store answer :=
  ⟨principal.sound, fun b f solved => principal.factors b.1 f solved⟩

/-- **Solvability is preserved and reflected** at a store with a principal answer inside. -/
theorem restrict_solvable_iff_of_principal {a : {a : Obj // Inside a}} {m : Obj} (inside : Inside m)
    {store : EquationStore (Tm a.1)} {answer : Hom a.1 m} (principal : X.Principal store answer) :
    (X.restrict Inside).Solvable (a := a) store ↔ X.Solvable store :=
  ⟨restrict_solvable, fun _ => (principal.restrict inside).solvable⟩

/-- **Asks of equality guards are preserved and reflected** at a store with a principal answer
inside: both are the guards at the answer. -/
theorem restrict_entails_models_iff_of_principal {a : {a : Obj // Inside a}} {m : Obj}
    (inside : Inside m) {store : EquationStore (Tm a.1)} {answer : Hom a.1 m}
    (principal : X.Principal store answer) (guards : EquationStore (Tm a.1)) :
    (X.restrict Inside).Entails (a := a) store (fun _ f => (X.restrict Inside).Models f guards) ↔
      X.Entails store (fun _ f => X.Models f guards) :=
  ((principal.restrict inside).entails_models_iff guards).trans
    (principal.entails_models_iff guards).symm

end Frames

namespace Dependent

open _root_.CategoryTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveContextual

variable {Head : Type} {rules : Rules Head}

/-! ## Simple frames -/

/-- Telescopes none of whose entries mentions a variable: each entry is a closed term read in the
telescope before it. -/
inductive ClosedEntries : {n : Nat} → Ctx Head n → Prop
  | nil : ClosedEntries .nil
  | snoc {n : Nat} {Γ : Ctx Head n} (T : Tm Head 0) (σ : Sub Head 0 n) :
      ClosedEntries Γ → ClosedEntries (.snoc Γ (subst σ T))

/-- The newest entry of a telescope with closed entries is a closed term read in the telescope. -/
theorem ClosedEntries.last {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} (closed : ClosedEntries (.snoc Γ A)) :
    ∃ (T : Tm Head 0) (σ : Sub Head 0 n), A = subst σ T := by
  cases closed with
  | snoc T σ _ => exact ⟨T, σ, rfl⟩

/-- **A simple frame**: no type of its telescope depends on a variable. -/
def Simple (Γ : Context rules) : Prop := ClosedEntries Γ.raw

theorem simple_empty : Simple (empty rules) := .nil

/-- **A helper of a closed type keeps a simple frame simple.** -/
theorem simple_extend {Γ : Context rules} (simple : Simple Γ) (T : TypeOver (empty rules)) :
    Simple (extend Γ (T.reindex (toEmpty Γ))) :=
  .snoc T.code (toEmpty Γ).substitution simple

variable (rules) in
/-- **The simple fibre of the dependent frames.** -/
abbrev simpleFrames := (frames rules).restrict Simple

/-! ## The simple step -/

variable (rules) (O : Type)

/-- A state of the simple step: a state of the dependent helper step at a simple frame. -/
structure SimpleState where
  state : State rules O
  simple : Simple state.frame

variable {rules O}

/-- A firing of the simple step: a dependent helper firing whose helper type is closed. -/
structure SimpleFiring (s : SimpleState rules O) where
  firing : Firing s.state
  closedType : TypeOver (empty rules)
  closed : firing.helper = closedType.reindex (toEmpty s.state.frame)

/-- The frame a simple firing makes is simple. -/
theorem SimpleFiring.simple_after {s : SimpleState rules O} (f : SimpleFiring s) :
    Simple (extend s.state.frame f.firing.helper) := by
  rw [f.closed]
  exact simple_extend s.simple f.closedType

variable [DecidableEq O]

/-- **The simple step**: the dependent helper step on simple frames with closed helper types, its
solvability and asks taken over simple frames only. -/
abbrev simpleStep : Interface.Step.Standard (simpleFrames rules) O (SimpleState rules O) SimpleFiring where
  frame s := ⟨s.state.frame, s.simple⟩
  knowledge s := s.state.knowledge
  present s := s.state.present
  selection f := f.firing.selection
  target f := ⟨extend _ f.firing.helper, f.simple_after⟩
  extension f := projectionHom _ f.firing.helper
  information f := f.firing.information
  transported := by
    intro s f e member
    exact List.mem_append_left _ (List.mem_map.mpr ⟨e, member, rfl⟩)
  Shapes f := f.firing.selection.made.Nodup
  Holds {s} f _ σ := (frames rules).Models ((frames rules).comp σ (projectionHom s.state.frame f.firing.helper))
    f.firing.guards
  Admits {s} f := f.firing.selection.made.Nodup ∧
    Enabled (fun _ : O => ()) s.state.present (f.firing.selection.commit (T := Unit)) ∧
    (simpleFrames rules).Solvable (a := ⟨extend _ f.firing.helper, f.simple_after⟩) f.firing.information ∧
    (simpleFrames rules).Entails (a := ⟨extend _ f.firing.helper, f.simple_after⟩) f.firing.information
      fun _ σ => (frames rules).Models ((frames rules).comp σ (projectionHom s.state.frame f.firing.helper))
        f.firing.guards
  admits_iff _ := Iff.rfl
  preparedResult f _ := ⟨f.firing.after, f.simple_after⟩
  present_preparedResult _ _ := rfl
  preparedSettle f _ := (frames rules).id (extend _ f.firing.helper)
  knowledge_preparedResult f _ := (Frames.applyStore_id (X := frames rules) f.firing.information).symm

omit [DecidableEq O] in
/-- The knowledge has a principal answer at a simple frame. -/
def PrincipalInside (s : State rules O) : Prop :=
  ∃ (M : Context rules) (m : M ⟶ s.frame), Simple M ∧ (frames rules).Principal (a := s.frame) (m := M) s.knowledge m

omit [DecidableEq O] in
/-- No knowledge at a simple frame has the identity as a principal answer. -/
theorem principalInside_nil {Γ : Context rules} (simple : Simple Γ) (present : Finset O) :
    PrincipalInside (⟨Γ, [], present⟩ : State rules O) :=
  ⟨Γ, 𝟙 Γ, simple, principal_nil Γ⟩

/-- **Every helper firing keeps a principal answer at a simple frame**, at the same frame. -/
theorem principalInside_after {s : State rules O} (f : Firing s) (principal : PrincipalInside s) :
    PrincipalInside f.after := by
  obtain ⟨M, m, simple, answer⟩ := principal
  exact ⟨M, m ≫ instantiate s.frame f.value, simple, principal_definition f.value answer⟩

/-- **The fibre theorem**: a firing of the simple step is admitted exactly when its underlying
dependent firing is admitted, when the knowledge has a principal answer at a simple frame. -/
theorem simpleStep_admits_iff {s : SimpleState rules O} (f : SimpleFiring s)
    (principal : PrincipalInside s.state) :
    (simpleStep (rules := rules) (O := O)).Admits f ↔ (helperStep (rules := rules)).Admits f.firing := by
  obtain ⟨M, m, simple, answer⟩ := principal
  have information := principal_definition f.firing.value answer
  have holds : ∀ {b : Context rules} (σ : b ⟶ extend s.state.frame f.firing.helper),
      (frames rules).Models ((frames rules).comp σ (projectionHom s.state.frame f.firing.helper))
          f.firing.guards ↔
        (frames rules).Models σ
          ((frames rules).applyStore (projectionHom s.state.frame f.firing.helper) f.firing.guards) :=
    fun σ => (Frames.models_applyStore (X := frames rules) _ σ _).symm
  have solvable := Frames.restrict_solvable_iff_of_principal (Inside := Simple)
    (a := ⟨extend s.state.frame f.firing.helper, f.simple_after⟩) simple information
  have asks := Frames.restrict_entails_models_iff_of_principal (Inside := Simple)
    (a := ⟨extend s.state.frame f.firing.helper, f.simple_after⟩) simple information
    ((frames rules).applyStore (projectionHom s.state.frame f.firing.helper) f.firing.guards)
  have fibreAsks :
      (simpleFrames rules).Entails (a := ⟨extend _ f.firing.helper, f.simple_after⟩) f.firing.information
          (fun _ σ => (frames rules).Models ((frames rules).comp σ (projectionHom s.state.frame f.firing.helper))
            f.firing.guards) ↔
        (frames rules).Entails f.firing.information
          (fun _ σ => (frames rules).Models ((frames rules).comp σ (projectionHom s.state.frame f.firing.helper))
            f.firing.guards) :=
    ⟨fun asked => (asks.mp fun b σ solved => (holds σ).mp (asked b σ solved)).mono
        fun _ σ moved => (holds σ).mpr moved,
      fun asked b σ solved => asked b.1 σ solved⟩
  exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr solvable fibreAsks))

/-- **Along every run from a simple frame with no knowledge, the simple fibre decides admission as
the dependent step does**: at every state that keeps a principal answer at a simple frame. -/
theorem admits_iff_along {s : SimpleState rules O} (f : SimpleFiring s)
    (start : ∃ (Γ : Context rules) (present : Finset O) (r : (helperStep (rules := rules)).Run
      (⟨Γ, [], present⟩ : State rules O)), Simple Γ ∧ r.last = s.state) :
    (simpleStep (rules := rules) (O := O)).Admits f ↔ (helperStep (rules := rules)).Admits f.firing := by
  obtain ⟨Γ, present, r, simple, last⟩ := start
  refine simpleStep_admits_iff f ?_
  rw [← last]
  have reach : ∀ {t : State rules O} (run : (helperStep (rules := rules)).Run t),
      PrincipalInside t → PrincipalInside run.last := by
    intro t run
    induction run with
    | nil _ => exact id
    | cons g _ _ ih => exact fun principal => ih (principalInside_after g principal)
  exact reach r (principalInside_nil simple present)

/-! ## Controls -/

namespace Consumer

/-- The empty frame, as a state of the simple step. -/
def simpleStart : SimpleState tiny Nat := ⟨start, simple_empty⟩

/-- The firing that makes `x : g → g`, as a firing of the simple step. -/
def simpleFirst : SimpleFiring simpleStart :=
  ⟨first, arrowType, (TypeOver.reindex_id arrowType).symm.trans
    (congrArg arrowType.reindex (toEmpty_unique _ _))⟩

/-- **The consumer's first firing runs in the fibre**, admitted there as in the dependent step. -/
theorem first_fibre : (simpleStep (rules := tiny) (O := Nat)).Admits simpleFirst :=
  (simpleStep_admits_iff simpleFirst (principalInside_nil simple_empty ∅)).mpr first_admitted

/-- **The dependent firing leaves the fibre**: the frame `x : g → g, y : Id (g → g) x x` is not
simple. -/
theorem dependent_leaves_fibre : ¬ Simple (extend first.after.frame dependent.helper) := by
  intro simple
  obtain ⟨T, σ, closed⟩ := ClosedEntries.last simple
  apply dependent_not_weakened T
  rw [closed]
  have same : subst (projection (Head := TinyHead) (n := 0)) T = subst σ T :=
    congrArg (fun τ => subst τ T) (funext fun i => i.elim0)
  rw [subst_projection] at same
  exact same

end Consumer

end Dependent

#print axioms Frames.restrict
#print axioms Frames.Principal.restrict
#print axioms Frames.restrict_solvable_iff_of_principal
#print axioms Frames.restrict_entails_models_iff_of_principal
#print axioms Dependent.simple_extend
#print axioms Dependent.principalInside_after
#print axioms Dependent.simpleStep_admits_iff
#print axioms Dependent.admits_iff_along
#print axioms Dependent.Consumer.first_fibre
#print axioms Dependent.Consumer.dependent_leaves_fibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
