import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SettlementInstances

/-!
# Prepared steps: the structural effect of a firing without its admission

A `Prestep` computes a firing's result from its shapes. The native step cannot: its result is the
state the solver returns, and the solver returns a state only for solvable information. Obtaining
that result from the native step's own admission asks the guards at **every** solution of the
information; with disequations only the separating solutions count, so a guard made valid by a told
disequation is out of reach of that route (`Controls.disequation_restriction_changes_guard`).
Preparation is the repair: the structural effect of a firing is computed before any guard is asked.

## Preparation (`Prepared`)

A **prepared step** carries a type of preparations of a firing (`Prep`), the structural effect
computed from one (`result`, `settle`, `knowledge_result`), and a preparation of every firing that
is **ready** (its shapes and the physical enabling of its selection, `Ready`) and whose information
is solvable (`prepare`). No guard and no predicate query is asked to prepare.

* **Its step** (`Prepared.step`) admits by the interface's characterization: readiness, solvability
  and the ask, in the base constraint domain (`step_admits_iff`).
* **Every prestep is prepared**, by its shapes (`ofPrestep`), with the same step
  (`ofPrestep_step`).

## Disequations on a prepared step

A prepared step's step tells disequations as every step does (`Interface.Step.withDisequations`):
admission is the interface's characterization in the current constraint domain, and the result is the
prepared result at the readiness and the base solvability that separation implies; the base step's
admission is never asked, and guarded firings keep their guards. Answer coverage holds when every
prepared settlement extends (`SettlementCoverage.withDisequations_coversAnswers`).

## The control (`Controls`)

Over Boolean observations of two-bit worlds, with the guard `x ≠ false` on the first bit `x`:
* the restriction by the disequation `x ≠ false` is satisfiable, and the unrestricted guard is not
  entailed (`disequation_restriction_changes_guard`);
* the base step refuses the guarded firing (`guarded_refused`); with the disequation told, the
  prepared step admits it and computes its result (`apart_admitted`), and covers its answers
  (`guarded_coversAnswers`);
* the guard fails at the solution `x ↦ false` (`guard_not_everywhere`), so a result obtained from the
  base step's admission, which needs the guard at every solution, cannot exist for this firing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PreparedStep

open Interface (Frames)
open Disequality (DisequationStore)
open DisequalityFrames (Frame Morphism frames Separates separates_applyStore separates_append
  separates_congr separates_of_reflects separates_nil solvable_base solvable_iff entails_iff Prestep)
open SettlementCoverage (Extends CoversAnswers coversAnswers_of_extends extends_frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uO uT uH uOcc uS uF uP

/-- **A prepared step**: every part of an instance of the step except admission, with the
structural effect of a firing computed from a preparation of it, which readiness and solvability of
the information already give. -/
structure Prepared {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
    (X : Frames Tm Hom) (O : Type uOcc) [DecidableEq O] (State : Type uS)
    (Firing : State → Type uF) where
  frame : State → Obj
  knowledge : (s : State) → EquationStore (Tm (frame s))
  present : State → Finset O
  selection : {s : State} → Firing s → Selection O
  target : {s : State} → Firing s → Obj
  extension : {s : State} → (f : Firing s) → Hom (frame s) (target f)
  information : {s : State} → (f : Firing s) → EquationStore (Tm (target f))
  transported : ∀ {s : State} (f : Firing s) (e : Equation (Tm (frame s))), e ∈ knowledge s →
    (X.act (extension f) e.1, X.act (extension f) e.2) ∈ information f
  Shapes : {s : State} → Firing s → Prop
  Holds : {s : State} → (f : Firing s) → (b : Obj) → Hom (target f) b → Prop
  /-- The preparations of a firing: what its structural effect is computed from. -/
  Prep : {s : State} → Firing s → Sort uP
  /-- **Preparation asks no guard**: shapes, the physical enabling and solvability prepare. -/
  prepare : ∀ {s : State} (f : Firing s), Shapes f →
    Enabled (fun _ : O => ()) (present s) ((selection f).commit (T := Unit)) →
    X.Solvable (information f) → Prep f
  result : {s : State} → (f : Firing s) → Prep f → State
  present_result : ∀ {s : State} (f : Firing s) (p : Prep f),
    present (result f p) = fire (present s) ((selection f).commit (T := Unit))
  settle : {s : State} → (f : Firing s) → (p : Prep f) → Hom (target f) (frame (result f p))
  knowledge_result : ∀ {s : State} (f : Firing s) (p : Prep f),
    knowledge (result f p) = X.applyStore (settle f p) (information f)

namespace Prepared

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  (Q : Prepared.{uO, uT, uH, uOcc, uS, uF, uP} X O State Firing)

/-- **Readiness**: the shapes and the physical enabling of the selection. -/
def Ready {s : State} (f : Firing s) : Prop :=
  Q.Shapes f ∧ Enabled (fun _ : O => ()) (Q.present s) ((Q.selection f).commit (T := Unit))

/-- **The step of a prepared step**: admission is the interface's characterization, and the result
is prepared from it. -/
def step : Interface.Step.Standard X O State Firing where
  frame := Q.frame
  knowledge := Q.knowledge
  present := Q.present
  selection := Q.selection
  target := Q.target
  extension := Q.extension
  information := Q.information
  transported := Q.transported
  Shapes := Q.Shapes
  Holds := Q.Holds
  Admits {s} f := Q.Shapes f ∧ Enabled (fun _ : O => ()) (Q.present s) ((Q.selection f).commit (T := Unit)) ∧
    X.Solvable (Q.information f) ∧ X.Entails (Q.information f) (Q.Holds f)
  admits_iff _ := Iff.rfl
  preparedResult f p := Q.result f (Q.prepare f p.1 p.2.1 p.2.2)
  present_preparedResult f _ := Q.present_result f _
  preparedSettle f _ := Q.settle f _
  knowledge_preparedResult f _ := Q.knowledge_result f _

/-- **Admission is readiness, solvability and the ask**, in the base constraint domain. -/
theorem step_admits_iff {s : State} (f : Firing s) :
    Q.step.Admits f ↔ Q.Ready f ∧ X.Solvable (Q.information f) ∧ X.Entails (Q.information f) (Q.Holds f) :=
  ⟨fun ⟨shapes, enabled, solvable, asked⟩ => ⟨⟨shapes, enabled⟩, solvable, asked⟩,
    fun ⟨⟨shapes, enabled⟩, solvable, asked⟩ => ⟨shapes, enabled, solvable, asked⟩⟩

end Prepared

/-- **Every prestep is prepared, by its shapes.** -/
def ofPrestep {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
    {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
    (R : Prestep X O State Firing) : Prepared.{uO, uT, uH, uOcc, uS, uF, 0} X O State Firing where
  frame := R.frame
  knowledge := R.knowledge
  present := R.present
  selection := R.selection
  target := R.target
  extension := R.extension
  information := R.information
  transported := R.transported
  Shapes := R.Shapes
  Holds := R.Holds
  Prep f := R.Shapes f
  prepare _ shapes _ _ := shapes
  result := R.result
  present_result := R.present_result
  settle := R.settle
  knowledge_result := R.knowledge_result

/-- **A prestep's step is its prepared step.** -/
theorem ofPrestep_step {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
    {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
    (R : Prestep X O State Firing) : (ofPrestep R).step = R.step :=
  rfl

namespace Prepared

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  (Q : Prepared.{uO, uT, uH, uOcc, uS, uF, uP} X O State Firing)

/-- **The prepared step covers its answers** when every prepared settlement extends. -/
theorem step_coversAnswers
    (extend : ∀ {s : State} (f : Firing s) (p : Q.Prep f), Extends X (Q.settle f p)) :
    CoversAnswers Q.step.toStep := by
  apply coversAnswers_of_extends
  intro _ f admitted
  exact extend f _

end Prepared

/-! ## The control: a guard valid only under a told disequation -/

namespace Controls

open AdmissionObservationCover.Controls (World frame)
open SettlementCoverage (extends_of_retraction)

/-- The first bit, as an observation. -/
def bit : World → Bool := fun w => w 0

/-- The constant `false` observation. -/
def no : World → Bool := fun _ => false

/-- **The guard `x ≠ false`**, at one solution. -/
def nonzero (_ : Unit) (σ : World → World) : Prop :=
  ¬ frame.E (a := ()) (frame.act (a := ()) (b := ()) σ bit) (frame.act (a := ()) (b := ()) σ no)

/-- **Restricting solutions by a disequation can validate a guard the base step refuses**: the
restriction by `x ≠ false` is satisfiable, and the guard `x ≠ false` is not entailed without it. -/
theorem disequation_restriction_changes_guard :
    (∃ σ : World → World, frame.Models (a := ()) (b := ()) σ [] ∧ nonzero () σ) ∧
    ¬ frame.Entails (a := ()) [] nonzero := by
  constructor
  · refine ⟨fun _ _ => true, Frames.models_nil _, ?_⟩
    intro equal
    have point := congrFun equal (fun _ => false)
    cases point
  · intro entailed
    exact entailed () (fun _ _ => false) (Frames.models_nil _) rfl

/-- **The guarded firing**: one state, one firing that takes, reads, makes and tells nothing, with
the guard `x ≠ false`, prepared by its shapes and settled by the identity. -/
def guarded : Prepared.{0, 0, 0, 0, 0, 0, 0} frame Nat Unit (fun _ => Unit) where
  frame _ := ()
  knowledge _ := []
  present _ := ∅
  selection _ := ⟨[], [], []⟩
  target _ := ()
  extension _ := id
  information _ := []
  transported _ _ member := False.elim (List.not_mem_nil member)
  Shapes _ := ([] : List Nat).Nodup
  Holds _ := nonzero
  Prep _ := ([] : List Nat).Nodup
  prepare _ shapes _ _ := shapes
  result _ _ := ()
  present_result _ _ := by ext o; simp [fire, Selection.commit]
  settle _ _ := id
  knowledge_result _ _ := rfl

theorem guarded_reflects : guarded.step.Reflects := fun _ _ _ _ same => same

/-- The state without disequations. -/
def start : guarded.step.DState := ⟨(), [], separates_nil _⟩

/-- **The firing that tells `x ≠ false`**, with the guard `x ≠ false`. -/
def apart : guarded.step.DFiring start :=
  ⟨(), [(bit, no)], by
    intro d member equal
    have only : d = (bit, no) := List.mem_singleton.mp member
    subst only
    have point := congrFun equal (fun _ => true)
    cases point⟩

/-- **The base step refuses the guarded firing**: the solution `x ↦ false` fails its guard. -/
theorem guarded_refused : ¬ guarded.step.Admits (s := ()) () := by
  intro admitted
  exact admitted.2.2.2 () (fun _ _ => false) (Frames.models_nil _) rfl

/-- **With the disequation told, the prepared step admits it**, and computes its result. -/
theorem apart_admitted : (guarded.step.withDisequations guarded_reflects).Admits apart := by
  refine (Interface.Step.admits_iff_separating guarded_reflects apart).mpr
    ⟨List.nodup_nil, EvidenceInterface.Controls.enabled_nothing ∅,
      ⟨(), frame.id (), Frames.models_nil _, apart.formed⟩, ?_⟩
  intro b g _ separated
  exact separated (bit, no) (List.mem_append_right _ (List.mem_singleton_self _))

/-- **The guard does not hold at every solution**: `x ↦ false` fails it. A result obtained from the
base step's admission needs the guard at every solution; preparation does not. -/
theorem guard_not_everywhere : ¬ ∀ (b : Unit) (g : World → World), guarded.Holds (s := ()) () b g :=
  fun everywhere => everywhere () (fun _ _ => false) rfl

/-- **The guarded step with disequations covers its answers.** -/
theorem guarded_coversAnswers : CoversAnswers (guarded.step.withDisequations guarded_reflects) := by
  apply SettlementCoverage.withDisequations_coversAnswers guarded_reflects
  intro _ f p
  exact extends_of_retraction (X := frame) (e := guarded.step.preparedSettle f p) id fun _ => rfl

/-- **The F3 control**: the base step refuses the guarded firing, the prepared step with the told
disequation admits it, and the guard fails at a solution, so no result from base admission exists. -/
theorem control :
    ¬ guarded.step.Admits (s := ()) () ∧ (guarded.step.withDisequations guarded_reflects).Admits apart ∧
      ¬ ∀ (b : Unit) (g : World → World), guarded.Holds (s := ()) () b g :=
  ⟨guarded_refused, apart_admitted, guard_not_everywhere⟩

end Controls

#print axioms Prepared.step_admits_iff
#print axioms ofPrestep_step
#print axioms Prepared.step_coversAnswers
#print axioms Controls.disequation_restriction_changes_guard
#print axioms Controls.guarded_refused
#print axioms Controls.apart_admitted
#print axioms Controls.guard_not_everywhere
#print axioms Controls.guarded_coversAnswers
#print axioms Controls.control

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PreparedStep
