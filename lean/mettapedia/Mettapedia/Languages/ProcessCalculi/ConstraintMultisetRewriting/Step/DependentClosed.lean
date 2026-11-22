import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentControls

/-!
# Closed solutions, separate from symbolic solvability

Symbolic solvability (`Frames.Solvable`) asks for a solution into *some* later frame. A later frame
may keep any metavariable as a metavariable, so symbolic solvability treats every type as
inhabited. In a dependent foundation a metavariable is a proof obligation, and "consistent" is not
"proved". This module adds a second ask, over closed solutions.

**Generic** (any category of frames with a designated closed frame `point`):
* `Frames.ClosedSolvable`: a solution into `point`; `Frames.ClosedEntails`: an observation at every
  closed solution; `Step.ClosedAdmits`: admission with both asks taken over closed solutions.
* Closed solvability implies symbolic solvability (`ClosedSolvable.solvable`). They agree when the
  store has a principal answer whose frame has a closed point
  (`closedSolvable_iff_of_principal`), and everywhere when `point` is weakly terminal.

**Dependent frames** (`point` is the empty telescope; a closed solution of `Γ` is a substitution of
closed terms for its variables):
* **Symbolic solvability ignores the type of a new metavariable** (`solvable_extend_iff`): knowledge
  read in `Γ.A` is solvable exactly when it is solvable at `Γ`, whatever `A` is.
* **Closed solvability asks for an inhabitant** (`closedSolvable_extend_iff`): knowledge read in
  `Γ.A` has a closed solution exactly when the knowledge has one at which `A` has a closed term.
* **They agree on closed-inhabited types** (`closedSolvable_extend_iff_of_inhabited`), and **differ
  on empty ones** (`obligation_trap`): at the frame `x : A`, the empty store is always symbolically
  solvable, and closed-solvable exactly when `A` has a closed term.
* At the helper step: closed admission is closed-solvable knowledge, a fresh occurrence and closed
  guards (`closedAdmits_iff`); for guard-free firings it agrees with admission when the knowledge
  has a principal answer at a closed-inhabited frame (`closedAdmits_iff_admits`); at an obligation
  of an empty type every fresh guard-free firing is admitted and never closed-admitted
  (`trap_helper`).

Control (`Consumer.copy`): at the frame `x : g → g`, which `λx.x` inhabits, a helper is admitted and
closed-admitted. The negative control over the candidate's universe tower is in
`DependentClosedTower`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)

namespace Frames

universe uO uT uH

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} (X : Frames Tm Hom)

/-- **Closed solvability**: a solution into the closed frame `point`. -/
def ClosedSolvable (point : Obj) {a : Obj} (store : EquationStore (Tm a)) : Prop :=
  ∃ f : Hom a point, X.Models f store

/-- **A closed ask**: the observation holds at every closed solution. -/
def ClosedEntails (point : Obj) {a : Obj} (store : EquationStore (Tm a))
    (observation : Hom a point → Prop) : Prop :=
  ∀ f : Hom a point, X.Models f store → observation f

variable {X}

theorem ClosedSolvable.solvable {point a : Obj} {store : EquationStore (Tm a)}
    (closed : X.ClosedSolvable point store) : X.Solvable store := by
  obtain ⟨f, solved⟩ := closed
  exact ⟨point, f, solved⟩

/-- An ask over every later frame is an ask over the closed solutions. -/
theorem Entails.closed {point a : Obj} {store : EquationStore (Tm a)}
    {observation : (b : Obj) → Hom a b → Prop} (asked : X.Entails store observation) :
    X.ClosedEntails point store (observation point) :=
  fun f solved => asked point f solved

/-- **Closed and symbolic solvability agree at a closed-inhabited principal answer.** -/
theorem closedSolvable_iff_of_principal {point a m : Obj} {store : EquationStore (Tm a)}
    {answer : Hom a m} (principal : X.Principal store answer) (inhabited : Nonempty (Hom m point)) :
    X.ClosedSolvable point store ↔ X.Solvable store := by
  refine ⟨ClosedSolvable.solvable, fun _ => ?_⟩
  obtain ⟨c⟩ := inhabited
  exact ⟨X.comp c answer, models_comp principal.sound c⟩

/-- At a weakly terminal closed frame the two agree on every store. -/
theorem closedSolvable_iff_of_weaklyTerminal {point a : Obj} (terminal : WeaklyTerminal Hom point)
    (store : EquationStore (Tm a)) : X.ClosedSolvable point store ↔ X.Solvable store :=
  (solvable_iff_into terminal store).symm

end Frames

namespace Step

universe uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  (P : Step X O State Firing)
  [P.Guarded]

/-- **Closed admission**: the firing's shapes, the physical enabling of its selection, a closed
solution of its information, and its guards and queries at every closed solution. -/
def ClosedAdmits (point : Obj) {s : State} (f : Firing s) : Prop :=
  P.Shapes f ∧ Enabled (fun _ : O => ()) (P.present s) ((P.selection f).commit (T := Unit)) ∧
    X.ClosedSolvable point (P.information f) ∧
    X.ClosedEntails point (P.information f) (P.Holds f point)

/-- A closed-admitted firing has symbolically solvable information. -/
theorem ClosedAdmits.solvable {point : Obj} {s : State} {f : Firing s}
    (closed : P.ClosedAdmits point f) : X.Solvable (P.information f) :=
  closed.2.2.1.solvable

end Step

namespace Dependent

open _root_.CategoryTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveContextual

variable {Head : Type} {rules : Rules Head}

/-! ## A new metavariable, symbolically and closed -/

/-- **Symbolic solvability ignores the type of a new metavariable**: knowledge read in `Γ.A` is
solvable exactly when it is solvable at `Γ`, for every formed type `A`, inhabited or not. -/
theorem solvable_extend_iff {Γ : Context rules} (A : TypeOver Γ) (knowledge : EquationStore (Entry Γ)) :
    (frames rules).Solvable ((frames rules).applyStore (projectionHom Γ A) knowledge) ↔
      (frames rules).Solvable knowledge := by
  constructor
  · exact Frames.solvable_of_applyStore (X := frames rules) _
  · rintro ⟨Δ, σ, solved⟩
    refine ⟨extend Δ (A.reindex σ), lift σ rfl,
      (Frames.models_applyStore (X := frames rules) _ _ knowledge).mpr ?_⟩
    show (frames rules).Models (lift σ rfl ≫ projectionHom Γ A) knowledge
    rw [lift_projection]
    exact Frames.models_comp (X := frames rules) solved (projectionHom Δ (A.reindex σ))

/-- **Closed solvability asks for an inhabitant**: knowledge read in `Γ.A` has a closed solution
exactly when the knowledge has a closed solution at which `A` has a closed term. -/
theorem closedSolvable_extend_iff {Γ : Context rules} (A : TypeOver Γ)
    (knowledge : EquationStore (Entry Γ)) :
    (frames rules).ClosedSolvable (empty rules)
        ((frames rules).applyStore (projectionHom Γ A) knowledge) ↔
      ∃ c : empty rules ⟶ Γ, (frames rules).Models c knowledge ∧
        Nonempty (Term (empty rules) (A.reindex c)) := by
  constructor
  · rintro ⟨f, solved⟩
    exact ⟨f ≫ projectionHom Γ A,
      (Frames.models_applyStore (X := frames rules) _ _ knowledge).mp solved, ⟨pulledNewest f⟩⟩
  · rintro ⟨c, solved, ⟨t⟩⟩
    refine ⟨pair c t, (Frames.models_applyStore (X := frames rules) _ _ knowledge).mpr ?_⟩
    show (frames rules).Models (pair c t ≫ projectionHom Γ A) knowledge
    rw [pair_projection]
    exact solved

/-- **Closed and symbolic solvability agree on closed-inhabited types**: when `A` has a closed term
at every closed point of `Γ`, closed solvability at `Γ.A` is closed solvability at `Γ`. -/
theorem closedSolvable_extend_iff_of_inhabited {Γ : Context rules} (A : TypeOver Γ)
    (inhabited : ∀ c : empty rules ⟶ Γ, Nonempty (Term (empty rules) (A.reindex c)))
    (knowledge : EquationStore (Entry Γ)) :
    (frames rules).ClosedSolvable (empty rules)
        ((frames rules).applyStore (projectionHom Γ A) knowledge) ↔
      (frames rules).ClosedSolvable (empty rules) knowledge := by
  rw [closedSolvable_extend_iff]
  exact ⟨fun ⟨c, solved, _⟩ => ⟨c, solved⟩, fun ⟨c, solved⟩ => ⟨c, solved, inhabited c⟩⟩

/-- **The trap**: at the frame `x : A` over the empty telescope, the empty store is always
symbolically solvable, and has a closed solution exactly when `A` has a closed term. -/
theorem obligation_trap (A : TypeOver (empty rules)) :
    (frames rules).Solvable (a := extend (empty rules) A) [] ∧
      ((frames rules).ClosedSolvable (empty rules) (a := extend (empty rules) A) [] ↔
        Nonempty (Term (empty rules) A)) := by
  refine ⟨⟨_, 𝟙 _, Frames.models_nil _⟩, ?_⟩
  have unfolded := closedSolvable_extend_iff (rules := rules) A []
  refine unfolded.trans ⟨?_, ?_⟩
  · rintro ⟨c, -, ⟨t⟩⟩
    have identity : c = 𝟙 (empty rules) := (toEmpty_unique _ c).trans (toEmpty_unique _ _).symm
    subst identity
    exact ⟨t.cast A.reindex_id⟩
  · rintro ⟨t⟩
    exact ⟨𝟙 _, Frames.models_nil _, ⟨t.cast A.reindex_id.symm⟩⟩

/-! ## Closed admission at the helper step -/

variable {O : Type} [DecidableEq O]

/-- **Closed admission of a dependent helper firing**: closed-solvable knowledge, a fresh
occurrence, and guards at every closed solution of the knowledge. -/
theorem closedAdmits_iff {s : State rules O} (f : Firing s) :
    (helperStep (rules := rules) (O := O)).toStep.ClosedAdmits (empty rules) f ↔
      (frames rules).ClosedSolvable (empty rules) s.knowledge ∧ f.made ∉ s.present ∧
        (frames rules).ClosedEntails (empty rules) s.knowledge
          (fun c => (frames rules).Models c f.guards) := by
  constructor
  · rintro ⟨-, enabled, ⟨c, solved⟩, asked⟩
    refine ⟨⟨c ≫ projectionHom s.frame f.helper, restrict_models f c solved⟩, (enabled_iff f).mp enabled,
      fun c' solved' => ?_⟩
    have holds : (frames rules).Models (extendSolution f c' ≫ projectionHom s.frame f.helper) f.guards :=
      asked (extendSolution f c') (extendSolution_models f c' solved')
    rwa [extendSolution_restrict] at holds
  · rintro ⟨⟨c, solved⟩, absent, asked⟩
    exact ⟨List.nodup_singleton _, (enabled_iff f).mpr absent,
      ⟨extendSolution f c, extendSolution_models f c solved⟩,
      fun c' solved' => asked _ (restrict_models f c' solved')⟩

/-- **Closed and symbolic admission agree** on guard-free firings whose knowledge has a principal
answer at a closed-inhabited frame. -/
theorem closedAdmits_iff_admits {s : State rules O} (f : Firing s) (guardFree : f.guards = [])
    {M : Context rules} {m : M ⟶ s.frame}
    (principal : (frames rules).Principal (a := s.frame) (m := M) s.knowledge m)
    (inhabited : Nonempty (empty rules ⟶ M)) :
    (helperStep (rules := rules) (O := O)).toStep.ClosedAdmits (empty rules) f ↔ (helperStep (rules := rules)).Admits f := by
  rw [closedAdmits_iff, admits_iff, guardFree,
    Frames.closedSolvable_iff_of_principal (X := frames rules) principal inhabited]
  exact ⟨fun ⟨solvable, absent, _⟩ => ⟨solvable, absent, fun _ _ _ => Frames.models_nil _⟩,
    fun ⟨solvable, absent, _⟩ => ⟨solvable, absent, fun _ _ => Frames.models_nil _⟩⟩

/-- **The trap at the helper step**: at an obligation `x : A` of a type with no closed term, every
helper firing with a fresh occurrence and no guards is admitted, and none is closed-admitted. -/
theorem trap_helper (A : TypeOver (empty rules)) (noTerm : IsEmpty (Term (empty rules) A))
    (present : Finset O) (f : Firing (⟨extend (empty rules) A, [], present⟩ : State rules O))
    (fresh : f.made ∉ present) (guardFree : f.guards = []) :
    (helperStep (rules := rules)).Admits f ∧
      ¬ (helperStep (rules := rules) (O := O)).toStep.ClosedAdmits (empty rules) f := by
  refine ⟨(admits_iff f).mpr ⟨(obligation_trap A).1, fresh, fun _ _ _ => ?_⟩, fun closed => ?_⟩
  · rw [guardFree]
    exact Frames.models_nil _
  · obtain ⟨t⟩ := (obligation_trap A).2.mp ((closedAdmits_iff f).mp closed).1
    exact noTerm.false t

/-! ## Control: a closed-inhabited frame -/

namespace Consumer

/-- The frame `x : g → g`, with no knowledge and no occurrences. -/
abbrev arrowState : State tiny Nat := ⟨extend (empty tiny) arrowType, [], ∅⟩

/-- A helper `y : g → g` valued `x`. -/
def copy : Firing arrowState :=
  ⟨5, arrowType.reindex (projectionHom _ arrowType), newest _ arrowType, []⟩

/-- `λx.x` is a closed point of the frame `x : g → g`. -/
theorem arrowState_inhabited : Nonempty (empty tiny ⟶ arrowState.frame) :=
  ⟨pair (𝟙 _) (⟨.lam (.var 0), identity_typed _⟩ : Term (empty tiny) (arrowType.reindex (𝟙 _)))⟩

/-- **At a closed-inhabited frame the two admissions agree**: the helper is admitted and
closed-admitted. -/
theorem copy_admitted :
    (helperStep (rules := tiny)).Admits copy ∧ (helperStep (rules := tiny) (O := Nat)).toStep.ClosedAdmits (empty tiny) copy := by
  have admitted : (helperStep (rules := tiny)).Admits copy :=
    (admits_iff copy).mpr ⟨⟨_, 𝟙 _, Frames.models_nil _⟩, by decide, fun _ _ _ => Frames.models_nil _⟩
  exact ⟨admitted, (closedAdmits_iff_admits copy rfl (principal_nil _) arrowState_inhabited).mpr admitted⟩

end Consumer

end Dependent

#print axioms Frames.closedSolvable_iff_of_principal
#print axioms Frames.closedSolvable_iff_of_weaklyTerminal
#print axioms Step.ClosedAdmits.solvable
#print axioms Dependent.solvable_extend_iff
#print axioms Dependent.closedSolvable_extend_iff
#print axioms Dependent.closedSolvable_extend_iff_of_inhabited
#print axioms Dependent.obligation_trap
#print axioms Dependent.closedAdmits_iff
#print axioms Dependent.closedAdmits_iff_admits
#print axioms Dependent.trap_helper
#print axioms Dependent.Consumer.copy_admitted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
