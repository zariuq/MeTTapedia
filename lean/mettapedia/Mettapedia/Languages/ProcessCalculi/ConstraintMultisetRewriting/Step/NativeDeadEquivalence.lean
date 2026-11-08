import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeDeadNames
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeClosing

/-!
# Equivalence up to dead names, and the native step respects it

## The relation

Two native states **agree up to dead names** (`DeadEquiv`) when both are dead-name extensions of
one common state: a cospan of dead-name extensions. A cospan, not a span, is chosen because its
composition needs only a pushout of inclusions (`pushout`), which is built from names alone; a span
would need a pullback, which asks which names a term mentions. A span gives a cospan through the
same pushout (`DeadEquiv.of_span`).

* **The pushout** of two dead-name extensions of one state (`pushout`, `pushoutLeft`,
  `pushoutRight`): the first state's names beside the second's off-image names. Its rows and
  knowledge are the first state's, carried; the second inclusion carries the second state's to the
  same rows because both inclusions agree on the common state.
* `DeadEquiv` is an equivalence relation (`DeadEquiv.refl`, `symm`, `trans`, `setoid`); transitivity
  is the pushout.

## The result of a live firing is its core, extended by dead names

The **core** of a live firing (`core`) is its result with the solver's helpers removed: the
information frame, the firing's information as knowledge, its outputs as live rows and every other
row read at the information frame. It mentions no solver return. For every execution of the firing
(`Runs`), with any solver return and any budget, the published result is a dead-name extension of
the core (`coreExtension`): the solver's helper names and helper private names are dead.
Garbage-collecting them is therefore a dead-name equivalence (`result_equiv_core`).

The core is carried along every dead-name extension (`coreCarried`).

## The native step respects the relation

* `DeadExtension.result_equiv`: along a dead-name extension, a live firing's result and its
  carrying's result agree up to dead names.
* **The step theorem** (`DeadEquiv.step`): for states agreeing up to dead names through a common
  state, two live firings whose carryings to the common state agree are admitted together, and their
  results agree up to dead names. This is the bisimulation on the live fragment; the labelled form
  is in `Step/NativeStepBisim`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.Logic.LP (ScopedVar)

namespace NativeDead

/-! ## Inclusions are determined by their maps -/

section Congruence

variable {S : Signature} {O : Type} {Γ : Ctx S} {sort : S.Srt} {s u : NativeState S O Γ sort}

theorem Inclusion.row_congr {e e' : Inclusion s u} (locals : e.locals = e'.locals) (names : e.names = e'.names)
    (r : ContextualConditionalRows.Row s.locals s.state.declarations Γ sort) : e.row r = e'.row r := by
  obtain ⟨l, _, _, n, _, _⟩ := e
  obtain ⟨l', _, _, n', _, _⟩ := e'
  dsimp only at locals names
  subst locals names
  rfl

theorem Inclusion.frame_congr {e e' : Inclusion s u} (names : e.names = e'.names) : e.frame = e'.frame := by
  obtain ⟨l, _, _, n, _, _⟩ := e
  obtain ⟨l', _, _, n', _, _⟩ := e'
  dsimp only at names
  subst names
  rfl

/-- A carried shared row is shared. -/
theorem Inclusion.row_shared (e : Inclusion s u) (value : Term (signature S s.state.declarations) Γ sort) :
    e.row (ContextualConditionalRows.ofStored _ _ (.shared value)) =
      ContextualConditionalRows.ofStored _ _ (.shared (instantiate e.frame value)) :=
  rfl

end Congruence

/-! ## The pushout of two dead-name extensions -/

section Pushout

variable {S : Signature} {O : Type} {Γ : Ctx S} {sort : S.Srt} {j s t : NativeState S O Γ sort}
  (e : DeadExtension j s) (e' : DeadExtension j t)

/-- The private family of the pushout: the first state's beside the second's off-image names. -/
abbrev PushoutLocal (s : NativeState S O Γ sort) (e' : DeadExtension j t) := s.Local ⊕ {name : t.Local // name ∉ Set.range e'.locals}

/-- The names of the pushout: the first state's beside the second's off-image names. -/
abbrev PushoutNames (s : NativeState S O Γ sort) (e' : DeadExtension j t) := s.state.Names ⊕ {name : t.state.Names // name ∉ Set.range e'.names}

/-- The private arities of the pushout. -/
abbrev pushoutLocals (s : NativeState S O Γ sort) (e' : DeadExtension j t) : PushoutLocal s e' → MetaArity S := Sum.elim s.locals fun name => t.locals name.val

/-- The arities of the pushout. -/
abbrev pushoutDeclarations (s : NativeState S O Γ sort) (e' : DeadExtension j t) :
    PushoutNames s e' → MetaArity S :=
  Sum.elim s.state.declarations fun name => t.state.declarations name.val

/-- **The pushout state**: the first state, carried into the pushout frame. -/
noncomputable def pushout (s : NativeState S O Γ sort) (e' : DeadExtension j t) : NativeState S O Γ sort := by
  classical
  exact ⟨PushoutLocal s e', inferInstance, pushoutLocals s e',
    { Names := PushoutNames s e'
      equality := inferInstance
      declarations := pushoutDeclarations s e'
      occupied := s.state.occupied
      equations := ContextualResidual.mapProblem
        (reindex (source := s.state.declarations) (target := pushoutDeclarations s e') Sum.inl (fun _ => rfl))
        s.state.equations
      present := s.state.present
      rows := fun o => ContextualConditionalPublication.reindexPrivate s.locals (pushoutLocals s e')
        (pushoutDeclarations s e') Sum.inl (fun _ => rfl)
        ((s.state.rows o).map s.locals s.state.declarations
          (reindex (source := s.state.declarations) (target := pushoutDeclarations s e') Sum.inl (fun _ => rfl))) }⟩

/-- The first state in the pushout. -/
noncomputable def pushoutLeft (s : NativeState S O Γ sort) (e' : DeadExtension j t) : DeadExtension s (pushout s e') where
  locals := Sum.inl
  locals_injective := Sum.inl_injective
  locals_preserves _ := rfl
  names := Sum.inl
  names_injective := Sum.inl_injective
  names_preserves _ := rfl
  rows _ := rfl
  equations := List.Perm.refl _
  present := rfl
  occupied := rfl

open Classical in
/-- The second state's private names in the pushout. -/
noncomputable def rightLocals (name : t.Local) : PushoutLocal s e' :=
  if h : name ∈ Set.range e'.locals then .inl (e.locals (Classical.choose h)) else .inr ⟨name, h⟩

open Classical in
/-- The second state's names in the pushout. -/
noncomputable def rightNames (name : t.state.Names) : PushoutNames s e' :=
  if h : name ∈ Set.range e'.names then .inl (e.names (Classical.choose h)) else .inr ⟨name, h⟩

theorem rightLocals_image (name : j.Local) : rightLocals e e' (e'.locals name) = .inl (e.locals name) := by
  have h : e'.locals name ∈ Set.range e'.locals := ⟨name, rfl⟩
  unfold rightLocals
  rw [dif_pos h, e'.locals_injective (Classical.choose_spec h)]

theorem rightNames_image (name : j.state.Names) : rightNames e e' (e'.names name) = .inl (e.names name) := by
  have h : e'.names name ∈ Set.range e'.names := ⟨name, rfl⟩
  unfold rightNames
  rw [dif_pos h, e'.names_injective (Classical.choose_spec h)]

theorem rightLocals_injective : Function.Injective (rightLocals e e') := by
  intro first second same
  by_cases h₁ : first ∈ Set.range e'.locals
  · by_cases h₂ : second ∈ Set.range e'.locals
    · obtain ⟨a, rfl⟩ := h₁
      obtain ⟨b, rfl⟩ := h₂
      rw [rightLocals_image, rightLocals_image] at same
      rw [e.locals_injective (Sum.inl.inj same)]
    · unfold rightLocals at same
      rw [dif_pos h₁, dif_neg h₂] at same
      cases same
  · by_cases h₂ : second ∈ Set.range e'.locals
    · unfold rightLocals at same
      rw [dif_neg h₁, dif_pos h₂] at same
      cases same
    · unfold rightLocals at same
      rw [dif_neg h₁, dif_neg h₂] at same
      exact congrArg Subtype.val (Sum.inr.inj same)

theorem rightNames_injective : Function.Injective (rightNames e e') := by
  intro first second same
  by_cases h₁ : first ∈ Set.range e'.names
  · by_cases h₂ : second ∈ Set.range e'.names
    · obtain ⟨a, rfl⟩ := h₁
      obtain ⟨b, rfl⟩ := h₂
      rw [rightNames_image, rightNames_image] at same
      rw [e.names_injective (Sum.inl.inj same)]
    · unfold rightNames at same
      rw [dif_pos h₁, dif_neg h₂] at same
      cases same
  · by_cases h₂ : second ∈ Set.range e'.names
    · unfold rightNames at same
      rw [dif_neg h₁, dif_pos h₂] at same
      cases same
    · unfold rightNames at same
      rw [dif_neg h₁, dif_neg h₂] at same
      exact congrArg Subtype.val (Sum.inr.inj same)

theorem rightLocals_preserves (name : t.Local) :
    pushoutLocals s e' (rightLocals e e' name) = t.locals name := by
  by_cases h : name ∈ Set.range e'.locals
  · obtain ⟨a, rfl⟩ := h
    rw [rightLocals_image]
    exact (e.locals_preserves a).trans (e'.locals_preserves a).symm
  · unfold rightLocals
    rw [dif_neg h]
    rfl

theorem rightNames_preserves (name : t.state.Names) :
    pushoutDeclarations s e' (rightNames e e' name) = t.state.declarations name := by
  by_cases h : name ∈ Set.range e'.names
  · obtain ⟨a, rfl⟩ := h
    rw [rightNames_image]
    exact (e.names_preserves a).trans (e'.names_preserves a).symm
  · unfold rightNames
    rw [dif_neg h]
    rfl

/-- The second state's inclusion into the pushout. -/
noncomputable def rightInclusion : Inclusion t (pushout s e') :=
  ⟨rightLocals e e', rightLocals_injective e e', rightLocals_preserves e e',
    rightNames e e', rightNames_injective e e', rightNames_preserves e e'⟩

/-- **The pushout square commutes**: both inclusions agree on the common state. -/
theorem pushout_square_locals :
    (e.toInclusion.comp (pushoutLeft s e').toInclusion).locals =
      (e'.toInclusion.comp (rightInclusion e e')).locals :=
  funext fun name => (rightLocals_image e e' name).symm

theorem pushout_square_names :
    (e.toInclusion.comp (pushoutLeft s e').toInclusion).names =
      (e'.toInclusion.comp (rightInclusion e e')).names :=
  funext fun name => (rightNames_image e e' name).symm

/-- **The second state in the pushout.** -/
noncomputable def pushoutRight : DeadExtension t (pushout s e') where
  toInclusion := rightInclusion e e'
  rows o := by
    refine ((pushoutLeft s e').rows o).trans ?_
    rw [e.rows o, Inclusion.row_comp, Inclusion.row_congr (pushout_square_locals e e') (pushout_square_names e e'),
      ← Inclusion.row_comp, ← e'.rows o]
  equations := by
    refine (pushoutLeft s e').equations.trans ((e.equations.map _).trans (List.Perm.of_eq ?_) |>.trans
      (e'.equations.map _).symm)
    show ContextualResidual.mapProblem (pushoutLeft s e').frame (ContextualResidual.mapProblem e.frame j.state.equations) =
      ContextualResidual.mapProblem (rightInclusion e e').frame (ContextualResidual.mapProblem e'.frame j.state.equations)
    rw [ContextualConditionalNaturality.map_problem_compose, ContextualConditionalNaturality.map_problem_compose,
      Inclusion.frame_comp, Inclusion.frame_comp, Inclusion.frame_congr (pushout_square_names e e')]
  present := e.present.trans e'.present.symm
  occupied := e.occupied.trans e'.occupied.symm

end Pushout

/-! ## Agreement up to dead names -/

section Equivalence

variable {S : Signature} {O : Type} {Γ : Ctx S} {sort : S.Srt}

/-- **Two native states agree up to dead names** when both are dead-name extensions of one state. -/
def DeadEquiv (s t : NativeState S O Γ sort) : Prop :=
  ∃ u : NativeState S O Γ sort, Nonempty (DeadExtension s u) ∧ Nonempty (DeadExtension t u)

namespace DeadEquiv

theorem refl (s : NativeState S O Γ sort) : DeadEquiv s s := ⟨s, ⟨DeadExtension.refl s⟩, ⟨DeadExtension.refl s⟩⟩

theorem symm {s t : NativeState S O Γ sort} (same : DeadEquiv s t) : DeadEquiv t s := by
  obtain ⟨u, first, second⟩ := same
  exact ⟨u, second, first⟩

/-- **A span of dead-name extensions gives agreement**, through its pushout. -/
theorem of_span {j s t : NativeState S O Γ sort} (e : DeadExtension j s) (e' : DeadExtension j t) :
    DeadEquiv s t :=
  ⟨pushout s e', ⟨pushoutLeft s e'⟩, ⟨pushoutRight e e'⟩⟩

theorem of_extension {s u : NativeState S O Γ sort} (e : DeadExtension s u) : DeadEquiv s u :=
  ⟨u, ⟨e⟩, ⟨DeadExtension.refl u⟩⟩

/-- **Agreement up to dead names is transitive**: the two common states amalgamate in a pushout. -/
theorem trans {s t w : NativeState S O Γ sort} (first : DeadEquiv s t) (second : DeadEquiv t w) :
    DeadEquiv s w := by
  obtain ⟨u, ⟨su⟩, ⟨tu⟩⟩ := first
  obtain ⟨v, ⟨tv⟩, ⟨wv⟩⟩ := second
  exact ⟨pushout u tv, ⟨su.comp (pushoutLeft u tv)⟩, ⟨wv.comp (pushoutRight tu tv)⟩⟩

/-- Agreement up to dead names, as a setoid. -/
def setoid : Setoid (NativeState S O Γ sort) := ⟨DeadEquiv, ⟨refl, symm, trans⟩⟩

end DeadEquiv

end Equivalence

/-! ## The core of a live result -/

section Core

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

/-- **The core of a live firing's result**: its result with the solver's helpers removed. -/
def core {s : NativeState S O Γ sort} (f : LiveFiring s) : NativeState S O Γ sort :=
  ⟨s.Local, s.localEquality, s.locals,
    { Names := ScopedVar s.Local ⊕ s.state.Names
      equality := by letI := s.localEquality; letI := s.state.equality; exact inferInstance
      declarations := ContextualActivatedStep.target s.locals s.state.declarations
      occupied := ContextualFreshFrameScopeLedger.helperLedger
        (ContextualActivationScopes.after s.state.occupied f.selection)
      equations := NativeResidual.problemOf s f.selection f.rule
      present := fire s.state.present (f.selection.commit (T := Unit))
      rows := fun o => if o ∈ f.selection.made then
          ContextualConditionalRows.ofStored _ _ (.shared (f.outputs o))
        else (s.state.rows o).map s.locals s.state.declarations
          (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) }⟩

/-- **An execution of a live firing**: an execution with the firing's data and live outputs. -/
structure Runs {s : NativeState S O Γ sort} (G : ContextualConditionalExecution.Firing s.locals s.state)
    (f : LiveFiring s) : Prop where
  rule : G.rule = f.rule
  selection : G.selection = f.selection
  outputs : G.outputs = f.outputs
  live : ∀ o ∈ G.selection.made, G.reusable o = false

variable {s : NativeState S O Γ sort}
/-- The inclusion of the core into a published result. -/
def coreInclusion (G : ContextualConditionalExecution.Firing s.locals s.state) (f : LiveFiring s) :
    Inclusion (core f) (rawTarget G) :=
  ⟨Sum.inl, Sum.inl_injective, fun _ => rfl, Sum.inl, Sum.inl_injective, fun _ => rfl⟩

theorem coreInclusion_frame (G : ContextualConditionalExecution.Firing s.locals s.state) (f : LiveFiring s) :
    (coreInclusion G f).frame = ContextualComputedFreshFrame.includeSource G.update :=
  G.resultFrame_assignment

theorem coreInclusion_rows (G : ContextualConditionalExecution.Firing s.locals s.state) (f : LiveFiring s)
    (runs : Runs G f) (o : O) :
    (rawTarget G).state.rows o = (coreInclusion G f).row ((core f).state.rows o) := by
  by_cases made : o ∈ f.selection.made
  · have madeG : o ∈ G.selection.made := by rw [runs.selection]; exact made
    have coreRow : (core f).state.rows o = ContextualConditionalRows.ofStored _ _ (.shared (f.outputs o)) :=
      if_pos made
    calc (rawTarget G).state.rows o
        = ContextualConditionalRows.ofStored _ _ (.shared (instantiate (coreInclusion G f).frame (f.outputs o))) := by
          rw [coreInclusion_frame, ← runs.outputs]
          exact G.shared_row o madeG (runs.live o madeG)
      _ = (coreInclusion G f).row ((core f).state.rows o) := (congrArg (coreInclusion G f).row coreRow).symm
  · have notG : o ∉ G.selection.made := by rw [runs.selection]; exact made
    have coreRow : (core f).state.rows o = (s.state.rows o).map s.locals s.state.declarations
        (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) := if_neg made
    have step : (s.state.rows o).map s.locals s.state.declarations (NativeResidual.change G) =
        ((s.state.rows o).map s.locals s.state.declarations
          (ContextualSelectionViews.capturedTarget s.locals s.state.declarations)).map s.locals
          (ContextualActivatedStep.target s.locals s.state.declarations)
          (ContextualComputedFreshFrame.includeSource G.update) :=
      (ContextualConditionalNaturality.row_map_compose s.locals _ _ _).symm
    show G.target.rows o = (coreInclusion G f).row ((core f).state.rows o)
    refine (NativeResidual.rows_of_not_made G notG).trans
      ((extendPrivate_eq_reindexPrivate s.locals G.update.declaration G.target.declarations _).trans
        ((congrArg (ContextualConditionalPublication.reindexPrivate s.locals
          (ContextualPublication.privateFamily s.locals G.update.declaration) G.target.declarations Sum.inl
          (fun _ => rfl)) step).trans
          ((congrArg (fun frame : Assignment (ContextualActivatedStep.target s.locals s.state.declarations)
              G.target.declarations =>
            ContextualConditionalPublication.reindexPrivate s.locals
              (ContextualPublication.privateFamily s.locals G.update.declaration) G.target.declarations Sum.inl
              (fun _ => rfl)
              (((s.state.rows o).map s.locals s.state.declarations
                (ContextualSelectionViews.capturedTarget s.locals s.state.declarations)).map s.locals
                (ContextualActivatedStep.target s.locals s.state.declarations) frame))
            (coreInclusion_frame G f).symm).trans ?_)))
    exact (congrArg (coreInclusion G f).row coreRow).symm

/-- **The published result is the core, extended by dead names**: the solver's helper names and
helper private names, which no row, equation or occurrence mentions. Any solver return. -/
def coreExtension (G : ContextualConditionalExecution.Firing s.locals s.state) (f : LiveFiring s)
    (runs : Runs G f) : DeadExtension (core f) (rawTarget G) where
  toInclusion := coreInclusion G f
  rows := coreInclusion_rows G f runs
  equations := by
    have same : ContextualConditionalExecution.information s.locals s.state.declarations s.state.occupied G.selection
        G.rule s.state.rows s.state.equations = NativeResidual.problemOf s f.selection f.rule := by
      rw [runs.selection, runs.rule]
    refine List.Perm.of_eq ((congrArg (ContextualResidual.mapProblem
      (ContextualComputedFreshFrame.includeSource G.update)) same).trans ?_)
    exact congrArg (fun frame => ContextualResidual.mapProblem frame (NativeResidual.problemOf s f.selection f.rule))
      (coreInclusion_frame G f).symm
  present := by
    show fire s.state.present (G.selection.commit (T := Unit)) = fire s.state.present (f.selection.commit (T := Unit))
    rw [runs.selection]
  occupied := by
    show ContextualFreshFrameScopeLedger.helperLedger (ContextualActivationScopes.after s.state.occupied G.selection) =
      ContextualFreshFrameScopeLedger.helperLedger (ContextualActivationScopes.after s.state.occupied f.selection)
    rw [runs.selection]

variable {u : NativeState S O Γ sort}

/-- The inclusion of a core into the core of the carried firing. -/
def coreCarriedInclusion (e : DeadExtension s u) (f : LiveFiring s) : Inclusion (core f) (core (e.firing f)) :=
  ⟨e.locals, e.locals_injective, e.locals_preserves, Sum.map e.scopedName e.names,
    e.scopedName_injective.sumMap e.names_injective, e.target_preserves⟩

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem coreCarriedInclusion_rows (e : DeadExtension s u) (f : LiveFiring s) (o : O) :
    (core (e.firing f)).state.rows o = (coreCarriedInclusion e f).row ((core f).state.rows o) := by
  by_cases made : o ∈ f.selection.made
  · have coreRow : (core f).state.rows o = ContextualConditionalRows.ofStored _ _ (.shared (f.outputs o)) :=
      if_pos made
    exact (show (core (e.firing f)).state.rows o =
        ContextualConditionalRows.ofStored _ _ (.shared (instantiate e.target (f.outputs o))) from if_pos made).trans
      (congrArg (coreCarriedInclusion e f).row coreRow).symm
  · have coreRow : (core f).state.rows o = (s.state.rows o).map s.locals s.state.declarations
        (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) := if_neg made
    exact (show (core (e.firing f)).state.rows o = (u.state.rows o).map u.locals u.state.declarations
        (ContextualSelectionViews.capturedTarget u.locals u.state.declarations) from if_neg made).trans
      ((congrArg (fun r => r.map u.locals u.state.declarations
          (ContextualSelectionViews.capturedTarget u.locals u.state.declarations)) (e.rows o)).trans
        ((e.row_guard (s.state.rows o)).trans (congrArg (coreCarriedInclusion e f).row coreRow).symm))

/-- **The core is carried along every dead-name extension.** -/
def coreCarried (e : DeadExtension s u) (f : LiveFiring s) : DeadExtension (core f) (core (e.firing f)) where
  toInclusion := coreCarriedInclusion e f
  rows := coreCarriedInclusion_rows e f
  equations := e.information_firing f
  present := by
    show fire u.state.present (f.selection.commit (T := Unit)) = fire s.state.present (f.selection.commit (T := Unit))
    rw [e.present]
  occupied := by
    show ContextualFreshFrameScopeLedger.helperLedger (ContextualActivationScopes.after u.state.occupied f.selection) =
      ContextualFreshFrameScopeLedger.helperLedger (ContextualActivationScopes.after s.state.occupied f.selection)
    rw [e.occupied]

end Core

/-! ## The native step respects agreement up to dead names -/

section Step

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] {s u t : NativeState S O Γ sort}

/-- The pinned execution of an admitted live firing runs it. -/
theorem runs_execution (f : LiveFiring s) (admitted : f.toNative.Realized) :
    Runs (LiveFiring.execution admitted) f where
  rule := (LiveFiring.execution_data admitted).1
  selection := (LiveFiring.execution_data admitted).2.1
  outputs := (LiveFiring.execution_data admitted).2.2.1
  live o _ := by rw [(LiveFiring.execution_data admitted).2.2.2]

/-- **A live firing's step publishes its core extended by dead names.** -/
noncomputable def result_core (f : LiveFiring s) (admitted : f.toNative.Realized) :
    DeadExtension (core f) (native.result f.toNative admitted) :=
  coreExtension (LiveFiring.execution admitted) f (runs_execution f admitted)

/-- **Garbage-collecting the solver's helpers is sound**: the result agrees with its core up to dead
names. -/
theorem result_equiv_core (f : LiveFiring s) (admitted : f.toNative.Realized) :
    DeadEquiv (core f) (native.result f.toNative admitted) :=
  DeadEquiv.of_extension (result_core f admitted)

/-- Equal live firings have equal results. -/
theorem result_congr {f g : LiveFiring s} (same : f = g) (first : f.toNative.Realized)
    (second : g.toNative.Realized) :
    native.result f.toNative first = native.result g.toNative second := by
  subst same
  rfl

/-- **Along a dead-name extension, a live firing's result and its carrying's result agree up to dead
names**, whatever the two solver returns. -/
theorem DeadExtension.result_equiv (e : DeadExtension s u) (f : LiveFiring s) (first : f.toNative.Realized)
    (second : (e.firing f).toNative.Realized) :
    DeadEquiv (native.result f.toNative first) (native.result (e.firing f).toNative second) :=
  DeadEquiv.of_span (result_core f first) ((coreCarried e f).comp (result_core (e.firing f) second))

/-- **The step theorem**: states that agree up to dead names through a common state admit together
every two live firings whose carryings to the common state agree, and their results agree up to dead
names. -/
theorem DeadEquiv.step (e : DeadExtension s u) (e' : DeadExtension t u) {f : LiveFiring s} {f' : LiveFiring t}
    (same : e.firing f = e'.firing f') :
    (f.toNative.Realized ↔ f'.toNative.Realized) ∧
      ∀ (first : f.toNative.Realized) (second : f'.toNative.Realized),
        DeadEquiv (native.result f.toNative first) (native.result f'.toNative second) := by
  have along : (e.firing f).toNative.Realized ↔ (e'.firing f').toNative.Realized := by rw [same]
  refine ⟨(e.admits_iff f).trans (along.trans (e'.admits_iff f').symm), fun first second => ?_⟩
  have middle := (e.admits_iff f).mp first
  have middle' := (e'.admits_iff f').mp second
  exact ((e.result_equiv f first middle).trans
    (DeadEquiv.of_extension (DeadExtension.refl _) |>.trans
      (by rw [result_congr same middle middle']; exact DeadEquiv.refl _))).trans
    (e'.result_equiv f' second middle').symm

end Step

end NativeDead

#print axioms NativeDead.pushoutRight
#print axioms NativeDead.DeadEquiv.of_span
#print axioms NativeDead.DeadEquiv.trans
#print axioms NativeDead.coreExtension
#print axioms NativeDead.coreCarried
#print axioms NativeDead.result_equiv_core
#print axioms NativeDead.DeadExtension.result_equiv
#print axioms NativeDead.DeadEquiv.step

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
