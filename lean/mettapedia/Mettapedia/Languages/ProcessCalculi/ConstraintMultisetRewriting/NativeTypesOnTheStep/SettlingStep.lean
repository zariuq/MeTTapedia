import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.SyntacticShadow
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PrincipalAnswers

/-!
# A step that settles along initial solutions

The dependent full step (`Interface.DependentFull.step`) settles every firing along the identity, so
a made row must be typed in the raw frame before any solution is chosen. The step here has the same
states and firings and settles **lazily**:

* when every made row is typed in the frame (`FrameTyped`), it settles along the identity, exactly as
  the present step does;
* otherwise it asks a **settler** for a verdict on the firing's information (`Verdict`): an initial
  solution `σ : M ⟶ Δ`, or postponement. Settled, the made rows must be typed along `σ`, and the result
  lives at `M`, with the information transported along `σ` as its knowledge and every row read along
  `σ` (`settledState`). Postponed, nothing is settled and the rows must be typed in the frame.

**Conservativity** (`settling_admits_of_admits`, `settling_result_eq`): every firing the present step
admits is admitted, with the same result state. **The present step is the settling step whose settler
never settles** (`never_admits_iff`, `never_result_eq`).

**Soundness** (`settling_typedUpToAgreement`): every made row of an admitted firing is typed after the
match of its information, up to agreement. **Exactness** (`settled_exact`): settling along a
principal answer loses no solution up to agreement.

**Decision at the answer** (`settled_admits_iff`): when the settler settles a firing without queries,
admission is the shapes, the enabling, the made rows typed at the answer and the guards at the
answer: a check at one substitution, decidable wherever typing and the guards' equality are. The
semantic settler (`Settler.ideal`) settles every store that has an initial solution; a solver that
reaches a principal answer on a decided fragment supplies one.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep

open _root_.CategoryTheory Opposite Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull (Make State Firing relabel)
open UnificationWithLevels (Agree InitialSolution)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
variable (levels : LevelModel rules L)

/-! ## Settlers -/

section Settlers

/-- **A settler's verdict on a store**: an initial solution, with the frame it lands in, or
postponement. -/
inductive Verdict {Δ : Context rules} (I : EquationStore (TotalTerm Δ)) : Type
  | settled (M : Context rules) (σ : M ⟶ Δ) (initial : InitialSolution (frames levels) I σ)
  | postponed

/-- **A settler**: a verdict on every store. -/
def Settler : Type := ∀ {Δ : Context rules} (I : EquationStore (TotalTerm Δ)), Verdict levels I

/-- The settler that never settles. -/
def Settler.never : Settler levels := fun _ => .postponed

open Classical in
/-- **The semantic settler**: it settles every store that has an initial solution, along a chosen
one. -/
noncomputable def Settler.ideal : Settler levels := fun {Δ} I =>
  if h : ∃ (M : Context rules) (σ : M ⟶ Δ), InitialSolution (frames levels) I σ then
    .settled h.choose h.choose_spec.choose h.choose_spec.choose_spec
  else .postponed

/-- The semantic settler settles every store with an initial solution. -/
theorem Settler.ideal_settles {M Δ : Context rules} {I : EquationStore (TotalTerm Δ)} {σ : M ⟶ Δ}
    (initial : InitialSolution (frames levels) I σ) :
    ∃ (M' : Context rules) (σ' : M' ⟶ Δ) (initial' : InitialSolution (frames levels) I σ'),
      Settler.ideal levels I = .settled M' σ' initial' := by
  unfold Settler.ideal
  rw [dif_pos ⟨M, σ, initial⟩]
  exact ⟨_, _, _, rfl⟩

/-- **A store without an initial solution is postponed by every settler.** -/
theorem Verdict.eq_postponed {Δ : Context rules} {I : EquationStore (TotalTerm Δ)}
    (none : ∀ (M : Context rules) (σ : M ⟶ Δ), ¬ InitialSolution (frames levels) I σ)
    (v : Verdict levels I) : v = .postponed := by
  cases v with
  | settled M σ initial => exact (none M σ initial).elim
  | postponed => rfl

/-- An initial solution is a principal answer. -/
theorem principal_of_initial {M Δ : Context rules} {I : EquationStore (TotalTerm Δ)} {σ : M ⟶ Δ}
    (initial : InitialSolution (frames levels) I σ) : (frames levels).Principal I σ :=
  ⟨initial.solves, initial.factor⟩

variable {levels}

/-- The morphism a verdict settles along: the answer, or the identity when postponed. -/
def Verdict.along {Δ : Context rules} {I : EquationStore (TotalTerm Δ)} :
    Verdict levels I → Σ M : Context rules, M ⟶ Δ
  | .settled M σ _ => ⟨M, σ⟩
  | .postponed => ⟨Δ, 𝟙 Δ⟩

end Settlers

/-! ## The settling step -/

section Step

variable {O : Type} [DecidableEq O]

omit [UniverseLevel.LevelOrder L] in
theorem Make.reindex_id' {Δ : Context rules} (m : Make Δ) : m.reindex (𝟙 Δ) = m :=
  make_ext (TypeOver.reindex_id m.type) (subst_ids m.code)

/-- Every made row of the firing is typed in its frame. -/
def FrameTyped {s : State rules O} (f : Firing levels s) : Prop := ∀ m ∈ f.makes, m.2.WellTyped

open Classical in
/-- **The plan of a firing**: the identity when its made rows are typed in its frame; otherwise the
settler's answer for its information, or the identity when the settler postpones. -/
noncomputable def plan (settler : Settler levels) {s : State rules O} (f : Firing levels s) :
    Σ M : Context rules, M ⟶ f.helpers.frame :=
  if FrameTyped levels f then ⟨f.helpers.frame, 𝟙 _⟩ else (settler f.information).along

/-- **Settled shapes**: the step's shapes, with made rows typed along the plan. -/
def SettledShapes (settler : Settler levels) {s : State rules O} (f : Firing levels s) : Prop :=
  f.taken.Nodup ∧ f.made.Nodup ∧ f.takes.length = f.taken.length ∧ f.reads.length = f.read.length ∧
    ∀ m ∈ f.makes, (m.2.reindex (plan levels settler f).2).WellTyped

omit [UniverseLevel.LevelOrder L] [DecidableEq O] in
/-- The made rows, settled along a morphism. -/
def settledMakes {s : State rules O} (f : Firing levels s) {M : Context rules}
    (σ : M ⟶ f.helpers.frame) : List (O × Make M) :=
  f.makes.map fun m => (m.1, m.2.reindex σ)

omit [DecidableEq O] in
theorem settledMakes_typed {s : State rules O} (f : Firing levels s) {M : Context rules}
    (σ : M ⟶ f.helpers.frame) (typed : ∀ m ∈ f.makes, (m.2.reindex σ).WellTyped) :
    ∀ m ∈ settledMakes levels f σ, m.2.WellTyped := by
  intro m member
  obtain ⟨m', member', rfl⟩ := List.mem_map.mp member
  exact typed m' member'

/-- **The settled state**: the frame the plan lands in, the information transported along it as
knowledge, the fired occurrences, and every row read along the settlement. -/
def settledState {s : State rules O} (f : Firing levels s)
    (p : Σ M : Context rules, M ⟶ f.helpers.frame) (typed : ∀ m ∈ f.makes, (m.2.reindex p.2).WellTyped) :
    State rules O :=
  ⟨p.1, (frames levels).applyStore p.2 f.information, fire s.present (f.selection.commit (T := Unit)),
    relabel (fun o => (f.row o).reindex p.2) (settledMakes levels f p.2) (settledMakes_typed levels f p.2 typed)⟩

variable (O) in
/-- **The settling step**: the dependent full step's states and firings, settled lazily along the
settler's initial solutions. -/
noncomputable def settlingStep (settler : Settler levels) :
    Interface.Step.Standard (frames levels) O (State rules O) (Firing levels) where
  frame s := s.frame
  knowledge s := s.knowledge
  present s := s.present
  selection f := f.selection
  target f := f.helpers.frame
  extension f := f.helpers.weaken
  information f := f.information
  transported := (DependentFull.step levels O).transported
  Shapes f := SettledShapes levels settler f
  Holds f _ τ := f.Holds τ
  Admits {s} f := SettledShapes levels settler f ∧
    Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ∧
    (frames levels).Solvable f.information ∧ (frames levels).Entails f.information (fun _ τ => f.Holds τ)
  admits_iff _ := Iff.rfl
  preparedResult f p := settledState levels f (plan levels settler f) p.1.2.2.2.2
  present_preparedResult _ _ := rfl
  preparedSettle f _ := (plan levels settler f).2
  knowledge_preparedResult _ _ := rfl

/-! ## Conservativity -/

variable (settler : Settler levels)

omit [DecidableEq O] in
theorem plan_of_frameTyped {s : State rules O} {f : Firing levels s} (typed : FrameTyped levels f) :
    plan levels settler f = ⟨f.helpers.frame, 𝟙 _⟩ := by
  unfold plan
  rw [if_pos typed]

omit [DecidableEq O] in
theorem plan_never {s : State rules O} (f : Firing levels s) :
    plan levels (Settler.never levels) f = ⟨f.helpers.frame, 𝟙 _⟩ := by
  unfold plan
  split <;> rfl

omit [DecidableEq O] in
theorem settledShapes_iff_of_plan {s : State rules O} {f : Firing levels s}
    (identity : plan levels settler f = ⟨f.helpers.frame, 𝟙 _⟩) :
    SettledShapes levels settler f ↔ f.Shapes := by
  unfold SettledShapes Firing.Shapes
  rw [identity]
  constructor
  · rintro ⟨a, b, c, d, typed⟩
    exact ⟨a, b, c, d, fun m member => by simpa only [Make.reindex_id'] using typed m member⟩
  · rintro ⟨a, b, c, d, typed⟩
    exact ⟨a, b, c, d, fun m member => by simpa only [Make.reindex_id'] using typed m member⟩

omit [UniverseLevel.LevelOrder L] in
theorem relabel_congr {Δ : Context rules} {row row' : O → TotalTerm Δ}
    {makes makes' : List (O × Make Δ)} (sameRow : row = row') (sameMakes : makes = makes')
    (typed : ∀ m ∈ makes, m.2.WellTyped) (typed' : ∀ m ∈ makes', m.2.WellTyped) :
    relabel row makes typed = relabel row' makes' typed' := by
  subst sameRow
  subst sameMakes
  rfl

omit [UniverseLevel.LevelOrder L] [DecidableEq O] in
theorem map_reindex_id {Δ : Context rules} :
    ∀ makes : List (O × Make Δ), makes.map (fun m => (m.1, m.2.reindex (𝟙 Δ))) = makes
  | [] => rfl
  | m :: rest => by rw [List.map_cons, map_reindex_id rest, Make.reindex_id']

/-- **Settled along the identity, the state is the present step's.** -/
theorem settledState_eq_of_plan {s : State rules O} (f : Firing levels s)
    {p : Σ M : Context rules, M ⟶ f.helpers.frame} (identity : p = ⟨f.helpers.frame, 𝟙 _⟩)
    (typed : ∀ m ∈ f.makes, (m.2.reindex p.2).WellTyped) (typed' : ∀ m ∈ f.makes, m.2.WellTyped) :
    settledState levels f p typed =
      ⟨f.helpers.frame, f.information, fire s.present (f.selection.commit (T := Unit)),
        relabel f.row f.makes typed'⟩ := by
  subst identity
  have knowledge : (frames levels).applyStore (𝟙 f.helpers.frame) f.information = f.information :=
    Frames.applyStore_id _
  have rows : (fun o => (f.row o).reindex (𝟙 f.helpers.frame)) = f.row :=
    funext fun o => reindex_id (f.row o)
  have labels := relabel_congr rows (map_reindex_id f.makes)
    (settledMakes_typed levels f (𝟙 f.helpers.frame) typed) typed'
  unfold settledState
  dsimp only
  rw [knowledge]
  exact congrArg (State.mk f.helpers.frame f.information (fire s.present (f.selection.commit (T := Unit))))
    labels

/-- **Conservativity of admission**: every firing the present step admits, the settling step admits. -/
theorem settling_admits_of_admits {s : State rules O} {f : Firing levels s}
    (admitted : (DependentFull.step levels O).Admits f) : (settlingStep levels O settler).Admits f := by
  obtain ⟨shapes, enabled, solvable, holds⟩ := admitted
  have typed : FrameTyped levels f := shapes.2.2.2.2
  exact ⟨(settledShapes_iff_of_plan levels settler (plan_of_frameTyped levels settler typed)).mpr shapes,
    enabled, solvable, holds⟩

/-- **Conservativity of results**: with the same result state. -/
theorem settling_result_eq {s : State rules O} {f : Firing levels s}
    (admitted : (DependentFull.step levels O).Admits f) :
    (settlingStep levels O settler).result f (settling_admits_of_admits levels settler admitted) =
      (DependentFull.step levels O).result f admitted :=
  settledState_eq_of_plan levels f (plan_of_frameTyped levels settler admitted.1.2.2.2.2)
    (settling_admits_of_admits levels settler admitted).1.2.2.2.2 admitted.1.2.2.2.2

/-- On firings whose rows are typed in the frame the two steps admit the same firings. -/
theorem settling_admits_iff_of_frameTyped {s : State rules O} {f : Firing levels s}
    (typed : FrameTyped levels f) :
    (settlingStep levels O settler).Admits f ↔ (DependentFull.step levels O).Admits f := by
  constructor
  · rintro ⟨shapes, enabled, solvable, holds⟩
    exact ⟨(settledShapes_iff_of_plan levels settler (plan_of_frameTyped levels settler typed)).mp shapes,
      enabled, solvable, holds⟩
  · exact settling_admits_of_admits levels settler

/-- **The present step is the settling step that never settles**: the same admissions. -/
theorem never_admits_iff {s : State rules O} (f : Firing levels s) :
    (settlingStep levels O (Settler.never levels)).Admits f ↔ (DependentFull.step levels O).Admits f := by
  constructor
  · rintro ⟨shapes, enabled, solvable, holds⟩
    exact ⟨(settledShapes_iff_of_plan levels _ (plan_never levels f)).mp shapes, enabled, solvable, holds⟩
  · rintro ⟨shapes, enabled, solvable, holds⟩
    exact ⟨(settledShapes_iff_of_plan levels _ (plan_never levels f)).mpr shapes, enabled, solvable, holds⟩

/-- ... and the same results. -/
theorem never_result_eq {s : State rules O} {f : Firing levels s}
    (admitted : (settlingStep levels O (Settler.never levels)).Admits f) :
    (settlingStep levels O (Settler.never levels)).result f admitted =
      (DependentFull.step levels O).result f ((never_admits_iff levels f).mp admitted) :=
  settledState_eq_of_plan levels f (plan_never levels f) admitted.1.2.2.2.2
    ((never_admits_iff levels f).mp admitted).1.2.2.2.2

/-! ## Soundness, exactness and decision at the answer -/

omit [DecidableEq O] in
/-- What the plan is when the rows are not typed in the frame. -/
theorem plan_of_not_frameTyped {s : State rules O} {f : Firing levels s} (untyped : ¬ FrameTyped levels f) :
    plan levels settler f = (settler f.information).along := by
  unfold plan
  rw [if_neg untyped]

/-- **Soundness**: every made row of an admitted firing is typed after the match of its
information, up to agreement. -/
theorem settling_typedUpToAgreement {s : State rules O} {f : Firing levels s}
    (admitted : (settlingStep levels O settler).Admits f) :
    ∀ m ∈ f.makes, TypedUpToAgreement levels f.information m.2 := by
  intro m member
  have typedAlong : (m.2.reindex (plan levels settler f).2).WellTyped := admitted.1.2.2.2.2 m member
  by_cases typed : FrameTyped levels f
  · exact TypedAfterMatch.upToAgreement levels (typedAfterMatch_of_wellTyped levels _ (typed m member))
  · rw [plan_of_not_frameTyped levels settler typed] at typedAlong
    cases verdict : settler f.information with
    | settled M σ initial =>
        rw [verdict] at typedAlong
        exact settled_sound levels (principal_of_initial levels initial) typedAlong
    | postponed =>
        rw [verdict] at typedAlong
        have plain : m.2.WellTyped := by simpa only [Verdict.along, Make.reindex_id'] using typedAlong
        exact TypedAfterMatch.upToAgreement levels (typedAfterMatch_of_wellTyped levels _ plain)

/-- **Settling along a principal answer is an exact transition**: the solutions of the information
are, up to agreement, the composites through the answer of the solutions of the settled knowledge. -/
theorem settled_exact {M Δ : Context rules} {I : EquationStore (TotalTerm Δ)} {σ : M ⟶ Δ}
    (principal : (frames levels).Principal I σ) :
    UnificationWithLevels.Exact (frames levels) I σ ((frames levels).applyStore σ I) := by
  intro Θ τ
  constructor
  · intro solved
    obtain ⟨g, agree⟩ := principal.factors Θ τ solved
    exact ⟨g, agree, (Frames.models_applyStore (X := frames levels) σ g I).mpr
      (Frames.models_comp principal.sound g)⟩
  · rintro ⟨g, agree, solvedG⟩
    exact (UnificationWithLevels.models_of_agree agree I).mpr
      ((Frames.models_applyStore (X := frames levels) σ g I).mp solvedG)

/-- **Admission is decided at the answer**: when the settler settles a firing without queries whose
rows are not typed in the frame, admission is its shapes, its enabling, its made rows typed at the
answer and its guards at the answer. -/
theorem settled_admits_iff {s : State rules O} {f : Firing levels s} (untyped : ¬ FrameTyped levels f)
    (noQueries : f.queries = []) {M : Context rules} {σ : M ⟶ f.helpers.frame}
    {initial : InitialSolution (frames levels) f.information σ}
    (verdict : settler f.information = .settled M σ initial) :
    (settlingStep levels O settler).Admits f ↔
      (f.taken.Nodup ∧ f.made.Nodup ∧ f.takes.length = f.taken.length ∧ f.reads.length = f.read.length ∧
        ∀ m ∈ f.makes, (m.2.reindex σ).WellTyped) ∧
      Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ∧
      (frames levels).Models σ f.guards := by
  have principal := principal_of_initial levels initial
  have planned : plan levels settler f = ⟨M, σ⟩ := by
    rw [plan_of_not_frameTyped levels settler untyped, verdict]
    rfl
  have guards : (frames levels).Entails f.information (fun _ τ => f.Holds τ) ↔
      (frames levels).Models σ f.guards := by
    rw [← Frames.Principal.entails_models_iff principal f.guards]
    unfold Firing.Holds
    rw [noQueries]
    constructor
    · exact fun entailed b τ solved => (entailed b τ solved).1
    · exact fun entailed b τ solved => ⟨entailed b τ solved, fun q member => absurd member List.not_mem_nil⟩
  constructor
  · rintro ⟨shapes, enabled, _, holds⟩
    unfold SettledShapes at shapes
    rw [planned] at shapes
    exact ⟨shapes, enabled, guards.mp holds⟩
  · rintro ⟨shapes, enabled, holds⟩
    refine ⟨?_, enabled, principal.solvable, guards.mpr holds⟩
    unfold SettledShapes
    rw [planned]
    exact shapes

end Step

end NativeTypesOnTheStep

#print axioms NativeTypesOnTheStep.Settler.ideal_settles
#print axioms NativeTypesOnTheStep.Verdict.eq_postponed
#print axioms NativeTypesOnTheStep.settlingStep
#print axioms NativeTypesOnTheStep.settledState_eq_of_plan
#print axioms NativeTypesOnTheStep.settling_admits_of_admits
#print axioms NativeTypesOnTheStep.settling_result_eq
#print axioms NativeTypesOnTheStep.settling_admits_iff_of_frameTyped
#print axioms NativeTypesOnTheStep.never_admits_iff
#print axioms NativeTypesOnTheStep.never_result_eq
#print axioms NativeTypesOnTheStep.settling_typedUpToAgreement
#print axioms NativeTypesOnTheStep.settled_exact
#print axioms NativeTypesOnTheStep.settled_admits_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
