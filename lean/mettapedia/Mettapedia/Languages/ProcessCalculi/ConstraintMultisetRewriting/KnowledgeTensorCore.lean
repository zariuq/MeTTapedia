import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ContextualTensorInterpretation

/-!
# Runs are graded proofs, on the step itself

The step has opaque states, and its firings are indexed by the state they fire at. Its runs are
therefore already the cut-and-leaf proofs: the paths of the free category of events. What a proof
calculus adds is a frame rule, and on the step a frame is a placement beside another state
(`ContextualRunInterpretation`). The frame rule is admissible exactly on a grade, and the grade is
computed rule by rule.

* The **grade** of a run at a placement is `Checks`: every firing leaves the context unchanged
  (`domain`) and its placed candidate is admitted (`check`). `checks_append` is the grade of a cut:
  the earlier grade, and the later grade at the placement the earlier run leaves (`advanceRun`).
* `frame_law`: a run whose grade admits a placement has a native run at the placed state, ending
  at the advanced placement.
* `Places`, `realize_places`, `Places.similar`: the events of the native run are the placed
  candidates of the events of the local run, and this determines the native run up to the
  similarity of the transport.
* The grade has a **structural part** `Fits`: the context is unchanged and every placed candidate
  is prepared (shaped, enabled on fresh outputs, with solvable information). Permission is the
  rest. Admission is **stable under placement** (`Stable`) when a prepared placed candidate of an
  admitted firing is admitted. `stable_iff_fits_implies_checks`: the grade of every run is its
  structural part exactly for the stable admissions. For a guarded step, stability fails at a
  firing exactly when the guard of its placed candidate is not entailed (`not_stableAt_iff`), and
  a guard read through a map of targets is stable (`stableAt_of_guardTransport`).
  `stableAt_ofEffect_iff` and `stableAt_guarded_iff` say the same for a step built from an
  effect core and an admission, or a guard admission: stability is the persistence of the
  permission, or of the entailment, under placement.
* `tensor_execution`, `tensorChecks_iff`: the parallel composition of two runs is the cut of two
  framed runs, and its grade is the conjunction of the two grades.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore

universe uO uT uH uOcc uS uF uI uP

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} {P : Step X O State Firing}
  {T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P}
  (I : ContextualRunInterpretation.{uO,uT,uH,uOcc,uS,uF,uI,uP} T)

/-! ## The placement a run leaves, and the grade of a cut -/

/-- The placement a run leaves: the placement advanced past each of its firings. -/
def advanceRun : ∀ {left right : State}, I.Place left right → (run : P.Run left) →
    I.Place run.last right
  | _, _, place, .nil _ => place
  | _, _, place, .cons f allowed rest => advanceRun (I.advance place f allowed) rest

/-- The realization of a plan ends at the advanced placement. -/
theorem realize_target : ∀ {left right : State} (place : I.Place left right) (run : P.Run left)
    (plan : I.Plan place run), (plan.realize I place run).target = advanceRun I place run
  | _, _, _, .nil _, .nil _ => rfl
  | _, _, place, .cons f allowed rest, .cons _ _ tail =>
      realize_target (I.advance place f allowed) rest tail

/-- **The grade of a cut**: the grade of the earlier run, and the grade of the later run at the
placement the earlier run leaves. -/
theorem checks_append : ∀ {left right : State} (place : I.Place left right) (first : P.Run left)
    (second : P.Run first.last),
    I.Checks place (first.append second) ↔
      I.Checks place first ∧ I.Checks (advanceRun I place first) second
  | _, _, _, .nil _, _ => ⟨fun checked => ⟨trivial, checked⟩, fun checked => checked.2⟩
  | _, _, place, .cons f allowed rest, second => by
      show ((I.domain place f ∧ I.check place f) ∧
          I.Checks (I.advance place f allowed) (rest.append second)) ↔
        ((I.domain place f ∧ I.check place f) ∧ I.Checks (I.advance place f allowed) rest) ∧
          I.Checks (advanceRun I (I.advance place f allowed) rest) second
      rw [checks_append (I.advance place f allowed) rest second]
      exact and_assoc.symm

/-- **The frame law relative to the grade.** A run whose grade admits a placement has a native
run at the placed state, with as many firings, ending at the advanced placement up to an
isomorphism of the transport. -/
theorem frame_law {left right : State} (place : I.Place left right) (run : P.Run left)
    (checked : I.Checks place run) :
    ∃ real : I.Realization place run, real.target = advanceRun I place run :=
  ⟨(ContextualRunInterpretation.Plan.ofChecks I place run checked).realize I place run,
    realize_target I place run _⟩

/-! ## The events of a framed run -/

/-- A native run places a local run: firing by firing, the native firing is the placed candidate
of the local firing, and the rest is carried along a similar run. -/
inductive Places : {left right : State} → (place : I.Place left right) → P.Run left →
    P.Run (I.pair place).state → Prop
  | nil {left right : State} (place : I.Place left right) :
      Places place (.nil left) (.nil (I.pair place).state)
  | cons {left right : State} {place : I.Place left right} {f : Firing left}
      {allowed : P.Admits f} {rest : P.Run (P.result f allowed)} (framed : I.domain place f)
      (nativeAllowed : P.Admits (I.candidate place f))
      {later : P.Run (I.pair (I.advance place f allowed)).state}
      {moved : P.Run (P.result (I.candidate place f) nativeAllowed)}
      (tail : Places (I.advance place f allowed) rest later) (similar : T.Similar later moved) :
      Places place (.cons f allowed rest) (.cons (I.candidate place f) nativeAllowed moved)

/-- A placed run of a run that begins with a firing begins with the placed candidate of that
firing, and continues with a run similar to a placed run of the rest. -/
theorem Places.cons_inv {left right : State} {place : I.Place left right} {f : Firing left}
    {allowed : P.Admits f} {rest : P.Run (P.result f allowed)}
    {native : P.Run (I.pair place).state} (placed : Places I place (.cons f allowed rest) native) :
    ∃ (nativeAllowed : P.Admits (I.candidate place f))
      (moved : P.Run (P.result (I.candidate place f) nativeAllowed))
      (later : P.Run (I.pair (I.advance place f allowed)).state),
      native = .cons (I.candidate place f) nativeAllowed moved ∧ I.domain place f ∧
        Places I (I.advance place f allowed) rest later ∧ T.Similar later moved := by
  cases placed with
  | cons framed nativeAllowed tail similar =>
      exact ⟨nativeAllowed, _, _, rfl, framed, tail, similar⟩

/-- The realization of a plan places its local run. -/
theorem realize_places : ∀ {left right : State} (place : I.Place left right) (run : P.Run left)
    (plan : I.Plan place run), Places I place run (plan.realize I place run).execution
  | _, _, place, .nil _, .nil _ => Places.nil place
  | _, _, place, .cons f allowed rest, .cons framed nativeAllowed tail =>
      Places.cons framed nativeAllowed (realize_places (I.advance place f allowed) rest tail)
        (Transport.Similar.moveRun
          (T.symm (I.resultIso place f allowed framed nativeAllowed))
          (tail.realize I (I.advance place f allowed) rest).execution)

/-- **The placed run is determined up to similarity** by the local run and the placement. -/
theorem Places.similar : ∀ {left right : State} {place : I.Place left right} {run : P.Run left}
    {one two : P.Run (I.pair place).state}, Places I place run one → Places I place run two →
      T.Similar one two
  | _, _, _, _, _, _, .nil _, .nil _ => Transport.Similar.refl _
  | _, _, _, _, _, _, .cons _ _ tail similar, .cons _ _ tail' similar' =>
      Transport.Similar.cons_self
        (Transport.Similar.trans
          (Transport.Similar.trans (Transport.Similar.symm similar) (Places.similar tail tail'))
          similar')

/-- A placed run has as many firings as the local run. -/
theorem Places.length_eq : ∀ {left right : State} {place : I.Place left right} {run : P.Run left}
    {native : P.Run (I.pair place).state}, Places I place run native →
      native.word.length = run.word.length
  | _, _, _, _, _, .nil _ => rfl
  | _, _, _, _, _, .cons _ _ tail similar => by
      have lengths := Transport.Similar.length_eq similar
      have earlier := Places.length_eq tail
      show _ + 1 = _ + 1
      rw [← lengths, earlier]

/-- **Runs are graded proofs, on the step.** A run whose grade admits a placement has a native
run that places it, and any two such native runs are similar. -/
theorem placed_run_of_checks {left right : State} (place : I.Place left right) (run : P.Run left)
    (checked : I.Checks place run) :
    ∃ native : P.Run (I.pair place).state, Places I place run native ∧
      ∀ other : P.Run (I.pair place).state, Places I place run other → T.Similar native other :=
  ⟨((ContextualRunInterpretation.Plan.ofChecks I place run checked).realize I place run).execution,
    realize_places I place run _, fun _ placed => Places.similar I (realize_places I place run _) placed⟩

/-- A placed run exists only on the grade. -/
theorem checks_of_places : ∀ {left right : State} {place : I.Place left right} {run : P.Run left}
    {native : P.Run (I.pair place).state}, Places I place run native → I.Checks place run
  | _, _, _, _, _, .nil _ => trivial
  | _, _, place, .cons f allowed _, _, .cons framed nativeAllowed tail _ =>
      ⟨⟨framed, (I.admission place f allowed).mp nativeAllowed⟩, checks_of_places tail⟩

/-- **The grade is exactly where the frame rule applies.** -/
theorem exists_places_iff_checks {left right : State} (place : I.Place left right)
    (run : P.Run left) :
    (∃ native : P.Run (I.pair place).state, Places I place run native) ↔ I.Checks place run :=
  ⟨fun ⟨_, placed⟩ => checks_of_places I placed,
    fun checked => ⟨_, (placed_run_of_checks I place run checked).choose_spec.1⟩⟩

/-! ## The structural part of the grade, and permission -/

/-- The structural part of the grade: every firing leaves the context unchanged, and its placed
candidate is prepared. -/
def Fits : ∀ {left right : State}, I.Place left right → P.Run left → Prop
  | _, _, _, .nil _ => True
  | _, _, place, .cons f allowed rest =>
      (I.domain place f ∧ P.Prepares (I.candidate place f)) ∧ Fits (I.advance place f allowed) rest

/-- Admission of one firing is stable under one placement: where the context is unchanged and
the placed candidate is prepared, it is admitted. -/
def StableAt {left right : State} (place : I.Place left right) (f : Firing left) : Prop :=
  P.Admits f → I.domain place f → P.Prepares (I.candidate place f) → P.Admits (I.candidate place f)

/-- Admission is stable under placement. -/
def Stable : Prop :=
  ∀ {left right : State} (place : I.Place left right) (f : Firing left), StableAt I place f

/-- Every firing of a run is stable at the placement it meets. -/
def StableAlong : ∀ {left right : State}, I.Place left right → P.Run left → Prop
  | _, _, _, .nil _ => True
  | _, _, place, .cons f allowed rest =>
      StableAt I place f ∧ StableAlong (I.advance place f allowed) rest

/-- The grade implies its structural part. -/
theorem fits_of_checks : ∀ {left right : State} (place : I.Place left right) (run : P.Run left),
    I.Checks place run → Fits I place run
  | _, _, _, .nil _, _ => trivial
  | _, _, place, .cons f allowed rest, checked =>
      ⟨⟨checked.1.1, P.prepares ((I.admission place f allowed).mpr checked.1.2)⟩,
        fits_of_checks (I.advance place f allowed) rest checked.2⟩

/-- Along stable firings the structural part is the whole grade. -/
theorem checks_of_fits : ∀ {left right : State} (place : I.Place left right) (run : P.Run left),
    StableAlong I place run → Fits I place run → I.Checks place run
  | _, _, _, .nil _, _, _ => trivial
  | _, _, place, .cons f allowed rest, stable, fitted =>
      ⟨⟨fitted.1.1, (I.admission place f allowed).mp (stable.1 allowed fitted.1.1 fitted.1.2)⟩,
        checks_of_fits (I.advance place f allowed) rest stable.2 fitted.2⟩

theorem stableAlong_of_stable (stable : Stable I) :
    ∀ {left right : State} (place : I.Place left right) (run : P.Run left), StableAlong I place run
  | _, _, _, .nil _ => trivial
  | _, _, place, .cons f allowed rest =>
      ⟨stable place f, stableAlong_of_stable stable (I.advance place f allowed) rest⟩

/-- **The plain reading holds exactly for the stable admissions.** The grade of every run is its
structural part if and only if admission is stable under placement. -/
theorem stable_iff_fits_implies_checks :
    Stable I ↔ ∀ {left right : State} (place : I.Place left right) (run : P.Run left),
      Fits I place run → I.Checks place run := by
  constructor
  · intro stable left right place run fitted
    exact checks_of_fits I place run (stableAlong_of_stable I stable place run) fitted
  · intro plain left right place f allowed framed prepared
    have checked := plain place (.cons f allowed (.nil _)) ⟨⟨framed, prepared⟩, trivial⟩
    exact (I.admission place f allowed).mpr checked.1.2

/-! ## Guards -/

/-- **Where a guarded admission is graded.** Stability fails at a firing and a placement exactly
when the firing is admitted, the context is unchanged, the placed candidate is prepared, and the
guard of the placed candidate is not entailed by its information. -/
theorem not_stableAt_iff [P.Guarded] {left right : State} (place : I.Place left right)
    (f : Firing left) :
    ¬ StableAt I place f ↔ P.Admits f ∧ I.domain place f ∧ P.Prepares (I.candidate place f) ∧
      ¬ X.Entails (P.information (I.candidate place f)) (P.Holds (I.candidate place f)) := by
  constructor
  · intro unstable
    by_contra other
    apply unstable
    intro allowed framed prepared
    by_contra refused
    apply other
    refine ⟨allowed, framed, prepared, fun asked => refused ?_⟩
    exact (P.admits_iff_prepares _).mpr ⟨prepared, asked⟩
  · rintro ⟨allowed, framed, prepared, refused⟩ stable
    exact refused ((P.admits_iff_prepares _).mp (stable allowed framed prepared)).2

/-- The guard of a placed candidate reads the guard of the local firing: a map of targets along
which the candidate's information refines the firing's, and along which the guard is kept. -/
structure GuardTransportAt [P.Guarded] {left right : State} (place : I.Place left right)
    (f : Firing left) where
  through : Hom (P.target f) (P.target (I.candidate place f))
  refines : ∀ {b : Obj} (σ : Hom (P.target (I.candidate place f)) b),
    X.Models σ (P.information (I.candidate place f)) →
      X.Models (X.comp σ through) (P.information f)
  holds : ∀ {b : Obj} (σ : Hom (P.target (I.candidate place f)) b),
    X.Models σ (P.information (I.candidate place f)) →
      P.Holds f b (X.comp σ through) → P.Holds (I.candidate place f) b σ

/-- **A guard kept along a placement is stable there.** -/
theorem stableAt_of_guardTransport [P.Guarded] {left right : State} {place : I.Place left right}
    {f : Firing left} (G : GuardTransportAt I place f) : StableAt I place f := by
  intro allowed _ prepared
  refine (P.admits_iff_prepares _).mpr ⟨prepared, fun b σ solved => ?_⟩
  exact G.holds σ solved (((P.admits_iff_prepares f).mp allowed).2 b _ (G.refines σ solved))

/-- **Guards kept along every placement make admission stable.** -/
theorem stable_of_guardTransport [P.Guarded]
    (G : ∀ {left right : State} (place : I.Place left right) (f : Firing left),
      GuardTransportAt I place f) : Stable I :=
  fun place f => stableAt_of_guardTransport I (G place f)

/-! ## What the reading sees of an admission -/

/-- **An admission is stable at a placement exactly when permission persists there.** For the
step of an effect core under any admission: wherever a permitted candidate leaves the context
unchanged and its placed candidate is prepared, the placed candidate is permitted. -/
theorem stableAt_ofEffect_iff {E : EffectCore X O State Firing} {allow : E.Admission}
    {T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} (Step.ofEffect E allow)}
    (I : ContextualRunInterpretation.{uO,uT,uH,uOcc,uS,uF,uI,uP} T)
    {left right : State} (place : I.Place left right) (f : Firing left) :
    StableAt I place f ↔
      ((∃ prepared : E.Prepares f, allow f prepared) → I.domain place f →
        ∀ placed : E.Prepares (I.candidate place f), allow (I.candidate place f) placed) := by
  constructor
  · intro stable allowed framed placed
    obtain ⟨_, permitted⟩ := stable allowed framed placed
    exact permitted
  · intro persists allowed framed placed
    exact ⟨placed, persists allowed framed placed⟩

/-- **A guard admission is stable at a placement exactly when the entailment persists there.**
For the step of an effect core under `guardAdmission`: the observation entailed by the
information of the firing is entailed by the information of its placed candidate. -/
theorem stableAt_guarded_iff {E : EffectCore X O State Firing}
    {holds : ∀ {s : State} (f : Firing s) (b : Obj), Hom (E.target f) b → Prop}
    {T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} (Step.guarded E holds)}
    (I : ContextualRunInterpretation.{uO,uT,uH,uOcc,uS,uF,uI,uP} T)
    {left right : State} (place : I.Place left right) (f : Firing left) :
    StableAt I place f ↔
      (E.Prepares f → X.Entails (E.information f) (holds f) → I.domain place f →
        E.Prepares (I.candidate place f) →
          X.Entails (E.information (I.candidate place f)) (holds (I.candidate place f))) := by
  constructor
  · intro stable prepared asked framed placed
    obtain ⟨_, entailed⟩ := stable ⟨prepared, asked⟩ framed placed
    exact entailed
  · intro persists allowed framed placed
    obtain ⟨prepared, asked⟩ := allowed
    exact ⟨placed, persists prepared asked framed placed⟩

/-! ## The tensor is the cut of two framed runs -/

/-- **The parallel composition of two runs is the cut of two framed runs**: the first run placed
beside the start of the second, then the second placed beside the end of the first. -/
theorem tensor_execution (flip : I.Flip) {left right : State} {place : I.Place left right}
    {first : P.Run left} {second : P.Run right} (plan : I.TensorPlan flip place first second) :
    (plan.realize I flip).execution =
      (plan.leftPlan.realize I place first).execution.append
        (T.moveRun
          (T.trans (flip.stateIso (plan.leftPlan.realize I place first).target)
            (T.symm (plan.leftPlan.realize I place first).resultIso))
          (plan.rightPlan.realize I
            (flip.swap (plan.leftPlan.realize I place first).target) second).execution) :=
  rfl

/-- **The grade of a tensor**: the grade of the first run at the placement, and the grade of the
second at the swapped placement the first run leaves. -/
theorem tensorChecks_iff (flip : I.Flip) {left right : State} (place : I.Place left right)
    (first : P.Run left) (second : P.Run right) :
    I.TensorChecks flip place first second ↔
      I.Checks place first ∧ I.Checks (flip.swap (advanceRun I place first)) second := by
  constructor
  · rintro ⟨leftChecks, rightChecks⟩
    rw [realize_target] at rightChecks
    exact ⟨leftChecks, rightChecks⟩
  · rintro ⟨leftChecks, rightChecks⟩
    refine ⟨leftChecks, ?_⟩
    rw [realize_target]
    exact rightChecks

/-- A tensor of two runs exists exactly on the conjunction of their grades. -/
theorem tensor_plan_iff_grades (flip : I.Flip) {left right : State} (place : I.Place left right)
    (first : P.Run left) (second : P.Run right) :
    Nonempty (I.TensorPlan flip place first second) ↔
      I.Checks place first ∧ I.Checks (flip.swap (advanceRun I place first)) second :=
  (I.tensor_plan_iff_checks flip place first second).trans (tensorChecks_iff I flip place first second)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore
