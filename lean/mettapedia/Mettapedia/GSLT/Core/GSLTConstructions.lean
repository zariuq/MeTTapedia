import Mettapedia.GSLT.Core.Composition
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Nat

set_option linter.dupNamespace false

/-!
# The GSLT construction pack

`Composition` builds GSLTs side by side over a sum carrier
(`disjointSum`, `interactingSum`).  This module supplies the remaining
elementary ways of making one theory out of others, each with the
comparison theorem it owes to its inputs:

```
  operation             carrier      steps                 owes
  ─────────────         ──────────   ───────────────────   ─────────────────
  spendLift            Term × V     base step, grade      erasure: preserves
                                     multiplied onto an    always; reflects
                                     accumulator           exactly when total
  restrict              Term         pruned by a policy    simulation only,
                                                           strict at refusals
  synchronousProduct    A × B        both components       projections erase
                                     step together         to component steps
  interleavingProduct   A × B        exactly one           each component
                                     component steps       embeds at any
                                                           frozen partner
  quotientBy            Term         unchanged             steps preserved
                        (coarser E)                        verbatim; equality
                                                           only coarsens
  closure               Term         finitely many steps,  contains the base;
                                     up to equivalence     reflexive and
                                                           transitive
```

Three remarks the table compresses:

* **Grades are extra structure, necessarily.**  Steps are propositions
  and proof-irrelevant, so no grade can be read off a step proof; a
  `StepSpend` is a `V`-indexed refinement of the step relation, exactly
  as a weight table is genuine additional syntax.  A partial grading
  deliberately has no totality field — an ungraded step does not lift;
  totality is the separate predicate `StepSpend.Total`.
* **Quotient stays on the same carrier.**  Coarsening the equations is an
  operation *within* the theory's own space; its entire content is the
  obligation that the untouched step relation respect the coarser
  equality.  Canonicalization presents exactly such a coarsening: terms
  are identified when their canonical representatives agree.
* **Closure is level-preserving.**  Reflexive-transitive completion is an
  ordinary endo-operation on the step relation; the only care needed is
  closing up to equivalence, since a GSLT's right-respect law demands the
  exact target, not a merely equivalent one.
-/

namespace Mettapedia.GSLT

namespace GSLT

universe u v

variable (S : GSLT)

/-! ## Step grading -/

/-- A `V`-indexed refinement of the step relation: `graded s t v` says the
system steps from `s` to `t` *at grade `v`*.  Soundness confines grades to
real steps; the two respect fields make the refinement well defined on
equivalence classes, grade included.

There is deliberately no totality field.  A step no clause grades does not
lift — the inert reading.  See `Total` for the opposite commitment. -/
structure StepSpend (V : Type v) where
  graded : S.Term → S.Term → V → Prop
  sound : ∀ {source target : S.Term} {grade : V},
    graded source target grade → S.Step source target
  resp_left : ∀ {source source' target : S.Term} {grade : V},
    S.Equiv source source' → graded source target grade →
    ∃ target', graded source' target' grade ∧ S.Equiv target target'
  resp_right : ∀ {source target target' : S.Term} {grade : V},
    graded source target grade → S.Equiv target target' →
    graded source target' grade

namespace StepSpend

variable {S : GSLT} {V : Type v}

/-- Totality: every step carries at least one grade.  This is the *gated*
commitment a caller must supply to obtain the reflection half of erasure. -/
def Total (grading : StepSpend S V) : Prop :=
  ∀ {source target : S.Term}, S.Step source target →
    ∃ grade, grading.graded source target grade

end StepSpend

/-! ## The graded lift -/

/-- The product setoid: base equivalence on the state, exact equality on
the accumulator. -/
def spendSetoid (V : Type v) : Setoid (S.Term × V) where
  r := fun source target => S.Equiv source.1 target.1 ∧ source.2 = target.2
  iseqv :=
    ⟨fun _ => ⟨S.equations.iseqv.refl _, rfl⟩,
      fun related => ⟨S.equations.iseqv.symm related.1, related.2.symm⟩,
      fun first second =>
        ⟨S.equations.iseqv.trans first.1 second.1,
          first.2.trans second.2⟩⟩

/-- **The graded lift**: one system re-run over `Term × V`, every graded
step multiplying the accumulator on the right by its grade.  A lift of one
system, not a combination of two: the accumulator has no steps of its own. -/
def spendLift {V : Type v} [Monoid V] (grading : StepSpend S V) : GSLT where
  Term := S.Term × V
  equations := S.spendSetoid V
  rewrites := fun source target =>
    ∃ grade, grading.graded source.1 target.1 grade ∧
      target.2 = source.2 * grade
  rewrites_resp_left := by
    rintro source source' target ⟨stateEq, accumulatorEq⟩
      ⟨grade, graded, accumulated⟩
    obtain ⟨state', graded', stateEq'⟩ := grading.resp_left stateEq graded
    exact ⟨(state', source'.2 * grade), ⟨grade, graded', rfl⟩,
      stateEq', by rw [accumulated, accumulatorEq]⟩
  rewrites_resp_right := by
    rintro source target target' ⟨grade, graded, accumulated⟩
      ⟨stateEq, accumulatorEq⟩
    exact ⟨grade, grading.resp_right graded stateEq,
      accumulatorEq ▸ accumulated⟩

section GradedLift

variable {S : GSLT} {V : Type v} [Monoid V] (grading : StepSpend S V)

@[simp] theorem spendLift_Term :
    (S.spendLift grading).Term = (S.Term × V) := rfl

theorem spendLift_step_iff {source target : S.Term × V} :
    (S.spendLift grading).Step source target ↔
      ∃ grade, grading.graded source.1 target.1 grade ∧
        target.2 = source.2 * grade := Iff.rfl

/-- Erasure, preservation half: projecting the accumulator away sends
every lifted step to a base step.  Holds for every grading, total or not. -/
theorem spendLift_erase_step {source target : S.Term × V}
    (step : (S.spendLift grading).Step source target) :
    S.Step source.1 target.1 := by
  obtain ⟨grade, graded, _⟩ := step
  exact grading.sound graded

/-- Erasure, reflection half: when the grading is total, every base step
lifts from every accumulator value.  Together with the preservation half,
the projection is then surjective on steps with full fibres. -/
theorem spendLift_lift_step (total : grading.Total)
    {source target : S.Term} (step : S.Step source target)
    (accumulator : V) :
    ∃ value, (S.spendLift grading).Step (source, accumulator)
      (target, value) := by
  obtain ⟨grade, graded⟩ := total step
  exact ⟨accumulator * grade, grade, graded, rfl⟩

/-- Grades act by left translation: every lifted step is the unit-based
step translated by the source accumulator. -/
theorem spendLift_step_action {source target : S.Term}
    {before after : V} :
    (S.spendLift grading).Step (source, before) (target, after) ↔
      ∃ weight,
        (S.spendLift grading).Step (source, 1) (target, weight) ∧
        after = before * weight := by
  constructor
  · rintro ⟨grade, graded, accumulated⟩
    dsimp only at accumulated
    exact ⟨1 * grade, ⟨grade, graded, rfl⟩, by rw [accumulated, one_mul]⟩
  · rintro ⟨weight, ⟨grade, graded, weightEq⟩, accumulated⟩
    dsimp only at weightEq
    refine ⟨grade, graded, ?_⟩
    dsimp only
    rw [accumulated, weightEq, one_mul]

/-- Every lifted run factors through its accumulated weight. -/
theorem spendLift_multiStep_factors {source target : S.Term × V}
    (path : (S.spendLift grading).MultiStep source target) :
    ∃ weight, target.2 = source.2 * weight := by
  refine @GSLT.MultiStep.rec (S.spendLift grading)
    (fun first last _ => ∃ weight, last.2 = first.2 * weight)
    ?_ ?_ source target path
  · intro term
    exact ⟨1, (mul_one term.2).symm⟩
  · intro first middle last firstStep _ inductionHypothesis
    obtain ⟨grade, _, accumulated⟩ := firstStep
    obtain ⟨weight, factored⟩ := inductionHypothesis
    exact ⟨grade * weight, by rw [factored, accumulated, mul_assoc]⟩

end GradedLift

/-! ## Restriction -/

/-- A step filter: a policy keeping some steps, stated with the respect
laws that make the pruned relation well defined on equivalence classes.
`resp_left` must supply the surviving step itself, because the filter's
choice of successor may have to move with the equivalence. -/
structure StepFilter where
  keep : S.Term → S.Term → Prop
  keep_sound : ∀ {source target : S.Term},
    keep source target → S.Step source target
  resp_left : ∀ {source source' target : S.Term},
    S.Equiv source source' → keep source target →
    ∃ target', keep source' target' ∧ S.Equiv target target'
  resp_right : ∀ {source target target' : S.Term},
    keep source target → S.Equiv target target' → keep source target'

/-- **Restriction**: same carrier, same equations, pruned steps.  The
shape of every resolution policy. -/
def restrict (filter : StepFilter S) : GSLT where
  Term := S.Term
  equations := S.equations
  rewrites := filter.keep
  rewrites_resp_left := filter.resp_left
  rewrites_resp_right := filter.resp_right

section Restrict

variable {S : GSLT} (filter : StepFilter S)

@[simp] theorem restrict_Term : (S.restrict filter).Term = S.Term := rfl

theorem restrict_step_iff {source target : S.Term} :
    (S.restrict filter).Step source target ↔ filter.keep source target :=
  Iff.rfl

/-- Simulation — the only comparison theorem restriction can owe: every
kept step is a base step. -/
theorem restrict_simulation {source target : S.Term}
    (kept : (S.restrict filter).Step source target) :
    S.Step source target :=
  filter.keep_sound kept

/-- The simulation is strict at every genuinely refused step. -/
theorem restrict_strict {source target : S.Term}
    (step : S.Step source target) (refused : ¬ filter.keep source target) :
    S.Step source target ∧
      ¬ (S.restrict filter).Step source target :=
  ⟨step, refused⟩

end Restrict

/-! ## Products -/

/-- The product setoid on a pair of theories. -/
def productSetoid (left right : GSLT) : Setoid (left.Term × right.Term) where
  r := fun source target =>
    left.Equiv source.1 target.1 ∧ right.Equiv source.2 target.2
  iseqv :=
    ⟨fun _ => ⟨left.equations.iseqv.refl _, right.equations.iseqv.refl _⟩,
      fun related =>
        ⟨left.equations.iseqv.symm related.1,
          right.equations.iseqv.symm related.2⟩,
      fun first second =>
        ⟨left.equations.iseqv.trans first.1 second.1,
          right.equations.iseqv.trans first.2 second.2⟩⟩

/-- **The synchronous product**: both components step together.  This is
the lockstep composition; a state is a state of each component
simultaneously, and a step is a step of each. -/
def synchronousProduct (left right : GSLT) : GSLT where
  Term := left.Term × right.Term
  equations := productSetoid left right
  rewrites := fun source target =>
    left.Step source.1 target.1 ∧ right.Step source.2 target.2
  rewrites_resp_left := by
    rintro source source' target ⟨leftEq, rightEq⟩ ⟨leftStep, rightStep⟩
    obtain ⟨leftTarget, leftStep', leftTargetEq⟩ :=
      left.rewrites_resp_left leftEq leftStep
    obtain ⟨rightTarget, rightStep', rightTargetEq⟩ :=
      right.rewrites_resp_left rightEq rightStep
    exact ⟨(leftTarget, rightTarget), ⟨leftStep', rightStep'⟩,
      leftTargetEq, rightTargetEq⟩
  rewrites_resp_right := by
    rintro source target target' ⟨leftStep, rightStep⟩ ⟨leftEq, rightEq⟩
    exact ⟨left.rewrites_resp_right leftStep leftEq,
      right.rewrites_resp_right rightStep rightEq⟩

/-- **The interleaving product**: exactly one component steps while the
other holds still.  This is the asynchronous composition of independent
systems; genuine concurrency licenses live here once non-interference is
supplied. -/
def interleavingProduct (left right : GSLT) : GSLT where
  Term := left.Term × right.Term
  equations := productSetoid left right
  rewrites := fun source target =>
    (left.Step source.1 target.1 ∧ right.Equiv source.2 target.2) ∨
      (left.Equiv source.1 target.1 ∧ right.Step source.2 target.2)
  rewrites_resp_left := by
    rintro source source' target ⟨leftEq, rightEq⟩
      (⟨leftStep, rightHold⟩ | ⟨leftHold, rightStep⟩)
    · obtain ⟨leftTarget, leftStep', leftTargetEq⟩ :=
        left.rewrites_resp_left leftEq leftStep
      exact ⟨(leftTarget, target.2),
        Or.inl ⟨leftStep',
          (right.equations.iseqv.trans (right.equations.iseqv.symm rightEq)
            rightHold)⟩,
        leftTargetEq, right.equations.iseqv.refl _⟩
    · obtain ⟨rightTarget, rightStep', rightTargetEq⟩ :=
        right.rewrites_resp_left rightEq rightStep
      exact ⟨(target.1, rightTarget),
        Or.inr ⟨(left.equations.iseqv.trans
            (left.equations.iseqv.symm leftEq) leftHold),
          rightStep'⟩,
        left.equations.iseqv.refl _, rightTargetEq⟩
  rewrites_resp_right := by
    rintro source target target'
      (⟨leftStep, rightHold⟩ | ⟨leftHold, rightStep⟩) ⟨leftEq, rightEq⟩
    · exact Or.inl ⟨left.rewrites_resp_right leftStep leftEq,
        right.equations.iseqv.trans rightHold rightEq⟩
    · exact Or.inr ⟨left.equations.iseqv.trans leftHold leftEq,
        right.rewrites_resp_right rightStep rightEq⟩

section Products

variable {left right : GSLT}

theorem synchronousProduct_step_iff
    {source target : left.Term × right.Term} :
    (synchronousProduct left right).Step source target ↔
      left.Step source.1 target.1 ∧ right.Step source.2 target.2 :=
  Iff.rfl

/-- Both projections of a synchronous step are component steps. -/
theorem synchronousProduct_erase_left
    {source target : left.Term × right.Term}
    (step : (synchronousProduct left right).Step source target) :
    left.Step source.1 target.1 := step.1

theorem synchronousProduct_erase_right
    {source target : left.Term × right.Term}
    (step : (synchronousProduct left right).Step source target) :
    right.Step source.2 target.2 := step.2

theorem interleavingProduct_step_iff
    {source target : left.Term × right.Term} :
    (interleavingProduct left right).Step source target ↔
      (left.Step source.1 target.1 ∧ right.Equiv source.2 target.2) ∨
        (left.Equiv source.1 target.1 ∧ right.Step source.2 target.2) :=
  Iff.rfl

/-- Each component embeds into the interleaving at any frozen partner. -/
theorem interleavingProduct_step_left
    {source target : left.Term} (step : left.Step source target)
    (partner : right.Term) :
    (interleavingProduct left right).Step (source, partner)
      (target, partner) :=
  Or.inl ⟨step, right.equations.iseqv.refl _⟩

theorem interleavingProduct_step_right
    {source target : right.Term} (step : right.Step source target)
    (partner : left.Term) :
    (interleavingProduct left right).Step (partner, source)
      (partner, target) :=
  Or.inr ⟨left.equations.iseqv.refl _, step⟩

/-- An interleaving step moves at least one component by a genuine step. -/
theorem interleavingProduct_erase
    {source target : left.Term × right.Term}
    (step : (interleavingProduct left right).Step source target) :
    left.Step source.1 target.1 ∨ right.Step source.2 target.2 := by
  rcases step with ⟨leftStep, _⟩ | ⟨_, rightStep⟩
  · exact Or.inl leftStep
  · exact Or.inr rightStep

/-- **Independent component steps form a commuting square.**  A left step
and a right step may be taken in either order and reach the same product
state.  This is the precise non-interference license supplied by product
decomposition; it assumes real component separation, not merely labels that
claim two effects are disjoint. -/
theorem interleavingProduct_commutingSquare
    {leftSource leftTarget : left.Term}
    {rightSource rightTarget : right.Term}
    (leftStep : left.Step leftSource leftTarget)
    (rightStep : right.Step rightSource rightTarget) :
    (interleavingProduct left right).Step
        (leftSource, rightSource) (leftTarget, rightSource) ∧
      (interleavingProduct left right).Step
        (leftTarget, rightSource) (leftTarget, rightTarget) ∧
      (interleavingProduct left right).Step
        (leftSource, rightSource) (leftSource, rightTarget) ∧
      (interleavingProduct left right).Step
        (leftSource, rightTarget) (leftTarget, rightTarget) := by
  exact ⟨interleavingProduct_step_left leftStep rightSource,
    interleavingProduct_step_right rightStep leftTarget,
    interleavingProduct_step_right rightStep leftSource,
    interleavingProduct_step_left leftStep rightTarget⟩

end Products

/-! ### Negative control: nondeterminism alone supplies no diamond -/

/-- A three-state fork with two terminal branches. -/
private def forkGSLT : GSLT where
  Term := Fin 3
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target =>
    source = 0 ∧ (target = 1 ∨ target = 2)
  rewrites_resp_left := by
    rintro source source' target rfl step
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    rintro source target target' step rfl
    exact step

/-- Two steps from one source need not commute.  The product theorem above
earns its diamond from component separation, not from nondeterminism by
itself. -/
example :
    forkGSLT.Step (0 : Fin 3) (1 : Fin 3) ∧
      forkGSLT.Step (0 : Fin 3) (2 : Fin 3) ∧
      ¬ ∃ join,
        forkGSLT.Step (1 : Fin 3) join ∧
          forkGSLT.Step (2 : Fin 3) join := by
  constructor
  · exact ⟨rfl, Or.inl rfl⟩
  constructor
  · exact ⟨rfl, Or.inr rfl⟩
  · rintro ⟨join, first, _⟩
    exact Fin.zero_ne_one first.1.symm

/-! ## Quotient -/

/-- A coarsening of a theory's equations: a new setoid containing the old
one, together with the proof that the untouched step relation respects
it.  That proof is the entire content of quotienting — the operation
itself changes nothing else. -/
structure Coarsening (S : GSLT) where
  setoid : Setoid S.Term
  coarser : ∀ {source target : S.Term},
    S.Equiv source target → setoid.r source target
  resp_left : ∀ {source source' target : S.Term},
    setoid.r source source' → S.Step source target →
    ∃ target', S.Step source' target' ∧ setoid.r target target'
  resp_right : ∀ {source target target' : S.Term},
    S.Step source target → setoid.r target target' →
    S.Step source target'

/-- **Quotient**: same carrier, same steps, coarser equality.
Canonicalization presents exactly such a coarsening — terms are
identified when their canonical representatives agree. -/
def quotientBy (S : GSLT) (coarsening : Coarsening S) : GSLT where
  Term := S.Term
  equations := coarsening.setoid
  rewrites := S.rewrites
  rewrites_resp_left := coarsening.resp_left
  rewrites_resp_right := coarsening.resp_right

section Quotient

variable {S : GSLT} (coarsening : Coarsening S)

@[simp] theorem quotientBy_Term : (S.quotientBy coarsening).Term = S.Term :=
  rfl

/-- Steps are preserved verbatim: quotienting touches only equality. -/
theorem quotientBy_step_iff {source target : S.Term} :
    (S.quotientBy coarsening).Step source target ↔ S.Step source target :=
  Iff.rfl

/-- Old equalities remain equalities. -/
theorem quotientBy_equiv_of_equiv {source target : S.Term}
    (equivalent : S.Equiv source target) :
    (S.quotientBy coarsening).Equiv source target :=
  coarsening.coarser equivalent

end Quotient

/-! ## Closure -/

/-- Finite runs transport along source equivalence, reaching an
equivalent end. -/
private theorem multiStep_resp_left {S : GSLT} :
    ∀ {first last : S.Term}, S.MultiStep first last →
      ∀ {first' : S.Term}, S.Equiv first first' →
      ∃ last', S.MultiStep first' last' ∧ S.Equiv last last' := by
  intro first last path
  induction path with
  | refl term =>
      intro first' equivalent
      exact ⟨first', .refl first', equivalent⟩
  | step firstStep rest inductionHypothesis =>
      intro first' equivalent
      obtain ⟨middle', middleStep, middleEq⟩ :=
        S.rewrites_resp_left equivalent firstStep
      obtain ⟨last', path', lastEq⟩ := inductionHypothesis middleEq
      exact ⟨last', .step middleStep path', lastEq⟩

/-- **Reflexive-transitive closure, up to equivalence**: the theory whose
steps are finite runs of the base theory ending at an equivalent term.
Closing up to equivalence is forced: the right-respect law of a GSLT
demands the exact target, and a zero-length run can reach an equivalent
term only through the equations. -/
def closure (S : GSLT) : GSLT where
  Term := S.Term
  equations := S.equations
  rewrites := fun source target =>
    ∃ reached, S.MultiStep source reached ∧ S.Equiv reached target
  rewrites_resp_left := by
    rintro source source' target sourceEq ⟨reached, path, reachedEq⟩
    obtain ⟨reached', path', reachedEq'⟩ :=
      multiStep_resp_left path sourceEq
    exact ⟨target,
      ⟨reached', path',
        S.equations.iseqv.trans (S.equations.iseqv.symm reachedEq')
          reachedEq⟩,
      S.equations.iseqv.refl _⟩
  rewrites_resp_right := by
    rintro source target target' ⟨reached, path, reachedEq⟩ targetEq
    exact ⟨reached, path, S.equations.iseqv.trans reachedEq targetEq⟩

section Closure

variable {S : GSLT}

@[simp] theorem closure_Term : S.closure.Term = S.Term := rfl

theorem closure_step_iff {source target : S.Term} :
    S.closure.Step source target ↔
      ∃ reached, S.MultiStep source reached ∧ S.Equiv reached target :=
  Iff.rfl

/-- The closure contains the base theory. -/
theorem closure_step_of_step {source target : S.Term}
    (step : S.Step source target) : S.closure.Step source target :=
  ⟨target, .step step (.refl target), S.equations.iseqv.refl _⟩

/-- The closure is reflexive. -/
theorem closure_step_refl (term : S.Term) : S.closure.Step term term :=
  ⟨term, .refl term, S.equations.iseqv.refl _⟩

private theorem multiStep_append {first middle last : S.Term}
    (front : S.MultiStep first middle) (back : S.MultiStep middle last) :
    S.MultiStep first last := by
  induction front with
  | refl _ => exact back
  | step firstStep _ inductionHypothesis =>
      exact .step firstStep (inductionHypothesis back)

/-- The closure is transitive. -/
theorem closure_step_trans {first second third : S.Term}
    (front : S.closure.Step first second)
    (back : S.closure.Step second third) : S.closure.Step first third := by
  obtain ⟨reachedFront, pathFront, frontEq⟩ := front
  obtain ⟨reachedBack, pathBack, backEq⟩ := back
  obtain ⟨reachedBack', pathBack', backEq'⟩ :=
    multiStep_resp_left pathBack (S.equations.iseqv.symm frontEq)
  exact ⟨reachedBack', multiStep_append pathFront pathBack',
    S.equations.iseqv.trans (S.equations.iseqv.symm backEq') backEq⟩

end Closure

/-! ## Spending and choosing: the separation theorems

Three roles hide under the word "grade".  A **spend** decorates steps and
accumulates along the run (writer role: `StepSpend`, `spendLift`).  A
**weigh** values candidates by observation (quantifier role:
`WeighClause`, in the scheduler).  A **choose** prunes the step relation
by a policy (selection role: `StepFilter`, `restrict`).  The theorems
below separate spend from choose:

* `spendLift_restrict_comm` — a choice policy that reads only the state
  commutes with the spend lift.  **Spending is invisible to state-level
  choice**; this is the machine-checked content of "cost is orthogonal
  to truth grading".
* `budget_filter_not_base_expressible` — the converse.  A policy that
  reads the ledger (refuse once expenditure exceeds a bound) is not
  expressible as any base policy.  The axes couple exactly when the
  guard consults accumulated cost — the optimization regime (tropical
  shortest-path being the canonical inhabitant).
-/

section SpendChooseSeparation

/-- Lift a base-level choice policy to the spend-lifted system.  The
policy reads **only the erased state pair** — never the accumulator. -/
def StepFilter.lifted {S : GSLT} {C : Type v} [Monoid C]
    (spend : StepSpend S C) (filter : StepFilter S) :
    StepFilter (S.spendLift spend) where
  keep := fun source target =>
    (S.spendLift spend).Step source target ∧
      filter.keep source.1 target.1
  keep_sound := And.left
  resp_left := by
    rintro source source' target equiv ⟨step, keepBase⟩
    obtain ⟨target', step', equiv'⟩ :=
      (S.spendLift spend).rewrites_resp_left equiv step
    refine ⟨target', ⟨step', ?_⟩, equiv'⟩
    obtain ⟨targetBase, keepBase', equivBase⟩ :=
      filter.resp_left equiv.1 keepBase
    exact filter.resp_right keepBase'
      (S.equations.iseqv.trans (S.equations.iseqv.symm equivBase) equiv'.1)
  resp_right := by
    rintro source target target' ⟨step, keepBase⟩ equiv
    exact ⟨(S.spendLift spend).rewrites_resp_right step equiv,
      filter.resp_right keepBase equiv.1⟩

/-- Restrict a spend to the steps a base choice policy keeps. -/
def StepSpend.restrictBy {S : GSLT} {C : Type v}
    (spend : StepSpend S C) (filter : StepFilter S) :
    StepSpend (S.restrict filter) C where
  graded := fun source target grade =>
    spend.graded source target grade ∧ filter.keep source target
  sound := And.right
  resp_left := by
    rintro source source' target grade equiv ⟨graded, keep⟩
    obtain ⟨targetKeep, keep', equivKeep⟩ := filter.resp_left equiv keep
    obtain ⟨targetGrade, graded', equivGrade⟩ :=
      spend.resp_left equiv graded
    refine ⟨targetKeep, ⟨?_, keep'⟩, equivKeep⟩
    exact spend.resp_right graded'
      (S.equations.iseqv.trans (S.equations.iseqv.symm equivGrade) equivKeep)
  resp_right := by
    rintro source target target' grade ⟨graded, keep⟩ equiv
    exact ⟨spend.resp_right graded equiv, filter.resp_right keep equiv⟩

/-- **Spend/choose commutation.**  Restricting the spend-lifted system by
a lifted state-level policy is, step for step, the spend-lift of the
restricted base system.  A choice that never reads the ledger cannot
tell whether the ledger is being kept. -/
theorem spendLift_restrict_comm {S : GSLT} {C : Type v} [Monoid C]
    (spend : StepSpend S C) (filter : StepFilter S)
    (source target : S.Term × C) :
    ((S.spendLift spend).restrict (filter.lifted spend)).Step
        source target ↔
      ((S.restrict filter).spendLift (spend.restrictBy filter)).Step
        source target := by
  constructor
  · rintro ⟨⟨grade, graded, accumulated⟩, keepBase⟩
    exact ⟨grade, ⟨graded, keepBase⟩, accumulated⟩
  · rintro ⟨grade, ⟨graded, keepBase⟩, accumulated⟩
    exact ⟨⟨grade, graded, accumulated⟩, keepBase⟩

/-- The two composites also share their equations on the nose. -/
theorem spendLift_restrict_comm_equations {S : GSLT} {C : Type v}
    [Monoid C] (spend : StepSpend S C) (filter : StepFilter S) :
    ((S.spendLift spend).restrict (filter.lifted spend)).equations =
      ((S.restrict filter).spendLift
        (spend.restrictBy filter)).equations := rfl

/-- One state, one always-enabled step: the minimal spending system. -/
def tickSystem : GSLT where
  Term := Unit
  equations :=
    ⟨fun _ _ => True,
      ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩⟩
  rewrites := fun _ _ => True
  rewrites_resp_left := fun _ _ => ⟨(), trivial, trivial⟩
  rewrites_resp_right := fun _ _ => trivial

/-- Every tick costs two. -/
def tickSpend : StepSpend tickSystem ℕ where
  graded := fun _ _ grade => grade = 2
  sound := fun _ => trivial
  resp_left := fun _ graded => ⟨(), graded, trivial⟩
  resp_right := fun graded _ => graded

/-- The budget policy: refuse any step whose resulting expenditure
exceeds eight.  This policy reads the accumulator. -/
def budgetFilter : StepFilter (tickSystem.spendLift tickSpend) where
  keep := fun source target =>
    (tickSystem.spendLift tickSpend).Step source target ∧ target.2 ≤ 8
  keep_sound := And.left
  resp_left := by
    rintro source source' target ⟨-, accumulatorEq⟩
      ⟨⟨grade, gradeEq, accumulated⟩, budget⟩
    subst gradeEq
    refine ⟨((), source'.2 * 2), ⟨⟨2, rfl, rfl⟩, ?_⟩, ⟨trivial, ?_⟩⟩
    · rw [accumulated] at budget
      rw [accumulatorEq] at budget
      exact budget
    · rw [accumulated, accumulatorEq]
  resp_right := by
    rintro source target target' ⟨step, budget⟩ ⟨-, accumulatorEq⟩
    refine ⟨(tickSystem.spendLift tickSpend).rewrites_resp_right step
      ⟨trivial, accumulatorEq⟩, ?_⟩
    rw [← accumulatorEq]
    exact budget

/-- **The converse of commutation.**  No base-level choice policy
reproduces the budget policy: any candidate either keeps the tick — and
then permits a spend the budget refuses (`8 ↦ 16`) — or drops it, and
then refuses a spend the budget permits (`1 ↦ 2`).  Coupling between
the axes occurs exactly when the guard reads accumulated cost. -/
theorem budget_filter_not_base_expressible :
    ¬ ∃ filter : StepFilter tickSystem,
      ∀ source target,
        ((tickSystem.spendLift tickSpend).restrict budgetFilter).Step
            source target ↔
          ((tickSystem.restrict filter).spendLift
            (tickSpend.restrictBy filter)).Step source target := by
  rintro ⟨filter, agree⟩
  by_cases keep : filter.keep () ()
  · have overspend :
        ((tickSystem.restrict filter).spendLift
          (tickSpend.restrictBy filter)).Step ((), 8) ((), 16) :=
      ⟨2, ⟨rfl, keep⟩, rfl⟩
    obtain ⟨-, bound⟩ := (agree ((), 8) ((), 16)).mpr overspend
    omega
  · have inBudget :
        ((tickSystem.spendLift tickSpend).restrict budgetFilter).Step
          ((), 1) ((), 2) :=
      ⟨⟨2, rfl, rfl⟩, by omega⟩
    obtain ⟨grade, ⟨-, kept⟩, -⟩ := (agree ((), 1) ((), 2)).mp inBudget
    exact keep kept

end SpendChooseSeparation


end GSLT

end Mettapedia.GSLT
