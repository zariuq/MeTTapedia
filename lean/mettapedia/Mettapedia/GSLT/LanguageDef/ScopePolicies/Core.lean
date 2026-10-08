import Mettapedia.GSLT.LanguageDef.TemplateScope.IdentitySlotRenaming
import Mettapedia.GSLT.LanguageDef.ScopePolicies.ReadAlong

/-!
# The core of the scope policies, as a theory

The core of `TemplateScope.Spectrum`: scope-bearing terms whose store names
are slots (`Tm S (Slot X)`), a program of such terms, an activation
discipline, and the one evaluator `run`.  This module presents it as a theory
(terms, static equivalence, reduction) and, through `GSLT.termsAlone`, as a
theory presented through its contexts.

## The terms

A term of the theory (`Core`) is a judgment still to run, `run d prog t`: the
discipline `d`, the equations `prog` and a closed query `t`, run from the root
path and the empty store; or an observation, `done bag`: the bag of results
with their final stores, in the evaluator's order.  The bag is the whole
observation: the answers (`act` of each store on its result) with their
multiplicity, the stores, and which names share a cell.

## The reduction

`Evaluates (run d prog t) (done bag)` holds when some fuel gives the bag:
`∃ n, run d prog n [] ∅ t = some bag`.  The reduction of the theory is this
relation, closed under the static equivalence on its right
(`core_rewrites_run_iff`).  It is one step from a judgment to its observation;
an observation has no step (`core_rewrites_done`); a judgment has at most one
reduct up to the static equivalence (`core_rewrites_functional`), because a
defined run does not depend on the fuel (`Evaluates.unique`, from `run_mono`);
a judgment whose run is undefined at every fuel has no step
(`core_no_step_iff`).  The existing relational semantics is this reduction
followed by reading the answers (`answerBag_iff_evaluates`).

## The static equivalence

It is generated (`Relation.EqvGen`) by two kinds of link (`CoreLink`).

* Two observations are linked when both are, result by result, renamings of
  one bag of the identity model (`IdSlot.Renamed`): the relation that
  `IdSlot.transfer` states between the two bags of the slot model.
* Two judgments under the static discipline are linked when one judgment of
  the identity model reads both (`Reads`): each is the slot-model elaboration,
  under rule M or under lexical fresh, of an admissible program whose
  identity-model elaboration is that judgment.  This is renaming of slots in
  the sense of `IdSlot.renaming_M` and `IdSlot.renaming_LF`, which are the
  reason the reduction respects it (`CoreLink.evaluates`).

Renaming of an arbitrary judgment is not part of it: that would need the
evaluator to commute with renaming on every configuration, and the renaming
theorems of `TemplateScope` are about elaborated admissible programs run from
the empty store under the static discipline.  A judgment that is no such
elaboration, and every judgment under the snapshot discipline, is equivalent
to itself only (`coreEquiv_eq_of_unlinked`, `coreEquiv_copyAtCall`).

The static equivalence keeps the number of results (`coreEquiv_done_length`)
and never relates a judgment to an observation (`coreEquiv_kind`).  On results
with a first-order answer it keeps the answer, the store and the sharing of
cells, up to a one-to-one correspondence of names
(`coreEquiv_done_firstOrder`, in `ScopePolicies.Observations`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ScopePolicies

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.IdSlot

universe u v

/-! ## Two facts about a generated equivalence -/

/-- A function that the generating relation preserves is preserved by the
equivalence it generates. -/
theorem eqvGen_invariant {α : Type*} {β : Type*} {relation : α → α → Prop} (measure : α → β)
    (preserved : ∀ first second, relation first second → measure first = measure second)
    {first second : α} (equivalent : Relation.EqvGen relation first second) :
    measure first = measure second := by
  induction equivalent with
  | rel first second related => exact preserved first second related
  | refl first => rfl
  | symm first second _ ih => exact ih.symm
  | trans first middle second _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- An element that the generating relation relates to nothing, on either
side, is equivalent to itself only. -/
theorem eqvGen_eq_of_isolated {α : Type*} {relation : α → α → Prop} (isolated : α → Prop)
    (left : ∀ first second, relation first second → ¬ isolated first)
    (right : ∀ first second, relation first second → ¬ isolated second)
    {first second : α} (equivalent : Relation.EqvGen relation first second) :
    isolated first ∨ isolated second → first = second := by
  induction equivalent with
  | rel first second related =>
      rintro (alone | alone)
      · exact absurd alone (left first second related)
      · exact absurd alone (right first second related)
  | refl first => exact fun _ => rfl
  | symm first second _ ih => exact fun alone => (ih alone.symm).symm
  | trans first middle second _ _ ih₁ ih₂ =>
      rintro (alone | alone)
      · have same := ih₁ (Or.inl alone)
        subst same
        exact ih₂ (Or.inl alone)
      · have same := ih₂ (Or.inr alone)
        subst same
        exact ih₁ (Or.inr alone)

/-! ## Authored programs -/

/-- An authored program: equations by name, and a query. -/
structure Program (S : Type u) (X : Type v) where
  clauses : S → Option (Src S X)
  query : Src S X

variable {S : Type u} {X : Type v}

/-- An admissible program: every equation and the query are admissible text
(`Src.Admissible`). -/
def Program.Admissible [DecidableEq X] (program : Program S X) : Prop :=
  (∀ F body, program.clauses F = some body → body.Admissible) ∧ program.query.Admissible

/-! ## The terms of the core -/

/-- **A term of the core**: a judgment still to run, from the root path and
the empty store, or an observation. -/
inductive Core (S : Type u) (X : Type v) where
  | run (d : Disc) (prog : S → Option (Tm S (Slot X))) (t : Tm S (Slot X))
  | done (bag : Result S (Slot X))

/-- The number of results of an observation. -/
def Core.bagLength : Core S X → Option ℕ
  | .run _ _ _ => none
  | .done bag => some bag.length

/-- The discipline of a judgment. -/
def Core.discipline : Core S X → Option Disc
  | .run d _ _ => some d
  | .done _ => none

/-! ## Identity-model readings -/

/-- The two ownership policies that have an identity-model elaboration. -/
inductive Reading where
  | mercury
  | lexicalFresh
  deriving DecidableEq, Repr

/-- The configuration of a reading: per-call lifetime, reference readout. -/
def Reading.config : Reading → Config
  | .mercury => cfgM
  | .lexicalFresh => cfgLF

variable [DecidableEq X]

/-- The identity-model equations of a program. -/
def Reading.idProg (reading : Reading) (u : X) (unit : S) (cl : S → Option (Src S X)) :
    S → Option (Tm S (BId X)) :=
  match reading with
  | .mercury => progM u unit cl
  | .lexicalFresh => progLF u unit cl

/-- The identity-model elaboration of a query. -/
def Reading.idQuery (reading : Reading) (t : Src S X) : Tm S (BId X) :=
  match reading with
  | .mercury => elabMFormAt [] t
  | .lexicalFresh => elabLFFormAt [] t

/-- **A judgment of the identity model reads a judgment of the slot model**:
they are the two elaborations, under rule M or under lexical fresh, of one
admissible program. -/
def Reads (prog₁ : S → Option (Tm S (Slot X))) (t₁ : Tm S (Slot X))
    (prog₂ : S → Option (Tm S (BId X))) (t₂ : Tm S (BId X)) : Prop :=
  ∃ (u : X) (unit : S) (reading : Reading) (program : Program S X), program.Admissible ∧
    prog₁ = progSlot reading.config u unit program.clauses ∧
    t₁ = elabCfg reading.config [] program.query ∧
    prog₂ = reading.idProg u unit program.clauses ∧ t₂ = reading.idQuery program.query

/-- The elaborations of an admissible program are read by its identity-model
elaboration. -/
theorem reads_of_admissible (u : X) (unit : S) (reading : Reading) {program : Program S X}
    (admissible : program.Admissible) :
    Reads (progSlot reading.config u unit program.clauses)
      (elabCfg reading.config [] program.query)
      (reading.idProg u unit program.clauses) (reading.idQuery program.query) :=
  ⟨u, unit, reading, program, admissible, rfl, rfl, rfl, rfl⟩

/-! ## The links of the static equivalence -/

/-- **The links that generate the static equivalence.** -/
inductive CoreLink : Core S X → Core S X → Prop
  /-- Two judgments under the static discipline that one judgment of the
  identity model reads. -/
  | run {prog₁ prog₁' : S → Option (Tm S (Slot X))} {t₁ t₁' : Tm S (Slot X)}
      {prog₂ : S → Option (Tm S (BId X))} {t₂ : Tm S (BId X)} :
      Reads prog₁ t₁ prog₂ t₂ → Reads prog₁' t₁' prog₂ t₂ →
        CoreLink (.run .static prog₁ t₁) (.run .static prog₁' t₁')
  /-- Two observations that are, result by result, renamings of one bag of the
  identity model. -/
  | done {bag bag' : Result S (Slot X)} {bag₂ : Result S (BId X)} :
      List.Forall₂ Renamed bag bag₂ → List.Forall₂ Renamed bag' bag₂ →
        CoreLink (.done bag) (.done bag')

theorem CoreLink.symm {first second : Core S X} (link : CoreLink first second) :
    CoreLink second first := by
  cases link with
  | run reads reads' => exact .run reads' reads
  | done renamed renamed' => exact .done renamed' renamed

theorem CoreLink.bagLength {first second : Core S X} (link : CoreLink first second) :
    first.bagLength = second.bagLength := by
  cases link with
  | run _ _ => rfl
  | done renamed renamed' =>
      exact congrArg some (renamed.length_eq.trans renamed'.length_eq.symm)

theorem CoreLink.discipline {first second : Core S X} (link : CoreLink first second) :
    first.discipline = second.discipline := by
  cases link <;> rfl

/-- A linked judgment is an elaboration, under rule M or under lexical fresh,
of an admissible program, under the static discipline. -/
theorem CoreLink.run_left {d : Disc} {prog : S → Option (Tm S (Slot X))} {t : Tm S (Slot X)}
    {second : Core S X} (link : CoreLink (.run d prog t) second) :
    d = .static ∧ ∃ (u : X) (unit : S) (reading : Reading) (program : Program S X),
      program.Admissible ∧ prog = progSlot reading.config u unit program.clauses ∧
        t = elabCfg reading.config [] program.query := by
  cases link with
  | run reads _ =>
      obtain ⟨u, unit, reading, program, admissible, same, same', -, -⟩ := reads
      exact ⟨rfl, u, unit, reading, program, admissible, same, same'⟩

/-! ## The static equivalence -/

/-- **The static equivalence of the core.** -/
def CoreEquiv : Core S X → Core S X → Prop := Relation.EqvGen CoreLink

theorem CoreEquiv.refl (term : Core S X) : CoreEquiv term term := Relation.EqvGen.refl term

theorem CoreEquiv.symm {first second : Core S X} (equivalent : CoreEquiv first second) :
    CoreEquiv second first :=
  Relation.EqvGen.symm _ _ equivalent

theorem CoreEquiv.trans {first second third : Core S X} (firstSecond : CoreEquiv first second)
    (secondThird : CoreEquiv second third) : CoreEquiv first third :=
  Relation.EqvGen.trans _ _ _ firstSecond secondThird

theorem CoreEquiv.of_link {first second : Core S X} (link : CoreLink first second) :
    CoreEquiv first second :=
  Relation.EqvGen.rel _ _ link

/-- The static equivalence, as a setoid. -/
def coreSetoid (S : Type u) (X : Type v) [DecidableEq X] : Setoid (Core S X) where
  r := CoreEquiv
  iseqv := ⟨CoreEquiv.refl, CoreEquiv.symm, CoreEquiv.trans⟩

/-- The static equivalence keeps the number of results, and never relates a
judgment to an observation. -/
theorem coreEquiv_bagLength {first second : Core S X} (equivalent : CoreEquiv first second) :
    first.bagLength = second.bagLength :=
  eqvGen_invariant Core.bagLength (fun _ _ link => link.bagLength) equivalent

/-- **The static equivalence keeps the number of results.** -/
theorem coreEquiv_done_length {bag bag' : Result S (Slot X)}
    (equivalent : CoreEquiv (.done bag) (.done bag')) : bag.length = bag'.length :=
  Option.some.inj (coreEquiv_bagLength equivalent)

/-- The static equivalence keeps the discipline of a judgment. -/
theorem coreEquiv_discipline {first second : Core S X} (equivalent : CoreEquiv first second) :
    first.discipline = second.discipline :=
  eqvGen_invariant Core.discipline (fun _ _ link => link.discipline) equivalent

/-- **A judgment is not equivalent to an observation.** -/
theorem coreEquiv_kind {d : Disc} {prog : S → Option (Tm S (Slot X))} {t : Tm S (Slot X)}
    {bag : Result S (Slot X)} : ¬ CoreEquiv (.run d prog t) (.done bag) := by
  intro equivalent
  have same := coreEquiv_discipline equivalent
  cases same

/-- What is equivalent to an observation is an observation. -/
theorem coreEquiv_done_right {first : Core S X} {bag : Result S (Slot X)}
    (equivalent : CoreEquiv first (.done bag)) : ∃ bag', first = .done bag' := by
  cases first with
  | run d prog t => exact absurd equivalent coreEquiv_kind
  | done bag' => exact ⟨bag', rfl⟩

/-- What an observation is equivalent to is an observation. -/
theorem coreEquiv_done_left {second : Core S X} {bag : Result S (Slot X)}
    (equivalent : CoreEquiv (.done bag) second) : ∃ bag', second = .done bag' :=
  coreEquiv_done_right equivalent.symm

/-- **A term with no link is equivalent to itself only.** -/
theorem coreEquiv_eq_of_unlinked {first second : Core S X}
    (unlinked : ∀ other, ¬ CoreLink first other) (equivalent : CoreEquiv first second) :
    first = second :=
  eqvGen_eq_of_isolated (fun term => ∀ other, ¬ CoreLink term other)
    (fun _ second link alone => alone second link)
    (fun first _ link alone => alone first link.symm) equivalent (Or.inl unlinked)

/-- **A judgment under the snapshot discipline is equivalent to itself
only.** -/
theorem coreEquiv_copyAtCall {prog : S → Option (Tm S (Slot X))} {t : Tm S (Slot X)}
    {second : Core S X} (equivalent : CoreEquiv (.run .copyAtCall prog t) second) :
    second = .run .copyAtCall prog t := by
  refine (coreEquiv_eq_of_unlinked (fun other link => ?_) equivalent).symm
  have impossible := link.run_left.1
  cases impossible

/-- Negative, for the static equivalence: two observations with different
numbers of results are apart. -/
theorem done_apart_of_length {bag bag' : Result S (Slot X)} (differ : bag.length ≠ bag'.length) :
    ¬ CoreEquiv (.done bag) (.done bag') :=
  fun equivalent => differ (coreEquiv_done_length equivalent)

/-- Negative: the empty bag and a bag with one result. -/
theorem empty_apart_singleton (result : Tm S (Slot X) × GStore S (Slot X)) :
    ¬ CoreEquiv (.done [] : Core S X) (.done [result]) :=
  done_apart_of_length (by simp)

/-- Negative: the two disciplines on one program and query are apart. -/
theorem disciplines_apart (prog : S → Option (Tm S (Slot X))) (t : Tm S (Slot X)) :
    ¬ CoreEquiv (.run .static prog t) (.run .copyAtCall prog t) := by
  intro equivalent
  have same := coreEquiv_discipline equivalent
  cases same

variable [DecidableEq S]

/-- **A reading runs as what it reads, up to renaming** (`IdSlot.renaming_M`,
`IdSlot.renaming_LF`): the two runs are defined together, and their bags
correspond result by result, each pair related by a renaming. -/
theorem Reads.renaming {prog₁ : S → Option (Tm S (Slot X))} {t₁ : Tm S (Slot X)}
    {prog₂ : S → Option (Tm S (BId X))} {t₂ : Tm S (BId X)} (reads : Reads prog₁ t₁ prog₂ t₂) :
    ((∃ n bag₁, run .static prog₁ n [] Store.empty t₁ = some bag₁) ↔
        ∃ m bag₂, run .static prog₂ m [] Store.empty t₂ = some bag₂) ∧
      ∀ {n m : ℕ} {bag₁ : Result S (Slot X)} {bag₂ : Result S (BId X)},
        run .static prog₁ n [] Store.empty t₁ = some bag₁ →
        run .static prog₂ m [] Store.empty t₂ = some bag₂ →
          List.Forall₂ Renamed bag₁ bag₂ := by
  obtain ⟨u, unit, reading, program, admissible, rfl, rfl, rfl, rfl⟩ := reads
  cases reading
  · exact renaming_M u unit program.clauses program.query admissible.1 admissible.2
  · exact renaming_LF u unit program.clauses program.query admissible.1 admissible.2

/-! ## Evaluation -/

/-- **The evaluation relation of the core**: a judgment evaluates to the bag
that some fuel gives. -/
def Evaluates : Core S X → Core S X → Prop
  | .run d prog t, .done bag => ∃ n, run d prog n [] Store.empty t = some bag
  | _, _ => False

theorem evaluates_run_done {d : Disc} {prog : S → Option (Tm S (Slot X))} {t : Tm S (Slot X)}
    {bag : Result S (Slot X)} :
    Evaluates (.run d prog t) (.done bag) ↔ ∃ n, run d prog n [] Store.empty t = some bag :=
  Iff.rfl

/-- Only a judgment evaluates, and only to an observation. -/
theorem Evaluates.shape {first second : Core S X} (evaluates : Evaluates first second) :
    ∃ d prog t bag, first = .run d prog t ∧ second = .done bag ∧
      ∃ n, run d prog n [] Store.empty t = some bag := by
  cases first with
  | run d prog t =>
      cases second with
      | run _ _ _ => exact evaluates.elim
      | done bag => exact ⟨d, prog, t, bag, rfl, rfl, evaluates⟩
  | done _ => cases second <;> exact evaluates.elim

/-- An observation evaluates to nothing. -/
theorem not_evaluates_done (bag : Result S (Slot X)) (next : Core S X) :
    ¬ Evaluates (.done bag) next := by
  intro evaluates
  obtain ⟨_, _, _, _, impossible, _⟩ := evaluates.shape
  cases impossible

/-- **Evaluation does not depend on the fuel**: a judgment evaluates to at
most one observation. -/
theorem Evaluates.unique {first second second' : Core S X} (evaluates : Evaluates first second)
    (evaluates' : Evaluates first second') : second = second' := by
  obtain ⟨d, prog, t, bag, rfl, rfl, n, defined⟩ := evaluates.shape
  obtain ⟨_, _, _, bag', same, rfl, n', defined'⟩ := evaluates'.shape
  cases same
  have atMax := run_mono d prog (le_max_left n n') defined
  have atMax' := run_mono d prog (le_max_right n n') defined'
  rw [atMax] at atMax'
  cases atMax'
  rfl

/-- **The reduction respects a link**: linked terms evaluate together, to
linked observations. -/
theorem CoreLink.evaluates {first first' next : Core S X} (link : CoreLink first first')
    (evaluates : Evaluates first next) : ∃ next', Evaluates first' next' ∧ CoreLink next next' := by
  cases link with
  | run reads reads' =>
      obtain ⟨_, _, _, bag, same, rfl, n, defined⟩ := evaluates.shape
      cases same
      obtain ⟨m, bag₂, defined₂⟩ := reads.renaming.1.mp ⟨n, bag, defined⟩
      obtain ⟨n', bag', defined'⟩ := reads'.renaming.1.mpr ⟨m, bag₂, defined₂⟩
      exact ⟨.done bag', ⟨n', defined'⟩,
        .done (reads.renaming.2 defined defined₂) (reads'.renaming.2 defined' defined₂)⟩
  | done _ _ => exact absurd evaluates (not_evaluates_done _ _)

/-- **The static equivalence is a bisimulation for evaluation.** -/
theorem coreEquiv_evaluates {first first' : Core S X} (equivalent : CoreEquiv first first') :
    (∀ next, Evaluates first next → ∃ next', Evaluates first' next' ∧ CoreEquiv next next') ∧
      ∀ next', Evaluates first' next' → ∃ next, Evaluates first next ∧ CoreEquiv next next' := by
  induction equivalent with
  | rel first first' link =>
      refine ⟨fun next evaluates => ?_, fun next' evaluates => ?_⟩
      · obtain ⟨next', evaluates', related⟩ := link.evaluates evaluates
        exact ⟨next', evaluates', .of_link related⟩
      · obtain ⟨next, evaluates', related⟩ := link.symm.evaluates evaluates
        exact ⟨next, evaluates', .of_link related.symm⟩
  | refl first =>
      exact ⟨fun next evaluates => ⟨next, evaluates, .refl next⟩,
        fun next evaluates => ⟨next, evaluates, .refl next⟩⟩
  | symm first first' _ ih =>
      refine ⟨fun next evaluates => ?_, fun next' evaluates => ?_⟩
      · obtain ⟨next', evaluates', related⟩ := ih.2 next evaluates
        exact ⟨next', evaluates', related.symm⟩
      · obtain ⟨next, evaluates', related⟩ := ih.1 next' evaluates
        exact ⟨next, evaluates', related.symm⟩
  | trans first middle last _ _ ih₁ ih₂ =>
      refine ⟨fun next evaluates => ?_, fun next' evaluates => ?_⟩
      · obtain ⟨between, evaluates₁, related₁⟩ := ih₁.1 next evaluates
        obtain ⟨next', evaluates₂, related₂⟩ := ih₂.1 between evaluates₁
        exact ⟨next', evaluates₂, related₁.trans related₂⟩
      · obtain ⟨between, evaluates₂, related₂⟩ := ih₂.2 next' evaluates
        obtain ⟨next, evaluates₁, related₁⟩ := ih₁.2 between evaluates₂
        exact ⟨next, evaluates₁, related₁.trans related₂⟩

/-! ## The theory -/

/-- **The core, as a theory**: its terms, its static equivalence, and
evaluation as its reduction. -/
def coreGSLT (S : Type u) (X : Type v) [DecidableEq X] [DecidableEq S] : GSLT.{max u v} where
  Term := Core S X
  equations := coreSetoid S X
  rewrites := fun term next => ∃ observed, Evaluates term observed ∧ CoreEquiv observed next
  rewrites_resp_left := by
    rintro term term' next equivalent ⟨observed, evaluates, related⟩
    obtain ⟨observed', evaluates', related'⟩ := (coreEquiv_evaluates equivalent).1 observed evaluates
    exact ⟨observed', ⟨observed', evaluates', .refl observed'⟩, related.symm.trans related'⟩
  rewrites_resp_right := by
    rintro term next next' ⟨observed, evaluates, related⟩ equivalent
    exact ⟨observed, evaluates, related.trans equivalent⟩

/-- **The core, as a theory presented through its contexts.** -/
def coreTheory (S : Type u) (X : Type v) [DecidableEq X] [DecidableEq S] :
    ContextTheory.{max u v} :=
  (coreGSLT S X).termsAlone

@[simp] theorem coreGSLT_equations (first second : Core S X) :
    (coreGSLT S X).equations.r first second ↔ CoreEquiv first second :=
  Iff.rfl

/-- **The reduction and `run`.**  A judgment steps to a term exactly when
some fuel gives a bag whose observation is equivalent to that term. -/
theorem core_rewrites_run_iff {d : Disc} {prog : S → Option (Tm S (Slot X))}
    {t : Tm S (Slot X)} {next : Core S X} :
    (coreGSLT S X).rewrites (.run d prog t) next ↔
      ∃ n bag, run d prog n [] Store.empty t = some bag ∧ CoreEquiv (.done bag) next := by
  constructor
  · rintro ⟨observed, evaluates, related⟩
    obtain ⟨_, _, _, bag, same, rfl, n, defined⟩ := evaluates.shape
    cases same
    exact ⟨n, bag, defined, related⟩
  · rintro ⟨n, bag, defined, related⟩
    exact ⟨.done bag, ⟨n, defined⟩, related⟩

/-- A defined run is a step to its observation. -/
theorem core_rewrites_of_run {d : Disc} {prog : S → Option (Tm S (Slot X))}
    {t : Tm S (Slot X)} {n : ℕ} {bag : Result S (Slot X)}
    (defined : run d prog n [] Store.empty t = some bag) :
    (coreGSLT S X).rewrites (.run d prog t) (.done bag) :=
  core_rewrites_run_iff.mpr ⟨n, bag, defined, .refl _⟩

/-- **An observation has no step.** -/
theorem core_rewrites_done (bag : Result S (Slot X)) (next : Core S X) :
    ¬ (coreGSLT S X).rewrites (.done bag) next := by
  rintro ⟨observed, evaluates, -⟩
  exact not_evaluates_done bag observed evaluates

/-- **Every reduct is an observation.** -/
theorem core_rewrites_target {term next : Core S X} (step : (coreGSLT S X).rewrites term next) :
    ∃ bag, next = .done bag := by
  obtain ⟨observed, evaluates, related⟩ := step
  obtain ⟨_, _, _, bag, -, rfl, -⟩ := evaluates.shape
  exact coreEquiv_done_left related

/-- **The reduction is functional up to the static equivalence.** -/
theorem core_rewrites_functional {term next next' : Core S X}
    (step : (coreGSLT S X).rewrites term next) (step' : (coreGSLT S X).rewrites term next') :
    CoreEquiv next next' := by
  obtain ⟨observed, evaluates, related⟩ := step
  obtain ⟨observed', evaluates', related'⟩ := step'
  cases evaluates.unique evaluates'
  exact related.symm.trans related'

/-- **A judgment has no step exactly when its run is undefined at every
fuel.** -/
theorem core_no_step_iff {d : Disc} {prog : S → Option (Tm S (Slot X))} {t : Tm S (Slot X)} :
    (∀ next, ¬ (coreGSLT S X).rewrites (.run d prog t) next) ↔
      ∀ n, run d prog n [] Store.empty t = none := by
  constructor
  · intro stuck n
    cases defined : run d prog n [] Store.empty t with
    | none => rfl
    | some bag => exact absurd (core_rewrites_of_run defined) (stuck _)
  · intro undefined next step
    obtain ⟨n, bag, defined, -⟩ := core_rewrites_run_iff.mp step
    rw [undefined n] at defined
    cases defined

/-- **The existing relational semantics is this reduction followed by reading
the answers**: the answer bag is the image of the observation under the
environment action. -/
theorem answerBag_iff_evaluates (d : Disc) (prog : S → Option (Tm S (Slot X)))
    (t : Tm S (Slot X)) (answerBag : List (Tm S (Slot X))) :
    AnswerBag d prog t answerBag ↔
      ∃ bag, Evaluates (.run d prog t) (.done bag) ∧
        answerBag = bag.map fun result => act result.2 result.1 := by
  constructor
  · rintro ⟨n, answered⟩
    unfold answers at answered
    cases defined : run d prog n [] Store.empty t with
    | none =>
        rw [defined] at answered
        cases answered
    | some bag =>
        rw [defined] at answered
        exact ⟨bag, ⟨n, defined⟩, (Option.some.inj answered).symm⟩
  · rintro ⟨bag, ⟨n, defined⟩, rfl⟩
    refine ⟨n, ?_⟩
    unfold answers
    rw [defined]
    rfl

/-! ## Examples -/

/-- Positive: a symbol evaluates to itself, with the empty store. -/
theorem symbol_evaluates (d : Disc) (s : S) :
    Evaluates (.run d (fun _ => none) (.sym s) : Core S X) (.done [(.sym s, Store.empty)]) :=
  ⟨1, rfl⟩

/-- Positive: so it has a step in the theory. -/
theorem symbol_steps (d : Disc) (s : S) :
    (coreGSLT S X).rewrites (.run d (fun _ => none) (.sym s)) (.done [(.sym s, Store.empty)]) :=
  ⟨_, symbol_evaluates d s, .refl _⟩

/-- The program whose one equation `F` is defined as a call of itself. -/
def loopProgram (F : S) : S → Option (Tm S (Slot X)) :=
  fun G => if G = F then some (.fn F) else none

/-- The run of that call is undefined at every fuel, path and store. -/
theorem run_loop (d : Disc) (F : S) :
    ∀ (n : ℕ) (π : Path) (σ : GStore S (Slot X)),
      run d (loopProgram F) n π σ (.fn F) = none
  | 0, _, _ => rfl
  | n + 1, π, σ => by
      show step d (loopProgram F) (run d (loopProgram F) n) π σ (.fn F) = none
      simp only [step, loopProgram, if_true]
      exact run_loop d F n _ _

/-- Negative: a judgment with no step that is not an observation. -/
theorem loop_no_step (d : Disc) (F : S) (next : Core S X) :
    ¬ (coreGSLT S X).rewrites (.run d (loopProgram F) (.fn F)) next :=
  core_no_step_iff.mpr (fun n => run_loop d F n [] Store.empty) next

#print axioms Reads.renaming
#print axioms Evaluates.unique
#print axioms CoreLink.evaluates
#print axioms coreEquiv_evaluates
#print axioms coreGSLT
#print axioms core_rewrites_run_iff
#print axioms core_rewrites_functional
#print axioms core_no_step_iff
#print axioms answerBag_iff_evaluates
#print axioms coreEquiv_done_length
#print axioms coreEquiv_copyAtCall
#print axioms loop_no_step

end Mettapedia.GSLT.LanguageDef.ScopePolicies
