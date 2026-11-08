import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.GuardFragments
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SuperpositionSaturation

/-!
# Lowering a guard on the step: a specification licenses a checkable guard

A firing over labelled occurrences (`Superposition.clauseFiring`) takes, reads and makes
occurrences and has one guard. Its admission is base admission and the guard
(`Template.admits_iff`); its result does not depend on the guard (`Template.result_eq`).

## The proof–run interface (`runs_spec_iff_lowered`)

A **specification** guards each template; a **lowered guard** guards each template together with a
certificate. Suppose an invariant of configurations is kept by every base-admitted template, and
where it holds and base admission holds, the specification holds exactly when some certificate
passes the lowered guard. Then **the runs with the specification are exactly the runs with the
lowered guard, certificates erased**. The schema has two instances here.

* **Checked certificates** (`certified_runs`): a template reads a datum and is guarded by the Pi
  specification `Always succ p` of it; the lowered guard checks a finite certificate
  (`GuardFragments.checkInvariant`). The invariant is that every datum in the store is
  finite-state (`FiniteData`), kept when the program makes only finite-state data. The check needs
  no trust in whoever made the certificate.
* **Budgets** (`budgeted_runs`): the lowered guard is the closure verdict at a budget
  (`GuardFragments.verdictAlways`) reading commit. A suspended verdict leaves the firing pending.

## Controls on the step

All at the store holding one datum occurrence, with a template that reads it.

* **The closure-free lowering is wrong on a separating store** (`closure_free_admits_wrongly`): the
  fragment check admits the template, the specification refuses it, and so does the certificate
  guard for every certificate.
* **Agreement on a cyclic datum** (`cycle_agrees`): the specification, the certificate `{0, 1, 2}`
  and the verdict at budget `2` each admits the firing.
* **An infinite-state datum needs an offline proof** (`infinite_state_needs_offline_proof`): the
  specification admits, no certificate and no budget does, and the symbolic invariant proved in
  `GuardFragments.Controls.parity_exact` admits by one test.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardLowering

open Superposition (GuardedFiring guarded syntactic clauseFiring clauseFiring_admits_iff
  clauseFiring_present Plain)
open GuardFragments

universe uT uO uR uI uC

variable {T : Type uT} {O : Type uO} [DecidableEq O]

/-- What a firing over labelled occurrences takes, reads and makes. -/
structure Template (O : Type uO) (T : Type uT) where
  takes : List (O × T)
  reads : List (O × T)
  makes : List (O × T)

namespace Template

/-- The template with a guard: a firing of the guarded step. -/
def withGuard (t : Template O T) (guard : Prop) : GuardedFiring T Unit O :=
  clauseFiring t.takes t.reads t.makes guard

/-- The firing a template performs, whatever its guard. -/
def firing (t : Template O T) : AnnotatedRuns.Firing T Unit O := (t.withGuard False).firing

omit [DecidableEq O] in
/-- The guard does not enter the firing. -/
theorem withGuard_firing (t : Template O T) (guard : Prop) : (t.withGuard guard).firing = t.firing :=
  rfl

variable (label : O → T)

/-- **Base admission**: everything admission asks of a template except its guard. -/
def Base (C : Configuration T O) (t : Template O T) : Prop :=
  (t.takes.map Prod.fst).Nodup ∧ (t.makes.map Prod.fst).Nodup ∧
    (∀ p ∈ t.takes ++ t.reads, p.1 ∈ C.present ∧ label p.1 = p.2) ∧
    (∀ p ∈ t.takes, ∀ q ∈ t.reads, p.1 ≠ q.1) ∧
    (∀ p ∈ t.makes, p.1 ∉ C.present ∧ label p.1 = p.2) ∧ Plain C

/-- **Admission is base admission and the guard.** -/
theorem admits_iff (C : Configuration T O) (t : Template O T) (guard : Prop) :
    (guarded (syntactic T) label).Admits (s := C) (t.withGuard guard) ↔ t.Base label C ∧ guard := by
  rw [withGuard, clauseFiring_admits_iff label C t.takes t.reads t.makes guard]
  simp only [Base, and_assoc]

/-- The configuration after the template fires. -/
def after (C : Configuration T O) (t : Template O T) : Configuration T O := t.firing.result label C

/-- **The result does not depend on the guard.** -/
theorem result_eq {C : Configuration T O} {t : Template O T} {guard : Prop}
    (admitted : (guarded (syntactic T) label).Admits (s := C) (t.withGuard guard)) :
    (guarded (syntactic T) label).result (t.withGuard guard) admitted = t.after label C :=
  rfl

theorem present_after (C : Configuration T O) (t : Template O T) :
    (t.after label C).present = (C.present \ (t.takes.map Prod.fst).toFinset) ∪ (t.makes.map Prod.fst).toFinset :=
  clauseFiring_present label C t.takes t.reads t.makes False

end Template

/-! ## Runs of guarded templates -/

section Runs

variable (label : O → T) {ι : Type uI} (template : ι → Template O T) (guard : ι → Prop)

/-- **Runs of guarded templates**: each template is admitted, with its guard, at the configuration
it fires from. -/
inductive Runs : Configuration T O → List ι → Prop
  | nil (C : Configuration T O) : Runs C []
  | cons {C : Configuration T O} {i : ι} {rest : List ι}
      (admitted : (guarded (syntactic T) label).Admits (s := C) ((template i).withGuard (guard i)))
      (later : Runs ((template i).after label C) rest) : Runs C (i :: rest)

theorem runs_cons_iff {C : Configuration T O} {i : ι} {rest : List ι} :
    Runs label template guard C (i :: rest) ↔
      (template i).Base label C ∧ guard i ∧ Runs label template guard ((template i).after label C) rest := by
  constructor
  · rintro (_ | ⟨admitted, later⟩)
    obtain ⟨base, holds⟩ := (Template.admits_iff label C (template i) (guard i)).mp admitted
    exact ⟨base, holds, later⟩
  · rintro ⟨base, holds, later⟩
    exact .cons ((Template.admits_iff label C (template i) (guard i)).mpr ⟨base, holds⟩) later

end Runs

/-! ## The proof–run interface -/

section Interface

variable (label : O → T) {ι : Type uI} {Cert : Type uC} (template : ι → Template O T)

/-- **The proof–run interface.** If an invariant of configurations is kept by every base-admitted
template, and where it holds the specification of a base-admitted template holds exactly when some
certificate passes the lowered guard, then the runs with the specification are exactly the runs
with the lowered guard, certificates erased. -/
theorem runs_spec_iff_lowered (spec : ι → Prop) (low : ι → Cert → Prop)
    (Inv : Configuration T O → Prop)
    (preserved : ∀ C i, Inv C → (template i).Base label C → Inv ((template i).after label C))
    (agree : ∀ C i, Inv C → (template i).Base label C → (spec i ↔ ∃ c, low i c)) :
    ∀ (w : List ι) {C : Configuration T O}, Inv C →
      (Runs label template spec C w ↔
        ∃ v : List (ι × Cert), v.map Prod.fst = w ∧
          Runs label (fun ic => template ic.1) (fun ic => low ic.1 ic.2) C v)
  | [], C, _ => by
      constructor
      · exact fun _ => ⟨[], rfl, .nil C⟩
      · exact fun _ => .nil C
  | i :: rest, C, inv => by
      constructor
      · intro runs
        obtain ⟨base, holds, later⟩ := (runs_cons_iff label template spec).mp runs
        obtain ⟨c, passes⟩ := (agree C i inv base).mp holds
        obtain ⟨v, erased, lowered⟩ :=
          (runs_spec_iff_lowered spec low Inv preserved agree rest (preserved C i inv base)).mp later
        exact ⟨(i, c) :: v, by rw [List.map_cons, erased], (runs_cons_iff label _ _).mpr ⟨base, passes, lowered⟩⟩
      · rintro ⟨v, erased, lowered⟩
        cases v with
        | nil => cases erased
        | cons ic v =>
            obtain ⟨j, c⟩ := ic
            simp only [List.map_cons, List.cons.injEq] at erased
            obtain ⟨rfl, erasedRest⟩ := erased
            obtain ⟨base, passes, later⟩ := (runs_cons_iff label _ _).mp lowered
            have holds := (agree C j inv base).mpr ⟨c, passes⟩
            exact (runs_cons_iff label template spec).mpr ⟨base, holds,
              (runs_spec_iff_lowered spec low Inv preserved agree rest (preserved C j inv base)).mpr
                ⟨v, erasedRest, later⟩⟩

end Interface

/-! ## Instances: certificates and budgets for a Pi guard -/

section Certificates

variable (label : O → T) {R : Type uR} [DecidableEq R] (succ : R → Finset R) (p : R → Bool)
  (embed : R → T)

/-- A template guarded on a datum it reads. -/
structure ReadsDatum where
  template : Template O T
  datum : R
  site : O
  reads : (site, embed datum) ∈ template.reads

/-- **Every datum in the store is finite-state.** -/
def FiniteData (C : Configuration T O) : Prop :=
  ∀ o ∈ C.present, ∀ e, label o = embed e → FiniteState succ e

variable {label succ embed}

omit [DecidableEq R] in
/-- **The invariant is kept** by a template that makes only finite-state data. -/
theorem finiteData_after {C : Configuration T O} {t : Template O T}
    (made : ∀ q ∈ t.makes, ∀ e, q.2 = embed e → FiniteState succ e) (inv : FiniteData label succ embed C)
    (base : t.Base label C) : FiniteData label succ embed (t.after label C) := by
  intro o member e labelled
  rw [Template.present_after] at member
  rcases Finset.mem_union.mp member with old | new
  · exact inv o (Finset.mem_sdiff.mp old).1 e labelled
  · obtain ⟨q, inMakes, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp new)
    exact made q inMakes e ((base.2.2.2.2.1 q inMakes).2.symm.trans labelled)

omit [DecidableEq O] [DecidableEq R] in
/-- At a base-admitted template the datum it reads is finite-state. -/
theorem finiteState_datum {C : Configuration T O} (g : ReadsDatum (O := O) embed)
    (inv : FiniteData label succ embed C) (base : g.template.Base label C) : FiniteState succ g.datum :=
  inv g.site (base.2.2.1 _ (List.mem_append_right _ g.reads)).1 g.datum
    (base.2.2.1 _ (List.mem_append_right _ g.reads)).2

/-- **Checked certificates.** On stores of finite-state data, for a program that makes only
finite-state data, the runs guarded by the Pi specification are exactly the runs guarded by a
certificate check, certificates erased. -/
theorem certified_runs
    (made : ∀ g : ReadsDatum (O := O) embed, ∀ q ∈ g.template.makes, ∀ e, q.2 = embed e → FiniteState succ e)
    (w : List (ReadsDatum (O := O) embed)) {C : Configuration T O} (start : FiniteData label succ embed C) :
    Runs label ReadsDatum.template (fun g => Always succ (fun e => p e = true) g.datum) C w ↔
      ∃ v : List (ReadsDatum (O := O) embed × Finset R), v.map Prod.fst = w ∧
        Runs label (fun gc => gc.1.template) (fun gc => checkInvariant succ p gc.1.datum gc.2 = true) C v :=
  runs_spec_iff_lowered label ReadsDatum.template _ (fun g I => checkInvariant succ p g.datum I = true)
    (FiniteData label succ embed) (fun _ g inv base => finiteData_after (made g) inv base)
    (fun _ g inv base => always_iff_exists_checkInvariant (finiteState_datum g inv base)) w start

/-- **Budgets.** The same runs are exactly the runs guarded by the closure verdict reading commit at
some budget, budgets erased. -/
theorem budgeted_runs
    (made : ∀ g : ReadsDatum (O := O) embed, ∀ q ∈ g.template.makes, ∀ e, q.2 = embed e → FiniteState succ e)
    (w : List (ReadsDatum (O := O) embed)) {C : Configuration T O} (start : FiniteData label succ embed C) :
    Runs label ReadsDatum.template (fun g => Always succ (fun e => p e = true) g.datum) C w ↔
      ∃ v : List (ReadsDatum (O := O) embed × ℕ), v.map Prod.fst = w ∧
        Runs label (fun gn => gn.1.template) (fun gn => verdictAlways succ p gn.1.datum gn.2 = .commit) C v :=
  runs_spec_iff_lowered label ReadsDatum.template _ (fun g n => verdictAlways succ p g.datum n = .commit)
    (FiniteData label succ embed) (fun _ g inv base => finiteData_after (made g) inv base)
    (fun _ g inv base => always_iff_exists_commit (finiteState_datum g inv base)) w start

/-- **A checked certificate is sound at every store**, finite-state or not: a firing it admits is
admitted by the specification. -/
theorem admitted_of_certificate {C : Configuration T O} {t : Template O T} {d : R} {I : Finset R}
    (admitted : (guarded (syntactic T) label).Admits (s := C) (t.withGuard (checkInvariant succ p d I = true))) :
    (guarded (syntactic T) label).Admits (s := C) (t.withGuard (Always succ (fun e => p e = true) d)) := by
  obtain ⟨base, checks⟩ := (Template.admits_iff label C t _).mp admitted
  exact (Template.admits_iff label C t _).mpr ⟨base, (checkInvariant_eq_true_iff.mp checks).always⟩

end Certificates

/-! ## Controls on the step -/

namespace Controls

open GuardFragments.Controls

/-- Every occurrence carries the datum `0`. -/
def probeLabel : ℕ → ℕ := fun _ => 0

/-- One occurrence, identity `0`. -/
def probeStart : Configuration ℕ ℕ := ⟨[], {0}⟩

/-- Read the datum occurrence. -/
def probe : Template ℕ ℕ := ⟨[], [(0, 0)], []⟩

theorem probe_base : probe.Base probeLabel probeStart := by
  unfold Template.Base
  refine ⟨List.nodup_nil, List.nodup_nil, ?_, fun _ member => by simp [probe] at member,
    fun _ member => by simp [probe] at member, ?_⟩
  · intro q member
    simp only [probe, List.nil_append, List.mem_singleton] at member
    subst member
    exact ⟨by decide, rfl⟩
  · intro e member
    simp [probeStart] at member

theorem probe_admits_iff (guard : Prop) :
    (guarded (syntactic ℕ) probeLabel).Admits (s := probeStart) (probe.withGuard guard) ↔ guard :=
  ⟨fun admitted => ((Template.admits_iff probeLabel probeStart probe guard).mp admitted).2,
    fun holds => (Template.admits_iff probeLabel probeStart probe guard).mpr ⟨probe_base, holds⟩⟩

/-- **The closure-free lowering is wrong on a separating store**: it admits the read of the datum
`0`, which steps to the bad state `1`; the specification refuses, and so does the certificate guard
for every certificate. -/
theorem closure_free_admits_wrongly :
    (guarded (syntactic ℕ) probeLabel).Admits (s := probeStart)
        (probe.withGuard (checkFragment zeroOnly 0 {0} = true)) ∧
      ¬ (guarded (syntactic ℕ) probeLabel).Admits (s := probeStart)
        (probe.withGuard (Always escape (fun e => zeroOnly e = true) 0)) ∧
      ∀ I, ¬ (guarded (syntactic ℕ) probeLabel).Admits (s := probeStart)
        (probe.withGuard (checkInvariant escape zeroOnly 0 I = true)) :=
  ⟨(probe_admits_iff _).mpr closure_free_unsound.1,
    fun admitted => closure_free_unsound.2.1 ((probe_admits_iff _).mp admitted),
    fun _ admitted => closure_free_unsound.2.1
      ((probe_admits_iff _).mp (admitted_of_certificate zeroOnly admitted))⟩

/-- Three states in a cycle. -/
def cycle : ℕ → Finset ℕ := fun n => {(n + 1) % 3}

/-- Below three. -/
def belowThree : ℕ → Bool := fun n => decide (n < 3)

/-- **Agreement on a cyclic datum**: the specification, the certificate `{0, 1, 2}` and the verdict
at budget `2` each admits the read of `0`. -/
theorem cycle_agrees :
    (guarded (syntactic ℕ) probeLabel).Admits (s := probeStart)
        (probe.withGuard (Always cycle (fun e => belowThree e = true) 0)) ∧
      (guarded (syntactic ℕ) probeLabel).Admits (s := probeStart)
        (probe.withGuard (checkInvariant cycle belowThree 0 {0, 1, 2} = true)) ∧
      (guarded (syntactic ℕ) probeLabel).Admits (s := probeStart)
        (probe.withGuard (verdictAlways cycle belowThree 0 2 = .commit)) := by
  have checks : checkInvariant cycle belowThree 0 {0, 1, 2} = true := by decide
  exact ⟨(probe_admits_iff _).mpr (checkInvariant_eq_true_iff.mp checks).always,
    (probe_admits_iff _).mpr checks, (probe_admits_iff _).mpr (by decide)⟩

/-- Even. -/
def even : ℕ → Bool := fun n => n % 2 == 0

theorem twoStep_always_even : Always twoStep (fun e => even e = true) 0 :=
  fun e reach => by simpa [even] using (parity_exact 0).mpr rfl e reach

/-- **An infinite-state datum needs an offline proof**: the specification admits the read of `0`
under `n ↦ n + 2`; no certificate and no budget admits it; the symbolic invariant admits it by one
test. -/
theorem infinite_state_needs_offline_proof :
    (guarded (syntactic ℕ) probeLabel).Admits (s := probeStart)
        (probe.withGuard (Always twoStep (fun e => even e = true) 0)) ∧
      (∀ I, ¬ (guarded (syntactic ℕ) probeLabel).Admits (s := probeStart)
        (probe.withGuard (checkInvariant twoStep even 0 I = true))) ∧
      (∀ n, ¬ (guarded (syntactic ℕ) probeLabel).Admits (s := probeStart)
        (probe.withGuard (verdictAlways twoStep even 0 n = .commit))) ∧
      (guarded (syntactic ℕ) probeLabel).Admits (s := probeStart) (probe.withGuard ((0 : ℕ) % 2 = 0)) := by
  refine ⟨(probe_admits_iff _).mpr twoStep_always_even, fun I admitted => ?_, fun n admitted => ?_,
    (probe_admits_iff _).mpr rfl⟩
  · exact twoStep_infinite (checkInvariant_eq_true_iff.mp ((probe_admits_iff _).mp admitted)).finiteState
  · have suspended := parity_suspended n
    rw [show (fun e => e % 2 == 0) = even from rfl] at suspended
    rw [(probe_admits_iff _).mp admitted] at suspended
    exact absurd suspended (by decide)

end Controls

#print axioms Template.admits_iff
#print axioms Template.result_eq
#print axioms runs_cons_iff
#print axioms runs_spec_iff_lowered
#print axioms finiteData_after
#print axioms certified_runs
#print axioms budgeted_runs
#print axioms admitted_of_certificate
#print axioms Controls.closure_free_admits_wrongly
#print axioms Controls.cycle_agrees
#print axioms Controls.infinite_state_needs_offline_proof

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardLowering
