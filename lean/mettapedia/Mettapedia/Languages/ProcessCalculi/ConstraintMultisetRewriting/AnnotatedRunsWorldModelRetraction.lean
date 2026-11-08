import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsWorldModel
import Mettapedia.PLN.WorldModel.LedgerRetraction

/-!
# Retraction along runs: causal deletion as a firing, and the two forgetting laws

## Causal deletion is a firing

`retractFiring withdrawn taken` has the predicate query of the space of withdrawn observations,
which saw `taken`, and takes exactly those occurrences. It is admitted exactly when the
query saw every withdrawn observation present, once each, and the store has a solution
(`retractFiring_valid_iff`). Its cut has nothing withdrawn left in the ledger
(`ledger_retract`): the withdrawn sources are removed from every support at once.

## Claims and their supports

A claim names the observations relevant to it and those that support it (`Claim`). Its support in a
ledger is its relevant part (`support`); its evidence is the evidence of that support
(`claimEvidence`). Nonzero evidence always has a nonempty support (`support_nonempty_of_ne_zero`).

## Both laws hold along runs

* **No manufactured evidence** (`retract_no_manufactured`): an admitted retraction never raises the
  evidence of any claim. The recount is exact (`retract_recount`): the evidence of the support
  that was withdrawn is subtracted.
* **Support closure** (`retract_support_subset`, `retract_support_avoids`): the support afterwards
  is part of the support before, and contains nothing withdrawn.
* **Along a run** that makes no observation, the ledger only shrinks
  (`ledger_follow_subset_of_makes_none`), so no claim gains evidence or support
  (`run_no_manufactured`, `run_support_subset`).

## The forgetting interface

* On bags of identified observations, causal deletion of a finite set of identities is the
  library's retraction layer (`LedgerRetraction.causalRetractionLayer`): both forgetting laws,
  exact unlearning on clean bases, and relevance.  The retraction firing computes it on the ledger
  (`retract_is_causalForget`).
* An exact inverse asked of every base is degenerate: it forces forgetting to be the identity and
  the revision to be zero
  (`GenericWorldModelForgetting.ForgettingLayer.exactInverse_everywhere_degenerate`), so with sound
  supports a single observation would be zero (`LedgerRetraction.no_sound_allBases_exactInverse`).
  The library interface asks the inverse only of clean bases.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

namespace WorldModelRuns

open MeTTaCalculus.OccurrenceCommits (regionOf PredicateQuery mem_regionOf mem_fire)
open Mettapedia.PLN.WorldModel.EvidenceSpaces
open Mettapedia.PLN.WorldModel.EvidenceContracts
open Mettapedia.PLN.WorldModel.LedgerRetraction (causalForget)

universe uT uS uO uW
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] {W : Type uW}

/-! ## Causal deletion as a firing -/

section Retraction

variable (A : SubstitutionAction T S) (label : O → T) (space : T → Bool)

/-- **The retraction firing**: the predicate query of the space of withdrawn observations saw
`taken`, and the firing takes exactly those occurrences. -/
def retractFiring (withdrawn : T → Bool) (taken : List O) : Firing T S O :=
  ⟨⟨taken.map label, [], [], [], []⟩,
    [PredicateQueryAdmission.Query.fixed ⟨withdrawn, taken.toFinset⟩], ⟨taken, [], []⟩⟩

omit [DecidableEq O] in
theorem equations_self {e : Equation T} :
    ∀ {l : List O}, e ∈ Selection.equations label (l.map label) l → e.1 = e.2
  | [], member => by simp [Selection.equations] at member
  | o :: rest, member => by
      simp only [Selection.equations, List.map_cons, List.zipWith_cons_cons,
        List.mem_cons] at member
      rcases member with rfl | member
      · rfl
      · exact equations_self member

/-- **Admission of retraction**: the query saw every withdrawn observation present, the take lists
each once, and the store has a solution. -/
theorem retractFiring_valid_iff (withdrawn : T → Bool) (taken : List O) (C : Configuration T O) :
    (retractFiring (S := S) label withdrawn taken).Valid A label C ↔
      regionOf label C.present withdrawn = taken.toFinset ∧ taken.Nodup ∧
        A.Consistent C.equations := by
  change PredicateQueryAdmission.Valid A label _
    ([(⟨withdrawn, taken.toFinset⟩ : PredicateQuery O T)].map PredicateQueryAdmission.Query.fixed) C _ ↔ _
  rw [PredicateQueryAdmission.valid_fixed_iff]
  constructor
  · rintro ⟨firing, holds⟩
    refine ⟨holds _ (List.mem_singleton_self _), firing.take_distinct, ?_⟩
    obtain ⟨σ, solved⟩ := firing.consistent
    exact ⟨σ, fun e member => solved e (by simp [Selection.problem, retractFiring, member])⟩
  · rintro ⟨seen, distinct, consistent⟩
    have inside : taken.toFinset ⊆ C.present := by
      rw [← seen]
      exact Finset.filter_subset _ _
    refine ⟨⟨distinct, by simp [retractFiring], by simp [retractFiring], rfl,
      by simp [retractFiring], ?_, ?_, by simp [retractFiring]⟩, ?_⟩
    · exact ⟨by simpa [Selection.commit, retractFiring] using inside,
        by simp [Selection.commit, retractFiring], by simp [Selection.commit, retractFiring],
        by simp [Selection.commit, retractFiring], by simp [Selection.commit, retractFiring]⟩
    · obtain ⟨σ, solved⟩ := consistent
      refine ⟨σ, fun e member => ?_⟩
      simp only [Selection.problem, retractFiring, List.append_assoc, List.mem_append] at member
      rcases member with old | takes | rest
      · exact solved e old
      · have same := equations_self label takes
        change A.E (A.apply σ e.1) (A.apply σ e.2)
        rw [same]
        exact A.equivalence.refl _
      · simp [Selection.equations] at rest
    · intro query member
      rw [List.mem_singleton.mp member]
      exact seen

/-- **The withdrawn observations leave the ledger**, and only they. -/
theorem ledger_retract {withdrawn : T → Bool} {taken : List O} {C : Configuration T O}
    (valid : (retractFiring (S := S) label withdrawn taken).Valid A label C) :
    ledger label space ((retractFiring (S := S) label withdrawn taken).result label C) =
      (ledger label space C).filter fun o => withdrawn (label o) = false := by
  have seen := ((retractFiring_valid_iff A label withdrawn taken C).mp valid).1
  rw [ledger_result]
  have noMade :
      madeObservations label space (retractFiring (S := S) label withdrawn taken) = ∅ := by
    simp [madeObservations, retractFiring]
  rw [noMade, Finset.union_empty]
  ext o
  simp only [Finset.mem_sdiff, Finset.mem_filter, retractFiring]
  rw [← seen]
  simp only [mem_regionOf, mem_ledger]
  constructor
  · rintro ⟨⟨present, inSpace⟩, notWithdrawn⟩
    refine ⟨⟨present, inSpace⟩, ?_⟩
    cases value : withdrawn (label o)
    · rfl
    · exact absurd ⟨present, value⟩ notWithdrawn
  · rintro ⟨⟨present, inSpace⟩, notWithdrawn⟩
    refine ⟨⟨present, inSpace⟩, fun ⟨_, isWithdrawn⟩ => ?_⟩
    rw [isWithdrawn] at notWithdrawn
    cases notWithdrawn

end Retraction

/-! ## Claims and supports -/

section Claims

variable (label : O → T) (outcome : T → W)

/-- **A claim**: which observations are relevant to it, and which of those support it. -/
structure Claim (W : Type uW) where
  relevant : W → Bool
  holds : W → Bool

/-- The support of a claim in a ledger: its relevant observations. -/
def support (q : Claim W) (L : Finset O) : Finset O :=
  L.filter fun o => q.relevant (recorded label outcome o) = true

/-- The evidence of a claim in a ledger: the evidence of its support. -/
def claimEvidence (q : Claim W) (L : Finset O) : Evidence ℕ :=
  ledgerEvidence (recorded label outcome) q.holds (support label outcome q L)

omit [DecidableEq O] in
theorem support_mono (q : Claim W) {L L' : Finset O} (sub : L ⊆ L') :
    support label outcome q L ⊆ support label outcome q L' :=
  Finset.filter_subset_filter _ sub

theorem claimEvidence_mono (q : Claim W) {L L' : Finset O} (sub : L ⊆ L') :
    claimEvidence label outcome q L ≤ claimEvidence label outcome q L' :=
  ledgerEvidence_mono _ q.holds (support_mono label outcome q sub)

omit [DecidableEq O] in
/-- **Nonzero evidence has a nonempty support.** -/
theorem support_nonempty_of_ne_zero (q : Claim W) {L : Finset O}
    (nonzero : claimEvidence label outcome q L ≠ 0) : (support label outcome q L).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro empty
  apply nonzero
  unfold claimEvidence
  rw [empty]
  exact (ledgerEvidence_eq_zero_iff _ q.holds ∅).mpr rfl

end Claims

/-! ## Both laws hold for retraction -/

section Laws

variable (A : SubstitutionAction T S) (label : O → T) (space : T → Bool) (outcome : T → W)
variable {withdrawn : T → Bool} {taken : List O} {C : Configuration T O}

/-- **No manufactured evidence**: retraction never raises the evidence of a claim. -/
theorem retract_no_manufactured
    (valid : (retractFiring (S := S) label withdrawn taken).Valid A label C)
    (q : Claim W) :
    claimEvidence label outcome q
        (ledger label space ((retractFiring (S := S) label withdrawn taken).result label C)) ≤
      claimEvidence label outcome q (ledger label space C) := by
  rw [ledger_retract A label space valid]
  exact claimEvidence_mono label outcome q (Finset.filter_subset _ _)

/-- **Support closure, first part**: the support afterwards is part of the support before. -/
theorem retract_support_subset
    (valid : (retractFiring (S := S) label withdrawn taken).Valid A label C)
    (q : Claim W) :
    support label outcome q
        (ledger label space ((retractFiring (S := S) label withdrawn taken).result label C)) ⊆
      support label outcome q (ledger label space C) := by
  rw [ledger_retract A label space valid]
  exact support_mono label outcome q (Finset.filter_subset _ _)

/-- **Support closure, second part**: nothing withdrawn remains in any support. -/
theorem retract_support_avoids
    (valid : (retractFiring (S := S) label withdrawn taken).Valid A label C)
    (q : Claim W) :
    ∀ o ∈ support label outcome q
        (ledger label space ((retractFiring (S := S) label withdrawn taken).result label C)),
      withdrawn (label o) = false := by
  intro o member
  rw [ledger_retract A label space valid] at member
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp member).1).2

/-- **The recount is exact**: the evidence of the withdrawn part of the support is subtracted. -/
theorem retract_recount
    (valid : (retractFiring (S := S) label withdrawn taken).Valid A label C)
    (q : Claim W) :
    claimEvidence label outcome q
        (ledger label space ((retractFiring (S := S) label withdrawn taken).result label C)) =
      claimEvidence label outcome q (ledger label space C) -
        ledgerEvidence (recorded label outcome) q.holds
          ((support label outcome q (ledger label space C)).filter
            fun o => withdrawn (label o) = true) := by
  rw [ledger_retract A label space valid]
  have split : support label outcome q
      ((ledger label space C).filter fun o => withdrawn (label o) = false) =
      support label outcome q (ledger label space C) \
        (support label outcome q (ledger label space C)).filter
          fun o => withdrawn (label o) = true := by
    ext o
    simp only [support, Finset.mem_filter, Finset.mem_sdiff]
    cases withdrawn (label o) <;> simp
  unfold claimEvidence
  rw [split, ledgerEvidence_sdiff, Finset.inter_eq_right.mpr (Finset.filter_subset _ _)]

/-- **Along a run that makes no observation, the ledger only shrinks.** -/
theorem ledger_follow_subset_of_makes_none :
    ∀ {C : Configuration T O} {w : List (Firing T S O)},
      (∀ f ∈ w, madeObservations label space f = ∅) →
        ledger label space (follow label C w) ⊆ ledger label space C
  | C, [], _ => subset_rfl
  | C, f :: rest, noMade => by
      have later := ledger_follow_subset_of_makes_none (C := f.result label C) (w := rest)
        (fun g member => noMade g (List.mem_cons_of_mem f member))
      refine later.trans ?_
      rw [ledger_result, noMade f List.mem_cons_self, Finset.union_empty]
      exact Finset.sdiff_subset

/-- **No manufactured evidence along a run that makes no observation.** -/
theorem run_no_manufactured {C : Configuration T O} {w : List (Firing T S O)}
    (none : ∀ f ∈ w, madeObservations label space f = ∅) (q : Claim W) :
    claimEvidence label outcome q (ledger label space (follow label C w)) ≤
      claimEvidence label outcome q (ledger label space C) :=
  claimEvidence_mono label outcome q (ledger_follow_subset_of_makes_none label space none)

/-- **Support closure along a run that makes no observation.** -/
theorem run_support_subset {C : Configuration T O} {w : List (Firing T S O)}
    (none : ∀ f ∈ w, madeObservations label space f = ∅) (q : Claim W) :
    support label outcome q (ledger label space (follow label C w)) ⊆
      support label outcome q (ledger label space C) :=
  support_mono label outcome q (ledger_follow_subset_of_makes_none label space none)

end Laws

/-! ## The retraction firing computes causal deletion -/

section Interface

variable (A : SubstitutionAction T S) (label : O → T) (space : T → Bool)

/-- **The retraction firing computes causal deletion on the ledger.** -/
theorem retract_is_causalForget {withdrawn : T → Bool} {taken : List O} {C : Configuration T O}
    (valid : (retractFiring (S := S) label withdrawn taken).Valid A label C) :
    (ledger label space ((retractFiring (S := S) label withdrawn taken).result label C)).val =
      causalForget taken.toFinset (ledger label space C).val := by
  have seen := ((retractFiring_valid_iff A label withdrawn taken C).mp valid).1
  rw [ledger_retract A label space valid, Finset.filter_val]
  unfold causalForget
  apply Multiset.filter_congr
  intro o member
  rw [← seen, mem_regionOf]
  have present := ((mem_ledger label space).mp member).1
  cases withdrawn (label o) <;> simp [present]

end Interface

end WorldModelRuns

open WorldModelRuns

#print axioms retractFiring_valid_iff
#print axioms ledger_retract
#print axioms support_nonempty_of_ne_zero
#print axioms retract_no_manufactured
#print axioms retract_support_subset
#print axioms retract_support_avoids
#print axioms retract_recount
#print axioms ledger_follow_subset_of_makes_none
#print axioms run_no_manufactured
#print axioms run_support_subset
#print axioms retract_is_causalForget

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
