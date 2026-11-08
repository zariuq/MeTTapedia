import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunUnfolding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualAttemptOutcomes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunEvidence

/-!
# Candidate firings from the sources, with explicit incompleteness

`AnnotatedRunUnfolding` filters a declared catalogue of firings. This module derives that
catalogue from the sources: a finite catalogue of freshened rule instances with their predicate
queries, the occurrences a scan of the space returns, and a supply of fresh identities for the
outputs (`candidates`). Every choice of scanned occurrences for the takes and reads of every entry
is a candidate (`mem_candidates`), and every admitted firing of an entry, with the supplied fresh
identities, is among them once the scan covers the present occurrences
(`mem_candidates_of_valid`).

A budgeted classifier then decides admission candidate by candidate. A completed answer must be
correct (`Calibrated`); an unfinished one is `none` and claims nothing. A generation records the
admitted candidates, the pending ones, and a status: complete when nothing is pending, incomplete
when the budget ran out on some candidate (`generate`).

* **Complete generation is exact** (`complete_exact`, `complete_exact_catalogue`): its admitted
  firings are exactly the admitted firings of the catalogue entries with the supplied identities.
* **Incomplete generation never reports "no admitted firing"** (`incomplete_never_none`), and it
  names a pending candidate (`incomplete_has_pending`).
* **`none` certifies terminality** (`none_iff_terminal`), so it is never reported while an
  admitted candidate exists (`not_none_of_valid`, `not_none_of_valid_source`).
* **More budget** (`admitted_mono`, `complete_mono`, `none_mono`): with a classifier that never
  loses a completed verdict, admitted candidates stay admitted, a complete generation stays
  complete, and "no admitted firing" stays the verdict.
* **The same rule as the source attempts** (`Verdict.rule`): "none" exactly when the search is
  complete and found nothing. `ContextualAttemptOutcomes` decides its non-firing outcomes by this
  rule (`attempt_none_iff`, `attempt_incomplete_iff`, `unfinished_status_cannot_report_none`).
* **Attempt records** (`Generation.attemptRecord`, `attemptRecord_none_iff`): a generation that
  admits nothing is a non-firing attempt of `AnnotatedRunEvidence`, with its pending candidates as
  answer table and its classification charge; it records `none` exactly when it is complete.

The controls encode the defect found in a rho-weighted stochastic simulator: classification
errors dropped, then a zero total read as absorption. With a known enabled firing and an exhausted
budget it reports absorption; the generator here reports incomplete
(`AnnotatedRunCandidatesControls`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunCandidates

open AnnotatedRuns
open AnnotatedRunUnfolding (enabled mem_enabled known pending ClassifierSound Terminal)

/-! ## Words over the scanned occurrences -/

section Tuples

variable {α : Type*}

/-- Every word of length `k` over a list. -/
def tuples : ℕ → List α → List (List α)
  | 0, _ => [[]]
  | k + 1, l => l.flatMap fun a => (tuples k l).map (a :: ·)

theorem mem_tuples (l : List α) : ∀ (k : ℕ) (s : List α),
    s ∈ tuples k l ↔ s.length = k ∧ ∀ a ∈ s, a ∈ l
  | 0, s => by
      cases s with
      | nil => simp [tuples]
      | cons a s => simp [tuples]
  | k + 1, s => by
      rw [tuples, List.mem_flatMap]
      constructor
      · rintro ⟨b, hb, inMap⟩
        obtain ⟨s', hs', rfl⟩ := List.mem_map.mp inMap
        obtain ⟨length, all⟩ := (mem_tuples l k s').mp hs'
        refine ⟨by simp [length], ?_⟩
        intro a member
        rcases List.mem_cons.mp member with rfl | inRest
        · exact hb
        · exact all a inRest
      · rintro ⟨length, all⟩
        cases s with
        | nil => simp at length
        | cons a s =>
            refine ⟨a, all a List.mem_cons_self, List.mem_map.mpr ⟨s, (mem_tuples l k s).mpr
              ⟨by simpa using length, fun b hb => all b (List.mem_cons_of_mem _ hb)⟩, rfl⟩⟩

end Tuples

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-! ## Candidates from the sources -/

/-- A catalogue entry: a freshened rule instance with its predicate queries. -/
abbrev Entry (T : Type uT) (S : Type uS) (O : Type uO) :=
  RuleInstance T × List (PredicateQueryAdmission.Query T S O)

/-- The entry of a firing. -/
def entryOf (f : Firing T S O) : Entry T S O := (f.rule, f.queries)

/-- **The candidates, derived from the sources**: every catalogue entry, with every choice of
scanned occurrences for its takes and its reads, and the supplied fresh identities for its
outputs. -/
def candidates (catalogue : List (Entry T S O)) (contents : List O)
    (supply : Entry T S O → List O) : List (Firing T S O) :=
  catalogue.flatMap fun entry =>
    (tuples entry.1.take.length contents).flatMap fun taken =>
      (tuples entry.1.read.length contents).map fun read =>
        ⟨entry.1, entry.2, ⟨taken, read, supply entry⟩⟩

omit [DecidableEq O] in
theorem mem_candidates {catalogue : List (Entry T S O)} {contents : List O}
    {supply : Entry T S O → List O} {f : Firing T S O} :
    f ∈ candidates catalogue contents supply ↔
      entryOf f ∈ catalogue ∧ f.selection.taken.length = f.rule.take.length ∧
        (∀ o ∈ f.selection.taken, o ∈ contents) ∧ f.selection.read.length = f.rule.read.length ∧
        (∀ o ∈ f.selection.read, o ∈ contents) ∧ f.selection.made = supply (entryOf f) := by
  obtain ⟨rule, queries, ⟨taken, read, made⟩⟩ := f
  simp only [candidates, List.mem_flatMap, List.mem_map, entryOf, mem_tuples]
  constructor
  · rintro ⟨⟨rule', queries'⟩, entry, taken', ⟨takenLength, takenScanned⟩, read',
      ⟨readLength, readScanned⟩, same⟩
    cases same
    exact ⟨entry, takenLength, takenScanned, readLength, readScanned, rfl⟩
  · rintro ⟨entry, takenLength, takenScanned, readLength, readScanned, rfl⟩
    exact ⟨(rule, queries), entry, taken, ⟨takenLength, takenScanned⟩, read,
      ⟨readLength, readScanned⟩, rfl⟩

section Sources

variable (A : SubstitutionAction T S) (label : O → T)

/-- **Source completeness**: once the scan covers the present occurrences, every admitted
firing of a catalogue entry, with the supplied fresh identities, is a candidate. -/
theorem mem_candidates_of_valid {catalogue : List (Entry T S O)} {contents : List O}
    {supply : Entry T S O → List O} {C : Configuration T O} (covers : ∀ o ∈ C.present, o ∈ contents)
    {f : Firing T S O} (entry : entryOf f ∈ catalogue) (made : f.selection.made = supply (entryOf f))
    (valid : f.Valid A label C) : f ∈ candidates catalogue contents supply :=
  mem_candidates.mpr ⟨entry, valid.firing.take_length.symm,
    fun o member => covers o (valid.firing.occurrences.taken_subset
      (by simpa [Selection.commit] using member)),
    valid.firing.read_length.symm,
    fun o member => covers o (valid.firing.occurrences.kept_subset
      (by simpa [Selection.commit] using member)),
    made⟩

end Sources

/-! ## Budgeted classification and generation -/

/-- A budgeted classifier: `some b` is a completed verdict, `none` means the budget ran out. -/
abbrev Classifier (T : Type uT) (S : Type uS) (O : Type uO) := ℕ → Firing T S O → Option Bool

/-- **Calibration**: at every budget, a completed verdict on a candidate is correct. Nothing is
claimed of an unfinished one. -/
def Calibrated (A : SubstitutionAction T S) (label : O → T) (C : Configuration T O)
    (cands : List (Firing T S O)) (classify : Classifier T S O) : Prop :=
  ∀ budget, ClassifierSound A label cands C (classify budget)

inductive Status where
  | complete
  | incomplete
deriving DecidableEq

/-- Complete exactly when nothing is pending. -/
def statusOf {F : Type*} : List F → Status
  | [] => .complete
  | _ :: _ => .incomplete

/-- What a generation reports: the candidates classified admitted, those still pending, and
whether the classification finished. -/
structure Generation (F : Type*) where
  status : Status
  admitted : List F
  pending : List F

/-- **The generator.** -/
def generate (catalogue : List (Entry T S O)) (contents : List O) (supply : Entry T S O → List O)
    (classify : Classifier T S O) (budget : ℕ) : Generation (Firing T S O) where
  status := statusOf (pending (candidates catalogue contents supply) (classify budget))
  admitted := known (candidates catalogue contents supply) (classify budget)
  pending := pending (candidates catalogue contents supply) (classify budget)

inductive Verdict where
  | admitted
  | none
  | incomplete
deriving DecidableEq

/-- **The decision rule**, from a completeness status and whether an answer was found: `none`
needs a complete search. -/
def Verdict.rule : Status → Bool → Verdict
  | _, true => .admitted
  | .complete, false => .none
  | .incomplete, false => .incomplete

theorem Verdict.rule_none_iff (status : Status) (found : Bool) :
    Verdict.rule status found = .none ↔ status = .complete ∧ found = false := by
  cases status <;> cases found <;> simp [Verdict.rule]

/-- The verdict of a generation. -/
def Generation.verdict {F : Type*} (g : Generation F) : Verdict :=
  Verdict.rule g.status (!g.admitted.isEmpty)

section Generation

variable (A : SubstitutionAction T S) (label : O → T)
variable {catalogue : List (Entry T S O)} {contents : List O} {supply : Entry T S O → List O}
  {classify : Classifier T S O} {budget : ℕ}

omit [DecidableEq O] in
theorem status_complete_iff :
    (generate catalogue contents supply classify budget).status = .complete ↔
      pending (candidates catalogue contents supply) (classify budget) = [] := by
  change statusOf _ = _ ↔ _
  cases pending (candidates catalogue contents supply) (classify budget) <;> simp [statusOf]

omit [DecidableEq O] in
/-- An incomplete generation names a candidate on which the budget ran out. -/
theorem incomplete_has_pending
    (incomplete : (generate catalogue contents supply classify budget).status = .incomplete) :
    ∃ f ∈ candidates catalogue contents supply, classify budget f = none := by
  have notComplete : pending (candidates catalogue contents supply) (classify budget) ≠ [] := by
    intro empty
    rw [← status_complete_iff] at empty
    rw [empty] at incomplete
    cases incomplete
  obtain ⟨f, member⟩ := List.exists_mem_of_ne_nil _ notComplete
  simp only [pending, List.mem_filter, decide_eq_true_eq] at member
  exact ⟨f, member⟩

/-- Every admitted candidate is admitted, at any budget. -/
theorem admitted_valid {C : Configuration T O}
    (calibrated : Calibrated A label C (candidates catalogue contents supply) classify)
    {f : Firing T S O} (member : f ∈ (generate catalogue contents supply classify budget).admitted) :
    f.Valid A label C := by
  simp only [generate, known, List.mem_filter, decide_eq_true_eq] at member
  exact (calibrated budget f member.1 true member.2).mpr rfl

/-- **Complete generation is exact**: its admitted firings are exactly the admitted
candidates. -/
theorem complete_exact {C : Configuration T O}
    (calibrated : Calibrated A label C (candidates catalogue contents supply) classify)
    (complete : (generate catalogue contents supply classify budget).status = .complete)
    (f : Firing T S O) :
    f ∈ (generate catalogue contents supply classify budget).admitted ↔
      f ∈ candidates catalogue contents supply ∧ f.Valid A label C := by
  have closed := (status_complete_iff (catalogue := catalogue) (contents := contents)
    (supply := supply) (classify := classify) (budget := budget)).mp complete
  change f ∈ known _ _ ↔ _
  rw [AnnotatedRunUnfolding.closed_classifier_exact A label _ C _ (calibrated budget) closed,
    mem_enabled]

/-- **Complete generation is exact relative to the catalogue**: with a scan that covers the
present occurrences, its admitted firings are exactly the admitted firings of the catalogue
entries with the supplied fresh identities. -/
theorem complete_exact_catalogue {C : Configuration T O}
    (covers : ∀ o ∈ C.present, o ∈ contents)
    (calibrated : Calibrated A label C (candidates catalogue contents supply) classify)
    (complete : (generate catalogue contents supply classify budget).status = .complete)
    (f : Firing T S O) :
    f ∈ (generate catalogue contents supply classify budget).admitted ↔
      entryOf f ∈ catalogue ∧ f.selection.made = supply (entryOf f) ∧ f.Valid A label C := by
  rw [complete_exact A label calibrated complete]
  constructor
  · rintro ⟨member, valid⟩
    obtain ⟨entry, -, -, -, -, made⟩ := mem_candidates.mp member
    exact ⟨entry, made, valid⟩
  · rintro ⟨entry, made, valid⟩
    exact ⟨mem_candidates_of_valid A label covers entry made valid, valid⟩

omit [DecidableEq O] in
/-- **Incomplete generation never reports "no admitted firing".** -/
theorem incomplete_never_none
    (incomplete : (generate catalogue contents supply classify budget).status = .incomplete) :
    (generate catalogue contents supply classify budget).verdict ≠ .none := by
  intro none
  have := (Verdict.rule_none_iff _ _).mp none
  rw [incomplete] at this
  cases this.1

/-- **`none` certifies terminality.** A generation reports "no admitted firing" exactly when it
is complete and no candidate is admitted. -/
theorem none_iff_terminal {C : Configuration T O}
    (calibrated : Calibrated A label C (candidates catalogue contents supply) classify) :
    (generate catalogue contents supply classify budget).verdict = .none ↔
      (generate catalogue contents supply classify budget).status = .complete ∧
        Terminal A label (candidates catalogue contents supply) C := by
  unfold Generation.verdict
  rw [Verdict.rule_none_iff]
  constructor
  · rintro ⟨complete, empty⟩
    refine ⟨complete, fun f member valid => ?_⟩
    have admitted := (complete_exact A label calibrated complete f).mpr ⟨member, valid⟩
    rw [Bool.not_eq_false', List.isEmpty_iff] at empty
    rw [empty] at admitted
    cases admitted
  · rintro ⟨complete, terminal⟩
    refine ⟨complete, ?_⟩
    rw [Bool.not_eq_false', List.isEmpty_iff, List.eq_nil_iff_forall_not_mem]
    intro f admitted
    obtain ⟨member, valid⟩ := (complete_exact A label calibrated complete f).mp admitted
    exact terminal f member valid

/-- **No "no admitted firing" while a candidate is admitted.** -/
theorem not_none_of_valid {C : Configuration T O}
    (calibrated : Calibrated A label C (candidates catalogue contents supply) classify)
    {f : Firing T S O} (member : f ∈ candidates catalogue contents supply) (valid : f.Valid A label C) :
    (generate catalogue contents supply classify budget).verdict ≠ .none := fun none =>
  ((none_iff_terminal A label calibrated).mp none).2 f member valid

/-- **The source form**: no "no admitted firing" while some catalogue entry is admitted with the
supplied fresh identities. -/
theorem not_none_of_valid_source {C : Configuration T O} (covers : ∀ o ∈ C.present, o ∈ contents)
    (calibrated : Calibrated A label C (candidates catalogue contents supply) classify)
    {f : Firing T S O} (entry : entryOf f ∈ catalogue) (made : f.selection.made = supply (entryOf f))
    (valid : f.Valid A label C) :
    (generate catalogue contents supply classify budget).verdict ≠ .none :=
  not_none_of_valid A label calibrated (mem_candidates_of_valid A label covers entry made valid) valid

end Generation

/-! ## More budget -/

/-- More budget never loses or changes a completed verdict. -/
def MonotoneBudget (classify : Classifier T S O) : Prop :=
  ∀ budget budget' f answer, budget ≤ budget' → classify budget f = some answer →
    classify budget' f = some answer

section Budget

variable {catalogue : List (Entry T S O)} {contents : List O} {supply : Entry T S O → List O}
  {classify : Classifier T S O} {budget budget' : ℕ}

omit [DecidableEq O] in
/-- An admitted candidate stays admitted with more budget. -/
theorem admitted_mono (mono : MonotoneBudget classify) (le : budget ≤ budget') {f : Firing T S O}
    (member : f ∈ (generate catalogue contents supply classify budget).admitted) :
    f ∈ (generate catalogue contents supply classify budget').admitted := by
  simp only [generate, known, List.mem_filter, decide_eq_true_eq] at member ⊢
  exact ⟨member.1, mono budget budget' f true le member.2⟩

omit [DecidableEq O] in
/-- A complete generation stays complete with more budget. -/
theorem complete_mono (mono : MonotoneBudget classify) (le : budget ≤ budget')
    (complete : (generate catalogue contents supply classify budget).status = .complete) :
    (generate catalogue contents supply classify budget').status = .complete := by
  rw [status_complete_iff] at complete ⊢
  rw [List.eq_nil_iff_forall_not_mem] at complete ⊢
  intro f member
  simp only [pending, List.mem_filter, decide_eq_true_eq] at member
  have earlier := complete f
  simp only [pending, List.mem_filter, decide_eq_true_eq, not_and] at earlier
  obtain ⟨answer, answered⟩ := Option.ne_none_iff_exists'.mp (earlier member.1)
  rw [mono budget budget' f answer le answered] at member
  cases member.2

omit [DecidableEq O] in
/-- **"No admitted firing" stays the verdict with more budget**: it was a completed claim. -/
theorem none_mono (mono : MonotoneBudget classify) (le : budget ≤ budget')
    (none : (generate catalogue contents supply classify budget).verdict = .none) :
    (generate catalogue contents supply classify budget').verdict = .none := by
  unfold Generation.verdict at none ⊢
  rw [Verdict.rule_none_iff] at none ⊢
  obtain ⟨complete, empty⟩ := none
  refine ⟨complete_mono mono le complete, ?_⟩
  rw [Bool.not_eq_false', List.isEmpty_iff] at empty ⊢
  rw [List.eq_nil_iff_forall_not_mem]
  intro f member
  have closed := (status_complete_iff.mp complete)
  rw [List.eq_nil_iff_forall_not_mem] at closed
  simp only [generate, known, List.mem_filter, decide_eq_true_eq] at member
  have earlier := closed f
  simp only [pending, List.mem_filter, decide_eq_true_eq, not_and] at earlier
  obtain ⟨answer, answered⟩ := Option.ne_none_iff_exists'.mp (earlier member.1)
  have same := mono budget budget' f answer le answered
  rw [member.2] at same
  obtain rfl := Option.some.inj same
  have admitted : f ∈ (generate catalogue contents supply classify budget).admitted := by
    simp only [generate, known, List.mem_filter, decide_eq_true_eq]
    exact ⟨member.1, answered⟩
  rw [empty] at admitted
  cases admitted

end Budget

/-! ## The same rule as the source attempts -/

section AttemptOutcomes

open Mettapedia.OSLF.Binding
open ContextualAttemptOutcomes (Search Attempt)

variable {Sig : Signature} {Query Local Shared Occ : Type} {queries : Query → MetaArity Sig}
  {locals : Local → MetaArity Sig} {captures : Shared → MetaArity Sig} {Γ : Ctx Sig} {sort : Sig.Srt}
  [DecidableEq Query] [DecidableEq Local] [DecidableEq Shared] [DecidableEq Occ]
  [DecidableEq Sig.Srt] [∀ result, DecidableEq (Sig.Op result)]
  {Term' EffectSubst EffectO : Type} [DecidableEq EffectO]

/-- The completeness status of a source search. -/
def Status.ofSearch (search : Search queries locals captures (O := Occ) (Γ := Γ) (sort := sort)) :
    Status :=
  if search.complete = true then .complete else .incomplete

theorem Status.ofSearch_complete_iff
    (search : Search queries locals captures (O := Occ) (Γ := Γ) (sort := sort)) :
    Status.ofSearch search = .complete ↔ search.complete = true := by
  unfold Status.ofSearch
  split <;> simp_all

/-- **A source attempt reports `none` exactly when the decision rule does**, applied to the
completeness of its search and to whether its answer table is nonempty. -/
theorem attempt_none_iff
    (search : Search queries locals captures (O := Occ) (Γ := Γ) (sort := sort))
    (action : SubstitutionAction Term' EffectSubst) (label : EffectO → Term')
    (code : List (StagedSourceEffects.Instruction Term' EffectSubst EffectO))
    (before : Configuration Term' EffectO) :
    (∃ after, Attempt search .one action label code before .none after) ↔
      Verdict.rule (Status.ofSearch search) (decide search.entries.Nonempty) = .none := by
  rw [Verdict.rule_none_iff, Status.ofSearch_complete_iff, decide_eq_false_iff_not,
    Finset.not_nonempty_iff_eq_empty]
  constructor
  · rintro ⟨after, attempt⟩
    cases attempt with
    | none _ complete empty => exact ⟨complete, empty⟩
  · rintro ⟨complete, empty⟩
    exact ⟨before, .none rfl complete empty⟩

/-- A source attempt can end incomplete exactly when its search is incomplete. -/
theorem attempt_incomplete_iff
    (search : Search queries locals captures (O := Occ) (Γ := Γ) (sort := sort))
    (mode : ContextualAttemptOutcomes.Mode) (action : SubstitutionAction Term' EffectSubst)
    (label : EffectO → Term') (code : List (StagedSourceEffects.Instruction Term' EffectSubst EffectO))
    (before : Configuration Term' EffectO) :
    (∃ after, Attempt search mode action label code before .incomplete after) ↔
      Status.ofSearch search = .incomplete := by
  have incompleteIff : Status.ofSearch search = .incomplete ↔ search.complete = false := by
    unfold Status.ofSearch
    split <;> simp_all
  rw [incompleteIff]
  constructor
  · rintro ⟨after, attempt⟩
    cases attempt with
    | incomplete unfinished => exact unfinished
  · intro unfinished
    exact ⟨before, .incomplete unfinished⟩

/-- `ContextualAttemptOutcomes.Attempt.unfinished_cannot_report_none`, read through the status. -/
theorem unfinished_status_cannot_report_none
    (search : Search queries locals captures (O := Occ) (Γ := Γ) (sort := sort))
    {mode : ContextualAttemptOutcomes.Mode} {action : SubstitutionAction Term' EffectSubst}
    {label : EffectO → Term'} {code : List (StagedSourceEffects.Instruction Term' EffectSubst EffectO)}
    {before after : Configuration Term' EffectO}
    (incomplete : Status.ofSearch search = .incomplete) :
    ¬ Attempt search mode action label code before .none after := by
  have unfinished : search.complete = false := by
    unfold Status.ofSearch at incomplete
    split at incomplete
    · cases incomplete
    · simpa using (by assumption : ¬ search.complete = true)
  exact ContextualAttemptOutcomes.Attempt.unfinished_cannot_report_none unfinished

end AttemptOutcomes

/-! ## Verdicts as attempt records of the evidence layer -/

/-- The attempt outcome of a verdict. -/
def Verdict.outcome : Verdict → ContextualAttemptOutcomes.Outcome
  | .admitted => .fired
  | .none => .none
  | .incomplete => .incomplete

theorem Verdict.outcome_ne_fired {verdict : Verdict} (nothing : verdict ≠ .admitted) :
    verdict.outcome ≠ .fired := by
  cases verdict with
  | admitted => exact absurd rfl nothing
  | none => decide
  | incomplete => decide

/-- **A generation that admits nothing is a non-firing attempt** of `AnnotatedRunEvidence`: its
outcome is `none` or `incomplete`, its answer table the pending candidates, with the task, world,
round and physical charge of the classification. -/
def Generation.attemptRecord {F Task World Round : Type*} (g : Generation F)
    (nothing : g.verdict ≠ .admitted) (task : Task) (world : World) (round : Round) (charge : ℕ) :
    AnnotatedRunEvidence.AttemptRecord (List F) Task World Round where
  outcome := g.verdict.outcome
  nonfiring := Verdict.outcome_ne_fired nothing
  answers := g.pending
  task := task
  world := world
  round := round
  charge := charge

/-- **The record reports `none` exactly for a complete generation.** -/
theorem attemptRecord_none_iff {F Task World Round : Type*} (g : Generation F)
    (nothing : g.verdict ≠ .admitted) (task : Task) (world : World) (round : Round) (charge : ℕ) :
    (g.attemptRecord nothing task world round charge).outcome = .none ↔ g.status = .complete := by
  change g.verdict.outcome = .none ↔ g.status = .complete
  unfold Generation.verdict at nothing ⊢
  cases hs : g.status <;> cases hb : g.admitted.isEmpty <;> simp_all [Verdict.rule, Verdict.outcome]

#print axioms Verdict.outcome_ne_fired
#print axioms attemptRecord_none_iff
#print axioms mem_tuples
#print axioms mem_candidates
#print axioms mem_candidates_of_valid
#print axioms status_complete_iff
#print axioms incomplete_has_pending
#print axioms admitted_valid
#print axioms complete_exact
#print axioms complete_exact_catalogue
#print axioms incomplete_never_none
#print axioms none_iff_terminal
#print axioms not_none_of_valid
#print axioms not_none_of_valid_source
#print axioms admitted_mono
#print axioms complete_mono
#print axioms none_mono
#print axioms attempt_none_iff
#print axioms attempt_incomplete_iff
#print axioms unfinished_status_cannot_report_none

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunCandidates
