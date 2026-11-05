import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunCandidates

/-!
# The unfolding driven by the sources

`AnnotatedRunUnfolding.frontier` extends every firing of a fixed catalogue. Here every cut
generates its own candidates from the sources (`Sources.candidatesAt`: the rule catalogue, the
scan of the cut and the fresh identities it supplies), classifies them within a budget, and
extends the admitted ones (`sourceFrontier`). The frontier carries a status: complete only when
every generation on the way was complete.

* **Soundness** (`sourceFrontier_sound`): every history the frontier holds is a run of the
  candidate step whose firings were candidates where they fired.
* **Exactness when complete** (`sourceFrontier_exact`): a complete frontier holds exactly the runs
  of its depth whose firings were candidates where they fired. With scans that cover the present
  occurrences, these are exactly the runs of catalogue entries with the supplied identities
  (`sourceRun_iff`).
* **Incompleteness is located** (`sourceFrontier_incomplete`): an incomplete frontier names a
  reached cut whose generation ran out of budget.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunCandidates

open AnnotatedRuns

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-- The sources of candidates at every cut. -/
structure Sources (T : Type uT) (S : Type uS) (O : Type uO) where
  catalogue : List (Entry T S O)
  scan : Configuration T O → List O
  supply : Configuration T O → Entry T S O → List O

/-- The candidates at a cut. -/
def Sources.candidatesAt (src : Sources T S O) (cut : Configuration T O) : List (Firing T S O) :=
  candidates src.catalogue (src.scan cut) (src.supply cut)

/-- The generation at a cut. -/
def Sources.generateAt (src : Sources T S O) (classify : Configuration T O → Classifier T S O)
    (budget : ℕ) (cut : Configuration T O) : Generation (Firing T S O) :=
  generate src.catalogue (src.scan cut) (src.supply cut) (classify cut) budget

/-- Complete when both are. -/
def Status.both : Status → Status → Status
  | .complete, .complete => .complete
  | _, _ => .incomplete

theorem Status.both_eq_complete {first second : Status} :
    Status.both first second = .complete ↔ first = .complete ∧ second = .complete := by
  cases first <;> cases second <;> simp [Status.both]

section Frontier

variable (A : SubstitutionAction T S) (label : O → T)

/-- A run whose firings were candidates where they fired. -/
inductive SourceRun (src : Sources T S O) : Configuration T O → List (Firing T S O) → Prop
  | nil (cut : Configuration T O) : SourceRun src cut []
  | cons {cut : Configuration T O} {f : Firing T S O} {rest : List (Firing T S O)} :
      f ∈ src.candidatesAt cut → SourceRun src (f.result label cut) rest → SourceRun src cut (f :: rest)

/-- A run whose firings come from catalogue entries, with the identities supplied where they
fired. -/
inductive EntryRun (src : Sources T S O) : Configuration T O → List (Firing T S O) → Prop
  | nil (cut : Configuration T O) : EntryRun src cut []
  | cons {cut : Configuration T O} {f : Firing T S O} {rest : List (Firing T S O)} :
      entryOf f ∈ src.catalogue → f.selection.made = src.supply cut (entryOf f) →
        EntryRun src (f.result label cut) rest → EntryRun src cut (f :: rest)

/-- The status of a list of children, on top of the generation's own. -/
def childStatus (own : Status) (children : List (List (List (Firing T S O)) × Status)) : Status :=
  children.foldr (fun child status => Status.both child.2 status) own

omit [DecidableEq O] in
theorem childStatus_eq_complete (own : Status) :
    ∀ children : List (List (List (Firing T S O)) × Status),
      childStatus own children = .complete ↔ own = .complete ∧ ∀ child ∈ children, child.2 = .complete
  | [] => by simp [childStatus]
  | child :: rest => by
      rw [show childStatus own (child :: rest) = Status.both child.2 (childStatus own rest) from rfl,
        Status.both_eq_complete, childStatus_eq_complete own rest]
      simp only [List.mem_cons, forall_eq_or_imp]
      tauto

open Classical in
/-- **The frontier driven by the sources**, with its status. -/
noncomputable def sourceFrontier (src : Sources T S O) (classify : Configuration T O → Classifier T S O)
    (budget : ℕ) : ℕ → Configuration T O → List (List (Firing T S O)) × Status
  | 0, cut => (if A.Consistent cut.equations then [[]] else [], .complete)
  | depth + 1, cut =>
      let children := (src.generateAt classify budget cut).admitted.map fun f =>
        (((sourceFrontier src classify budget depth (f.result label cut)).1.map (f :: ·)),
          (sourceFrontier src classify budget depth (f.result label cut)).2)
      (children.flatMap Prod.fst, childStatus (src.generateAt classify budget cut).status children)

variable {src : Sources T S O} {classify : Configuration T O → Classifier T S O} {budget : ℕ}

/-- Calibration at every cut. -/
def CalibratedEverywhere (src : Sources T S O) (classify : Configuration T O → Classifier T S O) :
    Prop :=
  ∀ cut, Calibrated A label cut (src.candidatesAt cut) (classify cut)

theorem mem_sourceFrontier_succ {depth : ℕ} {cut : Configuration T O} {word : List (Firing T S O)} :
    word ∈ (sourceFrontier A label src classify budget (depth + 1) cut).1 ↔
      ∃ f ∈ (src.generateAt classify budget cut).admitted, ∃ rest,
        rest ∈ (sourceFrontier A label src classify budget depth (f.result label cut)).1 ∧
          word = f :: rest := by
  simp only [sourceFrontier, List.mem_flatMap]
  constructor
  · rintro ⟨child, inChildren, inChild⟩
    obtain ⟨f, admitted, rfl⟩ := List.mem_map.mp inChildren
    obtain ⟨rest, inRest, rfl⟩ := List.mem_map.mp inChild
    exact ⟨f, admitted, rest, inRest, rfl⟩
  · rintro ⟨f, admitted, rest, inRest, rfl⟩
    exact ⟨_, List.mem_map.mpr ⟨f, admitted, rfl⟩, List.mem_map.mpr ⟨rest, inRest, rfl⟩⟩

theorem sourceFrontier_succ_status {depth : ℕ} {cut : Configuration T O} :
    (sourceFrontier A label src classify budget (depth + 1) cut).2 = .complete ↔
      (src.generateAt classify budget cut).status = .complete ∧
        ∀ f ∈ (src.generateAt classify budget cut).admitted,
          (sourceFrontier A label src classify budget depth (f.result label cut)).2 = .complete := by
  rw [show (sourceFrontier A label src classify budget (depth + 1) cut).2 =
      childStatus (src.generateAt classify budget cut).status
        ((src.generateAt classify budget cut).admitted.map fun f =>
          (((sourceFrontier A label src classify budget depth (f.result label cut)).1.map (f :: ·)),
            (sourceFrontier A label src classify budget depth (f.result label cut)).2)) from rfl,
    childStatus_eq_complete]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

/-- **Soundness**: every history of the frontier is a run whose firings were candidates where
they fired. -/
theorem sourceFrontier_sound (calibrated : CalibratedEverywhere A label src classify) :
    ∀ (depth : ℕ) (cut : Configuration T O) (word : List (Firing T S O)),
      word ∈ (sourceFrontier A label src classify budget depth cut).1 →
        word.length = depth ∧ Executable A label cut word ∧ SourceRun label src cut word
  | 0, cut, word, member => by
      classical
      simp only [sourceFrontier] at member
      split at member
      · next consistent =>
          rw [List.mem_singleton] at member
          subst member
          exact ⟨rfl, consistent, .nil cut⟩
      · cases member
  | depth + 1, cut, word, member => by
      obtain ⟨f, admitted, rest, inRest, rfl⟩ := (mem_sourceFrontier_succ A label).mp member
      have valid := admitted_valid A label (calibrated cut) admitted
      have candidate : f ∈ src.candidatesAt cut := by
        simp only [Sources.generateAt, generate, AnnotatedRunUnfolding.known, List.mem_filter] at admitted
        exact admitted.1
      obtain ⟨length, run, source⟩ := sourceFrontier_sound calibrated depth (f.result label cut) rest inRest
      exact ⟨congrArg Nat.succ length, ⟨valid, run⟩, .cons candidate source⟩

/-- **Exactness when complete**: a complete frontier holds exactly the runs of its depth whose
firings were candidates where they fired. -/
theorem sourceFrontier_exact (calibrated : CalibratedEverywhere A label src classify) :
    ∀ (depth : ℕ) (cut : Configuration T O),
      (sourceFrontier A label src classify budget depth cut).2 = .complete →
        ∀ word, word ∈ (sourceFrontier A label src classify budget depth cut).1 ↔
          word.length = depth ∧ Executable A label cut word ∧ SourceRun label src cut word
  | 0, cut, _, word => by
      classical
      constructor
      · exact sourceFrontier_sound A label calibrated 0 cut word
      · rintro ⟨length, run, _⟩
        rw [List.length_eq_zero_iff] at length
        subst length
        simp only [sourceFrontier]
        rw [if_pos (show A.Consistent cut.equations from run)]
        exact List.mem_singleton_self _
  | depth + 1, cut, complete, word => by
      constructor
      · exact sourceFrontier_sound A label calibrated (depth + 1) cut word
      · rintro ⟨length, run, source⟩
        obtain ⟨generated, children⟩ := (sourceFrontier_succ_status A label).mp complete
        cases source with
        | nil => simp at length
        | @cons _ f restWord candidate rest =>
            have admitted : f ∈ (src.generateAt classify budget cut).admitted :=
              (complete_exact A label (calibrated cut) generated f).mpr ⟨candidate, run.1⟩
            refine (mem_sourceFrontier_succ A label).mpr ⟨f, admitted, restWord, ?_, rfl⟩
            exact (sourceFrontier_exact calibrated depth (f.result label cut) (children f admitted)
              restWord).mpr ⟨Nat.succ.inj length, run.2, rest⟩

/-- Firings admitted one after another, each where its predecessors left the configuration. -/
inductive Admitted : Configuration T O → List (Firing T S O) → Prop
  | nil (cut : Configuration T O) : Admitted cut []
  | cons {cut : Configuration T O} {f : Firing T S O} {rest : List (Firing T S O)} :
      f.Valid A label cut → Admitted (f.result label cut) rest → Admitted cut (f :: rest)

/-- **Incompleteness is located**: an incomplete frontier names a cut, reached by admitted firings
before its depth, whose generation ran out of budget. -/
theorem sourceFrontier_incomplete (calibrated : CalibratedEverywhere A label src classify) :
    ∀ (depth : ℕ) (cut : Configuration T O),
      (sourceFrontier A label src classify budget depth cut).2 = .incomplete →
        ∃ prefix_ : List (Firing T S O), prefix_.length < depth ∧ Admitted A label cut prefix_ ∧
          (src.generateAt classify budget (follow label cut prefix_)).status = .incomplete
  | 0, _, incomplete => by
      simp [sourceFrontier] at incomplete
  | depth + 1, cut, incomplete => by
      by_cases generated : (src.generateAt classify budget cut).status = .complete
      · by_cases children : ∀ f ∈ (src.generateAt classify budget cut).admitted,
            (sourceFrontier A label src classify budget depth (f.result label cut)).2 = .complete
        · have complete := (sourceFrontier_succ_status A label).mpr ⟨generated, children⟩
          rw [complete] at incomplete
          cases incomplete
        · simp only [not_forall] at children
          obtain ⟨f, admitted, open_⟩ := children
          have childIncomplete :
              (sourceFrontier A label src classify budget depth (f.result label cut)).2 = .incomplete := by
            cases h : (sourceFrontier A label src classify budget depth (f.result label cut)).2 with
            | complete => exact absurd h open_
            | incomplete => rfl
          obtain ⟨prefix_, length, path, located⟩ :=
            sourceFrontier_incomplete calibrated depth (f.result label cut) childIncomplete
          exact ⟨f :: prefix_, Nat.succ_lt_succ length,
            .cons (admitted_valid A label (calibrated cut) admitted) path, located⟩
      · have here : (src.generateAt classify budget cut).status = .incomplete := by
          cases h : (src.generateAt classify budget cut).status with
          | complete => exact absurd h generated
          | incomplete => rfl
        exact ⟨[], Nat.succ_pos depth, .nil cut, here⟩

/-- **The source form of exactness**: with scans that cover the present occurrences, a run's
firings were candidates where they fired exactly when they come from catalogue entries with the
identities supplied there. -/
theorem sourceRun_iff (covers : ∀ cut : Configuration T O, ∀ o ∈ cut.present, o ∈ src.scan cut) :
    ∀ (cut : Configuration T O) (word : List (Firing T S O)), Executable A label cut word →
      (SourceRun label src cut word ↔ EntryRun label src cut word)
  | _, [], _ => ⟨fun _ => .nil _, fun _ => .nil _⟩
  | cut, f :: rest, run => by
      constructor
      · intro source
        cases source with
        | cons candidate later =>
            obtain ⟨entry, -, -, -, -, made⟩ := mem_candidates.mp candidate
            exact .cons entry made ((sourceRun_iff covers _ rest run.2).mp later)
      · intro entries
        cases entries with
        | cons entry made later =>
            exact .cons (mem_candidates_of_valid A label (covers cut) entry made run.1)
              ((sourceRun_iff covers _ rest run.2).mpr later)

end Frontier

#print axioms Status.both_eq_complete
#print axioms childStatus_eq_complete
#print axioms mem_sourceFrontier_succ
#print axioms sourceFrontier_succ_status
#print axioms sourceFrontier_sound
#print axioms sourceFrontier_exact
#print axioms sourceFrontier_incomplete
#print axioms sourceRun_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunCandidates
