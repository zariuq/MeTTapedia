import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceReadoutsTraces

/-!
# Control: raw multiplicities differ, class sets agree, reduction counts trace classes

One program, every occurrence carrying `τ`, all firings ground:

* **`a | b`** (`PAR = {a, b}`): `fa` takes `a`, `fb` takes `b`. Two complete runs, `fa fb` and
  `fb fa`, one trace class: the two runs differ by one swap.
* **`a.b`** (`SEQ = {r}`): `ga` takes `r` and makes `s`, `gb` takes `s`. One complete run.

Both end at the configuration `End` with no occurrences.

* **Raw multiplicities differ** (`collect_PAR`, `collect_SEQ`, `runs_PAR`, `runs_SEQ`): R61's
  `collect` reports `End` twice for `a | b` and once for `a.b`, because it counts runs.
* **Class sets agree** (`classSet_PAR_SEQ`), for every classifier.
* **Partial-order reduction** with the key `a < b` and the exact independence as oracle
  (`keyLaws`, `sound`): the canonical complete runs of `a | b` are `fa fb` alone
  (`canonicalTo_PAR`), so the reduced count is one, the number of trace classes (`traces_PAR`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.TraceControls

open AnnotatedRuns (Firing)
open MeTTaCalculus.OccurrenceCommits (Enabled)
open GuardFreeProcessOrders (SameUpTo)

universe uT uS

/-- Occurrence identities. -/
inductive Site
  | a | b | r | s
  deriving DecidableEq

/-- The key of an occurrence: `a < b`. -/
def siteKey : Site → ℕ
  | .a => 0
  | .b => 1
  | .r => 2
  | .s => 3

variable {T : Type uT} {S : Type uS} (τ : T)

/-- Every occurrence carries `τ`. -/
def label : Site → T := fun _ => τ

/-- The ground firing that takes `taken` and makes `made`. -/
def firing (taken made : List Site) : Firing T S Site :=
  ⟨⟨taken.map (label τ), [], [], [], made.map (label τ)⟩, [], ⟨taken, [], made⟩⟩

def fa : Firing T S Site := firing τ [.a] []
def fb : Firing T S Site := firing τ [.b] []
def ga : Firing T S Site := firing τ [.r] [.s]
def gb : Firing T S Site := firing τ [.s] []

def alphabet : List (Firing T S Site) := [fa τ, fb τ, ga τ, gb τ]

/-- `n` copies of `(τ, τ)`. -/
def E (n : ℕ) : EquationStore T := List.replicate n (τ, τ)

def PAR : Configuration T Site := ⟨[], {.a, .b}⟩
def PARa : Configuration T Site := ⟨E τ 1, {.b}⟩
def PARb : Configuration T Site := ⟨E τ 1, {.a}⟩
def SEQ : Configuration T Site := ⟨[], {.r}⟩
def SEQa : Configuration T Site := ⟨E τ 1, {.s}⟩
def End : Configuration T Site := ⟨E τ 2, ∅⟩

theorem config_eq {C D : Configuration T Site} (equations : C.equations = D.equations)
    (present : C.present = D.present) : C = D := by
  cases C
  cases D
  cases equations
  cases present
  rfl

theorem reflexive_E (n : ℕ) : Reflexive (E τ n) := by
  intro e member
  rw [List.eq_of_mem_replicate member]

theorem ground : ∀ f ∈ alphabet (S := S) τ, Ground (label τ) f := by
  intro f member
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, of_decide_eq_true rfl, of_decide_eq_true rfl⟩

theorem alphabet_nodup : (alphabet (S := S) τ).Nodup := by
  simp [alphabet, fa, fb, ga, gb, firing]

theorem mem_fa : fa (S := S) τ ∈ alphabet τ := by simp [alphabet]
theorem mem_fb : fb (S := S) τ ∈ alphabet τ := by simp [alphabet]

variable (A : SubstitutionAction T S)

theorem valid_iff {f : Firing T S Site} (member : f ∈ alphabet τ) {C : Configuration T Site}
    (refl : Reflexive C.equations) :
    f.Valid A (label τ) C ↔ Enabled (label τ) C.present (f.selection.commit (T := T)) :=
  (ground τ f member).valid_iff A refl

theorem result_fa : (fa (S := S) τ).result (label τ) PAR = PARa τ := config_eq rfl (of_decide_eq_true rfl)
theorem result_fb : (fb (S := S) τ).result (label τ) PAR = PARb τ := config_eq rfl (of_decide_eq_true rfl)
theorem result_fb_a : (fb (S := S) τ).result (label τ) (PARa τ) = End τ :=
  config_eq rfl (of_decide_eq_true rfl)
theorem result_fa_b : (fa (S := S) τ).result (label τ) (PARb τ) = End τ :=
  config_eq rfl (of_decide_eq_true rfl)
theorem result_ga : (ga (S := S) τ).result (label τ) SEQ = SEQa τ := config_eq rfl (of_decide_eq_true rfl)
theorem result_gb : (gb (S := S) τ).result (label τ) (SEQa τ) = End τ :=
  config_eq rfl (of_decide_eq_true rfl)

/-! ## The search -/

/-- The search of the program. -/
noncomputable abbrev search := (alternatives A (label τ) (alphabet τ)).space

theorem next_PAR :
    ((alternatives A (label τ) (alphabet τ)).next PAR).map (fun g => g.1.1) = [fa (S := S) τ, fb τ] := by
  rw [next_map_of_ground (ground τ) reflexive_nil]
  rfl

theorem next_PARa :
    ((alternatives A (label τ) (alphabet τ)).next (PARa τ)).map (fun g => g.1.1) = [fb (S := S) τ] := by
  rw [next_map_of_ground (ground τ) (reflexive_E τ 1)]
  rfl

theorem next_PARb :
    ((alternatives A (label τ) (alphabet τ)).next (PARb τ)).map (fun g => g.1.1) = [fa (S := S) τ] := by
  rw [next_map_of_ground (ground τ) (reflexive_E τ 1)]
  rfl

theorem next_SEQ :
    ((alternatives A (label τ) (alphabet τ)).next SEQ).map (fun g => g.1.1) = [ga (S := S) τ] := by
  rw [next_map_of_ground (ground τ) reflexive_nil]
  rfl

theorem next_SEQa :
    ((alternatives A (label τ) (alphabet τ)).next (SEQa τ)).map (fun g => g.1.1) = [gb (S := S) τ] := by
  rw [next_map_of_ground (ground τ) (reflexive_E τ 1)]
  rfl

theorem next_End :
    ((alternatives A (label τ) (alphabet (S := S) τ)).next (End τ)).map (fun g => g.1.1) = [] := by
  rw [next_map_of_ground (ground τ) (reflexive_E τ 2)]
  rfl

theorem approx_End (n : ℕ) : (search τ A).approx (n + 1) (.inr (End τ)) = Search.Outcome.pure (End τ) := by
  rw [Search.Space.approx_succ, unfold_of_nil (next_End τ A)]
  simp [Search.Space.approx_inl]

theorem approx_PARa (n : ℕ) :
    (search τ A).approx (n + 1) (.inr (PARa τ)) = (search τ A).approx n (.inr (End τ)) := by
  rw [Search.Space.approx_succ, unfold_of_cons (next_PARa τ A)]
  simp [result_fb_a]

theorem approx_PARb (n : ℕ) :
    (search τ A).approx (n + 1) (.inr (PARb τ)) = (search τ A).approx n (.inr (End τ)) := by
  rw [Search.Space.approx_succ, unfold_of_cons (next_PARb τ A)]
  simp [result_fa_b]

theorem approx_SEQa (n : ℕ) :
    (search τ A).approx (n + 1) (.inr (SEQa τ)) = (search τ A).approx n (.inr (End τ)) := by
  rw [Search.Space.approx_succ, unfold_of_cons (next_SEQa τ A)]
  simp [result_gb]

theorem approx_PAR_succ (n : ℕ) : (search τ A).approx (n + 1) (.inr PAR) =
    (search τ A).approx n (.inr (PARa τ)) + (search τ A).approx n (.inr (PARb τ)) := by
  rw [Search.Space.approx_succ, unfold_of_cons (next_PAR τ A)]
  simp [result_fa, result_fb]

theorem approx_SEQ_succ (n : ℕ) :
    (search τ A).approx (n + 1) (.inr SEQ) = (search τ A).approx n (.inr (SEQa τ)) := by
  rw [Search.Space.approx_succ, unfold_of_cons (next_SEQ τ A)]
  simp [result_ga]

theorem approx_PAR : (search τ A).approx 3 (.inr PAR) = ⟨{End τ, End τ}, .finished⟩ := by
  rw [approx_PAR_succ, approx_PARa, approx_PARb, approx_End]
  rfl

theorem approx_SEQ : (search τ A).approx 3 (.inr SEQ) = ⟨{End τ}, .finished⟩ := by
  rw [approx_SEQ_succ, approx_SEQa, approx_End]
  rfl

theorem finished_PAR : ((search τ A).run 3 (.inr PAR)).status = .finished := by
  have status : ((search τ A).approx 3 (.inr PAR)).status = .finished := by
    rw [approx_PAR]
  exact status

theorem finished_SEQ : ((search τ A).run 3 (.inr SEQ)).status = .finished := by
  have status : ((search τ A).approx 3 (.inr SEQ)).status = .finished := by
    rw [approx_SEQ]
  exact status

/-- **`collect` reports `End` twice for `a | b`.** -/
theorem collect_PAR : Search.Outcome.collect ((search τ A).approx 3 (.inr PAR)) =
    Search.Outcome.pure ({End τ, End τ} : Multiset (Configuration T Site)) := by
  rw [approx_PAR]
  rfl

/-- **`collect` reports `End` once for `a.b`.** -/
theorem collect_SEQ : Search.Outcome.collect ((search τ A).approx 3 (.inr SEQ)) =
    Search.Outcome.pure ({End τ} : Multiset (Configuration T Site)) := by
  rw [approx_SEQ]
  rfl

/-- **The class sets agree**, for every classifier. -/
theorem classSet_PAR_SEQ {β : Type*} (cls : Configuration T Site → β) :
    Search.classSet cls ((search τ A).approx 3 (.inr PAR)) =
      Search.classSet cls ((search τ A).approx 3 (.inr SEQ)) := by
  rw [approx_PAR, approx_SEQ]
  ext c
  simp [Search.classSet]

/-! ## Runs, trace classes and canonical runs -/

/-- The step of the program. -/
abbrev Prog := program A (label τ) (alphabet (S := S) τ)

/-- The one-frame transport of the program. -/
abbrev Tr := programTransport A (label τ) (alphabet (S := S) τ)

/-- The key of a firing: the key of the occurrence it takes first. -/
def key (_ : Configuration T Site) (f : {f : Firing T S Site // f ∈ alphabet τ}) : ℕ :=
  siteKey (f.1.selection.taken.headD .a)

/-- **The oracle**: the exact independence of the transport. -/
def indep (s : Configuration T Site) (f g : {f : Firing T S Site // f ∈ alphabet τ}) : Prop :=
  (Tr τ A).Independent s f g

theorem sound : ∀ s f g, indep τ A s f g → (Tr τ A).Independent s f g := fun _ _ _ h => h

/-- **The key is kept by transport, alikeness and residuals.** -/
theorem keyLaws : Interface.Transport.KeyLaws (Tr τ A) (key τ) := by
  refine ⟨fun _ _ => rfl, ?_, fun _ _ _ => rfl⟩
  intro _ f f' alike
  have same : f.1 = f'.1 := alike
  show siteKey (f.1.selection.taken.headD .a) = siteKey (f'.1.selection.taken.headD .a)
  rw [same]

theorem valid_fa : (fa (S := S) τ).Valid A (label τ) PAR :=
  (valid_iff τ A (mem_fa τ) reflexive_nil).mpr (of_decide_eq_true rfl)
theorem valid_fb : (fb (S := S) τ).Valid A (label τ) PAR :=
  (valid_iff τ A (mem_fb τ) reflexive_nil).mpr (of_decide_eq_true rfl)
theorem valid_fb_after : (fb (S := S) τ).Valid A (label τ) ((fa (S := S) τ).result (label τ) PAR) := by
  rw [result_fa]
  exact (valid_iff τ A (mem_fb τ) (reflexive_E τ 1)).mpr (of_decide_eq_true rfl)
theorem valid_fa_after : (fa (S := S) τ).Valid A (label τ) ((fb (S := S) τ).result (label τ) PAR) := by
  rw [result_fb]
  exact (valid_iff τ A (mem_fa τ) (reflexive_E τ 1)).mpr (of_decide_eq_true rfl)

/-- The run `fa fb`. -/
def r₁ : (Prog τ A).Run PAR :=
  .cons ⟨fa τ, mem_fa τ⟩ (valid_fa τ A) (.cons ⟨fb τ, mem_fb τ⟩ (valid_fb_after τ A) (.nil _))

/-- The run `fb fa`. -/
def r₂ : (Prog τ A).Run PAR :=
  .cons ⟨fb τ, mem_fb τ⟩ (valid_fb τ A) (.cons ⟨fa τ, mem_fa τ⟩ (valid_fa_after τ A) (.nil _))

theorem halted_End : Search.Halted (Prog τ A) (End τ) := by
  rintro ⟨f, member⟩ valid
  have valid' : f.Valid A (label τ) (End τ) := valid
  rw [valid_iff τ A member (reflexive_E τ 2)] at valid'
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> exact of_decide_eq_false rfl valid'

theorem last_r₁ : (r₁ τ A).last = End τ := by
  show (fb (S := S) τ).result (label τ) ((fa (S := S) τ).result (label τ) PAR) = End τ
  rw [result_fa, result_fb_a]

theorem last_r₂ : (r₂ τ A).last = End τ := by
  show (fa (S := S) τ).result (label τ) ((fb (S := S) τ).result (label τ) PAR) = End τ
  rw [result_fb, result_fa_b]

theorem r₁_ne_r₂ : r₁ τ A ≠ r₂ τ A := fun same =>
  absurd (congrArg (Interface.Transport.keyWord (key τ)) same) (of_decide_eq_false rfl)

/-- The firing `fa` of the program. -/
abbrev pa : {f : Firing T S Site // f ∈ alphabet τ} := ⟨fa τ, mem_fa τ⟩
/-- The firing `fb` of the program. -/
abbrev pb : {f : Firing T S Site // f ∈ alphabet τ} := ⟨fb τ, mem_fb τ⟩

theorem same_ends :
    (Tr τ A).Same ((fb (S := S) τ).result (label τ) ((fa (S := S) τ).result (label τ) PAR))
      ((fa (S := S) τ).result (label τ) ((fb (S := S) τ).result (label τ) PAR)) := by
  rw [result_fa, result_fb, result_fb_a, result_fa_b]
  exact ⟨⟨SameUpTo.refl A _⟩⟩

/-- **The two runs of `a | b` are one trace class**: they differ by one swap. -/
theorem traceEquiv_r₁_r₂ : (Tr τ A).TraceEquiv PAR (r₁ τ A) (r₂ τ A) :=
  .rel _ _ (.inl (Interface.Transport.SwapStep.here (T := Tr τ A) (f := pa τ) (g := pb τ)
    (valid_fa τ A) (valid_fb τ A) (g₁ := pb τ) rfl (valid_fb_after τ A) (f₁ := pa τ) rfl
    (valid_fa_after τ A) (rest := .nil _) (rest' := .nil _) (same_ends τ A)))

/-- `fa fb` is canonical: nothing has a key below `a`. -/
theorem canonical_r₁ : Interface.Transport.Canonical (Tr τ A) (key τ) (indep τ A) (r₁ τ A) := by
  refine (Interface.Transport.canonical_pair_iff (T := Tr τ A) (key := key τ) (indep := indep τ A)
    (f := pa τ) (g₁ := pb τ) (valid_fa τ A) (valid_fb_after τ A)).mpr ?_
  rintro ⟨g, _, smaller, _⟩
  exact Nat.not_lt_zero _ smaller

theorem independent_fb_fa : (Tr τ A).Independent PAR (pb τ) (pa τ) :=
  ⟨valid_fb τ A, valid_fa τ A, valid_fa_after τ A, valid_fb_after τ A, (same_ends τ A).symm⟩

/-- `fb fa` is not canonical: `a` has the smaller key and the pair is independent. -/
theorem not_canonical_r₂ : ¬ Interface.Transport.Canonical (Tr τ A) (key τ) (indep τ A) (r₂ τ A) :=
  fun canonical => canonical (Interface.Transport.Inverted.here (T := Tr τ A) (key := key τ)
    (indep := indep τ A) (f := pb τ) (g := pa τ) (g₁ := pa τ) (valid_fb τ A) rfl
    (valid_fa_after τ A) (.nil _) (show key τ PAR (pa τ) < key τ PAR (pb τ) from Nat.zero_lt_one)
    (independent_fb_fa τ A))

theorem complete_r₁ : r₁ τ A ∈ Search.runsTo (Prog τ A) id PAR (End τ) :=
  ⟨by rw [last_r₁]; exact halted_End τ A, last_r₁ τ A⟩

theorem complete_r₂ : r₂ τ A ∈ Search.runsTo (Prog τ A) id PAR (End τ) :=
  ⟨by rw [last_r₂]; exact halted_End τ A, last_r₂ τ A⟩

/-- **`a | b` has two complete runs ending at `End`.** -/
theorem runs_PAR : (Search.runsTo (Prog τ A) id PAR (End τ)).encard = 2 := by
  classical
  rw [← Search.count_eq_runs (enumeration A (label τ) (alphabet τ) (alphabet_nodup τ))
    (finished_PAR τ A) (End τ)]
  show (((search τ A).approx 3 (.inr PAR)).answers.count (End τ) : ℕ∞) = 2
  rw [approx_PAR]
  simp

/-- **`a.b` has one complete run ending at `End`.** -/
theorem runs_SEQ : (Search.runsTo (Prog τ A) id SEQ (End τ)).encard = 1 := by
  classical
  rw [← Search.count_eq_runs (enumeration A (label τ) (alphabet τ) (alphabet_nodup τ))
    (finished_SEQ τ A) (End τ)]
  show (((search τ A).approx 3 (.inr SEQ)).answers.count (End τ) : ℕ∞) = 1
  rw [approx_SEQ]
  simp

theorem runsTo_PAR : Search.runsTo (Prog τ A) id PAR (End τ) = {r₁ τ A, r₂ τ A} := by
  refine (Set.Finite.eq_of_subset_of_encard_le (Set.toFinite _) ?_ ?_).symm
  · intro r member
    rcases member with rfl | rfl
    · exact complete_r₁ τ A
    · exact complete_r₂ τ A
  · rw [runs_PAR, Set.encard_pair (r₁_ne_r₂ τ A)]
/-- **Partial-order reduction keeps `fa fb` alone.** -/
theorem canonicalTo_PAR :
    Search.canonicalTo (Tr τ A) (key τ) (indep τ A) id PAR (End τ) = {r₁ τ A} := by
  ext r
  constructor
  · rintro ⟨halted, ends, canonical⟩
    have member : r ∈ Search.runsTo (Prog τ A) id PAR (End τ) := ⟨halted, ends⟩
    rw [runsTo_PAR] at member
    rcases member with rfl | member
    · rfl
    · rw [Set.mem_singleton_iff.mp member] at canonical
      exact absurd canonical (not_canonical_r₂ τ A)
  · rintro rfl
    exact ⟨(complete_r₁ τ A).1, (complete_r₁ τ A).2, canonical_r₁ τ A⟩

/-- **`a | b` has one trace class of complete runs ending at `End`.** -/
theorem traces_PAR : (Search.tracesTo (Tr τ A) id PAR (End τ)).encard = 1 := by
  unfold Search.tracesTo
  rw [runsTo_PAR, Set.image_pair,
    Quotient.sound (s := Search.traceSetoid (Tr τ A) PAR) (traceEquiv_r₁_r₂ τ A), Set.pair_eq_singleton,
    Set.encard_singleton]

/-- **Raw multiplicities differ, class sets agree, and the reduction counts trace classes.** -/
theorem multiplicity_control {β : Type*} (cls : Configuration T Site → β) :
    Search.Outcome.collect ((search τ A).approx 3 (.inr PAR)) ≠
        Search.Outcome.collect ((search τ A).approx 3 (.inr SEQ)) ∧
      Search.classSet cls ((search τ A).approx 3 (.inr PAR)) =
        Search.classSet cls ((search τ A).approx 3 (.inr SEQ)) ∧
      (Search.runsTo (Prog τ A) id PAR (End τ)).encard = 2 ∧
      (Search.runsTo (Prog τ A) id SEQ (End τ)).encard = 1 ∧
      (Search.canonicalTo (Tr τ A) (key τ) (indep τ A) id PAR (End τ)).encard = 1 ∧
      (Search.tracesTo (Tr τ A) id PAR (End τ)).encard = 1 := by
  refine ⟨?_, classSet_PAR_SEQ τ A cls, runs_PAR τ A, runs_SEQ τ A, ?_, traces_PAR τ A⟩
  · rw [collect_PAR, collect_SEQ]
    intro same
    have inner : ({End τ, End τ} : Multiset (Configuration T Site)) = {End τ} := by
      have answers := congrArg Search.Outcome.answers same
      simpa using answers
    have cards := congrArg Multiset.card inner
    simp at cards
  · rw [canonicalTo_PAR, Set.encard_singleton]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.TraceControls

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.TraceControls in
#print axioms keyLaws
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.TraceControls in
#print axioms traceEquiv_r₁_r₂
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.TraceControls in
#print axioms canonicalTo_PAR
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.TraceControls in
#print axioms multiplicity_control
