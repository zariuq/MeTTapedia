import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.PracticalEthicsKernel
import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.MetaEthicsKernel
import Mathlib.Computability.Partrec

set_option autoImplicit false

/-!
# Practical Ethics Resolution

A finite, deterministic GenEth-style resolver over an explicit candidate set.

The resolver checks whether any candidate dominates all competitors under a
`GenEthPrinciple`.  If such a candidate exists, it is recommended; otherwise
the judgment is tied.

This is intentionally restricted: no probabilistic search, no learning, no
heavy optimization.  The point is one honest, provably correct practical
resolution procedure.

## References

- M. Anderson & S. L. Anderson, "GenEth: A General Ethical Dilemma
  Analyzer," AAAI 2014.
-/

namespace Mettapedia.CognitiveArchitecture.GodelClaw.Ethics

open Mettapedia.Ethics
open scoped Classical

universe u v

variable {Action : Type u} {Feature : Type v} {Duty : Type v}

/-- An action `a` is preferred to `b` under a principle when the principle
prefers the duty differential `a - b`. -/
def actionPreferred
    (principle : GenEthPrinciple Duty)
    (profiles : Action → GenEthActionProfile Action Feature Duty)
    (a b : Action) : Prop :=
  principle.Prefers ((profiles a).differential (profiles b))

/-- An action `a` dominates all competitors in a finite set. -/
def dominatesAll
    (principle : GenEthPrinciple Duty)
    (profiles : Action → GenEthActionProfile Action Feature Duty)
    (candidates : Finset Action)
    (a : Action) : Prop :=
  a ∈ candidates ∧ ∀ b ∈ candidates, b ≠ a → actionPreferred principle profiles a b

/-- The deterministic pairwise resolver: recommends a dominant candidate if one
exists, otherwise returns tied.

Uses `Classical.choice` to select a witness when existence is established.
The correctness theorems below certify the relationship between the judgment
and the `dominatesAll` predicate. -/
noncomputable def pairwiseResolveJudgment
    [DecidableEq Action]
    (principle : GenEthPrinciple Duty)
    (profiles : Action → GenEthActionProfile Action Feature Duty)
    (candidates : Finset Action) : ResolutionJudgment Action :=
  if h : ∃ a ∈ candidates, dominatesAll principle profiles candidates a then
    let a := Classical.choose h
    { status := .recommends
      chosen := some a
      rejected := { b | b ∈ candidates ∧ b ≠ a } }
  else
    { status := .tied
      chosen := none
      rejected := ∅ }

/-- If a dominant candidate exists, the resolver recommends one. -/
theorem pairwiseResolveJudgment_recommends_of_dominant
    [DecidableEq Action]
    {principle : GenEthPrinciple Duty}
    {profiles : Action → GenEthActionProfile Action Feature Duty}
    {candidates : Finset Action}
    (hexists : ∃ a ∈ candidates, dominatesAll principle profiles candidates a) :
    (pairwiseResolveJudgment principle profiles candidates).status = .recommends := by
  unfold pairwiseResolveJudgment
  rw [dif_pos hexists]

/-- The recommended candidate is genuinely dominant. -/
theorem pairwiseResolveJudgment_chosen_dominates
    [DecidableEq Action]
    {principle : GenEthPrinciple Duty}
    {profiles : Action → GenEthActionProfile Action Feature Duty}
    {candidates : Finset Action}
    (hexists : ∃ a ∈ candidates, dominatesAll principle profiles candidates a) :
    ∃ a, (pairwiseResolveJudgment principle profiles candidates).Recommends a ∧
      dominatesAll principle profiles candidates a := by
  have hdom := Classical.choose_spec hexists
  refine ⟨Classical.choose hexists, ?_, hdom.2⟩
  unfold pairwiseResolveJudgment
  rw [dif_pos hexists]
  exact ⟨rfl, rfl⟩

/-- If no candidate dominates, the resolver returns tied. -/
theorem pairwiseResolveJudgment_tied_of_no_dominant
    [DecidableEq Action]
    {principle : GenEthPrinciple Duty}
    {profiles : Action → GenEthActionProfile Action Feature Duty}
    {candidates : Finset Action}
    (hno : ¬ ∃ a ∈ candidates, dominatesAll principle profiles candidates a) :
    (pairwiseResolveJudgment principle profiles candidates).status = .tied := by
  unfold pairwiseResolveJudgment
  rw [dif_neg hno]

/-- A dominant candidate that is recommended beats every specific competitor. -/
theorem dominatesAll_beats_competitor
    {principle : GenEthPrinciple Duty}
    {profiles : Action → GenEthActionProfile Action Feature Duty}
    {candidates : Finset Action}
    {a b : Action}
    (hdom : dominatesAll principle profiles candidates a)
    (hb : b ∈ candidates) (hne : b ≠ a) :
    actionPreferred principle profiles a b :=
  hdom.2 b hb hne

-- ═══════════════════════════════════════════════════════════════════════════
-- Computable finite resolver: explicit search instead of Classical.choose
-- ═══════════════════════════════════════════════════════════════════════════

/-- Bool recursion lemmas for explicit finite lists. -/
theorem list_all_eq_true_iff {α : Type u} {l : List α} {p : α → Bool} :
    l.all p = true ↔ ∀ a ∈ l, p a = true := by
  induction l with
  | nil =>
      simp
  | cons b rest ih =>
      simp [ih]

theorem list_any_eq_true_iff {α : Type u} {l : List α} {p : α → Bool} :
    l.any p = true ↔ ∃ a ∈ l, p a = true := by
  induction l with
  | nil =>
      simp
  | cons b rest ih =>
      simp [ih]

/-- Boolean checker for clause satisfaction over an explicit duty domain. -/
def DutyDifferential.satisfiesBool
    (dutyDomain : ExplicitFiniteDomain Duty)
    (δ : DutyDifferential Duty) (clause : GenEthClause Duty) : Bool :=
  dutyDomain.elems.all fun d => decide (clause.lowerBound d ≤ δ.delta d)

@[simp] theorem DutyDifferential.satisfiesBool_eq_true_iff
    (dutyDomain : ExplicitFiniteDomain Duty)
    (δ : DutyDifferential Duty) (clause : GenEthClause Duty) :
    δ.satisfiesBool dutyDomain clause = true ↔ δ.Satisfies clause := by
  constructor
  · intro h d
    have hall := (list_all_eq_true_iff).1 h d (dutyDomain.complete d)
    simpa using hall
  · intro h
    apply (list_all_eq_true_iff).2
    intro d hd
    simpa using h d

/-- Boolean checker for whether a GenEth principle prefers a duty differential. -/
def GenEthPrinciple.prefersBool
    (dutyDomain : ExplicitFiniteDomain Duty)
    (principle : GenEthPrinciple Duty) (δ : DutyDifferential Duty) : Bool :=
  principle.any fun clause => δ.satisfiesBool dutyDomain clause

@[simp] theorem GenEthPrinciple.prefersBool_eq_true_iff
    (dutyDomain : ExplicitFiniteDomain Duty)
    (principle : GenEthPrinciple Duty) (δ : DutyDifferential Duty) :
    principle.prefersBool dutyDomain δ = true ↔ principle.Prefers δ := by
  unfold GenEthPrinciple.prefersBool GenEthPrinciple.Prefers
  simp [DutyDifferential.satisfiesBool_eq_true_iff]

/-- Boolean checker for pairwise action preference under an explicit duty domain. -/
def actionPreferredBool
    (dutyDomain : ExplicitFiniteDomain Duty)
    (principle : GenEthPrinciple Duty)
    (profiles : Action → GenEthActionProfile Action Feature Duty)
    (a b : Action) : Bool :=
  principle.prefersBool dutyDomain ((profiles a).differential (profiles b))

@[simp] theorem actionPreferredBool_eq_true_iff
    (dutyDomain : ExplicitFiniteDomain Duty)
    (principle : GenEthPrinciple Duty)
    (profiles : Action → GenEthActionProfile Action Feature Duty)
    (a b : Action) :
    actionPreferredBool dutyDomain principle profiles a b = true ↔
      actionPreferred principle profiles a b := by
  unfold actionPreferredBool actionPreferred
  simp

/-- Boolean checker for dominance over an explicit candidate set. -/
def dominatesAllBool
    [DecidableEq Action]
    (dutyDomain : ExplicitFiniteDomain Duty)
    (candidateSet : ExplicitFiniteSet Action)
    (principle : GenEthPrinciple Duty)
    (profiles : Action → GenEthActionProfile Action Feature Duty)
    (a : Action) : Bool :=
  decide (a ∈ candidateSet.toFinset) &&
    candidateSet.elems.all fun b =>
      decide (b = a) || actionPreferredBool dutyDomain principle profiles a b

@[simp] theorem dominatesAllBool_eq_true_iff
    [DecidableEq Action]
    (dutyDomain : ExplicitFiniteDomain Duty)
    (candidateSet : ExplicitFiniteSet Action)
    (principle : GenEthPrinciple Duty)
    (profiles : Action → GenEthActionProfile Action Feature Duty)
    (a : Action) :
    dominatesAllBool dutyDomain candidateSet principle profiles a = true ↔
      dominatesAll principle profiles candidateSet.toFinset a := by
  constructor
  · intro h
    have hsplit :
        decide (a ∈ candidateSet.toFinset) = true ∧
          candidateSet.elems.all
              (fun b => decide (b = a) || actionPreferredBool dutyDomain principle profiles a b) =
            true := by
      simpa [dominatesAllBool, Bool.and_eq_true] using h
    have ha : a ∈ candidateSet.toFinset := by
      simpa using hsplit.1
    refine ⟨ha, ?_⟩
    intro b hb hne
    have hbList : b ∈ candidateSet.elems := by
      exact (ExplicitFiniteSet.mem_toFinset_iff candidateSet b).1 hb
    have hall :=
      (list_all_eq_true_iff).1 hsplit.2 b hbList
    have hprefBool : actionPreferredBool dutyDomain principle profiles a b = true := by
      simpa [hne] using hall
    exact (actionPreferredBool_eq_true_iff _ _ _ _ _).1 hprefBool
  · intro hdom
    have hleft : decide (a ∈ candidateSet.toFinset) = true := by
      simpa using hdom.1
    have hright :
        candidateSet.elems.all
            (fun b => decide (b = a) || actionPreferredBool dutyDomain principle profiles a b) =
          true := by
      apply (list_all_eq_true_iff).2
      intro b hb
      by_cases hEq : b = a
      · simp [hEq]
      · have hbFin : b ∈ candidateSet.toFinset := by
          exact (ExplicitFiniteSet.mem_toFinset_iff candidateSet b).2 hb
        have hpref : actionPreferred principle profiles a b := hdom.2 b hbFin hEq
        simp [hEq, (actionPreferredBool_eq_true_iff _ _ _ _ _).2 hpref]
    simpa [dominatesAllBool, Bool.and_eq_true] using And.intro hleft hright

/-- Explicit recursive search for a dominant candidate in an explicit candidate
list. -/
def searchDominantCandidate
    [DecidableEq Action]
    (dutyDomain : ExplicitFiniteDomain Duty)
    (candidateSet : ExplicitFiniteSet Action)
    (principle : GenEthPrinciple Duty)
    (profiles : Action → GenEthActionProfile Action Feature Duty) :
    List Action → Option Action
  | [] => none
  | a :: rest =>
      if dominatesAllBool dutyDomain candidateSet principle profiles a then
        some a
      else
        searchDominantCandidate dutyDomain candidateSet principle profiles rest

theorem searchDominantCandidate_some
    [DecidableEq Action]
    {dutyDomain : ExplicitFiniteDomain Duty}
    {candidateSet : ExplicitFiniteSet Action}
    {principle : GenEthPrinciple Duty}
    {profiles : Action → GenEthActionProfile Action Feature Duty}
    {search : List Action} {a : Action}
    (h : searchDominantCandidate dutyDomain candidateSet principle profiles search = some a) :
    a ∈ search ∧ dominatesAllBool dutyDomain candidateSet principle profiles a = true := by
  induction search with
  | nil =>
      simp [searchDominantCandidate] at h
  | cons b rest ih =>
      by_cases hb : dominatesAllBool dutyDomain candidateSet principle profiles b = true
      · simp [searchDominantCandidate, hb] at h
        cases h
        exact ⟨by simp, hb⟩
      · simp [searchDominantCandidate, hb] at h
        rcases ih h with ⟨hmem, hdom⟩
        exact ⟨by simp [hmem], hdom⟩

theorem searchDominantCandidate_some_of_exists
    [DecidableEq Action]
    {dutyDomain : ExplicitFiniteDomain Duty}
    {candidateSet : ExplicitFiniteSet Action}
    {principle : GenEthPrinciple Duty}
    {profiles : Action → GenEthActionProfile Action Feature Duty}
    {search : List Action}
    (hexists : ∃ a ∈ search, dominatesAllBool dutyDomain candidateSet principle profiles a = true) :
    ∃ a, searchDominantCandidate dutyDomain candidateSet principle profiles search = some a := by
  induction search with
  | nil =>
      rcases hexists with ⟨a, ha, _⟩
      simp at ha
  | cons b rest ih =>
      rcases hexists with ⟨a, ha, hdom⟩
      simp at ha
      rcases ha with rfl | ha
      · exact ⟨a, by simp [searchDominantCandidate, hdom]⟩
      · by_cases hb : dominatesAllBool dutyDomain candidateSet principle profiles b = true
        · exact ⟨b, by simp [searchDominantCandidate, hb]⟩
        · rcases ih ⟨a, ha, hdom⟩ with ⟨c, hc⟩
          exact ⟨c, by simp [searchDominantCandidate, hb, hc]⟩

/-- The explicit recursive search is extensionally the usual "find the first
candidate satisfying the dominance predicate" pattern. -/
theorem searchDominantCandidate_eq_findIdx_getElem?
    [DecidableEq Action]
    (dutyDomain : ExplicitFiniteDomain Duty)
    (candidateSet : ExplicitFiniteSet Action)
    (principle : GenEthPrinciple Duty)
    (profiles : Action → GenEthActionProfile Action Feature Duty) :
    ∀ search : List Action,
      searchDominantCandidate dutyDomain candidateSet principle profiles search =
        search[search.findIdx
          (fun a => dominatesAllBool dutyDomain candidateSet principle profiles a)]?
  | [] => by
      simp [searchDominantCandidate]
  | a :: rest => by
      by_cases hdom : dominatesAllBool dutyDomain candidateSet principle profiles a = true
      · simp [searchDominantCandidate, List.findIdx_cons, hdom]
      · simp [searchDominantCandidate, List.findIdx_cons, hdom,
          searchDominantCandidate_eq_findIdx_getElem?]

/-- Restricted mathlib computability certificate for the explicit dominant-action
search.

This is intentionally the first small honest foothold: if the boolean dominance
predicate is primitive recursive, then the explicit list search used by the
resolver is computable. -/
theorem searchDominantCandidate_computable
    [DecidableEq Action] [Primcodable Action]
    {dutyDomain : ExplicitFiniteDomain Duty}
    {candidateSet : ExplicitFiniteSet Action}
    {principle : GenEthPrinciple Duty}
    {profiles : Action → GenEthActionProfile Action Feature Duty}
    (hdom :
      _root_.Primrec
        (fun a : Action =>
          dominatesAllBool dutyDomain candidateSet principle profiles a)) :
    Computable
      (fun search : List Action =>
        searchDominantCandidate dutyDomain candidateSet principle profiles search) := by
  have hp₂ :
      _root_.Primrec₂
        (fun (_ : List Action) (a : Action) =>
          dominatesAllBool dutyDomain candidateSet principle profiles a) := by
    simpa using (hdom.comp _root_.Primrec.snd).to₂
  have hfindIdx :
      Computable
        (fun search : List Action =>
          search.findIdx
            (fun a => dominatesAllBool dutyDomain candidateSet principle profiles a)) := by
    simpa using ((_root_.Primrec.list_findIdx (_root_.Primrec.id) hp₂).to_comp :
      Computable
        (fun search : List Action =>
          search.findIdx
            (fun a => dominatesAllBool dutyDomain candidateSet principle profiles a)))
  have hget :
      Computable
        (fun search : List Action =>
          search[search.findIdx
            (fun a => dominatesAllBool dutyDomain candidateSet principle profiles a)]?) := by
    simpa using
      (Computable.list_getElem?.comp Computable.id hfindIdx :
        Computable
          (fun search : List Action =>
            search[search.findIdx
              (fun a => dominatesAllBool dutyDomain candidateSet principle profiles a)]?))
  refine Computable.of_eq hget ?_
  intro search
  symm
  exact searchDominantCandidate_eq_findIdx_getElem?
    dutyDomain candidateSet principle profiles search

/-- Explicit dominant-candidate search over the canonical candidate list. -/
def findDominantCandidate?
    [DecidableEq Action]
    (dutyDomain : ExplicitFiniteDomain Duty)
    (candidateSet : ExplicitFiniteSet Action)
    (principle : GenEthPrinciple Duty)
    (profiles : Action → GenEthActionProfile Action Feature Duty) : Option Action :=
  searchDominantCandidate dutyDomain candidateSet principle profiles candidateSet.elems

theorem findDominantCandidate?_some
    [DecidableEq Action]
    {dutyDomain : ExplicitFiniteDomain Duty}
    {candidateSet : ExplicitFiniteSet Action}
    {principle : GenEthPrinciple Duty}
    {profiles : Action → GenEthActionProfile Action Feature Duty}
    {a : Action}
    (h : findDominantCandidate? dutyDomain candidateSet principle profiles = some a) :
    a ∈ candidateSet.toFinset ∧
      dominatesAllBool dutyDomain candidateSet principle profiles a = true := by
  unfold findDominantCandidate? at h
  rcases searchDominantCandidate_some h with ⟨hmem, hdom⟩
  exact ⟨(ExplicitFiniteSet.mem_toFinset_iff candidateSet a).2 hmem, hdom⟩

theorem findDominantCandidate?_some_dominates
    [DecidableEq Action]
    {dutyDomain : ExplicitFiniteDomain Duty}
    {candidateSet : ExplicitFiniteSet Action}
    {principle : GenEthPrinciple Duty}
    {profiles : Action → GenEthActionProfile Action Feature Duty}
    {a : Action}
    (h : findDominantCandidate? dutyDomain candidateSet principle profiles = some a) :
    a ∈ candidateSet.toFinset ∧
      dominatesAll principle profiles candidateSet.toFinset a := by
  rcases findDominantCandidate?_some h with ⟨hmem, hdom⟩
  exact ⟨hmem, (dominatesAllBool_eq_true_iff _ _ _ _ _).1 hdom⟩

theorem findDominantCandidate?_some_of_dominates
    [DecidableEq Action]
    {dutyDomain : ExplicitFiniteDomain Duty}
    {candidateSet : ExplicitFiniteSet Action}
    {principle : GenEthPrinciple Duty}
    {profiles : Action → GenEthActionProfile Action Feature Duty}
    {a : Action}
    (hdom : dominatesAll principle profiles candidateSet.toFinset a) :
    ∃ b, findDominantCandidate? dutyDomain candidateSet principle profiles = some b := by
  have hbool : dominatesAllBool dutyDomain candidateSet principle profiles a = true :=
    (dominatesAllBool_eq_true_iff _ _ _ _ _).2 hdom
  refine searchDominantCandidate_some_of_exists ?_
  exact ⟨a, (ExplicitFiniteSet.mem_toFinset_iff candidateSet a).1 hdom.1, hbool⟩

theorem findDominantCandidate?_none_of_no_dominant
    [DecidableEq Action]
    {dutyDomain : ExplicitFiniteDomain Duty}
    {candidateSet : ExplicitFiniteSet Action}
    {principle : GenEthPrinciple Duty}
    {profiles : Action → GenEthActionProfile Action Feature Duty}
    (hno : ¬ ∃ a ∈ candidateSet.toFinset, dominatesAll principle profiles candidateSet.toFinset a) :
    findDominantCandidate? dutyDomain candidateSet principle profiles = none := by
  cases hfind : findDominantCandidate? dutyDomain candidateSet principle profiles with
  | none =>
      exact rfl
  | some a =>
      exfalso
      rcases findDominantCandidate?_some_dominates hfind with ⟨hmem, hdom⟩
      exact hno ⟨a, hmem, hdom⟩

/-- Computable resolver based on explicit finite search. -/
def pairwiseResolveJudgmentComputable
    [DecidableEq Action]
    (dutyDomain : ExplicitFiniteDomain Duty)
    (candidateSet : ExplicitFiniteSet Action)
    (principle : GenEthPrinciple Duty)
    (profiles : Action → GenEthActionProfile Action Feature Duty) :
    ResolutionJudgment Action :=
  match findDominantCandidate? dutyDomain candidateSet principle profiles with
  | some a =>
      { status := .recommends
        chosen := some a
        rejected := { b | b ∈ candidateSet.toFinset ∧ b ≠ a } }
  | none =>
      { status := .tied
        chosen := none
        rejected := ∅ }

theorem pairwiseResolveJudgmentComputable_recommends_of_dominant
    [DecidableEq Action]
    {dutyDomain : ExplicitFiniteDomain Duty}
    {candidateSet : ExplicitFiniteSet Action}
    {principle : GenEthPrinciple Duty}
    {profiles : Action → GenEthActionProfile Action Feature Duty}
    (hexists : ∃ a ∈ candidateSet.toFinset,
      dominatesAll principle profiles candidateSet.toFinset a) :
    (pairwiseResolveJudgmentComputable dutyDomain candidateSet principle profiles).status =
      ResolutionStatus.recommends := by
  rcases hexists with ⟨a, _, hdom⟩
  rcases findDominantCandidate?_some_of_dominates hdom with ⟨b, hb⟩
  unfold pairwiseResolveJudgmentComputable
  rw [show findDominantCandidate? dutyDomain candidateSet principle profiles = some b from hb]

theorem pairwiseResolveJudgmentComputable_chosen_dominates
    [DecidableEq Action]
    {dutyDomain : ExplicitFiniteDomain Duty}
    {candidateSet : ExplicitFiniteSet Action}
    {principle : GenEthPrinciple Duty}
    {profiles : Action → GenEthActionProfile Action Feature Duty}
    (hexists : ∃ a ∈ candidateSet.toFinset,
      dominatesAll principle profiles candidateSet.toFinset a) :
    ∃ a, (pairwiseResolveJudgmentComputable dutyDomain candidateSet principle profiles).Recommends a ∧
      dominatesAll principle profiles candidateSet.toFinset a := by
  rcases hexists with ⟨a, _, hdom⟩
  rcases findDominantCandidate?_some_of_dominates hdom with ⟨b, hb⟩
  refine ⟨b, ?_, ?_⟩
  · unfold pairwiseResolveJudgmentComputable ResolutionJudgment.Recommends
    rw [show findDominantCandidate? dutyDomain candidateSet principle profiles = some b from hb]
    simp
  · exact (findDominantCandidate?_some_dominates hb).2

theorem pairwiseResolveJudgmentComputable_tied_of_no_dominant
    [DecidableEq Action]
    {dutyDomain : ExplicitFiniteDomain Duty}
    {candidateSet : ExplicitFiniteSet Action}
    {principle : GenEthPrinciple Duty}
    {profiles : Action → GenEthActionProfile Action Feature Duty}
    (hno : ¬ ∃ a ∈ candidateSet.toFinset,
      dominatesAll principle profiles candidateSet.toFinset a) :
    (pairwiseResolveJudgmentComputable dutyDomain candidateSet principle profiles).status =
      ResolutionStatus.tied := by
  unfold pairwiseResolveJudgmentComputable
  simp [findDominantCandidate?_none_of_no_dominant hno]

-- ═══════════════════════════════════════════════════════════════════════════
-- Theory-guided resolver: filter by admissibility, then resolve
-- ═══════════════════════════════════════════════════════════════════════════

/-- Filter candidates to those admissible under a conflict discipline. -/
noncomputable def admissibleCandidates
    {World : Type u} {Agent : Type u} {Action : Type u}
    (discipline : ConflictDiscipline World)
    (problem : PracticalEthicalProblem World Agent Action)
    (candidates : Finset Action) : Finset Action :=
  candidates.filter fun a =>
    discipline.admissible problem.conflict.choicePoint (problem.actionFormula a)

/-- Every admissible candidate is a member of the original set. -/
theorem admissibleCandidates_subset
    {World : Type u} {Agent : Type u} {Action : Type u}
    (discipline : ConflictDiscipline World)
    (problem : PracticalEthicalProblem World Agent Action)
    (candidates : Finset Action) :
    admissibleCandidates discipline problem candidates ⊆ candidates :=
  Finset.filter_subset _ _

/-- Theory-guided resolver: filter by admissibility, then apply pairwise
resolution on the admissible subset.

This composes the top-down discipline (which actions are ethically permissible?)
with the bottom-up GenEth preference (which permissible action is best?). -/
noncomputable def theoryGuidedResolveJudgment
    [DecidableEq Action]
    {World : Type u} {Agent : Type u}
    (discipline : ConflictDiscipline World)
    (problem : PracticalEthicalProblem World Agent Action)
    (principle : GenEthPrinciple Duty)
    (profiles : Action → GenEthActionProfile Action Feature Duty)
    (candidates : Finset Action) : ResolutionJudgment Action :=
  pairwiseResolveJudgment principle profiles
    (admissibleCandidates discipline problem candidates)

/-- If a candidate dominates the admissible set, the theory-guided resolver
recommends it. -/
theorem theoryGuidedResolveJudgment_recommends_of_admissible_dominant
    [DecidableEq Action]
    {World : Type u} {Agent : Type u}
    {discipline : ConflictDiscipline World}
    {problem : PracticalEthicalProblem World Agent Action}
    {principle : GenEthPrinciple Duty}
    {profiles : Action → GenEthActionProfile Action Feature Duty}
    {candidates : Finset Action}
    (hexists : ∃ a ∈ admissibleCandidates discipline problem candidates,
      dominatesAll principle profiles
        (admissibleCandidates discipline problem candidates) a) :
    (theoryGuidedResolveJudgment discipline problem principle profiles
      candidates).status = .recommends := by
  exact pairwiseResolveJudgment_recommends_of_dominant hexists

/-- The theory-guided recommended candidate is genuinely dominant among
admissible candidates AND is itself admissible. -/
theorem theoryGuidedResolveJudgment_chosen_admissible_and_dominant
    [DecidableEq Action]
    {World : Type u} {Agent : Type u}
    {discipline : ConflictDiscipline World}
    {problem : PracticalEthicalProblem World Agent Action}
    {principle : GenEthPrinciple Duty}
    {profiles : Action → GenEthActionProfile Action Feature Duty}
    {candidates : Finset Action}
    (hexists : ∃ a ∈ admissibleCandidates discipline problem candidates,
      dominatesAll principle profiles
        (admissibleCandidates discipline problem candidates) a) :
    ∃ a, (theoryGuidedResolveJudgment discipline problem principle profiles
        candidates).Recommends a ∧
      a ∈ admissibleCandidates discipline problem candidates ∧
      dominatesAll principle profiles
        (admissibleCandidates discipline problem candidates) a := by
  rcases pairwiseResolveJudgment_chosen_dominates hexists with ⟨a, hrec, hdom⟩
  exact ⟨a, hrec, hdom.1, hdom⟩

/-- If no admissible candidate dominates, the resolver is tied. -/
theorem theoryGuidedResolveJudgment_tied_of_no_admissible_dominant
    [DecidableEq Action]
    {World : Type u} {Agent : Type u}
    {discipline : ConflictDiscipline World}
    {problem : PracticalEthicalProblem World Agent Action}
    {principle : GenEthPrinciple Duty}
    {profiles : Action → GenEthActionProfile Action Feature Duty}
    {candidates : Finset Action}
    (hno : ¬ ∃ a ∈ admissibleCandidates discipline problem candidates,
      dominatesAll principle profiles
        (admissibleCandidates discipline problem candidates) a) :
    (theoryGuidedResolveJudgment discipline problem principle profiles
      candidates).status = .tied := by
  exact pairwiseResolveJudgment_tied_of_no_dominant hno

-- ═══════════════════════════════════════════════════════════════════════════
-- Computable theory-guided resolver
-- ═══════════════════════════════════════════════════════════════════════════

/-- Computable admissible-candidate filter at the practical action seam. -/
def admissibleCandidateSetComputable
    {World : Type u} {Agent : Type u} {Action : Type u}
    {problem : PracticalEthicalProblem World Agent Action}
    (discipline : ComputableConflictDiscipline problem)
    (candidateSet : ExplicitFiniteSet Action) : ExplicitFiniteSet Action where
  elems := candidateSet.elems.filter discipline.admissibleAction
  nodup := candidateSet.nodup.filter _

@[simp] theorem mem_admissibleCandidateSetComputable_iff
    {World : Type u} {Agent : Type u} {Action : Type u}
    {problem : PracticalEthicalProblem World Agent Action}
    (discipline : ComputableConflictDiscipline problem)
    (candidateSet : ExplicitFiniteSet Action) (a : Action) :
    a ∈ (admissibleCandidateSetComputable discipline candidateSet).elems ↔
      a ∈ candidateSet.elems ∧
        discipline.toConflictDiscipline.admissible
          problem.conflict.choicePoint (problem.actionFormula a) := by
  simp [admissibleCandidateSetComputable, discipline.action_admissible_iff]

@[simp] theorem mem_admissibleCandidateSetComputable_toFinset_iff
    {World : Type u} {Agent : Type u} {Action : Type u}
    [DecidableEq Action]
    {problem : PracticalEthicalProblem World Agent Action}
    (discipline : ComputableConflictDiscipline problem)
    (candidateSet : ExplicitFiniteSet Action) (a : Action) :
    a ∈ (admissibleCandidateSetComputable discipline candidateSet).toFinset ↔
      a ∈ admissibleCandidates discipline.toConflictDiscipline problem candidateSet.toFinset := by
  simp [admissibleCandidates, mem_admissibleCandidateSetComputable_iff,
    ExplicitFiniteSet.mem_toFinset_iff]

/-- Computable theory-guided dominant-candidate search. -/
def theoryGuidedFindDominantCandidate?
    [DecidableEq Action]
    {World : Type u} {Agent : Type u}
    {problem : PracticalEthicalProblem World Agent Action}
    (discipline : ComputableConflictDiscipline problem)
    (dutyDomain : ExplicitFiniteDomain Duty)
    (candidateSet : ExplicitFiniteSet Action)
    (principle : GenEthPrinciple Duty)
    (profiles : Action → GenEthActionProfile Action Feature Duty) : Option Action :=
  findDominantCandidate? dutyDomain
    (admissibleCandidateSetComputable discipline candidateSet) principle profiles

/-- Computable theory-guided resolver: filter admissible actions by a boolean
companion, then run the explicit finite search. -/
def theoryGuidedResolveJudgmentComputable
    [DecidableEq Action]
    {World : Type u} {Agent : Type u}
    {problem : PracticalEthicalProblem World Agent Action}
    (discipline : ComputableConflictDiscipline problem)
    (dutyDomain : ExplicitFiniteDomain Duty)
    (candidateSet : ExplicitFiniteSet Action)
    (principle : GenEthPrinciple Duty)
    (profiles : Action → GenEthActionProfile Action Feature Duty) : ResolutionJudgment Action :=
  pairwiseResolveJudgmentComputable dutyDomain
    (admissibleCandidateSetComputable discipline candidateSet) principle profiles

theorem theoryGuidedResolveJudgmentComputable_chosen_admissible_and_dominant
    [DecidableEq Action]
    {World : Type u} {Agent : Type u}
    {problem : PracticalEthicalProblem World Agent Action}
    {discipline : ComputableConflictDiscipline problem}
    {dutyDomain : ExplicitFiniteDomain Duty}
    {candidateSet : ExplicitFiniteSet Action}
    {principle : GenEthPrinciple Duty}
    {profiles : Action → GenEthActionProfile Action Feature Duty}
    (hexists : ∃ a ∈ admissibleCandidates discipline.toConflictDiscipline problem candidateSet.toFinset,
      dominatesAll principle profiles
        (admissibleCandidates discipline.toConflictDiscipline problem candidateSet.toFinset) a) :
    ∃ a, (theoryGuidedResolveJudgmentComputable discipline dutyDomain candidateSet principle
        profiles).Recommends a ∧
      a ∈ admissibleCandidates discipline.toConflictDiscipline problem candidateSet.toFinset ∧
      dominatesAll principle profiles
        (admissibleCandidates discipline.toConflictDiscipline problem candidateSet.toFinset) a := by
  rcases hexists with ⟨a, ha, hdom⟩
  have hmemComp :
      a ∈ (admissibleCandidateSetComputable discipline candidateSet).toFinset := by
    exact (mem_admissibleCandidateSetComputable_toFinset_iff discipline candidateSet a).2 ha
  have hexistsComp :
      ∃ a ∈ (admissibleCandidateSetComputable discipline candidateSet).toFinset,
        dominatesAll principle profiles
          (admissibleCandidateSetComputable discipline candidateSet).toFinset a := by
    refine ⟨a, hmemComp, ?_⟩
    refine ⟨hmemComp, ?_⟩
    intro b hb hne
    have hbAd :
        b ∈ admissibleCandidates discipline.toConflictDiscipline problem candidateSet.toFinset := by
      exact (mem_admissibleCandidateSetComputable_toFinset_iff discipline candidateSet b).1 hb
    exact hdom.2 b hbAd hne
  rcases pairwiseResolveJudgmentComputable_chosen_dominates hexistsComp with
    ⟨a, hrec, hdomComp⟩
  have hmemAd :
      a ∈ admissibleCandidates discipline.toConflictDiscipline problem candidateSet.toFinset := by
    exact (mem_admissibleCandidateSetComputable_toFinset_iff discipline candidateSet a).1 hdomComp.1
  have hdomAd :
      dominatesAll principle profiles
        (admissibleCandidates discipline.toConflictDiscipline problem candidateSet.toFinset) a := by
    refine ⟨hmemAd, ?_⟩
    intro b hb hne
    have hbComp :
        b ∈ (admissibleCandidateSetComputable discipline candidateSet).toFinset := by
      exact (mem_admissibleCandidateSetComputable_toFinset_iff discipline candidateSet b).2 hb
    exact hdomComp.2 b hbComp hne
  exact ⟨a, hrec, hmemAd, hdomAd⟩

theorem theoryGuidedResolveJudgmentComputable_tied_of_no_admissible_dominant
    [DecidableEq Action]
    {World : Type u} {Agent : Type u}
    {problem : PracticalEthicalProblem World Agent Action}
    {discipline : ComputableConflictDiscipline problem}
    {dutyDomain : ExplicitFiniteDomain Duty}
    {candidateSet : ExplicitFiniteSet Action}
    {principle : GenEthPrinciple Duty}
    {profiles : Action → GenEthActionProfile Action Feature Duty}
    (hno : ¬ ∃ a ∈ admissibleCandidates discipline.toConflictDiscipline problem candidateSet.toFinset,
      dominatesAll principle profiles
        (admissibleCandidates discipline.toConflictDiscipline problem candidateSet.toFinset) a) :
    (theoryGuidedResolveJudgmentComputable discipline dutyDomain candidateSet principle
      profiles).status = ResolutionStatus.tied := by
  apply pairwiseResolveJudgmentComputable_tied_of_no_dominant
  intro hexists
  apply hno
  rcases hexists with ⟨a, ha, hdom⟩
  have haAd :
      a ∈ admissibleCandidates discipline.toConflictDiscipline problem candidateSet.toFinset := by
    exact (mem_admissibleCandidateSetComputable_toFinset_iff discipline candidateSet a).1 ha
  have hdomAd :
      dominatesAll principle profiles
        (admissibleCandidates discipline.toConflictDiscipline problem candidateSet.toFinset) a := by
    refine ⟨haAd, ?_⟩
    intro b hb hne
    have hbComp :
        b ∈ (admissibleCandidateSetComputable discipline candidateSet).toFinset := by
      exact (mem_admissibleCandidateSetComputable_toFinset_iff discipline candidateSet b).2 hb
    exact hdom.2 b hbComp hne
  exact ⟨a, haAd, hdomAd⟩

end Mettapedia.CognitiveArchitecture.GodelClaw.Ethics
