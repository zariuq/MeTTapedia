import Mettapedia.GSLT.ProofPlans.Derivations
import Mettapedia.TypeTheory.Authority

/-!
# Budgeted plan search

Plan search completes a plan by backward chaining: to discharge an obligation
it tries the rules of a finite library whose conclusion is the obligation and
recursively discharges their premises, within a depth budget (`search`).  Its
answer is an authority outcome (`AuthorityTheory.Outcome`):

* **established**, with a completion of the plan;
* **refuted**, with a checked obstruction: a refutation of one obligation,
  produced by an independent refuter such as a countermodel;
* **incomplete**, with the budget spent, when the search found nothing and
  the refuter certified nothing.

**Backward chaining is complete for its library**: a goal with a derivation
built from library rules within depth `n` is found at budget `n`
(`search_complete`).  So exhaustion at budget `n` certifies only that no
library derivation of depth at most `n` exists (`exhausted_no_shallow_evidence`),
which is not a refutation.  A ranking of the candidates changes which
derivation is found and never whether one is found (`search_isSome_perm`).

**Exhaustion is incomplete, never refuted.**  Without a refutation of some
obligation, the verdict is never `refuted`, at any budget
(`verdict_not_refuted`).  Each verdict is sound: an established verdict
carries a completion and a refuted verdict leaves the plan without
completions (`verdict_refuted_sound`).  Raising the budget refines the verdict
along the budget axis: established and refuted verdicts persist, and an
incomplete verdict may resolve (`verdict_budgetRefines`).

**Controls** (in the fixture kernel).
* The plan that assumes `C` is incomplete at budget `1` and established at
  budget `2` (`assumeC_incomplete_one`, `assumeC_established_two`).
* Treating exhaustion as refutation is unsound: the naive search refutes that
  plan at budget `1`, although it has a completion
  (`naive_refutation_unsound`).
* With the countermodel refuter, the plan `xc(?X)` is refuted at every budget
  (`planXC_refuted`); with a refuter that knows nothing about `CastCG`, the
  bypass plan is incomplete at every budget (`bypass_incomplete`).
* Reversing the library finds `axB` instead of `ab(axA₁)` for `B`, with the
  same status at every budget (`ranking_changes_provenance`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProofPlans.Search

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.TypeTheory.AuthorityTheory

/-! ## Backward chaining -/

/-- A checked rule application available to backward chaining. -/
structure Candidate (definition : ValidatedCalculusLanguageDef) where
  ruleInstance : RuleInstance
  premises : List Pattern
  conclusion : Pattern
  application : RuleApplication definition ruleInstance premises conclusion

variable {definition : ValidatedCalculusLanguageDef}

/-- Discharge an ordered list of judgments with a sub-search. -/
def searchPremises (subsearch : (goal : Pattern) → Option (Derivation definition goal)) :
    (premises : List Pattern) → Option (DerivationList definition premises)
  | [] => some .nil
  | premise :: premises =>
      match subsearch premise, searchPremises subsearch premises with
      | some head, some tail => some (.cons head tail)
      | _, _ => none

/-- Try one candidate rule against a goal. -/
def tryCandidate (subsearch : (goal : Pattern) → Option (Derivation definition goal))
    (goal : Pattern) (candidate : Candidate definition) : Option (Derivation definition goal) :=
  if concludes : candidate.conclusion = goal then
    (searchPremises subsearch candidate.premises).map fun children =>
      concludes ▸ Derivation.byRule candidate.ruleInstance candidate.application children
  else
    none

/-- **Backward chaining with a depth budget.** -/
def search (library : List (Candidate definition)) :
    ℕ → (goal : Pattern) → Option (Derivation definition goal)
  | 0, _ => none
  | fuel + 1, goal => library.findSome? (tryCandidate (search library fuel) goal)

theorem searchPremises_isSome_mono
    {first second : (goal : Pattern) → Option (Derivation definition goal)}
    (mono : ∀ goal, (first goal).isSome → (second goal).isSome) :
    ∀ premises, (searchPremises first premises).isSome →
      (searchPremises second premises).isSome
  | [], _ => rfl
  | premise :: premises, found => by
      simp only [searchPremises] at found ⊢
      cases firstHead : first premise with
      | none => simp [firstHead] at found
      | some head =>
          cases firstTail : searchPremises first premises with
          | none => simp [firstHead, firstTail] at found
          | some tail =>
              have secondHead := mono premise (by simp [firstHead])
              have secondTail := searchPremises_isSome_mono mono premises (by simp [firstTail])
              obtain ⟨head', found'⟩ := Option.isSome_iff_exists.mp secondHead
              obtain ⟨tail', foundTail'⟩ := Option.isSome_iff_exists.mp secondTail
              simp [found', foundTail']

/-- **More budget never loses a derivation.** -/
theorem search_isSome_succ (library : List (Candidate definition)) :
    ∀ fuel goal, (search library fuel goal).isSome → (search library (fuel + 1) goal).isSome
  | 0, _, found => by simp [search] at found
  | fuel + 1, goal, found => by
      simp only [search, List.findSome?_isSome_iff] at found ⊢
      obtain ⟨candidate, member, tried⟩ := found
      refine ⟨candidate, member, ?_⟩
      unfold tryCandidate at tried ⊢
      by_cases concludes : candidate.conclusion = goal
      · simp only [concludes, dif_pos, Option.isSome_map] at tried ⊢
        exact searchPremises_isSome_mono (search_isSome_succ library fuel) _ tried
      · simp [concludes] at tried

theorem search_isSome_mono (library : List (Candidate definition)) {fuel fuel' : ℕ}
    (bounded : fuel ≤ fuel') (goal : Pattern) (found : (search library fuel goal).isSome) :
    (search library fuel' goal).isSome := by
  induction bounded with
  | refl => exact found
  | step _ inductionHypothesis => exact search_isSome_succ library _ goal inductionHypothesis

/-! ## Completeness and the meaning of exhaustion -/

mutual

/-- A derivation built from library candidates within a depth. -/
inductive WithinLibrary (library : List (Candidate definition)) :
    ℕ → {goal : Pattern} → Derivation definition goal → Prop
  | node {fuel : ℕ} {ruleInstance : RuleInstance} {premises : List Pattern} {goal : Pattern}
      {application : RuleApplication definition ruleInstance premises goal}
      {children : DerivationList definition premises}
      (candidate : Candidate definition) (member : candidate ∈ library)
      (samePremises : candidate.premises = premises) (sameConclusion : candidate.conclusion = goal)
      (inside : WithinLibraryList library fuel children) :
      WithinLibrary library (fuel + 1) (.byRule ruleInstance application children)

/-- Ordered derivations built from library candidates within a depth. -/
inductive WithinLibraryList (library : List (Candidate definition)) :
    ℕ → {goals : List Pattern} → DerivationList definition goals → Prop
  | nil {fuel : ℕ} : WithinLibraryList library fuel .nil
  | cons {fuel : ℕ} {premise : Pattern} {premises : List Pattern}
      {head : Derivation definition premise} {tail : DerivationList definition premises} :
      WithinLibrary library fuel head → WithinLibraryList library fuel tail →
        WithinLibraryList library fuel (.cons head tail)

end

mutual

/-- **Completeness of backward chaining**: a goal with a derivation built from
the library within depth `fuel` is found at budget `fuel`. -/
theorem search_complete (library : List (Candidate definition)) :
    {fuel : ℕ} → {goal : Pattern} → (derivation : Derivation definition goal) →
      WithinLibrary library fuel derivation → (search library fuel goal).isSome
  | _, _, .byRule _ _ children, within => by
      cases within with
      | node candidate member samePremises sameConclusion inside =>
          simp only [search, List.findSome?_isSome_iff]
          refine ⟨candidate, member, ?_⟩
          unfold tryCandidate
          simp only [sameConclusion, dif_pos, Option.isSome_map]
          subst samePremises
          exact searchPremises_complete library children inside

/-- Pointwise form. -/
theorem searchPremises_complete (library : List (Candidate definition)) :
    {fuel : ℕ} → {goals : List Pattern} → (derivations : DerivationList definition goals) →
      WithinLibraryList library fuel derivations →
        (searchPremises (search library fuel) goals).isSome
  | _, _, .nil, _ => rfl
  | _, _, .cons head tail, within => by
      cases within with
      | cons headWithin tailWithin =>
          have headFound := search_complete library head headWithin
          have tailFound := searchPremises_complete library tail tailWithin
          obtain ⟨headDerivation, headEq⟩ := Option.isSome_iff_exists.mp headFound
          obtain ⟨tailDerivations, tailEq⟩ := Option.isSome_iff_exists.mp tailFound
          simp [searchPremises, headEq, tailEq]

end

/-- **What exhaustion certifies**: when search fails at a budget, no evidence
for the obligations is built from the library within that depth.  This is not
a refutation: a deeper derivation, or one using other rules, may exist. -/
theorem exhausted_no_shallow_evidence (library : List (Candidate definition)) {fuel : ℕ}
    {goals : List Pattern} (failed : searchPremises (search library fuel) goals = none)
    (evidence : DerivationList definition goals) :
    ¬ WithinLibraryList library fuel evidence := by
  intro within
  have found := searchPremises_complete library evidence within
  rw [failed] at found
  exact absurd found (by simp)

/-! ## Ranking guides search; it does not change what is found -/

theorem searchPremises_isSome_congr
    {first second : (goal : Pattern) → Option (Derivation definition goal)}
    (same : ∀ goal, (first goal).isSome = (second goal).isSome) :
    ∀ premises, (searchPremises first premises).isSome = (searchPremises second premises).isSome :=
  fun premises => Bool.eq_iff_iff.mpr
    ⟨searchPremises_isSome_mono (fun goal found => (same goal) ▸ found) premises,
      searchPremises_isSome_mono (fun goal found => (same goal).symm ▸ found) premises⟩

/-- **Reordering the candidates (a ranking) never changes whether a goal is
found**, only which derivation is found. -/
theorem search_isSome_perm {library library' : List (Candidate definition)}
    (permuted : library.Perm library') :
    ∀ fuel goal, (search library fuel goal).isSome = (search library' fuel goal).isSome
  | 0, _ => rfl
  | fuel + 1, goal => by
      simp only [search]
      apply Bool.eq_iff_iff.mpr
      simp only [List.findSome?_isSome_iff]
      have congr : ∀ candidate : Candidate definition,
          (tryCandidate (search library fuel) goal candidate).isSome =
            (tryCandidate (search library' fuel) goal candidate).isSome := by
        intro candidate
        unfold tryCandidate
        by_cases concludes : candidate.conclusion = goal
        · simp only [concludes, dif_pos, Option.isSome_map]
          exact searchPremises_isSome_congr (search_isSome_perm permuted fuel) _
        · simp [concludes]
      constructor
      · rintro ⟨candidate, member, found⟩
        exact ⟨candidate, permuted.mem_iff.mp member, (congr candidate) ▸ found⟩
      · rintro ⟨candidate, member, found⟩
        exact ⟨candidate, permuted.mem_iff.mpr member, (congr candidate).symm ▸ found⟩

/-! ## Plan verdicts -/

/-- A refuter certifies, for some judgments, that they have no derivation. -/
abbrev Refuter (definition : ValidatedCalculusLanguageDef) : Type :=
  (judgment : Pattern) → Option (PLift (Derivation definition judgment → False))

variable {object : Object}

/-- A refuted obligation of a plan, if the refuter certifies one. -/
def refutedObligation (refuter : Refuter object.definition) {goal : Pattern}
    (plan : DerivationPlan object goal) :
    Option (Σ index : Fin plan.obligations.length,
      PLift (Derivation object.definition (plan.obligations.get index) → False)) :=
  (List.finRange plan.obligations.length).findSome? fun index =>
    (refuter (plan.obligations.get index)).map fun refutation => ⟨index, refutation⟩

/-- The completions of a plan, as closed derivations: discharges of its
obligations (`mem_completions_iff_discharge`). -/
abbrev Completion {goal : Pattern} (plan : DerivationPlan object goal) : Type :=
  { completion : Derivation object.definition goal //
    ∃ evidence : DerivationList object.definition plan.obligations,
      plan.derivation.discharge evidence = completion }

/-- A plan without completions. -/
abbrev NoCompletion {goal : Pattern} (plan : DerivationPlan object goal) : Prop :=
  ∀ completion : Derivation object.definition goal,
    ¬ ∃ evidence : DerivationList object.definition plan.obligations,
      plan.derivation.discharge evidence = completion

/-- The verdict type of plan search: a completion, a proof that none exists,
or the budget spent.  The search never abstains, so its boundary type is
empty. -/
abbrev Verdict {goal : Pattern} (plan : DerivationPlan object goal) : Type 1 :=
  Outcome (Completion plan) (NoCompletion plan) Empty ℕ

/-- A completion of the verdict is a member of the plan's completion space. -/
theorem completion_mem {goal : Pattern} {plan : DerivationPlan object goal}
    (completion : Completion plan) :
    OpenDerivation.ofClosed completion.1 ∈ completions (derivationClone object) plan :=
  (mem_completions_iff_discharge plan completion.1).mpr completion.2

/-- A plan without completions has an empty completion space. -/
theorem noCompletion_empty {goal : Pattern} {plan : DerivationPlan object goal}
    (empty : NoCompletion plan) :
    ∀ completion, completion ∉ completions (derivationClone object) plan := by
  intro completion member
  rw [completion_eq_ofClosed completion] at member
  exact empty _ ((mem_completions_iff_discharge plan _).mp member)

/-- A refuted obligation leaves no completion. -/
theorem noCompletion_of_refuted {goal : Pattern} (plan : DerivationPlan object goal)
    (index : Fin plan.obligations.length)
    (refutation : Derivation object.definition (plan.obligations.get index) → False) :
    NoCompletion plan := by
  rintro completion ⟨evidence, _⟩
  exact refutation ((OpenDerivationList.ofClosed (context := []) evidence).get index).close

/-- **The verdict of budgeted plan search.** -/
def planVerdict (library : List (Candidate object.definition))
    (refuter : Refuter object.definition) {goal : Pattern}
    (plan : DerivationPlan object goal) (fuel : ℕ) : Verdict plan :=
  match searchPremises (search library fuel) plan.obligations with
  | some evidence => .established ⟨plan.derivation.discharge evidence, evidence, rfl⟩
  | none =>
      match refutedObligation refuter plan with
      | some ⟨index, refutation⟩ =>
          .refuted (noCompletion_of_refuted plan index refutation.down)
      | none => .incomplete fuel

variable (library : List (Candidate object.definition)) (refuter : Refuter object.definition)

/-- An established verdict carries a completion. -/
theorem verdict_established_sound {goal : Pattern} (plan : DerivationPlan object goal)
    (fuel : ℕ) (completion : Completion plan)
    (_verdict : planVerdict library refuter plan fuel = .established completion) :
    OpenDerivation.ofClosed completion.1 ∈ completions (derivationClone object) plan :=
  completion_mem completion

/-- **A refuted verdict leaves the plan without completions.** -/
theorem verdict_refuted_sound {goal : Pattern} (plan : DerivationPlan object goal)
    (fuel : ℕ) (obstruction : NoCompletion plan)
    (_verdict : planVerdict library refuter plan fuel = .refuted obstruction) :
    ∀ completion, completion ∉ completions (derivationClone object) plan :=
  noCompletion_empty obstruction

/-- **Exhaustion is incomplete, never refuted.**  If the refuter certifies no
obligation of the plan, the verdict is not `refuted` at any budget; when the
search also fails, the verdict is `incomplete`. -/
theorem verdict_not_refuted {goal : Pattern} (plan : DerivationPlan object goal)
    (silent : refutedObligation refuter plan = none) (fuel : ℕ) :
    (∀ obstruction, planVerdict library refuter plan fuel ≠ .refuted obstruction) ∧
      (searchPremises (search library fuel) plan.obligations = none →
        planVerdict library refuter plan fuel = .incomplete fuel) := by
  constructor
  · intro obstruction verdict
    unfold planVerdict at verdict
    cases found : searchPremises (search library fuel) plan.obligations with
    | some evidence => simp [found] at verdict
    | none => simp [found, silent] at verdict
  · intro failed
    unfold planVerdict
    simp [failed, silent]

/-- A failed search with a certified obligation gives a refuted verdict. -/
theorem publicStatus_refuted_of {goal : Pattern} (plan : DerivationPlan object goal)
    (fuel : ℕ) (failed : searchPremises (search library fuel) plan.obligations = none)
    (certified : (refutedObligation refuter plan).isSome) :
    (planVerdict library refuter plan fuel).publicStatus = .refuted := by
  unfold planVerdict
  split
  · rename_i found
    rw [failed] at found
    exact absurd found (by simp)
  · split
    · rfl
    · rename_i silent
      rw [silent] at certified
      exact absurd certified (by simp)

/-- **Raising the budget refines the verdict** along the budget axis. -/
theorem verdict_budgetRefines {goal : Pattern} (plan : DerivationPlan object goal)
    {fuel fuel' : ℕ} (bounded : fuel ≤ fuel') :
    Outcome.BudgetRefines (planVerdict library refuter plan fuel)
      (planVerdict library refuter plan fuel') := by
  have mono := fun goal => search_isSome_mono library bounded goal
  unfold planVerdict
  cases found : searchPremises (search library fuel) plan.obligations with
  | some evidence =>
      have found' := searchPremises_isSome_mono mono plan.obligations (by simp [found])
      obtain ⟨evidence', found''⟩ := Option.isSome_iff_exists.mp found'
      simp only [found'']
      exact .established _ _
  | none =>
      cases refuted : refutedObligation refuter plan with
      | some witness =>
          obtain ⟨index, refutation⟩ := witness
          cases found' : searchPremises (search library fuel') plan.obligations with
          | some evidence' =>
              exact absurd ⟨evidence', rfl⟩
                (noCompletion_of_refuted plan index refutation.down (plan.derivation.discharge evidence'))
          | none =>
              simp only
              exact .refuted _ _
      | none =>
          cases found' : searchPremises (search library fuel') plan.obligations with
          | some evidence' =>
              simp only
              exact .incompleteEstablished _ _
          | none =>
              simp only
              exact .incomplete _ _

/-! ## Controls -/

namespace Controls

open Fixture

/-- The kernel rules as backward-chaining candidates. -/
def kernelLibrary : List (Candidate kernel.definition) :=
  [⟨_, _, _, kernelApp (rule := ruleAxA₁) (by simp [kernelRules])⟩,
    ⟨_, _, _, kernelApp (rule := ruleAxA₂) (by simp [kernelRules])⟩,
    ⟨_, _, _, kernelApp (rule := ruleAB) (by simp [kernelRules])⟩,
    ⟨_, _, _, kernelApp (rule := ruleAxB) (by simp [kernelRules])⟩,
    ⟨_, _, _, kernelApp (rule := ruleBC) (by simp [kernelRules])⟩,
    ⟨_, _, _, kernelApp (rule := ruleXC) (by simp [kernelRules])⟩]

/-- The kernel library in the reverse order. -/
def reversedLibrary : List (Candidate kernel.definition) := kernelLibrary.reverse

/-- The rule at the root of a derivation. -/
def rootId {goal : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern} :
    Derivation kernel.definition goal → RuleId
  | .byRule ruleInstance _ _ => ruleInstance.ruleId

/-- **A ranking changes which derivation is found, never whether one is.**
Searching `B` at budget `2` finds `ab(axA₁)` with the kernel order and `axB`
with the reverse order. -/
theorem ranking_changes_provenance :
    (search kernelLibrary 2 B).map rootId = some ruleAB.id ∧
      (search reversedLibrary 2 B).map rootId = some ruleAxB.id ∧
      ∀ fuel goal, (search kernelLibrary fuel goal).isSome =
        (search reversedLibrary fuel goal).isSome :=
  ⟨by decide, by decide, search_isSome_perm (List.reverse_perm kernelLibrary).symm⟩

/-- The countermodel refuter: a judgment false in the kernel truth assignment
has no derivation. -/
def countermodelRefuter : Refuter kernel.definition := fun judgment =>
  if holds : kernelTruth judgment then none
  else some ⟨fun derivation => holds (derivation_truth derivation)⟩

/-- The refuter that certifies nothing. -/
def silentRefuter : Refuter kernel.definition := fun _ => none

/-- A refuter that knows only that `X` is underivable. -/
def xRefuter : Refuter kernel.definition := fun judgment =>
  if isX : judgment = X then some ⟨fun derivation => no_derivation_X (isX ▸ derivation)⟩
  else none

/-- The plan that assumes `C`. -/
abbrev assumeC : DerivationPlan kernel C := Plan.assume _ C

theorem assumeC_search_one : searchPremises (search kernelLibrary 1) assumeC.obligations = none := by
  decide

theorem assumeC_incomplete_one :
    planVerdict kernelLibrary countermodelRefuter assumeC 1 = .incomplete 1 := by
  unfold planVerdict
  rw [assumeC_search_one]
  rfl

/-- **Positive.**  With budget `2`, backward chaining finds `bc(axB)`. -/
theorem assumeC_established_two :
    (planVerdict kernelLibrary countermodelRefuter assumeC 2).publicStatus = .established := by
  decide

/-- The naive status: exhaustion reported as refutation. -/
def naiveStatus {goal : Pattern} (plan : DerivationPlan kernel goal) (fuel : ℕ) :
    Outcome.PublicStatus :=
  if (searchPremises (search kernelLibrary fuel) plan.obligations).isSome then .established
  else .refuted

/-- **Negative control.**  The naive search refutes the plan that assumes `C`
at budget `1`, though that plan has a completion. -/
theorem naive_refutation_unsound :
    naiveStatus assumeC 1 = .refuted ∧
      (completions (derivationClone kernel) assumeC).Nonempty := by
  refine ⟨by decide, ⟨_, mem_completions_assume (OpenDerivation.ofClosed dC)⟩⟩

/-- **Positive.**  With the countermodel refuter, `xc(?X)` is refuted at every
budget. -/
theorem planXC_refuted (fuel : ℕ) :
    (planVerdict kernelLibrary countermodelRefuter (ofOpen planXC) fuel).publicStatus =
      .refuted := by
  apply publicStatus_refuted_of
  · cases found : searchPremises (search kernelLibrary fuel) (ofOpen planXC).obligations with
    | none => exact found
    | some evidence =>
        exact absurd (discharge_mem_completions (ofOpen planXC) evidence)
          (PlanControls.planXC_no_completion _)
  · decide

/-- **Negative.**  With a refuter that knows only `X`, the bypass plan, whose
obligation `CastCG` is false, is incomplete at every budget: its failure is
reported as exhaustion, never as a refutation. -/
theorem bypass_incomplete (fuel : ℕ) :
    planVerdict kernelLibrary xRefuter (ofOpen planBypass) fuel = .incomplete fuel := by
  have noEvidence : searchPremises (search kernelLibrary fuel) (ofOpen planBypass).obligations =
      none := by
    cases found : searchPremises (search kernelLibrary fuel) (ofOpen planBypass).obligations with
    | none => rfl
    | some evidence =>
        cases evidence with
        | cons castEvidence _ => exact (no_derivation_castCG castEvidence).elim
  have silent : refutedObligation xRefuter (ofOpen planBypass) = none := by decide
  exact (verdict_not_refuted kernelLibrary xRefuter (ofOpen planBypass) silent fuel).2 noEvidence

end Controls

end Mettapedia.GSLT.ProofPlans.Search
