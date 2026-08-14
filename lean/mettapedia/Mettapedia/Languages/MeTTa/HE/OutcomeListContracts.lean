/-
# HE typing: outcome algebra and collection contracts (executable spec)

Theory-first specification for the HE typing interface, grounded in the live
engine's declared API: the four-valued check status (Established / Refuted /
Undetermined / Incomplete), the seven-valued normalization status, the five
list-valued type-inference operations (profiled, transient, budgeted,
structural, structural-budgeted), and the budget ledger whose documentation
already states one law this file makes formal: bounded producers may report
exhaustion, but exhaustion is never a refutation.

Sealed here (the laws any implementation answer must satisfy):

1. the outcome algebra with **budget-stability**: established, refuted, and
   genuinely undetermined outcomes are stable under budget increase; only an
   incomplete result may be revised by spending more budget.  Soundness is a
   separate law: exhaustion may never fabricate either semantic verdict;
2. the collection-contract vocabulary for list-valued inference (order,
   multiplicity, budget-completeness, memo publication) with each field's
   optimization LICENSE stated, plus the completed census of all five live
   operations;
3. search-as-strategy: search outcomes are either a complete witness sequence
   or incomplete — there is **no refutation constructor**, so silence proves
   nothing by construction.  A complete empty sequence is the separate,
   exhaustive negative case.
-/
import Mathlib.Data.List.Dedup
import Mathlib.Order.Basic

namespace Mettapedia.Languages.MeTTa.HE.OutcomeListContracts

/-! ## §1 The outcome algebra and budget stability -/

/-- The exhaustion kinds carried by the live budget ledger. -/
inductive ExhaustionKind where
  | resource | depth | typeCapacity | evaluatorStack | evaluatorCapacity
  deriving DecidableEq, Repr

/-- The four-valued check outcome, matching the live engine's status
vocabulary, with incompleteness carrying its exhaustion kind. -/
inductive CheckOutcome where
  | established
  | refuted
  | undetermined
  | incomplete (why : ExhaustionKind)
  deriving DecidableEq, Repr

/-- A lawful budgeted judgment: semantic verdicts are budget-stable, and
verdicts are semantically sound.  The stability laws ARE the
exhaustion-never-refutes discipline: an outcome that varies with budget
cannot be a semantic verdict. -/
structure BudgetedJudgment (Claim : Type) (Meaning : Claim → Prop) where
  run : Claim → Nat → CheckOutcome
  established_stable : ∀ c b b', run c b = .established → b ≤ b' →
    run c b' = .established
  refuted_stable : ∀ c b b', run c b = .refuted → b ≤ b' →
    run c b' = .refuted
  undetermined_stable : ∀ c b b', run c b = .undetermined → b ≤ b' →
    run c b' = .undetermined
  established_sound : ∀ c b, run c b = .established → Meaning c
  refuted_sound : ∀ c b, run c b = .refuted → ¬ Meaning c

/-! ### Positive witness: a lawful fuel-bounded judgment -/

/-- Toy: decide `n % 2 = 0` with fuel; insufficient fuel reports resource
incompleteness — never a verdict. -/
def toyRun (n : Nat) (b : Nat) : CheckOutcome :=
  if n ≤ b then (if n % 2 = 0 then .established else .refuted)
  else .incomplete .resource

def toyJudgment : BudgetedJudgment Nat (fun n => n % 2 = 0) where
  run := toyRun
  established_stable := by
    intro c b b' h hle
    unfold toyRun at h ⊢
    split at h
    · split at h
      · simp_all [Nat.le_trans ‹c ≤ b› hle]
      · simp_all
    · simp_all
  refuted_stable := by
    intro c b b' h hle
    unfold toyRun at h ⊢
    split at h
    · split at h
      · simp_all
      · simp_all [Nat.le_trans ‹c ≤ b› hle]
    · simp_all
  undetermined_stable := by
    intro c b b' h _
    unfold toyRun at h
    split at h
    · split at h <;> cases h
    · cases h
  established_sound := by
    intro c b h
    unfold toyRun at h
    split at h
    · split at h
      · assumption
      · simp_all
    · simp_all
  refuted_sound := by
    intro c b h
    unfold toyRun at h
    split at h
    · split at h
      · simp_all
      · simp_all
    · simp_all

/-- The toy is genuinely three-moded: verdicts at sufficient fuel,
incompleteness below it. -/
example : toyRun 4 10 = .established := by decide
example : toyRun 3 10 = .refuted := by decide
example : toyRun 4 2 = .incomplete .resource := by decide

/-! ### Negative witnesses: soundness and stability are independent -/

/-- The bad implementation which calls budget exhaustion a refutation. -/
def exhaustionRefutingRun (n : Nat) (b : Nat) : CheckOutcome :=
  if n ≤ b then .established else .refuted

/-- Refuting a true claim merely because fuel ran out violates soundness. -/
theorem exhaustionRefutingRun_unlawful :
    ¬ ∃ j : BudgetedJudgment Nat (fun _ => True),
      j.run = exhaustionRefutingRun := by
  rintro ⟨j, hj⟩
  exact j.refuted_sound 5 0 (by simp [hj, exhaustionRefutingRun]) trivial

/-- A second bad implementation returns a sound verdict at budget zero, then
regresses to incomplete when given more budget.  It isolates the stability
law from semantic soundness. -/
def verdictRegressingRun (claim : Bool) (budget : Nat) : CheckOutcome :=
  if budget = 0 then
    if claim then .established else .refuted
  else
    .incomplete .resource

theorem verdictRegressingRun_unlawful :
    ¬ ∃ j : BudgetedJudgment Bool (fun claim => claim = true),
      j.run = verdictRegressingRun := by
  rintro ⟨j, hj⟩
  have stable := j.established_stable true 0 1
    (by simp [hj, verdictRegressingRun]) (by omega)
  simp [hj, verdictRegressingRun] at stable

/-! ## §2 Normalization outcomes: the seven-valued partition -/

/-- The live normalization statuses, partitioned by class.  Resource and
depth are exhaustion (budget-sensitive); the rest are semantic verdicts or
the explicitly provisional state. -/
inductive NormalizeOutcome (Ty : Type) where
  | complete (normalForm : Ty)
  | ambiguous
  | noResult
  | inadmissible
  | provisional
  | exhausted (why : ExhaustionKind)

/-- The class partition: exactly the `exhausted` outcomes are
budget-sensitive; every other outcome must be budget-stable.  Authored
langdef rules must never map an `exhausted` outcome to a semantic
verdict. -/
def NormalizeOutcome.isExhaustion {Ty : Type} : NormalizeOutcome Ty → Bool
  | .exhausted _ => true
  | _ => false

/-- Budget stability for normalization is a law, not a consequence of the
seven constructor names.  A completed normal form, ambiguity, no-result,
inadmissibility, or provisionality may not change merely because the caller
offered more fuel.  Only `exhausted` may later refine to another outcome. -/
structure BudgetedNormalization (Claim Ty : Type) where
  run : Claim → Nat → NormalizeOutcome Ty
  nonexhausted_stable : ∀ claim budget larger outcome,
    run claim budget = outcome →
    outcome.isExhaustion = false →
    budget ≤ larger →
    run claim larger = outcome

def toyNormalizeRun (claim budget : Nat) : NormalizeOutcome Nat :=
  if claim ≤ budget then .complete claim else .exhausted .resource

def toyNormalization : BudgetedNormalization Nat Nat where
  run := toyNormalizeRun
  nonexhausted_stable := by
    intro claim budget larger outcome result nonexhausted grows
    unfold toyNormalizeRun at result ⊢
    split at result
    · next enough =>
      cases result
      simp [Nat.le_trans enough grows]
    · next insufficient =>
      cases result
      simp [NormalizeOutcome.isExhaustion] at nonexhausted

def normalizationRegressingRun (claim budget : Nat) : NormalizeOutcome Nat :=
  if budget = 0 then .complete claim else .exhausted .resource

theorem normalizationRegressingRun_unlawful :
    ¬ ∃ normalizer : BudgetedNormalization Nat Nat,
      normalizer.run = normalizationRegressingRun := by
  rintro ⟨normalizer, runEq⟩
  have stable := normalizer.nonexhausted_stable 7 0 1 (.complete 7)
    (by simp [runEq, normalizationRegressingRun]) (by decide) (by omega)
  simp [runEq, normalizationRegressingRun] at stable

/-! ## §3 Collection contracts for list-valued inference -/

/-- The contract vocabulary for a list-valued inference operation.  Each
field is simultaneously a semantic declaration and an optimization license:

* `orderSemantic = false`   licenses REORDERING (results modulo permutation);
* `multiplicitySemantic = false` licenses DEDUPLICATION;
* `unboundedComplete = true` states the unbounded form enumerates ALL
  solutions (licensing negative caching: absence from the list is
  refutation-grade);
* `memoPublishes`           records whether the operation publishes to the
  persistent memo (the profiled/transient distinction, documented fact). -/
structure CollectionContract where
  orderSemantic : Bool
  multiplicitySemantic : Bool
  unboundedComplete : Bool
  memoPublishes : Bool
  deriving DecidableEq, Repr

/-- The observation induced by the two collection-policy bits.  All four
combinations have content: exact sequence, bag up to permutation, ordered
first-occurrence set, or unordered set. -/
def CollectionEquivalent [DecidableEq Ty] (contract : CollectionContract)
    (left right : List Ty) : Prop :=
  match contract.orderSemantic, contract.multiplicitySemantic with
  | true, true => left = right
  | false, true => left.Perm right
  | true, false => left.dedup = right.dedup
  | false, false => ∀ value, value ∈ left ↔ value ∈ right

theorem CollectionEquivalent.mem_iff [DecidableEq Ty]
    {contract : CollectionContract} {left right : List Ty}
    (equivalent : CollectionEquivalent contract left right) (value : Ty) :
    value ∈ left ↔ value ∈ right := by
  rcases contract with ⟨order, multiplicity, complete, memo⟩
  cases order <;> cases multiplicity
  · exact equivalent value
  · exact List.Perm.mem_iff equivalent
  · constructor
    · intro member
      have dedupMember : value ∈ left.dedup := List.mem_dedup.2 member
      rw [equivalent] at dedupMember
      exact List.mem_dedup.1 dedupMember
    · intro member
      have dedupMember : value ∈ right.dedup := List.mem_dedup.2 member
      rw [← equivalent] at dedupMember
      exact List.mem_dedup.1 dedupMember
  · subst right
    rfl

/-- When order is declared nonsemantic, a permutation is observationally
free.  This is the actual reordering license promised by the contract bit. -/
theorem permutation_licensed [DecidableEq Ty]
    {contract : CollectionContract} (orderFree : contract.orderSemantic = false)
    {left right : List Ty} (permutation : left.Perm right) :
    CollectionEquivalent contract left right := by
  rcases contract with ⟨order, multiplicity, complete, memo⟩
  cases order <;> cases multiplicity
  · exact fun value => permutation.mem_iff
  · exact permutation
  · cases orderFree
  · cases orderFree

/-- When multiplicity is declared nonsemantic, first-occurrence
deduplication is observationally free. -/
theorem deduplication_licensed [DecidableEq Ty]
    {contract : CollectionContract}
    (multiplicityFree : contract.multiplicitySemantic = false)
    (values : List Ty) :
    CollectionEquivalent contract values values.dedup := by
  rcases contract with ⟨order, multiplicity, complete, memo⟩
  cases order <;> cases multiplicity <;>
    simp_all [CollectionEquivalent]

/-- An abstract list-valued inference operation with its ideal semantics:
`ideal` is the mathematically intended solution collection; the laws relate
what the implementation returns to that ideal.  `sound` always; `complete`
only where the contract claims it.  The budgeted form returns a sound
sub-collection, and its Boolean is a completion flag: `true` licenses treating
that collection as equivalent to the ordinary implementation result. -/
structure ListInferenceSpec (Space Atom Ty : Type) [DecidableEq Ty] where
  contract : CollectionContract
  ideal : Space → Atom → List Ty
  infer : Space → Atom → List Ty
  inferBudgeted : Space → Atom → Nat → List Ty × Bool
  sound : ∀ s a t, t ∈ infer s a → t ∈ ideal s a
  complete : contract.unboundedComplete = true →
    ∀ s a, CollectionEquivalent contract (infer s a) (ideal s a)
  budgeted_sound : ∀ s a b t,
    t ∈ (inferBudgeted s a b).1 → t ∈ ideal s a
  budgeted_complete : ∀ s a b,
    (inferBudgeted s a b).2 = true →
    CollectionEquivalent contract (inferBudgeted s a b).1 (infer s a)

theorem ListInferenceSpec.missing_unbounded_forces_incomplete
    [DecidableEq Ty] (spec : ListInferenceSpec Space Atom Ty)
    {space : Space} {atom : Atom} {budget : Nat} {value : Ty}
    (inUnbounded : value ∈ spec.infer space atom)
    (missing : value ∉ (spec.inferBudgeted space atom budget).1) :
    (spec.inferBudgeted space atom budget).2 = false := by
  rw [Bool.eq_false_iff]
  intro complete
  have equivalent := spec.budgeted_complete space atom budget complete
  exact missing ((equivalent.mem_iff value).2 inUnbounded)

/-- The five live operations in the order shared by the C inventory. -/
inductive InferenceAPI where
  | profiled
  | profiledTransient
  | profiledBudgeted
  | structuralProfiled
  | structuralProfiledBudgeted
  deriving DecidableEq, Repr

def InferenceAPI.name : InferenceAPI → String
  | .profiled => "eval_get_atom_types_profiled"
  | .profiledTransient => "eval_get_atom_types_profiled_transient"
  | .profiledBudgeted => "eval_get_atom_types_profiled_budgeted"
  | .structuralProfiled => "eval_get_atom_types_structural_profiled"
  | .structuralProfiledBudgeted =>
      "eval_get_atom_types_structural_profiled_budgeted"

def allInferenceAPIs : List InferenceAPI :=
  [.profiled, .profiledTransient, .profiledBudgeted,
   .structuralProfiled, .structuralProfiledBudgeted]

/-- Settled by the executable census.  All five functions return logical-space
order and retain repeated type occurrences.  This is observable through the
public `get-type` relation and is preserved by the profiled memo, so neither
reordering nor deduplication is licensed.  The three ordinary operations are
complete finite traversals; an explicitly budgeted operation may return a
sound proper prefix.  Only `.profiled` publishes to the persistent memo. -/
def settledContract : InferenceAPI → CollectionContract
  | .profiled => ⟨true, true, true, true⟩
  | .profiledTransient => ⟨true, true, true, false⟩
  | .profiledBudgeted => ⟨true, true, false, false⟩
  | .structuralProfiled => ⟨true, true, true, false⟩
  | .structuralProfiledBudgeted => ⟨true, true, false, false⟩

theorem allInferenceAPIs_count : allInferenceAPIs.length = 5 := rfl

theorem all_inference_contracts_are_sequence_semantic (api : InferenceAPI) :
    (settledContract api).orderSemantic = true ∧
    (settledContract api).multiplicitySemantic = true := by
  cases api <;> decide

theorem only_profiled_publishes (api : InferenceAPI) :
    (settledContract api).memoPublishes = true ↔ api = .profiled := by
  cases api <;> decide

theorem unbounded_complete_iff (api : InferenceAPI) :
    (settledContract api).unboundedComplete = true ↔
      api = .profiled ∨ api = .profiledTransient ∨
        api = .structuralProfiled := by
  cases api <;> decide

/-! ## §4 Search as strategy: refutation structurally unrepresentable -/

/-- Outcomes of a bounded search.  There is deliberately NO refutation
constructor.  `.complete []` records exhaustive negative evidence, whereas
`.incomplete` records silence caused by a bound.  Only the former can justify
a downstream negative presentation. -/
inductive SearchOutcome (Witness : Type) where
  | complete (witnesses : List Witness)
  | incomplete (spent : Nat)

/-- A search strategy over a judgment.  A completed sequence is sound and
complete for its claim; an incomplete observation carries no negative
authority.  Inhabitant search, first-inhabitant search, forward step, and
forward closure are all instances of this shape — never typing rules. -/
structure SearchStrategy (Claim Witness : Type)
    (Judges : Claim → Witness → Prop) where
  search : Claim → Nat → SearchOutcome Witness
  found_sound : ∀ c b witnesses w,
    search c b = .complete witnesses → w ∈ witnesses → Judges c w
  complete : ∀ c b witnesses,
    search c b = .complete witnesses → ∀ w, Judges c w → w ∈ witnesses

/-- The four live search operations in the order shared by the C inventory. -/
inductive SearchAPI where
  | inhabitants
  | firstInhabitant
  | forwardStep
  | forwardClosure
  deriving DecidableEq, Repr

def SearchAPI.name : SearchAPI → String
  | .inhabitants => "search-inhabitants"
  | .firstInhabitant => "search-first-inhabitant"
  | .forwardStep => "type-forward-step"
  | .forwardClosure => "type-forward-closure"

def allSearchAPIs : List SearchAPI :=
  [.inhabitants, .firstInhabitant, .forwardStep, .forwardClosure]

theorem allSearchAPIs_count : allSearchAPIs.length = 4 := rfl

/-- Only the first-inhabitant presentation turns a completed empty sequence
into a negative result.  No operation may do so for `.incomplete`. -/
def SearchAPI.exhaustiveEmptyMayReject : SearchAPI → Bool
  | .firstInhabitant => true
  | _ => false

theorem only_first_inhabitant_may_reject_complete_empty (api : SearchAPI) :
    api.exhaustiveEmptyMayReject = true ↔ api = .firstInhabitant := by
  cases api <;> decide

/-- Honesty witness: a claim can be TRUE while a (badly ordered) strategy
stays incomplete forever — incompleteness is not refutation, concretely. -/
def blindStrategy : SearchStrategy Nat Nat (fun c w => w = c) where
  search := fun _ b => .incomplete b
  found_sound := by intro _ _ _ _ h; cases h
  complete := by intro _ _ _ h; cases h

example : (∃ w, w = 42) ∧
    (∀ b, blindStrategy.search 42 b = .incomplete b) :=
  ⟨⟨42, rfl⟩, fun _ => rfl⟩

end Mettapedia.Languages.MeTTa.HE.OutcomeListContracts
