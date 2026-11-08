import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResolvedMatching
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalChecks

/-!
# Literal matching receipts as a fixed-observation profile of constraint steps

An actual matching receipt determines the same ordered physical selections
in the two-sided occurrence step. Equality, absence and exact-count checks
are retained. Their observation world is fixed under the substitution action,
so a successful literal check is valid in every remaining solution.

The old equation store and explicit tells must separately hold at the
identity assignment. A resolved matching observation alone supplies neither
that compatibility nor the stability of open checks. This bridge concerns
already instantiated literal rules; schematic admission and general data
conditions are separate interfaces.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FixedMatching

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

open Mettapedia.Languages.ProcessCalculi

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO}

/-- Fixedness is relative to the chosen substitution action, not a name for
groundness in every guest language. -/
def Fixed (A : SubstitutionAction T S) (term : T) : Prop :=
  ∀ assignment, A.apply assignment term = term

structure Observation (A : SubstitutionAction T S) (label : O → T)
    (world : Finset O) (rule : RuleInstance T) : Prop where
  gathers : ∀ term ∈ rule.take ++ rule.read, Fixed A term
  outputs : ∀ term ∈ rule.produce, Fixed A term
  arguments : ∀ check ∈ rule.checks, ∀ term ∈ check.terms, Fixed A term
  values : ∀ occurrence ∈ world, Fixed A (label occurrence)

def selection (receipt : GuardedMultisetRewriting.FiringReceipt O Empty T) : Selection O :=
  ⟨receipt.takes, receipt.reads, receipt.outputs⟩

private theorem empty_assignment_unique (assignment : Subst Empty T) :
    assignment = ResolvedMatching.assignment := by
  funext name
  cases name

theorem literal_solves_iff (A : SubstitutionAction T S) (assignment : Subst Empty T)
    (pattern value : T) :
    (ResolvedMatching.literalLayer A).Solves assignment pattern value ↔ A.E pattern value := by
  constructor
  · rintro ⟨actual, computed, equal⟩
    have same : pattern = actual := Option.some.inj computed
    cases same
    exact equal
  · intro equal
    exact ⟨pattern, rfl, equal⟩

theorem literal_instTemplate (A : SubstitutionAction T S) (assignment : Subst Empty T)
    (terms : List T) :
    instTemplate (ResolvedMatching.literalLayer A) assignment terms = some terms := by
  change terms.mapM (pure (f := Option)) = some terms
  simpa using (List.mapM_pure (m := Option) (l := terms) (f := id))

private theorem identity_function (A : SubstitutionAction T S) : A.apply A.identity = id :=
  funext A.apply_identity

private theorem labels_eq_zero_iff (label : O → T) (world : Finset O) :
    labels label world = 0 ↔ world = ∅ := by
  constructor
  · intro empty
    have cardinal := congrArg Multiset.card empty
    have zero : world.card = 0 := by simpa [labels] using cardinal
    exact Finset.card_eq_zero.mp zero
  · intro empty
    rw [empty]
    rfl

theorem literal_region (A : SubstitutionAction T S) (label : O → T)
    (world : Finset O) (pattern : T) :
    regionOf label world (semRegion (ResolvedMatching.literalLayer A)
      ResolvedMatching.assignment pattern) = Check.matches A A.identity label world pattern := by
  simpa only [A.apply_identity] using ResolvedMatching.resolved_region A A.identity label world pattern

theorem check_holds_iff (A : SubstitutionAction T S) (label : O → T)
    (world : Finset O) (check : Check T) :
    (ResolvedMatching.resolvedCheck A A.identity check).holds ResolvedMatching.assignment
      (GuardedMultisetRewriting.matchesIn (ResolvedMatching.literalLayer A) ResolvedMatching.assignment
        (ResolvedMatching.resolvedCheck A A.identity check).pattern (labels label world)) ↔
      check.Holds A A.identity label world := by
  classical
  have regions := literal_region A label world
  cases check with
  | equal left right => rfl
  | absent pattern =>
      change GuardedMultisetRewriting.matchesIn (ResolvedMatching.literalLayer A) ResolvedMatching.assignment
        (A.apply A.identity pattern) (labels label world) = 0 ↔ _
      rw [A.apply_identity, GuardedMultisetRewriting.matchesIn_labels, regions, labels_eq_zero_iff]
      constructor
      · intro empty occurrence present equal
        have member : occurrence ∈ Check.matches A A.identity label world pattern :=
          Finset.mem_filter.mpr ⟨present, equal⟩
        rw [empty] at member
        exact Finset.notMem_empty _ member
      · intro absent
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro occurrence member
        obtain ⟨present, equal⟩ := Finset.mem_filter.mp member
        exact absent occurrence present equal
  | count pattern number =>
      change Multiset.card (GuardedMultisetRewriting.matchesIn (ResolvedMatching.literalLayer A)
        ResolvedMatching.assignment (A.apply A.identity pattern) (labels label world)) = number ↔ _
      rw [A.apply_identity, GuardedMultisetRewriting.matchesIn_labels, regions]
      simp only [Check.Holds, labels, Multiset.card_map, Finset.card_def]

theorem fixed_check (A : SubstitutionAction T S) (label : O → T)
    (world : Finset O) (check : Check T)
    (arguments : ∀ term ∈ check.terms, Fixed A term)
    (values : ∀ occurrence ∈ world, Fixed A (label occurrence))
    (holds : check.Holds A A.identity label world) (assignment : S) :
    check.Holds A assignment label world := by
  apply (Check.holds_congr A A.identity assignment label world check
    (fun term member => by rw [A.apply_identity, arguments term member assignment]; exact A.equivalence.refl _)
    (fun occurrence member => by rw [A.apply_identity, values occurrence member assignment]; exact A.equivalence.refl _)).mp
  exact holds

private theorem fixed_matches (A : SubstitutionAction T S) (label : O → T) (assignment : S)
    {patterns : List T} {picked : List O}
    (matched : List.Forall₂ (fun pattern occurrence => A.E (A.apply assignment pattern)
      (A.apply assignment (label occurrence))) patterns picked)
    (patternsFixed : ∀ term ∈ patterns, Fixed A term)
    (valuesFixed : ∀ occurrence ∈ picked, Fixed A (label occurrence)) :
    List.Forall₂ (fun pattern occurrence => A.E (A.apply A.identity pattern)
      (A.apply A.identity (label occurrence))) patterns picked := by
  induction matched with
  | nil => exact .nil
  | @cons pattern occurrence patterns picked head tail ih =>
      refine .cons ?_ (ih
        (fun term member => patternsFixed term (List.mem_cons_of_mem _ member))
        (fun selected member => valuesFixed selected (List.mem_cons_of_mem _ member)))
      simpa only [A.apply_identity, patternsFixed pattern List.mem_cons_self assignment,
        valuesFixed occurrence List.mem_cons_self assignment] using head

variable [DecidableEq O]

/-- The matching receipt's own selections become the actual constraint-step
selections. No premise is inferred from a final-store equality. -/
theorem valid_of_receipt (A : SubstitutionAction T S) (label : O → T)
    {rule : RuleInstance T} {before : Configuration T O}
    (receipt : GuardedMultisetRewriting.FiringReceipt O Empty T)
    (valid : receipt.ValidAt (ResolvedMatching.literalLayer A)
      (ResolvedMatching.resolvedRule A A.identity rule) label before.present)
    (fixed : Observation A label before.present rule)
    (compatible : A.Models A.identity (before.equations ++ rule.tell)) :
    (selection receipt).Valid A label rule before := by
  have takes : List.Forall₂ (fun pattern occurrence => A.E pattern (label occurrence))
      rule.take receipt.takes := by
    have matched := valid.takesMatch
    simp only [ResolvedMatching.resolvedRule, identity_function A, List.map_id] at matched
    exact List.forall₂_map_right_iff.mp (matched.imp fun _ _ proof => (literal_solves_iff A _ _ _).mp proof)
  have reads : List.Forall₂ (fun pattern occurrence => A.E pattern (label occurrence))
      rule.read receipt.reads := by
    have matched := valid.readsMatch
    simp only [ResolvedMatching.resolvedRule, identity_function A, List.map_id] at matched
    exact List.forall₂_map_right_iff.mp (matched.imp fun _ _ proof => (literal_solves_iff A _ _ _).mp proof)
  have outputs : receipt.outputs.map label = rule.produce := by
    have made := valid.makes
    rw [literal_instTemplate] at made
    simpa only [ResolvedMatching.resolvedRule, identity_function A, List.map_id] using (Option.some.inj made).symm
  refine ⟨valid.uniqueTakes, valid.uniqueOutputs, takes.length_eq, reads.length_eq, outputs,
    ⟨valid.takesPresent, valid.readsPresent, valid.apart, valid.fresh, by simp [Selection.commit]⟩,
    ⟨A.identity, ?_⟩, ?_⟩
  · have split := (A.models_append A.identity before.equations rule.tell).mp compatible
    apply (A.models_append _ _ _).mpr
    constructor
    · apply (A.models_append _ _ _).mpr
      constructor
      · apply (A.models_append _ _ _).mpr
        exact ⟨split.1, (Selection.models_equations_iff A A.identity label takes.length_eq).mpr
          (by simpa only [A.apply_identity] using takes)⟩
      · exact (Selection.models_equations_iff A A.identity label reads.length_eq).mpr
          (by simpa only [A.apply_identity] using reads)
    · exact split.2
  · intro check member assignment _
    have accepted := valid.checks_hold (ResolvedMatching.resolvedCheck A A.identity check)
      (List.mem_map.mpr ⟨check, member, rfl⟩)
    rw [empty_assignment_unique receipt.assignment] at accepted
    exact fixed_check A label before.present check (fixed.arguments check member) fixed.values
      ((check_holds_iff A label before.present check).mp accepted) assignment

theorem identity_models_problem (A : SubstitutionAction T S) (label : O → T)
    {rule : RuleInstance T} {before : Configuration T O} {picked : Selection O}
    (valid : picked.Valid A label rule before)
    (fixed : Observation A label before.present rule)
    (compatible : A.Models A.identity (before.equations ++ rule.tell)) :
    A.Models A.identity (picked.problem label rule before) := by
  obtain ⟨assignment, solved⟩ := valid.consistent
  obtain ⟨_, taken, read, _⟩ := Selection.models_problem A valid solved
  have takeFixed : ∀ term ∈ rule.take, Fixed A term := fun term member =>
    fixed.gathers term (List.mem_append_left _ member)
  have readFixed : ∀ term ∈ rule.read, Fixed A term := fun term member =>
    fixed.gathers term (List.mem_append_right _ member)
  have takeValues : ∀ occurrence ∈ picked.taken, Fixed A (label occurrence) := fun occurrence member =>
    fixed.values occurrence (valid.occurrences.taken_subset (by simpa [Selection.commit] using member))
  have readValues : ∀ occurrence ∈ picked.read, Fixed A (label occurrence) := fun occurrence member =>
    fixed.values occurrence (valid.occurrences.kept_subset (by simpa [Selection.commit] using member))
  have previous := (A.models_append A.identity before.equations rule.tell).mp compatible
  apply (A.models_append _ _ _).mpr
  constructor
  · apply (A.models_append _ _ _).mpr
    constructor
    · apply (A.models_append _ _ _).mpr
      exact ⟨previous.1, (Selection.models_equations_iff A A.identity label valid.take_length).mpr
        (fixed_matches A label assignment taken takeFixed takeValues)⟩
    · exact (Selection.models_equations_iff A A.identity label valid.read_length).mpr
        (fixed_matches A label assignment read readFixed readValues)
  · exact previous.2

/-- The fixed-observation fragment is bidirectional at the exact receipt.
The background equations and tells remain explicit hypotheses. -/
theorem valid_iff_receipt (A : SubstitutionAction T S) (label : O → T)
    {rule : RuleInstance T} {before : Configuration T O} (picked : Selection O)
    (fixed : Observation A label before.present rule)
    (compatible : A.Models A.identity (before.equations ++ rule.tell)) :
    picked.Valid A label rule before ↔
      (ResolvedMatching.receipt A A.identity label before rule picked).ValidAt
        (ResolvedMatching.literalLayer A) (ResolvedMatching.resolvedRule A A.identity rule)
        label before.present := by
  constructor
  · intro valid
    have observed := ResolvedMatching.valid_receipt A valid (identity_models_problem A label valid fixed compatible)
    simpa only [A.apply_identity] using observed
  · intro valid
    exact valid_of_receipt A label _ valid fixed compatible

theorem step_of_receipt (A : SubstitutionAction T S) (label : O → T)
    {rule : RuleInstance T} {before : Configuration T O}
    (receipt : GuardedMultisetRewriting.FiringReceipt O Empty T)
    (valid : receipt.ValidAt (ResolvedMatching.literalLayer A)
      (ResolvedMatching.resolvedRule A A.identity rule) label before.present)
    (fixed : Observation A label before.present rule)
    (compatible : A.Models A.identity (before.equations ++ rule.tell)) :
    Step A label rule before ((selection receipt).result label rule before) :=
  ⟨selection receipt, valid_of_receipt A label receipt valid fixed compatible, rfl⟩

/-- The active world of a fixed profile remains fixed after the actual
publication. Fresh physical identities are preserved rather than quotiented
by equality of the values they carry. -/
theorem result_values_fixed (A : SubstitutionAction T S) (label : O → T)
    {rule : RuleInstance T} {before : Configuration T O} {picked : Selection O}
    (fixed : Observation A label before.present rule) (valid : picked.Valid A label rule before) :
    ∀ occurrence ∈ (picked.result label rule before).present, Fixed A (label occurrence) := by
  intro occurrence present
  rcases mem_fire.mp present with survived | produced
  · exact fixed.values occurrence survived.1
  · have made : occurrence ∈ picked.made := by simpa [Selection.commit] using produced
    apply fixed.outputs (label occurrence)
    rw [← valid.outputs]
    exact List.mem_map.mpr ⟨occurrence, made, rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FixedMatching
