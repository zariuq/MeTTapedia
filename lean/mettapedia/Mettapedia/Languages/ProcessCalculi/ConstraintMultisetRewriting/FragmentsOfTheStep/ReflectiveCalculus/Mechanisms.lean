import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Bisimulation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Source

/-!
# Placing communication on the step: what the knowledge does, and the controls

The rule set `Rules` keeps rows in canonical form and lets the knowledge solve the rule's unknowns
from them. This module states what that unification does, and the controls around it.

* **The match of the two channels is a solvability question of the knowledge**
  (`channel_match_is_solvability`): for an input row and an output row of a represented store, the
  communication firing that takes them is admitted exactly when the channels agree, which on
  canonical rows is name equivalence (`canonical_channels_iff`).
* **Name equivalence in the knowledge** (`equationalAction`: two terms are equal when their
  canonical forms agree under every grounding). Rows may then be written as they are:
  `knowledge_with_name_equivalence_fires` admits the communication between `for(y <- @(*@0)){*y}`
  and `@0!(@0!(0))` through quote-drop, which the syntactic knowledge refuses
  (`syntactic_knowledge_refuses`).
* **The bag laws in the knowledge make matching not principal** (`bag_laws_split_two_ways`):
  modulo the equations, splitting the row `@0!(0) | for(z <- @0){0}` has two solutions with
  different first rows. The first-order step admits on solvability and keeps every solution, so a
  store would come to denote two processes. With the bag laws out of the knowledge the split is
  principal (`split_is_principal`), which is why `Rules` keeps the parallel structure in the
  multiset of rows and heats.
* **The ground placement** (`groundComm`): one closed rule instance per reduction, contractum
  written in. A ground firing makes only its written contractum (`ground_makes_its_contractum`),
  and the contracta of the closed processes `for(y <- @0){*y} | @0!(nested n)` are pairwise
  different (`ground_placement_is_not_finite`): no finite list of ground rules has them all,
  while the one schema `comm` fires every reduction (`communication_complete`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Mechanisms

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
  (canonicalize IsCanonical IsCanonicalList)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReaction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReactionControls
open Source

/-! ## The match of the channels -/

/-- **The match of the two channels is a solvability question of the knowledge.** -/
theorem channel_match_is_solvability {C : Store} {P : RhoProcess} {meaning : Occ → Pattern}
    (represented : RepresentsBy C P meaning) {o₁ o₂ : Occ} (member₁ : o₁ ∈ C.present)
    (member₂ : o₂ ∈ C.present) {c₁ B c₂ R : Pattern}
    (at₁ : meaning o₁ = input c₁ B) (at₂ : meaning o₂ = output c₂ R)
    {index : Nat} (fresh : index ∉ mentioned C) (made : List Occ) :
    action.Consistent ((⟨[o₁, o₂], [], made⟩ : Selection Occ).problem label (comm index) C) ↔
      c₁ = c₂ := by
  rw [consistent_iff]
  constructor
  · rintro ⟨g, holds⟩
    obtain ⟨old, takes, _, _⟩ := holds_problem.mp holds
    simp only [comm, Selection.equations, List.zipWith_cons_cons, List.zipWith_nil_right,
      holds_cons, holds_nil, and_true] at takes
    have first := takes.1.trans (represented.determined g old o₁ member₁)
    have second := takes.2.trans (represented.determined g old o₂ member₂)
    rw [at₁] at first
    rw [at₂] at second
    simp only [Tm.eval, input, output, Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq,
      true_and, and_true] at first second
    exact first.1.symm.trans second.1
  · intro same
    obtain ⟨g, holds⟩ := represented.consistent
    let values : Port → Pattern
      | .channel => c₁
      | .body => B
      | .payload => R
      | _ => zeroPattern
    refine ⟨extend g index values, holds_problem.mpr
      ⟨holds_extend_of_fresh holds (not_mem_storeIndices fresh) values, ?_,
        by simp [Selection.equations], by simp [comm]⟩⟩
    simp only [comm, Selection.equations, List.zipWith_cons_cons, List.zipWith_nil_right,
      holds_cons, holds_nil, and_true]
    rw [eval_extend_of_fresh g values (not_mem_label_indices fresh member₁),
      eval_extend_of_fresh g values (not_mem_label_indices fresh member₂),
      represented.determined g holds o₁ member₁, represented.determined g holds o₂ member₂,
      at₁, at₂]
    simp only [Tm.eval, eval_unknown_extend]
    exact ⟨rfl, congrArg (fun channel => output channel R) same⟩

/-- On canonical rows, agreement of the channels is name equivalence. -/
theorem canonical_channels_iff {c₁ B c₂ R : Pattern} (inputPrime : IsPrime (input c₁ B))
    (outputPrime : IsPrime (output c₂ R)) :
    c₁ = c₂ ↔ canonicalize c₁ = canonicalize c₂ := by
  rw [channel_canonical inputPrime, output_channel_canonical outputPrime]

/-! ## Name equivalence in the knowledge -/

/-- **Name equivalence in the knowledge**: two terms are equal when their canonical forms agree
under every grounding. -/
def equationalAction : SubstitutionAction Tm (Unknown → Tm) where
  E left right := ∀ g, canonicalize (left.eval g) = canonicalize (right.eval g)
  equivalence := ⟨fun _ _ => rfl, fun same g => (same g).symm,
    fun first second g => (first g).trans (second g)⟩
  apply σ t := t.bind σ
  identity := Tm.var
  compose outer inner := fun unknown => (inner unknown).bind outer
  apply_identity := Tm.bind_var
  apply_compose outer inner t := (Tm.bind_bind outer inner t).symm
  preserves σ {left right} same := fun g => by
    rw [Tm.eval_bind, Tm.eval_bind]
    exact same _

/-- The input as written, on `@(*@0)`. -/
def writtenInput : Occ := (0, .lit (input alternateChannel body))

/-- The output as written, on `@0`. -/
def writtenOutput : Occ := (1, .lit (output channel payload))

/-- The made row. -/
def writtenMade : Occ := (2, .react (unknown 0 .body) (unknown 0 .payload))

/-- The two rows as written, with no knowledge. -/
def writtenStore : Store := ⟨[], {writtenInput, writtenOutput}⟩

def writtenSelection : Selection Occ := ⟨[writtenInput, writtenOutput], [], [writtenMade]⟩

/-- The solution: the channel is `@0`. -/
def writtenSolution : Unknown → Tm := fun unknown =>
  match unknown.port with
  | .channel => .lit channel
  | .body => .lit body
  | .payload => .lit payload
  | _ => .lit zeroPattern

/-- **Positive.** With name equivalence in the knowledge, communication fires between rows whose
channels are different names, through quote-drop. -/
theorem knowledge_with_name_equivalence_fires :
    writtenSelection.Valid equationalAction label (comm 0) writtenStore := by
  refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ⟨writtenSolution, ?_⟩, ?_⟩
  · simp [writtenSelection, writtenInput, writtenOutput]
  · simp [writtenSelection]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [Selection.commit, writtenSelection, writtenStore]
    · simp [Selection.commit, writtenSelection]
    · simp [Selection.commit, writtenSelection]
    · simp [Selection.commit, writtenSelection, writtenStore, writtenMade, writtenInput,
        writtenOutput]
    · simp [Selection.commit]
  · intro equation member g
    simp only [Selection.problem, writtenSelection, writtenStore, comm, Selection.equations,
      List.zipWith_cons_cons, List.zipWith_nil_right, List.nil_append, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · show canonicalize (input channel body) = canonicalize (input alternateChannel body)
      unfold input
      rw [CanonicalStepperCompleteness.canonicalize_input,
        CanonicalStepperCompleteness.canonicalize_input, actual_name_equation]
    · rfl
  · simp [comm]

/-- **Negative.** With syntactic knowledge, no communication fires between the same rows. -/
theorem syntactic_knowledge_refuses (index : Nat) (after : Store) :
    ¬ ConstraintMultisetRewriting.Step action label (comm index) writtenStore after := by
  rintro ⟨selection, valid, -⟩
  obtain ⟨o₁, o₂, taken⟩ := List.length_eq_two.mp valid.take_length.symm
  obtain ⟨g, holds⟩ := (consistent_iff _).mp valid.consistent
  obtain ⟨_, takes, _, _⟩ := holds_problem.mp holds
  simp only [comm, taken, Selection.equations, List.zipWith_cons_cons, List.zipWith_nil_right,
    holds_cons, holds_nil, and_true] at takes
  have sub := valid.occurrences.taken_subset
  simp only [Selection.commit, taken, List.toFinset_cons, List.toFinset_nil,
    insert_empty_eq] at sub
  have member₁ : o₁ ∈ writtenStore.present := sub (by simp)
  have member₂ : o₂ ∈ writtenStore.present := sub (by simp)
  simp only [writtenStore, Finset.mem_insert, Finset.mem_singleton] at member₁ member₂
  rcases member₁ with rfl | rfl <;> rcases member₂ with rfl | rfl
  · have bad := takes.2
    simp [Tm.eval, writtenInput, input, output, IndexedOccurrences.label] at bad
  · have one := takes.1
    have two := takes.2
    simp only [Tm.eval, writtenInput, writtenOutput, input, output, IndexedOccurrences.label,
      Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq, true_and, and_true] at one two
    exact literal_names_distinct (one.1.symm.trans two.1)
  · have bad := takes.1
    simp [Tm.eval, writtenOutput, input, output, IndexedOccurrences.label] at bad
  · have bad := takes.1
    simp [Tm.eval, writtenOutput, input, output, IndexedOccurrences.label] at bad

/-! ## The bag laws in the knowledge -/

/-- `@0!(0) | for(z <- @0){0}`. -/
def twoPrimes : Pattern := .collection .hashBag [payload, receiver] none

theorem canonicalize_swap (first second : Pattern) :
    canonicalize (.collection .hashBag [first, second] none) =
      canonicalize (.collection .hashBag [second, first] none) := by
  rw [CanonicalStepperCompleteness.canonicalize_bag, CanonicalStepperCompleteness.canonicalize_bag,
    Canonical.normalizeBagElements_eq_sort_bagContents,
    Canonical.normalizeBagElements_eq_sort_bagContents]
  congr 1
  apply Canonical.sortPatterns_eq_of_perm
  unfold Canonical.bagContents
  apply List.Perm.filter
  apply List.Perm.flatMap_right
  simp only [List.map_cons, List.map_nil]
  exact List.Perm.swap _ _ _

/-- One reading of the split: the output first. -/
def firstWay : Unknown → Pattern := fun unknown =>
  match unknown.port with
  | .first => payload
  | .others => .collection .hashBag [receiver] none
  | _ => zeroPattern

/-- The other reading: the input first. -/
def secondWay : Unknown → Pattern := fun unknown =>
  match unknown.port with
  | .first => receiver
  | .others => .collection .hashBag [payload] none
  | _ => zeroPattern

/-- **Breaking point: the bag laws in the knowledge.** Modulo the equations of the source, the
heating pattern matches `@0!(0) | for(z <- @0){0}` in two ways that make different first rows. -/
theorem bag_laws_split_two_ways :
    canonicalize ((Tm.split (unknown 0 .first) (unknown 0 .others)).eval firstWay) =
      canonicalize twoPrimes ∧
    canonicalize ((Tm.split (unknown 0 .first) (unknown 0 .others)).eval secondWay) =
      canonicalize twoPrimes ∧
    (unknown 0 .first).eval firstWay ≠ (unknown 0 .first).eval secondWay := by
  refine ⟨rfl, canonicalize_swap receiver payload, ?_⟩
  simp [firstWay, secondWay, unknown, Tm.eval, payload, receiver, output, input]

/-- **Without the bag laws the split is principal**: two solutions of the same heating equation
agree on both made rows. -/
theorem split_is_principal {elements : List Pattern} {g₁ g₂ : Unknown → Pattern}
    (first : (Tm.split (unknown 0 .first) (unknown 0 .others)).eval g₁ =
      .collection .hashBag elements none)
    (second : (Tm.split (unknown 0 .first) (unknown 0 .others)).eval g₂ =
      .collection .hashBag elements none) :
    (unknown 0 .first).eval g₁ = (unknown 0 .first).eval g₂ ∧
      (unknown 0 .others).eval g₁ = (unknown 0 .others).eval g₂ := by
  obtain ⟨tail₁, others₁, elements₁⟩ := consBag_eq_bag first
  obtain ⟨tail₂, others₂, elements₂⟩ := consBag_eq_bag second
  rw [elements₁] at elements₂
  simp only [List.cons.injEq] at elements₂
  exact ⟨elements₂.1, by rw [others₁, others₂, elements₂.2]⟩

/-! ## The ground placement -/

/-- **The ground placement**: one closed rule instance per reduction, with the contractum written
into it. -/
def groundComm (rule : GroundComm) : RuleInstance Tm where
  take := [.lit (input rule.inputChannel rule.body), .lit (output rule.outputChannel rule.payload)]
  read := []
  tell := []
  checks := []
  produce := [.lit (canonicalize rule.result.1)]

/-- A ground firing makes the contractum written into its rule, whatever the store. -/
theorem ground_makes_its_contractum {rule : GroundComm} {C C' : Store}
    (fires : Fires (groundComm rule) C C') :
    ∃ o ∈ C'.present, o ∉ C.present ∧ label o = .lit (canonicalize rule.result.1) := by
  obtain ⟨selection, valid, rfl⟩ := fires
  have outputs : selection.made.map label = [.lit (canonicalize rule.result.1)] := valid.outputs
  obtain ⟨o, made, labelled⟩ := List.map_eq_singleton_iff.mp outputs
  have fresh : o ∉ C.present := by
    have apart := valid.occurrences.fresh
    simp only [Selection.commit, made, List.toFinset_cons, List.toFinset_nil,
      insert_empty_eq] at apart
    exact Finset.disjoint_singleton_left.mp apart
  refine ⟨o, ?_, fresh, labelled⟩
  rw [result_present, made]
  simp

/-- `@0!(@0!(...@0!(0)...))`, `n` outputs deep. -/
def nested : Nat → Pattern
  | 0 => zero
  | n + 1 => output channel (nested n)

theorem nested_typed : ∀ n, ProcWellSorted rhoReflectivePresentation FreeSortContext.empty []
    (nested n)
  | 0 => .unit
  | n + 1 => .output (.quote .unit (by decide)) (nested_typed n)

theorem nested_safe : ∀ n, binderSafeAt "NQuote" 0 (nested n) = true
  | 0 => rfl
  | n + 1 => by
      change (binderSafeAt "NQuote" 0 (.apply "NQuote" [zero]) &&
        (binderSafeAt "NQuote" 0 (nested n) && true)) = true
      rw [nested_safe n]
      rfl

theorem nested_canonical : ∀ n, IsCanonical (nested n)
  | 0 => by simp [nested, zero, IsCanonical, IsCanonicalList]
  | n + 1 => by
      simp [nested, output, channel, zero, IsCanonical, IsCanonicalList, nested_canonical n]

theorem nested_normal : ∀ n, semanticNormalizeProc (nested n) = nested n
  | 0 => rfl
  | n + 1 => by
      change Pattern.apply "POutput"
        [semanticNormalizeName channel, semanticNormalizeProc (nested n)] = _
      rw [nested_normal n]
      rfl

theorem nested_injective : Function.Injective nested := by
  intro m
  induction m with
  | zero =>
      intro n same
      cases n with
      | zero => rfl
      | succ n => simp [nested, zero, output] at same
  | succ m earlier =>
      intro n same
      cases n with
      | zero => simp [nested, zero, output] at same
      | succ n =>
          simp only [nested, output, Pattern.apply.injEq, List.cons.injEq, true_and,
            and_true] at same
          exact congrArg Nat.succ (earlier same)

theorem nested_output_prime (n : Nat) : IsPrime (output channel (nested n)) := by
  refine ⟨(rhoClosedTermWellSorted_process_iff _).mpr
    ⟨.output (.quote .unit (by decide)) (nested_typed n), nested_safe (n + 1)⟩, nested_canonical (n + 1), ?_, ?_⟩
  · simp [output]
  · intro elements
    simp [output]

/-- `for(y <- @0){*y} | @0!(nested n)`. -/
def family (n : Nat) : GroundComm :=
  ⟨channel, channel, body, nested n, input_prime, nested_output_prime n, rfl⟩

theorem family_contractum (n : Nat) : canonicalize (family n).result.1 = nested n := by
  have collapse : semanticCommSubst body (nested n) = semanticNormalizeProc (nested n) :=
    semanticCommSubst_collapses_bound_drop (nested n)
  change canonicalize (semanticCommSubst body (nested n)) = nested n
  rw [collapse, nested_normal, Canonical.canonicalize_eq_of_isCanonical (nested_canonical n)]

/-- Every member of the family reduces. -/
theorem family_reduces (n : Nat) :
    rhoLanguageDefGSLT.Step ((family n).source empty) ((family n).target empty) :=
  (publicStep_iff _ _).mpr ⟨family n, empty, (family n).source_inventory empty,
    (family n).target_inventory empty⟩

/-- **The ground placement is not finite**: every finite list of ground communication rules misses
the contractum of some member of the family, and a ground firing makes only its own contractum
(`ground_makes_its_contractum`). -/
theorem ground_placement_is_not_finite (rules : List GroundComm) :
    ∃ n, ∀ rule ∈ rules, canonicalize rule.result.1 ≠ canonicalize (family n).result.1 := by
  classical
  let written : Finset Pattern := (rules.map fun rule => canonicalize rule.result.1).toFinset
  obtain ⟨n, fresh⟩ := Infinite.exists_notMem_finset
    (written.preimage nested (nested_injective.injOn))
  refine ⟨n, fun rule member same => fresh ?_⟩
  rw [Finset.mem_preimage, ← family_contractum n, ← same]
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨rule, member, rfl⟩)

/-! ## One communication schema alone is not enough; the separating program on the step -/

/-- A communication firing takes two different rows. -/
theorem communication_takes_two_rows {C C' : Store} (fires : Communicates C C') :
    2 ≤ C.present.card := by
  obtain ⟨index, selection, valid, rfl⟩ := fires
  obtain ⟨o₁, o₂, taken⟩ := List.length_eq_two.mp valid.take_length.symm
  have distinct : o₁ ≠ o₂ := by
    have nodup := valid.take_distinct
    rw [taken] at nodup
    simpa using nodup
  have sub : ({o₁, o₂} : Finset Occ) ⊆ C.present := by
    have sub := valid.occurrences.taken_subset
    simpa [Selection.commit, taken] using sub
  calc 2 = ({o₁, o₂} : Finset Occ).card := (Finset.card_pair distinct).symm
    _ ≤ C.present.card := Finset.card_le_card sub

/-- **Heating is needed.** The separating program reduces, but no communication fires at its
one-row store: the parallel structure must first be split into rows by administrative firings. -/
theorem heating_is_needed :
    rhoLanguageDefGSLT.Step (rule.source empty) (rule.target empty) ∧
      ∀ C', ¬ Communicates (initialStore (rule.source empty)) C' := by
  refine ⟨semantic_and_ordinary_differ.1, fun C' fires => ?_⟩
  have two := communication_takes_two_rows fires
  simp [initialStore] at two

/-- **The separating program on the step.** From the one-row store of
`for(y <- @0){*y} | @0!(@0!(0))`, administrative firings and one communication reach a store that
represents the process whose canonical bag is `{@0!(0)}`, the semantic contractum, which is not the
ordinary contractum `*@(@0!(0))`; a store represents one equation class
(`represents_functional`). -/
theorem separating_program_on_the_step :
    ∃ C₁ C₂, Relation.ReflTransGen Administers (initialStore (rule.source empty)) C₁ ∧
      Communicates C₁ C₂ ∧ Represents C₂ (rule.target empty) ∧
      (fromProcess (rule.target empty)).1 = {payload} ∧ payload ≠ ordinaryContractum := by
  obtain ⟨C₁, C₂, meaning₂, run, fires, represented⟩ :=
    communication_complete (initial_represents _) semantic_and_ordinary_differ.1
  refine ⟨C₁, C₂, run, fires, ⟨meaning₂, represented⟩, ?_, ?_⟩
  · rw [rule.target_inventory empty, append_inventory]
    show primes rule.result.1 + 0 = {payload}
    rw [actual_result, add_zero, primes_of_isPrime payload_prime]
  · simp [payload, ordinaryContractum, output]

#print axioms heating_is_needed
#print axioms separating_program_on_the_step
#print axioms channel_match_is_solvability
#print axioms knowledge_with_name_equivalence_fires
#print axioms syntactic_knowledge_refuses
#print axioms bag_laws_split_two_ways
#print axioms split_is_principal
#print axioms ground_makes_its_contractum
#print axioms ground_placement_is_not_finite

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Mechanisms
