import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ReferenceStepChain
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.SharedSteps

/-!
# Contextual reference execution refines the actual guarded rewriting step

Gather recovery may extend the shared store before outputs are built. Existing
bag references retain their meaning across both extensions. Query matching is
complete at its declared input patterns, so absence and exact-count checks
use the same regions as the core calculus. Output templates remain unrestricted
by the inverse-matching profile.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

variable {Head V : Type} [DecidableEq Head] [DecidableEq V]

def RuleInput (rule : Rule V (Term Head) (Pattern Head V)) : Prop :=
  (∀ p ∈ rule.take ++ rule.read, p.Input) ∧ ∀ check ∈ rule.checks, check.pattern.Input

/-- Only gathers and observed regions require inverse-matching completeness. -/
def ruleInputCheck (rule : Rule V (Term Head) (Pattern Head V)) : Bool :=
  (rule.take ++ rule.read).all Pattern.inputCheck &&
    rule.checks.all (fun check => check.pattern.inputCheck)

omit [DecidableEq Head] [DecidableEq V] in
theorem ruleInputCheck_iff (rule : Rule V (Term Head) (Pattern Head V)) :
    ruleInputCheck rule = true ↔ RuleInput rule := by
  simp only [ruleInputCheck, Bool.and_eq_true, List.all_eq_true, Pattern.inputCheck_iff, RuleInput]

/-- The implementation relation uses the common reference matcher, graft and constructor builder. -/
def SharedStep (rule : Rule V (Term Head) (Pattern Head V)) (store : Store Head) (bag : Multiset Ref)
    (finalStore : Store Head) (finalBag : Multiset Ref) : Prop :=
  ∃ (matchStore : Store Head) (assignment : Subst V Ref) (frame kept : Multiset Ref)
      (taken read made : List Ref),
    taken.length = rule.take.length ∧ bag = frame + taken + kept ∧
    kept ≤ (read : Multiset Ref) ∧ (∀ r ∈ read, r ∈ kept) ∧
    matchListContextR (rule.take ++ rule.read) store (fun _ => none) (taken ++ read) =
      (matchStore, some assignment) ∧
    (∀ check ∈ rule.checks, check.holds (unfoldSubst matchStore assignment)
      ((bag.filter fun r => (matchContextR matchStore check.pattern assignment r).2.isSome).map (unfold matchStore))) ∧
    instantiateTemplatesR rule.produce matchStore assignment = (finalStore, some made) ∧
    finalBag = frame + kept + made

theorem sharedStep_sound {rule : Rule V (Term Head) (Pattern Head V)} (input : RuleInput rule)
    {store finalStore : Store Head} {bag finalBag : Multiset Ref}
    (canonical : Canonical store) (validBag : ∀ r ∈ bag, CanonRef store r)
    (step : SharedStep rule store bag finalStore finalBag) :
    store <+: finalStore ∧ Canonical finalStore ∧ (∀ r ∈ finalBag, CanonRef finalStore r) ∧
      Step layer rule (trees store bag) (trees finalStore finalBag) := by
  obtain ⟨matchStore, assignment, frame, kept, taken, read, made, takeCount, before, keptBound, readKept,
    matched, checked, built, rfl⟩ := step
  have frameValid : ∀ r ∈ frame, CanonRef store r := by
    intro r member
    apply validBag r
    rw [before]
    simp [member]
  have keptValid : ∀ r ∈ kept, CanonRef store r := by
    intro r member
    apply validBag r
    rw [before]
    simp [member]
  have gathersValid : ∀ r ∈ taken ++ read, CanonRef store r := by
    intro r member
    rcases List.mem_append.mp member with takenHere | readHere
    · apply validBag r
      rw [before]
      simp [takenHere]
    · exact keptValid r (readKept r readHere)
  obtain ⟨grows, matchCanonical, assignments, matchExact⟩ := matchListContextR_spec
    (rule.take ++ rule.read) store (fun _ => none) (taken ++ read) canonical
    (by intro v r impossible; cases impossible) gathersValid
  rw [matched] at grows matchCanonical assignments matchExact
  dsimp only at grows matchCanonical assignments matchExact
  have assignmentValid := assignments assignment rfl
  obtain ⟨more, finalCanonical, results, outputExact⟩ := instantiateTemplatesR_spec
    rule.produce matchStore matchCanonical assignment assignmentValid
  rw [built] at more finalCanonical results outputExact
  dsimp only at more finalCanonical results outputExact
  have completeGrowth := grows.trans more
  have chain : StepChain layer (fun _ => none) (rule.take ++ rule.read)
      ((taken ++ read).map (unfold store)) (unfoldSubst matchStore assignment) := by
    apply (matchList_exact _ _ _ _ input.1).mp
    simpa only [Option.map_some, unfoldSubst_none] using matchExact.symm
  obtain ⟨binds, solves⟩ := (stepChain_empty_iff _ _ _ _).mp chain
  rw [List.map_append] at solves
  obtain ⟨takes, reads⟩ := forall₂_split solves (by simp [takeCount])
  refine ⟨completeGrowth, finalCanonical, ?_, ?_⟩
  · intro r member
    simp only [Multiset.mem_add, Multiset.mem_coe] at member
    rcases member with (inFrame | inKept) | inMade
    · exact (frameValid r inFrame).prefix completeGrowth
    · exact (keptValid r inKept).prefix completeGrowth
    · exact results made rfl r inMade
  · refine ⟨unfoldSubst matchStore assignment, trees store frame,
      ((taken.map (unfold store) : List _) : Multiset _), kept.map (unfold store),
      made.map (unfold finalStore), binds, ⟨_, takes, rfl⟩, ⟨_, reads, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · simpa using Multiset.map_le_map (f := unfold store) keptBound
    · intro t member
      obtain ⟨r, sourceMember, rfl⟩ := List.mem_map.mp member
      exact Multiset.mem_map_of_mem _ (readKept r sourceMember)
    · simp [trees, before, Multiset.map_add]
    · intro check member
      have satisfied := checked check member
      rw [matchesIn_contextual_shared matchCanonical assignmentValid check.pattern (input.2 check member)
        (fun r m => (validBag r m).prefix grows)] at satisfied
      rw [show bag.map (unfold matchStore) = trees store bag from trees_prefix canonical.topo grows validBag] at satisfied
      exact satisfied
    · simpa only [Option.map_some] using outputExact.symm
    · simp only [trees, Multiset.map_add, Multiset.map_coe]
      congr 2
      · exact Multiset.map_congr rfl fun r member =>
          unfold_prefix canonical.topo completeGrowth (frameValid r member).valid
      · exact Multiset.map_congr rfl fun r member =>
          unfold_prefix canonical.topo completeGrowth (keptValid r member).valid

/-- Every core instance in the declared input profile is realized by the reference implementation. -/
theorem sharedStep_complete {rule : Rule V (Term Head) (Pattern Head V)} (input : RuleInput rule)
    {store : Store Head} {bag : Multiset Ref} (canonical : Canonical store)
    (validBag : ∀ r ∈ bag, CanonRef store r) {after : Multiset (Term Head)}
    (step : Step layer rule (trees store bag) after) :
    ∃ finalStore finalBag, SharedStep rule store bag finalStore finalBag ∧ trees finalStore finalBag = after := by
  classical
  obtain ⟨assignmentT, frameT, _, keptT, made, only, ⟨takenT, takes, rfl⟩,
    ⟨readT, reads, keptBound, covered⟩, before, checked, produced, rfl⟩ := step
  obtain ⟨first, kept, splitKept, firstTrees, keptTrees⟩ := map_eq_add (unfold store) _ bag _ before
  obtain ⟨frame, consumed, splitTaken, frameTrees, takenTrees⟩ := map_eq_add (unfold store) _ first _ firstTrees
  obtain ⟨taken, takenBag, takenValues⟩ := exists_list_of_map (unfold store) takenT consumed takenTrees
  obtain ⟨extra, readsBag⟩ := Multiset.le_iff_exists_add.mp keptBound
  have extraKept : ∀ t ∈ extra, t ∈ keptT := by
    intro t member
    apply covered t
    rw [← Multiset.mem_coe, readsBag]
    exact Multiset.mem_add.mpr (Or.inr member)
  let pick : Term Head → Ref := fun t =>
    if found : ∃ r ∈ kept, unfold store r = t then found.choose else ⟨[], 0⟩
  have pick_correct : ∀ t ∈ keptT, pick t ∈ kept ∧ unfold store (pick t) = t := by
    intro t member
    have found : ∃ r ∈ kept, unfold store r = t := by
      rw [← keptTrees] at member
      exact Multiset.mem_map.mp member
    simp only [pick, dif_pos found]
    exact found.choose_spec
  have selectedReads : (kept + extra.map pick).map (unfold store) = (readT : Multiset (Term Head)) := by
    rw [Multiset.map_add, keptTrees, Multiset.map_map, readsBag]
    congr 1
    conv_rhs => rw [← Multiset.map_id extra]
    exact Multiset.map_congr rfl fun t member => (pick_correct t (extraKept t member)).2
  obtain ⟨read, readBag, readValues⟩ := exists_list_of_map (unfold store) readT _ selectedReads
  have keptBoundR : kept ≤ (read : Multiset Ref) := by rw [readBag]; exact Multiset.le_add_right _ _
  have readKept : ∀ r ∈ read, r ∈ kept := by
    intro r member
    rw [← Multiset.mem_coe, readBag] at member
    rcases Multiset.mem_add.mp member with member | member
    · exact member
    · obtain ⟨t, selected, rfl⟩ := Multiset.mem_map.mp member
      exact (pick_correct t (extraKept t selected)).1
  have beforeRefs : bag = frame + taken + kept := by rw [splitKept, splitTaken, takenBag]
  have frameValid : ∀ r ∈ frame, CanonRef store r := fun r member =>
    validBag r (by rw [beforeRefs]; simp [member])
  have keptValid : ∀ r ∈ kept, CanonRef store r := fun r member =>
    validBag r (by rw [beforeRefs]; simp [member])
  have gathersValid : ∀ r ∈ taken ++ read, CanonRef store r := by
    intro r member
    rcases List.mem_append.mp member with member | member
    · exact validBag r (by rw [beforeRefs]; simp [member])
    · exact keptValid r (readKept r member)
  obtain ⟨grows, matchCanonical, assignments, matchExact⟩ := matchListContextR_spec
    (rule.take ++ rule.read) store (fun _ => none) (taken ++ read) canonical
    (by intro v r impossible; cases impossible) gathersValid
  rw [unfoldSubst_none, List.map_append, takenValues, readValues] at matchExact
  have matchedT : matchList? (rule.take ++ rule.read) (fun _ => none) (takenT ++ readT) = some assignmentT :=
    (matchList_exact _ _ _ _ input.1).mpr
      ((stepChain_empty_iff _ _ _ _).mpr ⟨only, List.rel_append takes reads⟩)
  rw [matchedT] at matchExact
  generalize matched : matchListContextR (rule.take ++ rule.read) store (fun _ => none) (taken ++ read) =
    matchResult at grows matchCanonical assignments matchExact
  obtain ⟨matchStore, matchResult⟩ := matchResult
  dsimp only at grows matchCanonical assignments matchExact
  cases matchResult with
  | none => simp at matchExact
  | some assignment =>
    have assignmentValid := assignments assignment rfl
    have assignmentTrees : unfoldSubst matchStore assignment = assignmentT := by simpa using matchExact
    obtain ⟨more, finalCanonical, results, outputExact⟩ :=
      instantiateTemplatesR_spec rule.produce matchStore matchCanonical assignment assignmentValid
    rw [assignmentTrees, produced] at outputExact
    generalize built : instantiateTemplatesR rule.produce matchStore assignment = builtResult at more finalCanonical results outputExact
    obtain ⟨finalStore, builtResult⟩ := builtResult
    dsimp only at more finalCanonical results outputExact
    cases builtResult with
    | none => simp at outputExact
    | some madeR =>
      have outputValues : madeR.map (unfold finalStore) = made := by simpa using outputExact
      refine ⟨finalStore, frame + kept + madeR,
        ⟨matchStore, assignment, frame, kept, taken, read, madeR, ?_, beforeRefs, keptBoundR,
          readKept, matched, ?_, built, rfl⟩, ?_⟩
      · rw [← List.length_map (unfold store), takenValues]
        exact takes.length_eq.symm
      · intro check member
        rw [matchesIn_contextual_shared matchCanonical assignmentValid check.pattern (input.2 check member)
          (fun r m => (validBag r m).prefix grows), assignmentTrees]
        rw [show bag.map (unfold matchStore) = trees store bag from trees_prefix canonical.topo grows validBag]
        exact checked check member
      · simp only [trees, Multiset.map_add, Multiset.map_coe, outputValues]
        rw [← frameTrees, ← keptTrees]
        congr 2
        · exact Multiset.map_congr rfl fun r member =>
            unfold_prefix canonical.topo (grows.trans more) (frameValid r member).valid
        · exact Multiset.map_congr rfl fun r member =>
            unfold_prefix canonical.topo (grows.trans more) (keptValid r member).valid

namespace InputControls

theorem compound_output_does_not_restrict_rule_input : ruleInputCheck Controls.specialize = true := by decide

def repeatedInput : Rule Nat (Term Nat) (Pattern Nat Nat) :=
  { take := [], read := [Controls.hole 1 2 [.idx 0, .idx 0]], checks := [], produce := [] }

theorem repeated_input_not_in_unique_fragment : ruleInputCheck repeatedInput = false := by decide

end InputControls

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns
