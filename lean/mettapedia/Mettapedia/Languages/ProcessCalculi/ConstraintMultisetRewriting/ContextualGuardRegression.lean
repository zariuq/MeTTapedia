import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalGuards
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Exactness

/-!
# Original guard observations regress through a known occurrence update

The existing occurrence-query exactness law applies to conditional matching,
including latent row equations. Retained input rows need agree only outside
the removed set. Absence checks both surviving inputs and created rows;
counts subtract matching removals and add matching creations.

These formulas use explicit finite row data, not a source evaluator. Their
native expression and query-admission bridge remain separate obligations;
this module supplies neither a total higher-order matcher nor an algorithm
for deciding arbitrary all-future guards.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardRegression

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConditionalRows ContextualConditionalGuards
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {Local Other Shared Next O : Type} [DecidableEq O]
    (locals : Local → MetaArity S) (others : Other → MetaArity S)
    {captures : Shared → MetaArity S} {next : Next → MetaArity S}
    {Γ : Ctx S} {sort : S.Srt}

private noncomputable def queryRegion (candidate : Assignment captures next)
    (rows : O → Row locals captures Γ sort) (pattern : Term (signature S captures) Γ sort) : O → Bool := by
  classical
  exact fun occurrence => decide (Matches locals captures candidate (instantiate candidate pattern) (rows occurrence))

omit [DecidableEq O] in
private theorem region_as_query (candidate : Assignment captures next) (rows : O → Row locals captures Γ sort)
    (world : Finset O) (pattern : Term (signature S captures) Γ sort) :
    region locals candidate rows world pattern = regionOf id world (queryRegion locals candidate rows pattern) := by
  classical
  ext occurrence
  simp [mem_region, mem_regionOf, queryRegion]

theorem region_sdiff (candidate : Assignment captures next) (rows : O → Row locals captures Γ sort)
    (world removed : Finset O) (pattern : Term (signature S captures) Γ sort) :
    region locals candidate rows (world \ removed) pattern =
      region locals candidate rows world pattern \ region locals candidate rows removed pattern := by
  classical
  ext occurrence
  simp only [mem_region, Finset.mem_sdiff]
  tauto

/-- Reuses occurrence-commit query exactness, rather than a separate update algebra. -/
theorem region_delta (candidate : Assignment captures next) (rows : O → Row locals captures Γ sort)
    (world removed created : Finset O) (pattern : Term (signature S captures) Γ sort) :
    region locals candidate rows ((world \ removed) ∪ created) pattern =
      (region locals candidate rows world pattern \ region locals candidate rows removed pattern) ∪
        region locals candidate rows created pattern := by
  let delta : Commit O O := ⟨removed, ∅, created, []⟩
  have original := regionOf_fire id world delta (queryRegion locals candidate rows pattern)
  change regionOf id ((world \ removed) ∪ created) _ = (regionOf id world _ \ regionOf id removed _) ∪ regionOf id created _ at original
  simpa only [← region_as_query] using original

omit [DecidableEq O] in
theorem region_congr_on (candidate : Assignment captures next)
    (entryRows : O → Row locals captures Γ sort) (exitRows : O → Row others captures Γ sort)
    (world : Finset O) (pattern : Term (signature S captures) Γ sort)
    (agree : ∀ occurrence ∈ world,
      Matches locals captures candidate (instantiate candidate pattern) (entryRows occurrence) ↔
        Matches others captures candidate (instantiate candidate pattern) (exitRows occurrence)) :
    region locals candidate entryRows world pattern = region others candidate exitRows world pattern := by
  classical
  ext occurrence
  simp only [mem_region]
  exact and_congr_right (agree occurrence)

omit [DecidableEq O] in
theorem region_image_of_matches {Physical : Type} [DecidableEq Physical]
    (name : O → Physical) (candidate : Assignment captures next)
    (rows : O → Row locals captures Γ sort) (represented : Physical → Row others captures Γ sort)
    (world : Finset O) (pattern : Term (signature S captures) Γ sort)
    (agree : ∀ occurrence ∈ world,
      Matches locals captures candidate (instantiate candidate pattern) (rows occurrence) ↔
        Matches others captures candidate (instantiate candidate pattern) (represented (name occurrence))) :
    region others candidate represented (world.image name) pattern =
      (region locals candidate rows world pattern).image name := by
  classical
  ext physical
  constructor
  · intro member
    obtain ⟨present, matched⟩ := (mem_region _ _ _ _ _ _).mp member
    obtain ⟨occurrence, inside, rfl⟩ := Finset.mem_image.mp present
    exact Finset.mem_image.mpr ⟨occurrence,
      (mem_region _ _ _ _ _ _).mpr ⟨inside, (agree occurrence inside).mpr matched⟩, rfl⟩
  · intro member
    obtain ⟨occurrence, matched, rfl⟩ := Finset.mem_image.mp member
    obtain ⟨inside, matched⟩ := (mem_region _ _ _ _ _ _).mp matched
    exact (mem_region _ _ _ _ _ _).mpr ⟨Finset.mem_image_of_mem name inside, (agree occurrence inside).mp matched⟩

omit [DecidableEq O] in
theorem holds_image_of_matches {Physical : Type} [DecidableEq Physical]
    (name : O → Physical) (injective : Function.Injective name) (candidate : Assignment captures next)
    (rows : O → Row locals captures Γ sort) (represented : Physical → Row others captures Γ sort)
    (world : Finset O)
    (agree : ∀ pattern occurrence, occurrence ∈ world →
      (Matches locals captures candidate (instantiate candidate pattern) (rows occurrence) ↔
        Matches others captures candidate (instantiate candidate pattern) (represented (name occurrence))))
    (check : Check (Term (signature S captures) Γ sort)) :
    Holds others candidate represented (world.image name) check ↔ Holds locals candidate rows world check := by
  cases check with
  | equal _ _ => rfl
  | absent pattern =>
      constructor
      · intro absent occurrence inside matched
        exact absent (name occurrence) (Finset.mem_image_of_mem name inside) ((agree pattern occurrence inside).mp matched)
      · intro absent physical present matched
        obtain ⟨occurrence, inside, rfl⟩ := Finset.mem_image.mp present
        exact absent occurrence inside ((agree pattern occurrence inside).mpr matched)
  | count pattern number =>
      rw [Holds, Holds, region_image_of_matches locals others name candidate rows represented world pattern (agree pattern),
        Finset.card_image_of_injective _ injective]

theorem region_after_retained (candidate : Assignment captures next)
    (entryRows : O → Row locals captures Γ sort) (exitRows : O → Row others captures Γ sort)
    (world removed created : Finset O) (pattern : Term (signature S captures) Γ sort)
    (agree : ∀ occurrence ∈ world, occurrence ∉ removed →
      (Matches locals captures candidate (instantiate candidate pattern) (entryRows occurrence) ↔
        Matches others captures candidate (instantiate candidate pattern) (exitRows occurrence))) :
    region others candidate exitRows ((world \ removed) ∪ created) pattern =
      (region locals candidate entryRows world pattern \ region locals candidate entryRows removed pattern) ∪
        region others candidate exitRows created pattern := by
  rw [region_delta, ← region_sdiff]
  have retained := region_congr_on locals others candidate entryRows exitRows (world \ removed) pattern
    (fun occurrence member => agree occurrence (Finset.mem_sdiff.mp member).1 (Finset.mem_sdiff.mp member).2)
  rw [← retained, region_sdiff]

theorem count_after_retained (candidate : Assignment captures next)
    (entryRows : O → Row locals captures Γ sort) (exitRows : O → Row others captures Γ sort)
    (world removed created : Finset O) (pattern : Term (signature S captures) Γ sort)
    (taken : removed ⊆ world) (fresh : Disjoint created world)
    (agree : ∀ occurrence ∈ world, occurrence ∉ removed →
      (Matches locals captures candidate (instantiate candidate pattern) (entryRows occurrence) ↔
        Matches others captures candidate (instantiate candidate pattern) (exitRows occurrence))) :
    (region others candidate exitRows ((world \ removed) ∪ created) pattern).card =
      (region locals candidate entryRows world pattern).card -
        (region locals candidate entryRows removed pattern).card +
          (region others candidate exitRows created pattern).card := by
  classical
  have subset : region locals candidate entryRows removed pattern ⊆ region locals candidate entryRows world pattern := by
    intro occurrence member
    obtain ⟨inside, matched⟩ := (mem_region _ _ _ _ _ _).mp member
    exact (mem_region _ _ _ _ _ _).mpr ⟨taken inside, matched⟩
  have apart : Disjoint
      (region locals candidate entryRows world pattern \ region locals candidate entryRows removed pattern)
      (region others candidate exitRows created pattern) := by
    apply Finset.disjoint_left.mpr
    intro occurrence old new
    exact Finset.disjoint_left.mp fresh ((mem_region _ _ _ _ _ _).mp new).1
      ((mem_region _ _ _ _ _ _).mp (Finset.mem_sdiff.mp old).1).1
  rw [region_after_retained locals others candidate entryRows exitRows world removed created pattern agree,
    Finset.card_union_of_disjoint apart, Finset.card_sdiff_of_subset subset]

def entryCondition (candidate : Assignment captures next)
    (entryRows : O → Row locals captures Γ sort) (exitRows : O → Row others captures Γ sort)
    (world removed created : Finset O) : Check (Term (signature S captures) Γ sort) → Prop
  | .equal first second => instantiate candidate first = instantiate candidate second
  | .absent pattern =>
      (∀ occurrence ∈ world, occurrence ∉ removed →
        ¬ Matches locals captures candidate (instantiate candidate pattern) (entryRows occurrence)) ∧
      (∀ occurrence ∈ created,
        ¬ Matches others captures candidate (instantiate candidate pattern) (exitRows occurrence))
  | .count pattern number =>
      (region locals candidate entryRows world pattern).card -
        (region locals candidate entryRows removed pattern).card +
          (region others candidate exitRows created pattern).card = number

/-- Equality, absence and count are regressed pointwise under the same candidate assignment. -/
theorem holds_after_iff (candidate : Assignment captures next)
    (entryRows : O → Row locals captures Γ sort) (exitRows : O → Row others captures Γ sort)
    (world removed created : Finset O) (check : Check (Term (signature S captures) Γ sort))
    (taken : removed ⊆ world) (fresh : Disjoint created world)
    (agree : ∀ pattern occurrence, occurrence ∈ world → occurrence ∉ removed →
      (Matches locals captures candidate (instantiate candidate pattern) (entryRows occurrence) ↔
        Matches others captures candidate (instantiate candidate pattern) (exitRows occurrence))) :
    Holds others candidate exitRows ((world \ removed) ∪ created) check ↔
      entryCondition locals others candidate entryRows exitRows world removed created check := by
  cases check with
  | equal _ _ => rfl
  | count pattern number =>
      change (region others candidate exitRows ((world \ removed) ∪ created) pattern).card = number ↔ _
      rw [count_after_retained locals others candidate entryRows exitRows world removed created pattern taken fresh
        (fun occurrence member outside => agree pattern occurrence member outside)]
      rfl
  | absent pattern =>
      constructor
      · intro absent
        refine ⟨?_, ?_⟩
        · intro occurrence member outside matched
          exact absent occurrence (Finset.mem_union.mpr (.inl (Finset.mem_sdiff.mpr ⟨member, outside⟩)))
            ((agree pattern occurrence member outside).mp matched)
        · intro occurrence made
          exact absent occurrence (Finset.mem_union.mpr (.inr made))
      · rintro ⟨surviving, made⟩ occurrence member matched
        rcases Finset.mem_union.mp member with old | new
        · obtain ⟨inside, outside⟩ := Finset.mem_sdiff.mp old
          exact surviving occurrence inside outside ((agree pattern occurrence inside outside).mpr matched)
        · exact made occurrence new matched

/-- The regressed formulas retain every solution at the original information cut. -/
theorem ask_after_iff (problem : ContextualResidual.Problem captures)
    (entryRows : O → Row locals captures Γ sort) (exitRows : O → Row others captures Γ sort)
    (world removed created : Finset O) (check : Check (Term (signature S captures) Γ sort))
    (taken : removed ⊆ world) (fresh : Disjoint created world)
    (agree : ∀ (Future : Type) (future : Future → MetaArity S) (candidate : Assignment captures future),
      ContextualResidual.Models candidate problem → ∀ pattern occurrence, occurrence ∈ world → occurrence ∉ removed →
        (Matches locals captures candidate (instantiate candidate pattern) (entryRows occurrence) ↔
          Matches others captures candidate (instantiate candidate pattern) (exitRows occurrence))) :
    Ask others problem exitRows ((world \ removed) ∪ created) check ↔
      ∀ (Future : Type) (future : Future → MetaArity S) (candidate : Assignment captures future),
        ContextualResidual.Models candidate problem →
          entryCondition locals others candidate entryRows exitRows world removed created check := by
  constructor <;> intro observed Future future candidate model
  · exact (holds_after_iff locals others candidate entryRows exitRows world removed created check taken fresh
      (agree Future future candidate model)).mp (observed Future future candidate model)
  · exact (holds_after_iff locals others candidate entryRows exitRows world removed created check taken fresh
      (agree Future future candidate model)).mpr (observed Future future candidate model)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardRegression
