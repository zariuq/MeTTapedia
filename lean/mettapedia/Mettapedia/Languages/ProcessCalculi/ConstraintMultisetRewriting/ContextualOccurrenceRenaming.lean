import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalGuards

/-!
# Conditional guard observations under an injective occurrence renaming

Only live occurrences must have corresponding conditional rows. Matching
still retains every row's latent equations and caller references. The
physical image preserves absence and occurrence counts, rather than
identifying rows with equal values or relying on a ground matcher.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualOccurrenceRenaming

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConditionalRows ContextualConditionalGuards

variable {S : Signature} {Local Shared Next O P : Type} [DecidableEq P]
    (locals : Local → MetaArity S) {captures : Shared → MetaArity S} {next : Next → MetaArity S}
    {Γ : Ctx S} {sort : S.Srt}

theorem region_image (name : O → P) (candidate : Assignment captures next)
    (rows : O → Row locals captures Γ sort) (represented : P → Row locals captures Γ sort)
    (world : Finset O) (agrees : ∀ occurrence ∈ world, represented (name occurrence) = rows occurrence)
    (pattern : Term (signature S captures) Γ sort) :
    region locals candidate represented (world.image name) pattern =
      (region locals candidate rows world pattern).image name := by
  classical
  ext physical
  constructor
  · intro member
    obtain ⟨present, matched⟩ := (mem_region locals candidate represented (world.image name) pattern physical).mp member
    obtain ⟨occurrence, sourcePresent, rfl⟩ := Finset.mem_image.mp present
    rw [agrees occurrence sourcePresent] at matched
    exact Finset.mem_image.mpr ⟨occurrence, (mem_region locals candidate rows world pattern occurrence).mpr
      ⟨sourcePresent, matched⟩, rfl⟩
  · intro member
    obtain ⟨occurrence, matched, rfl⟩ := Finset.mem_image.mp member
    obtain ⟨present, matched⟩ := (mem_region locals candidate rows world pattern occurrence).mp matched
    apply (mem_region locals candidate represented (world.image name) pattern (name occurrence)).mpr
    exact ⟨Finset.mem_image_of_mem name present, (agrees occurrence present).symm ▸ matched⟩

/-- Physical injectivity is essential for preserving occurrence counts. -/
theorem holds_iff (name : O → P) (injective : Function.Injective name) (candidate : Assignment captures next)
    (rows : O → Row locals captures Γ sort) (represented : P → Row locals captures Γ sort)
    (world : Finset O) (agrees : ∀ occurrence ∈ world, represented (name occurrence) = rows occurrence)
    (check : Check (Term (signature S captures) Γ sort)) :
    Holds locals candidate represented (world.image name) check ↔ Holds locals candidate rows world check := by
  cases check with
  | equal _ _ => rfl
  | absent pattern =>
      constructor
      · intro absent occurrence present matched
        exact absent (name occurrence) (Finset.mem_image_of_mem name present)
          ((agrees occurrence present).symm ▸ matched)
      · intro absent physical present matched
        obtain ⟨occurrence, sourcePresent, rfl⟩ := Finset.mem_image.mp present
        exact absent occurrence sourcePresent (agrees occurrence sourcePresent ▸ matched)
  | count pattern cardinality =>
      rw [Holds, Holds, region_image locals name candidate rows represented world agrees pattern,
        Finset.card_image_of_injective _ injective]

/-- Every future model sees the same guard at the same information cut. -/
theorem ask_iff (name : O → P) (injective : Function.Injective name)
    (problem : ContextualResidual.Problem captures)
    (rows : O → Row locals captures Γ sort) (represented : P → Row locals captures Γ sort)
    (world : Finset O) (agrees : ∀ occurrence ∈ world, represented (name occurrence) = rows occurrence)
    (check : Check (Term (signature S captures) Γ sort)) :
    Ask locals problem represented (world.image name) check ↔ Ask locals problem rows world check := by
  constructor <;> intro asked Future future candidate model
  · exact (holds_iff locals name injective candidate rows represented world agrees check).mp
      (asked Future future candidate model)
  · exact (holds_iff locals name injective candidate rows represented world agrees check).mpr
      (asked Future future candidate model)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualOccurrenceRenaming
