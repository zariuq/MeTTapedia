import Mettapedia.Machines.RootRetirementLedger
import Mettapedia.GSLT.Dynamics.RegionInformationCoding
import Mathlib.Data.Fintype.Powerset

/-!
# Information needed by identity-specific root retirement

For one address, let its state be the finite set of root identities which
reach it. A future question retires any chosen identities and asks whether
the address remains live. These questions distinguish every contributor set.
An old mark or cardinality alone is insufficient. With n independently
retirable roots the exact fixed-width interface requires n bits.

This is a summary-alone lower bound, not a demand for a per-object bitmap.
A shared root-to-support index supplies side information: with its checked
retirement contribution, a scalar count updates exactly. The ledger realizes
that distributed interface, so the lower bound does not prescribe its layout.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.RootRetirementInformation

open RegionObservations
open Mettapedia.Machines.RootRetirementLedger

universe u
variable {Root : Type u} [DecidableEq Root]

def survives (retired contributors : Finset Root) : Bool :=
  decide ((contributors \ retired).Nonempty)

def futures (Root : Type u) [DecidableEq Root] : Family (Finset Root) where
  Question := Finset Root
  Answer _ := Bool
  read := survives

theorem survives_false_iff (retired contributors : Finset Root) :
    survives retired contributors = false ↔ contributors ⊆ retired := by
  simp [survives, Finset.sdiff_nonempty]

/-- Retiring all of either set is a distinguishing continuation if they differ. -/
theorem equivalent_iff (left right : Finset Root) :
    (futures Root).Equivalent left right ↔ left = right := by
  constructor
  · intro same
    change ∀ retired, survives retired left = survives retired right at same
    have leftGone : survives left right = false := by
      rw [← same left]
      simp [survives]
    have rightGone : survives right left = false := by
      rw [same right]
      simp [survives]
    exact Finset.Subset.antisymm ((survives_false_iff right left).mp rightGone)
      ((survives_false_iff left right).mp leftGone)
  · rintro rfl
    intro _
    rfl

theorem identity_exact : (futures Root).Exact (id : Finset Root → Finset Root) := by
  intro left right
  exact (equivalent_iff left right).symm

theorem sufficient_iff_injective {Code : Type*} (summary : Finset Root → Code) :
    (futures Root).Sufficient summary ↔ Function.Injective summary := by
  constructor
  · intro enough left right same
    exact (equivalent_iff left right).mp (enough left right same)
  · intro injective left right same
    exact (equivalent_iff left right).mpr (injective same)

theorem class_count [Fintype Root] :
    Nat.card (futures Root).Classes = 2 ^ Fintype.card Root := by
  have injective : Function.Injective (futures Root).classOf := by
    intro left right same
    exact (equivalent_iff left right).mp (((futures Root).classOf_eq_iff left right).mp same)
  have onto : Function.Surjective (futures Root).classOf := by
    intro cls
    induction cls using Quotient.inductionOn with
    | h state => exact ⟨state, rfl⟩
  have equal := Nat.card_congr (Equiv.ofBijective _ ⟨injective, onto⟩)
  simpa using equal.symm

theorem required_bits [Fintype Root] :
    RegionInformationCoding.requiredBits (futures Root) = Fintype.card Root := by
  rw [RegionInformationCoding.requiredBits, class_count, Nat.clog_pow 2 _ (by decide)]

theorem sufficient_word_iff [Fintype Root] (bits : Nat) :
    (∃ summary : Finset Root → Mettapedia.InformationTheory.FiniteInterfaceCoding.Word bits,
      (futures Root).Sufficient summary) ↔ Fintype.card Root ≤ bits := by
  rw [RegionInformationCoding.sufficient_bits_iff, required_bits]

/-- Exact side information permits a scalar update instead of reconstructing
the contributor set at the cell. Removed identities are intersected with the
active domain, so duplicate retirement cannot decrement twice. -/
theorem ledger_answers_future {Address : Type*} [DecidableEq Address]
    (ledger : Ledger Root Address) (consistent : Consistent ledger)
    (retired : Finset Root) (address : Address) :
    decide (0 < (retire ledger retired).count address) =
      survives retired (contributors ledger.support ledger.active address) := by
  rw [retire_consistent ledger consistent retired address]
  simp [survives, Finset.card_pos, contributors_sdiff, retire]

namespace Controls

theorem equal_counts_have_different_retirement_answers :
    ({false} : Finset Bool).card = ({true} : Finset Bool).card ∧
      survives {false} ({false} : Finset Bool) ≠ survives {false} ({true} : Finset Bool) := by
  decide +kernel

theorem count_alone_insufficient : ¬ (futures Bool).Sufficient Finset.card := by
  intro enough
  have same := (sufficient_iff_injective Finset.card).mp enough
    equal_counts_have_different_retirement_answers.1
  have impossible : ({false} : Finset Bool) ≠ {true} := by decide
  exact impossible same

theorem old_mark_alone_insufficient :
    ¬ (futures Bool).Sufficient (fun roots => decide roots.Nonempty) := by
  intro enough
  have same := (sufficient_iff_injective (fun roots : Finset Bool => decide roots.Nonempty)).mp
    enough (show decide ({false} : Finset Bool).Nonempty = decide ({true} : Finset Bool).Nonempty by decide)
  have impossible : ({false} : Finset Bool) ≠ {true} := by decide
  exact impossible same

theorem two_independent_roots_need_two_bits :
    RegionInformationCoding.requiredBits (futures Bool) = 2 := by
  rw [required_bits]
  rfl

end Controls
end Mettapedia.GSLT.Dynamics.RootRetirementInformation
