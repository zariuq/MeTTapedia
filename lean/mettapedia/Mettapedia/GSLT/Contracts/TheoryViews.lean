import Mettapedia.GSLT.Contracts.CanonicalSuccessorClasses
import Mathlib.Data.Rat.Defs

/-!
# Boundaries between equational views

A term may have several legitimate views: raw syntax for quotation,
a quotient for matching in one space, and an explicitly selected
operation for a Boolean comparison. Changing the comparison does not
change the quotient. A boundary between quotients is licensed by its
translation on raw terms, not by a global equality on pointers or names.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.TheoryViews

open Mettapedia.GSLT.Contracts.CanonicalSuccessorClasses (NormalForms)

universe u v w

variable {Raw : Type u} {Target : Type v} {Answer : Type w}

/-- The exact condition for an observation to forget spelling. -/
def Stable (equations : Setoid Raw) (observe : Raw → Answer) : Prop :=
  ∀ ⦃a b⦄, equations.r a b → observe a = observe b

theorem factors_iff_stable (equations : Setoid Raw) (observe : Raw → Answer) :
    (∃! view : Quotient equations → Answer, ∀ a, view (Quotient.mk equations a) = observe a) ↔
      Stable equations observe := by
  constructor
  · rintro ⟨view, commute, _⟩ a b same
    rw [← commute a, ← commute b, Quotient.sound (s := equations) same]
  · intro stable
    refine ⟨Quotient.lift observe (fun _ _ same => stable same), fun _ => rfl, ?_⟩
    intro other commute
    funext key
    induction key using Quotient.inductionOn with
    | _ a => exact commute a

section Boundary

variable (source : Setoid Raw) (target : Setoid Target) (translate : Raw → Target)

/-- Transport need not be injective, but must respect everything the
source has already forgotten. -/
abbrev Compatible : Prop := Stable source (fun raw => Quotient.mk target (translate raw))

def transfer (compatible : Compatible source target translate) : Quotient source → Quotient target :=
  Quotient.lift (fun raw => Quotient.mk target (translate raw))
    (fun _ _ same => compatible same)

theorem transfer_exists_iff :
    (∃! send : Quotient source → Quotient target,
      ∀ raw, send (Quotient.mk source raw) = Quotient.mk target (translate raw)) ↔
      ∀ ⦃a b⦄, source.r a b → target.r (translate a) (translate b) := by
  rw [factors_iff_stable]
  exact ⟨fun compat _ _ same => Quotient.exact (s := target) (compat same),
    fun preserves _ _ same => Quotient.sound (s := target) (preserves same)⟩

theorem transfer_injective_iff (compatible : Compatible source target translate) :
    Function.Injective (transfer source target translate compatible) ↔
      ∀ ⦃a b⦄, target.r (translate a) (translate b) → source.r a b := by
  constructor
  · intro reflects a b same
    exact Quotient.exact (s := source) (reflects (Quotient.sound (s := target) same))
  · intro reflects first second same
    induction first using Quotient.inductionOn with
    | _ a =>
      induction second using Quotient.inductionOn with
      | _ b =>
          exact Quotient.sound (s := source) (reflects (Quotient.exact (s := target) same))

theorem transfer_surjective_iff (compatible : Compatible source target translate) :
    Function.Surjective (transfer source target translate compatible) ↔
      ∀ value, ∃ a, target.r (translate a) value := by
  constructor
  · intro onto value
    obtain ⟨key, equal⟩ := onto (Quotient.mk target value)
    induction key using Quotient.inductionOn with
    | _ a => exact ⟨a, Quotient.exact (s := target) equal⟩
  · intro covers key
    induction key using Quotient.inductionOn with
    | _ value =>
        obtain ⟨a, same⟩ := covers value
        exact ⟨Quotient.mk source a, Quotient.sound (s := target) same⟩

theorem transfer_composes {Last : Type w} (last : Setoid Last) (thenSend : Target → Last)
    (first : Compatible source target translate) (second : Compatible target last thenSend)
    (both : Compatible source last (thenSend ∘ translate)) (key : Quotient source) :
    transfer target last thenSend second (transfer source target translate first key) =
      transfer source last (thenSend ∘ translate) both key := by
  induction key using Quotient.inductionOn with
  | _ a => rfl

end Boundary

section Comparison

variable {equations : Setoid Raw} (forms : NormalForms equations)

/-- A bound Boolean operation can be lowered to canonical-key equality
exactly when it decides this declared relation. The spelling of the
operation's name is irrelevant to that licence. -/
theorem compares_by_key_iff [DecidableEq forms.Key] (compare : Raw → Raw → Bool) :
    (∀ a b, compare a b = decide (forms.key a = forms.key b)) ↔
      ∀ a b, compare a b = true ↔ equations.r a b := by
  constructor
  · intro lowers a b
    rw [lowers, decide_eq_true_eq, forms.key_eq_iff]
  · intro decides a b
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq, forms.key_eq_iff] using decides a b

end Comparison

section Occurrences

variable {Id : Type v} {equations : Setoid Raw} (forms : NormalForms equations)

/-- Put keys beside the occurrences. There is no deduplication in this
operation, even if all their payloads have one key. -/
def keyedWord (word : List (Id × Raw)) : List (Id × forms.Key) :=
  word.map fun entry => (entry.1, forms.key entry.2)

@[simp] theorem keyedWord_ids (word : List (Id × Raw)) :
    (keyedWord forms word).map Prod.fst = word.map Prod.fst := by
  simp [keyedWord, List.map_map, Function.comp_def]

theorem keyedWord_selects [DecidableEq forms.Key] [DecidableRel equations.r]
    (word : List (Id × Raw)) (query : Raw) :
    ((keyedWord forms word).filter (fun row => decide (row.2 = forms.key query))).map Prod.fst =
      (word.filter (fun row => decide (equations.r row.2 query))).map Prod.fst := by
  induction word with
  | nil => rfl
  | cons row rest ih =>
      change (((row.1, forms.key row.2) :: keyedWord forms rest).filter
        (fun entry => decide (entry.2 = forms.key query))).map Prod.fst =
        ((row :: rest).filter (fun entry => decide (equations.r entry.2 query))).map Prod.fst
      by_cases agrees : equations.r row.2 query
      · have keyEq := forms.key_eq_iff.mpr agrees
        simp [agrees, keyEq, ih]
      · have keyNe : forms.key row.2 ≠ forms.key query :=
          fun eq => agrees (forms.key_eq_iff.mp eq)
        simp [agrees, keyNe, ih]

end Occurrences

namespace Controls

/-- The finite portion of two numeric spellings. The dyadic case
denotes its exact binary rational, not a rounded decimal rendering. -/
inductive Literal where
  | integer (value : Int)
  | dyadic (mantissa : Int) (fractionBits : Nat)
  deriving DecidableEq

def value : Literal → Rat
  | .integer n => n
  | .dyadic m bits => Rat.divInt m ((2 : Int) ^ bits)

def exactNumbers : Setoid Literal := Setoid.ker value
def spelling : Setoid Literal := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩

theorem same_value_distinct_spelling :
    exactNumbers.r (.integer 1) (.dyadic 2 1) ∧
      ¬ spelling.r (.integer 1) (.dyadic 2 1) := by
  constructor
  · change value (.integer 1) = value (.dyadic 2 1)
    decide +kernel
  · intro eq
    cases eq

/-- Materializing only a numeric key cannot later restore the
original spelling for a literal-space import or for quotation. -/
theorem spelling_cannot_be_recovered :
    ¬ (∃ restore : Quotient exactNumbers → Literal,
      ∀ atom, restore (Quotient.mk exactNumbers atom) = atom) := by
  rintro ⟨restore, roundTrip⟩
  have same := congrArg restore (Quotient.sound (s := exactNumbers) same_value_distinct_spelling.1)
  exact same_value_distinct_spelling.2 ((roundTrip _).symm.trans (same.trans (roundTrip _)))

/-- A perfectly usable comparison need not be a key equality: an
epsilon threshold is not transitive. -/
theorem near_comparison_has_no_keys {Key : Type*} :
    ¬ ∃ key : Int → Key, ∀ a b, key a = key b ↔ (a - b).natAbs ≤ 1 := by
  rintro ⟨key, exact⟩
  have close₁ := (exact 0 1).mpr (by decide)
  have close₂ := (exact 1 2).mpr (by decide)
  exact (by decide : ¬ ((0 : Int) - 2).natAbs ≤ 1) ((exact 0 2).mp (close₁.trans close₂))

end Controls

#print axioms factors_iff_stable
#print axioms transfer_exists_iff
#print axioms transfer_injective_iff
#print axioms transfer_surjective_iff
#print axioms compares_by_key_iff
#print axioms keyedWord_selects
#print axioms Controls.same_value_distinct_spelling
#print axioms Controls.spelling_cannot_be_recovered
#print axioms Controls.near_comparison_has_no_keys

end Mettapedia.GSLT.Contracts.TheoryViews
