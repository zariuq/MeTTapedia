import Mettapedia.SetTheory.Profiles.Diaconescu

/-!
# Witness-bearing choice and extensional selectors

The dependent product/sum rearrangement below computes a function and its
evidence from supplied witnesses. It neither extracts witnesses from
propositional existence nor requires compatibility with an extensional
identification of the index presentation. The finite control retains two
occurrences of the same material key and makes that compatibility fail.

The extensional-selector comparison uses exactly the hypotheses of the
existing pair-subset Diaconescu theorem. Countable and dependent choice are
not assigned that conclusion. A universal set is also incompatible with the
single Russell Separation instance, already a bounded predicate.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ProfileChoice

universe u v w

variable {A : Type u} {B : A → Type v} {Evidence : (a : A) → B a → Type w}

/-- Rearrange supplied witnesses, retaining all dependent evidence. -/
def piSigmaChoice (witnesses : (a : A) → Σ b : B a, Evidence a b) :
    Σ chosen : (a : A) → B a, (a : A) → Evidence a (chosen a) :=
  ⟨fun a => (witnesses a).1, fun a => (witnesses a).2⟩

/-- Recover the individual witnesses from the chosen function and evidence. -/
def sigmaPiWitnesses (selected : Σ chosen : (a : A) → B a,
    (a : A) → Evidence a (chosen a)) : (a : A) → Σ b : B a, Evidence a b :=
  fun a => ⟨selected.1 a, selected.2 a⟩

/-- The usual propositional statement follows from the computed rearrangement;
its premise is still a function of actual Sigma witnesses. -/
theorem piSigmaChoice_exists (witnesses : (a : A) → Σ b : B a, Evidence a b) :
    ∃ chosen : (a : A) → B a, Nonempty ((a : A) → Evidence a (chosen a)) :=
  ⟨(piSigmaChoice witnesses).1, ⟨(piSigmaChoice witnesses).2⟩⟩

theorem piSigmaChoice_value (witnesses : (a : A) → Σ b : B a, Evidence a b) (a : A) :
    (piSigmaChoice witnesses).1 a = (witnesses a).1 := rfl

theorem piSigmaChoice_evidence (witnesses : (a : A) → Σ b : B a, Evidence a b) (a : A) :
    (piSigmaChoice witnesses).2 a = (witnesses a).2 := rfl

theorem witnesses_roundTrip (witnesses : (a : A) → Σ b : B a, Evidence a b) :
    sigmaPiWitnesses (piSigmaChoice witnesses) = witnesses := by
  funext a
  change ⟨(witnesses a).1, (witnesses a).2⟩ = witnesses a
  cases witnesses a
  rfl

theorem selection_roundTrip (selected : Σ chosen : (a : A) → B a,
    (a : A) → Evidence a (chosen a)) : piSigmaChoice (sigmaPiWitnesses selected) = selected := by
  cases selected
  rfl

/-- Propositional existence follows from the data; this map does not assert
a reverse extraction from propositions to witness-bearing data. -/
theorem erase_witnesses (witnesses : (a : A) → Σ b : B a, Evidence a b) :
    ∀ a, ∃ b : B a, Nonempty (Evidence a b) :=
  fun a => ⟨(witnesses a).1, ⟨(witnesses a).2⟩⟩

/-- Dependent iteration can likewise run from an actual serial witness
producer. This premise is data, not merely a propositional seriality law. -/
def witnessedDependentRun {R : A → A → Type v}
    (next : (a : A) → Σ b : A, R a b) (initial : A) : Nat → A
  | 0 => initial
  | n+1 => (next (witnessedDependentRun next initial n)).1

def witnessedDependentReceipt {R : A → A → Type v}
    (next : (a : A) → Σ b : A, R a b) (initial : A) (n : Nat) :
    R (witnessedDependentRun next initial n) (witnessedDependentRun next initial (n+1)) :=
  (next (witnessedDependentRun next initial n)).2

theorem witnessedDependentRun_initial {R : A → A → Type v}
    (next : (a : A) → Σ b : A, R a b) (initial : A) :
    witnessedDependentRun next initial 0 = initial := rfl

namespace Controls

/-- The carrier of this family varies with the natural-number index. -/
def growingWitnesses (n : Nat) : Σ chosen : Fin (n+1), {k : Nat // k = chosen.val+1} :=
  ⟨⟨n, Nat.lt_succ_self n⟩, ⟨n+1, rfl⟩⟩

theorem growing_family_choice (n : Nat) :
    ((piSigmaChoice growingWitnesses).1 n).val = n := rfl

theorem growing_family_retains_evidence (n : Nat) :
    ((piSigmaChoice growingWitnesses).2 n).val = n+1 := rfl

/-- Occurrences carry the same key and distinct receipt numbers. -/
structure Occurrence where
  key : Nat
  receipt : Nat
  deriving DecidableEq

def first : Occurrence := ⟨7, 0⟩
def second : Occurrence := ⟨7, 1⟩

/-- The witness certifies the source occurrence, rather than only its key. -/
def receiptWitnesses (source : Occurrence) : Σ receipt : Nat, {origin : Occurrence //
    origin = source ∧ origin.receipt = receipt} :=
  ⟨source.receipt, ⟨source, rfl, rfl⟩⟩

theorem occurrence_keys_agree : first.key = second.key := rfl

theorem chosen_receipts_differ :
    (piSigmaChoice receiptWitnesses).1 first ≠
      (piSigmaChoice receiptWitnesses).1 second := by
  intro same
  exact Nat.zero_ne_one same

/-- Product/sum choice on presentations does not make its result descend
through the readout that forgets occurrence receipts. -/
theorem receipt_choice_does_not_descend :
    ¬ ∃ recover : Nat → Nat, ∀ source : Occurrence,
      recover source.key = (piSigmaChoice receiptWitnesses).1 source := by
  rintro ⟨recover, agrees⟩
  exact chosen_receipts_differ ((agrees first).symm.trans (agrees second))

/-- Mere inhabitedness can support a fresh selection, but cannot recover
every original witness. The two erased inputs are identical proofs. -/
theorem erased_inhabitedness_does_not_recover_original :
    ¬ ∃ recover : Nonempty Bool → Bool, ∀ original : Bool,
      recover ⟨original⟩ = original := by
  rintro ⟨recover, returnsOriginal⟩
  have codesAgree : (⟨false⟩ : Nonempty Bool) = ⟨true⟩ := rfl
  have selectedAgree : false = true := (returnsOriginal false).symm.trans
    ((congrArg recover codesAgree).trans (returnsOriginal true))
  exact Bool.noConfusion selectedAgree

end Controls

variable {S : Type u} {member : Mem S}

/-- A selector on inhabited material subsets of unordered pairs. Its input
is a material set, so Lean equality makes this selector substitutive. -/
structure ExtensionalPairSelector (member : Mem S) where
  select : S → S
  law : PairSubsetChoice (mem := member) select

theorem extensional_pair_choice_implies_excluded_middle
    (extensionality : Extensional member) (separation : HasSeparation member)
    (empty : HasEmpty member) (pairing : HasPairing member)
    (selector : ExtensionalPairSelector member) : ∀ p : Prop, p ∨ ¬ p :=
  lem_of_pairSubsetChoice extensionality separation empty pairing selector.select selector.law

/-- A failed excluded-middle instance rules out that selector under those
same set-forming hypotheses. -/
theorem no_extensional_pair_selector_of_no_excluded_middle
    (extensionality : Extensional member) (separation : HasSeparation member)
    (empty : HasEmpty member) (pairing : HasPairing member)
    (p : Prop) (notDecided : ¬ (p ∨ ¬ p)) :
    ¬ Nonempty (ExtensionalPairSelector member) := by
  rintro ⟨selector⟩
  exact notDecided
    (extensional_pair_choice_implies_excluded_middle extensionality separation empty pairing selector p)

/-- Only this Separation predicate is needed for the universal-set obstruction. -/
def RussellSeparation (member : Mem S) (universal : S) : Prop :=
  ∃ separated, ∀ child,
    member child separated ↔ member child universal ∧ ¬ member child child

theorem universal_set_refutes_russell_separation (universal : S)
    (containsEverything : ∀ child, member child universal) :
    ¬ RussellSeparation member universal := by
  rintro ⟨separated, specification⟩
  have notSelf : ¬ member separated separated :=
    fun belongs => ((specification separated).mp belongs).2 belongs
  exact notSelf ((specification separated).mpr ⟨containsEverything separated, notSelf⟩)

theorem universal_set_refutes_separation (universal : S)
    (containsEverything : ∀ child, member child universal) : ¬ HasSeparation member := by
  intro separation
  exact universal_set_refutes_russell_separation universal containsEverything
    (separation universal (fun child => ¬ member child child))

end Mettapedia.SetTheory.Profiles.ProfileChoice
