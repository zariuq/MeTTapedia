import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.BorrowedSteps

/-!
# Rholang's bundles cannot hand out reading without removing

A Rholang bundle has two flags (`Bundle{write_flag, read_flag}` in the reducer): `bundle+ {c}`
may send, `bundle- {c}` may receive, `bundle0 {c}` neither, `bundle {c}` both. Receiving with
`<-` or `<=` removes the message, and peeking with `<<-` does not, but both need the read flag.
So a holder who may look at a shared datum may also remove it.

## Results

* `peek_needs_take`, `no_peekOnly_bundle`: every bundle that permits a peek permits a take.
* `no_bundle_observes`: no bundle permits a predicate query (absence, count), a part rho lacks.
* `bundle_sets_card`: the bundles license four of the sixteen sets of parts that Prime's handles
  may carry (`rightSet_card`).
* `bundle_reader_removes`: with any bundle that can peek, one reader removes the datum, and then no
  peek can ever fire again (`removed_no_peek`).
* `peekOnly_keeps`: a holder whose rights omit take never removes it: the datum is present in every
  reachable configuration.

The rules here act on one location; a holder fires the steps its rights allow.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Weaknesses.Rights

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence (Rule Reduces)

/-- The four parts of a step a right can license at a location. -/
inductive Part where
  | send | take | peek | observe
  deriving DecidableEq

instance : Fintype Part where
  elems := {.send, .take, .peek, .observe}
  complete := by intro x; cases x <;> decide

/-- A Rholang bundle: a read flag and a write flag. -/
structure Bundle where
  read : Bool
  write : Bool
  deriving DecidableEq

/-- The four bundles. -/
instance : Fintype Bundle where
  elems := {⟨false, false⟩, ⟨false, true⟩, ⟨true, false⟩, ⟨true, true⟩}
  complete := by
    rintro ⟨r, w⟩
    cases r <;> cases w <;> decide

/-- What a bundle licenses: write is send; read is both take (`<-`, `<=`) and peek (`<<-`);
nothing is a predicate query. -/
def Bundle.permits (b : Bundle) : Part → Bool
  | .send => b.write
  | .take => b.read
  | .peek => b.read
  | .observe => false

/-- A set of rights, as a Prime handle may carry any set of parts. -/
abbrev RightSet := Part → Bool

/-- **Every bundle that permits a peek permits a take.** -/
theorem peek_needs_take (b : Bundle) (h : b.permits .peek = true) : b.permits .take = true := h

theorem no_peekOnly_bundle : ¬ ∃ b : Bundle, b.permits .peek = true ∧ b.permits .take = false :=
  fun ⟨b, hp, ht⟩ => by simp [Bundle.permits] at hp ht; simp [hp] at ht

/-- **No bundle permits a predicate query.** -/
theorem no_bundle_observes (b : Bundle) : b.permits .observe = false := rfl

/-- A board reader's rights: peek only. -/
def boardReader : RightSet := fun p => decide (p = .peek)

theorem boardReader_peeks : boardReader .peek = true ∧ boardReader .take = false := by decide

/-- **Bundles license four sets of parts.** -/
theorem bundle_sets_card : (Finset.univ.image (fun b : Bundle => b.permits)).card = 4 := by
  decide

/-- **Handles may carry all sixteen.** -/
theorem rightSet_card : Fintype.card RightSet = 16 := by
  simp only [RightSet, Fintype.card_fun, Fintype.card_bool]
  decide

/-! ## Readers on one shared datum -/

/-- A shared notice, what a peek leaves, what a take leaves. -/
inductive Board where
  | notice | seen | taken
  deriving DecidableEq

/-- Peek: keep the notice. -/
def peekRule : Rule Board := ⟨0, {.notice}, {.seen}, fun _ => false⟩

/-- Take: remove it. -/
def takeRule : Rule Board := ⟨{.notice}, 0, {.taken}, fun _ => false⟩

/-- The steps a holder with rights `r` may fire on the notice. -/
def Allowed (r : Part → Bool) (ρ : Rule Board) : Prop :=
  (ρ = peekRule ∧ r .peek = true) ∨ (ρ = takeRule ∧ r .take = true)

/-- **A holder that may not take never removes the notice.** -/
theorem peekOnly_keeps (r : Part → Bool) (noTake : r .take = false) {M M' : Multiset Board}
    (present : Board.notice ∈ M) (run : Relation.ReflTransGen (Reduces (Allowed r)) M M') :
    Board.notice ∈ M' := by
  induction run with
  | refl => exact present
  | tail _ last ih =>
    obtain ⟨ρ, (⟨rfl, _⟩ | ⟨rfl, hTake⟩), _, rfl⟩ := last
    · simp only [Rule.result, peekRule, tsub_zero, Multiset.mem_add]
      exact Or.inl ih
    · simp [noTake] at hTake

/-- **With any bundle that can peek, one reader removes the notice.** -/
theorem bundle_reader_removes (b : Bundle) (h : b.permits .peek = true) :
    ∃ M', Relation.ReflTransGen (Reduces (Allowed b.permits)) {.notice} M' ∧
      Board.notice ∉ M' :=
  ⟨{.taken}, .single ⟨takeRule, Or.inr ⟨rfl, peek_needs_take b h⟩, ⟨by decide, fun _ _ => rfl⟩,
    by decide⟩, by decide⟩

/-- **After the removal no peek can fire.** -/
theorem removed_no_peek (r : Part → Bool) :
    ¬ ∃ M', Reduces (Allowed r) {Board.taken} M' := by
  rintro ⟨M', ρ, (⟨rfl, _⟩ | ⟨rfl, _⟩), ⟨le, _⟩, _⟩ <;> exact absurd le (by decide)

/-- **The board reader keeps the notice for everyone.** -/
theorem boardReader_keeps {M' : Multiset Board}
    (run : Relation.ReflTransGen (Reduces (Allowed boardReader)) {.notice} M') :
    Board.notice ∈ M' :=
  peekOnly_keeps boardReader (by decide) (by simp) run

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Weaknesses.Rights
