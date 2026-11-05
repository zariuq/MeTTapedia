import Mettapedia.PLN.WorldModel.LedgerRetraction

/-!
# The retracted sighting: forgetting policies against the laws

A ledger holds four sightings of black birds: `1`, `2`, `3` are ravens and `4` is a crow.  Three
claims rest on them: "ravens are black" on `{1, 2, 3}`, "crows are black" on `{4}` and "birds are
black" on all four.  The sighting `4` is withdrawn.  A table gives each claim its evidence and its
support.

The laws, between the table before and the table after:

* **no manufactured evidence** (`NoManufactured`): no count grows;
* **support closure** (`ShrinksAndAvoids`): every support shrinks and avoids the withdrawn sighting;
* **sound supports** (`Sound`): nonzero evidence has a nonempty support;
* **relevance** (`Relevant`): a claim whose support avoids the withdrawn sighting is unchanged;
* **exact unlearning** (`Exact`): the table is the one recomputed from the ledger without the
  withdrawn sighting.

The three policies of the discriminator:

* **CAUSAL-DELETE** (`causal`) satisfies all five laws (`causal_laws`); its rows are those of the
  ledger without `4` (`causal_rows`).
* **RESET-TO-PRIOR** (`reset`) manufactures evidence and leaves the prior unsupported
  (`reset_manufactures`, `reset_unsupported`).
* **ZERO-IN-SCOPE** (`zero`) manufactures nothing and is not support closed: the aggregate claim
  keeps standing on `4` (`zero_no_manufactured`, `zero_not_support_closed`).
* All three are idempotent on this table and leave the ravens claim, outside the scope, unchanged
  (`earlier_interface_admits_all`): the earlier interface admits all three.

Each of the first four laws fails alone under one policy, so none follows from the other three
(`independence`):

* resetting to the prior on the remaining support (`resetRemaining`) breaks only no manufactured
  evidence;
* zeroing in scope breaks only support closure;
* keeping the counts while dropping the withdrawn sighting from the supports (`orphan`) breaks only
  sound supports;
* also deleting the unrelated sighting `3` (`offByOne`) breaks only relevance: the ravens claim,
  whose support avoids `4`, drops evidence.

Exact unlearning implies the four (`exact_implies`) and is strictly stronger: deleting every claim
that used `4`, without rederiving what remains (`overDelete`), satisfies the four and not exact
unlearning (`overDelete_four_laws`, `overDelete_not_exact`).

Relevance, positively: under causal deletion, and under every retraction layer on the ledger, the
ravens claim keeps its evidence exactly (`causal_relevance`, `retraction_relevance`).
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.LedgerRetraction.Controls

open Mettapedia.PLN.WorldModel.EvidenceSpaces
open Mettapedia.PLN.WorldModel.ForgettingEvidenceLaws (RetractionLayer)

/-- Decidable equality of counts, for checking tables. -/
local instance : DecidableEq (Evidence ℕ) := fun a b =>
  decidable_of_iff (a.pos = b.pos ∧ a.neg = b.neg) Evidence.ext_iff.symm

/-- Decidable order of counts, for checking tables. -/
local instance : DecidableLE (Evidence ℕ) := fun a b =>
  decidable_of_iff _ (Evidence.le_def a b).symm

/-- The four sightings. -/
def ledger : Multiset ℕ := {1, 2, 3, 4}

def isRaven (o : ℕ) : Bool := decide (o = 1 ∨ o = 2 ∨ o = 3)

def isCrow (o : ℕ) : Bool := decide (o = 4)

def isBird (o : ℕ) : Bool := isRaven o || isCrow o

/-- The three claims. -/
inductive BirdClaim where
  | ravens
  | crows
  | birds
  deriving DecidableEq

instance : Fintype BirdClaim :=
  ⟨{.ravens, .crows, .birds}, by intro q; cases q <;> decide⟩

/-- Every sighting is of a black bird. -/
def claimOf : BirdClaim → IdClaim ℕ
  | .ravens => ⟨isRaven, fun _ => true⟩
  | .crows => ⟨isCrow, fun _ => true⟩
  | .birds => ⟨isBird, fun _ => true⟩

/-- A claim table: the evidence and the support of each claim. -/
abbrev Table := BirdClaim → Evidence ℕ × Finset ℕ

/-- The table of a ledger. -/
def tableOf (m : Multiset ℕ) : Table := fun q =>
  (bagEvidence (claimOf q) m, bagSupport m (claimOf q))

/-- The withdrawn sighting. -/
def scope : Finset ℕ := {4}

/-- The table before the retraction. -/
abbrev before : Table := tableOf ledger

/-- **CAUSAL-DELETE**: the table of the ledger after causal deletion of the withdrawn sighting. -/
abbrev causal : Table := tableOf (causalForget scope ledger)

/-- **RESET-TO-PRIOR**: every claim touching the scope gets `(1, 1)` and no support. -/
def reset (t : Table) : Table := fun q => if ((t q).2 ∩ scope).Nonempty then (⟨1, 1⟩, ∅) else t q

/-- **ZERO-IN-SCOPE**: every claim supported only inside the scope gets `(0, 0)`. -/
def zero (t : Table) : Table := fun q => if (t q).2 ⊆ scope then (0, ∅) else t q

/-- Every claim touching the scope gets the prior `(1, 1)` on its remaining support, or nothing
when no support remains. -/
def resetRemaining (t : Table) : Table := fun q =>
  if ((t q).2 ∩ scope).Nonempty then
    (if ((t q).2 \ scope).Nonempty then (⟨1, 1⟩, (t q).2 \ scope) else (0, ∅))
  else t q

/-- The counts are kept and the withdrawn sighting is dropped from every support. -/
def orphan (t : Table) : Table := fun q => ((t q).1, (t q).2 \ scope)

/-- The unrelated sighting `3` is deleted together with the withdrawn one. -/
abbrev offByOne : Table := tableOf (causalForget {3, 4} ledger)

/-- Every claim that used the withdrawn sighting is deleted, and nothing is rederived. -/
def overDelete (t : Table) : Table := fun q => if ((t q).2 ∩ scope).Nonempty then (0, ∅) else t q

/-! ## The laws -/

/-- No count grows. -/
def NoManufactured (old new : Table) : Prop := ∀ q, (new q).1 ≤ (old q).1

/-- Every support shrinks and avoids the withdrawn sighting. -/
def ShrinksAndAvoids (old new : Table) : Prop :=
  ∀ q, (new q).2 ⊆ (old q).2 ∧ Disjoint (new q).2 scope

/-- Nonzero evidence has a nonempty support. -/
def Sound (new : Table) : Prop := ∀ q, (new q).1 ≠ 0 → (new q).2.Nonempty

/-- A claim whose support avoids the withdrawn sighting is unchanged. -/
def Relevant (old new : Table) : Prop := ∀ q, Disjoint (old q).2 scope → new q = old q

/-- The table is the one recomputed from the ledger without the withdrawn sighting. -/
def Exact (new : Table) : Prop := ∀ q, new q = causal q

instance (old new : Table) : Decidable (NoManufactured old new) := by
  unfold NoManufactured; infer_instance

instance (old new : Table) : Decidable (ShrinksAndAvoids old new) := by
  unfold ShrinksAndAvoids; infer_instance

instance (new : Table) : Decidable (Sound new) := by unfold Sound; infer_instance

instance (old new : Table) : Decidable (Relevant old new) := by unfold Relevant; infer_instance

instance (new : Table) : Decidable (Exact new) := by unfold Exact; infer_instance

/-! ## The rows -/

theorem before_rows :
    before .ravens = (⟨3, 0⟩, {1, 2, 3}) ∧ before .crows = (⟨1, 0⟩, {4}) ∧
      before .birds = (⟨4, 0⟩, {1, 2, 3, 4}) := by decide

/-- **The rows of causal deletion.** -/
theorem causal_rows :
    causal .ravens = (⟨3, 0⟩, {1, 2, 3}) ∧ causal .crows = (0, ∅) ∧
      causal .birds = (⟨3, 0⟩, {1, 2, 3}) := by decide

theorem reset_rows :
    reset before .ravens = (⟨3, 0⟩, {1, 2, 3}) ∧ reset before .crows = (⟨1, 1⟩, ∅) ∧
      reset before .birds = (⟨1, 1⟩, ∅) := by decide

theorem zero_rows :
    zero before .ravens = (⟨3, 0⟩, {1, 2, 3}) ∧ zero before .crows = (0, ∅) ∧
      zero before .birds = (⟨4, 0⟩, {1, 2, 3, 4}) := by decide

/-! ## The three policies of the discriminator -/

/-- **CAUSAL-DELETE satisfies all five laws.** -/
theorem causal_laws :
    NoManufactured before causal ∧ ShrinksAndAvoids before causal ∧ Sound causal ∧
      Relevant before causal ∧ Exact causal := by decide

/-- Causal deletion manufactures no evidence, by the law of the retraction layer. -/
theorem causal_no_manufactured : NoManufactured before causal := fun q =>
  (causalRetractionLayer (O := ℕ)).extract_forget_le scope ledger (claimOf q)

/-- Causal deletion is support closed, by the laws of the retraction layer. -/
theorem causal_support_closed : ShrinksAndAvoids before causal ∧ Sound causal :=
  ⟨fun q => ⟨(causalRetractionLayer (O := ℕ)).retained_support_subset scope ledger (claimOf q),
      (causalRetractionLayer (O := ℕ)).retained_support_disjoint scope ledger (claimOf q)⟩,
    fun q => (causalRetractionLayer (O := ℕ)).support_nonempty_of_ne_zero _ (claimOf q)⟩

/-- **RESET-TO-PRIOR manufactures evidence**: the crow claim gains a negative count. -/
theorem reset_manufactures : ¬ NoManufactured before (reset before) := by decide

/-- **The prior is evidence without support.** -/
theorem reset_unsupported : ¬ Sound (reset before) := by decide

/-- **ZERO-IN-SCOPE manufactures no evidence.** -/
theorem zero_no_manufactured : NoManufactured before (zero before) := by decide

/-- **ZERO-IN-SCOPE is not support closed**: the aggregate claim keeps standing on `4`. -/
theorem zero_not_support_closed : ¬ ShrinksAndAvoids before (zero before) := by decide

/-- **The earlier interface admits all three**: each is idempotent on this table and leaves the
ravens claim, which no withdrawn sighting is relevant to, unchanged. -/
theorem earlier_interface_admits_all :
    (∀ q, reset (reset before) q = reset before q) ∧
      (∀ q, zero (zero before) q = zero before q) ∧
      tableOf (causalForget scope (causalForget scope ledger)) = causal ∧
      reset before .ravens = before .ravens ∧ zero before .ravens = before .ravens ∧
      causal .ravens = before .ravens := by
  refine ⟨by decide, by decide, ?_, by decide, by decide, by decide⟩
  rw [causalForget_idempotent]

/-! ## Independence -/

/-- **Each of the four laws fails alone under one policy.** -/
theorem independence :
    (¬ NoManufactured before (resetRemaining before) ∧
        ShrinksAndAvoids before (resetRemaining before) ∧ Sound (resetRemaining before) ∧
        Relevant before (resetRemaining before)) ∧
      (NoManufactured before (zero before) ∧ ¬ ShrinksAndAvoids before (zero before) ∧
        Sound (zero before) ∧ Relevant before (zero before)) ∧
      (NoManufactured before (orphan before) ∧ ShrinksAndAvoids before (orphan before) ∧
        ¬ Sound (orphan before) ∧ Relevant before (orphan before)) ∧
      (NoManufactured before offByOne ∧ ShrinksAndAvoids before offByOne ∧ Sound offByOne ∧
        ¬ Relevant before offByOne) := by decide

/-- **Exact unlearning implies the four laws.** -/
theorem exact_implies (new : Table) (exact : Exact new) :
    NoManufactured before new ∧ ShrinksAndAvoids before new ∧ Sound new ∧ Relevant before new := by
  have same : new = causal := funext exact
  subst same
  exact ⟨causal_laws.1, causal_laws.2.1, causal_laws.2.2.1, causal_laws.2.2.2.1⟩

/-- **Over-deletion satisfies the four laws.** -/
theorem overDelete_four_laws :
    NoManufactured before (overDelete before) ∧ ShrinksAndAvoids before (overDelete before) ∧
      Sound (overDelete before) ∧ Relevant before (overDelete before) := by decide

/-- **Over-deletion is not exact unlearning**: the birds claim loses the ravens' evidence. -/
theorem overDelete_not_exact : ¬ Exact (overDelete before) := by decide

/-! ## Relevance -/

/-- **Relevance under causal deletion**: the ravens claim keeps its evidence exactly. -/
theorem causal_relevance :
    bagEvidence (claimOf .ravens) (causalForget scope ledger) =
      bagEvidence (claimOf .ravens) ledger :=
  bagEvidence_causalForget_of_disjoint (by decide)

/-- **Relevance under every retraction layer on the ledger with these supports.** -/
theorem retraction_relevance
    (L : RetractionLayer (Multiset ℕ) (Finset ℕ) (IdClaim ℕ) (Evidence ℕ) ℕ)
    (hsupport : L.support = bagSupport) (hfootprint : ∀ S, L.scopeFootprint S = S) :
    bagEvidence (claimOf .ravens) (L.forget scope ledger) =
      bagEvidence (claimOf .ravens) ledger :=
  L.extract_forget_of_disjoint (by rw [hsupport, hfootprint]; decide)

/-- **An operation that also deletes an unrelated sighting drops an unrelated claim**: the ravens
claim, whose support avoids the withdrawn sighting, loses a raven. -/
theorem offByOne_drops_unrelated :
    Disjoint (before .ravens).2 scope ∧ offByOne .ravens = (⟨2, 0⟩, {1, 2}) ∧
      offByOne .ravens ≠ before .ravens := by decide

end Mettapedia.PLN.WorldModel.LedgerRetraction.Controls

open Mettapedia.PLN.WorldModel.LedgerRetraction.Controls in
#print axioms causal_rows
open Mettapedia.PLN.WorldModel.LedgerRetraction.Controls in
#print axioms causal_laws
open Mettapedia.PLN.WorldModel.LedgerRetraction.Controls in
#print axioms causal_no_manufactured
open Mettapedia.PLN.WorldModel.LedgerRetraction.Controls in
#print axioms causal_support_closed
open Mettapedia.PLN.WorldModel.LedgerRetraction.Controls in
#print axioms reset_manufactures
open Mettapedia.PLN.WorldModel.LedgerRetraction.Controls in
#print axioms reset_unsupported
open Mettapedia.PLN.WorldModel.LedgerRetraction.Controls in
#print axioms zero_no_manufactured
open Mettapedia.PLN.WorldModel.LedgerRetraction.Controls in
#print axioms zero_not_support_closed
open Mettapedia.PLN.WorldModel.LedgerRetraction.Controls in
#print axioms earlier_interface_admits_all
open Mettapedia.PLN.WorldModel.LedgerRetraction.Controls in
#print axioms independence
open Mettapedia.PLN.WorldModel.LedgerRetraction.Controls in
#print axioms exact_implies
open Mettapedia.PLN.WorldModel.LedgerRetraction.Controls in
#print axioms overDelete_four_laws
open Mettapedia.PLN.WorldModel.LedgerRetraction.Controls in
#print axioms overDelete_not_exact
open Mettapedia.PLN.WorldModel.LedgerRetraction.Controls in
#print axioms causal_relevance
open Mettapedia.PLN.WorldModel.LedgerRetraction.Controls in
#print axioms retraction_relevance
open Mettapedia.PLN.WorldModel.LedgerRetraction.Controls in
#print axioms offByOne_drops_unrelated
