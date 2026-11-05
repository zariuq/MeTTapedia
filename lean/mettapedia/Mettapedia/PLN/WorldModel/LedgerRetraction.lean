import Mettapedia.PLN.WorldModel.ForgettingEvidenceLaws
import Mettapedia.PLN.WorldModel.EvidenceContracts

/-!
# Retraction on a ledger of identified observations: causal deletion

A ledger state is a bag of identified observations.  A claim names the observations relevant to
it and which of those hold (`IdClaim`).  The evidence of a claim is the evidence of its relevant
observations (`bagEvidence`), and its support is the set of their identities (`bagSupport`).  Bags
of identified observations form an additive world model of claims (`claimWorldModel`).

**Causal deletion** removes the forgotten identities (`causalForget`).

* **It is a retraction layer** (`causalRetractionLayer`).  It commutes with revision, erases every
  bag supported inside the forgotten identities and fixes every bag that avoids them, so it undoes a
  supported revision of a clean base exactly.  It never manufactures evidence.  Retained supports
  shrink and avoid the forgotten identities, and nonzero evidence is supported.  A claim whose
  support avoids them keeps its evidence exactly.
* **It is the only one** (`eq_causalForget_of_exactInverse_of_clean`).  Every bag splits into the
  part that avoids the forgotten identities and the part inside them, so an operation that undoes
  every supported revision of every clean base is causal deletion, and every support-tracked layer
  with these supports is causal deletion (`supportTracked_forget_eq_causalForget`).
* **The recount is exact** (`causal_recount`): the evidence of the withdrawn observations is
  subtracted.
* Forgetting twice is forgetting the union, in either order (`causalForget_causalForget`,
  `causalForget_comm`).
* **The all-bases inverse has no sound model** (`no_sound_allBases_exactInverse`).  With supports
  inside the bag and the forgotten identities as footprints, undoing every supported revision on
  every base would make a single observation zero.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.LedgerRetraction

open Mettapedia.PLN.Evidence.EvidenceClass (EvidenceType)
open Mettapedia.PLN.WorldModel.EvidenceSpaces
open Mettapedia.PLN.WorldModel.EvidenceSpaces.Evidence (retract_revision)
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric (AdditiveWorldModel)
open Mettapedia.PLN.WorldModel.GenericWorldModelForgetting (ForgettingLayer)
open Mettapedia.PLN.WorldModel.PLNWorldModelSupportForgetting (SupportTrackedForgettingLayer)
open Mettapedia.PLN.WorldModel.ForgettingEvidenceLaws
  (EvidenceMonotoneForgettingLayer SupportClosedForgettingLayer RetractionLayer)

universe u

variable {O : Type u}

/-! ## Claims about identified observations -/

/-- A claim about identified observations: which observations are relevant to it, and which of
those hold. -/
structure IdClaim (O : Type u) where
  relevant : O → Bool
  holds : O → Bool

/-- The evidence a bag of identified observations gives a claim. -/
def bagEvidence (q : IdClaim O) (m : Multiset O) : Evidence ℕ :=
  ((m.filter fun o => q.relevant o = true).map (sampleEvidence q.holds)).sum

theorem bagEvidence_add (q : IdClaim O) (m m' : Multiset O) :
    bagEvidence q (m + m') = bagEvidence q m + bagEvidence q m' := by
  simp [bagEvidence, Multiset.filter_add, Multiset.map_add, Multiset.sum_add]

/-- **Bags of identified observations are an additive world model of claims.** -/
instance claimWorldModel : AdditiveWorldModel (Multiset O) (IdClaim O) (Evidence ℕ) where
  extract m q := bagEvidence q m
  extract_add m m' q := bagEvidence_add q m m'

theorem bagEvidence_mono (q : IdClaim O) {m m' : Multiset O} (le : m ≤ m') :
    bagEvidence q m ≤ bagEvidence q m' := by
  obtain ⟨u, rfl⟩ := Multiset.le_iff_exists_add.mp le
  rw [bagEvidence_add]
  exact le_self_add

variable [DecidableEq O]

/-- The support of a claim in a bag: the identities of its relevant observations. -/
def bagSupport (m : Multiset O) (q : IdClaim O) : Finset O :=
  (m.filter fun o => q.relevant o = true).toFinset

theorem mem_bagSupport {m : Multiset O} {q : IdClaim O} {o : O} :
    o ∈ bagSupport m q ↔ o ∈ m ∧ q.relevant o = true := by
  simp [bagSupport]

/-- The claim to which every observation is relevant. -/
def totalClaim (holds : O → Bool) : IdClaim O := ⟨fun _ => true, holds⟩

/-- A bag supported inside `S` for every claim has all its observations in `S`. -/
theorem mem_of_supported {S : Finset O} {Δ : Multiset O}
    (supported : ∀ q : IdClaim O, bagSupport Δ q ⊆ S) : ∀ o ∈ Δ, o ∈ S :=
  fun _ member => supported (totalClaim fun _ => true) (mem_bagSupport.mpr ⟨member, rfl⟩)

/-- A bag clean for `S` for every claim has no observation in `S`. -/
theorem notMem_of_clean {S : Finset O} {W : Multiset O}
    (clean : ∀ q : IdClaim O, Disjoint (bagSupport W q) S) : ∀ o ∈ W, o ∉ S :=
  fun _ member inS => Finset.disjoint_left.mp (clean (totalClaim fun _ => true))
    (mem_bagSupport.mpr ⟨member, rfl⟩) inS

/-! ## Causal deletion -/

/-- **Causal deletion**: remove the forgotten identities. -/
def causalForget (forgotten : Finset O) (m : Multiset O) : Multiset O :=
  m.filter fun o => o ∉ forgotten

theorem causalForget_add (forgotten : Finset O) (m m' : Multiset O) :
    causalForget forgotten (m + m') = causalForget forgotten m + causalForget forgotten m' :=
  Multiset.filter_add _ _ _

theorem causalForget_le (forgotten : Finset O) (m : Multiset O) : causalForget forgotten m ≤ m :=
  Multiset.filter_le _ _

/-- **Forgetting twice is forgetting the union.** -/
theorem causalForget_causalForget (S T : Finset O) (m : Multiset O) :
    causalForget S (causalForget T m) = causalForget (S ∪ T) m := by
  unfold causalForget
  rw [Multiset.filter_filter]
  apply Multiset.filter_congr
  intro o _
  simp only [Finset.mem_union, not_or]

/-- **Forgettings commute.** -/
theorem causalForget_comm (S T : Finset O) (m : Multiset O) :
    causalForget S (causalForget T m) = causalForget T (causalForget S m) := by
  rw [causalForget_causalForget, causalForget_causalForget, Finset.union_comm]

theorem causalForget_idempotent (S : Finset O) (m : Multiset O) :
    causalForget S (causalForget S m) = causalForget S m := by
  rw [causalForget_causalForget, Finset.union_self]

/-- Every bag is its part outside the forgotten identities plus its part inside them. -/
theorem causalForget_add_withdrawn (S : Finset O) (m : Multiset O) :
    causalForget S m + m.filter (fun o => o ∈ S) = m := by
  unfold causalForget
  rw [add_comm]
  exact Multiset.filter_add_not _ _

/-- **Relevance**: a claim whose support avoids the forgotten identities keeps its evidence. -/
theorem bagEvidence_causalForget_of_disjoint {S : Finset O} {m : Multiset O} {q : IdClaim O}
    (avoids : Disjoint (bagSupport m q) S) :
    bagEvidence q (causalForget S m) = bagEvidence q m := by
  unfold bagEvidence causalForget
  rw [Multiset.filter_filter]
  congr 2
  apply Multiset.filter_congr
  intro o member
  constructor
  · exact fun both => both.1
  · intro relevant
    exact ⟨relevant, fun inS =>
      Finset.disjoint_left.mp avoids (mem_bagSupport.mpr ⟨member, relevant⟩) inS⟩

/-- **The recount is exact**: the evidence of the withdrawn observations is subtracted. -/
theorem causal_recount (S : Finset O) (m : Multiset O) (q : IdClaim O) :
    bagEvidence q (causalForget S m) =
      bagEvidence q m - bagEvidence q (m.filter fun o => o ∈ S) := by
  have split := congrArg (bagEvidence q) (causalForget_add_withdrawn S m)
  rw [bagEvidence_add] at split
  rw [← split, retract_revision]

/-! ## The forgetting interface -/

/-- **Causal deletion is a forgetting layer that never manufactures evidence.** -/
def causalLayer :
    EvidenceMonotoneForgettingLayer (Multiset O) (Finset O) (IdClaim O) (Evidence ℕ) where
  inScope forgotten q := ∃ o ∈ forgotten, q.relevant o = true
  forget := causalForget
  idempotent := causalForget_idempotent
  outsideInvariant := by
    intro forgotten m q outside
    change bagEvidence q (causalForget forgotten m) = bagEvidence q m
    apply bagEvidence_causalForget_of_disjoint
    rw [Finset.disjoint_left]
    intro o member inForgotten
    exact outside ⟨o, inForgotten, (mem_bagSupport.mp member).2⟩
  forget_le forgotten m q := bagEvidence_mono q (causalForget_le forgotten m)

/-- **Causal deletion is a retraction layer**: both forgetting laws, exact unlearning on clean bases
and relevance. -/
def causalRetractionLayer :
    RetractionLayer (Multiset O) (Finset O) (IdClaim O) (Evidence ℕ) O :=
  { causalLayer with
    scopeFootprint := fun forgotten => forgotten
    support := bagSupport
    forget_add := causalForget_add
    forget_eq_zero_of_supported := by
      intro forgotten Δ supported
      change causalForget forgotten Δ = 0
      exact Multiset.filter_eq_nil.mpr fun o member notIn =>
        notIn (mem_of_supported supported o member)
    forget_eq_self_of_clean := by
      intro forgotten W clean
      change causalForget forgotten W = W
      exact Multiset.filter_eq_self.mpr (notMem_of_clean clean)
    support_nonempty_of_ne_zero := by
      intro m q nonzero
      change bagEvidence q m ≠ 0 at nonzero
      by_contra empty
      rw [Finset.not_nonempty_iff_eq_empty, bagSupport, Multiset.toFinset_eq_empty] at empty
      apply nonzero
      unfold bagEvidence
      rw [empty]
      simp
    retained_support_subset := by
      intro forgotten m q o member
      change o ∈ bagSupport (causalForget forgotten m) q at member
      simp only [bagSupport, causalForget, Multiset.mem_toFinset, Multiset.mem_filter] at member ⊢
      exact ⟨member.1.1, member.2⟩
    retained_support_disjoint := by
      intro forgotten m q
      rw [Finset.disjoint_left]
      intro o member inForgotten
      change o ∈ bagSupport (causalForget forgotten m) q at member
      simp only [bagSupport, causalForget, Multiset.mem_toFinset, Multiset.mem_filter] at member
      exact member.1.2 inForgotten
    extract_forget_of_disjoint := by
      intro forgotten W q avoids
      exact bagEvidence_causalForget_of_disjoint avoids }

/-- **Causal deletion deletes**: a claim supported only inside the forgotten identities loses all
its evidence. -/
theorem causal_deletes_supported {forgotten : Finset O} {m : Multiset O} {q : IdClaim O}
    (inside : bagSupport m q ⊆ forgotten) : bagEvidence q (causalForget forgotten m) = 0 :=
  causalRetractionLayer.extract_forget_eq_zero_of_support_subset inside

/-- **Every surviving claim keeps a support outside the forgotten identities.** -/
theorem causal_retains_outside {forgotten : Finset O} {m : Multiset O} {q : IdClaim O}
    (survives : bagEvidence q (causalForget forgotten m) ≠ 0) :
    ∃ o ∈ bagSupport m q, o ∉ forgotten :=
  causalRetractionLayer.toSupportClosedForgettingLayer.exists_outside_support_of_retained survives

/-- **Exact unlearning on clean bases.** -/
theorem causal_exactInverse_of_clean {forgotten : Finset O} {W Δ : Multiset O}
    (supported : ∀ q : IdClaim O, bagSupport Δ q ⊆ forgotten)
    (clean : ∀ q : IdClaim O, Disjoint (bagSupport W q) forgotten) :
    causalForget forgotten (W + Δ) = W :=
  causalRetractionLayer.exactInverse_of_clean supported clean

/-! ## Exact unlearning determines forgetting on the ledger -/

/-- **Causal deletion is the only exact unlearning on the ledger**: an operation that undoes every
supported revision of every clean base is causal deletion. -/
theorem eq_causalForget_of_exactInverse_of_clean (S : Finset O) (f : Multiset O → Multiset O)
    (exact : ∀ W Δ : Multiset O, (∀ q : IdClaim O, bagSupport Δ q ⊆ S) →
      (∀ q : IdClaim O, Disjoint (bagSupport W q) S) → f (W + Δ) = W)
    (m : Multiset O) : f m = causalForget S m := by
  have supported : ∀ q : IdClaim O, bagSupport (m.filter fun o => o ∈ S) q ⊆ S := by
    intro q o member
    exact (Multiset.mem_filter.mp (mem_bagSupport.mp member).1).2
  have clean : ∀ q : IdClaim O, Disjoint (bagSupport (causalForget S m) q) S := by
    intro q
    rw [Finset.disjoint_left]
    intro o member inS
    exact (Multiset.mem_filter.mp (mem_bagSupport.mp member).1).2 inS
  calc f m = f (causalForget S m + m.filter fun o => o ∈ S) := by
        rw [causalForget_add_withdrawn]
    _ = causalForget S m := exact _ _ supported clean

/-- **Every support-tracked layer on the ledger with these supports is causal deletion.** -/
theorem supportTracked_forget_eq_causalForget
    (F : SupportTrackedForgettingLayer (Multiset O) (Finset O) (IdClaim O) (Evidence ℕ) O)
    (hsupport : F.support = bagSupport) (hfootprint : ∀ S, F.scopeFootprint S = S)
    (S : Finset O) (m : Multiset O) : F.forget S m = causalForget S m :=
  eq_causalForget_of_exactInverse_of_clean S (F.forget S)
    (fun W Δ supported clean => F.exactInverse_of_clean
      (fun q => by rw [hsupport, hfootprint]; exact supported q)
      (fun q => by rw [hsupport, hfootprint]; exact clean q)) m

/-! ## The all-bases inverse -/

/-- **The all-bases inverse has no sound model on the ledger.**  Whatever the forgetting layer, if
supports lie inside the bag and the forgotten identities are the footprints, undoing every
supported revision on every base fails already for a single observation. -/
theorem no_sound_allBases_exactInverse [Nonempty O]
    (F : ForgettingLayer (Multiset O) (Finset O) (IdClaim O) (Evidence ℕ))
    (support : Multiset O → IdClaim O → Finset O)
    (sound : ∀ m q, support m q ⊆ m.toFinset) :
    ¬ ∀ (S : Finset O) (Δ : Multiset O), (∀ q, support Δ q ⊆ S) →
        ∀ W : Multiset O, F.forget S (W + Δ) = W := by
  intro allBases
  obtain ⟨o⟩ := ‹Nonempty O›
  have supported : ∀ q, support {o} q ⊆ {o} := fun q => (sound {o} q).trans (by simp)
  exact Multiset.singleton_ne_zero o
    (F.exactInverse_everywhere_degenerate (allBases {o} {o} supported)).2

end Mettapedia.PLN.WorldModel.LedgerRetraction

open Mettapedia.PLN.WorldModel.LedgerRetraction in
#print axioms causalRetractionLayer
open Mettapedia.PLN.WorldModel.LedgerRetraction in
#print axioms causal_recount
open Mettapedia.PLN.WorldModel.LedgerRetraction in
#print axioms causalForget_comm
open Mettapedia.PLN.WorldModel.LedgerRetraction in
#print axioms eq_causalForget_of_exactInverse_of_clean
open Mettapedia.PLN.WorldModel.LedgerRetraction in
#print axioms supportTracked_forget_eq_causalForget
open Mettapedia.PLN.WorldModel.LedgerRetraction in
#print axioms no_sound_allBases_exactInverse
open Mettapedia.PLN.WorldModel.LedgerRetraction in
#print axioms causal_deletes_supported
open Mettapedia.PLN.WorldModel.LedgerRetraction in
#print axioms causal_retains_outside
