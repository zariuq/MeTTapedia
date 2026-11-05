import Mettapedia.PLN.WorldModel.ForgettingEvidenceLaws
import Mettapedia.PLN.WorldModel.LedgerRetraction
import Mettapedia.GSLT.Dynamics.ProvenanceInterpretation
import Mettapedia.GSLT.Causality.SemiringFactStores
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Retraction on how-provenance: deletion is the substitution homomorphism

Identified evidence with derived claims is annotated by how-provenance, a polynomial in `ℕ[X]` over
the source tokens `X`: a monomial is one derivation, the product of the sources it used, and
alternative derivations add (Green, Karvounarakis and Tannen, *Provenance semirings*, PODS 2007).
Withdrawing the tokens `S` is the semiring homomorphism that substitutes `0` for them
(`deletion`).

## Deletion drops exactly the derivations through a withdrawn token

* `coeff_deletion`: the coefficient of a monomial survives exactly when the monomial avoids `S`.
  Hence no derivation is manufactured (`coeff_deletion_le`); a polynomial that mentions no
  withdrawn token is fixed (`deletion_eq_self_of_disjoint`); one whose tokens are all withdrawn and
  that has no constant term is erased (`deletion_eq_zero_of_vars_subset`); the tokens shrink and
  avoid `S` (`vars_deletion_subset`, `vars_deletion_disjoint`); the constant term stays
  (`constantCoeff_deletion`).
* `deletion_provenance`: on explicit sets of derivations, deletion keeps the derivations that avoid
  `S`.  This is deletion propagation, and the label update of an assumption-based truth maintenance
  system when an assumption is retracted.  Every semiring reading of the result, the counts among
  them, is the reading of the surviving derivations (`interp_deletion_provenance`).
* Deletions are idempotent, commute and compose to the deletion of the union
  (`deletion_idempotent`, `deletion_comm`, `deletion_deletion`).

## Retraction propagates through derivations

A derived claim is built from base claims by revision, which adds the provenance of alternative
evidence, and deduction, which multiplies the provenance of its two premises (`Derived`).  Deleting
after deriving is deriving from the deleted base (`deletion_prov`): exact unlearning through every
derivation.

## Recursion: provenance succeeds where counting fails

Two atoms each derive the other, and one observation seeds the first.  Deletion commutes with every
stage of the recursive derivation (`SemiringFactStores.System.map_kStage`).  Both atoms are derived
from the observation (`cycleStage_two`), and after it is withdrawn neither has provenance at any
stage (`deletion_cycleStage`), as the closure of the remaining seeds says.  Counting maintenance keeps
both (`cycle_counting_fails_provenance_succeeds`).

## The world-model instance

Claims annotated by provenance polynomials form an additive world model (`ProvState`).  Deleting
tokens from every claim is a support-closed forgetting layer whose supports are the tokens of each
annotation, with `none` marking evidence that holds with no token (`provSupportClosedLayer`).  A
claim whose tokens avoid the withdrawn ones keeps its provenance exactly (`forgetTokens_relevance`),
and no derivation is manufactured (`forgetTokens_no_manufactured`).  With polynomials ordered
coefficientwise (`coeffOrder`), it is a retraction layer (`provRetractionLayer`).

## The ledger is degree-one provenance

On a bag of identified observations, the provenance of a claim has one monomial per relevant
observation (`bagProvenance`), and deleting tokens from it is causal deletion of the bag
(`deletion_bagProvenance`).

## Lineage is too coarse

Lineage records which tokens a claim used, not how they combined.  Two sets of derivations with the
same lineage can need different results after a token is withdrawn, so no operation on lineage
computes the lineage of the retraction (`lineage_not_deletion_compatible`), while how-provenance
tells them apart (`provenance_separates_lineage`).

## Symbol forgetting is another operation

Forgetting the symbol `p` from `{p, p → q}` keeps the consequence `q`; retracting the observation of
`p` retracts `q` (`Controls.symbol_and_data_forgetting_differ`).
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.ProvenanceRetraction

open MvPolynomial
open Mettapedia.PLN.Evidence.EvidenceClass (EvidenceType)
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric (AdditiveWorldModel)
open Mettapedia.PLN.WorldModel.ForgettingEvidenceLaws (SupportClosedForgettingLayer RetractionLayer)
open Mettapedia.GSLT.Dynamics.ProvenanceInterpretation
  (Derivation provOf provenance provenance_cons interpSet interp_provenance)

variable {σ : Type} [DecidableEq σ]

/-! ## Deletion -/

/-- Where a token goes on deletion of `S`: a withdrawn token to zero, every other to itself. -/
noncomputable def deleteValuation (S : Finset σ) (x : σ) : MvPolynomial σ ℕ :=
  if x ∈ S then 0 else MvPolynomial.X x

/-- **Deletion of the tokens `S`**: the substitution homomorphism sending them to zero. -/
noncomputable def deletion (S : Finset σ) : MvPolynomial σ ℕ →ₐ[ℕ] MvPolynomial σ ℕ :=
  bind₁ (deleteValuation S)

theorem deletion_X (S : Finset σ) (x : σ) :
    deletion S (X x) = if x ∈ S then 0 else X x :=
  bind₁_X_right _ _

theorem deletion_C (S : Finset σ) (r : ℕ) : deletion S (C r) = C r :=
  bind₁_C_right _ _

/-- **A monomial survives deletion exactly when it avoids the withdrawn tokens.** -/
theorem deletion_monomial (S : Finset σ) (d : σ →₀ ℕ) (r : ℕ) :
    deletion S (monomial d r) = if Disjoint d.support S then monomial d r else 0 := by
  unfold deletion
  rw [bind₁_monomial]
  split_ifs with h
  · have keep : ∀ i ∈ d.support, deleteValuation S i ^ d i = X i ^ d i := fun i hi => by
      rw [deleteValuation, if_neg (Finset.disjoint_left.mp h hi)]
    rw [Finset.prod_congr rfl keep, monomial_eq, Finsupp.prod]
  · obtain ⟨i, hi, hiS⟩ := Finset.not_disjoint_iff.mp h
    rw [Finset.prod_eq_zero hi (by rw [deleteValuation, if_pos hiS,
      zero_pow (Finsupp.mem_support_iff.mp hi)]), mul_zero]

/-- **The coefficient of a monomial after deletion**: kept when the monomial avoids the withdrawn
tokens, zero otherwise. -/
theorem coeff_deletion (S : Finset σ) (p : MvPolynomial σ ℕ) (m : σ →₀ ℕ) :
    coeff m (deletion S p) = if Disjoint m.support S then coeff m p else 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
      rw [deletion_monomial]
      by_cases hum : u = m
      · subst hum
        split_ifs <;> simp
      · have other : coeff m (monomial u a) = 0 := by rw [coeff_monomial, if_neg hum]
        split_ifs <;> simp [other]
  | add p q hp hq =>
      rw [map_add, coeff_add, coeff_add, hp, hq]
      split_ifs <;> simp

/-- **Deletion manufactures no derivation.** -/
theorem coeff_deletion_le (S : Finset σ) (p : MvPolynomial σ ℕ) (m : σ →₀ ℕ) :
    coeff m (deletion S p) ≤ coeff m p := by
  rw [coeff_deletion]
  split_ifs <;> simp

/-- Deletion keeps the constant term: evidence that uses no token is not withdrawn. -/
theorem constantCoeff_deletion (S : Finset σ) (p : MvPolynomial σ ℕ) :
    constantCoeff (deletion S p) = constantCoeff p := by
  have kept := coeff_deletion S p 0
  rw [if_pos (by simp)] at kept
  exact kept

theorem mem_vars_deletion {S : Finset σ} {p : MvPolynomial σ ℕ} {i : σ}
    (h : i ∈ (deletion S p).vars) : i ∈ p.vars ∧ i ∉ S := by
  rw [mem_vars_iff_mem_support] at h
  obtain ⟨d, hd, hid⟩ := h
  rw [mem_support_iff, coeff_deletion] at hd
  split_ifs at hd with hdis
  · exact ⟨(mem_vars_iff_mem_support i).mpr ⟨d, mem_support_iff.mpr hd, hid⟩,
      Finset.disjoint_left.mp hdis hid⟩
  · exact absurd rfl hd

/-- **The tokens shrink.** -/
theorem vars_deletion_subset (S : Finset σ) (p : MvPolynomial σ ℕ) :
    (deletion S p).vars ⊆ p.vars :=
  fun _ h => (mem_vars_deletion h).1

/-- **The tokens avoid the withdrawn ones.** -/
theorem vars_deletion_disjoint (S : Finset σ) (p : MvPolynomial σ ℕ) :
    Disjoint (deletion S p).vars S :=
  Finset.disjoint_left.mpr fun _ h => (mem_vars_deletion h).2

/-- **A polynomial that mentions no withdrawn token is fixed.** -/
theorem deletion_eq_self_of_disjoint {S : Finset σ} {p : MvPolynomial σ ℕ}
    (h : Disjoint p.vars S) : deletion S p = p := by
  ext m
  rw [coeff_deletion]
  split_ifs with hm
  · rfl
  · symm
    by_contra hne
    obtain ⟨i, hi, hiS⟩ := Finset.not_disjoint_iff.mp hm
    exact Finset.disjoint_left.mp h
      ((mem_vars_iff_mem_support i).mpr ⟨m, mem_support_iff.mpr hne, hi⟩) hiS

/-- **A polynomial whose tokens are all withdrawn, with no constant term, is erased.** -/
theorem deletion_eq_zero_of_vars_subset {S : Finset σ} {p : MvPolynomial σ ℕ}
    (hvars : p.vars ⊆ S) (hconst : constantCoeff p = 0) : deletion S p = 0 := by
  ext m
  rw [coeff_deletion, coeff_zero]
  split_ifs with hm
  · by_contra hne
    by_cases m0 : m = 0
    · subst m0
      exact hne ((congrFun constantCoeff_eq p).symm.trans hconst)
    · obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr m0
      exact Finset.disjoint_left.mp hm hi
        (hvars ((mem_vars_iff_mem_support i).mpr ⟨m, mem_support_iff.mpr hne, hi⟩))
  · rfl

/-- **Two deletions compose to the deletion of the union.** -/
theorem deletion_deletion (S T : Finset σ) (p : MvPolynomial σ ℕ) :
    deletion S (deletion T p) = deletion (S ∪ T) p := by
  ext m
  rw [coeff_deletion, coeff_deletion, coeff_deletion]
  by_cases hS : Disjoint m.support S <;> by_cases hT : Disjoint m.support T <;>
    simp [hS, hT, Finset.disjoint_union_right]

/-- **Deletions commute.** -/
theorem deletion_comm (S T : Finset σ) (p : MvPolynomial σ ℕ) :
    deletion S (deletion T p) = deletion T (deletion S p) := by
  rw [deletion_deletion, deletion_deletion, Finset.union_comm]

/-- **Deletion is idempotent.** -/
theorem deletion_idempotent (S : Finset σ) (p : MvPolynomial σ ℕ) :
    deletion S (deletion S p) = deletion S p := by
  rw [deletion_deletion, Finset.union_self]

/-! ## Deletion propagation on sets of derivations -/

/-- The derivations that use no withdrawn token. -/
def surviving (S : Finset σ) (ds : List (Derivation σ)) : List (Derivation σ) :=
  ds.filter fun d => decide (∀ c ∈ d, c ∉ S)

/-- **One derivation survives deletion exactly when it uses no withdrawn token.** -/
theorem deletion_provOf (S : Finset σ) (d : Derivation σ) :
    deletion S (provOf d) = if ∀ c ∈ d, c ∉ S then provOf d else 0 := by
  induction d with
  | nil => simp [provOf]
  | cons c rest ih =>
      have step : provOf (c :: rest) = X c * provOf rest := by simp [provOf]
      rw [step, map_mul, deletion_X, ih]
      by_cases hc : c ∈ S
      · rw [if_pos hc, zero_mul,
          if_neg (show ¬ ∀ c' ∈ c :: rest, c' ∉ S from fun h => h c List.mem_cons_self hc)]
      · by_cases hr : ∀ c' ∈ rest, c' ∉ S
        · rw [if_neg hc, if_pos hr,
            if_pos (show ∀ c' ∈ c :: rest, c' ∉ S from List.forall_mem_cons.mpr ⟨hc, hr⟩)]
        · rw [if_neg hc, if_neg hr, mul_zero,
            if_neg (show ¬ ∀ c' ∈ c :: rest, c' ∉ S from
              fun h => hr (List.forall_mem_cons.mp h).2)]

/-- **Deletion propagation**: deleting the withdrawn tokens from the provenance of a set of
derivations is the provenance of the derivations that avoid them. -/
theorem deletion_provenance (S : Finset σ) (ds : List (Derivation σ)) :
    deletion S (provenance ds) = provenance (surviving S ds) := by
  induction ds with
  | nil => simp [surviving]
  | cons d rest ih =>
      rw [provenance_cons, map_add, ih, deletion_provOf]
      by_cases hd : ∀ c ∈ d, c ∉ S
      · rw [if_pos hd]
        unfold surviving
        rw [List.filter_cons_of_pos (p := fun d => decide (∀ c ∈ d, c ∉ S)) (by simpa using hd),
          provenance_cons]
      · rw [if_neg hd, zero_add]
        unfold surviving
        rw [List.filter_cons_of_neg (p := fun d => decide (∀ c ∈ d, c ∉ S)) (by simpa using hd)]

/-- **Every semiring reading of the retraction is the reading of the surviving derivations**: the
recount of any annotation, counts among them, is exact. -/
theorem interp_deletion_provenance {K : Type} [CommSemiring K] (v : σ → K) (S : Finset σ)
    (ds : List (Derivation σ)) :
    eval₂ (Nat.castRingHom K) v (deletion S (provenance ds)) = interpSet v (surviving S ds) := by
  rw [deletion_provenance, interp_provenance]

/-! ## Derived claims -/

/-- A claim derived from base claims by revision, which adds the provenance of alternative evidence
for one claim, and deduction, which multiplies the provenance of its two premises. -/
inductive Derived (B : Type) where
  | base : B → Derived B
  | revise : Derived B → Derived B → Derived B
  | deduce : Derived B → Derived B → Derived B

/-- The provenance of a derived claim, from the provenance of the base claims. -/
noncomputable def Derived.prov {B : Type} (ann : B → MvPolynomial σ ℕ) :
    Derived B → MvPolynomial σ ℕ
  | .base b => ann b
  | .revise d e => d.prov ann + e.prov ann
  | .deduce d e => d.prov ann * e.prov ann

/-- **Exact unlearning through derivations**: deleting after deriving is deriving from the deleted
base claims. -/
theorem deletion_prov {B : Type} (S : Finset σ) (ann : B → MvPolynomial σ ℕ) (d : Derived B) :
    deletion S (d.prov ann) = d.prov (fun b => deletion S (ann b)) := by
  induction d with
  | base b => rfl
  | revise d e ihd ihe => rw [Derived.prov, Derived.prov, map_add, ihd, ihe]
  | deduce d e ihd ihe => rw [Derived.prov, Derived.prov, map_mul, ihd, ihe]

/-! ## Provenance-annotated claims as a world model -/

/-- A state: each claim annotated by a provenance polynomial over the tokens. -/
def ProvState (Claim σ : Type) : Type := Claim → MvPolynomial σ ℕ

noncomputable instance (Claim : Type) : EvidenceType (ProvState Claim σ) where
  toAddCommMonoid := inferInstanceAs (AddCommMonoid (Claim → MvPolynomial σ ℕ))

/-- The evidence of a claim is its provenance polynomial. -/
noncomputable instance provWorldModel (Claim : Type) :
    AdditiveWorldModel (ProvState Claim σ) Claim (MvPolynomial σ ℕ) where
  extract W q := W q
  extract_add _ _ _ := rfl

/-- Delete the tokens `S` from every claim. -/
noncomputable def forgetTokens {Claim : Type} (S : Finset σ) (W : ProvState Claim σ) :
    ProvState Claim σ :=
  fun q => deletion S (W q)

/-- The support of an annotation: its tokens, and `none` when it holds with no token. -/
noncomputable def provSupport (p : MvPolynomial σ ℕ) : Finset (Option σ) :=
  p.vars.image some ∪ (if constantCoeff p = 0 then ∅ else {none})

theorem some_mem_provSupport {p : MvPolynomial σ ℕ} {x : σ} :
    some x ∈ provSupport p ↔ x ∈ p.vars := by
  unfold provSupport
  split_ifs <;> simp

theorem none_mem_provSupport {p : MvPolynomial σ ℕ} :
    none ∈ provSupport p ↔ constantCoeff p ≠ 0 := by
  unfold provSupport
  split_ifs with h <;> simp [h]

theorem vars_subset_of_provSupport_subset {p : MvPolynomial σ ℕ} {S : Finset σ}
    (h : provSupport p ⊆ S.image some) : p.vars ⊆ S := by
  intro x hx
  have member : some x ∈ S.image some := h (some_mem_provSupport.mpr hx)
  simpa using member

theorem constantCoeff_eq_zero_of_provSupport_subset {p : MvPolynomial σ ℕ} {S : Finset σ}
    (h : provSupport p ⊆ S.image some) : constantCoeff p = 0 := by
  by_contra hne
  have member : none ∈ S.image some := h (none_mem_provSupport.mpr hne)
  simp at member

theorem vars_disjoint_of_provSupport_disjoint {p : MvPolynomial σ ℕ} {S : Finset σ}
    (h : Disjoint (provSupport p) (S.image some)) : Disjoint p.vars S :=
  Finset.disjoint_left.mpr fun _ hx hxS =>
    Finset.disjoint_left.mp h (some_mem_provSupport.mpr hx) (Finset.mem_image_of_mem some hxS)

theorem provSupport_deletion_subset (S : Finset σ) (p : MvPolynomial σ ℕ) :
    provSupport (deletion S p) ⊆ provSupport p := by
  intro o ho
  cases o with
  | none =>
      exact none_mem_provSupport.mpr
        (by rw [← constantCoeff_deletion S p]; exact none_mem_provSupport.mp ho)
  | some x => exact some_mem_provSupport.mpr (vars_deletion_subset S p (some_mem_provSupport.mp ho))

theorem provSupport_deletion_disjoint (S : Finset σ) (p : MvPolynomial σ ℕ) :
    Disjoint (provSupport (deletion S p)) (S.image some) := by
  rw [Finset.disjoint_left]
  intro o ho hoS
  obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hoS
  exact Finset.disjoint_left.mp (vars_deletion_disjoint S p) (some_mem_provSupport.mp ho) hxS

/-- Nonzero provenance has a nonempty support. -/
theorem provSupport_nonempty {p : MvPolynomial σ ℕ} (h : p ≠ 0) : (provSupport p).Nonempty := by
  by_cases hc : constantCoeff p = 0
  · have hv : p.vars ≠ ∅ := by
      intro hv
      apply h
      rw [vars_eq_empty_iff_eq_C.mp hv,
        show p.coeff 0 = 0 from (congrFun constantCoeff_eq p).symm.trans hc, map_zero]
    obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty hv
    exact ⟨some x, some_mem_provSupport.mpr hx⟩
  · exact ⟨none, none_mem_provSupport.mpr hc⟩

/-- **Deleting tokens is a support-closed forgetting layer on provenance-annotated claims.**  Every
claim may carry any token, so the static scope of a deletion is every claim, and the content of the
layer is in its supports. -/
noncomputable def provSupportClosedLayer (Claim : Type) :
    SupportClosedForgettingLayer (ProvState Claim σ) (Finset σ) Claim (MvPolynomial σ ℕ)
      (Option σ) where
  inScope _ _ := True
  forget := forgetTokens
  idempotent S W := funext fun q => deletion_idempotent S (W q)
  outsideInvariant hout := absurd trivial hout
  scopeFootprint S := S.image some
  support W q := provSupport (W q)
  forget_add S W₁ W₂ := funext fun q => map_add (deletion S) (W₁ q) (W₂ q)
  forget_eq_zero_of_supported := by
    intro S Δ hsupp
    funext q
    exact deletion_eq_zero_of_vars_subset (vars_subset_of_provSupport_subset (hsupp q))
      (constantCoeff_eq_zero_of_provSupport_subset (hsupp q))
  forget_eq_self_of_clean := by
    intro S W hclean
    funext q
    exact deletion_eq_self_of_disjoint (vars_disjoint_of_provSupport_disjoint (hclean q))
  support_nonempty_of_ne_zero _ _ h := provSupport_nonempty h
  retained_support_subset S W q := provSupport_deletion_subset S (W q)
  retained_support_disjoint S W q := provSupport_deletion_disjoint S (W q)

/-- **Relevance**: a claim whose provenance avoids the withdrawn tokens keeps it exactly. -/
theorem forgetTokens_relevance {Claim : Type} {S : Finset σ} {W : ProvState Claim σ} {q : Claim}
    (h : Disjoint (provSupport (W q)) (S.image some)) : forgetTokens S W q = W q :=
  deletion_eq_self_of_disjoint (vars_disjoint_of_provSupport_disjoint h)

/-- **No manufactured evidence**: no derivation of any claim is created. -/
theorem forgetTokens_no_manufactured {Claim : Type} (S : Finset σ) (W : ProvState Claim σ)
    (q : Claim) (m : σ →₀ ℕ) : coeff m (forgetTokens S W q) ≤ coeff m (W q) :=
  coeff_deletion_le S (W q) m

/-- Provenance polynomials ordered coefficientwise: one carries at most the derivations of the
other. -/
@[instance_reducible] noncomputable def coeffOrder : PartialOrder (MvPolynomial σ ℕ) :=
  PartialOrder.lift (fun p m => coeff m p) fun _ _ h => MvPolynomial.ext_iff.mpr fun m => congrFun h m

section Ordered

attribute [local instance] coeffOrder

omit [DecidableEq σ] in
theorem le_iff_coeff_le {p q : MvPolynomial σ ℕ} : p ≤ q ↔ ∀ m, coeff m p ≤ coeff m q :=
  Iff.rfl

/-- **Deleting tokens is a retraction layer on provenance-annotated claims**, with polynomials
ordered coefficientwise: both forgetting laws, exact unlearning on clean bases and relevance. -/
noncomputable def provRetractionLayer (Claim : Type) :
    RetractionLayer (ProvState Claim σ) (Finset σ) Claim (MvPolynomial σ ℕ) (Option σ) :=
  { provSupportClosedLayer Claim with
    forget_le := fun S W q => le_iff_coeff_le.mpr fun m => coeff_deletion_le S (W q) m
    extract_forget_of_disjoint := fun h => forgetTokens_relevance h }

end Ordered

/-! ## The ledger is degree-one provenance -/

open Mettapedia.PLN.WorldModel.LedgerRetraction (IdClaim causalForget)

/-- The provenance of a claim in a bag of identified observations: one monomial per relevant
observation. -/
noncomputable def bagProvenance (q : IdClaim σ) (m : Multiset σ) : MvPolynomial σ ℕ :=
  ((m.filter fun o => q.relevant o = true).map MvPolynomial.X).sum

/-- **Causal deletion is deletion on the provenance of the ledger.** -/
theorem deletion_bagProvenance (S : Finset σ) (q : IdClaim σ) (m : Multiset σ) :
    deletion S (bagProvenance q m) = bagProvenance q (causalForget S m) := by
  unfold bagProvenance causalForget
  induction m using Multiset.induction_on with
  | empty => simp
  | cons o m ih =>
      by_cases hr : q.relevant o = true <;> by_cases hS : o ∈ S <;>
        simp_all [deletion_X]

/-! ## Recursion: provenance succeeds where counting fails -/

open Mettapedia.GSLT.Causality.ResourceInteraction (System)
open Mettapedia.GSLT.Causality.ResourceInteraction.SemiringControls
  (cycle cycleCatalogue counting_retraction_inexact_on_cycle)

/-- One step of the cycle: an atom is its seed plus the other atom, through its rule. -/
theorem cycle_kStep {K : Type} [CommSemiring K] (seed : Bool → K) (weight : cycle.Entry → K)
    (f : Bool → K) (b : Bool) :
    cycle.kStep cycleCatalogue seed weight f b = seed b + weight ⟨(), b⟩ * f (!b) := by
  cases b <;> simp [System.kStep, System.firingValue, cycleCatalogue, cycle]

/-- The seed of the cycle: the atom `true` is observed once, under the token `x`. -/
noncomputable def cycleSeed (x : σ) : Bool → MvPolynomial σ ℕ :=
  fun b => if b then MvPolynomial.X x else 0

/-- The stages of the provenance of the cycle. -/
noncomputable def cycleStage (x : σ) (n : ℕ) : Bool → MvPolynomial σ ℕ :=
  cycle.kStage cycleCatalogue (cycleSeed x) (fun _ => 1) n

omit [DecidableEq σ] in
/-- **Both atoms are derived from the observation.** -/
theorem cycleStage_two (x : σ) (b : Bool) : cycleStage x 2 b = MvPolynomial.X x := by
  unfold cycleStage
  rw [show (2 : ℕ) = 0 + 1 + 1 from rfl, System.kStage_succ, cycle_kStep, System.kStage_succ,
    cycle_kStep, System.kStage_zero]
  cases b <;> simp [cycleSeed]

omit [DecidableEq σ] in
/-- With no seed the cycle derives nothing. -/
theorem cycle_kStage_zero_seed (n : ℕ) :
    cycle.kStage cycleCatalogue (0 : Bool → MvPolynomial σ ℕ) (fun _ => 1) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext b
      rw [System.kStage_succ, cycle_kStep, ih]
      simp

/-- **After the observation is withdrawn, neither atom has provenance at any stage.** -/
theorem deletion_cycleStage (x : σ) (n : ℕ) (b : Bool) : deletion {x} (cycleStage x n b) = 0 := by
  have mapped := congrFun (cycle.map_kStage (deletion {x}).toRingHom cycleCatalogue (cycleSeed x)
    (fun _ => 1) n) b
  have seed0 : ⇑(deletion {x}).toRingHom ∘ cycleSeed x = 0 := by
    funext b
    cases b <;> simp [cycleSeed, deletion_X]
  have weight1 :
      ⇑(deletion {x}).toRingHom ∘ (fun _ : cycle.Entry => (1 : MvPolynomial σ ℕ)) = fun _ => 1 := by
    funext e
    simp
  rw [seed0, weight1, cycle_kStage_zero_seed] at mapped
  exact mapped

/-- **Counting fails on the cycle and provenance succeeds.**  After the seed is withdrawn, counting
maintenance keeps both atoms while the closure of the remaining seeds is empty; with provenance,
both atoms were derived from the observation and neither keeps provenance at any stage once it is
withdrawn. -/
theorem cycle_counting_fails_provenance_succeeds (x : σ) :
    (∀ b, cycle.supportCount cycleCatalogue ∅ Set.univ b ≠ 0) ∧
      cycle.saturation {entry | entry ∈ cycleCatalogue} ∅ = ∅ ∧
      (∀ b, cycleStage x 2 b = MvPolynomial.X x) ∧
      ∀ n b, deletion {x} (cycleStage x n b) = 0 :=
  ⟨counting_retraction_inexact_on_cycle.1, counting_retraction_inexact_on_cycle.2.2,
    cycleStage_two x, deletion_cycleStage x⟩

/-! ## Lineage is too coarse -/

/-- The lineage of a set of derivations: the tokens it used, or nothing when there is no
derivation. -/
def lineage : List (Derivation σ) → Option (Finset σ)
  | [] => none
  | ds@(_ :: _) => some ds.flatten.toFinset

/-- **No operation on lineage computes the lineage of a retraction.**  The derivation sets `x` or
`y`, and `x` with `y`, have one lineage; withdrawing `x` leaves `y` from the first and nothing from
the second. -/
theorem lineage_not_deletion_compatible {x y : σ} (hxy : x ≠ y) :
    ¬ ∃ f : Option (Finset σ) → Option (Finset σ),
      ∀ ds : List (Derivation σ), f (lineage ds) = lineage (surviving {x} ds) := by
  rintro ⟨f, hf⟩
  have alternatives := hf [[x], [y]]
  have joint := hf [[x, y]]
  have same : lineage [[x], [y]] = lineage ([[x, y]] : List (Derivation σ)) := rfl
  have left : surviving {x} [[x], [y]] = [[y]] := by simp [surviving, hxy.symm]
  have right : surviving {x} [[x, y]] = [] := by simp [surviving]
  rw [left] at alternatives
  rw [right, ← same, alternatives] at joint
  simp [lineage] at joint

/-- **How-provenance tells apart what lineage conflates.** -/
theorem provenance_separates_lineage {x y : σ} (hxy : x ≠ y) :
    lineage [[x], [y]] = lineage ([[x, y]] : List (Derivation σ)) ∧
      deletion {x} (provenance [[x], [y]]) = MvPolynomial.X y ∧
      deletion {x} (provenance [[x, y]]) = 0 := by
  refine ⟨rfl, ?_, ?_⟩
  · rw [deletion_provenance]
    simp [surviving, hxy.symm, provOf]
  · rw [deletion_provenance]
    simp [surviving]

namespace Controls

/-! ## A deduction with revision -/

/-- Base claims: `A → B` observed by source `0`, `B → C` by sources `1` and `2`, and `A → C`
directly by source `3`. -/
inductive Base where
  | ab
  | bc₁
  | bc₂
  | ac

/-- The provenance of the base claims. -/
noncomputable def ann : Base → MvPolynomial ℕ ℕ
  | .ab => X 0
  | .bc₁ => X 1
  | .bc₂ => X 2
  | .ac => X 3

/-- `A → C`: the direct observation, revised with the deduction through `B`, whose second premise
is the revision of its two observations. -/
def conclusion : Derived Base :=
  .revise (.base .ac) (.deduce (.base .ab) (.revise (.base .bc₁) (.base .bc₂)))

/-- The number of derivations of an annotation. -/
noncomputable def derivations (p : MvPolynomial ℕ ℕ) : ℕ := eval (fun _ => 1) p

theorem conclusion_prov : conclusion.prov ann = X 3 + X 0 * (X 1 + X 2) := rfl

/-- **Withdrawing a premise's source propagates to the conclusion**, which is what deriving from the
retracted base gives: the deduction keeps its other derivation. -/
theorem withdraw_bc₁ :
    deletion {1} (conclusion.prov ann) = conclusion.prov (fun b => deletion {1} (ann b)) ∧
      deletion {1} (conclusion.prov ann) = X 3 + X 0 * X 2 ∧
      derivations (conclusion.prov ann) = 3 ∧
      derivations (deletion {1} (conclusion.prov ann)) = 2 := by
  refine ⟨deletion_prov _ _ _, ?_, ?_, ?_⟩
  · rw [conclusion_prov]
    simp [deletion_X]
  · simp [derivations, conclusion_prov]
  · rw [conclusion_prov]
    simp [deletion_X, derivations]

/-- **Withdrawing the first premise's source removes the deduction**; the direct observation
stands. -/
theorem withdraw_ab : deletion {0} (conclusion.prov ann) = X 3 := by
  rw [conclusion_prov]
  simp [deletion_X]

/-- **Withdrawing that source and the direct one deletes the conclusion.** -/
theorem withdraw_ab_ac : deletion {0, 3} (conclusion.prov ann) = 0 := by
  rw [conclusion_prov]
  simp [deletion_X]

/-! ## Symbol forgetting against data retraction -/

/-- Claims `p`, `p → q` and `q`. -/
inductive Claim where
  | p
  | pq
  | q

/-- The claims that mention the symbol `p`. -/
def mentionsP : Claim → Bool
  | .p => true
  | .pq => true
  | .q => false

/-- `p` observed by source `0`, `p → q` by source `1`, and `q` derived from both. -/
noncomputable def state : Claim → MvPolynomial ℕ ℕ
  | .p => X 0
  | .pq => X 1
  | .q => X 0 * X 1

/-- Forgetting the symbol `p`: claims mentioning it are dropped, and every other claim keeps its
evidence. -/
noncomputable def forgetSymbolP (W : Claim → MvPolynomial ℕ ℕ) : Claim → MvPolynomial ℕ ℕ :=
  fun c => if mentionsP c then 0 else W c

/-- **Forgetting the symbol keeps the consequence; retracting the observation retracts it.** -/
theorem symbol_and_data_forgetting_differ :
    forgetSymbolP state .q = X 0 * X 1 ∧ deletion {0} (state .q) = 0 ∧
      forgetSymbolP state .q ≠ deletion {0} (state .q) := by
  have kept : forgetSymbolP state .q = X 0 * X 1 := rfl
  have retracted : deletion {0} (state .q) = 0 := by simp [state, deletion_X]
  refine ⟨kept, retracted, ?_⟩
  rw [kept, retracted]
  exact mul_ne_zero (X_ne_zero 0) (X_ne_zero 1)

end Controls

end Mettapedia.PLN.WorldModel.ProvenanceRetraction

open Mettapedia.PLN.WorldModel.ProvenanceRetraction in
#print axioms coeff_deletion
open Mettapedia.PLN.WorldModel.ProvenanceRetraction in
#print axioms deletion_deletion
open Mettapedia.PLN.WorldModel.ProvenanceRetraction in
#print axioms deletion_provenance
open Mettapedia.PLN.WorldModel.ProvenanceRetraction in
#print axioms interp_deletion_provenance
open Mettapedia.PLN.WorldModel.ProvenanceRetraction in
#print axioms deletion_prov
open Mettapedia.PLN.WorldModel.ProvenanceRetraction in
#print axioms provSupportClosedLayer
open Mettapedia.PLN.WorldModel.ProvenanceRetraction in
#print axioms provRetractionLayer
open Mettapedia.PLN.WorldModel.ProvenanceRetraction in
#print axioms forgetTokens_relevance
open Mettapedia.PLN.WorldModel.ProvenanceRetraction in
#print axioms forgetTokens_no_manufactured
open Mettapedia.PLN.WorldModel.ProvenanceRetraction in
#print axioms deletion_bagProvenance
open Mettapedia.PLN.WorldModel.ProvenanceRetraction in
#print axioms cycle_counting_fails_provenance_succeeds
open Mettapedia.PLN.WorldModel.ProvenanceRetraction in
#print axioms lineage_not_deletion_compatible
open Mettapedia.PLN.WorldModel.ProvenanceRetraction in
#print axioms provenance_separates_lineage
open Mettapedia.PLN.WorldModel.ProvenanceRetraction in
#print axioms Controls.withdraw_bc₁
open Mettapedia.PLN.WorldModel.ProvenanceRetraction in
#print axioms Controls.withdraw_ab
open Mettapedia.PLN.WorldModel.ProvenanceRetraction in
#print axioms Controls.withdraw_ab_ac
open Mettapedia.PLN.WorldModel.ProvenanceRetraction in
#print axioms Controls.symbol_and_data_forgetting_differ
