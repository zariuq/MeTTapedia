import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions.Ambient

/-!
# Bounded regions have no top, and what happens to the bound

A **bounded region** (`IsBoundedRegion`) is a decidable region with a computable bound on the search.
For a property that is not decidable:

* **every bounded region misses a certified instance and an uncertified one**
  (`misses_certified`, `misses_uncertified`): containing every certified instance would make the
  property the certified part of the region, and containing every uncertified one would make it the
  complement of the region together with that part; both are decidable;
* **so it is strictly contained in another bounded region, in two ways**
  (`exists_strict_extension`, `exists_strict_extension_uncertified`). Adding a missed certified instance
  changes the bound at that instance only, where it becomes the least certificate of the instance
  (`extend_certified`); adding a missed uncertified instance keeps the bound;
* **there is an infinite strictly increasing chain of bounded regions** (`exists_strict_chain`), each
  step adding a certified instance;
* **the bounds outrun every computable function**: for every family of regions with bounds and every
  computable `B`, infinitely many certified instances have `B q` below the bound of every region of the
  family that contains them (`bounds_exceed`). The budget regions of the ambient search
  (`budgetRegion`) are such a family and cover the property, so every certified instance lies in one.

**The checkers of `CheckerTower` are the bounded regions inside the property.** A computable sound
checker has a total computable certificate on its accepted instances (`soundChecker_certificate`, the
total form of `CheckerTower.certificate_choice`, which gives a partial one); its accepted set is a
bounded region (`soundChecker_boundedOn`). Conversely the certified part of a bounded region is a sound
checker accepting exactly that part (`soundChecker_of_boundedRegion`). A bounded region also answers
no: it decides the property on all its instances, certified or not.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions

open CheckerTower (Certified SoundChecker)

section NoTop

variable {Q : Type} [Primcodable Q] (R : ℕ → Q → Bool)

/-- **A bounded region**: a decidable region with a computable bound on the search. -/
def IsBoundedRegion (D : Q → Bool) (b : Q → ℕ) : Prop :=
  Computable D ∧ Computable b ∧ BoundsOn R D b

/-- The empty region is bounded. -/
theorem empty_bounded : IsBoundedRegion R (fun _ => false) fun _ => 0 :=
  ⟨Computable.const false, Computable.const 0, fun _ inside => Bool.noConfusion inside⟩

/-- **A bounded region of an undecidable property misses a certified instance.** -/
theorem misses_certified (hR : Computable₂ R) (undecidable : ¬ ComputablePred (Certified R))
    {D : Q → Bool} {b : Q → ℕ} (region : IsBoundedRegion R D b) :
    ∃ q, Certified R q ∧ D q = false := by
  by_contra noneMissed
  apply undecidable
  have inside : ∀ q, Certified R q → D q = true := fun q certified => by
    cases h : D q with
    | true => rfl
    | false => exact absurd ⟨q, certified, h⟩ noneMissed
  refine ComputablePred.computable_iff.mpr ⟨fun q => anyBelow R q (b q + 1),
    computable_anyBelow R hR (m := fun q => b q + 1)
      ((Computable.succ.comp region.2.1).of_eq fun _ => rfl),
    funext fun q => propext ?_⟩
  show Certified R q ↔ anyBelow R q (b q + 1) = true
  constructor
  · intro certified
    exact (decide_of_bounds R region.2.2 (inside q certified)).mpr certified
  · intro found
    obtain ⟨n, _, hit⟩ := (anyBelow_iff R q (b q + 1)).mp found
    exact ⟨n, hit⟩

/-- **…and an uncertified one.** -/
theorem misses_uncertified (hR : Computable₂ R) (undecidable : ¬ ComputablePred (Certified R))
    {D : Q → Bool} {b : Q → ℕ} (region : IsBoundedRegion R D b) :
    ∃ q, ¬ Certified R q ∧ D q = false := by
  by_contra noneMissed
  apply undecidable
  have outside : ∀ q, D q = false → Certified R q := fun q h => by
    by_contra notCertified
    exact noneMissed ⟨q, notCertified, h⟩
  refine ComputablePred.computable_iff.mpr ⟨fun q => !D q || anyBelow R q (b q + 1),
    Primrec.or.to_comp.comp (Primrec.not.to_comp.comp region.1)
      (computable_anyBelow R hR (m := fun q => b q + 1)
        ((Computable.succ.comp region.2.1).of_eq fun _ => rfl)),
    funext fun q => propext ?_⟩
  show Certified R q ↔ (!D q || anyBelow R q (b q + 1)) = true
  cases h : D q with
  | false => exact ⟨fun _ => rfl, fun _ => outside q h⟩
  | true => exact (decide_of_bounds R region.2.2 h).symm

variable [DecidableEq Q]

/-- **Adding a certified instance**: the bound is unchanged except at the new instance, where it is a
certificate of it. -/
theorem extend_certified {D : Q → Bool} {b : Q → ℕ} (region : IsBoundedRegion R D b) (q₀ : Q)
    (n₀ : ℕ) (found : R n₀ q₀ = true) :
    IsBoundedRegion R (fun q => D q || decide (q = q₀)) fun q => if q = q₀ then n₀ else b q := by
  have isNew : Computable fun q => decide (q = q₀) :=
    (Primrec.eq.decide.comp Primrec.id (Primrec.const q₀)).to_comp
  refine ⟨Primrec.or.to_comp.comp region.1 isNew,
    (Computable.cond isNew (Computable.const n₀) region.2.1).of_eq fun q => ?_, ?_⟩
  · by_cases h : q = q₀ <;> simp [h]
  · intro q inside certified
    by_cases h : q = q₀
    · subst h
      exact ⟨n₀, by simp, found⟩
    · have inD : D q = true := by simpa [h] using inside
      obtain ⟨n, le, hit⟩ := region.2.2 q inD certified
      exact ⟨n, by simpa [h] using le, hit⟩

/-- **Adding an uncertified instance keeps the bound.** -/
theorem extend_uncertified {D : Q → Bool} {b : Q → ℕ} (region : IsBoundedRegion R D b) (q₀ : Q)
    (uncertified : ¬ Certified R q₀) : IsBoundedRegion R (fun q => D q || decide (q = q₀)) b := by
  have isNew : Computable fun q => decide (q = q₀) :=
    (Primrec.eq.decide.comp Primrec.id (Primrec.const q₀)).to_comp
  refine ⟨Primrec.or.to_comp.comp region.1 isNew, region.2.1, fun q inside certified => ?_⟩
  have ne : q ≠ q₀ := fun same => uncertified (same ▸ certified)
  exact region.2.2 q (by simpa [ne] using inside) certified

/-- **No top, with bounds**: every bounded region of an undecidable property is strictly contained in
another, which adds a certified instance `q₀` and changes the bound only at `q₀`, to its least
certificate. -/
theorem exists_strict_extension (hR : Computable₂ R) (undecidable : ¬ ComputablePred (Certified R))
    {D : Q → Bool} {b : Q → ℕ} (region : IsBoundedRegion R D b) :
    ∃ q₀ n₀, Certified R q₀ ∧ D q₀ = false ∧ R n₀ q₀ = true ∧ (∀ n < n₀, R n q₀ = false) ∧
      IsBoundedRegion R (fun q => D q || decide (q = q₀)) fun q => if q = q₀ then n₀ else b q := by
  obtain ⟨q₀, certified, missed⟩ := misses_certified R hR undecidable region
  exact ⟨q₀, Nat.find certified, certified, missed, Nat.find_spec certified,
    fun n lt => Bool.eq_false_iff.mpr (Nat.find_min certified lt),
    extend_certified R region q₀ _ (Nat.find_spec certified)⟩

/-- **No top, on the side of no**: every bounded region of an undecidable property is strictly contained
in another with the same bound, which adds an uncertified instance. -/
theorem exists_strict_extension_uncertified (hR : Computable₂ R)
    (undecidable : ¬ ComputablePred (Certified R)) {D : Q → Bool} {b : Q → ℕ}
    (region : IsBoundedRegion R D b) :
    ∃ q₀, ¬ Certified R q₀ ∧ D q₀ = false ∧ IsBoundedRegion R (fun q => D q || decide (q = q₀)) b := by
  obtain ⟨q₀, uncertified, missed⟩ := misses_uncertified R hR undecidable region
  exact ⟨q₀, uncertified, missed, extend_uncertified R region q₀ uncertified⟩

/-- **An infinite strictly increasing chain of bounded regions**, each adding a certified instance. -/
theorem exists_strict_chain (hR : Computable₂ R) (undecidable : ¬ ComputablePred (Certified R)) :
    ∃ (D : ℕ → Q → Bool) (b : ℕ → Q → ℕ), (∀ k, IsBoundedRegion R (D k) (b k)) ∧
      ∀ k, (∀ q, D k q = true → D (k + 1) q = true) ∧
        ∃ q, D (k + 1) q = true ∧ D k q = false ∧ Certified R q := by
  classical
  let Region := {p : (Q → Bool) × (Q → ℕ) // IsBoundedRegion R p.1 p.2}
  have step : ∀ p : Region, ∃ p' : Region, (∀ q, p.1.1 q = true → p'.1.1 q = true) ∧
      ∃ q, p'.1.1 q = true ∧ p.1.1 q = false ∧ Certified R q := by
    intro p
    obtain ⟨q₀, n₀, certified, missed, _, _, region'⟩ :=
      exists_strict_extension R hR undecidable p.2
    exact ⟨⟨(_, _), region'⟩, fun q inside => by simp [inside], q₀,
      Bool.or_eq_true_iff.mpr (Or.inr (decide_eq_true rfl)), missed, certified⟩
  let start : Region := ⟨(fun _ => false, fun _ => 0), empty_bounded R⟩
  let seq : ℕ → Region := fun k => Nat.rec start (fun _ p => Classical.choose (step p)) k
  exact ⟨fun k => (seq k).1.1, fun k => (seq k).1.2, fun k => (seq k).2,
    fun k => Classical.choose_spec (step (seq k))⟩

end NoTop

section Exceed

variable {Q : Type} [Primcodable Q] (R : ℕ → Q → Bool)

/-- **The bounds outrun every computable function**: for any family of regions with bounds, infinitely
many certified instances have `B q` below the bound of every region of the family containing them. -/
theorem bounds_exceed (hR : Computable₂ R) (undecidable : ¬ ComputablePred (Certified R))
    (D : ℕ → Q → Bool) (b : ℕ → Q → ℕ) (bounds : ∀ k, BoundsOn R (D k) (b k)) {B : Q → ℕ}
    (hB : Computable B) :
    {q | Certified R q ∧ ∀ k, D k q = true → B q < b k q}.Infinite := by
  refine Set.Infinite.mono ?_ (exceeded_infinite R hR undecidable hB)
  rintro q ⟨certified, beyond⟩
  refine ⟨certified, fun k inside => ?_⟩
  obtain ⟨n, le, found⟩ := bounds k q inside certified
  by_contra small
  rw [beyond n (le.trans (Nat.le_of_not_lt small))] at found
  exact Bool.noConfusion found

/-- **On the budget regions**: every budget that answers one of these instances exceeds `B` there. -/
theorem budgets_exceed (hR : Computable₂ R) (undecidable : ¬ ComputablePred (Certified R))
    {B : Q → ℕ} (hB : Computable B) :
    {q | Certified R q ∧ ∀ k, budgetRegion R k q = true → B q < k}.Infinite :=
  bounds_exceed R hR undecidable (budgetRegion R) (fun k _ => k) (budgetRegion_bounds R) hB

end Exceed

/-! ## Sound checkers are the bounded regions inside the property -/

section Checkers

variable (R : ℕ → ℕ → Bool)

/-- **A computable sound checker has a total computable certificate** on the instances it accepts. -/
theorem soundChecker_certificate (hR : Computable₂ R) {c : ℕ → Bool}
    (sound : SoundChecker (Certified R) c) : CertificateOn R c :=
  certificateOn_of_decidedOn R hR sound.1
    ⟨fun _ => true, Computable.const true, fun q accepted => ⟨fun _ => sound.2 q accepted, fun _ => rfl⟩⟩

/-- **The accepted set of a computable sound checker is a bounded region.** -/
theorem soundChecker_boundedOn (hR : Computable₂ R) {c : ℕ → Bool}
    (sound : SoundChecker (Certified R) c) : BoundedOn R c :=
  boundedOn_of_certificateOn R (soundChecker_certificate R hR sound)

/-- **The certified part of a bounded region is a sound checker** accepting exactly that part. -/
theorem soundChecker_of_boundedRegion (hR : Computable₂ R) {D : ℕ → Bool} {b : ℕ → ℕ}
    (region : IsBoundedRegion R D b) :
    SoundChecker (Certified R) (fun q => D q && anyBelow R q (b q + 1)) ∧
      ∀ q, (D q && anyBelow R q (b q + 1)) = true ↔ D q = true ∧ Certified R q := by
  have accepts : ∀ q, (D q && anyBelow R q (b q + 1)) = true ↔ D q = true ∧ Certified R q := by
    intro q
    rw [Bool.and_eq_true_iff]
    constructor
    · rintro ⟨inside, found⟩
      exact ⟨inside, (decide_of_bounds R region.2.2 inside).mp found⟩
    · rintro ⟨inside, certified⟩
      exact ⟨inside, (decide_of_bounds R region.2.2 inside).mpr certified⟩
  refine ⟨⟨Primrec.and.to_comp.comp region.1
    (computable_anyBelow R hR (m := fun q => b q + 1)
      ((Computable.succ.comp region.2.1).of_eq fun _ => rfl)),
    fun q accepted => ((accepts q).mp accepted).2⟩, accepts⟩

end Checkers

/-! ## Controls -/

namespace Controls

-- Equality of codes is decided through their numbers.
attribute [local instance] Encodable.decidableEqOfEncodable

/-- The program `zero` halts at step index `1`. -/
theorem haltR_zero : haltR 1 Nat.Partrec.Code.zero = true := by
  simp [haltR, Nat.Partrec.Code.evaln]

/-- The extension of the empty region of the halting property by a program that halts at once. -/
theorem halting_first_extension :
    IsBoundedRegion haltR (fun c => false || decide (c = Nat.Partrec.Code.zero))
      fun c => if c = Nat.Partrec.Code.zero then 1 else 0 :=
  extend_certified haltR (empty_bounded haltR) _ 1 haltR_zero

/-- The halting property has an infinite strictly increasing chain of bounded regions. -/
theorem halting_chain :
    ∃ (D : ℕ → Nat.Partrec.Code → Bool) (b : ℕ → Nat.Partrec.Code → ℕ),
      (∀ k, IsBoundedRegion haltR (D k) (b k)) ∧
      ∀ k, (∀ q, D k q = true → D (k + 1) q = true) ∧
        ∃ q, D (k + 1) q = true ∧ D k q = false ∧ Certified haltR q :=
  exists_strict_chain haltR haltR_computable not_computablePred_haltR

/-- **Control: a decidable property has a top bounded region**, all instances, bounded by the instance. -/
theorem square_top : IsBoundedRegion squareR (fun _ => true) id :=
  ⟨Computable.const true, Computable.id, square_bounds⟩

end Controls

#print axioms empty_bounded
#print axioms misses_certified
#print axioms misses_uncertified
#print axioms extend_certified
#print axioms extend_uncertified
#print axioms exists_strict_extension
#print axioms exists_strict_extension_uncertified
#print axioms exists_strict_chain
#print axioms bounds_exceed
#print axioms budgets_exceed
#print axioms soundChecker_certificate
#print axioms soundChecker_boundedOn
#print axioms soundChecker_of_boundedRegion
#print axioms Controls.halting_first_extension
#print axioms Controls.halting_chain
#print axioms Controls.square_top

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions
