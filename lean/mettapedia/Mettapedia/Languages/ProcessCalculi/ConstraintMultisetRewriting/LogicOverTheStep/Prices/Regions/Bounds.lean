import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.CheckerTower

/-!
# Regions with a certificate bound: the region theorem

A property of coded instances is given by a decidable certificate relation `R`
(`CheckerTower.Certified R q := ∃ n, R n q = true`). The ambient check searches `n = 0, 1, 2, …` for a
certificate. On a **region** `D : Q → Bool` the search may be **bounded** by a function `b` of the
instance (`BoundsOn`: every certified instance of `D` has a certificate at most `b q`).

## The region theorem

For a computable certificate relation and a **decidable** region, three statements are equivalent
(`region_theorem`, `certificate_iff_decided`):

* the search is bounded on `D` by a computable function of the instance (`BoundedOn`);
* the property is decided on `D` by a computable function (`DecidedOn`);
* a computable function of the instance is a certificate on the certified part of `D`
  (`CertificateOn`); it can be taken to be the least certificate (`least_certificate_of_decidedOn`).

Bounded search decides (`decidedOn_of_boundedOn`, which needs no decidability of `D`); a decision on a
decidable region makes the search for the least certificate total, hence computable
(`least_certificate_of_decidedOn`, through Mathlib's `Computable.find`); a certificate is its own bound
(`boundedOn_of_certificateOn`). So the property decided on `D` is the same as `D ∩ Certified R`
decidable (`decidedOn_iff_computablePred`).

**The decidability of the region cannot be dropped.** The region of all certified instances is not
decidable when the property is not; the constant `true` decides the property on it
(`decidedOn_certifiedRegion`), and no computable function bounds the search on it
(`not_boundedOn_certifiedRegion`). The instance: halting on input zero, with the step index of bounded
evaluation as certificate (`haltR`, `halting_region_decided`, `halting_region_unbounded`).

## The algebra

* **Invariant: the property, not the format.** Two certificate relations with the same certified
  instances have the same bounded regions (`boundedOn_congr`); the bound itself depends on the format
  (`Controls.format_bound`: the least certificates `q` and `0` for the same property).
* **Composition.** A union of two regions is bounded by the maximum of their bounds
  (`boundsOn_union`, `boundedOn_union`); a subregion keeps the bound (`boundsOn_mono`); a larger bound
  still bounds (`boundsOn_of_le`); a certificate on a region pulls back along a computable reduction that
  translates certificates (`certificateOn_comap`); a finite table is a bounded region with a constant
  bound (`table_boundedOn`).
* **Decided cheaply:** membership in the region (by hypothesis), a given certificate (`R` computable),
  and on a bounded region the property itself, by bounded search (`decide_of_bounds`).

## Controls

Positive: perfect squares, certificate the root, bound the instance itself (`Controls.square_bounds`).
Negative: the certified region of halting (above).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions

open CheckerTower (Certified)
open Nat.Partrec

/-! ## Bounded search -/

section Search

variable {Q : Type} [Primcodable Q] (R : ℕ → Q → Bool)

/-- **Bounded search**: whether some number below `m` is a certificate of `q`. -/
def anyBelow (q : Q) (m : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun n found => found || R n q) m

omit [Primcodable Q] in
theorem anyBelow_zero (q : Q) : anyBelow R q 0 = false := rfl

omit [Primcodable Q] in
theorem anyBelow_succ (q : Q) (m : ℕ) : anyBelow R q (m + 1) = (anyBelow R q m || R m q) := rfl

omit [Primcodable Q] in
theorem anyBelow_iff (q : Q) : ∀ m, anyBelow R q m = true ↔ ∃ n < m, R n q = true
  | 0 => by simp [anyBelow_zero]
  | m + 1 => by
    rw [anyBelow_succ, Bool.or_eq_true, anyBelow_iff q m]
    constructor
    · rintro (⟨n, lt, found⟩ | found)
      · exact ⟨n, by omega, found⟩
      · exact ⟨m, by omega, found⟩
    · rintro ⟨n, lt, found⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp lt with lt | same
      · exact Or.inl ⟨n, lt, found⟩
      · rw [same] at found
        exact Or.inr found

/-- Bounded search is computable when the certificate relation and the bound are. -/
theorem computable_anyBelow (hR : Computable₂ R) {m : Q → ℕ} (hm : Computable m) :
    Computable fun q => anyBelow R q (m q) := by
  have step : Computable₂ fun (q : Q) (p : ℕ × Bool) => p.2 || R p.1 q :=
    (Primrec.or.to_comp.comp (Computable.snd.comp Computable.snd)
      (hR.comp (Computable.fst.comp Computable.snd) Computable.fst)).to₂
  exact (Computable.nat_rec hm (Computable.const false) step).of_eq fun _ => rfl

end Search

/-! ## Regions, bounds, decisions, certificates -/

section Region

variable {Q : Type} [Primcodable Q] (R : ℕ → Q → Bool)

/-- **`b` bounds the search for a certificate on the region `D`**: every certified instance of `D`
has a certificate at most `b q`. -/
def BoundsOn (D : Q → Bool) (b : Q → ℕ) : Prop :=
  ∀ q, D q = true → Certified R q → ∃ n ≤ b q, R n q = true

/-- **The search is computably bounded on `D`.** -/
def BoundedOn (D : Q → Bool) : Prop :=
  ∃ b : Q → ℕ, Computable b ∧ BoundsOn R D b

/-- **The property is decided on `D`** by a computable function. -/
def DecidedOn (D : Q → Bool) : Prop :=
  ∃ f : Q → Bool, Computable f ∧ ∀ q, D q = true → (f q = true ↔ Certified R q)

/-- **A computable certificate on the certified part of `D`.** -/
def CertificateOn (D : Q → Bool) : Prop :=
  ∃ c : Q → ℕ, Computable c ∧ ∀ q, D q = true → Certified R q → R (c q) q = true

omit [Primcodable Q] in
/-- **On its region, bounded search answers the property.** -/
theorem decide_of_bounds {D : Q → Bool} {b : Q → ℕ} (bounds : BoundsOn R D b) {q : Q}
    (inside : D q = true) : anyBelow R q (b q + 1) = true ↔ Certified R q := by
  rw [anyBelow_iff]
  constructor
  · rintro ⟨n, _, found⟩
    exact ⟨n, found⟩
  · intro certified
    obtain ⟨n, le, found⟩ := bounds q inside certified
    exact ⟨n, Nat.lt_succ_of_le le, found⟩

/-- **A bound decides**: no decidability of the region is needed. -/
theorem decidedOn_of_boundedOn (hR : Computable₂ R) {D : Q → Bool} (bounded : BoundedOn R D) :
    DecidedOn R D := by
  obtain ⟨b, hb, bounds⟩ := bounded
  exact ⟨fun q => anyBelow R q (b q + 1),
    computable_anyBelow R hR (m := fun q => b q + 1) ((Computable.succ.comp hb).of_eq fun _ => rfl),
    fun q inside => decide_of_bounds R bounds inside⟩

/-- **On a decidable region, a decision gives the least certificate as a total computable function**:
the search for a certificate is made total by answering `0` off the decided part, and its least
solution is computable (`Computable.find`). -/
theorem least_certificate_of_decidedOn (hR : Computable₂ R) {D : Q → Bool} (hD : Computable D)
    (decided : DecidedOn R D) :
    ∃ c : Q → ℕ, Computable c ∧ ∀ q, D q = true → Certified R q →
      R (c q) q = true ∧ ∀ n < c q, R n q = false := by
  obtain ⟨f, hf, spec⟩ := decided
  have exists_n : ∀ q, ∃ n, (!(D q && f q) || R n q) = true := by
    intro q
    cases accepted : (D q && f q) with
    | false => exact ⟨0, rfl⟩
    | true =>
      obtain ⟨inside, yes⟩ := Bool.and_eq_true_iff.mp accepted
      obtain ⟨n, found⟩ := (spec q inside).mp yes
      exact ⟨n, by simp [found]⟩
  have computableP : ComputablePred fun p : Q × ℕ => (!(D p.1 && f p.1) || R p.2 p.1) = true :=
    ComputablePred.computable_iff.mpr ⟨fun p => !(D p.1 && f p.1) || R p.2 p.1,
      Primrec.or.to_comp.comp
        (Primrec.not.to_comp.comp (Primrec.and.to_comp.comp (hD.comp Computable.fst)
          (hf.comp Computable.fst)))
        (hR.comp Computable.snd Computable.fst), rfl⟩
  refine ⟨fun q => Nat.find (exists_n q),
    Computable.find (P := fun q n => (!(D q && f q) || R n q) = true) computableP exists_n,
    fun q inside certified => ?_⟩
  have accepted : (D q && f q) = true :=
    Bool.and_eq_true_iff.mpr ⟨inside, (spec q inside).mpr certified⟩
  have key : ∀ m, (!(D q && f q) || R m q) = true ↔ R m q = true := by
    intro m
    simp only [accepted, Bool.not_true, Bool.false_or]
  refine ⟨(key _).mp (Nat.find_spec (exists_n q)), fun n lt => ?_⟩
  have notHolds := Nat.find_min (exists_n q) lt
  exact Bool.eq_false_iff.mpr fun yes => notHolds ((key n).mpr yes)

/-- **A decision on a decidable region gives a computable certificate.** -/
theorem certificateOn_of_decidedOn (hR : Computable₂ R) {D : Q → Bool} (hD : Computable D)
    (decided : DecidedOn R D) : CertificateOn R D := by
  obtain ⟨c, hc, spec⟩ := least_certificate_of_decidedOn R hR hD decided
  exact ⟨c, hc, fun q inside certified => (spec q inside certified).1⟩

/-- **A certificate is its own bound.** -/
theorem boundedOn_of_certificateOn {D : Q → Bool} (certificate : CertificateOn R D) :
    BoundedOn R D := by
  obtain ⟨c, hc, valid⟩ := certificate
  exact ⟨c, hc, fun q inside certified => ⟨c q, le_rfl, valid q inside certified⟩⟩

/-- **The region theorem**: on a decidable region, the search is computably bounded exactly when the
property is decided. -/
theorem region_theorem (hR : Computable₂ R) {D : Q → Bool} (hD : Computable D) :
    BoundedOn R D ↔ DecidedOn R D :=
  ⟨decidedOn_of_boundedOn R hR, fun decided =>
    boundedOn_of_certificateOn R (certificateOn_of_decidedOn R hR hD decided)⟩

/-- **The certificate form**: on a decidable region, a computable certificate exists exactly when the
property is decided. -/
theorem certificate_iff_decided (hR : Computable₂ R) {D : Q → Bool} (hD : Computable D) :
    CertificateOn R D ↔ DecidedOn R D :=
  ⟨fun certificate => decidedOn_of_boundedOn R hR (boundedOn_of_certificateOn R certificate),
    certificateOn_of_decidedOn R hR hD⟩

/-- **On a bounded decidable region the least certificate is computable.** -/
theorem least_certificate_of_boundedOn (hR : Computable₂ R) {D : Q → Bool} (hD : Computable D)
    (bounded : BoundedOn R D) :
    ∃ c : Q → ℕ, Computable c ∧ ∀ q, D q = true → Certified R q →
      R (c q) q = true ∧ ∀ n < c q, R n q = false :=
  least_certificate_of_decidedOn R hR hD (decidedOn_of_boundedOn R hR bounded)

/-- **Decided on `D` is the same as `D ∩ Certified R` decidable**, for a decidable region. -/
theorem decidedOn_iff_computablePred {D : Q → Bool} (hD : Computable D) :
    DecidedOn R D ↔ ComputablePred fun q => D q = true ∧ Certified R q := by
  constructor
  · rintro ⟨f, hf, spec⟩
    refine ComputablePred.computable_iff.mpr ⟨fun q => D q && f q,
      Primrec.and.to_comp.comp hD hf, funext fun q => propext ?_⟩
    show (D q = true ∧ Certified R q) ↔ (D q && f q) = true
    rw [Bool.and_eq_true_iff]
    constructor
    · rintro ⟨inside, certified⟩
      exact ⟨inside, (spec q inside).mpr certified⟩
    · rintro ⟨inside, yes⟩
      exact ⟨inside, (spec q inside).mp yes⟩
  · intro decidable
    obtain ⟨g, hg, same⟩ := ComputablePred.computable_iff.mp decidable
    refine ⟨g, hg, fun q inside => ?_⟩
    have atQ : (D q = true ∧ Certified R q) = (g q = true) := congrFun same q
    rw [← atQ]
    exact ⟨fun both => both.2, fun certified => ⟨inside, certified⟩⟩

/-! ## The algebra of bounded regions -/

omit [Primcodable Q] in
/-- **Union, with the maximum of the bounds.** -/
theorem boundsOn_union {D₁ D₂ : Q → Bool} {b₁ b₂ : Q → ℕ} (h₁ : BoundsOn R D₁ b₁)
    (h₂ : BoundsOn R D₂ b₂) : BoundsOn R (fun q => D₁ q || D₂ q) (fun q => max (b₁ q) (b₂ q)) := by
  intro q inside certified
  rcases Bool.or_eq_true_iff.mp inside with in₁ | in₂
  · obtain ⟨n, le, found⟩ := h₁ q in₁ certified
    exact ⟨n, le.trans (le_max_left _ _), found⟩
  · obtain ⟨n, le, found⟩ := h₂ q in₂ certified
    exact ⟨n, le.trans (le_max_right _ _), found⟩

/-- **Bounded regions are closed under finite union.** -/
theorem boundedOn_union {D₁ D₂ : Q → Bool} (h₁ : BoundedOn R D₁) (h₂ : BoundedOn R D₂) :
    BoundedOn R fun q => D₁ q || D₂ q := by
  obtain ⟨b₁, hb₁, bounds₁⟩ := h₁
  obtain ⟨b₂, hb₂, bounds₂⟩ := h₂
  exact ⟨fun q => max (b₁ q) (b₂ q), Primrec.nat_max.to_comp.comp hb₁ hb₂,
    boundsOn_union R bounds₁ bounds₂⟩

omit [Primcodable Q] in
/-- **A subregion keeps the bound.** -/
theorem boundsOn_mono {D D' : Q → Bool} {b : Q → ℕ} (sub : ∀ q, D' q = true → D q = true)
    (bounds : BoundsOn R D b) : BoundsOn R D' b :=
  fun q inside certified => bounds q (sub q inside) certified

omit [Primcodable Q] in
/-- **A larger bound still bounds.** -/
theorem boundsOn_of_le {D : Q → Bool} {b b' : Q → ℕ} (le : ∀ q, b q ≤ b' q)
    (bounds : BoundsOn R D b) : BoundsOn R D b' := by
  intro q inside certified
  obtain ⟨n, small, found⟩ := bounds q inside certified
  exact ⟨n, small.trans (le q), found⟩

/-- **Finite sets of instances are decidable regions.** -/
theorem computable_mem_finset [DecidableEq Q] (T : Finset Q) :
    Computable fun q => decide (q ∈ T) := by
  induction T using Finset.induction_on with
  | empty => exact (Computable.const false).of_eq fun q => by simp
  | insert a T _ ih =>
    exact (Primrec.or.to_comp.comp (Primrec.eq.decide.comp Primrec.id (Primrec.const a)).to_comp
      ih).of_eq fun q => by simp [Finset.mem_insert]

/-- **A finite table is a bounded region**, with a constant bound: the largest least certificate of
its certified instances. -/
theorem table_boundedOn [DecidableEq Q] (T : Finset Q) : BoundedOn R fun q => decide (q ∈ T) := by
  classical
  let least : Q → ℕ := fun q => if h : Certified R q then Nat.find h else 0
  refine ⟨fun _ => T.sup least, Computable.const _, fun q inside certified => ?_⟩
  have member : q ∈ T := of_decide_eq_true inside
  refine ⟨Nat.find certified, ?_, Nat.find_spec certified⟩
  have atQ : least q = Nat.find certified := dif_pos certified
  exact (le_of_eq atQ.symm).trans (Finset.le_sup (f := least) member)

/-! ### Format invariance: the region depends on the property, not on the certificate format -/

/-- Being decided on a region depends only on the certified instances. -/
theorem decidedOn_congr {R₁ R₂ : ℕ → Q → Bool} (same : ∀ q, Certified R₁ q ↔ Certified R₂ q)
    {D : Q → Bool} : DecidedOn R₁ D ↔ DecidedOn R₂ D := by
  constructor
  · rintro ⟨f, hf, spec⟩
    exact ⟨f, hf, fun q inside => (spec q inside).trans (same q)⟩
  · rintro ⟨f, hf, spec⟩
    exact ⟨f, hf, fun q inside => (spec q inside).trans (same q).symm⟩

/-- **Two certificate formats for the same property have the same bounded regions.** -/
theorem boundedOn_congr {R₁ R₂ : ℕ → Q → Bool} (hR₁ : Computable₂ R₁) (hR₂ : Computable₂ R₂)
    (same : ∀ q, Certified R₁ q ↔ Certified R₂ q) {D : Q → Bool} (hD : Computable D) :
    BoundedOn R₁ D ↔ BoundedOn R₂ D := by
  rw [region_theorem R₁ hR₁ hD, region_theorem R₂ hR₂ hD]
  exact decidedOn_congr same

/-! ### Pulling a certificate back along a reduction -/

/-- **Memoization along a reduction**: a certificate on a region of `R` pulls back to a certificate on
the preimage region of `R'`, when the reduction reflects the property and translates certificates. -/
theorem certificateOn_comap {Q' : Type} [Primcodable Q'] (R' : ℕ → Q' → Bool) {D : Q → Bool}
    (g : Q' → Q) (translate : Q' → ℕ → ℕ) (hg : Computable g) (htranslate : Computable₂ translate)
    (reflects : ∀ q', Certified R' q' → Certified R (g q'))
    (carries : ∀ q' n, R n (g q') = true → R' (translate q' n) q' = true)
    (certificate : CertificateOn R D) : CertificateOn R' fun q' => D (g q') := by
  obtain ⟨c, hc, valid⟩ := certificate
  exact ⟨fun q' => translate q' (c (g q')), htranslate.comp Computable.id (hc.comp hg),
    fun q' inside certified => carries q' _ (valid (g q') inside (reflects q' certified))⟩

/-! ## The decidability of the region cannot be dropped -/

/-- The region of all certified instances (decided classically, not computably). -/
noncomputable def certifiedRegion (q : Q) : Bool :=
  @decide (Certified R q) (Classical.propDecidable _)

omit [Primcodable Q] in
theorem certifiedRegion_iff (q : Q) : certifiedRegion R q = true ↔ Certified R q := by
  unfold certifiedRegion
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

/-- **On the certified region the constant `true` decides the property.** -/
theorem decidedOn_certifiedRegion : DecidedOn R (certifiedRegion R) :=
  ⟨fun _ => true, Computable.const true, fun q inside =>
    ⟨fun _ => (certifiedRegion_iff R q).mp inside, fun _ => rfl⟩⟩

/-- **A bound on the certified region is a bound everywhere**, so it decides the property. -/
theorem not_boundedOn_certifiedRegion (hR : Computable₂ R)
    (undecidable : ¬ ComputablePred (Certified R)) : ¬ BoundedOn R (certifiedRegion R) := by
  rintro ⟨b, hb, bounds⟩
  apply undecidable
  have everywhere : BoundsOn R (fun _ => true) b := fun q _ certified =>
    bounds q ((certifiedRegion_iff R q).mpr certified) certified
  obtain ⟨f, hf, spec⟩ := decidedOn_of_boundedOn R hR ⟨b, hb, everywhere⟩
  exact ComputablePred.computable_iff.mpr ⟨f, hf, funext fun q =>
    propext (spec q rfl).symm⟩

/-- **So the region theorem needs a decidable region**: on the certified region of an undecidable
property the property is decided and the search is not bounded. -/
theorem decided_not_bounded (hR : Computable₂ R) (undecidable : ¬ ComputablePred (Certified R)) :
    DecidedOn R (certifiedRegion R) ∧ ¬ BoundedOn R (certifiedRegion R) :=
  ⟨decidedOn_certifiedRegion R, not_boundedOn_certifiedRegion R hR undecidable⟩

end Region

/-! ## Halting on input zero, with the step index as certificate -/

section Halting

/-- **The halting certificate**: program `c` has halted on input `0` by step index `n`. -/
def haltR (n : ℕ) (c : Code) : Bool := (Code.evaln n c 0).isSome

theorem haltR_computable : Computable₂ haltR :=
  (Primrec.option_isSome.comp
    (Code.primrec_evaln.comp (Primrec.pair Primrec.id (Primrec.const 0)))).to_comp

theorem certified_haltR_iff (c : Code) : Certified haltR c ↔ (Code.eval c 0).Dom :=
  (Mettapedia.Logic.ReverseMathematics.Omniscience.halts_iff_exists_haltBit c).symm

/-- **Halting on input zero is not decidable.** -/
theorem not_computablePred_haltR : ¬ ComputablePred (Certified haltR) := fun decidable =>
  ComputablePred.halting_problem 0 (decidable.of_eq fun c => certified_haltR_iff c)

/-- **The halting region is decided and not bounded.** -/
theorem halting_region_decided : DecidedOn haltR (certifiedRegion haltR) :=
  decidedOn_certifiedRegion haltR

theorem halting_region_unbounded : ¬ BoundedOn haltR (certifiedRegion haltR) :=
  not_boundedOn_certifiedRegion haltR haltR_computable not_computablePred_haltR

end Halting

/-! ## Controls -/

namespace Controls

/-- Perfect squares, with the root as certificate. -/
def squareR (n q : ℕ) : Bool := decide (n * n = q)

theorem squareR_computable : Computable₂ squareR :=
  (Primrec.eq.decide.comp (Primrec.nat_mul.comp Primrec.fst Primrec.fst) Primrec.snd).to_comp

/-- **Positive control: the instance itself bounds the root.** -/
theorem square_bounds : BoundsOn squareR (fun _ => true) id := by
  rintro q - ⟨n, found⟩
  have same : n * n = q := of_decide_eq_true found
  refine ⟨n, ?_, found⟩
  show n ≤ q
  rw [← same]
  exact Nat.le_mul_self n

theorem square_boundedOn : BoundedOn squareR fun _ => true :=
  ⟨id, Computable.id, square_bounds⟩

/-- Positive control: `9` is certified, `8` is not, read off by bounded search. -/
theorem square_nine : anyBelow squareR 9 (9 + 1) = true := by decide

theorem square_eight : anyBelow squareR 8 (8 + 1) = false := by decide

/-- Every instance, with the instance as certificate. -/
def selfR (n q : ℕ) : Bool := decide (n = q)

/-- Every instance, with `0` as certificate. -/
def zeroR (n _ : ℕ) : Bool := decide (n = 0)

theorem selfR_computable : Computable₂ selfR :=
  (Primrec.eq.decide.comp Primrec.fst Primrec.snd).to_comp

theorem zeroR_computable : Computable₂ zeroR :=
  (Primrec.eq.decide.comp Primrec.fst (Primrec.const 0)).to_comp

theorem self_zero_same (q : ℕ) : Certified selfR q ↔ Certified zeroR q :=
  ⟨fun _ => ⟨0, rfl⟩, fun _ => ⟨q, decide_eq_true rfl⟩⟩

/-- **The bound depends on the format, the region does not**: for the same property (every instance),
the least certificate is the instance itself in one format and `0` in the other, and both formats have
the same bounded regions. -/
theorem format_bound (q : ℕ) :
    (∀ n < q, selfR n q = false) ∧ selfR q q = true ∧ zeroR 0 q = true ∧
      (BoundedOn selfR (fun _ => true) ↔ BoundedOn zeroR fun _ => true) := by
  refine ⟨fun n lt => decide_eq_false (Nat.ne_of_lt lt), decide_eq_true rfl, rfl, ?_⟩
  exact boundedOn_congr selfR_computable zeroR_computable self_zero_same (Computable.const true)

end Controls

#print axioms anyBelow_iff
#print axioms computable_anyBelow
#print axioms decide_of_bounds
#print axioms decidedOn_of_boundedOn
#print axioms least_certificate_of_decidedOn
#print axioms certificateOn_of_decidedOn
#print axioms boundedOn_of_certificateOn
#print axioms region_theorem
#print axioms certificate_iff_decided
#print axioms least_certificate_of_boundedOn
#print axioms decidedOn_iff_computablePred
#print axioms boundsOn_union
#print axioms boundedOn_union
#print axioms boundsOn_mono
#print axioms boundsOn_of_le
#print axioms computable_mem_finset
#print axioms table_boundedOn
#print axioms decidedOn_congr
#print axioms boundedOn_congr
#print axioms certificateOn_comap
#print axioms decidedOn_certifiedRegion
#print axioms not_boundedOn_certifiedRegion
#print axioms decided_not_bounded
#print axioms haltR_computable
#print axioms certified_haltR_iff
#print axioms not_computablePred_haltR
#print axioms halting_region_decided
#print axioms halting_region_unbounded
#print axioms Controls.square_bounds
#print axioms Controls.square_boundedOn
#print axioms Controls.square_nine
#print axioms Controls.square_eight
#print axioms Controls.format_bound

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions
