import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.Algebra.Group.Irreducible.Defs
import Mathlib.Algebra.Group.Units.Basic

/-!
# Unique decomposition into primes, without a zero

Mathlib's factorization theory is stated for a commutative monoid *with zero*,
because it is written for rings.  The monoid of processes under parallel
composition has no zero.

That does not make the machinery inapplicable, and it would be wrong to say so:
`WithZero M` is a commutative monoid with zero for any commutative monoid `M`,
the embedding preserves units and divisibility, and zero divides nothing but
itself -- so the transport exists.  What it costs is that every statement then
quantifies over a phantom element that no process denotes, and every hypothesis
acquires a side condition excluding it.  The zero-free development below is
declined machinery rather than unavailable machinery, and it is declined so that
the statements read as statements about processes.

Where a notion here coincides with a Mathlib one, that is recorded as a theorem
rather than left to the reader: `reduced_iff_subsingleton_units` and
`irred_iff_irreducible` below.  `Irreducible` in particular is stated for a plain
monoid and needs no zero at all.

Two hypotheses carry the theorem and both are load-bearing:

* **Cancellation.**  Parallel composition must be cancellable, or a factor could
  be inserted and removed without trace.
* **Well-founded factorization.**  No element may factor forever.  This is the
  hypothesis a replicated process violates: with an unfolding law in the
  equational theory, a term equals that term beside a copy of its body, so the
  descent never stops.

Uniqueness needs a third thing that is *not* automatic and is the whole content
of the process-algebra literature on this question: that every irreducible is
prime.  It is assumed here rather than derived, and the two instantiations
differ exactly in how it is obtained -- freely when the monoid is free on its
irreducibles, and by a substantial argument when it is not.

The development is `Multiset`-valued: a decomposition is the multiset of its
factors, and uniqueness is equality of multisets.

The three hypotheses below are exactly those of Luttik and van Oostrom,
*Decomposition orders -- another generalisation of the fundamental theorem of
arithmetic*, Theoretical Computer Science 335 (2005), Theorem 17: cancellation,
well-founded divisibility, and every indecomposable prime with respect to
divisibility.  That paper works with *partial* commutative monoids, where a
product may be undefined; parallel composition is total, so the total case
suffices here.

Two things in that literature are not yet formalised and are named rather than
imitated.  Their Theorems 32 and 33 replace the third hypothesis by the
existence of a *decomposition order* -- a well-founded partial order with the
identity least, strictly compatible, precompositional and Archimedean -- and
show that a partial commutative monoid has unique decomposition *if and only
if* it admits one, the divisibility relation being the least such order.  That
is the sharper statement, and it is what would let the third hypothesis be
discharged rather than assumed.  And the fact that finite processes modulo
bisimulation satisfy the hypotheses is Milner and Moller, *Unique decomposition
of processes*, Theoretical Computer Science 107 (1993) 357-363; Luttik and van
Oostrom extend it to the weakly normed processes.
-/

namespace Mettapedia.Algebra

universe u

variable {M : Type u} [CommMonoid M]

/-- A monoid is **reduced** when the only invertible element is the identity.
Process monoids are reduced: a parallel composition is inert only if both
parands are. -/
def Reduced (M : Type u) [CommMonoid M] : Prop := ∀ a b : M, a * b = 1 → a = 1

/-- **Irreducible**: not the identity, and not a product of two non-identities. -/
def Irred (p : M) : Prop := p ≠ 1 ∧ ∀ a b : M, p = a * b → a = 1 ∨ b = 1

/-- **Prime**: not the identity, and dividing a product means dividing a factor. -/
def PrimeElt (p : M) : Prop := p ≠ 1 ∧ ∀ a b : M, p ∣ a * b → p ∣ a ∨ p ∣ b

/-- A **decomposition** of `a`: a multiset of irreducibles whose product is `a`. -/
def IsDecomposition (s : Multiset M) (a : M) : Prop :=
  (∀ p ∈ s, Irred p) ∧ s.prod = a

/-- Proper factorization: `b` is `a` times something that is not the identity. -/
def ProperFactor (b a : M) : Prop := ∃ c : M, a = b * c ∧ c ≠ 1

/-! ## The same notions, in Mathlib's vocabulary

Recorded as theorems so the two spellings cannot drift, and so a reader who
knows the standard names can see that nothing new is being asserted. -/

/-- **Reducedness is `Subsingleton Mˣ`.** -/
theorem reduced_iff_subsingleton_units : Reduced M ↔ Subsingleton Mˣ := by
  constructor
  · intro h
    refine ⟨fun u v => Units.ext ?_⟩
    have hu : (u : M) = 1 := h u ↑u⁻¹ u.mul_inv
    have hv : (v : M) = 1 := h v ↑v⁻¹ v.mul_inv
    rw [hu, hv]
  · intro _ a b hab
    exact isUnit_iff_eq_one.mp (IsUnit.of_mul_eq_one b hab)

/-- **And irreducibility is Mathlib's `Irreducible`**, which is stated for a
plain monoid and needs no zero. -/
theorem irred_iff_irreducible [Subsingleton Mˣ] {p : M} :
    Irred p ↔ Irreducible p := by
  constructor
  · rintro ⟨hne, hsplit⟩
    refine ⟨fun hu => hne (isUnit_iff_eq_one.mp hu), fun a b hab => ?_⟩
    rcases hsplit a b hab with h | h
    · exact Or.inl (h ▸ isUnit_one)
    · exact Or.inr (h ▸ isUnit_one)
  · intro hirr
    refine ⟨fun h => hirr.not_isUnit (h ▸ isUnit_one), fun a b hab => ?_⟩
    rcases hirr.isUnit_or_isUnit hab with h | h
    · exact Or.inl (isUnit_iff_eq_one.mp h)
    · exact Or.inr (isUnit_iff_eq_one.mp h)

/-! ## Existence -/

/-- **Every element decomposes**, when factorization is well founded.  The
descent is on the proper-factor relation, so the hypothesis is exactly that no
element factors forever. -/
theorem exists_decomposition (hwf : WellFounded (ProperFactor (M := M)))
    (_hred : Reduced M) : ∀ a : M, ∃ s : Multiset M, IsDecomposition s a := by
  intro a
  induction a using hwf.induction with
  | _ a ih =>
      by_cases ha : a = 1
      · exact ⟨0, by simp, by simp [ha]⟩
      · by_cases hirr : ∀ b c : M, a = b * c → b = 1 ∨ c = 1
        · exact ⟨{a}, by
            intro p hp
            rw [Multiset.mem_singleton] at hp
            exact hp ▸ ⟨ha, hirr⟩, by simp⟩
        · push Not at hirr
          obtain ⟨b, c, hbc, hb, hc⟩ := hirr
          obtain ⟨sb, hsb⟩ := ih b ⟨c, hbc, hc⟩
          obtain ⟨sc, hsc⟩ := ih c ⟨b, by rw [hbc, mul_comm], hb⟩
          refine ⟨sb + sc, ?_, ?_⟩
          · intro p hp
            rcases Multiset.mem_add.mp hp with h | h
            · exact hsb.1 p h
            · exact hsc.1 p h
          · rw [Multiset.prod_add, hsb.2, hsc.2, hbc]

/-! ## Uniqueness -/

/-- A prime dividing a product of a multiset divides one of its members. -/
theorem prime_dvd_multiset_prod (hred : Reduced M) {p : M} (hp : PrimeElt p) :
    ∀ (s : Multiset M), p ∣ s.prod → ∃ q ∈ s, p ∣ q := by
  intro s
  induction s using Multiset.induction with
  | empty =>
      intro h
      rw [Multiset.prod_zero] at h
      obtain ⟨c, hc⟩ := h
      exact absurd (hred p c hc.symm) hp.1
  | cons q s ih =>
      intro h
      rw [Multiset.prod_cons] at h
      rcases hp.2 q s.prod h with hq | hs
      · exact ⟨q, Multiset.mem_cons_self q s, hq⟩
      · obtain ⟨r, hr, hdvd⟩ := ih hs
        exact ⟨r, Multiset.mem_cons_of_mem hr, hdvd⟩

/-- In a reduced monoid a prime dividing an irreducible is that irreducible. -/
theorem eq_of_prime_dvd_irred {p q : M}
    (hp : PrimeElt p) (hq : Irred q) (h : p ∣ q) : p = q := by
  obtain ⟨c, hc⟩ := h
  rcases hq.2 p c hc with h1 | h1
  · exact absurd h1 hp.1
  · rw [hc, h1, mul_one]

/-- **Decompositions are unique** when the irreducibles are prime.  The
multiset of factors is determined by the element. -/
theorem decomposition_unique [IsCancelMul M] [DecidableEq M] (hred : Reduced M)
    (hprime : ∀ p : M, Irred p → PrimeElt p) :
    ∀ (s t : Multiset M) (a : M), IsDecomposition s a → IsDecomposition t a → s = t := by
  intro s
  induction s using Multiset.induction with
  | empty =>
      intro t a hs ht
      by_contra hne
      obtain ⟨q, hq⟩ := Multiset.exists_mem_of_ne_zero (fun h => hne h.symm)
      have hqd : q ∣ t.prod := Multiset.dvd_prod hq
      rw [ht.2, ← hs.2, Multiset.prod_zero] at hqd
      obtain ⟨c, hc⟩ := hqd
      exact (ht.1 q hq).1 (hred q c hc.symm)
  | cons p s ih =>
      intro t a hs ht
      have hpirr : Irred p := hs.1 p (Multiset.mem_cons_self p s)
      have hpd : p ∣ a := by
        rw [← hs.2, Multiset.prod_cons]
        exact Dvd.intro _ rfl
      obtain ⟨q, hq, hpq⟩ := prime_dvd_multiset_prod hred (hprime p hpirr) t (ht.2 ▸ hpd)
      have hpqe : p = q := eq_of_prime_dvd_irred (hprime p hpirr) (ht.1 q hq) hpq
      subst hpqe
      have hterase : p ::ₘ t.erase p = t := (Multiset.cons_erase hq)
      have hprods : p * s.prod = p * (t.erase p).prod := by
        rw [← Multiset.prod_cons, ← Multiset.prod_cons, hs.2, hterase, ht.2]
      have hcancel : s.prod = (t.erase p).prod := mul_left_cancel hprods
      have hrec : s = t.erase p :=
        ih (t.erase p) s.prod
          ⟨fun r hr => hs.1 r (Multiset.mem_cons_of_mem hr), rfl⟩
          ⟨fun r hr => ht.1 r (Multiset.mem_of_mem_erase hr), hcancel.symm⟩
      rw [hrec, hterase]

/-- **Unique decomposition**, packaged: existence and uniqueness together. -/
theorem existsUnique_decomposition [IsCancelMul M] [DecidableEq M]
    (hwf : WellFounded (ProperFactor (M := M))) (hred : Reduced M)
    (hprime : ∀ p : M, Irred p → PrimeElt p) (a : M) :
    ∃! s : Multiset M, IsDecomposition s a := by
  obtain ⟨s, hs⟩ := exists_decomposition hwf hred a
  exact ⟨s, hs, fun t ht => decomposition_unique hred hprime t s a ht hs⟩

/-! ## Why each hypothesis is needed

Well-foundedness is exactly what an unfolding law destroys: if `p = p * q` with
`q` not the identity then `p` is a proper factor of itself, so the relation has
a loop and nothing decomposes. -/

/-- **A self-absorbing element makes factorization ill-founded.**  This is the
shape a replicated process has when its unfolding law is in the equational
theory. -/
theorem not_wellFounded_of_self_absorbing {p q : M} (hq : q ≠ 1) (h : p = p * q) :
    ¬ WellFounded (ProperFactor (M := M)) := by
  intro hwf
  have hself : ProperFactor p p := ⟨q, h, hq⟩
  have hirrefl : ∀ x : M, Acc (ProperFactor (M := M)) x → ¬ ProperFactor x x := by
    intro x hx
    induction hx with
    | intro y _ ih => intro hyy; exact ih y hyy hyy
  exact hirrefl p (hwf.apply p) hself

/-! ## A monoid that satisfies all three hypotheses

The free commutative monoid on a set of generators is the arithmetic the
theorem was written for: a process built from independent parts, with no
equation relating them.  Every hypothesis is discharged by computation on
multisets rather than assumed, and the third -- every irreducible is prime --
is *free* here, which is exactly the difference from the process case.  There
the same statement is the substantial theorem of the literature.  Writing both
out is what keeps the abstract development honest about which of its
hypotheses is cheap and which is not. -/

/-- The free commutative monoid on `σ`: multisets of generators, written
multiplicatively. -/
abbrev FreeCM (σ : Type u) := Multiplicative (Multiset σ)

variable {σ : Type u}

theorem freeCM_toAdd_mul (a b : FreeCM σ) :
    Multiplicative.toAdd (a * b) = Multiplicative.toAdd a + Multiplicative.toAdd b := rfl

theorem freeCM_eq_one_iff {a : FreeCM σ} : a = 1 ↔ Multiplicative.toAdd a = 0 :=
  ⟨fun h => by rw [h]; rfl, fun h => Multiplicative.toAdd.injective h⟩

/-- Divisibility is multiset containment. -/
theorem freeCM_dvd_iff {p a : FreeCM σ} :
    p ∣ a ↔ Multiplicative.toAdd p ≤ Multiplicative.toAdd a := by
  refine ⟨?_, ?_⟩
  · rintro ⟨c, rfl⟩
    exact Multiset.le_iff_exists_add.mpr ⟨Multiplicative.toAdd c, freeCM_toAdd_mul _ _⟩
  · intro h
    obtain ⟨u, hu⟩ := Multiset.le_iff_exists_add.mp h
    exact ⟨Multiplicative.ofAdd u, Multiplicative.toAdd.injective hu⟩

/-- Nothing but the empty multiset is invertible. -/
theorem freeCM_reduced : Reduced (FreeCM σ) := by
  intro a b h
  rw [freeCM_eq_one_iff] at h ⊢
  rw [freeCM_toAdd_mul] at h
  have hc := congrArg Multiset.card h
  rw [Multiset.card_add] at hc
  simp only [Multiset.card_zero] at hc
  exact Multiset.card_eq_zero.mp (by omega)

/-- Factorization terminates, because a proper factor is strictly smaller. -/
theorem freeCM_wellFounded : WellFounded (ProperFactor (M := FreeCM σ)) := by
  apply Subrelation.wf (r := InvImage Nat.lt (fun a : FreeCM σ => (Multiplicative.toAdd a).card))
  · rintro b a ⟨c, rfl, hc⟩
    show (Multiplicative.toAdd b).card < (Multiplicative.toAdd (b * c)).card
    rw [freeCM_toAdd_mul, Multiset.card_add]
    have hpos : 0 < (Multiplicative.toAdd c).card := by
      rcases Nat.eq_zero_or_pos (Multiplicative.toAdd c).card with h | h
      · exact absurd (freeCM_eq_one_iff.mpr (Multiset.card_eq_zero.mp h)) hc
      · exact h
    omega
  · exact InvImage.wf _ Nat.lt_wfRel.wf

/-- The irreducibles are exactly the generators. -/
theorem freeCM_irred_iff [DecidableEq σ] {p : FreeCM σ} :
    Irred p ↔ (Multiplicative.toAdd p).card = 1 := by
  constructor
  · rintro ⟨hne, hsplit⟩
    have hne0 : Multiplicative.toAdd p ≠ 0 := fun h => hne (freeCM_eq_one_iff.mpr h)
    obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne0
    have hcons : Multiplicative.toAdd p = {x} + (Multiplicative.toAdd p).erase x := by
      simpa using (Multiset.cons_erase hx).symm
    rcases hsplit (Multiplicative.ofAdd ({x} : Multiset σ))
      (Multiplicative.ofAdd ((Multiplicative.toAdd p).erase x))
      (Multiplicative.toAdd.injective (by rw [freeCM_toAdd_mul]; exact hcons)) with h | h
    · exact absurd (freeCM_eq_one_iff.mp h) (by simp)
    · have herase : (Multiplicative.toAdd p).erase x = 0 := freeCM_eq_one_iff.mp h
      rw [hcons, herase]; simp
  · intro hcard
    obtain ⟨x, hx⟩ := Multiset.card_eq_one.mp hcard
    refine ⟨fun h => by rw [freeCM_eq_one_iff, hx] at h; simp at h, ?_⟩
    intro a b hab
    have hsum : ({x} : Multiset σ) = Multiplicative.toAdd a + Multiplicative.toAdd b := by
      rw [← hx, hab, freeCM_toAdd_mul]
    have hc := congrArg Multiset.card hsum
    rw [Multiset.card_add, Multiset.card_singleton] at hc
    rcases Nat.eq_zero_or_pos (Multiplicative.toAdd a).card with h | h
    · exact Or.inl (freeCM_eq_one_iff.mpr (Multiset.card_eq_zero.mp h))
    · exact Or.inr (freeCM_eq_one_iff.mpr (Multiset.card_eq_zero.mp (by omega)))

/-- **Every irreducible is prime, for free.**  A generator sits in a product
exactly when it sits in one of the factors, which is a fact about membership
rather than a theorem about processes. -/
theorem freeCM_prime_of_card_one {p : FreeCM σ}
    (hcard : (Multiplicative.toAdd p).card = 1) : PrimeElt p := by
  obtain ⟨x, hx⟩ := Multiset.card_eq_one.mp hcard
  refine ⟨fun h => by rw [freeCM_eq_one_iff, hx] at h; simp at h, ?_⟩
  intro a b hdvd
  rw [freeCM_dvd_iff, hx, freeCM_toAdd_mul, Multiset.singleton_le, Multiset.mem_add] at hdvd
  rcases hdvd with h | h
  · exact Or.inl (freeCM_dvd_iff.mpr (by rw [hx]; exact Multiset.singleton_le.mpr h))
  · exact Or.inr (freeCM_dvd_iff.mpr (by rw [hx]; exact Multiset.singleton_le.mpr h))

/-- **The free commutative monoid has unique decomposition.**  Every hypothesis
of the abstract theorem is met, so the abstract theorem applies: the development
above is inhabited rather than merely stated. -/
theorem freeCM_existsUnique_decomposition [DecidableEq σ] (a : FreeCM σ) :
    ∃! s : Multiset (FreeCM σ), IsDecomposition s a :=
  existsUnique_decomposition freeCM_wellFounded freeCM_reduced
    (fun _ hp => freeCM_prime_of_card_one (freeCM_irred_iff.mp hp)) a

/-! ## A monoid that does not

The negative control.  `ℕ∞` under addition, written multiplicatively, has an
absorbing element: `⊤` is `⊤` beside one more.  So `⊤` is a proper factor of
itself, factorization never terminates, and the well-foundedness hypothesis
fails -- concretely, not merely conceivably.  This is the shape a replicated
process has once its unfolding law is in the equational theory, which is why
the hypothesis cannot be dropped. -/

/-- One more added to infinity is infinity, so infinity properly factors
itself. -/
theorem enat_top_self_absorbing :
    (Multiplicative.ofAdd (⊤ : ℕ∞))
      = Multiplicative.ofAdd (⊤ : ℕ∞) * Multiplicative.ofAdd (1 : ℕ∞) := by
  apply Multiplicative.toAdd.injective
  show (⊤ : ℕ∞) = (⊤ : ℕ∞) + (1 : ℕ∞)
  simp

/-- **So this monoid is not an instance.**  Both signs are now checked: the
hypotheses are satisfiable, and they are not satisfied by everything. -/
theorem enat_not_wellFounded :
    ¬ WellFounded (ProperFactor (M := Multiplicative ℕ∞)) :=
  not_wellFounded_of_self_absorbing
    (q := Multiplicative.ofAdd (1 : ℕ∞))
    (fun h => by
      have : (1 : ℕ∞) = 0 := congrArg Multiplicative.toAdd h
      simp at this)
    enat_top_self_absorbing


/-! ## The hypothesis that is not free

The negative control above is for well-foundedness -- the hypothesis nobody
doubts.  This one is for the hypothesis the header calls the whole content of
the literature: that every irreducible is prime.  It is assumed rather than
derived, so it owes a witness that it can fail.

The witness is the numerical monoid generated by two and three: the naturals
under addition with one removed, written multiplicatively.  Cancellation,
reducedness and well-founded factorization all hold, so the two hypotheses that
*are* discharged elsewhere are satisfied here.  What fails is the third, and
with it uniqueness: two is irreducible and divides three times three without
dividing three, and six decomposes both as three twos and as two threes. -/

namespace Num23

/-- The numerical monoid generated by two and three: every natural but one. -/
def Carrier : Type := {n : ℕ // n ≠ 1}

instance : CommMonoid Carrier where
  mul a b := ⟨a.1 + b.1, by rcases a with ⟨x, hx⟩; rcases b with ⟨y, hy⟩; simp; omega⟩
  one := ⟨0, by omega⟩
  mul_assoc a b c := Subtype.ext (by show a.1 + b.1 + c.1 = a.1 + (b.1 + c.1); omega)
  one_mul a := Subtype.ext (by show 0 + a.1 = a.1; omega)
  mul_one a := Subtype.ext (by show a.1 + 0 = a.1; omega)
  mul_comm a b := Subtype.ext (by show a.1 + b.1 = b.1 + a.1; omega)

@[simp] theorem val_mul (a b : Carrier) : (a * b).1 = a.1 + b.1 := rfl
@[simp] theorem val_one : (1 : Carrier).1 = 0 := rfl

theorem eq_one_iff {a : Carrier} : a = 1 ↔ a.1 = 0 :=
  ⟨fun h => by rw [h, val_one], fun h => Subtype.ext (by rw [val_one]; exact h)⟩

theorem ne_one_val (a : Carrier) : a.1 ≠ 1 := a.2

instance : DecidableEq Carrier := fun a b =>
  decidable_of_iff (a.1 = b.1) ⟨Subtype.ext, fun h => h ▸ rfl⟩

instance : IsCancelMul Carrier where
  mul_left_cancel a b c h := Subtype.ext (by
    have := congrArg Subtype.val h; simp only [val_mul] at this; omega)
  mul_right_cancel a b c h := Subtype.ext (by
    have := congrArg Subtype.val h; simp only [val_mul] at this; omega)

/-- The two hypotheses that are discharged elsewhere hold here. -/
theorem reduced : Reduced Carrier := by
  intro a b h
  have hv := congrArg Subtype.val h
  rw [val_mul, val_one] at hv
  exact eq_one_iff.mpr (by omega)

theorem wellFounded : WellFounded (ProperFactor (M := Carrier)) := by
  apply Subrelation.wf (r := InvImage Nat.lt (fun a : Carrier => a.1))
  · intro b a hba
    obtain ⟨c, hac, hc⟩ := hba
    show b.1 < a.1
    have hval : a.1 = b.1 + c.1 := by rw [hac, val_mul]
    have hcne : c.1 ≠ 0 := fun h => hc (eq_one_iff.mpr h)
    omega
  · exact InvImage.wf _ Nat.lt_wfRel.wf

def two : Carrier := ⟨2, by omega⟩
def three : Carrier := ⟨3, by omega⟩
def four : Carrier := ⟨4, by omega⟩
def six : Carrier := ⟨6, by omega⟩

@[simp] theorem val_two : two.1 = 2 := rfl
@[simp] theorem val_three : three.1 = 3 := rfl
@[simp] theorem val_four : four.1 = 4 := rfl
@[simp] theorem val_six : six.1 = 6 := rfl

theorem two_irred : Irred two := by
  refine ⟨fun h => by rw [eq_one_iff, val_two] at h; omega, ?_⟩
  intro a b hab
  have hv : a.1 + b.1 = 2 := by
    have := congrArg Subtype.val hab
    rw [val_mul, val_two] at this
    omega
  have ha := ne_one_val a
  have hb := ne_one_val b
  rw [eq_one_iff, eq_one_iff]
  omega

theorem three_irred : Irred three := by
  refine ⟨fun h => by rw [eq_one_iff, val_three] at h; omega, ?_⟩
  intro a b hab
  have hv : a.1 + b.1 = 3 := by
    have := congrArg Subtype.val hab
    rw [val_mul, val_three] at this
    omega
  have ha := ne_one_val a
  have hb := ne_one_val b
  rw [eq_one_iff, eq_one_iff]
  omega

theorem two_dvd_six : two ∣ three * three :=
  ⟨four, Subtype.ext (by show (3:ℕ) + 3 = 2 + 4; omega)⟩

theorem three_not_multiple_of_two : ∀ c : Carrier, three ≠ two * c := by
  intro c hc
  have hv := congrArg Subtype.val hc
  rw [val_mul, val_two, val_three] at hv
  exact ne_one_val c (by omega)

/-- **Two is irreducible and not prime.**  This is the hypothesis the uniqueness
theorem assumes, exhibited failing. -/
theorem two_not_prime : ¬ PrimeElt two := by
  rintro ⟨-, hp⟩
  rcases hp three three two_dvd_six with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact three_not_multiple_of_two c hc
  · exact three_not_multiple_of_two c hc

theorem decomposition_twos : IsDecomposition {two, two, two} six := by
  refine ⟨?_, ?_⟩
  · intro p hp
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
      Multiset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> exact two_irred
  · show Multiset.prod {two, two, two} = six
    exact Subtype.ext (by show (2:ℕ) + (2 + (2 + 0)) = 6; omega)

theorem decomposition_threes : IsDecomposition {three, three} six := by
  refine ⟨?_, ?_⟩
  · intro p hp
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
      Multiset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> exact three_irred
  · show Multiset.prod {three, three} = six
    exact Subtype.ext (by show (3:ℕ) + (3 + 0) = 6; omega)

/-- **And decomposition is not unique.**  So the third hypothesis is doing work:
without it the conclusion is false, in a monoid satisfying the other two. -/
theorem decomposition_not_unique :
    ∃ s t : Multiset Carrier,
      IsDecomposition s six ∧ IsDecomposition t six ∧ s ≠ t :=
  ⟨{two, two, two}, {three, three}, decomposition_twos, decomposition_threes, by
    intro h
    have hcard := congrArg Multiset.card h
    simp at hcard⟩

end Num23

end Mettapedia.Algebra
