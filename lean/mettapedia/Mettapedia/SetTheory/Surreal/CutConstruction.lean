import Mettapedia.SetTheory.Surreal.Cut
import Mathlib.SetTheory.Ordinal.Family

/-!
# Existence of surreal cuts

Separated option families with bounded birthdays admit a simplest separator.
The bound is essential at the chosen ordinal universe: an arbitrary
`Set Surreal` can include every surreal represented at that level.

The existence construction recursively chooses a positive sign precisely when
a compatible left option still requires it. A length strictly above the option
birthdays gives a separator; ordinal well-foundedness then selects a least
birthday. This uses the existing padded sign order, not an assumed cut operator.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.SignExpansion

namespace PreSurreal

/-- A compatible left option forces a positive sign at the next position. -/
noncomputable def upperSigns (L : Set PreSurreal) : Ordinal → Bool :=
  Ordinal.lt_wf.fix fun β earlier => by
    classical
    exact decide (∃ l ∈ L,
      (∀ γ (h : γ < β), (if earlier γ h then Sign.pos else Sign.neg) = l.signAt γ) ∧
      Sign.zero ≤ l.signAt β)

theorem upperSigns_eq_true_iff (L : Set PreSurreal) (β : Ordinal) :
    upperSigns L β = true ↔ ∃ l ∈ L,
      (∀ γ < β, (if upperSigns L γ then Sign.pos else Sign.neg) = l.signAt γ) ∧
      Sign.zero ≤ l.signAt β := by
  classical
  conv_lhs => rw [upperSigns, WellFounded.fix_eq]
  simp only [decide_eq_true_eq]
  rfl

/-- A bounded-length separator candidate. Minimality is established separately. -/
noncomputable def upperCandidate (L : Set PreSurreal) (bound : Ordinal) :
    PreSurreal := ⟨bound, upperSigns L⟩

private theorem sign_lt_nonzero {a b : Sign} (h : a < b) (ha : a ≠ .zero) :
    a = .neg ∧ Sign.zero ≤ b := by
  cases a <;> cases b <;> simp_all [Sign.lt_def, Sign.le_def, Sign.toNat]

private theorem nonzero_sign_gt {a b : Sign} (h : a < b) (hb : b ≠ .zero) :
    b = .pos ∧ a ≤ .zero := by
  cases a <;> cases b <;> simp_all [Sign.lt_def, Sign.le_def, Sign.toNat]

theorem signs_of_lt_of_ne_zero {a b : Sign} (h : a < b)
    (ha : a ≠ .zero) (hb : b ≠ .zero) : a = .neg ∧ b = .pos :=
  ⟨(sign_lt_nonzero h ha).1, (nonzero_sign_gt h hb).1⟩

/-- The candidate is strictly above each left option shorter than its bound. -/
theorem lt_upperCandidate {L : Set PreSurreal} {bound : Ordinal}
    {l : PreSurreal} (hl : l ∈ L) (hlen : l.length < bound) :
    Lt l (upperCandidate L bound) := by
  classical
  rcases lt_or_equiv_or_gt l (upperCandidate L bound) with h | h | h
  · exact h
  · exact (ne_of_lt hlen (length_eq_of_signAt_eq h)).elim
  · obtain ⟨β, hagree, hlt⟩ := h
    have hβ : β < bound :=
      lt_of_le_of_lt (le_length_of_first_diff hagree (ne_of_lt hlt)).2 hlen
    have hx := sign_lt_nonzero hlt
      (signAt_ne_zero_of_lt (x := upperCandidate L bound) hβ)
    have hpos : upperSigns L β = true :=
      (upperSigns_eq_true_iff L β).mpr ⟨l, hl, fun γ hγ => by
        have h := hagree γ hγ
        rw [signAt_of_lt (x := upperCandidate L bound) (hγ.trans hβ)] at h
        exact h, hx.2⟩
    have hneg := hx.1
    rw [signAt_of_lt (x := upperCandidate L bound) hβ] at hneg
    simp [upperCandidate, hpos] at hneg

/-- When padded signs agree through their common end they agree everywhere. -/
private theorem equiv_of_agree_of_zero {x y : PreSurreal} {β : Ordinal}
    (h : ∀ γ < β, x.signAt γ = y.signAt γ)
    (hx : x.signAt β = .zero) (hy : y.signAt β = .zero) : Equiv x y := by
  funext γ
  rcases lt_or_ge γ β with hγ | hγ
  · exact h γ hγ
  · rw [signAt_of_ge ((signAt_eq_zero_iff.mp hx).trans hγ),
      signAt_of_ge ((signAt_eq_zero_iff.mp hy).trans hγ)]

/-- Separation of the options prevents the candidate from overshooting a
right option shorter than its bound. -/
theorem upperCandidate_lt {L : Set PreSurreal} {bound : Ordinal}
    {r : PreSurreal} (hr : ∀ l ∈ L, Lt l r) (hlen : r.length < bound) :
    Lt (upperCandidate L bound) r := by
  classical
  rcases lt_or_equiv_or_gt (upperCandidate L bound) r with h | h | h
  · exact h
  · exact (ne_of_lt hlen (length_eq_of_signAt_eq h).symm).elim
  · obtain ⟨β, hagree, hlt⟩ := h
    have hβ : β < bound :=
      lt_of_le_of_lt (le_length_of_first_diff hagree (ne_of_lt hlt)).1 hlen
    have hx := nonzero_sign_gt hlt
      (signAt_ne_zero_of_lt (x := upperCandidate L bound) hβ)
    have hpos : upperSigns L β = true := by
      have h := hx.1
      rw [signAt_of_lt (x := upperCandidate L bound) hβ] at h
      change (if upperSigns L β then Sign.pos else Sign.neg) = Sign.pos at h
      cases hs : upperSigns L β <;> simp_all
    obtain ⟨l, hl, hcompatible, hsign⟩ := (upperSigns_eq_true_iff L β).mp hpos
    have heq : ∀ γ < β, r.signAt γ = l.signAt γ := by
      intro γ hγ
      have h := hagree γ hγ
      rw [signAt_of_lt (x := upperCandidate L bound) (hγ.trans hβ)] at h
      exact h.trans (hcompatible γ hγ)
    have hle : r.signAt β ≤ l.signAt β := hx.2.trans hsign
    rcases lt_or_eq_of_le hle with hstrict | hequal
    · exact (not_lt_self l (lt_trans (hr l hl) ⟨β, heq, hstrict⟩)).elim
    · have hrzero : r.signAt β = .zero := le_antisymm hx.2 (hequal ▸ hsign)
      have hlzero : l.signAt β = .zero := hequal.symm.trans hrzero
      exact (not_lt_self l (lt_of_lt_of_equiv (hr l hl)
        (equiv_of_agree_of_zero heq hrzero hlzero))).elim

end PreSurreal

namespace Surreal

/-- Strict separation of the two option families. -/
def Separated (L R : Set Surreal) : Prop := ∀ l ∈ L, ∀ r ∈ R, l < r

/-- A strict separator, with no minimality requirement. -/
def Between (L R : Set Surreal) (x : Surreal) : Prop :=
  (∀ l ∈ L, l < x) ∧ (∀ r ∈ R, x < r)

/-- The cut specification: separation and least birthday among separators. -/
structure IsCut (L R : Set Surreal) (x : Surreal) : Prop where
  left : ∀ l ∈ L, l < x
  right : ∀ r ∈ R, x < r
  simplest : ∀ y, Between L R y → birthday x ≤ birthday y

theorem IsCut.between {L R : Set Surreal} {x : Surreal} (h : IsCut L R x) :
    Between L R x := ⟨h.left, h.right⟩

/-- The transfinite candidate really separates the original quotient families. -/
theorem upperCandidate_between {L R : Set Surreal} (hsep : Separated L R)
    {bound : Ordinal} (hbound : ∀ x ∈ L ∪ R, birthday x < bound) :
    Between L R (mk (PreSurreal.upperCandidate (mk ⁻¹' L) bound)) := by
  constructor
  · intro l hl
    induction l using Quotient.inductionOn with
    | h p => exact PreSurreal.lt_upperCandidate hl (hbound (mk p) (Or.inl hl))
  · intro r hr
    induction r using Quotient.inductionOn with
    | h p =>
      exact PreSurreal.upperCandidate_lt
        (fun l hl => hsep (mk l) hl (mk p) hr) (hbound (mk p) (Or.inr hr))

/-- Any separated families of bounded birthdays have a separator. -/
theorem exists_between {L R : Set Surreal} (hsep : Separated L R)
    (hbound : BddAbove (birthday '' (L ∪ R))) : ∃ x, Between L R x := by
  obtain ⟨bound, hbound⟩ := hbound
  exact ⟨mk (PreSurreal.upperCandidate (mk ⁻¹' L) (bound + 1)),
    upperCandidate_between hsep (fun x hx =>
      lt_of_le_of_lt (hbound ⟨x, hx, rfl⟩) (lt_add_one bound))⟩

/-- Existence of the simplest separator, using ordinal well-foundedness after
constructing a genuine separator. -/
theorem exists_isCut {L R : Set Surreal} (hsep : Separated L R)
    (hbound : BddAbove (birthday '' (L ∪ R))) : ∃ x, IsCut L R x := by
  obtain ⟨w, hw⟩ := exists_between hsep hbound
  obtain ⟨β, ⟨x, hx, hβ⟩, hmin⟩ := Ordinal.lt_wf.has_min
    {α | ∃ y, Between L R y ∧ birthday y = α} ⟨birthday w, w, hw, rfl⟩
  refine ⟨x, hx.1, hx.2, fun y hy => ?_⟩
  rw [hβ]
  exact not_lt.mp (hmin (birthday y) ⟨y, hy, rfl⟩)

/-- A strict interval between equal-birthday numbers contains an earlier one. -/
theorem exists_earlier_between {x y : Surreal} (hxy : x < y)
    (hb : birthday x = birthday y) :
    ∃ z, birthday z < birthday y ∧ x < z ∧ z < y := by
  induction x using Quotient.inductionOn with
  | h p =>
    induction y using Quotient.inductionOn with
    | h q =>
      obtain ⟨z, hz, hxz, hzy⟩ := PreSurreal.exists_simpler_between hxy hb
      exact ⟨mk z, hz, hxz, hzy⟩

/-- Minimality determines a unique number, for arbitrary option families. -/
theorem IsCut.unique {L R : Set Surreal} {x y : Surreal}
    (hx : IsCut L R x) (hy : IsCut L R y) : x = y := by
  have hb : birthday x = birthday y :=
    le_antisymm (hx.simplest y hy.between) (hy.simplest x hx.between)
  have key : ∀ a b, IsCut L R a → IsCut L R b →
      birthday a = birthday b → ¬ a < b := by
    intro a b ha hb hab hlt
    obtain ⟨z, hz, haz, hzb⟩ := exists_earlier_between hlt hab
    exact (not_le_of_gt hz) (hb.simplest z
      ⟨fun l hl => (ha.left l hl).trans haz, fun r hr => hzb.trans (hb.right r hr)⟩)
  exact le_antisymm (not_lt.mp (key y x hy hx hb.symm))
    (not_lt.mp (key x y hx hy hb))

theorem existsUnique_isCut {L R : Set Surreal} (hsep : Separated L R)
    (hbound : BddAbove (birthday '' (L ∪ R))) : ∃! x, IsCut L R x := by
  obtain ⟨x, hx⟩ := exists_isCut hsep hbound
  exact ⟨x, hx, fun y hy => hy.unique hx⟩

/-- In particular, small separated families always admit a unique cut.
Smallness is relative to the universe of the ordinal indices. -/
theorem existsUnique_isCut_of_small {L R : Set Surreal} [Small.{0} L] [Small.{0} R]
    (hsep : Separated L R) : ∃! x, IsCut L R x :=
  existsUnique_isCut hsep Ordinal.bddAbove_of_small

/-- The simplest separator is an initial segment of every separator, not
merely a number with a smaller ordinal birthday. This is the sign-expansion
content of the source's `SNoCutP_SNoCut_fst`. -/
theorem IsCut.agree_below {L R : Set Surreal} {p q : PreSurreal}
    (hp : IsCut L R (Surreal.mk p)) (hq : Between L R (Surreal.mk q)) :
    ∀ β < p.length, p.signAt β = q.signAt β := by
  classical
  have hlen : p.length ≤ q.length := hp.simplest _ hq
  intro β hβ
  by_contra hne
  have hfun : p.signAt ≠ q.signAt := fun h => hne (congrFun h β)
  obtain ⟨δ, hδne, hδmin⟩ := PreSurreal.exists_least_diff hfun
  have hδβ : δ ≤ β := not_lt.mp (fun h => hne (hδmin β h))
  have hδp : δ < p.length := hδβ.trans_lt hβ
  have hδq : δ < q.length := hδp.trans_le hlen
  rcases lt_or_gt_of_ne hδne with hlt | hgt
  · obtain ⟨hpneg, hqpos⟩ := PreSurreal.signs_of_lt_of_ne_zero hlt
      (PreSurreal.signAt_ne_zero_of_lt hδp) (PreSurreal.signAt_ne_zero_of_lt hδq)
    obtain ⟨hpz, hzq⟩ := PreSurreal.prefixOf_between hδmin hpneg hqpos
    have hz : Between L R (Surreal.mk (PreSurreal.prefixOf p δ)) :=
      ⟨fun l hl => (hp.left l hl).trans hpz,
        fun r hr => lt_trans (show Surreal.mk (PreSurreal.prefixOf p δ) < Surreal.mk q from hzq) (hq.2 r hr)⟩
    exact (not_le_of_gt hδp) (hp.simplest _ hz)
  · obtain ⟨hqneg, hppos⟩ := PreSurreal.signs_of_lt_of_ne_zero hgt
      (PreSurreal.signAt_ne_zero_of_lt hδq) (PreSurreal.signAt_ne_zero_of_lt hδp)
    obtain ⟨hqz, hzp⟩ := PreSurreal.prefixOf_between (fun γ hγ => (hδmin γ hγ).symm)
      hqneg hppos
    have hz : Between L R (Surreal.mk (PreSurreal.prefixOf q δ)) :=
      ⟨fun l hl => (hq.1 l hl).trans hqz,
        fun r hr => lt_trans (show Surreal.mk (PreSurreal.prefixOf q δ) < Surreal.mk p from hzp) (hp.right r hr)⟩
    exact (not_le_of_gt hδp) (hp.simplest _ hz)

/-- The simplest surreal between valid bounded option families. -/
noncomputable def cut (L R : Set Surreal) (hsep : Separated L R)
    (hbound : BddAbove (birthday '' (L ∪ R))) : Surreal :=
  (exists_isCut hsep hbound).choose

theorem isCut_cut (L R : Set Surreal) (hsep : Separated L R)
    (hbound : BddAbove (birthday '' (L ∪ R))) : IsCut L R (cut L R hsep hbound) :=
  (exists_isCut hsep hbound).choose_spec

/-- A strict birthday bound on all options bounds the birthday of the cut. -/
theorem IsCut.birthday_le_bound {L R : Set Surreal} {x : Surreal}
    (hx : IsCut L R x) {bound : Ordinal}
    (hbound : ∀ y ∈ L ∪ R, birthday y < bound) : birthday x ≤ bound :=
  hx.simplest _ (upperCandidate_between
    (fun l hl r hr => (hx.left l hl).trans (hx.right r hr)) hbound)

/-- The canonical left options are bounded above by the supplied left family. -/
theorem IsCut.left_cofinal {L R : Set Surreal} {x : Surreal} (hx : IsCut L R x)
    {w : Surreal} (hw : w ∈ leftOptions x) : ∃ l ∈ L, w ≤ l := by
  classical
  by_contra h
  have hL : ∀ l ∈ L, l < w := by
    intro l hl
    exact not_le.mp (fun hwl => h ⟨l, hl, hwl⟩)
  exact (not_le_of_gt hw.2) (hx.simplest w
    ⟨hL, fun r hr => hw.1.trans (hx.right r hr)⟩)

/-- The dual coinitiality law for right options. -/
theorem IsCut.right_coinitial {L R : Set Surreal} {x : Surreal} (hx : IsCut L R x)
    {w : Surreal} (hw : w ∈ rightOptions x) : ∃ r ∈ R, r ≤ w := by
  classical
  by_contra h
  have hR : ∀ r ∈ R, w < r := by
    intro r hr
    exact not_le.mp (fun hrw => h ⟨r, hr, hrw⟩)
  exact (not_le_of_gt hw.2) (hx.simplest w
    ⟨fun l hl => (hx.left l hl).trans hw.1, hR⟩)

/-- Conway's cut comparison criterion, derived from least birthdays. -/
theorem IsCut.le_iff {L₁ R₁ L₂ R₂ : Set Surreal} {x y : Surreal}
    (hx : IsCut L₁ R₁ x) (hy : IsCut L₂ R₂ y) :
    x ≤ y ↔ (∀ l ∈ L₁, l < y) ∧ (∀ r ∈ R₂, x < r) := by
  constructor
  · intro hxy
    exact ⟨fun l hl => (hx.left l hl).trans_le hxy,
      fun r hr => hxy.trans_lt (hy.right r hr)⟩
  · rintro ⟨hL, hR⟩
    by_contra h
    have hyx : y < x := not_le.mp h
    rcases lt_trichotomy (birthday y) (birthday x) with hb | hb | hb
    · exact (not_le_of_gt hb) (hx.simplest y
        ⟨hL, fun r hr => hyx.trans (hx.right r hr)⟩)
    · obtain ⟨z, hz, hyz, hzx⟩ := exists_earlier_between hyx hb
      exact (not_le_of_gt hz) (hx.simplest z
        ⟨fun l hl => (hL l hl).trans hyz, fun r hr => hzx.trans (hx.right r hr)⟩)
    · exact (not_le_of_gt hb) (hy.simplest x
        ⟨fun l hl => (hy.left l hl).trans hyx, hR⟩)

/-- **Two cuts that separate each other's families are the same number.**

Cuts of *different* families still coincide whenever each number separates the
other's families — which is the practical form of Conway's cofinality
principle, and the way an identity between two differently-presented sums gets
proved without comparing the presentations term by term. -/
theorem IsCut.eq_of_between {L₁ R₁ L₂ R₂ : Set Surreal} {x y : Surreal}
    (hx : IsCut L₁ R₁ x) (hy : IsCut L₂ R₂ y)
    (hxy : Between L₁ R₁ y) (hyx : Between L₂ R₂ x) : x = y :=
  le_antisymm ((hx.le_iff hy).mpr ⟨hxy.1, hyx.2⟩) ((hy.le_iff hx).mpr ⟨hyx.1, hxy.2⟩)

/-- The constructed operation recovers the existing canonical option view. -/
theorem isCut_self (x : Surreal) : IsCut (leftOptions x) (rightOptions x) x :=
  ⟨fun _ h => h.1, fun _ h => h.1,
    fun _ h => birthday_le_of_between h.1 h.2⟩

theorem canonical_separated (x : Surreal) : Separated (leftOptions x) (rightOptions x) :=
  fun _ hl _ hr => hl.1.trans hr.1

theorem canonical_bounded (x : Surreal) :
    BddAbove (birthday '' (leftOptions x ∪ rightOptions x)) := by
  refine ⟨birthday x, ?_⟩
  rintro _ ⟨y, hy | hy, rfl⟩ <;> exact hy.2.le

theorem cut_self (x : Surreal) :
    cut (leftOptions x) (rightOptions x) (canonical_separated x) (canonical_bounded x) = x :=
  (isCut_cut _ _ _ _).unique (isCut_self x)

/-- **`ofNat n` is the largest number born by day `n`.**

A sign expansion of length at most `n` cannot exceed `n` pluses: wherever the
two first differ, either `natPre n` still has a plus and nothing beats it, or
the expansion has already ended and its sign is `zero`. This is the fact that
makes `ofNat (n+1)` the simplest number above `ofNat n`, and it is used well
before the controls, so it is stated here rather than inside them. -/
theorem le_ofNat_of_birthday_le {x : Surreal} {n : ℕ}
    (hb : birthday x ≤ (n : Ordinal)) : x ≤ ofNat n := by
  induction x using Quotient.inductionOn with
  | h p =>
    apply le_of_not_gt
    rintro ⟨β, -, hlt⟩
    rcases lt_or_ge β (n : Ordinal) with hβ | hβ
    · rw [natPre_signAt_of_lt hβ] at hlt
      have hnot : ¬ Sign.pos < p.signAt β := by cases p.signAt β <;> decide
      exact hnot hlt
    · rw [natPre_signAt_of_ge hβ, PreSurreal.signAt_of_ge (hb.trans hβ)] at hlt
      exact (lt_irrefl _) hlt

namespace CutConstructionControls

/-- The nested-endpoint case is no longer restricted to opposite first signs:
the simplest number strictly between zero and one is the expansion `+ -`. -/
theorem half_isCut : IsCut {0} {ofNat 1} (mk (dyadicPre 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro l hl
    simpa only [Set.mem_singleton_iff.mp hl] using dyadic_pos 1
  · intro r hr
    rw [Set.mem_singleton_iff.mp hr, ← dyadic_zero_eq_one]
    exact dyadic_anti 0
  · intro y hy
    rw [birthday_mk, dyadicPre_length, Nat.cast_one]
    by_contra h
    have hb : birthday y ≤ (1 : Ordinal) := by simpa using (not_le.mp h)
    have hypos := hy.1 0 (Set.mem_singleton _)
    rcases lt_or_eq_of_le hb with hb | hb
    · have hb0 : birthday y = 0 := by simpa using hb
      have hy0 : y ≤ (0 : Surreal) := by
        simpa only [ofNat_zero] using le_ofNat_of_birthday_le (n := 0) (by simp [hb0])
      exact (not_lt_of_ge hy0) hypos
    · have hb' : birthday y = birthday (ofNat 1) := by simpa [ofNat, natPre] using hb
      obtain ⟨z, hz, hyz, -⟩ := exists_earlier_between (hy.2 _ (Set.mem_singleton _)) hb'
      have hz0 : birthday z = 0 := by simpa [ofNat, natPre] using hz
      have hzle : z ≤ (0 : Surreal) := by
        simpa only [ofNat_zero] using le_ofNat_of_birthday_le (n := 0) (by simp [hz0])
      exact (not_lt_of_ge (hyz.le.trans hzle)) hypos

theorem cut_zero_one_eq_half (hsep : Separated {0} {ofNat 1})
    (hbound : BddAbove (birthday '' ({0} ∪ {ofNat 1}))) :
    cut {0} {ofNat 1} hsep hbound = mk (dyadicPre 1) :=
  (isCut_cut _ _ _ _).unique half_isCut

/-- A genuinely infinite option family: the simplest number above every
natural number is the existing all-positive expansion of length omega. -/
theorem omega_isCut_naturals : IsCut (Set.range ofNat) ∅ omega := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact ofNat_lt_omega n
  · intro r hr
    exact (Set.notMem_empty r hr).elim
  · intro y hy
    change Ordinal.omega0 ≤ birthday y
    by_contra h
    obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp (not_le.mp h)
    exact (not_lt_of_ge (le_ofNat_of_birthday_le hn.le))
      (hy.1 (ofNat n) ⟨n, rfl⟩)

theorem cut_naturals_eq_omega
    (hsep : Separated (Set.range ofNat) ∅)
    (hbound : BddAbove (birthday '' (Set.range ofNat ∪ ∅))) :
    cut (Set.range ofNat) ∅ hsep hbound = omega :=
  (isCut_cut _ _ _ _).unique omega_isCut_naturals

theorem zero_isCut_empty : IsCut ∅ ∅ (0 : Surreal) := by
  simpa only [CutControls.zero_leftOptions_empty, CutControls.zero_rightOptions_empty]
    using isCut_self (0 : Surreal)

theorem cut_empty_empty (hsep : Separated ∅ ∅)
    (hbound : BddAbove (birthday '' (∅ ∪ ∅))) : cut ∅ ∅ hsep hbound = 0 :=
  (isCut_cut _ _ _ _).unique zero_isCut_empty

/-- The ordering premise cannot be omitted, even for singleton families. -/
theorem overlapping_options_rejected : ¬ ∃ x, Between {0} {0} x := by
  rintro ⟨x, hL, hR⟩
  exact (lt_irrefl x) ((hR 0 (Set.mem_singleton _)).trans (hL 0 (Set.mem_singleton _)))

/-- Separation alone is insufficient for arbitrary large families. -/
theorem unbounded_options_separated : Separated Set.univ ∅ := by
  intro l hl r hr
  exact (Set.notMem_empty r hr).elim

theorem unbounded_options_have_no_cut : ¬ ∃ x, Between Set.univ ∅ x := by
  rintro ⟨x, hL, -⟩
  exact (lt_irrefl x) (hL x (Set.mem_univ x))

theorem all_birthdays_not_bounded : ¬ BddAbove (birthday '' (Set.univ ∪ ∅)) :=
  fun h => unbounded_options_have_no_cut (exists_between unbounded_options_separated h)

end CutConstructionControls

end Surreal

end Mettapedia.SetTheory.SignExpansion

#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.existsUnique_isCut
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.IsCut.agree_below
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.IsCut.le_iff
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.cut_self
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.CutConstructionControls.cut_zero_one_eq_half
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.CutConstructionControls.cut_naturals_eq_omega
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.CutConstructionControls.all_birthdays_not_bounded
