import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Surreal numbers as sign expansions

A surreal number is a transfinite sequence of signs.  This is Gonshor's
presentation, and it is the one the Megalodon surreal development uses: there a
surreal of level `α` is a set `x` such that for every `β < α` exactly one of
`β ∈ x` and `β' ∈ x` holds, so `β ∈ x` records a `+` at position `β` and
`β' ∈ x` records a `−`.  Comparison is lexicographic on the pair (level, signs).

This module carries that over with `Ordinal` in place of the internal ordinals
and no set theory, and makes two changes that are improvements rather than
departures.

* The level is the *least* ordinal that works.  The source defines it with a
  choice operator and then proves it unique, so nothing is lost and the
  definition becomes choice-free.
* Comparison is stated once, as lexicographic order on a total sign function
  that pads every position at or above the level with a middle sign.  The
  source states it as a three-way disjunction — a first difference below the
  common level, or one level running out while the other continues.  Padding
  makes those one case, because a level running out *is* the middle sign
  appearing, and `neg < zero < pos` puts a finished expansion between its two
  continuations.

What is here is the ordered structure: trichotomy, transitivity, a linear order
on the quotient, and `ω` above every natural number.  Addition and
multiplication are Conway's recursions and are not here; that port is a
separate and much larger obligation.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.SignExpansion

/-! ## Signs -/

/-- A sign at a position: `neg` and `pos` occur below the level, `zero` pads
every position at or above it. -/
inductive Sign where
  | neg
  | zero
  | pos
  deriving DecidableEq, Repr

namespace Sign

/-- The order `neg < zero < pos`, as a number. -/
def toNat : Sign → Nat
  | .neg => 0
  | .zero => 1
  | .pos => 2

theorem toNat_injective : Function.Injective toNat := by
  intro a b h
  cases a <;> cases b <;> simp_all [toNat]

instance : LE Sign := ⟨fun a b => a.toNat ≤ b.toNat⟩
instance : LT Sign := ⟨fun a b => a.toNat < b.toNat⟩

theorem le_def {a b : Sign} : a ≤ b ↔ a.toNat ≤ b.toNat := Iff.rfl
theorem lt_def {a b : Sign} : a < b ↔ a.toNat < b.toNat := Iff.rfl

instance : LinearOrder Sign where
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl a := Nat.le_refl _
  le_trans _ _ _ h₁ h₂ := Nat.le_trans h₁ h₂
  lt_iff_le_not_ge _ _ := Nat.lt_iff_le_and_not_ge
  le_antisymm _ _ h₁ h₂ := toNat_injective (Nat.le_antisymm h₁ h₂)
  le_total _ _ := Nat.le_total _ _
  toDecidableLE a b := Nat.decLe a.toNat b.toNat

theorem neg_lt_zero : Sign.neg < Sign.zero := by decide
theorem zero_lt_pos : Sign.zero < Sign.pos := by decide
theorem neg_lt_pos : Sign.neg < Sign.pos := by decide

end Sign

/-! ## Pre-surreals -/

/-- A sign expansion of a stated length.  Positions at or above `length` are
not significant; `signAt` pads them. -/
structure PreSurreal where
  /-- The level: the length of the sign sequence. -/
  length : Ordinal
  /-- The sign at each position below the level; `true` means `+`. -/
  sign : Ordinal → Bool

namespace PreSurreal

/-- The total sign function: the recorded sign below the level, the middle sign
at or above it. -/
noncomputable def signAt (x : PreSurreal) (β : Ordinal) : Sign :=
  if β < x.length then (if x.sign β then Sign.pos else Sign.neg) else Sign.zero

theorem signAt_of_lt {x : PreSurreal} {β : Ordinal} (h : β < x.length) :
    x.signAt β = if x.sign β then Sign.pos else Sign.neg := by
  simp [signAt, h]

theorem signAt_of_ge {x : PreSurreal} {β : Ordinal} (h : x.length ≤ β) :
    x.signAt β = Sign.zero := by
  simp [signAt, not_lt_of_ge h]

theorem signAt_ne_zero_of_lt {x : PreSurreal} {β : Ordinal} (h : β < x.length) :
    x.signAt β ≠ Sign.zero := by
  rw [signAt_of_lt h]
  cases hs : x.sign β <;> simp

theorem signAt_eq_zero_iff {x : PreSurreal} {β : Ordinal} :
    x.signAt β = Sign.zero ↔ x.length ≤ β := by
  constructor
  · intro h
    by_contra hlt
    exact signAt_ne_zero_of_lt (not_le.mp hlt) h
  · exact signAt_of_ge

/-- **The padded sign function determines the level**, so comparing expansions
through it loses nothing. -/
theorem length_eq_of_signAt_eq {x y : PreSurreal} (h : x.signAt = y.signAt) :
    x.length = y.length := by
  have key : ∀ β : Ordinal, x.length ≤ β ↔ y.length ≤ β := by
    intro β
    rw [← signAt_eq_zero_iff, ← signAt_eq_zero_iff, h]
  exact le_antisymm ((key y.length).mpr (le_refl _)) ((key x.length).mp (le_refl _))

/-! ## Equality and order -/

/-- Two expansions denote the same surreal when their padded sign functions
agree.  By `length_eq_of_signAt_eq` this forces equal levels, so it is the
source's notion: same level, and agreeing signs below it. -/
def Equiv (x y : PreSurreal) : Prop := x.signAt = y.signAt

theorem equiv_refl (x : PreSurreal) : Equiv x x := rfl
theorem equiv_symm {x y : PreSurreal} (h : Equiv x y) : Equiv y x := h.symm
theorem equiv_trans {x y z : PreSurreal} (h₁ : Equiv x y) (h₂ : Equiv y z) :
    Equiv x z := h₁.trans h₂

instance setoid : Setoid PreSurreal where
  r := Equiv
  iseqv := ⟨equiv_refl, equiv_symm, equiv_trans⟩

/-- Lexicographic comparison: the first position at which the padded signs
differ decides. -/
noncomputable def Lt (x y : PreSurreal) : Prop :=
  ∃ β : Ordinal, (∀ γ : Ordinal, γ < β → x.signAt γ = y.signAt γ) ∧
    x.signAt β < y.signAt β

/-- Differing expansions have a least position of difference, by
well-foundedness of the ordinals. -/
theorem exists_least_diff {x y : PreSurreal} (h : x.signAt ≠ y.signAt) :
    ∃ β : Ordinal, x.signAt β ≠ y.signAt β ∧
      ∀ γ : Ordinal, γ < β → x.signAt γ = y.signAt γ := by
  classical
  have hne : Set.Nonempty {b : Ordinal | x.signAt b ≠ y.signAt b} :=
    Function.ne_iff.mp h
  obtain ⟨β, hβ, hmin⟩ := Ordinal.lt_wf.has_min _ hne
  exact ⟨β, hβ, fun γ hγ => not_not.mp fun hne' => hmin γ hne' hγ⟩

theorem lt_or_equiv_or_gt (x y : PreSurreal) : Lt x y ∨ Equiv x y ∨ Lt y x := by
  by_cases h : x.signAt = y.signAt
  · exact Or.inr (Or.inl h)
  obtain ⟨β, hβ, hmin⟩ := exists_least_diff h
  rcases lt_or_gt_of_ne hβ with hlt | hgt
  · exact Or.inl ⟨β, hmin, hlt⟩
  · exact Or.inr (Or.inr ⟨β, fun γ hγ => (hmin γ hγ).symm, hgt⟩)

theorem not_lt_self (x : PreSurreal) : ¬ Lt x x := by
  rintro ⟨β, -, hβ⟩
  exact absurd hβ (lt_irrefl _)

theorem lt_trans {x y z : PreSurreal} (h₁ : Lt x y) (h₂ : Lt y z) : Lt x z := by
  obtain ⟨β₁, hagree₁, hlt₁⟩ := h₁
  obtain ⟨β₂, hagree₂, hlt₂⟩ := h₂
  rcases lt_trichotomy β₁ β₂ with h | rfl | h
  · refine ⟨β₁, fun γ hγ => (hagree₁ γ hγ).trans (hagree₂ γ (hγ.trans h)), ?_⟩
    rw [← hagree₂ β₁ h]; exact hlt₁
  · exact ⟨β₁, fun γ hγ => (hagree₁ γ hγ).trans (hagree₂ γ hγ), hlt₁.trans hlt₂⟩
  · refine ⟨β₂, fun γ hγ => (hagree₁ γ (hγ.trans h)).trans (hagree₂ γ hγ), ?_⟩
    rw [hagree₁ β₂ h]; exact hlt₂

theorem lt_of_lt_of_equiv {x y z : PreSurreal} (h₁ : Lt x y) (h₂ : Equiv y z) : Lt x z := by
  obtain ⟨β, hagree, hlt⟩ := h₁
  exact ⟨β, fun γ hγ => (hagree γ hγ).trans (congrFun h₂ γ), (congrFun h₂ β) ▸ hlt⟩

theorem lt_of_equiv_of_lt {x y z : PreSurreal} (h₁ : Equiv x y) (h₂ : Lt y z) : Lt x z := by
  obtain ⟨β, hagree, hlt⟩ := h₂
  exact ⟨β, fun γ hγ => (congrFun h₁ γ).trans (hagree γ hγ), (congrFun h₁ β) ▸ hlt⟩

end PreSurreal

/-! ## The surreal numbers -/

/-- A surreal number: a sign expansion, up to agreement of padded signs. -/
def Surreal : Type _ := Quotient PreSurreal.setoid

namespace Surreal

/-- The surreal denoted by an expansion. -/
def mk (x : PreSurreal) : Surreal := Quotient.mk _ x

theorem mk_eq_mk {x y : PreSurreal} : mk x = mk y ↔ PreSurreal.Equiv x y :=
  Quotient.eq

noncomputable instance : LT Surreal where
  lt := Quotient.lift₂ PreSurreal.Lt (fun _ _ _ _ h₁ h₂ => by
    apply propext
    constructor
    · exact fun h => PreSurreal.lt_of_equiv_of_lt (PreSurreal.equiv_symm h₁)
        (PreSurreal.lt_of_lt_of_equiv h h₂)
    · exact fun h => PreSurreal.lt_of_equiv_of_lt h₁
        (PreSurreal.lt_of_lt_of_equiv h (PreSurreal.equiv_symm h₂)))

theorem mk_lt_mk {x y : PreSurreal} : mk x < mk y ↔ PreSurreal.Lt x y := Iff.rfl

theorem lt_irrefl' (a : Surreal) : ¬ a < a :=
  Quotient.inductionOn a PreSurreal.not_lt_self

theorem lt_trans' {a b c : Surreal} : a < b → b < c → a < c :=
  Quotient.inductionOn₃ a b c (fun _ _ _ h₁ h₂ => PreSurreal.lt_trans h₁ h₂)

theorem lt_trichotomy' (a b : Surreal) : a < b ∨ a = b ∨ b < a :=
  Quotient.inductionOn₂ a b (fun x y => by
    rcases PreSurreal.lt_or_equiv_or_gt x y with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Quotient.sound h))
    · exact Or.inr (Or.inr h))

noncomputable instance : LinearOrder Surreal where
  lt := (· < ·)
  le a b := a < b ∨ a = b
  le_refl _ := Or.inr rfl
  le_trans a b c hab hbc := by
    rcases hab with h | h
    · rcases hbc with h' | h'
      · exact Or.inl (lt_trans' h h')
      · exact Or.inl (h' ▸ h)
    · exact h ▸ hbc
  lt_iff_le_not_ge a b := by
    constructor
    · intro h
      refine ⟨Or.inl h, ?_⟩
      rintro (h' | h')
      · exact lt_irrefl' a (lt_trans' h h')
      · exact lt_irrefl' a (h' ▸ h)
    · rintro ⟨h | h, hnot⟩
      · exact h
      · exact absurd (Or.inr h.symm) hnot
  le_antisymm a b hab hba := by
    rcases hab with h | h
    · rcases hba with h' | h'
      · exact absurd (lt_trans' h h') (lt_irrefl' a)
      · exact h'.symm
    · exact h
  le_total a b := by
    rcases lt_trichotomy' a b with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl h)
  toDecidableLE := Classical.decRel _

/-! ## Some numbers -/

/-- Zero: the empty expansion. -/
def zeroPre : PreSurreal := ⟨0, fun _ => false⟩

/-- A natural number `n`: a `+` at every position below `n`. -/
def natPre (n : ℕ) : PreSurreal := ⟨(n : Ordinal), fun _ => true⟩

/-- `ω`: a `+` at every position below `ω`. -/
def omegaPre : PreSurreal := ⟨Ordinal.omega0, fun _ => true⟩

noncomputable instance : Zero Surreal := ⟨mk zeroPre⟩

/-- The surreal `ω`. -/
noncomputable def omega : Surreal := mk omegaPre

/-- The surreal named by a natural number. -/
noncomputable def ofNat (n : ℕ) : Surreal := mk (natPre n)

theorem natPre_signAt_of_lt {n : ℕ} {β : Ordinal} (h : β < (n : Ordinal)) :
    (natPre n).signAt β = Sign.pos := by
  have hlt : β < (natPre n).length := h
  rw [PreSurreal.signAt_of_lt hlt]
  simp [natPre]

theorem natPre_signAt_of_ge {n : ℕ} {β : Ordinal} (h : (n : Ordinal) ≤ β) :
    (natPre n).signAt β = Sign.zero :=
  PreSurreal.signAt_of_ge h

theorem omegaPre_signAt_of_lt {β : Ordinal} (h : β < Ordinal.omega0) :
    omegaPre.signAt β = Sign.pos := by
  have hlt : β < omegaPre.length := h
  rw [PreSurreal.signAt_of_lt hlt]
  simp [omegaPre]

/-- **Every natural number is below `ω`.**  They agree with `+` up to `n`, and
at `n` the natural has run out — the middle sign — while `ω` continues with
`+`. -/
theorem ofNat_lt_omega (n : ℕ) : ofNat n < omega := by
  rw [ofNat, omega, mk_lt_mk]
  refine ⟨(n : Ordinal), fun γ hγ => ?_, ?_⟩
  · rw [natPre_signAt_of_lt hγ,
      omegaPre_signAt_of_lt (hγ.trans (Ordinal.natCast_lt_omega0 n))]
  · rw [natPre_signAt_of_ge (le_refl _),
      omegaPre_signAt_of_lt (Ordinal.natCast_lt_omega0 n)]
    exact Sign.zero_lt_pos

/-- `natPre 0` and `zeroPre` are different *expansions* — one records `+`
signs, the other `−` — but both have level `0`, so no position is significant
and they denote the same surreal. -/
theorem ofNat_zero : ofNat 0 = (0 : Surreal) := by
  rw [ofNat]
  refine mk_eq_mk.mpr (funext fun β => ?_)
  rw [PreSurreal.signAt_of_ge (by simp [natPre]),
    PreSurreal.signAt_of_ge (by simp [zeroPre])]

/-- `ω` is positive. -/
theorem zero_lt_omega : (0 : Surreal) < omega := by
  rw [← ofNat_zero]
  exact ofNat_lt_omega 0

end Surreal

end Mettapedia.SetTheory.SignExpansion

#print axioms Mettapedia.SetTheory.SignExpansion.PreSurreal.length_eq_of_signAt_eq
#print axioms Mettapedia.SetTheory.SignExpansion.PreSurreal.lt_or_equiv_or_gt
#print axioms Mettapedia.SetTheory.SignExpansion.PreSurreal.lt_trans
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.ofNat_lt_omega
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.zero_lt_omega
