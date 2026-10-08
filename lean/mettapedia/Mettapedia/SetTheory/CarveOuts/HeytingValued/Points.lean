import Mettapedia.SetTheory.CarveOuts.HeytingValued.Names
import Mathlib.Order.Atoms
import Mathlib.SetTheory.ZFC.Basic

/-!
# Points of the frame: two-valued readings and the principal collapse

A **point** of a frame `H` is a completely prime filter: a set of truth values containing
`⊤`, closed under binary meets and upward, such that a join belongs to it exactly when some
joinand does (`Point`). Equivalently, a frame homomorphism `H → Prop`.

* **The two-valued quotient.** At a point `p`, names are identified when `p` holds of their
  equality and related by membership when `p` holds of their membership. This is an
  equivalence and a congruence for membership (`Point.setoid`, `Point.Quotient`,
  `Point.Quotient.mem`): a two-valued structure.
* **What every point transfers.** For a positive bounded formula (no implication, no bounded
  universal) the point holds of its value exactly when the formula is satisfied in the
  two-valued reading (`Point.holds_eval_iff_of_positive`). Implication and the bounded
  universal are not transferred by every point; a counterexample at a non-principal point
  is in `FreePoint`.
* **The principal collapse.** An atom `a` generates a point (`atomPoint`), and at that point
  the reading collapses to the ground: the map `collapseZF a` to Mathlib's `ZFSet` sends
  `p`-equal names to equal sets and `p`-members to members, and conversely
  (`le_eq_iff_collapseZF_eq`, `le_mem_iff_collapseZF_mem`); it is onto, through the check
  names of pre-sets (`collapseZF_check`). Every bounded formula transfers
  (`le_eval_iff_zfHolds`), so the two-valued quotient at the atom is `ZFSet`, membership
  preserved and reflected (`atomQuotientEquivZFSet`, `atomQuotientEquivZFSet_mem_iff`).
  The two-element frame `Prop` is the case `a = ⊤`.

Choice enters only through the atom: that an atom is completely prime and passes through
implication uses excluded middle. The quotient, the congruence and the positive transfer
are choice-free.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.CarveOuts.HeytingValued

universe u

/-! ## Points -/

/-- A point of a frame: a completely prime filter of truth values. -/
structure Point (H : Type u) [Order.Frame H] where
  /-- The truth values the point affirms. -/
  holds : H → Prop
  holds_top : holds ⊤
  holds_inf : ∀ a b, holds (a ⊓ b) ↔ holds a ∧ holds b
  holds_sSup : ∀ S : Set H, holds (sSup S) ↔ ∃ s ∈ S, holds s

namespace Point

variable {H : Type u} [Order.Frame H] (p : Point H)

theorem holds_mono {a b : H} (hab : a ≤ b) (ha : p.holds a) : p.holds b := by
  have e : a ⊓ b = a := inf_eq_left.mpr hab
  exact ((p.holds_inf a b).mp (e.symm ▸ ha)).2

theorem holds_iSup {ι : Sort*} (f : ι → H) : p.holds (⨆ i, f i) ↔ ∃ i, p.holds (f i) := by
  rw [iSup, p.holds_sSup]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, h⟩
    exact ⟨i, h⟩
  · rintro ⟨i, h⟩
    exact ⟨f i, ⟨i, rfl⟩, h⟩

theorem not_holds_bot : ¬ p.holds ⊥ := by
  rw [← sSup_empty, p.holds_sSup]
  rintro ⟨_, h, _⟩
  exact h

theorem holds_sup (a b : H) : p.holds (a ⊔ b) ↔ p.holds a ∨ p.holds b := by
  rw [← sSup_pair, p.holds_sSup]
  constructor
  · rintro ⟨s, hs, h⟩
    rcases hs with rfl | rfl
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨a, Or.inl rfl, h⟩
    · exact ⟨b, Or.inr rfl, h⟩

/-! ### The two-valued quotient -/

/-- Names identified at the point. -/
def setoid : Setoid (Name H) where
  r x y := p.holds (Name.eq x y)
  iseqv :=
    { refl := fun x => by rw [Name.eq_self]; exact p.holds_top
      symm := fun {x y} h => by rw [Name.eq_comm]; exact h
      trans := fun {x y z} hxy hyz =>
        p.holds_mono (Name.eq_inf_eq_le x y z) ((p.holds_inf _ _).mpr ⟨hxy, hyz⟩) }

/-- The two-valued reading of the names at the point. -/
def Quotient : Type (u + 1) :=
  _root_.Quotient p.setoid

/-- Membership at the point respects the identification. -/
theorem holds_mem_congr {x x' y y' : Name H} (hx : p.holds (Name.eq x x'))
    (hy : p.holds (Name.eq y y')) (h : p.holds (Name.mem x y)) : p.holds (Name.mem x' y') := by
  have h1 : p.holds (Name.mem x' y) :=
    p.holds_mono (Name.eq_inf_mem_le_left x x' y) ((p.holds_inf _ _).mpr ⟨hx, h⟩)
  exact p.holds_mono (Name.eq_inf_mem_le_right x' y y') ((p.holds_inf _ _).mpr ⟨hy, h1⟩)

/-- Membership in the two-valued reading. -/
def Quotient.mem : p.Quotient → p.Quotient → Prop :=
  _root_.Quotient.lift₂ (s₁ := p.setoid) (s₂ := p.setoid) (fun x y => p.holds (Name.mem x y))
    fun _ _ _ _ hx hy => propext
      ⟨fun h => p.holds_mem_congr hx hy h,
        fun h => p.holds_mem_congr (p.setoid.symm hx) (p.setoid.symm hy) h⟩

theorem Quotient.mem_mk (x y : Name H) :
    Quotient.mem p (_root_.Quotient.mk p.setoid x) (_root_.Quotient.mk p.setoid y) ↔
      p.holds (Name.mem x y) :=
  Iff.rfl

end Point

/-! ## Satisfaction in a two-valued structure -/

/-- Satisfaction of a bounded formula in a structure with a membership and an equality. -/
def Holds {M : Type*} (memM eqM : M → M → Prop) : {n : ℕ} → BFormula n → (Fin n → M) → Prop
  | _, .falsum, _ => False
  | _, .mem a b, v => memM (v a) (v b)
  | _, .eq a b, v => eqM (v a) (v b)
  | _, .and φ ψ, v => Holds memM eqM φ v ∧ Holds memM eqM ψ v
  | _, .or φ ψ, v => Holds memM eqM φ v ∨ Holds memM eqM ψ v
  | _, .imp φ ψ, v => Holds memM eqM φ v → Holds memM eqM ψ v
  | _, .ball b φ, v => ∀ z, memM z (v b) → Holds memM eqM φ (Fin.cons z v : Fin _ → M)
  | _, .bex b φ, v => ∃ z, memM z (v b) ∧ Holds memM eqM φ (Fin.cons z v : Fin _ → M)

/-- Satisfaction in Mathlib's `ZFSet`. -/
abbrev ZFHolds {n : ℕ} (φ : BFormula n) (v : Fin n → ZFSet.{u}) : Prop :=
  Holds (fun x y : ZFSet.{u} => x ∈ y) (fun x y => x = y) φ v

/-- Positive bounded formulas: no implication and no bounded universal. -/
inductive BFormula.Positive : {n : ℕ} → BFormula n → Prop
  | falsum {n : ℕ} : Positive (BFormula.falsum (n := n))
  | mem {n : ℕ} (a b : Fin n) : Positive (BFormula.mem a b)
  | eq {n : ℕ} (a b : Fin n) : Positive (BFormula.eq a b)
  | and {n : ℕ} {φ ψ : BFormula n} : Positive φ → Positive ψ → Positive (BFormula.and φ ψ)
  | or {n : ℕ} {φ ψ : BFormula n} : Positive φ → Positive ψ → Positive (BFormula.or φ ψ)
  | bex {n : ℕ} (b : Fin n) {φ : BFormula (n + 1)} : Positive φ → Positive (BFormula.bex b φ)

namespace Point

variable {H : Type u} [Order.Frame H] (p : Point H)

/-- The two-valued reading at a point, as a structure on names. -/
abbrev reads {n : ℕ} (φ : BFormula n) (v : Fin n → Name H) : Prop :=
  Holds (fun x y => p.holds (Name.mem x y)) (fun x y => p.holds (Name.eq x y)) φ v

/-- **Every point transfers positive bounded truth.** -/
theorem holds_eval_iff_of_positive : ∀ {n : ℕ} {φ : BFormula n}, φ.Positive →
    ∀ v : Fin n → Name H, (p.holds (Name.eval φ v) ↔ p.reads φ v)
  | _, _, .falsum, _ => ⟨fun h => p.not_holds_bot h, False.elim⟩
  | _, _, .mem _ _, _ => Iff.rfl
  | _, _, .eq _ _, _ => Iff.rfl
  | _, _, .and hφ hψ, v => by
    show p.holds (_ ⊓ _) ↔ _ ∧ _
    rw [p.holds_inf, holds_eval_iff_of_positive hφ v, holds_eval_iff_of_positive hψ v]
  | _, _, .or hφ hψ, v => by
    show p.holds (_ ⊔ _) ↔ _ ∨ _
    rw [p.holds_sup, holds_eval_iff_of_positive hφ v, holds_eval_iff_of_positive hψ v]
  | _, _, .bex b (φ := φ) hφ, v => by
    show p.holds (⨆ i, (v b).weight i ⊓ Name.eval φ (Fin.cons ((v b).child i) v)) ↔
      ∃ z, p.holds (Name.mem z (v b)) ∧ p.reads φ (Fin.cons z v)
    rw [p.holds_iSup]
    constructor
    · rintro ⟨i, hi⟩
      obtain ⟨hw, hφi⟩ := (p.holds_inf _ _).mp hi
      exact ⟨(v b).child i, p.holds_mono (Name.weight_le_mem _ i) hw,
        (holds_eval_iff_of_positive hφ _).mp hφi⟩
    · rintro ⟨z, hz, hφz⟩
      rw [Name.mem_eq_iSup, p.holds_iSup] at hz
      obtain ⟨j, hj⟩ := hz
      obtain ⟨hw, heq⟩ := (p.holds_inf _ _).mp hj
      refine ⟨j, (p.holds_inf _ _).mpr ⟨hw, ?_⟩⟩
      exact p.holds_mono (Name.eval_subst_cons φ v z _)
        ((p.holds_inf _ _).mpr ⟨heq, (holds_eval_iff_of_positive hφ _).mpr hφz⟩)

end Point

/-! ## Atoms generate points -/

section Atoms

variable {H : Type u} [Order.Frame H] {a : H}

/-- An atom below a join is below some joinand. -/
theorem atom_le_iSup_iff (ha : IsAtom a) {ι : Sort*} (f : ι → H) :
    a ≤ ⨆ i, f i ↔ ∃ i, a ≤ f i := by
  constructor
  · intro h
    by_contra none
    have below : ∀ i, a ⊓ f i = ⊥ := fun i =>
      ha.2 _ (lt_of_le_of_ne inf_le_left fun e => not_exists.mp none i (e ▸ inf_le_right))
    apply ha.1
    calc a = a ⊓ ⨆ i, f i := (inf_eq_left.mpr h).symm
      _ = ⨆ i, a ⊓ f i := inf_iSup_eq _ _
      _ = ⊥ := by simp only [below, iSup_bot]
  · rintro ⟨i, hi⟩
    exact le_iSup_of_le i hi

theorem atom_le_sup_iff (ha : IsAtom a) (b c : H) : a ≤ b ⊔ c ↔ a ≤ b ∨ a ≤ c := by
  constructor
  · intro h
    by_contra none
    rw [not_or] at none
    have hb : a ⊓ b = ⊥ :=
      ha.2 _ (lt_of_le_of_ne inf_le_left fun e => none.1 (e ▸ inf_le_right))
    have hc : a ⊓ c = ⊥ :=
      ha.2 _ (lt_of_le_of_ne inf_le_left fun e => none.2 (e ▸ inf_le_right))
    apply ha.1
    refine le_bot_iff.mp ?_
    calc a ≤ a ⊓ (b ⊔ c) := le_inf le_rfl h
      _ ≤ a ⊓ b ⊔ a ⊓ c := Name.inf_sup_le_sup_inf _ _ _
      _ = ⊥ := by rw [hb, hc, sup_bot_eq]
  · rintro (h | h)
    · exact le_sup_of_le_left h
    · exact le_sup_of_le_right h

/-- An atom passes through implication. -/
theorem atom_le_himp_iff (ha : IsAtom a) (b c : H) : a ≤ b ⇨ c ↔ (a ≤ b → a ≤ c) := by
  constructor
  · intro h hb
    exact le_trans (le_inf le_rfl hb) (le_himp_iff.mp h)
  · intro h
    rw [le_himp_iff]
    by_cases hb : a ≤ b
    · exact le_trans inf_le_left (h hb)
    · have : a ⊓ b = ⊥ :=
        ha.2 _ (lt_of_le_of_ne inf_le_left fun e => hb (e ▸ inf_le_right))
      rw [this]
      exact bot_le

/-- **The principal point of an atom.** -/
def atomPoint (ha : IsAtom a) : Point H where
  holds h := a ≤ h
  holds_top := le_top
  holds_inf _ _ := le_inf_iff
  holds_sSup S := by
    rw [sSup_eq_iSup', atom_le_iSup_iff ha]
    constructor
    · rintro ⟨s, hs⟩
      exact ⟨s.1, s.2, hs⟩
    · rintro ⟨s, hs, h⟩
      exact ⟨⟨s, hs⟩, h⟩

end Atoms

/-! ## The collapse to the ground -/

namespace Name

variable {H : Type u} [Order.Frame H]

/-- The pre-set of a name at `a`: the children whose weight is at least `a`, collapsed. -/
def collapse (a : H) : Name H → PSet.{u}
  | mk ι A B => ⟨{i : ι // a ≤ B i}, fun i => collapse a (A i.1)⟩

/-- The set of a name at `a`. -/
def collapseZF (a : H) (x : Name H) : ZFSet.{u} :=
  ZFSet.mk (collapse a x)

/-- The check name of a pre-set: every member with weight `⊤`. -/
def check : PSet.{u} → Name H
  | ⟨α, A⟩ => mk α (fun i => check (A i)) (fun _ => ⊤)

theorem collapse_check (a : H) (x : PSet.{u}) : PSet.Equiv (collapse a (check x)) x := by
  induction x with
  | mk α A ih =>
    rw [PSet.equiv_iff]
    exact ⟨fun i => ⟨i.1, ih i.1⟩, fun i => ⟨⟨i, le_top⟩, ih i⟩⟩

theorem collapseZF_check (a : H) (x : PSet.{u}) :
    collapseZF a (check (H := H) x) = ZFSet.mk x :=
  ZFSet.sound (collapse_check a x)

/-- **The collapse is onto the ground.** -/
theorem collapseZF_surjective (a : H) : Function.Surjective (collapseZF (H := H) a) := by
  intro s
  induction s using Quotient.inductionOn with
  | h x => exact ⟨check x, collapseZF_check a x⟩

theorem mem_collapseZF_iff (a : H) (x : Name H) (z : ZFSet.{u}) :
    z ∈ collapseZF a x ↔ ∃ i, a ≤ x.weight i ∧ z = collapseZF a (x.child i) := by
  cases x with
  | mk ι A B =>
    induction z using Quotient.inductionOn with
    | h w =>
      show ZFSet.mk w ∈ ZFSet.mk (collapse a (mk ι A B)) ↔ _
      rw [ZFSet.mk_mem_iff, PSet.mem_def]
      constructor
      · rintro ⟨⟨i, hi⟩, e⟩
        exact ⟨i, hi, ZFSet.sound e⟩
      · rintro ⟨i, hi, e⟩
        exact ⟨⟨i, hi⟩, ZFSet.exact e⟩

variable {a : H}

/-- **Principal collapse of equality.** -/
theorem le_eq_iff_collapse_equiv (ha : IsAtom a) (x y : Name H) :
    a ≤ eq x y ↔ PSet.Equiv (collapse a x) (collapse a y) := by
  induction x generalizing y with
  | mk ι A B ih =>
    cases y with
    | mk κ A' B' =>
      rw [eq_mk, le_inf_iff, le_iInf_iff, le_iInf_iff, PSet.equiv_iff]
      simp only [atom_le_himp_iff ha, atom_le_iSup_iff ha, le_inf_iff, ih]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun i => ?_, fun j => ?_⟩
        · obtain ⟨j, hj, e⟩ := h1 i.1 i.2
          exact ⟨⟨j, hj⟩, e⟩
        · obtain ⟨i, hi, e⟩ := h2 j.1 j.2
          exact ⟨⟨i, hi⟩, e⟩
      · rintro ⟨h1, h2⟩
        refine ⟨fun i hi => ?_, fun j hj => ?_⟩
        · obtain ⟨⟨j, hj⟩, e⟩ := h1 ⟨i, hi⟩
          exact ⟨j, hj, e⟩
        · obtain ⟨⟨i, hi⟩, e⟩ := h2 ⟨j, hj⟩
          exact ⟨i, hi, e⟩

theorem le_eq_iff_collapseZF_eq (ha : IsAtom a) (x y : Name H) :
    a ≤ eq x y ↔ collapseZF a x = collapseZF a y := by
  rw [le_eq_iff_collapse_equiv ha, collapseZF, collapseZF, ZFSet.eq]

/-- **Principal collapse of membership.** -/
theorem le_mem_iff_collapseZF_mem (ha : IsAtom a) (x y : Name H) :
    a ≤ mem x y ↔ collapseZF a x ∈ collapseZF a y := by
  rw [mem_eq_iSup, atom_le_iSup_iff ha, mem_collapseZF_iff]
  simp only [le_inf_iff, le_eq_iff_collapseZF_eq ha]

/-- **Principal collapse of every bounded formula.** At an atom, the value of a bounded
formula is affirmed exactly when the formula holds in `ZFSet` of the collapsed names. -/
theorem le_eval_iff_zfHolds (ha : IsAtom a) : ∀ {n : ℕ} (φ : BFormula n) (v : Fin n → Name H),
    a ≤ eval φ v ↔ ZFHolds φ (collapseZF a ∘ v)
  | _, .falsum, _ => ⟨fun h => ha.1 (le_bot_iff.mp h), False.elim⟩
  | _, .mem x y, v => le_mem_iff_collapseZF_mem ha (v x) (v y)
  | _, .eq x y, v => le_eq_iff_collapseZF_eq ha (v x) (v y)
  | _, .and φ ψ, v => by
    show a ≤ _ ⊓ _ ↔ _ ∧ _
    rw [le_inf_iff, le_eval_iff_zfHolds ha φ v, le_eval_iff_zfHolds ha ψ v]
  | _, .or φ ψ, v => by
    show a ≤ _ ⊔ _ ↔ _ ∨ _
    rw [atom_le_sup_iff ha, le_eval_iff_zfHolds ha φ v, le_eval_iff_zfHolds ha ψ v]
  | _, .imp φ ψ, v => by
    show a ≤ _ ⇨ _ ↔ (_ → _)
    rw [atom_le_himp_iff ha, le_eval_iff_zfHolds ha φ v, le_eval_iff_zfHolds ha ψ v]
  | _, .ball b φ, v => by
    show a ≤ ⨅ i, (v b).weight i ⇨ eval φ (Fin.cons ((v b).child i) v) ↔
      ∀ z, z ∈ collapseZF a (v b) → ZFHolds φ (Fin.cons z (collapseZF a ∘ v))
    rw [le_iInf_iff]
    simp only [atom_le_himp_iff ha, le_eval_iff_zfHolds ha φ, Fin.comp_cons, mem_collapseZF_iff]
    constructor
    · rintro h z ⟨i, hi, rfl⟩
      exact h i hi
    · intro h i hi
      exact h _ ⟨i, hi, rfl⟩
  | _, .bex b φ, v => by
    show a ≤ ⨆ i, (v b).weight i ⊓ eval φ (Fin.cons ((v b).child i) v) ↔
      ∃ z, z ∈ collapseZF a (v b) ∧ ZFHolds φ (Fin.cons z (collapseZF a ∘ v))
    rw [atom_le_iSup_iff ha]
    simp only [le_inf_iff, le_eval_iff_zfHolds ha φ, Fin.comp_cons, mem_collapseZF_iff]
    constructor
    · rintro ⟨i, hi, h⟩
      exact ⟨_, ⟨i, hi, rfl⟩, h⟩
    · rintro ⟨z, ⟨i, hi, rfl⟩, h⟩
      exact ⟨i, hi, h⟩

end Name

/-! ## The two-valued quotient at an atom is `ZFSet` -/

section AtomQuotient

variable {H : Type u} [Order.Frame H] {a : H}

/-- The collapse, read on the two-valued quotient at the atom. -/
def atomQuotientToZFSet (ha : IsAtom a) : (atomPoint ha).Quotient → ZFSet.{u} :=
  _root_.Quotient.lift (s := (atomPoint ha).setoid) (Name.collapseZF a)
    fun x y h => (Name.le_eq_iff_collapseZF_eq ha x y).mp h

theorem atomQuotientToZFSet_bijective (ha : IsAtom a) :
    Function.Bijective (atomQuotientToZFSet ha) := by
  constructor
  · intro x y
    induction x using _root_.Quotient.inductionOn with
    | h x =>
      induction y using _root_.Quotient.inductionOn with
      | h y =>
        intro e
        exact _root_.Quotient.sound ((Name.le_eq_iff_collapseZF_eq ha x y).mpr e)
  · intro s
    obtain ⟨x, hx⟩ := Name.collapseZF_surjective a s
    exact ⟨_root_.Quotient.mk _ x, hx⟩

/-- **The principal collapse.** At an atom, the two-valued quotient is the ground `ZFSet`. -/
noncomputable def atomQuotientEquivZFSet (ha : IsAtom a) : (atomPoint ha).Quotient ≃ ZFSet.{u} :=
  Equiv.ofBijective _ (atomQuotientToZFSet_bijective ha)

theorem atomQuotientEquivZFSet_mem_iff (ha : IsAtom a) (x y : (atomPoint ha).Quotient) :
    Point.Quotient.mem _ x y ↔ atomQuotientEquivZFSet ha x ∈ atomQuotientEquivZFSet ha y := by
  induction x using _root_.Quotient.inductionOn with
  | h x =>
    induction y using _root_.Quotient.inductionOn with
    | h y => exact Name.le_mem_iff_collapseZF_mem ha x y

end AtomQuotient

/-! ## The two-element frame -/

/-- `⊤` is an atom of the two-element frame `Prop`. -/
theorem isAtom_top_prop : IsAtom (⊤ : Prop) := by
  refine ⟨fun h => (h ▸ trivial : (⊥ : Prop)), fun b hb => ?_⟩
  have nb : ¬ b := fun hb' => (lt_iff_le_not_ge.mp hb).2 (fun _ => hb')
  exact propext ⟨fun h => nb h, False.elim⟩

/-- **The two-element frame is the ground.** Its two-valued quotient at `⊤` is `ZFSet`, and a
bounded formula holds there exactly when it holds in `ZFSet` of the collapsed names. -/
theorem prop_eval_iff_zfHolds {n : ℕ} (φ : BFormula n) (v : Fin n → Name.{0} Prop) :
    Name.eval φ v ↔ ZFHolds φ (Name.collapseZF ⊤ ∘ v) := by
  rw [← Name.le_eval_iff_zfHolds isAtom_top_prop φ v]
  exact ⟨fun h _ => h, fun h => h trivial⟩

end Mettapedia.SetTheory.CarveOuts.HeytingValued
