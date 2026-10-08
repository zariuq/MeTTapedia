import Mettapedia.SetTheory.CarveOuts.HeytingValued.Names
import Mathlib.Order.Heyting.Regular
import Mathlib.Data.Fin.VecNotation

/-!
# The double-negation part, and a constructive witness

**The double-negation part.** The regular elements of a frame `H` (those with `¬¬a = a`,
Mathlib's `Heyting.Regular H`) form a complete Boolean algebra (`regularCompleteBooleanAlgebra`):
joins are double negations of joins, meets are meets. The double negation
`toRegular : H → Regular H` preserves finite meets and all joins (`toRegular_inf`,
`toRegular_sSup`), so it is a frame quotient, the classical carve-out of the top.

**Excluded middle.** Over a complete Boolean algebra every bounded excluded-middle instance
has value `⊤` (`eval_lem_eq_top`), in particular over the double-negation part
(`eval_lem_regular`). Over a frame `H`, bounded excluded middle has value `⊤` for every
formula and assignment exactly when `H` is Boolean (`boundedLEM_iff`): every truth value is
the value of an atomic sentence.

**The constructive witness.** `Persistent P` is the frame of up-closed propositions over a
preorder `P` of stages, with Kripke implication, built by hand so that nothing in it uses
choice. Over the two stages `now ≤ later` it is the three-element chain `⊥ < m < ⊤`, where
`m` holds from `later` on. The sentence `∅ ∈ {∅ ↦ m}` has value `m`, and its excluded-middle
instance has value `m ≠ ⊤` (`chain_lem_value`, `chain_lem_ne_top`). The element `m` is dense,
`¬¬m = ⊤` (`chain_m_dense`): the double-negation part identifies it with truth.

The Boolean statements use the regular elements' complete Boolean algebra, which is
choice-free; the constructive witness is choice-free.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.CarveOuts.HeytingValued

universe u v

open Heyting

/-! ## The regular elements form a complete Boolean algebra -/

section Regular

variable {H : Type u} [Order.Frame H]

theorem compl_compl_mono {a b : H} (h : a ≤ b) : aᶜᶜ ≤ bᶜᶜ :=
  compl_le_compl (compl_le_compl h)

/-- The regular elements of a frame form a complete Boolean algebra. -/
instance regularCompleteBooleanAlgebra : CompleteBooleanAlgebra (Regular H) where
  __ := (inferInstance : BooleanAlgebra (Regular H))
  sSup S := Regular.toRegular (sSup (Regular.val '' S))
  sInf S := Regular.toRegular (sInf (Regular.val '' S))
  isLUB_sSup S := by
    refine ⟨fun r hr => ?_, fun r h => ?_⟩
    · rw [← Regular.coe_le_coe, Regular.coe_toRegular]
      exact le_trans (le_sSup (Set.mem_image_of_mem Regular.val hr)) le_compl_compl
    · rw [← Regular.coe_le_coe, Regular.coe_toRegular]
      refine le_trans (compl_compl_mono (sSup_le ?_)) (le_of_eq r.prop)
      rintro _ ⟨x, hx, rfl⟩
      exact Regular.coe_le_coe.mpr (h hx)
  isGLB_sInf S := by
    refine ⟨fun r hr => ?_, fun r h => ?_⟩
    · rw [← Regular.coe_le_coe, Regular.coe_toRegular]
      exact le_trans (compl_compl_mono (sInf_le (Set.mem_image_of_mem Regular.val hr)))
        (le_of_eq r.prop)
    · rw [← Regular.coe_le_coe, Regular.coe_toRegular]
      refine le_trans (le_of_eq r.prop.symm) (compl_compl_mono (le_sInf ?_))
      rintro _ ⟨x, hx, rfl⟩
      exact Regular.coe_le_coe.mpr (h hx)

theorem coe_sSup_regular (S : Set (Regular H)) :
    ((sSup S : Regular H) : H) = (sSup (Regular.val '' S))ᶜᶜ :=
  Regular.coe_toRegular _

/-- Double negation preserves binary meets. -/
theorem toRegular_inf (a b : H) :
    Regular.toRegular (a ⊓ b) = Regular.toRegular a ⊓ Regular.toRegular b := by
  apply Regular.coe_injective
  rw [Regular.coe_inf, Regular.coe_toRegular, Regular.coe_toRegular, Regular.coe_toRegular,
    compl_compl_inf_distrib]

theorem toRegular_top : Regular.toRegular (⊤ : H) = ⊤ := by
  apply Regular.coe_injective
  rw [Regular.coe_toRegular, Regular.coe_top, compl_top, compl_bot]

/-- Double negation preserves all joins. -/
theorem toRegular_sSup (T : Set H) :
    Regular.toRegular (sSup T) = sSup (Regular.toRegular '' T) := by
  apply Regular.coe_injective
  rw [Regular.coe_toRegular, coe_sSup_regular]
  apply le_antisymm
  · refine compl_compl_mono (sSup_le fun t ht => ?_)
    exact le_trans le_compl_compl (le_sSup ⟨Regular.toRegular t, ⟨t, ht, rfl⟩, rfl⟩)
  · have : sSup (Regular.val '' (Regular.toRegular '' T)) ≤ (sSup T)ᶜᶜ := by
      refine sSup_le ?_
      rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      rw [Regular.coe_toRegular]
      exact compl_compl_mono (le_sSup ht)
    exact le_trans (compl_compl_mono this) (le_of_eq (by rw [compl_compl_compl]))

end Regular

/-! ## Excluded middle -/

section ExcludedMiddle

theorem eval_lem {H : Type u} [Order.Frame H] {n : ℕ} (φ : BFormula n) (v : Fin n → Name H) :
    Name.eval φ.lem v = Name.eval φ v ⊔ (Name.eval φ v)ᶜ := by
  show Name.eval φ v ⊔ (Name.eval φ v ⇨ ⊥) = _
  rw [himp_bot]

/-- **Over a complete Boolean algebra, bounded excluded middle has value `⊤`.** -/
theorem eval_lem_eq_top {B : Type u} [CompleteBooleanAlgebra B] {n : ℕ} (φ : BFormula n)
    (v : Fin n → Name B) : Name.eval φ.lem v = ⊤ := by
  rw [eval_lem]
  exact sup_compl_eq_top

/-- **Bounded excluded middle holds in the double-negation part.** -/
theorem eval_lem_regular {H : Type u} [Order.Frame H] {n : ℕ} (φ : BFormula n)
    (v : Fin n → Name (Regular H)) : Name.eval φ.lem v = ⊤ :=
  eval_lem_eq_top φ v

/-- The atomic sentence `∅ ∈ x₁`. -/
def emptyMem : BFormula 2 :=
  .mem 0 1

theorem eval_emptyMem_truthName {H : Type u} [Order.Frame H] (h : H) :
    Name.eval emptyMem ![Name.empty, Name.truthName h] = h :=
  Name.mem_empty_truthName h

/-- **Bounded excluded middle is exactly Booleanness.** -/
theorem boundedLEM_iff {H : Type u} [Order.Frame H] :
    (∀ (n : ℕ) (φ : BFormula n) (v : Fin n → Name H), Name.eval φ.lem v = ⊤) ↔
      ∀ h : H, h ⊔ hᶜ = ⊤ := by
  constructor
  · intro all h
    have := all 2 emptyMem ![Name.empty, Name.truthName h]
    rwa [eval_lem, eval_emptyMem_truthName] at this
  · intro bool n φ v
    rw [eval_lem]
    exact bool _

end ExcludedMiddle

/-! ## A choice-free frame: persistent propositions over stages -/

/-- A proposition over a preorder of stages that persists to later stages. -/
@[ext]
structure Persistent (P : Type u) [Preorder P] where
  holds : P → Prop
  mono : ∀ {s t : P}, s ≤ t → holds s → holds t

namespace Persistent

variable {P : Type u} [Preorder P]

/-- Persistent propositions, with Kripke implication, form a frame. Every operation is
computed pointwise or by quantifying over later stages; nothing uses choice. -/
instance frame : Order.Frame (Persistent P) where
  le x y := ∀ s, x.holds s → y.holds s
  lt x y := (∀ s, x.holds s → y.holds s) ∧ ¬ ∀ s, y.holds s → x.holds s
  le_refl _ _ h := h
  le_trans _ _ _ hxy hyz s h := hyz s (hxy s h)
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_antisymm x y hxy hyx := Persistent.ext (funext fun s => propext ⟨hxy s, hyx s⟩)
  sup x y := ⟨fun s => x.holds s ∨ y.holds s, fun h => Or.imp (x.mono h) (y.mono h)⟩
  le_sup_left _ _ _ h := Or.inl h
  le_sup_right _ _ _ h := Or.inr h
  sup_le _ _ _ hx hy s h := h.elim (hx s) (hy s)
  inf x y := ⟨fun s => x.holds s ∧ y.holds s, fun h => And.imp (x.mono h) (y.mono h)⟩
  inf_le_left _ _ _ h := h.1
  inf_le_right _ _ _ h := h.2
  le_inf _ _ _ hy hz s h := ⟨hy s h, hz s h⟩
  sSup S := ⟨fun s => ∃ x ∈ S, x.holds s, fun h => fun ⟨x, hx, hs⟩ => ⟨x, hx, x.mono h hs⟩⟩
  isLUB_sSup _ := ⟨fun x hx _ h => ⟨x, hx, h⟩, fun _ h s ⟨x, hx, hs⟩ => h hx s hs⟩
  sInf S := ⟨fun s => ∀ x ∈ S, x.holds s, fun h hs x hx => x.mono h (hs x hx)⟩
  isGLB_sInf _ := ⟨fun x hx _ h => h x hx, fun _ h s hs x hx => h hx s hs⟩
  top := ⟨fun _ => True, fun _ _ => trivial⟩
  le_top _ _ _ := trivial
  bot := ⟨fun _ => False, fun _ h => h⟩
  bot_le _ _ h := h.elim
  himp x y := ⟨fun s => ∀ t, s ≤ t → x.holds t → y.holds t,
    fun hst h t htu hx => h t (le_trans hst htu) hx⟩
  le_himp_iff z x y := by
    constructor
    · intro h s ⟨hz, hx⟩
      exact h s hz s le_rfl hx
    · intro h s hz t hst hx
      exact h t ⟨z.mono hst hz, hx⟩
  compl x := ⟨fun s => ∀ t, s ≤ t → x.holds t → False,
    fun hst h t htu hx => h t (le_trans hst htu) hx⟩
  himp_bot _ := rfl

theorem holds_sup (x y : Persistent P) (s : P) : (x ⊔ y).holds s ↔ x.holds s ∨ y.holds s :=
  Iff.rfl

theorem holds_compl (x : Persistent P) (s : P) :
    xᶜ.holds s ↔ ∀ t, s ≤ t → x.holds t → False :=
  Iff.rfl

theorem holds_top (s : P) : (⊤ : Persistent P).holds s :=
  trivial

end Persistent

/-- Two stages, `now ≤ later`. -/
inductive Stage : Type where
  | now
  | later

namespace Stage

/-- `now` comes before every stage; `later` only before itself. -/
def le : Stage → Stage → Prop
  | now, _ => True
  | later, later => True
  | later, now => False

instance : Preorder Stage where
  le := le
  le_refl s := by cases s <;> exact trivial
  le_trans a b c hab hbc := by
    cases a <;> cases b <;> cases c <;> first | exact trivial | exact hab.elim | exact hbc.elim

end Stage

/-- The middle truth value of the three-element chain: it holds from `later` on. -/
def chainMiddle : Persistent Stage :=
  ⟨fun s => s = Stage.later, fun {s t} hst hs => by
    subst hs
    cases t
    · exact hst.elim
    · rfl⟩

/-- Nothing below the middle value but falsity: its negation is `⊥`. -/
theorem chainMiddle_compl : chainMiddleᶜ = ⊥ :=
  Persistent.ext (funext fun s => propext
    ⟨fun h => h Stage.later (by cases s <;> exact trivial) rfl, False.elim⟩)

theorem chainMiddle_ne_top : chainMiddle ≠ ⊤ := by
  intro h
  have : chainMiddle.holds Stage.now := h ▸ Persistent.holds_top Stage.now
  exact Stage.noConfusion this

/-- **The middle value is dense.** -/
theorem chain_m_dense : chainMiddleᶜᶜ = ⊤ := by
  rw [chainMiddle_compl, compl_bot]

/-- **The excluded-middle instance of `∅ ∈ {∅ ↦ m}` has value `m`.** -/
theorem chain_lem_value :
    Name.eval emptyMem.lem ![Name.empty, Name.truthName chainMiddle] = chainMiddle := by
  rw [eval_lem, eval_emptyMem_truthName, chainMiddle_compl, sup_bot_eq]

/-- **The constructive witness.** Over the three-element chain, a bounded excluded-middle
instance does not have value `⊤`. -/
theorem chain_lem_ne_top :
    Name.eval emptyMem.lem ![Name.empty, Name.truthName chainMiddle] ≠ ⊤ := by
  rw [chain_lem_value]
  exact chainMiddle_ne_top

/-- The three-element chain is not Boolean. -/
theorem chain_not_boolean : ¬ ∀ h : Persistent Stage, h ⊔ hᶜ = ⊤ := fun bool =>
  chain_lem_ne_top (boundedLEM_iff.mpr bool 2 emptyMem _)

end Mettapedia.SetTheory.CarveOuts.HeytingValued
