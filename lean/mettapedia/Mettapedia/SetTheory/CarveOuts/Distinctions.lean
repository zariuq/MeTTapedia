import Mettapedia.SetTheory.CarveOuts.HeytingValued.FreePoint
import Mettapedia.SetTheory.CarveOuts.HereditarilyFinite
import Mettapedia.SetTheory.CarveOuts.WellFoundedBubble
import Mettapedia.GSLT.Core.NonFactorization

/-!
# What each carve-out keeps

The carve-outs of the Heyting-valued top read the same sentences of the forcing language
(`Sentence H`: a bounded formula with names for its variables) and keep less and less:

* the **top** reads a sentence's truth value in `H` (`viewTop`);
* the **double-negation part** reads its double negation, in the complete Boolean algebra of
  regular elements (`viewNegNeg`);
* the **points** of the double-negation part read it two-valuedly, one verdict per point
  (`viewPoints`);
* the **ground** reads it in `ZFSet` at each atom of `H`, through the principal collapse
  (`viewGround`).

Each reading is a function of the one before (`factors_top_negNeg`, `factors_negNeg_points`,
`factors_points_ground`); the last step is the principal collapse: an atom gives a point of
the double-negation part (`regularAtomPoint`), and at it the verdict is the `ZFSet` verdict.

**One frame separates every step.** The frame of perspectives `Perspectives` is the product
of three poles: `Prop` (the finite pole: one atom, the ground), the chain `[0, ∞]` (a
non-Boolean pole with a free point), and the regular open sets of Cantor space (a gunky
Boolean pole with no point at all). Every truth value `h` is read by the atomic sentence
`∅ ∈ {∅ ↦ h}` (`atomicSentence`). The three witnesses:

* `fiber_negNeg_top`: the values `(⊥, 1, ⊥)` and `(⊥, ⊤, ⊥)` differ, and their double
  negations agree (`1` is dense in `[0, ∞]`);
* `fiber_points_negNeg`: the values `⊥` and `(⊥, ⊥, ⊤)` have different double negations, and
  no point tells them apart: a point affirming the second would give a point of the gunky
  pole (`not_holds_gunkTop`);
* `fiber_ground_points`: the values `(⊥, 0, ⊥)` and `(⊥, ⊤, ⊥)` receive the same verdict at
  every atom, because no atom lives on the chain (`atom_chain_eq_zero`), and different
  verdicts at the free point "positive" of the chain (`chainPoint`).

**The well-founded side.** The bubble's readout `toZFSet` is a function of the hyperset and
forgets the Quine atom: `Ω` and `∅` have the same readout (`fiber_bubble_hset`). The bubble's
seven laws hold both in `V_ω` and in all of `ZFSet`, while only `ZFSet` contains a closed
universe holding `∅` (`fiber_bubble_hotg`): the universe commitment of HOTG is not read off
the bubble.

Route grades are not claimed: none of these readings carries a distance.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.CarveOuts

open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.SetTheory.CarveOuts.HeytingValued
open Mettapedia.TypeTheory.MaterialSets
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Heyting TopologicalSpace
open scoped ENNReal ZFSet Ordinal

universe u

/-! ## Sentences and their readings -/

/-- A sentence of the forcing language: a bounded formula with names for its variables. -/
structure Sentence (H : Type u) where
  arity : ℕ
  formula : BFormula arity
  names : Fin arity → Name H

namespace Sentence

variable {H : Type u} [Order.Frame H]

/-- The truth value of a sentence. -/
def value (s : Sentence H) : H :=
  Name.eval s.formula s.names

end Sentence

variable {H : Type u} [Order.Frame H]

/-- The top reads the truth value. -/
def viewTop (s : Sentence H) : H :=
  s.value

/-- The double-negation part reads the double negation. -/
def viewNegNeg (s : Sentence H) : Regular H :=
  Regular.toRegular s.value

/-- The points of the double-negation part read one verdict each. -/
def viewPoints (s : Sentence H) : Point (Regular H) → Prop :=
  fun q => q.holds (Regular.toRegular s.value)

/-- The ground reads the sentence in `ZFSet` at each atom. -/
def viewGround (s : Sentence H) : {a : H // IsAtom a} → Prop :=
  fun a => ZFHolds s.formula (Name.collapseZF a.1 ∘ s.names)

/-- An atom is below a double negation exactly when it is below the value. -/
theorem atom_le_compl_compl_iff {a h : H} (ha : IsAtom a) : a ≤ hᶜᶜ ↔ a ≤ h := by
  constructor
  · intro hle
    by_contra hn
    have hah : a ⊓ h = ⊥ := ha.2 _ (lt_of_le_of_ne inf_le_left fun e => hn (e ▸ inf_le_right))
    have hc : a ≤ hᶜ := by
      rw [← himp_bot]
      exact le_himp_iff.mpr (le_of_eq hah)
    exact ha.1 (le_bot_iff.mp (le_trans (le_inf hc hle) (le_of_eq (inf_compl_self _))))
  · exact fun hle => le_trans hle le_compl_compl

/-- **An atom gives a point of the double-negation part.** -/
def regularAtomPoint {a : H} (ha : IsAtom a) : Point (Regular H) where
  holds r := a ≤ (r : H)
  holds_top := by
    rw [Regular.coe_top]
    exact le_top
  holds_inf r s := by
    show a ≤ (r : H) ⊓ (s : H) ↔ _
    exact le_inf_iff
  holds_sSup S := by
    show a ≤ ((sSup S : Regular H) : H) ↔ _
    rw [coe_sSup_regular, atom_le_compl_compl_iff ha, sSup_eq_iSup', atom_le_iSup_iff ha]
    constructor
    · rintro ⟨⟨_, ⟨r, hr, rfl⟩⟩, h⟩
      exact ⟨r, hr, h⟩
    · rintro ⟨r, hr, h⟩
      exact ⟨⟨r.val, r, hr, rfl⟩, h⟩

/-- A point of the frame that passes through double negation is a point of the
double-negation part. -/
def densePoint (p : Point H) (dense : ∀ h, p.holds hᶜᶜ ↔ p.holds h) :
    Point (Regular H) where
  holds r := p.holds (r : H)
  holds_top := by
    rw [Regular.coe_top]
    exact p.holds_top
  holds_inf r s := by
    show p.holds ((r : H) ⊓ (s : H)) ↔ _
    exact p.holds_inf _ _
  holds_sSup S := by
    show p.holds ((sSup S : Regular H) : H) ↔ _
    rw [coe_sSup_regular, dense, p.holds_sSup]
    constructor
    · rintro ⟨_, ⟨r, hr, rfl⟩, h⟩
      exact ⟨r, hr, h⟩
    · rintro ⟨r, hr, h⟩
      exact ⟨r.val, ⟨r, hr, rfl⟩, h⟩

/-! ## The chain of readings -/

theorem factors_top_negNeg : Factors (viewTop (H := H)) viewNegNeg :=
  ⟨Regular.toRegular, fun _ => rfl⟩

theorem factors_negNeg_points : Factors (viewNegNeg (H := H)) viewPoints :=
  ⟨fun r q => q.holds r, fun _ => rfl⟩

/-- **The principal collapse as a factorization.** The ground's verdict at an atom is the
verdict of the atom's point of the double-negation part. -/
theorem factors_points_ground : Factors (viewPoints (H := H)) viewGround := by
  refine ⟨fun F a => F (regularAtomPoint a.2), fun s => funext fun a => propext ?_⟩
  show a.1 ≤ (Regular.toRegular s.value : H) ↔ _
  rw [Regular.coe_toRegular, atom_le_compl_compl_iff a.2]
  exact Name.le_eval_iff_zfHolds a.2 _ _

/-- The atomic sentence `∅ ∈ {∅ ↦ h}`, whose truth value is `h`. -/
def atomicSentence (h : H) : Sentence H :=
  ⟨2, emptyMem, ![Name.empty, Name.truthName h]⟩

theorem atomicSentence_value (h : H) : (atomicSentence h).value = h :=
  eval_emptyMem_truthName h

/-! ## The frame of perspectives -/

/-- The gunky pole: the regular open sets of Cantor space. -/
abbrev Gunk : Type :=
  Regular (Opens (ℕ → Bool))

/-- The frame of perspectives: the finite pole, the chain `[0, ∞]`, and the gunky pole. -/
abbrev Perspectives : Type :=
  Prop × (ℝ≥0∞ × Gunk)

theorem gunk_top_ne_bot : (⊤ : Gunk) ≠ ⊥ := by
  intro h
  have e : ((⊤ : Gunk) : Opens (ℕ → Bool)) = ((⊥ : Gunk) : Opens (ℕ → Bool)) := by rw [h]
  rw [Regular.coe_top, Regular.coe_bot] at e
  have hmem : (fun _ => true : ℕ → Bool) ∈ (⊤ : Opens (ℕ → Bool)) := trivial
  rw [e] at hmem
  exact hmem

theorem perspectives_compl (h : Perspectives) : hᶜ = (h.1ᶜ, (h.2.1ᶜ, h.2.2ᶜ)) :=
  rfl

theorem perspectives_compl_compl (h : Perspectives) :
    hᶜᶜ = (h.1ᶜᶜ, (h.2.1ᶜᶜ, h.2.2ᶜᶜ)) :=
  rfl

/-! ### Top against double negation -/

/-- **The double-negation part forgets what the top keeps.** -/
noncomputable def fiber_negNeg_top : NonTrivialFiber (viewNegNeg (H := Perspectives)) viewTop where
  left := atomicSentence ((⊥, (1, ⊥)) : Perspectives)
  right := atomicSentence ((⊥, (⊤, ⊥)) : Perspectives)
  sameShadow := by
    apply Regular.coe_injective
    show ((atomicSentence _).value)ᶜᶜ = ((atomicSentence _).value)ᶜᶜ
    rw [atomicSentence_value, atomicSentence_value, perspectives_compl_compl,
      perspectives_compl_compl, ennreal_compl_compl, ennreal_compl_compl,
      if_neg one_ne_zero, if_neg ENNReal.top_ne_zero]
  differentValue := by
    show (atomicSentence _).value ≠ (atomicSentence _).value
    rw [atomicSentence_value, atomicSentence_value]
    intro h
    exact ENNReal.one_ne_top (congrArg (fun x : Perspectives => x.2.1) h)

/-! ### Double negation against points -/

/-- The gunky pole embedded in the frame of perspectives. -/
def embedGunk (g : Gunk) : Perspectives :=
  (⊥, (⊥, g))

theorem embedGunk_inf (g g' : Gunk) : embedGunk (g ⊓ g') = embedGunk g ⊓ embedGunk g' := by
  show ((⊥ : Prop), ((⊥ : ℝ≥0∞), g ⊓ g')) = ((⊥ : Prop) ⊓ ⊥, ((⊥ : ℝ≥0∞) ⊓ ⊥, g ⊓ g'))
  rw [inf_idem, inf_idem]

theorem embedGunk_sSup (S : Set Gunk) : embedGunk (sSup S) = sSup (embedGunk '' S) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show (⊥ : Prop) = (sSup (embedGunk '' S)).1
    rw [Prod.fst_sSup]
    refine (sSup_eq_bot.mpr ?_).symm
    rintro _ ⟨_, ⟨g, _, rfl⟩, rfl⟩
    rfl
  · show (⊥ : ℝ≥0∞) = (sSup (embedGunk '' S)).2.1
    rw [Prod.snd_sSup, Prod.fst_sSup]
    refine (sSup_eq_bot.mpr ?_).symm
    rintro _ ⟨_, ⟨_, ⟨g, _, rfl⟩, rfl⟩, rfl⟩
    rfl
  · show sSup S = (sSup (embedGunk '' S)).2.2
    rw [Prod.snd_sSup, Prod.snd_sSup, Set.image_image, Set.image_image]
    simp only [embedGunk, Set.image_id']

/-- A point of the double-negation part of the perspectives that affirms the gunky pole
gives a point of the gunky pole. -/
def gunkPoint (q : Point (Regular Perspectives))
    (hq : q.holds (Regular.toRegular (embedGunk ⊤))) : Point Gunk where
  holds g := q.holds (Regular.toRegular (embedGunk g))
  holds_top := hq
  holds_inf g g' := by
    have e : Regular.toRegular (embedGunk (g ⊓ g')) =
        Regular.toRegular (embedGunk g) ⊓ Regular.toRegular (embedGunk g') := by
      rw [← toRegular_inf, embedGunk_inf]
      rfl
    exact (iff_of_eq (congrArg q.holds e)).trans (q.holds_inf _ _)
  holds_sSup S := by
    rw [embedGunk_sSup, toRegular_sSup, q.holds_sSup]
    constructor
    · rintro ⟨_, ⟨_, ⟨g, hg, rfl⟩, rfl⟩, h⟩
      exact ⟨g, hg, h⟩
    · rintro ⟨g, hg, h⟩
      exact ⟨_, ⟨embedGunk g, ⟨g, hg, rfl⟩, rfl⟩, h⟩

/-- **No point of the double-negation part affirms the gunky pole.** -/
theorem not_holds_gunkTop (q : Point (Regular Perspectives)) :
    ¬ q.holds (Regular.toRegular (embedGunk ⊤)) := fun hq =>
  cantorGunkyWitness.regularPointless.false (gunkPoint q hq)

theorem embedGunk_bot : embedGunk ⊥ = ⊥ :=
  rfl

/-- **The points forget what the double-negation part keeps.** -/
noncomputable def fiber_points_negNeg : NonTrivialFiber (viewPoints (H := Perspectives)) viewNegNeg where
  left := atomicSentence (embedGunk ⊥)
  right := atomicSentence (embedGunk ⊤)
  sameShadow := by
    funext q
    show q.holds (Regular.toRegular (atomicSentence _).value) =
      q.holds (Regular.toRegular (atomicSentence _).value)
    rw [atomicSentence_value, atomicSentence_value, embedGunk_bot]
    refine propext ⟨fun h => ?_, fun h => absurd h (not_holds_gunkTop q)⟩
    have hb : Regular.toRegular (⊥ : Perspectives) = ⊥ := by
      apply Regular.coe_injective
      rw [Regular.coe_toRegular, Regular.coe_bot, compl_bot, compl_top]
    rw [hb] at h
    exact absurd h q.not_holds_bot
  differentValue := by
    show Regular.toRegular (atomicSentence _).value ≠ Regular.toRegular (atomicSentence _).value
    rw [atomicSentence_value, atomicSentence_value]
    intro h
    have e : (⊥ : Gunk)ᶜᶜ = (⊤ : Gunk)ᶜᶜ :=
      congrArg (fun r : Regular Perspectives => ((r : Perspectives)).2.2) h
    simp only [compl_bot, compl_top] at e
    exact gunk_top_ne_bot e.symm

/-! ### Points against the ground -/

/-- An atom of the perspectives has nothing on the chain. -/
theorem atom_chain_eq_zero {a : Perspectives} (ha : IsAtom a) : a.2.1 = 0 := by
  by_contra h
  set e := a.2.1 with he
  have hm : min e 1 ≠ 0 := by
    rw [ne_eq, min_eq_iff]
    rintro (⟨h1, _⟩ | ⟨h1, _⟩)
    · exact h h1
    · exact one_ne_zero h1
  have hmt : min e 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  let c : Perspectives := (⊥, (min e 1 / 2, ⊥))
  have hc : c ≤ a :=
    ⟨bot_le, le_trans ENNReal.half_le_self (min_le_left _ _), bot_le⟩
  have hcne : c ≠ ⊥ := fun hc0 =>
    (ENNReal.half_pos hm).ne' (congrArg (fun x : Perspectives => x.2.1) hc0)
  have hca : c ≠ a := fun hca => by
    have : min e 1 / 2 = e := congrArg (fun x : Perspectives => x.2.1) hca
    exact absurd (this ▸ (ENNReal.half_lt_self hm hmt).trans_le (min_le_left _ _))
      (lt_irrefl _)
  exact hcne (ha.2 c (lt_of_le_of_ne hc hca))

/-- The finite pole's atom: the ground is present. -/
theorem isAtom_finitePole : IsAtom ((⊤, (⊥, ⊥)) : Perspectives) := by
  refine ⟨fun h => ?_, fun b hb => ?_⟩
  · have this : (⊤ : Prop) = ⊥ := congrArg Prod.fst h
    have h' : (⊤ : Prop) := trivial
    rw [this] at h'
    exact h'
  · obtain ⟨⟨_, h2, h3⟩, hne⟩ := lt_iff_le_and_ne.mp hb
    have hb1 : b.1 = ⊥ := by
      by_contra h1
      have : b.1 = ⊤ := propext ⟨fun _ => trivial, fun _ => by
        by_contra hn
        exact h1 (propext ⟨fun hb' => (hn hb').elim, False.elim⟩)⟩
      exact hne (Prod.ext this (Prod.ext (le_bot_iff.mp h2) (le_bot_iff.mp h3)))
    exact Prod.ext hb1 (Prod.ext (le_bot_iff.mp h2) (le_bot_iff.mp h3))

/-- The point of the perspectives that reads the chain as "positive". -/
noncomputable def chainPointOfFrame : Point Perspectives where
  holds h := positivePoint.holds h.2.1
  holds_top := positivePoint.holds_top
  holds_inf _ _ := positivePoint.holds_inf _ _
  holds_sSup S := by
    show positivePoint.holds (sSup S).2.1 ↔ _
    rw [Prod.snd_sSup, Prod.fst_sSup, Set.image_image, positivePoint.holds_sSup]
    constructor
    · rintro ⟨_, ⟨h, hh, rfl⟩, hp⟩
      exact ⟨h, hh, hp⟩
    · rintro ⟨h, hh, hp⟩
      exact ⟨h.2.1, ⟨h, hh, rfl⟩, hp⟩

/-- **The free point of the chain**, a point of the double-negation part of the perspectives. -/
noncomputable def chainPoint : Point (Regular Perspectives) :=
  densePoint chainPointOfFrame fun h => positivePoint_holds_compl_compl h.2.1

/-- The free point is not the point of any atom. -/
theorem chainPoint_ne_regularAtomPoint {a : Perspectives} (ha : IsAtom a) :
    chainPoint ≠ regularAtomPoint ha := by
  intro e
  have hchain : chainPoint.holds (Regular.toRegular ((⊥, (⊤, ⊥)) : Perspectives)) := by
    show 0 < ((⊥, (⊤, ⊥)) : Perspectives)ᶜᶜ.2.1
    rw [perspectives_compl_compl, ennreal_compl_compl, if_neg ENNReal.top_ne_zero]
    exact ENNReal.zero_lt_top
  rw [e] at hchain
  change a ≤ ((Regular.toRegular ((⊥, (⊤, ⊥)) : Perspectives)) : Perspectives) at hchain
  rw [Regular.coe_toRegular, atom_le_compl_compl_iff ha] at hchain
  apply ha.1
  exact Prod.ext (le_bot_iff.mp hchain.1)
    (Prod.ext (atom_chain_eq_zero ha) (le_bot_iff.mp hchain.2.2))

/-- **The ground forgets what the points keep.** -/
noncomputable def fiber_ground_points : NonTrivialFiber (viewGround (H := Perspectives)) viewPoints where
  left := atomicSentence ((⊥, (0, ⊥)) : Perspectives)
  right := atomicSentence ((⊥, (⊤, ⊥)) : Perspectives)
  sameShadow := by
    funext a
    apply propext
    show ZFHolds _ _ ↔ ZFHolds _ _
    rw [← Name.le_eval_iff_zfHolds a.2, ← Name.le_eval_iff_zfHolds a.2]
    show a.1 ≤ (atomicSentence _).value ↔ a.1 ≤ (atomicSentence _).value
    rw [atomicSentence_value, atomicSentence_value]
    have h0 := atom_chain_eq_zero a.2
    constructor
    · rintro ⟨h1, _, h3⟩
      exact ⟨h1, le_top, h3⟩
    · rintro ⟨h1, _, h3⟩
      exact ⟨h1, le_of_eq h0, h3⟩
  differentValue := by
    intro e
    have := congrFun e chainPoint
    change (0 < ((atomicSentence ((⊥, (0, ⊥)) : Perspectives)).value)ᶜᶜ.2.1) =
      (0 < ((atomicSentence ((⊥, (⊤, ⊥)) : Perspectives)).value)ᶜᶜ.2.1) at this
    rw [atomicSentence_value, atomicSentence_value, perspectives_compl_compl,
      perspectives_compl_compl, ennreal_compl_compl, ennreal_compl_compl, if_pos rfl,
      if_neg ENNReal.top_ne_zero] at this
    exact lt_irrefl (0 : ℝ≥0∞) (this ▸ ENNReal.zero_lt_top)

/-! ## The well-founded side -/

theorem toZFSet_empty : HSet.toZFSet (∅ : HSet.{u}) = ∅ := by
  rw [← HSet.ofZFSet_empty, HSet.toZFSet_ofZFSet]

theorem factors_hset_bubble : Factors (id : HSet.{u} → HSet.{u}) HSet.toZFSet :=
  ⟨HSet.toZFSet, fun _ => rfl⟩

/-- **The bubble forgets the Quine atom.** Its readout sends `Ω` and `∅` to the same set. -/
noncomputable def fiber_bubble_hset : NonTrivialFiber HSet.toZFSet (id : HSet.{u} → HSet.{u}) where
  left := HSet.quineAtom
  right := ∅
  sameShadow := HSet.toZFSet_quineAtom.trans toZFSet_empty.symm
  differentValue := fun h => HSet.empty_ne_quineAtom h.symm

/-- On the bubble the readout forgets nothing. -/
theorem bubble_readout_injective {x y : WellFoundedPart.{u}}
    (h : HSet.toZFSet x.1 = HSet.toZFSet y.1) : x = y :=
  HSet.wellFoundedPartEquivZFSet.injective h

/-- Two slices of `ZFSet`: the hereditarily finite sets, and all sets. -/
inductive Slice : Type where
  | hereditarilyFinite
  | all

/-- The sets of a slice. -/
def Slice.carrier : Slice → ZFSet.{u} → Prop
  | .hereditarilyFinite => fun x => x ∈ V_ ω
  | .all => fun _ => True

/-- The bubble reads a slice by its seven laws. -/
def bubbleView (s : Slice) : Prop :=
  BubbleLaws (fun x y : {x : ZFSet.{u} // Slice.carrier s x} => x.1 ∈ y.1)

/-- HOTG also asks for a closed universe holding the empty set. -/
def universeView (s : Slice) : Prop :=
  ∃ U : ZFSet.{u}, Slice.carrier s U ∧ (∅ : ZFSet.{u}) ∈ U ∧
    Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure.Closed U

/-- **The bubble's laws do not decide the universe commitment.** -/
noncomputable def fiber_bubble_hotg : NonTrivialFiber bubbleView.{u} universeView.{u} :=
  NonTrivialFiber.ofProp (a := Slice.all) (b := Slice.hereditarilyFinite)
    (propext ⟨fun _ => hereditarilyFinite_bubbleLaws, fun _ => zfSet_bubbleLaws⟩)
    (let ⟨U, h0, hU⟩ := exists_closed_universe.{u}; ⟨U, trivial, h0, hU⟩)
    (fun ⟨U, hU, h0, hc⟩ => no_closed_universe_in_hereditarilyFinite ⟨U, hU, h0, hc⟩)

/-! ## Non-factorization, as theorems -/

theorem not_factors_negNeg_top : ¬ Factors (viewNegNeg (H := Perspectives)) viewTop :=
  fiber_negNeg_top.not_factors

theorem not_factors_points_negNeg : ¬ Factors (viewPoints (H := Perspectives)) viewNegNeg :=
  fiber_points_negNeg.not_factors

theorem not_factors_ground_points : ¬ Factors (viewGround (H := Perspectives)) viewPoints :=
  fiber_ground_points.not_factors

theorem not_factors_bubble_hset : ¬ Factors HSet.toZFSet (id : HSet.{u} → HSet.{u}) :=
  fiber_bubble_hset.not_factors

theorem not_factors_bubble_hotg : ¬ Factors bubbleView.{u} universeView.{u} :=
  fiber_bubble_hotg.not_factors

end Mettapedia.SetTheory.CarveOuts
