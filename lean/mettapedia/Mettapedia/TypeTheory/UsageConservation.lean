import Mettapedia.TypeTheory.UsageOwnedLent
import Mettapedia.TypeTheory.BubbleBetaConfluence

/-!
# Owned hypotheses are conserved by computation

`UsageOwnedLent.owned` counts the uses of a variable by a term, and `beta_owned_once` says that a
β step at the root keeps every count when the bound variable is used exactly once. This module
makes the discipline a property of terms and proves that computation keeps it.

* `Owned e`: every abstraction in `e` uses its bound variable exactly once. Products and
  quantifiers bind for types and are not constrained.
* `owned_substAt_term`: the property is kept by instantiation with a term that has it.
* `beta_conserves`: a β step at any position of a term with the property gives a term with the
  property, and no use of any variable is gained or lost.
* `beta_conserves_star`: the same along any number of steps.
* `typed_beta_conserves`: in the bubble of β, a typed term with the property keeps its type, the
  property and every count along any computation.

The property is defined on terms. Modes on the hypotheses of a context, with the judgment that
reads them, are not defined here.

## Controls

* `Controls.identity_owned`: the identity has the property.
* `Controls.reads_twice_not_owned`: the abstraction `λ x. x ≐ x` does not, and its β step changes
  the counts (`UsageOwnedLent.Controls.read_twice_doubles`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.UsageConservation

open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.BubbleTypingInside
open Mettapedia.TypeTheory.BubbleBetaTyping
open Mettapedia.TypeTheory.BubbleTypingAdmission
open Mettapedia.TypeTheory.BubbleBetaConfluence
open Mettapedia.TypeTheory.KnowledgeSubstitution
open Mettapedia.TypeTheory.UsageOwnedLent
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Expr

universe u v

section Core

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Every abstraction uses its bound variable exactly once. -/
def Owned : Expr Base Const → Prop
  | .bvar _ => True
  | .univ => True
  | .prop => True
  | .base _ => True
  | .pi A B => Owned A ∧ Owned B
  | .lam A b => Owned A ∧ Owned b ∧ owned 0 b = 1
  | .app f a => Owned f ∧ Owned a
  | .const _ _ => True
  | .tyFam _ => True
  | .top => True
  | .bot => True
  | .and p q => Owned p ∧ Owned q
  | .or p q => Owned p ∧ Owned q
  | .imp p q => Owned p ∧ Owned q
  | .not p => Owned p
  | .eq a b => Owned a ∧ Owned b
  | .all A b => Owned A ∧ Owned b
  | .ex A b => Owned A ∧ Owned b

/-- The property is kept by a shift. -/
theorem owned_shiftAt_term : ∀ (e : Expr Base Const) (c : Nat), Owned e → Owned (shiftAt c e)
  | .bvar i, c, _ => by
      by_cases under : i < c
      · rw [shiftAt_bvar_lt under]
        exact True.intro
      · rw [shiftAt_bvar_ge under]
        exact True.intro
  | .univ, _, _ => True.intro
  | .prop, _, _ => True.intro
  | .base _, _, _ => True.intro
  | .pi A B, c, h => by
      obtain ⟨hA, hB⟩ : Owned A ∧ Owned B := h
      show Owned (shiftAt c A) ∧ Owned (shiftAt (c + 1) B)
      exact ⟨owned_shiftAt_term A c hA, owned_shiftAt_term B (c + 1) hB⟩
  | .lam A b, c, h => by
      obtain ⟨hA, hb, once⟩ : Owned A ∧ Owned b ∧ owned 0 b = 1 := h
      show Owned (shiftAt c A) ∧ Owned (shiftAt (c + 1) b) ∧ owned 0 (shiftAt (c + 1) b) = 1
      exact ⟨owned_shiftAt_term A c hA, owned_shiftAt_term b (c + 1) hb,
        (owned_shiftAt_lt b 0 (c + 1) (Nat.succ_pos c)).trans once⟩
  | .app f a, c, h => by
      obtain ⟨hf, ha⟩ : Owned f ∧ Owned a := h
      show Owned (shiftAt c f) ∧ Owned (shiftAt c a)
      exact ⟨owned_shiftAt_term f c hf, owned_shiftAt_term a c ha⟩
  | .const _ _, _, _ => True.intro
  | .tyFam _, _, _ => True.intro
  | .top, _, _ => True.intro
  | .bot, _, _ => True.intro
  | .and p q, c, h => by
      obtain ⟨hp, hq⟩ : Owned p ∧ Owned q := h
      show Owned (shiftAt c p) ∧ Owned (shiftAt c q)
      exact ⟨owned_shiftAt_term p c hp, owned_shiftAt_term q c hq⟩
  | .or p q, c, h => by
      obtain ⟨hp, hq⟩ : Owned p ∧ Owned q := h
      show Owned (shiftAt c p) ∧ Owned (shiftAt c q)
      exact ⟨owned_shiftAt_term p c hp, owned_shiftAt_term q c hq⟩
  | .imp p q, c, h => by
      obtain ⟨hp, hq⟩ : Owned p ∧ Owned q := h
      show Owned (shiftAt c p) ∧ Owned (shiftAt c q)
      exact ⟨owned_shiftAt_term p c hp, owned_shiftAt_term q c hq⟩
  | .not p, c, h => by
      show Owned (shiftAt c p)
      exact owned_shiftAt_term p c h
  | .eq a b, c, h => by
      obtain ⟨ha, hb⟩ : Owned a ∧ Owned b := h
      show Owned (shiftAt c a) ∧ Owned (shiftAt c b)
      exact ⟨owned_shiftAt_term a c ha, owned_shiftAt_term b c hb⟩
  | .all A b, c, h => by
      obtain ⟨hA, hb⟩ : Owned A ∧ Owned b := h
      show Owned (shiftAt c A) ∧ Owned (shiftAt (c + 1) b)
      exact ⟨owned_shiftAt_term A c hA, owned_shiftAt_term b (c + 1) hb⟩
  | .ex A b, c, h => by
      obtain ⟨hA, hb⟩ : Owned A ∧ Owned b := h
      show Owned (shiftAt c A) ∧ Owned (shiftAt (c + 1) b)
      exact ⟨owned_shiftAt_term A c hA, owned_shiftAt_term b (c + 1) hb⟩

theorem owned_shiftN_term {s : Expr Base Const} (hs : Owned s) : ∀ count : Nat,
    Owned (shiftN count s)
  | 0 => hs
  | count + 1 => owned_shiftAt_term (shiftN count s) 0 (owned_shiftN_term hs count)

/-- **The property is kept by instantiation** with a term that has it. -/
theorem owned_substAt_term {s : Expr Base Const} (hs : Owned s) :
    ∀ (e : Expr Base Const) (k : Nat), Owned e → Owned (substAt k s e)
  | .bvar i, k, _ => by
      rcases Nat.lt_trichotomy i k with under | same | above
      · rw [substAt_bvar_lt s under]
        exact True.intro
      · subst same
        rw [substAt_bvar_eq]
        exact owned_shiftN_term hs i
      · rw [substAt_bvar_gt s above]
        exact True.intro
  | .univ, _, _ => True.intro
  | .prop, _, _ => True.intro
  | .base _, _, _ => True.intro
  | .pi A B, k, h => by
      obtain ⟨hA, hB⟩ : Owned A ∧ Owned B := h
      show Owned (substAt k s A) ∧ Owned (substAt (k + 1) s B)
      exact ⟨owned_substAt_term hs A k hA, owned_substAt_term hs B (k + 1) hB⟩
  | .lam A b, k, h => by
      obtain ⟨hA, hb, once⟩ : Owned A ∧ Owned b ∧ owned 0 b = 1 := h
      show Owned (substAt k s A) ∧ Owned (substAt (k + 1) s b) ∧
        owned 0 (substAt (k + 1) s b) = 1
      exact ⟨owned_substAt_term hs A k hA, owned_substAt_term hs b (k + 1) hb,
        (owned_substAt_lt s b 0 (k + 1) (Nat.succ_pos k)).trans once⟩
  | .app f a, k, h => by
      obtain ⟨hf, ha⟩ : Owned f ∧ Owned a := h
      show Owned (substAt k s f) ∧ Owned (substAt k s a)
      exact ⟨owned_substAt_term hs f k hf, owned_substAt_term hs a k ha⟩
  | .const _ _, _, _ => True.intro
  | .tyFam _, _, _ => True.intro
  | .top, _, _ => True.intro
  | .bot, _, _ => True.intro
  | .and p q, k, h => by
      obtain ⟨hp, hq⟩ : Owned p ∧ Owned q := h
      show Owned (substAt k s p) ∧ Owned (substAt k s q)
      exact ⟨owned_substAt_term hs p k hp, owned_substAt_term hs q k hq⟩
  | .or p q, k, h => by
      obtain ⟨hp, hq⟩ : Owned p ∧ Owned q := h
      show Owned (substAt k s p) ∧ Owned (substAt k s q)
      exact ⟨owned_substAt_term hs p k hp, owned_substAt_term hs q k hq⟩
  | .imp p q, k, h => by
      obtain ⟨hp, hq⟩ : Owned p ∧ Owned q := h
      show Owned (substAt k s p) ∧ Owned (substAt k s q)
      exact ⟨owned_substAt_term hs p k hp, owned_substAt_term hs q k hq⟩
  | .not p, k, h => by
      show Owned (substAt k s p)
      exact owned_substAt_term hs p k h
  | .eq a b, k, h => by
      obtain ⟨ha, hb⟩ : Owned a ∧ Owned b := h
      show Owned (substAt k s a) ∧ Owned (substAt k s b)
      exact ⟨owned_substAt_term hs a k ha, owned_substAt_term hs b k hb⟩
  | .all A b, k, h => by
      obtain ⟨hA, hb⟩ : Owned A ∧ Owned b := h
      show Owned (substAt k s A) ∧ Owned (substAt (k + 1) s b)
      exact ⟨owned_substAt_term hs A k hA, owned_substAt_term hs b (k + 1) hb⟩
  | .ex A b, k, h => by
      obtain ⟨hA, hb⟩ : Owned A ∧ Owned b := h
      show Owned (substAt k s A) ∧ Owned (substAt (k + 1) s b)
      exact ⟨owned_substAt_term hs A k hA, owned_substAt_term hs b (k + 1) hb⟩

/-- **A β step conserves owned hypotheses.** At any position of a term all of whose abstractions
use their variable once, the step gives such a term, and no use of any variable is gained or
lost. -/
theorem beta_conserves {e e' : Expr Base Const} (step : Rewrite Beta e e') :
    Owned e → Owned e' ∧ ∀ i : Nat, owned i e' = owned i e := by
  induction step with
  | root rule =>
      cases rule with
      | contract A b a =>
          intro h
          obtain ⟨⟨_, hb, once⟩, ha⟩ : (Owned A ∧ Owned b ∧ owned 0 b = 1) ∧ Owned a := h
          exact ⟨owned_substAt_term ha b 0 hb, beta_owned_once A a once⟩
  | piDomain _ ih =>
      intro h
      obtain ⟨hA, hB⟩ : Owned _ ∧ Owned _ := h
      obtain ⟨hA', same⟩ := ih hA
      refine ⟨show Owned _ ∧ Owned _ from ⟨hA', hB⟩, fun i => ?_⟩
      show owned i _ + owned (i + 1) _ = owned i _ + owned (i + 1) _
      rw [same i]
  | piBody _ ih =>
      intro h
      obtain ⟨hA, hB⟩ : Owned _ ∧ Owned _ := h
      obtain ⟨hB', same⟩ := ih hB
      refine ⟨show Owned _ ∧ Owned _ from ⟨hA, hB'⟩, fun i => ?_⟩
      show owned i _ + owned (i + 1) _ = owned i _ + owned (i + 1) _
      rw [same (i + 1)]
  | lamDomain _ ih =>
      intro h
      obtain ⟨hA, hb, once⟩ : Owned _ ∧ Owned _ ∧ owned 0 _ = 1 := h
      obtain ⟨hA', _⟩ := ih hA
      exact ⟨show Owned _ ∧ Owned _ ∧ owned 0 _ = 1 from ⟨hA', hb, once⟩, fun _ => rfl⟩
  | lamBody _ ih =>
      intro h
      obtain ⟨hA, hb, once⟩ : Owned _ ∧ Owned _ ∧ owned 0 _ = 1 := h
      obtain ⟨hb', same⟩ := ih hb
      refine ⟨show Owned _ ∧ Owned _ ∧ owned 0 _ = 1 from ⟨hA, hb', (same 0).trans once⟩,
        fun i => ?_⟩
      show owned (i + 1) _ = owned (i + 1) _
      rw [same (i + 1)]
  | appFunction _ ih =>
      intro h
      obtain ⟨hf, ha⟩ : Owned _ ∧ Owned _ := h
      obtain ⟨hf', same⟩ := ih hf
      refine ⟨show Owned _ ∧ Owned _ from ⟨hf', ha⟩, fun i => ?_⟩
      show owned i _ + owned i _ = owned i _ + owned i _
      rw [same i]
  | appArgument _ ih =>
      intro h
      obtain ⟨hf, ha⟩ : Owned _ ∧ Owned _ := h
      obtain ⟨ha', same⟩ := ih ha
      refine ⟨show Owned _ ∧ Owned _ from ⟨hf, ha'⟩, fun i => ?_⟩
      show owned i _ + owned i _ = owned i _ + owned i _
      rw [same i]
  | andLeft _ ih =>
      intro h
      obtain ⟨hp, hq⟩ : Owned _ ∧ Owned _ := h
      obtain ⟨hp', same⟩ := ih hp
      refine ⟨show Owned _ ∧ Owned _ from ⟨hp', hq⟩, fun i => ?_⟩
      show owned i _ + owned i _ = owned i _ + owned i _
      rw [same i]
  | andRight _ ih =>
      intro h
      obtain ⟨hp, hq⟩ : Owned _ ∧ Owned _ := h
      obtain ⟨hq', same⟩ := ih hq
      refine ⟨show Owned _ ∧ Owned _ from ⟨hp, hq'⟩, fun i => ?_⟩
      show owned i _ + owned i _ = owned i _ + owned i _
      rw [same i]
  | orLeft _ ih =>
      intro h
      obtain ⟨hp, hq⟩ : Owned _ ∧ Owned _ := h
      obtain ⟨hp', same⟩ := ih hp
      refine ⟨show Owned _ ∧ Owned _ from ⟨hp', hq⟩, fun i => ?_⟩
      show owned i _ + owned i _ = owned i _ + owned i _
      rw [same i]
  | orRight _ ih =>
      intro h
      obtain ⟨hp, hq⟩ : Owned _ ∧ Owned _ := h
      obtain ⟨hq', same⟩ := ih hq
      refine ⟨show Owned _ ∧ Owned _ from ⟨hp, hq'⟩, fun i => ?_⟩
      show owned i _ + owned i _ = owned i _ + owned i _
      rw [same i]
  | impLeft _ ih =>
      intro h
      obtain ⟨hp, hq⟩ : Owned _ ∧ Owned _ := h
      obtain ⟨hp', same⟩ := ih hp
      refine ⟨show Owned _ ∧ Owned _ from ⟨hp', hq⟩, fun i => ?_⟩
      show owned i _ + owned i _ = owned i _ + owned i _
      rw [same i]
  | impRight _ ih =>
      intro h
      obtain ⟨hp, hq⟩ : Owned _ ∧ Owned _ := h
      obtain ⟨hq', same⟩ := ih hq
      refine ⟨show Owned _ ∧ Owned _ from ⟨hp, hq'⟩, fun i => ?_⟩
      show owned i _ + owned i _ = owned i _ + owned i _
      rw [same i]
  | notBody _ ih =>
      intro h
      obtain ⟨hp', same⟩ := ih (show Owned _ from h)
      exact ⟨show Owned _ from hp', fun i => same i⟩
  | eqLeft _ ih =>
      intro h
      obtain ⟨ha, hb⟩ : Owned _ ∧ Owned _ := h
      obtain ⟨ha', same⟩ := ih ha
      refine ⟨show Owned _ ∧ Owned _ from ⟨ha', hb⟩, fun i => ?_⟩
      show owned i _ + owned i _ = owned i _ + owned i _
      rw [same i]
  | eqRight _ ih =>
      intro h
      obtain ⟨ha, hb⟩ : Owned _ ∧ Owned _ := h
      obtain ⟨hb', same⟩ := ih hb
      refine ⟨show Owned _ ∧ Owned _ from ⟨ha, hb'⟩, fun i => ?_⟩
      show owned i _ + owned i _ = owned i _ + owned i _
      rw [same i]
  | allDomain _ ih =>
      intro h
      obtain ⟨hA, hb⟩ : Owned _ ∧ Owned _ := h
      obtain ⟨hA', same⟩ := ih hA
      refine ⟨show Owned _ ∧ Owned _ from ⟨hA', hb⟩, fun i => ?_⟩
      show owned i _ + owned (i + 1) _ = owned i _ + owned (i + 1) _
      rw [same i]
  | allBody _ ih =>
      intro h
      obtain ⟨hA, hb⟩ : Owned _ ∧ Owned _ := h
      obtain ⟨hb', same⟩ := ih hb
      refine ⟨show Owned _ ∧ Owned _ from ⟨hA, hb'⟩, fun i => ?_⟩
      show owned i _ + owned (i + 1) _ = owned i _ + owned (i + 1) _
      rw [same (i + 1)]
  | exDomain _ ih =>
      intro h
      obtain ⟨hA, hb⟩ : Owned _ ∧ Owned _ := h
      obtain ⟨hA', same⟩ := ih hA
      refine ⟨show Owned _ ∧ Owned _ from ⟨hA', hb⟩, fun i => ?_⟩
      show owned i _ + owned (i + 1) _ = owned i _ + owned (i + 1) _
      rw [same i]
  | exBody _ ih =>
      intro h
      obtain ⟨hA, hb⟩ : Owned _ ∧ Owned _ := h
      obtain ⟨hb', same⟩ := ih hb
      refine ⟨show Owned _ ∧ Owned _ from ⟨hA, hb'⟩, fun i => ?_⟩
      show owned i _ + owned (i + 1) _ = owned i _ + owned (i + 1) _
      rw [same (i + 1)]

/-- **Any computation conserves owned hypotheses.** -/
theorem beta_conserves_star {e e' : Expr Base Const}
    (reduced : Relation.ReflTransGen (Rewrite Beta) e e') (h : Owned e) :
    Owned e' ∧ ∀ i : Nat, owned i e' = owned i e := by
  induction reduced with
  | refl => exact ⟨h, fun _ => rfl⟩
  | tail _ step ih =>
      obtain ⟨middle, same⟩ := ih
      obtain ⟨last, more⟩ := beta_conserves step middle
      exact ⟨last, fun i => (more i).trans (same i)⟩

/-- **In the bubble of β, a typed term with owned hypotheses keeps its type, the property and
every count along any computation.** -/
theorem typed_beta_conserves {Γ : List (Expr Base Const)} {e e' A : Expr Base Const}
    (typed : HasTypeInside Beta Γ e A) (h : Owned e)
    (reduced : Relation.ReflTransGen (Rewrite Beta) e e') :
    HasTypeInside Beta Γ e' A ∧ Owned e' ∧ ∀ i : Nat, owned i e' = owned i e :=
  ⟨beta_admitted.reduces typed reduced, beta_conserves_star reduced h⟩

end Core

/-! ## Controls -/

namespace Controls

open Mettapedia.TypeTheory.BubbleConversion.Arith
open Mettapedia.TypeTheory.UsageOwnedLent.Controls

/-- The identity uses its bound variable once. -/
theorem identity_owned : Owned (Expr.lam natType (bvar 0) : AExpr) :=
  ⟨True.intro, True.intro, rfl⟩

/-- **The abstraction `λ x. x ≐ x` does not have the property**: it uses its variable twice. -/
theorem reads_twice_not_owned : ¬ Owned (Expr.lam natType readsTwice : AExpr) := by
  intro h
  obtain ⟨_, _, once⟩ : Owned natType ∧ Owned readsTwice ∧ owned 0 readsTwice = 1 := h
  exact absurd once (by decide)

end Controls

/-! ## Axiom audit -/

#print axioms owned_substAt_term
#print axioms beta_conserves
#print axioms beta_conserves_star
#print axioms typed_beta_conserves
#print axioms Controls.identity_owned
#print axioms Controls.reads_twice_not_owned

end Mettapedia.TypeTheory.UsageConservation
