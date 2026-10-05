import Mettapedia.GSLT.Causality.EventConcurrency

/-!
# Valuations of sites along swaps of independent events

A swap of two independent events (`EventConcurrency.Concurrency.Pair`) fires
the same two sites in the two orders, and its second route is cast to the
common target.  This module states once what every concurrency in the shared
trace core uses about such swaps.

* **Casting the end of a path** (`OccurrenceValuation.onPath_cast`): a
  valuation does not see a change of the name of the end of a path.
* **The two routes of a swap** (`Concurrency.onPath_route`,
  `Concurrency.onPath_swapped`): the grades of the two occurrences, in the two
  orders.
* **Site valuations** (`siteValuation`): an occurrence is graded by its site.
  Such a valuation is a property of the trace exactly when the grades of the
  two sites of every swap commute (`Concurrency.siteValuation_descends_iff`);
  in a commutative monoid it always is
  (`Concurrency.siteValuation_descends`).

The controls (`SiteValuationControls`): counting firings descends for the
token concurrency (`count_descends`, `tokenCount_descends`), and so does a word
of sites when every firing has the one site of its rule (`siteWord_descends`);
the ordered word of the tokens consumed does not
(`amountWord_not_descends`), because the swap of the firings on tokens `0` and
`1` exchanges two different letters.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Causality.OccurrenceHistory
open Mettapedia.GSLT.Causality.EventConcurrency

universe uSite uEvent

variable {theory : GSLT}

namespace OccurrenceHistory.OccurrenceValuation

/-- **A valuation does not see a change of the name of the end of a path.** -/
theorem onPath_cast {P : InteractionPresentation.{uSite, uEvent} theory} {A : Type*}
    [AddMonoid A] (v : OccurrenceValuation P A) {s t t' : theory.Term} (same : t = t')
    (p : OccurrencePath P s t) : v.onPath (same ▸ p) = v.onPath p := by
  cases same
  rfl

end OccurrenceHistory.OccurrenceValuation

/-- **A site valuation**: an occurrence is graded by its site. -/
def siteValuation (P : InteractionPresentation.{uSite, uEvent} theory) {A : Type*} [AddMonoid A]
    (grade : P.Site → A) : OccurrenceValuation P A where
  grade occurrence := grade occurrence.site

namespace EventConcurrency.Concurrency

variable {P : InteractionPresentation.{uSite, uEvent} theory} (C : Concurrency P)
  {A : Type*} [AddMonoid A]

/-- The value of a valuation on the first route of a swap. -/
theorem onPath_route (v : OccurrenceValuation P A) {s : theory.Term} (pair : C.Pair s) :
    v.onPath (pair.route C) =
      v.grade (occ pair.first) + (v.grade (occ (C.residual pair.independent)) + 0) :=
  rfl

/-- The value of a valuation on the second route of a swap: the second event,
then the residual of the first. -/
theorem onPath_swapped (v : OccurrenceValuation P A) {s : theory.Term} (pair : C.Pair s) :
    v.onPath (pair.swapped C) =
      v.grade (occ pair.second) + (v.grade (occ (C.residual (C.symm pair.independent))) + 0) := by
  unfold Pair.swapped
  rw [OccurrenceValuation.onPath_cast]
  rfl

/-- On a swap, a site valuation reads the two sites in the two orders. -/
theorem siteValuation_swap (grade : P.Site → A) {s : theory.Term} (pair : C.Pair s) :
    (siteValuation P grade).onPath (pair.route C) = grade pair.first.site + grade pair.second.site ∧
      (siteValuation P grade).onPath (pair.swapped C) =
        grade pair.second.site + grade pair.first.site := by
  rw [onPath_route, onPath_swapped]
  change grade pair.first.site + (grade (C.residual pair.independent).site + 0) = _ ∧
    grade pair.second.site + (grade (C.residual (C.symm pair.independent)).site + 0) = _
  rw [C.residual_site, C.residual_site, add_zero, add_zero]
  exact ⟨rfl, rfl⟩

/-- **A site valuation is a property of the trace exactly when the grades of
the two sites of every swap commute.** -/
theorem siteValuation_descends_iff (grade : P.Site → A) :
    Descends C.tiles (siteValuation P grade) ↔
      ∀ {s : theory.Term} (pair : C.Pair s),
        AddCommute (grade pair.first.site) (grade pair.second.site) := by
  rw [descends_iff_tiles]
  constructor
  · intro descends _ pair
    have same : (siteValuation P grade).onPath (pair.route C) =
        (siteValuation P grade).onPath (pair.swapped C) := descends pair
    rw [(C.siteValuation_swap grade pair).1, (C.siteValuation_swap grade pair).2] at same
    exact same
  · intro commute _ pair
    change (siteValuation P grade).onPath (pair.route C) =
      (siteValuation P grade).onPath (pair.swapped C)
    rw [(C.siteValuation_swap grade pair).1, (C.siteValuation_swap grade pair).2]
    exact commute pair

/-- **In a commutative monoid every site valuation is a property of the
trace.** -/
theorem siteValuation_descends {A : Type*} [AddCommMonoid A] (grade : P.Site → A) :
    Descends C.tiles (siteValuation P grade) :=
  (C.siteValuation_descends_iff grade).2 fun _ => AddCommute.all _ _

end EventConcurrency.Concurrency

/-! ## Controls -/

namespace SiteValuationControls

open Mettapedia.GSLT.Causality.Mazurkiewicz (SiteWord)
open Mettapedia.GSLT.Causality.EventConcurrency.Tokens

/-- **Positive**: counting firings descends for the token concurrency. -/
theorem count_descends :
    Descends concurrency.tiles (siteValuation presentation fun _ => (1 : ℕ)) :=
  concurrency.siteValuation_descends _

/-- The ordered word of the sites fired.  Every firing of the one rule has the
same site, so this word only counts. -/
def siteWord : OccurrenceValuation presentation (SiteWord Unit) :=
  siteValuation presentation fun site => ⟨[site]⟩

/-- A site word of one rule descends: its two letters are equal. -/
theorem siteWord_descends : Descends concurrency.tiles siteWord :=
  (concurrency.siteValuation_descends_iff _).2 fun _ => by
    change (⟨[()]⟩ : SiteWord Unit) + ⟨[()]⟩ = ⟨[()]⟩ + ⟨[()]⟩
    rfl

/-- The token presentation with the consumed token as the site of a firing. -/
def tokenPresentation : InteractionPresentation tokenTheory where
  Site := ℕ
  Event i s t := PLift (i ∈ s ∧ t = s.erase i)
  sound event := ⟨_, event.down.1, event.down.2⟩

/-- Consume token `i`, with `i` as the site. -/
def consumeToken (s : Finset ℕ) (i : ℕ) (member : i ∈ s) : tokenPresentation.Enabled s where
  site := i
  target := s.erase i
  evidence := ⟨member, rfl⟩

/-- Firings on different tokens are independent. -/
def tokenConcurrency : Concurrency tokenPresentation where
  Independent a b := a.site ≠ b.site
  symm h := Ne.symm h
  residual {s a b} h := consumeToken a.target b.site (by
    rw [a.evidence.down.2]
    exact Finset.mem_erase.mpr ⟨Ne.symm h, b.evidence.down.1⟩)
  residual_site _ := rfl
  close {s a b} h := by
    change a.target.erase b.site = b.target.erase a.site
    rw [a.evidence.down.2, b.evidence.down.2]
    exact Finset.erase_right_comm

/-- The firings on tokens `0` and `1` of `{0, 1}`. -/
def tokenPair : tokenConcurrency.Pair ({0, 1} : Finset ℕ) where
  first := consumeToken {0, 1} 0 (by decide)
  second := consumeToken {0, 1} 1 (by decide)
  independent := by change (0 : ℕ) ≠ 1; decide

/-- The ordered word of the tokens consumed. -/
def amountWord : OccurrenceValuation tokenPresentation (SiteWord ℕ) :=
  siteValuation tokenPresentation fun site => ⟨[site]⟩

/-- **Negative**: the ordered word of the tokens consumed is not a property of
the trace: the swap of the firings on tokens `0` and `1` exchanges two
different letters. -/
theorem amountWord_not_descends : ¬ Descends tokenConcurrency.tiles amountWord := by
  intro descends
  have commute := (tokenConcurrency.siteValuation_descends_iff _).1 descends tokenPair
  have words := congrArg SiteWord.toList commute.eq
  change [0, 1] = [1, 0] at words
  cases words

/-- The commutative count of the same firings descends. -/
theorem tokenCount_descends :
    Descends tokenConcurrency.tiles (siteValuation tokenPresentation fun _ => (1 : ℕ)) :=
  tokenConcurrency.siteValuation_descends _

end SiteValuationControls

end Mettapedia.GSLT.Causality
