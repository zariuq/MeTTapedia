/-
# The combinators are a soup presentation

`GSLT/Logic/SoupPresentation.lean` proves, once and for an arbitrary carrier,
that structural congruence is equality of component bags. This file exhibits the
combinator calculus as an instance, which does two things.

It checks the abstraction against a carrier that was developed independently:
the generic soundness and completeness theorems specialize to `cong_components`
and `cong_of_components`, which were proved here directly, so the generic
statement is neither weaker nor differently scoped.

And it records what a carrier has to earn. The only substantive field is
`decomposes` — that a term is congruent to the parallel composition of its own
components — which for `Comb` is `cong_ofList`, proved by structural induction
over the fifteen constructors. Everything else the abstraction hands back.

The congruence relations have to be identified first: `Comb`'s `Cong` is its own
inductive, and the generic `Cong` is parameterized by unit and composition.
`cong_iff_soupCong` proves them the same relation, constructor for constructor.
This is the part that would fail if the mechanized congruence were closed under
atom arguments as well as parallel composition, so it also pins down which
relation the abstraction is about.
-/
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.NormalForm
import Mettapedia.GSLT.Logic.SoupPresentation

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb
open Mettapedia.GSLT.SoupPresentation (Soup)

/-- The generic congruence at the combinator carrier. -/
abbrev SoupCong : Comb → Comb → Prop :=
  Mettapedia.GSLT.SoupPresentation.Cong nil par

/-- **The two congruences are the same relation.**  Constructor for constructor:
the mechanized congruence of this calculus is the commutative-monoid congruence
on parallel composition, and nothing more. -/
theorem cong_iff_soupCong {p q : Comb} : Cong p q ↔ SoupCong p q := by
  constructor
  · intro h
    induction h with
    | refl p => exact .refl p
    | symm _ ih => exact .symm ih
    | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
    | parNil p => exact .compUnit p
    | parComm p q => exact .compComm p q
    | parAssoc p q r => exact .compAssoc p q r
    | parLeft q _ ih => exact .compLeft q ih
    | parRight p _ ih => exact .compRight p ih
  · intro h
    induction h with
    | refl p => exact Cong.refl p
    | symm _ ih => exact Cong.symm ih
    | trans _ _ ih₁ ih₂ => exact Cong.trans ih₁ ih₂
    | compUnit p => exact Cong.parNil p
    | compComm p q => exact Cong.parComm p q
    | compAssoc p q r => exact Cong.parAssoc p q r
    | compLeft q _ ih => exact Cong.parLeft q ih
    | compRight p _ ih => exact Cong.parRight p ih

/-- Recomposition agrees with this calculus's own `ofList`. -/
theorem soupOfList_eq_ofList :
    ∀ l : List Comb, Mettapedia.GSLT.SoupPresentation.ofList nil par l = ofList l
  | [] => rfl
  | _ :: rest => congrArg _ (soupOfList_eq_ofList rest)

/-- **The combinator calculus as a soup presentation.**  The only field it has
to earn is `decomposes`. -/
def combSoup : Soup where
  Term := Comb
  unit := nil
  comp := par
  componentList := componentList
  componentList_unit := rfl
  componentList_comp := fun _ _ => rfl
  decomposes := fun t => by
    rw [soupOfList_eq_ofList]
    exact cong_iff_soupCong.mp (cong_ofList t)

/-! ## The abstraction returns what was proved directly -/

/-- The generic component bag is this calculus's. -/
theorem combSoup_components (t : Comb) : combSoup.components t = components t := by
  simp only [Soup.components, combSoup, components_eq_coe]

/-- The generic soundness theorem specializes to `cong_components`. -/
theorem cong_components_via_soup {p q : Comb} (h : Cong p q) :
    components p = components q := by
  rw [← combSoup_components, ← combSoup_components]
  exact combSoup.cong_components (cong_iff_soupCong.mp h)

/-- The generic completeness theorem specializes to `cong_of_components`. -/
theorem cong_of_components_via_soup {p q : Comb} (h : components p = components q) :
    Cong p q := by
  refine cong_iff_soupCong.mpr (combSoup.cong_of_components ?_)
  rw [combSoup_components, combSoup_components]
  exact h

/-- **The soup theorem at this carrier**, as the abstraction delivers it. -/
theorem cong_iff_components_via_soup (p q : Comb) :
    Cong p q ↔ components p = components q :=
  ⟨cong_components_via_soup, cong_of_components_via_soup⟩

/-- Decidability of name equivalence is also generic: it needs only decidable
equality on the carrier. -/
def decidableCong_via_soup (p q : Comb) : Decidable (Cong p q) :=
  decidable_of_iff _ (cong_iff_components_via_soup p q).symm

end Mettapedia.Languages.ProcessCalculi.RhoCombinators
