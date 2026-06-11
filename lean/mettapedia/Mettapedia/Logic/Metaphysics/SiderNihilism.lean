import Mettapedia.Logic.GunkyMereology

/-!
# Sider's argument against mereological nihilism (formal philosophy)

Theodore Sider (*Van Inwagen and the Possibility of Gunk*, Analysis 1993) argues against
**mereological nihilism** — the thesis that there are no composite objects, that every
object is a mereological *simple* — using the mere possibility of *gunk* (atomless
parthood). His argument:

1. Nihilism is necessarily true or necessarily false (it is non-contingent).
2. Gunk is metaphysically possible.
3. If gunk is possible, nihilism is not necessarily true.
4. Therefore nihilism is necessarily false.

We formalize this with the standard semantic reading of metaphysical modality: a **world**
is a parthood structure (a bounded order), `□P := ∀ W, P W` and `◇P := ∃ W, P W` (the
universal / S5 frame). `SiderNihilism W` says *every object is a simple* (`∀ a ≠ ⊥, IsAtom a`);
`Gunky W` reuses `IsGunky` (atomless).

What the formalization shows, honestly:

* **The argument is valid**, and premises 2–3 are *theorems* here:
  `possible_gunk` (witnessed by the continuum) and `gunky_not_siderNihilism`
  (gunk ⟹ no simples). Hence `siders_argument : NonContingent SiderNihilism → □¬SiderNihilism`.
* **But premise 1 fails in the unrestricted logical space of mereologies**
  (`not_nonContingent_siderNihilism`): there is a gunky world *and* a nihilist world, so
  neither nihilism nor its negation is necessary. The argument is therefore sound only under
  the metaphysical posit that restricts the frame so that nihilism is non-contingent.

Tie-in to the Stone-duality development: a world is gunky iff its Stone space is *perfect*
(no isolated point — "no true separation"); a nihilist world sits at the opposite,
*discrete*-Stone pole. The two poles are both realized, which is exactly why premise 1 is not
a logical truth.
-/

namespace Mettapedia.Logic.Metaphysics

open Mettapedia.Foundations.Gunk
open scoped NNReal

/-- A **mereology** (a metaphysically possible parthood structure / "world"): a bounded order
on at least two individuals. `Nontrivial` excludes the degenerate one-element world, in which
gunk and nihilism would both hold vacuously. -/
structure Mereology : Type 1 where
  /-- The individuals of this world. -/
  carrier : Type
  [order : PartialOrder carrier]
  [orderBot : OrderBot carrier]
  [ntriv : Nontrivial carrier]

attribute [instance] Mereology.order Mereology.orderBot Mereology.ntriv

/-- A world is **gunky** when its parthood is atomless: every individual is properly
divisible (reusing `IsGunky`). -/
def Gunky (W : Mereology) : Prop := IsGunky W.carrier

/-- **Sider's nihilism** at a world: every object is a mereological *simple* — a
non-bottom atom with no proper non-bottom parts. -/
def SiderNihilism (W : Mereology) : Prop := ∀ a : W.carrier, a ≠ ⊥ → IsAtom a

/-- Metaphysical necessity (`□`): true at every world (the universal / S5 frame). -/
def Nec (P : Mereology → Prop) : Prop := ∀ W, P W

/-- Metaphysical possibility (`◇`): true at some world. -/
def Pos (P : Mereology → Prop) : Prop := ∃ W, P W

/-- **The incompatibility (premise 3's content).** A gunky world is not a nihilist world:
gunk means *no* atoms, while nihilism requires every (non-bottom) object to be an atom. -/
theorem gunky_not_siderNihilism {W : Mereology} (hg : Gunky W) : ¬ SiderNihilism W := by
  intro hnih
  obtain ⟨a, ha⟩ : ∃ a : W.carrier, a ≠ ⊥ := by
    obtain ⟨x, y, hxy⟩ := exists_pair_ne W.carrier
    rcases eq_or_ne x ⊥ with hx | hx
    · exact ⟨y, fun hy => hxy (hx.trans hy.symm)⟩
    · exact ⟨x, hx⟩
  exact (isGunky_iff_no_isAtom.mp hg a) (hnih a ha)

/-! ## Witnesses: both poles are realized -/

/-- The continuum as a gunky world (the non-negative reals: every magnitude is halvable). -/
noncomputable def gunkyWorld : Mereology := { carrier := ℝ≥0 }

/-- **Premise 2.** Gunk is possible — witnessed by the continuum. -/
theorem possible_gunk : Pos Gunky := by
  refine ⟨gunkyWorld, ?_⟩
  show IsGunky ℝ≥0
  exact isGunky_nnreal

/-- A two-valued algebra as a nihilist world: a single simple `⊤` over the null `⊥`. -/
noncomputable def nihilistWorld : Mereology := { carrier := Bool }

/-- Nihilism is possible — witnessed by the two-element world. -/
theorem possible_nihilism : Pos SiderNihilism := by
  refine ⟨nihilistWorld, ?_⟩
  show ∀ a : Bool, a ≠ ⊥ → IsAtom a
  intro a ha
  cases a with
  | false => exact absurd rfl ha
  | true =>
    refine ⟨by decide, fun b hb => ?_⟩
    cases b with
    | false => rfl
    | true => exact absurd hb (lt_irrefl _)

/-! ## The argument, and where it really turns -/

/-- **Premise 3, derived.** If gunk is possible, nihilism is not necessary. -/
theorem pos_gunk_imp_not_nec_nihilism (h : Pos Gunky) : ¬ Nec SiderNihilism := by
  obtain ⟨W, hW⟩ := h
  intro hnec
  exact gunky_not_siderNihilism hW (hnec W)

/-- **Premise 1.** A proposition is *non-contingent* when it is necessary or its negation is. -/
def NonContingent (P : Mereology → Prop) : Prop := Nec P ∨ Nec (fun W => ¬ P W)

/-- **Sider's argument is valid.** Granting premise 1 (nihilism non-contingent), and with
premises 2–3 discharged as theorems, nihilism is necessarily false. -/
theorem siders_argument (h1 : NonContingent SiderNihilism) :
    Nec (fun W => ¬ SiderNihilism W) := by
  rcases h1 with hN | hnotN
  · exact absurd hN (pos_gunk_imp_not_nec_nihilism possible_gunk)
  · exact hnotN

/-- **Where the argument really turns.** In the unrestricted logical space of mereologies,
premise 1 is *false*: there is a gunky world (so nihilism is not necessary) and a nihilist
world (so its negation is not necessary either). Sider's argument is therefore valid but
*unsound* in the full frame; its soundness requires the metaphysical posit that restricts the
space of worlds so that nihilism becomes non-contingent. -/
theorem not_nonContingent_siderNihilism : ¬ NonContingent SiderNihilism := by
  rintro (hN | hnotN)
  · exact pos_gunk_imp_not_nec_nihilism possible_gunk hN
  · obtain ⟨W, hW⟩ := possible_nihilism
    exact hnotN W hW

/-- Corollary: nihilism is genuinely *contingent* across mereologies — true at some worlds
(e.g. `nihilistWorld`), false at others (e.g. `gunkyWorld`). It is neither necessary nor
impossible. -/
theorem siderNihilism_contingent :
    Pos SiderNihilism ∧ Pos (fun W => ¬ SiderNihilism W) := by
  refine ⟨possible_nihilism, gunkyWorld, ?_⟩
  exact gunky_not_siderNihilism (show IsGunky ℝ≥0 from isGunky_nnreal)

end Mettapedia.Logic.Metaphysics

