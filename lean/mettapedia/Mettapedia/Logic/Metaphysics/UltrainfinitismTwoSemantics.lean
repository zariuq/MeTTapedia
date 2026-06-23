import Mettapedia.Logic.Metaphysics.MonadicSecondOrder
import Mettapedia.Logic.GunkyMereology
import Mettapedia.Logic.StoneGunkDuality

/-!
# The ultrainfinitist theory is satisfiable under both standard and Henkin semantics

The monadic second-order theory `T_UI` — Boolean-algebra mereology with

* `gunkAx` : every non-bottom individual has a proper non-bottom part (atomlessness),
* `nontrivAx` : the world is nontrivial (`⊥ ≠ ⊤`),
* `freeUFAx` : **every ultrafilter is free** (no ultrafilter has a least element; no
  finitary, principal coordinate exists) — the genuinely second-order axiom,

is satisfiable under **standard (full)** semantics and under **Henkin** semantics, with
the *same* witness: the clopen algebra of Cantor space
(`T_UI_satisfiable_standard`, `T_UI_satisfiable_henkin`).

The bridge is the internalized Stone dictionary `sat_freeUFAx_iff_isGunky`: over standard
semantics, the second-order free-ultrafilter axiom is *equivalent* to first-order
atomlessness (`IsGunky`), because the principal ultrafilters of a Boolean algebra are
exactly the up-sets of its atoms (`isUltraSet_principalUp`, `isAtom_of_least`).

These are *satisfiability* (model-existence) theorems relative to Lean's metatheory;
no proof calculus is in scope and no proof-theoretic consistency claim is made.
-/

namespace Mettapedia.Logic.Metaphysics

open Mettapedia.Foundations.Gunk

universe u

variable {M : Type u} [BooleanAlgebra M]

/-! ## The sentences

Binder discipline: innermost bound variable = index `0`; all variable indices ≤ 1.
The lone second-order variable `X` is index `0`. Each encoding is immediately followed
by its semantic unfolding lemma. -/

/-- `X` is upward closed: `∀ a b, a ∈ X → a ≤ b → b ∈ X`. -/
def upwardFml : MSO 0 1 :=
  .allFO (.allFO (.imp (.mem (.fvar 1) 0) (.imp (.le (.fvar 1) (.fvar 0))
    (.mem (.fvar 0) 0))))

/-- `X` is closed under meets: `∀ a b, a ∈ X → b ∈ X → a ⊓ b ∈ X`. -/
def infMemFml : MSO 0 1 :=
  .allFO (.allFO (.imp (.mem (.fvar 1) 0) (.imp (.mem (.fvar 0) 0)
    (.mem (.inf (.fvar 1) (.fvar 0)) 0))))

/-- `X` is proper: `⊥ ∉ X`. -/
def properFml : MSO 0 1 := .not (.mem .bot 0)

/-- `X` is total (ultra): `∀ a, a ∈ X ∨ aᶜ ∈ X`. -/
def totalFml : MSO 0 1 :=
  .allFO (.or (.mem (.fvar 0) 0) (.mem (.compl (.fvar 0)) 0))

/-- `X` is an ultrafilter: upward closed, meet closed, proper, total. -/
def isUltrafilterFml : MSO 0 1 :=
  .and (.and upwardFml infMemFml) (.and properFml totalFml)

/-- `X` has a least element (is principal): `∃ m, m ∈ X ∧ ∀ b, b ∈ X → m ≤ b`. -/
def hasLeastFml : MSO 0 1 :=
  .exFO (.and (.mem (.fvar 0) 0)
    (.allFO (.imp (.mem (.fvar 0) 0) (.le (.fvar 1) (.fvar 0)))))

/-- **The free-ultrafilter axiom** (second order): every ultrafilter is free — no
ultrafilter has a least element. "The One has no finitary coordinate." -/
def freeUFAx : MSO 0 0 := .allSO (.imp isUltrafilterFml (.not hasLeastFml))

/-- **The gunk axiom** (first order): every non-bottom individual has a proper
non-bottom part. -/
def gunkAx : MSO 0 0 :=
  .allFO (.imp (.not (.eq (.fvar 0) .bot))
    (.exFO (.and (.not (.eq (.fvar 0) .bot))
      (.and (.le (.fvar 0) (.fvar 1)) (.not (.eq (.fvar 0) (.fvar 1)))))))

/-- Nontriviality: `⊥ ≠ ⊤`. -/
def nontrivAx : MSO 0 0 := .not (.eq .bot .top)

/-- The ultrainfinitist core theory. -/
def T_UI : Set (MSO 0 0) := {gunkAx, nontrivAx, freeUFAx}

/-- Satisfaction of a set of sentences over a quantifier domain `𝒮`. -/
def SatTheory (𝒮 : Set (Set M)) (T : Set (MSO 0 0)) : Prop :=
  ∀ φ ∈ T, SatSentence 𝒮 φ

/-! ## The semantic side -/

/-- An ultrafilter on a Boolean algebra, as a plain set of elements (bespoke clauses,
matching the four conjuncts of `isUltrafilterFml`). -/
structure IsUltraSet (F : Set M) : Prop where
  upward : ∀ a b : M, a ∈ F → a ≤ b → b ∈ F
  inf_mem : ∀ a b : M, a ∈ F → b ∈ F → a ⊓ b ∈ F
  proper : ⊥ ∉ F
  total : ∀ a : M, a ∈ F ∨ aᶜ ∈ F

/-- `F` has a least element (is a principal filter). -/
def HasLeast (F : Set M) : Prop := ∃ m, m ∈ F ∧ ∀ b, b ∈ F → m ≤ b

/-! ## Unfolding lemmas (syntax ⟷ semantics) -/

section Unfolding

variable {𝒮 : Set (Set M)} (vS : Fin 1 → Set M)

theorem sat_isUltrafilterFml_iff :
    Sat 𝒮 Fin.elim0 vS isUltrafilterFml ↔ IsUltraSet (vS 0) := by
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨fun a b => by simpa using h1 a b, fun a b => by simpa using h2 a b,
      by simpa [properFml] using h3, fun a => by simpa using h4 a⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨fun a b => by simpa using h1 a b, fun a b => by simpa using h2 a b⟩,
      by simpa [properFml] using h3, fun a => by simpa using h4 a⟩

theorem sat_hasLeastFml_iff :
    Sat 𝒮 Fin.elim0 vS hasLeastFml ↔ HasLeast (vS 0) := by
  constructor
  · rintro ⟨m, hm, hl⟩
    exact ⟨m, by simpa using hm, fun b hb => by simpa using hl b (by simpa using hb)⟩
  · rintro ⟨m, hm, hl⟩
    exact ⟨m, by simpa using hm, fun b hb => by simpa using hl b (by simpa using hb)⟩

theorem sat_gunkAx_iff_isGunky {𝒮 : Set (Set M)} :
    SatSentence 𝒮 gunkAx ↔ IsGunky M := by
  constructor
  · intro h a ha
    obtain ⟨b, hb, hba, hne⟩ := by simpa [SatSentence, gunkAx] using h a ha
    exact ⟨b, hb, lt_of_le_of_ne hba hne⟩
  · intro h a ha
    obtain ⟨b, hb, hba⟩ := h a (by simpa using ha)
    exact by simpa using ⟨b, hb, hba.le, hba.ne⟩

theorem sat_nontrivAx_iff {𝒮 : Set (Set M)} :
    SatSentence 𝒮 nontrivAx ↔ (⊥ : M) ≠ ⊤ := by
  simp [SatSentence, nontrivAx]

end Unfolding

/-! ## Bridge lemmas: principal ultrafilters are exactly atom up-sets -/

/-- The up-set of an atom is an ultrafilter. -/
theorem isUltraSet_principalUp {a : M} (h : IsAtom a) :
    IsUltraSet {b : M | a ≤ b} where
  upward _ _ hx hxy := le_trans hx hxy
  inf_mem _ _ hx hy := le_inf hx hy
  proper hbot := h.1 (le_bot_iff.mp hbot)
  total b := by
    rcases h.le_iff.mp (inf_le_left : a ⊓ b ≤ a) with hbot | heq
    · exact Or.inr (le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr hbot))
    · exact Or.inl (inf_eq_left.mp heq)

/-- The up-set of any element has a least element (itself). -/
theorem hasLeast_principalUp (a : M) : HasLeast {b : M | a ≤ b} :=
  ⟨a, le_refl a, fun _ hb => hb⟩

/-- The least element of an ultrafilter is an atom. -/
theorem isAtom_of_least {F : Set M} (hF : IsUltraSet F) {m : M}
    (hm : m ∈ F) (hleast : ∀ b ∈ F, m ≤ b) : IsAtom m := by
  refine ⟨fun hbot => hF.proper (hbot ▸ hm), fun b hb => ?_⟩
  rcases hF.total b with hmem | hmem
  · exact absurd (hleast b hmem) (not_le_of_gt hb)
  · exact le_compl_self.mp (le_trans hb.le (hleast _ hmem))

/-! ## The jewel: the second-order free-ultrafilter axiom IS atomlessness -/

/-- **Internalized Stone dictionary.** Over standard semantics, the second-order axiom
"every ultrafilter is free" holds iff the algebra is atomless (gunky): the principal
ultrafilters of a Boolean algebra are exactly the up-sets of its atoms. -/
theorem sat_freeUFAx_iff_isGunky :
    SatSentence (Set.univ : Set (Set M)) freeUFAx ↔ IsGunky M := by
  rw [isGunky_iff_no_isAtom]
  constructor
  · intro h a ha
    have := h {b : M | a ≤ b} (Set.mem_univ _)
    rw [sat_imp, sat_not, sat_isUltrafilterFml_iff, sat_hasLeastFml_iff] at this
    simp only [Fin.cons_zero] at this
    exact this (isUltraSet_principalUp ha) (hasLeast_principalUp a)
  · intro h X _
    rw [sat_imp, sat_not, sat_isUltrafilterFml_iff, sat_hasLeastFml_iff]
    simp only [Fin.cons_zero]
    rintro hX ⟨m, hm, hleast⟩
    exact h m (isAtom_of_least hX hm hleast)

/-! ## The witness world and the two headline theorems -/

open TopologicalSpace in
/-- A Boolean-algebra world (the bundled-world house pattern). -/
structure BAWorld : Type 1 where
  /-- The individuals. -/
  carrier : Type
  [ba : BooleanAlgebra carrier]

attribute [instance] BAWorld.ba

open TopologicalSpace in
/-- The Cantor witness: the clopen algebra of Cantor space. -/
noncomputable def cantorWorld : BAWorld := { carrier := Clopens (ℕ → Bool) }

open TopologicalSpace in
theorem cantorWorld_bot_ne_top :
    (⊥ : Clopens (ℕ → Bool)) ≠ ⊤ := by
  intro h
  have := congrArg (fun K : Clopens (ℕ → Bool) => (K : Set (ℕ → Bool))) h
  simp only [Clopens.coe_bot, Clopens.coe_top] at this
  exact Set.empty_ne_univ this

/-- **The ultrainfinitist theory is satisfiable under standard (full) semantics** —
witnessed by the clopen algebra of Cantor space. (Satisfiability = model existence,
relative to Lean's metatheory.) -/
theorem T_UI_satisfiable_standard :
    ∃ W : BAWorld, SatTheory (M := W.carrier) Set.univ T_UI := by
  refine ⟨cantorWorld, fun φ hφ => ?_⟩
  rcases hφ with h | h | h
  · exact h ▸ sat_gunkAx_iff_isGunky.mpr isGunky_clopens_cantor
  · exact h ▸ sat_nontrivAx_iff.mpr cantorWorld_bot_ne_top
  · exact h ▸ sat_freeUFAx_iff_isGunky.mpr isGunky_clopens_cantor

/-- **The ultrainfinitist theory is satisfiable under Henkin semantics** — by the *same*
witness, viewed as the Henkin model over the universal family. One gunky world satisfies
the theory under both readings of the second-order quantifier. -/
theorem T_UI_satisfiable_henkin :
    ∃ (W : BAWorld) (H : HenkinFamily W.carrier), SatTheory H.family T_UI := by
  obtain ⟨W, hW⟩ := T_UI_satisfiable_standard
  exact ⟨W, HenkinFamily.univ W.carrier, hW⟩

/-- The matrix of `freeUFAx` contains no second-order quantifiers. -/
theorem soqf_freeUFAx_matrix :
    SOQuantFree (.imp isUltrafilterFml (.not hasLeastFml)) := by
  simp [SOQuantFree, isUltrafilterFml, upwardFml, infMemFml, properFml, totalFml,
    hasLeastFml]

/-- **Strengthening: every second-order perspective.** On the Cantor witness the theory
holds over *every* quantifier domain `𝒮` whatsoever — the first-order axioms do not see
`𝒮`, and the Π¹₁ free-ultrafilter axiom passes downward from the standard reading
(`sat_allSO_anti`). The gunky world satisfies ultrainfinitism from all Henkin
perspectives at once. -/
theorem T_UI_satisfiable_every_family :
    ∃ W : BAWorld, ∀ 𝒮 : Set (Set W.carrier), SatTheory 𝒮 T_UI := by
  refine ⟨cantorWorld, fun 𝒮 φ hφ => ?_⟩
  rcases hφ with h | h | h
  · exact h ▸ sat_gunkAx_iff_isGunky.mpr isGunky_clopens_cantor
  · exact h ▸ sat_nontrivAx_iff.mpr cantorWorld_bot_ne_top
  · subst h
    exact sat_allSO_anti (Set.subset_univ 𝒮) _ soqf_freeUFAx_matrix _ _
      (sat_freeUFAx_iff_isGunky.mpr isGunky_clopens_cantor)

/-! ## Henkin absoluteness of the free-ultrafilter axiom

The comprehension clause of a `HenkinFamily` is load-bearing: the would-be refuting
witness of `freeUFAx` at an atom `a` — the principal up-set `{b | a ≤ b}` — is
*definable with parameter `a`*, so comprehension forces it into every Henkin family.
Hence `freeUFAx` has the *same* truth value over every Henkin family as over the
standard semantics: it is **Henkin-absolute**. By contrast, Σ¹₁ truths can change over
non-universal raw families (`sigma11_not_family_absolute`) — the latitude is located
precisely at non-definable witnesses. -/

/-- Every Henkin family contains every principal up-set: `{b | a ≤ b}` is defined by
the formula `fvar 1 ≤ fvar 0` with parameter `a`, so comprehension applies. -/
theorem principalUp_mem_henkinFamily (H : HenkinFamily M) (a : M) :
    {b : M | a ≤ b} ∈ H.family := by
  have h := H.comprehension (n := 1) (m := 0)
    (.le (.fvar 1) (.fvar 0)) (Fin.cons a Fin.elim0) Fin.elim0 (fun i => i.elim0)
  have heq : {x : M | Sat H.family (Fin.cons x (Fin.cons a Fin.elim0)) Fin.elim0
      (.le (.fvar 1) (.fvar 0))} = {b : M | a ≤ b} := by
    ext x; simp
  rwa [heq] at h

/-- The internalized Stone dictionary over any family containing the principal
up-sets (the only sets the refutation needs). -/
theorem sat_freeUFAx_iff_isGunky_of_principalUps {𝒮 : Set (Set M)}
    (h𝒮 : ∀ a : M, {b : M | a ≤ b} ∈ 𝒮) :
    SatSentence 𝒮 freeUFAx ↔ IsGunky M := by
  rw [isGunky_iff_no_isAtom]
  constructor
  · intro h a ha
    have := h {b : M | a ≤ b} (h𝒮 a)
    rw [sat_imp, sat_not, sat_isUltrafilterFml_iff, sat_hasLeastFml_iff] at this
    simp only [Fin.cons_zero] at this
    exact this (isUltraSet_principalUp ha) (hasLeast_principalUp a)
  · intro h X _
    rw [sat_imp, sat_not, sat_isUltrafilterFml_iff, sat_hasLeastFml_iff]
    simp only [Fin.cons_zero]
    rintro hX ⟨m, hm, hleast⟩
    exact h m (isAtom_of_least hX hm hleast)

/-- **Henkin absoluteness.** Over *every* Henkin family — universal or not — the
free-ultrafilter axiom holds iff the algebra is gunky; its truth value agrees with the
standard semantics in all Henkin models over `M`. -/
theorem sat_freeUFAx_iff_isGunky_henkin (H : HenkinFamily M) :
    SatSentence H.family freeUFAx ↔ IsGunky M :=
  sat_freeUFAx_iff_isGunky_of_principalUps (principalUp_mem_henkinFamily H)

/-- **The theory holds over every Henkin family** on the Cantor witness — not merely
the universal one. Whatever second-order perspective a Henkin model takes, the gunky
world satisfies ultrainfinitism. -/
theorem T_UI_satisfiable_all_henkin :
    ∃ W : BAWorld, ∀ H : HenkinFamily W.carrier, SatTheory H.family T_UI := by
  refine ⟨cantorWorld, fun H φ hφ => ?_⟩
  rcases hφ with h | h | h
  · exact h ▸ sat_gunkAx_iff_isGunky.mpr isGunky_clopens_cantor
  · exact h ▸ sat_nontrivAx_iff.mpr cantorWorld_bot_ne_top
  · exact h ▸ (sat_freeUFAx_iff_isGunky_henkin H).mpr isGunky_clopens_cantor

/-! ## The Σ¹₁ contrast: where the latitude genuinely bites -/

/-- The Σ¹₁ sentence "some ultrafilter exists". -/
def existsUFAx : MSO 0 0 := .exSO isUltrafilterFml

open TopologicalSpace in
/-- A choice-free ultrafilter on the Cantor clopen algebra: the clopens containing a
fixed point. -/
theorem isUltraSet_pointUltra (x : ℕ → Bool) :
    IsUltraSet {K : Clopens (ℕ → Bool) | x ∈ K} where
  upward _ _ hx hxy := hxy hx
  inf_mem K L hx hy := by
    show x ∈ (K ⊓ L : Clopens (ℕ → Bool))
    rw [← SetLike.mem_coe, Clopens.coe_inf]
    exact ⟨hx, hy⟩
  proper hbot := by
    rw [Set.mem_setOf_eq, ← SetLike.mem_coe, Clopens.coe_bot] at hbot
    exact hbot
  total K := by
    rcases em (x ∈ K) with hx | hx
    · exact Or.inl hx
    · right
      show x ∈ (Kᶜ : Clopens (ℕ → Bool))
      rw [← SetLike.mem_coe, Clopens.coe_compl]
      exact hx

open TopologicalSpace in
/-- Under standard semantics the Cantor witness *does* have an ultrafilter
(choice-free: a point filter). -/
theorem sat_existsUFAx_standard :
    SatSentence (Set.univ : Set (Set (Clopens (ℕ → Bool)))) existsUFAx := by
  refine ⟨{K | (fun _ => false) ∈ K}, Set.mem_univ _, ?_⟩
  rw [sat_isUltrafilterFml_iff]
  simpa using isUltraSet_pointUltra (fun _ => false)

/-- **Σ¹₁ truths are not family-absolute.** Unlike the Π¹₁ axiom `freeUFAx` (downward
absolute, `sat_allSO_anti`; Henkin-absolute, `sat_freeUFAx_iff_isGunky_henkin`), the
Σ¹₁ sentence "some ultrafilter exists" is true under standard semantics yet false over
a small raw family that omits all ultrafilters. (The family `{∅}` is not
comprehension-closed; constructing a *proper* comprehension-closed family on a given
algebra is genuine model-construction work, honestly left open.) The latitude lives
exactly at non-definable witnesses. -/
theorem sigma11_not_family_absolute :
    SatSentence (Set.univ : Set (Set (TopologicalSpace.Clopens (ℕ → Bool)))) existsUFAx ∧
      ∃ 𝒮 : Set (Set (TopologicalSpace.Clopens (ℕ → Bool))), ¬ SatSentence 𝒮 existsUFAx := by
  refine ⟨sat_existsUFAx_standard, {(∅ : Set (TopologicalSpace.Clopens (ℕ → Bool)))}, ?_⟩
  rintro ⟨X, hX, hsat⟩
  rw [Set.mem_singleton_iff] at hX
  subst hX
  rw [sat_isUltrafilterFml_iff] at hsat
  simp only [Fin.cons_zero] at hsat
  rcases hsat.total ⊥ with h | h
  · exact h
  · exact h

/-! ## The Stone-points weld: ultrafilter-sets ARE the points of the Stone space

`IsUltraSet` (the semantic ultrafilters of the MSO layer) and the points of
`StoneSpace B = PrimeSpectrum (AsBoolRing B)` are the same object: an ultrafilter-set
corresponds to the prime ideal of (the ring images of) its non-members
(`ultraSetEquivStonePoint`). Under this correspondence, **having a least element is being
an isolated point** (`hasLeast_iff_isOpen_singleton`), so the two previously parallel
chains — `sat_freeUFAx_iff_isGunky` (MSO side) and `isGunky_iff_perfect_stoneSpace`
(topological side) — close into one circle
(`sat_freeUFAx_iff_perfect_stoneSpace`):

free-ultrafilter axiom ⟺ no principal ultrafilter-set ⟺ no atom ⟺ no isolated point
⟺ perfect Stone space. -/

section StoneWeld

namespace IsUltraSet

theorem top_mem {F : Set M} (hF : IsUltraSet F) : (⊤ : M) ∈ F := by
  rcases hF.total ⊤ with h | h
  · exact h
  · rw [compl_top] at h
    exact absurd h hF.proper

theorem sup_mem_or {F : Set M} (hF : IsUltraSet F) {a b : M}
    (h : a ⊔ b ∈ F) : a ∈ F ∨ b ∈ F := by
  by_contra hc
  push_neg at hc
  have ha := (hF.total a).resolve_left hc.1
  have hb := (hF.total b).resolve_left hc.2
  have hinf := hF.inf_mem _ _ ha hb
  rw [← compl_sup] at hinf
  have hbot := hF.inf_mem _ _ h hinf
  rw [inf_compl_self] at hbot
  exact hF.proper hbot

/-- The prime ideal of an ultrafilter-set: the ring images of its non-members. -/
def stoneIdeal {F : Set M} (hF : IsUltraSet F) : Ideal (AsBoolRing M) where
  carrier := {x : AsBoolRing M | ofBoolRing x ∉ F}
  zero_mem' := by
    show ofBoolRing (0 : AsBoolRing M) ∉ F
    rw [show ofBoolRing (0 : AsBoolRing M) = (⊥ : M) from rfl]
    exact hF.proper
  add_mem' := by
    intro x y hx hy
    show ofBoolRing (x + y) ∉ F
    rw [show ofBoolRing (x + y) = symmDiff (ofBoolRing x : M) (ofBoolRing y) from rfl]
    intro hmem
    have hsup : (ofBoolRing x : M) ⊔ ofBoolRing y ∈ F :=
      hF.upward _ _ hmem symmDiff_le_sup
    rcases hF.sup_mem_or hsup with h | h
    · exact hx h
    · exact hy h
  smul_mem' := by
    intro c x hx
    show ofBoolRing (c * x) ∉ F
    rw [show ofBoolRing (c * x) = (ofBoolRing c : M) ⊓ ofBoolRing x from rfl]
    intro hmem
    exact hx (hF.upward _ _ hmem inf_le_right)

theorem stoneIdeal_isPrime {F : Set M} (hF : IsUltraSet F) :
    (hF.stoneIdeal).IsPrime := by
  constructor
  · rw [Ideal.ne_top_iff_one]
    show ¬ ofBoolRing (1 : AsBoolRing M) ∉ F
    rw [show ofBoolRing (1 : AsBoolRing M) = (⊤ : M) from rfl, not_not]
    exact hF.top_mem
  · intro x y hxy
    have h : (ofBoolRing x : M) ⊓ ofBoolRing y ∉ F := by
      rw [show (ofBoolRing x : M) ⊓ ofBoolRing y = ofBoolRing (x * y) from rfl]
      exact hxy
    rcases em ((ofBoolRing x : M) ∈ F) with hx | hx
    · right
      show ofBoolRing y ∉ F
      intro hy
      exact h (hF.inf_mem _ _ hx hy)
    · exact Or.inl hx

/-- The Stone point of an ultrafilter-set. -/
def stonePoint {F : Set M} (hF : IsUltraSet F) : StoneSpace M :=
  ⟨hF.stoneIdeal, hF.stoneIdeal_isPrime⟩

end IsUltraSet

/-- The ultrafilter-set of a Stone point: the elements whose ring image avoids the
prime ideal. -/
def stonePointUltraSet (p : StoneSpace M) : Set M :=
  {a : M | toBoolRing a ∉ p.asIdeal}

theorem isUltraSet_stonePointUltraSet (p : StoneSpace M) :
    IsUltraSet (stonePointUltraSet p) where
  upward a b ha hab := by
    show toBoolRing b ∉ p.asIdeal
    intro hb
    apply ha
    show toBoolRing a ∈ p.asIdeal
    rw [show (toBoolRing a : AsBoolRing M) = toBoolRing a * toBoolRing b by
      rw [show (toBoolRing a * toBoolRing b : AsBoolRing M) = toBoolRing (a ⊓ b) from rfl,
        inf_eq_left.mpr hab]]
    exact Ideal.mul_mem_left _ _ hb
  inf_mem a b ha hb := by
    show toBoolRing (a ⊓ b) ∉ p.asIdeal
    rw [show (toBoolRing (a ⊓ b) : AsBoolRing M) = toBoolRing a * toBoolRing b from rfl]
    intro h
    rcases p.2.mem_or_mem h with h' | h'
    · exact ha h'
    · exact hb h'
  proper := by
    intro h
    exact h (by
      rw [show (toBoolRing (⊥ : M) : AsBoolRing M) = 0 from rfl]
      exact p.asIdeal.zero_mem)
  total a := by
    by_contra hc
    push_neg at hc
    have h1 : toBoolRing a ∈ p.asIdeal := not_not.mp hc.1
    have h2 : toBoolRing aᶜ ∈ p.asIdeal := not_not.mp hc.2
    have hsum := p.asIdeal.add_mem h1 h2
    rw [show (toBoolRing a + toBoolRing aᶜ : AsBoolRing M) = toBoolRing (symmDiff a aᶜ)
        from rfl,
      show symmDiff a aᶜ = (⊤ : M) by
        simp [symmDiff_def, sdiff_eq, compl_compl]] at hsum
    exact p.2.ne_top (Ideal.eq_top_iff_one _ |>.mpr hsum)

theorem stonePointUltraSet_stonePoint {F : Set M} (hF : IsUltraSet F) :
    stonePointUltraSet hF.stonePoint = F := by
  ext a
  show ¬ (ofBoolRing (toBoolRing a) : M) ∉ F ↔ a ∈ F
  rw [show (ofBoolRing (toBoolRing a) : M) = a from rfl]
  exact not_not

theorem stonePoint_stonePointUltraSet (p : StoneSpace M) :
    (isUltraSet_stonePointUltraSet p).stonePoint = p := by
  refine PrimeSpectrum.ext (Ideal.ext fun x => ?_)
  show ¬ (toBoolRing (ofBoolRing x : M)) ∉ p.asIdeal ↔ x ∈ p.asIdeal
  rw [show (toBoolRing (ofBoolRing x : M) : AsBoolRing M) = x from rfl]
  exact not_not

/-- **The Stone-points weld.** The semantic ultrafilters of the MSO layer are exactly
the points of the Stone space. -/
noncomputable def ultraSetEquivStonePoint :
    {F : Set M // IsUltraSet F} ≃ StoneSpace M where
  toFun F := F.2.stonePoint
  invFun p := ⟨stonePointUltraSet p, isUltraSet_stonePointUltraSet p⟩
  left_inv F := Subtype.ext (stonePointUltraSet_stonePoint F.2)
  right_inv p := stonePoint_stonePointUltraSet p

open PrimeSpectrum in
/-- **Principal = isolated, through the weld.** An ultrafilter-set has a least element
exactly when its Stone point is isolated. -/
theorem hasLeast_iff_isOpen_singleton {F : Set M} (hF : IsUltraSet F) :
    HasLeast F ↔ IsOpen ({hF.stonePoint} : Set (StoneSpace M)) := by
  constructor
  · rintro ⟨m, hm, hleast⟩
    have hatom : IsAtom m := isAtom_of_least hF hm hleast
    have hKatom : IsAtom (stoneRepr M m) := (OrderIso.isAtom_iff (stoneRepr M) m).mpr hatom
    obtain ⟨q, hq⟩ := isAtom_clopens_isSingleton hKatom
    rw [coe_stoneRepr] at hq
    have hp_mem : hF.stonePoint ∈ (basicOpen (toBoolRing m) : Set (StoneSpace M)) := by
      show toBoolRing m ∉ hF.stonePoint.asIdeal
      exact not_not.mpr hm
    rw [hq, Set.mem_singleton_iff] at hp_mem
    rw [hp_mem, ← hq]
    exact (basicOpen (toBoolRing m)).2
  · intro hopen
    have hcl : IsClopen ({hF.stonePoint} : Set (StoneSpace M)) := ⟨isClosed_singleton, hopen⟩
    set K : TopologicalSpace.Clopens (StoneSpace M) := ⟨{hF.stonePoint}, hcl⟩ with hK
    have hKatom : IsAtom K := isAtom_clopens_of_singleton hcl
    set a := (stoneRepr M).symm K with ha
    have hrepr : stoneRepr M a = K := by rw [ha]; exact (stoneRepr M).apply_symm_apply _
    have hbo : (basicOpen (toBoolRing a) : Set (StoneSpace M)) = {hF.stonePoint} := by
      rw [← coe_stoneRepr, hrepr]
      rfl
    refine ⟨a, ?_, ?_⟩
    · have hmem : hF.stonePoint ∈ (basicOpen (toBoolRing a) : Set (StoneSpace M)) := by
        rw [hbo]; rfl
      exact not_not.mp hmem
    · intro b hb
      have hsub : ({hF.stonePoint} : Set (StoneSpace M)) ⊆
          (basicOpen (toBoolRing b) : Set (StoneSpace M)) := by
        intro q hq
        rw [Set.mem_singleton_iff] at hq
        subst hq
        show toBoolRing b ∉ hF.stonePoint.asIdeal
        exact not_not.mpr hb
      have hle : stoneRepr M a ≤ stoneRepr M b := by
        rw [← SetLike.coe_subset_coe, coe_stoneRepr, coe_stoneRepr, hbo]
        exact hsub
      exact (stoneRepr M).le_iff_le.mp hle

/-- **The full circle.** The second-order free-ultrafilter axiom holds (standard
semantics) iff the Stone space is perfect: freeUFAx ⟺ no principal ultrafilter-set ⟺
no atom ⟺ no isolated point ⟺ perfect. The two previously parallel chains, closed. -/
theorem sat_freeUFAx_iff_perfect_stoneSpace :
    SatSentence (Set.univ : Set (Set M)) freeUFAx ↔ PerfectSpace (StoneSpace M) := by
  rw [sat_freeUFAx_iff_isGunky, isGunky_iff_perfect_stoneSpace]

end StoneWeld

end Mettapedia.Logic.Metaphysics




