import Mettapedia.Logic.ModalCompanion.GeometricBarr

/-!
# Gödel's reverse translation from S4 to intuitionistic logic (Theorem 63)

In Gödel's 1941 syntactic proof of the faithfulness of his modal translation, every modal
formula is read back into intuitionistic logic. A *B-formula* is an atom or a formula
beginning with `□`. Every modal formula is `M[A₁, …, Aₙ]` for a classical matrix `M` (here
built from `⊥` and `➝`, the primitive connectives of Foundation's modal language) and
B-formulas `Aᵢ`, the *matrix variables*. The *distinguished matrix* `M′` of `M` is the
conjunction, in a fixed order, of all geometric implications over the matrix variables that
follow classically from `M`; classically `M ≡ M′`. The reverse translation is

* `p′ = p`, `(□A)′ = A′`,
* `M[A₁, …, Aₙ]′ = M′[A₁′, …, Aₙ′]` when the formula is not a B-formula.

Here `slots` lists the matrix variables, `matrixVal` evaluates the matrix,
`distinguished` lists the distinguished implications (candidate pairs of sublists of the
variables, filtered by a truth-table test) and `reverseTranslate` is `A ↦ A′`. Gödel's
Theorem 62 (`GeometricBarr`) turns classical consequence between distinguished matrices into
intuitionistic derivability of the translations (`transfer`, `transferF`, `transferG`); the
lemmas of Gödel's proof follow:

* Lemmas 1, 2 and 5: classically equivalent matrices have intuitionistically equivalent
  translations (`reverseTranslate_equiv_of_classical`);
* Lemma 4: `(A ∧ C)′ ≡ A′ ∧ C′`; Lemmas 6–8: `(¬□A)′ ≡ ¬A′`, `(□A ∨ □C)′ ≡ A′ ∨ C′` and
  `(□A ⊃ □C)′ ≡ A′ ⊃ C′`;
* Lemma 10: `(A ⊃ C)′ ∧ A′ ⊃ C′`, closure under modus ponens;
* Lemma 11: the translation of the axiom `□A ⊃ A` is provable; here the geometric normal
  form is used, since `(□A)′ = A′` must imply each distinguished implication of `A`;
* Lemma 12: translations of classical tautologies are provable;
* Lemma 13: translations of the axioms 4 and K are provable; Lemmas 14–15: modus ponens and
  necessitation, where `(□A)′ = A′`.

**Theorem 63** (`s4ToInt`): a derivation of `A` in S4 from assumptions `Δ` is transformed
into a derivation of `A′` from `Δ′` in any Foundation entailment system with the
intuitionistic axioms; for Foundation's `Propositional.Int` this gives
`provable_reverseTranslate`. The translation does not commute with substitution: Gödel's
example is that `(p ⊃ □p)′` is provable while `(¬p ⊃ □¬p)′` is equivalent to `p ∨ ¬p`
(`reverseTranslate_imp_box_atom`, `reverseTranslate_neg_imp_box_neg`); with Theorem 63 this
shows that `p ⊃ □p` is not a theorem of S4 (`not_provable_imp_box_atom`).

## References

* K. Gödel, *Results on Foundations*, M. Hämeen-Anttila and J. von Plato (eds.), Springer,
  2023 (notebook *Resultate Grundlagen*, Theorems 62–64).
* S. Negri and J. von Plato, *Intuitionistic and modal logic in Gödel's Resultate
  Grundlagen*, Logique et Analyse 268, 439–465, doi:10.2143/LEA.268.0.3295055.
* J. von Plato, *Gödel's modal interpretation of intuitionistic logic and its proof theory*,
  Monatsh. Math. 208 (2025), 791–817, doi:10.1007/s00605-025-02083-0.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ModalCompanion

open LO LO.Entailment

/-! ## Matrices and matrix variables -/

/-- The matrix variables of a modal formula in order of occurrence: its maximal subformulas
that are atoms or boxed formulas (B-formulas). -/
def slots : Modal.Formula ℕ → List (Modal.Formula ℕ)
  | .atom a => [.atom a]
  | .falsum => []
  | .imp φ ψ => slots φ ++ slots ψ
  | .box φ => [.box φ]

/-- The value of the classical matrix of a modal formula under a valuation of its matrix
variables. -/
def matrixVal (v : Modal.Formula ℕ → Bool) : Modal.Formula ℕ → Bool
  | .atom a => v (.atom a)
  | .falsum => false
  | .imp φ ψ => !matrixVal v φ || matrixVal v ψ
  | .box φ => v (.box φ)

section Matrix

variable (v : Modal.Formula ℕ → Bool) (φ ψ : Modal.Formula ℕ)

@[simp] theorem matrixVal_imp : matrixVal v (φ ➝ ψ) = (!matrixVal v φ || matrixVal v ψ) :=
  rfl
@[simp] theorem matrixVal_box : matrixVal v (□φ) = v (□φ) := rfl
@[simp] theorem matrixVal_bot : matrixVal v ⊥ = false := rfl
@[simp] theorem matrixVal_neg : matrixVal v (∼φ) = !matrixVal v φ := by
  change (!matrixVal v φ || false) = !matrixVal v φ
  cases matrixVal v φ <;> rfl
@[simp] theorem matrixVal_and :
    matrixVal v (φ ⋏ ψ) = (matrixVal v φ && matrixVal v ψ) := by
  change (!(!matrixVal v φ || (!matrixVal v ψ || false)) || false) = _
  cases matrixVal v φ <;> cases matrixVal v ψ <;> rfl
@[simp] theorem matrixVal_or :
    matrixVal v (φ ⋎ ψ) = (matrixVal v φ || matrixVal v ψ) := by
  change (!(!matrixVal v φ || false) || matrixVal v ψ) = _
  cases matrixVal v φ <;> cases matrixVal v ψ <;> rfl

end Matrix

theorem matrixVal_congr {v w : Modal.Formula ℕ → Bool} :
    ∀ φ : Modal.Formula ℕ, (∀ x ∈ slots φ, v x = w x) → matrixVal v φ = matrixVal w φ
  | .atom _, h => h _ List.mem_cons_self
  | .falsum, _ => rfl
  | .imp φ ψ, h => by
    change (!matrixVal v φ || matrixVal v ψ) = (!matrixVal w φ || matrixVal w ψ)
    rw [matrixVal_congr φ fun x hx => h x (List.mem_append_left _ hx),
      matrixVal_congr ψ fun x hx => h x (List.mem_append_right _ hx)]
  | .box _, h => h _ List.mem_cons_self

/-- The matrix variables without repetitions, in order of first occurrence. -/
def vars (φ : Modal.Formula ℕ) : List (Modal.Formula ℕ) := (slots φ).eraseDups

theorem mem_vars {φ x : Modal.Formula ℕ} : x ∈ vars φ ↔ x ∈ slots φ := List.mem_eraseDups

/-! ## Distinguished matrices -/

/-- All geometric implications over the variables `l`, as pairs of sublists. -/
def candidates {α : Type*} (l : List α) : List (GeoImp α) :=
  l.sublists.flatMap fun Γ => l.sublists.map fun Δ => ⟨Γ, Δ⟩

theorem mem_candidates {α : Type*} {l : List α} {g : GeoImp α} :
    g ∈ candidates l ↔ g.ante.Sublist l ∧ g.cons.Sublist l := by
  unfold candidates
  constructor
  · intro h
    obtain ⟨Γ, hΓ, hg⟩ := List.mem_flatMap.mp h
    obtain ⟨Δ, hΔ, rfl⟩ := List.mem_map.mp hg
    exact ⟨List.mem_sublists.mp hΓ, List.mem_sublists.mp hΔ⟩
  · rintro ⟨hΓ, hΔ⟩
    exact List.mem_flatMap.mpr ⟨g.ante, List.mem_sublists.mpr hΓ,
      List.mem_map.mpr ⟨g.cons, List.mem_sublists.mpr hΔ, rfl⟩⟩

/-- Truth-table test whether the geometric implication `g` follows classically from the
matrix of `φ`. -/
def entails (φ : Modal.Formula ℕ) (g : GeoImp (Modal.Formula ℕ)) : Bool :=
  (vars φ).sublists.all fun T =>
    !(matrixVal (fun x => decide (x ∈ T)) φ) || g.eval fun x => decide (x ∈ T)

theorem entails_iff {φ : Modal.Formula ℕ} {g : GeoImp (Modal.Formula ℕ)}
    (ha : g.ante ⊆ vars φ) (hc : g.cons ⊆ vars φ) :
    entails φ g = true ↔ ∀ v, matrixVal v φ = true → g.eval v = true := by
  unfold entails
  rw [all_sublists_eq_true_iff _ (fun v => !(matrixVal v φ) || g.eval v)]
  · constructor
    · intro h v hv
      have := h v
      rw [hv] at this
      exact this
    · intro h v
      cases hv : matrixVal v φ
      · rfl
      · rw [h v hv]; rfl
  · intro v w hvw
    rw [matrixVal_congr φ fun x hx => hvw x (mem_vars.mpr hx),
      GeoImp.eval_congr (fun a h => hvw a (ha h)) (fun c h => hvw c (hc h))]

/-- The distinguished implications of `φ`: the geometric implications over its matrix
variables that follow classically from its matrix. -/
def distinguished (φ : Modal.Formula ℕ) : List (GeoImp (Modal.Formula ℕ)) :=
  (candidates (vars φ)).filter (entails φ)

theorem mem_distinguished {φ : Modal.Formula ℕ} {g : GeoImp (Modal.Formula ℕ)} :
    g ∈ distinguished φ ↔
      (g.ante.Sublist (vars φ) ∧ g.cons.Sublist (vars φ)) ∧
        ∀ v, matrixVal v φ = true → g.eval v = true := by
  unfold distinguished
  rw [List.mem_filter, mem_candidates]
  constructor
  · rintro ⟨hs, he⟩
    exact ⟨hs, (entails_iff hs.1.subset hs.2.subset).mp he⟩
  · rintro ⟨hs, he⟩
    exact ⟨hs, (entails_iff hs.1.subset hs.2.subset).mpr he⟩

theorem distinguished_subset_vars {φ : Modal.Formula ℕ} {g : GeoImp (Modal.Formula ℕ)}
    (hg : g ∈ distinguished φ) : g.ante ⊆ vars φ ∧ g.cons ⊆ vars φ :=
  ⟨(mem_distinguished.mp hg).1.1.subset, (mem_distinguished.mp hg).1.2.subset⟩

/-- The distinguished implications of `φ` are classically equivalent to its matrix. -/
theorem distinguished_iff (φ : Modal.Formula ℕ) (v : Modal.Formula ℕ → Bool) :
    (∀ g ∈ distinguished φ, g.eval v = true) ↔ matrixVal v φ = true := by
  constructor
  · intro h
    cases hv : matrixVal v φ
    · -- the full clause of `v` is distinguished and false under `v`
      let g₀ : GeoImp (Modal.Formula ℕ) :=
        ⟨(vars φ).filter v, (vars φ).filter fun x => !v x⟩
      have hg₀ : g₀ ∈ distinguished φ := by
        refine mem_distinguished.mpr ⟨⟨List.filter_sublist, List.filter_sublist⟩, ?_⟩
        intro w hw
        cases he : g₀.eval w
        · exfalso
          obtain ⟨hante, hcons⟩ := GeoImp.eval_eq_false.mp he
          have hagree : ∀ x ∈ slots φ, w x = v x := by
            intro x hx
            have hx' := mem_vars.mpr hx
            cases hvx : v x
            · have hxc : x ∈ g₀.cons := List.mem_filter.mpr ⟨hx', by rw [hvx]; rfl⟩
              cases hwx : w x
              · rfl
              · exact absurd hwx (List.any_eq_false.mp hcons x hxc)
            · exact List.all_eq_true.mp hante x (List.mem_filter.mpr ⟨hx', hvx⟩)
          rw [matrixVal_congr φ hagree, hv] at hw
          exact absurd hw (by decide)
        · rfl
      have h₀ := h g₀ hg₀
      have hfalse : g₀.eval v = false := GeoImp.eval_eq_false.mpr
        ⟨List.all_eq_true.mpr fun x hx => (List.mem_filter.mp hx).2,
          List.any_eq_false.mpr fun x hx hvx => by
            have := (List.mem_filter.mp hx).2
            rw [hvx] at this
            exact absurd this (by decide)⟩
      rw [hfalse] at h₀
      exact absurd h₀ (by decide)
    · rfl
  · intro hv g hg
    exact (mem_distinguished.mp hg).2 v hv

/-! ## The reverse translation -/

/-- Gödel's distinguished matrix `M′` of `φ`, with the matrix variables read through `τ`. -/
def normalForm (φ : Modal.Formula ℕ) (τ : Modal.Formula ℕ → Propositional.Formula ℕ) :
    Propositional.Formula ℕ :=
  ⋀((distinguished φ).map (GeoImp.toFormula τ))

/-- The reverse translation together with a table of the translations of the matrix
variables; defined by structural recursion. -/
def revAux :
    Modal.Formula ℕ → Propositional.Formula ℕ × (Modal.Formula ℕ → Propositional.Formula ℕ)
  | .atom a => (.atom a, fun _ => .atom a)
  | .falsum => (normalForm .falsum fun _ => ⊥, fun _ => ⊥)
  | .imp φ ψ =>
    let τ : Modal.Formula ℕ → Propositional.Formula ℕ :=
      fun x => if x ∈ slots φ then (revAux φ).2 x else (revAux ψ).2 x
    (normalForm (.imp φ ψ) τ, τ)
  | .box φ => ((revAux φ).1, fun _ => (revAux φ).1)

/-- Gödel's reverse translation `A ↦ A′`: `p′ = p`, `(□A)′ = A′`, and for a formula that is
not a B-formula, the distinguished matrix of its matrix applied to the translations of its
matrix variables. -/
def reverseTranslate (φ : Modal.Formula ℕ) : Propositional.Formula ℕ := (revAux φ).1

@[simp] theorem reverseTranslate_atom (a : ℕ) :
    reverseTranslate (.atom a) = .atom a := rfl

@[simp] theorem reverseTranslate_box (φ : Modal.Formula ℕ) :
    reverseTranslate (□φ) = reverseTranslate φ := rfl

theorem revAux_snd : ∀ (φ : Modal.Formula ℕ) (x : Modal.Formula ℕ), x ∈ slots φ →
    (revAux φ).2 x = reverseTranslate x
  | .atom _, _, hx => by
    rw [List.mem_singleton.mp hx]; rfl
  | .falsum, _, hx => absurd hx List.not_mem_nil
  | .imp φ ψ, x, hx => by
    change (if x ∈ slots φ then (revAux φ).2 x else (revAux ψ).2 x) = _
    by_cases hφ : x ∈ slots φ
    · rw [if_pos hφ, revAux_snd φ x hφ]
    · rw [if_neg hφ, revAux_snd ψ x ((List.mem_append.mp hx).resolve_left hφ)]
  | .box _, _, hx => by
    rw [List.mem_singleton.mp hx]; rfl

theorem normalForm_congr {φ : Modal.Formula ℕ} {τ τ' : Modal.Formula ℕ → Propositional.Formula ℕ}
    (h : ∀ x ∈ vars φ, τ x = τ' x) : normalForm φ τ = normalForm φ τ' := by
  unfold normalForm
  congr 1
  refine List.map_congr_left fun g hg => ?_
  unfold GeoImp.toFormula
  rw [List.map_congr_left fun x hx => h x ((distinguished_subset_vars hg).1 hx),
    List.map_congr_left fun x hx => h x ((distinguished_subset_vars hg).2 hx)]

theorem reverseTranslate_imp_eq (φ ψ : Modal.Formula ℕ) :
    reverseTranslate (φ ➝ ψ) = normalForm (φ ➝ ψ) reverseTranslate :=
  normalForm_congr fun x hx => revAux_snd (φ ➝ ψ) x (mem_vars.mp hx)

theorem reverseTranslate_bot_eq :
    reverseTranslate ⊥ = normalForm ⊥ reverseTranslate :=
  normalForm_congr fun _ hx => absurd (mem_vars.mp hx) List.not_mem_nil

/-! ## The translation and its distinguished matrix -/

section Transfer

variable {S : Type*} [Entailment S (Propositional.Formula ℕ)] (𝓢 : S) [Entailment.Int 𝓢]

/-- The generic `(⊤ ➝ φ) ➝ φ`. -/
def verumImp (φ : Propositional.Formula ℕ) : 𝓢 ⊢! (⊤ ➝ φ) ➝ φ := CCC ⨀ verum

/-- For a B-formula `x`, every distinguished implication of `x` has `x` among its consequent
atoms. -/
theorem mem_cons_of_distinguished_B {x : Modal.Formula ℕ} (hslots : slots x = [x])
    (hval : ∀ v, matrixVal v x = v x) {g : GeoImp (Modal.Formula ℕ)}
    (hg : g ∈ distinguished x) : x ∈ g.cons := by
  have he := (mem_distinguished.mp hg).2 (fun _ => true) (hval _)
  obtain ⟨y, hy, -⟩ := GeoImp.eval_eq_true_of_ante he fun _ _ => rfl
  have hy' := mem_vars.mp ((distinguished_subset_vars hg).2 hy)
  rw [hslots, List.mem_singleton] at hy'
  exact hy' ▸ hy

theorem singleton_mem_distinguished_B {x : Modal.Formula ℕ} (hslots : slots x = [x])
    (hval : ∀ v, matrixVal v x = v x) : (⟨[], [x]⟩ : GeoImp _) ∈ distinguished x := by
  refine mem_distinguished.mpr ⟨⟨List.nil_sublist _, List.singleton_sublist.mpr ?_⟩, ?_⟩
  · exact mem_vars.mpr (by rw [hslots]; exact List.mem_cons_self)
  · intro v hv
    rw [hval] at hv
    change (!true || (v x || false)) = true
    rw [hv]; rfl

/-- A B-formula implies its distinguished matrix. -/
def toNormalFormB {x : Modal.Formula ℕ} (hslots : slots x = [x])
    (hval : ∀ v, matrixVal v x = v x) :
    𝓢 ⊢! reverseTranslate x ➝ normalForm x reverseTranslate :=
  right_Conj'_intro _ _ _ fun g hg =>
    C_trans (right_Disj'_intro reverseTranslate g.cons
      (mem_cons_of_distinguished_B hslots hval hg)) implyK

/-- The distinguished matrix of a B-formula implies it. -/
def ofNormalFormB {x : Modal.Formula ℕ} (hslots : slots x = [x])
    (hval : ∀ v, matrixVal v x = v x) :
    𝓢 ⊢! normalForm x reverseTranslate ➝ reverseTranslate x :=
  C_trans (left_Conj'_intro (singleton_mem_distinguished_B hslots hval)
    (GeoImp.toFormula reverseTranslate)) (verumImp 𝓢 _)

/-- `A′` implies the conjunction of the distinguished implications of `A`, read through `′`. -/
def toNormalForm : (φ : Modal.Formula ℕ) →
    𝓢 ⊢! reverseTranslate φ ➝ normalForm φ reverseTranslate
  | .atom _ => toNormalFormB 𝓢 rfl fun _ => rfl
  | .falsum => by
    show 𝓢 ⊢! reverseTranslate ⊥ ➝ normalForm ⊥ reverseTranslate
    rw [← reverseTranslate_bot_eq]; exact C_id
  | .imp φ ψ => by
    show 𝓢 ⊢! reverseTranslate (φ ➝ ψ) ➝ normalForm (φ ➝ ψ) reverseTranslate
    rw [← reverseTranslate_imp_eq φ ψ]; exact C_id
  | .box _ => toNormalFormB 𝓢 rfl fun _ => rfl

/-- The conjunction of the distinguished implications of `A`, read through `′`, implies `A′`. -/
def ofNormalForm : (φ : Modal.Formula ℕ) →
    𝓢 ⊢! normalForm φ reverseTranslate ➝ reverseTranslate φ
  | .atom _ => ofNormalFormB 𝓢 rfl fun _ => rfl
  | .falsum => by
    show 𝓢 ⊢! normalForm ⊥ reverseTranslate ➝ reverseTranslate ⊥
    rw [← reverseTranslate_bot_eq]; exact C_id
  | .imp φ ψ => by
    show 𝓢 ⊢! normalForm (φ ➝ ψ) reverseTranslate ➝ reverseTranslate (φ ➝ ψ)
    rw [← reverseTranslate_imp_eq φ ψ]; exact C_id
  | .box _ => ofNormalFormB 𝓢 rfl fun _ => rfl

/-- **Transfer** (Theorem 62 applied to distinguished matrices): if the geometric
implications `𝔄` over modal formulas classically imply the matrix of `φ`, then their
translations intuitionistically imply `φ′`. -/
def transfer (𝔄 : List (GeoImp (Modal.Formula ℕ))) (φ : Modal.Formula ℕ)
    (h : ∀ v, (∀ g ∈ 𝔄, g.eval v = true) → matrixVal v φ = true) :
    𝓢 ⊢! ⋀(𝔄.map (GeoImp.toFormula reverseTranslate)) ➝ reverseTranslate φ :=
  C_trans
    (right_Conj'_intro _ (distinguished φ) (GeoImp.toFormula reverseTranslate) fun g hg =>
      barr 𝓢 reverseTranslate 𝔄 g fun v hv => (distinguished_iff φ v).mpr (h v hv) g hg)
    (ofNormalForm 𝓢 φ)

/-- The translations of the formulas `Φ` imply the translated distinguished implications of
all of them. -/
def toDistinguishedAll (Φ : List (Modal.Formula ℕ)) :
    𝓢 ⊢! ⋀(Φ.map reverseTranslate) ➝
      ⋀((Φ.flatMap distinguished).map (GeoImp.toFormula reverseTranslate)) :=
  right_Conj'_intro _ _ _ fun g hg =>
    let ψ := Φ.chooseX (fun ψ => g ∈ distinguished ψ) (List.mem_flatMap.mp hg)
    C_trans (left_Conj'_intro ψ.2.1 reverseTranslate)
      (C_trans (toNormalForm 𝓢 ψ.1) (left_Conj'_intro ψ.2.2 _))

theorem eval_of_matrixVal {Φ : List (Modal.Formula ℕ)} {v : Modal.Formula ℕ → Bool}
    (hv : ∀ g ∈ Φ.flatMap distinguished, g.eval v = true) :
    ∀ ψ ∈ Φ, matrixVal v ψ = true := fun ψ hψ =>
  (distinguished_iff ψ v).mp fun g hg => hv g (List.mem_flatMap.mpr ⟨ψ, hψ, hg⟩)

/-- **Transfer between formulas**: if the matrices of `Φ` classically imply the matrix of
`φ`, then `⋀Φ′ ➝ φ′` is intuitionistically derivable. -/
def transferF (Φ : List (Modal.Formula ℕ)) (φ : Modal.Formula ℕ)
    (h : ∀ v, (∀ ψ ∈ Φ, matrixVal v ψ = true) → matrixVal v φ = true) :
    𝓢 ⊢! ⋀(Φ.map reverseTranslate) ➝ reverseTranslate φ :=
  C_trans (toDistinguishedAll 𝓢 Φ)
    (transfer 𝓢 _ φ fun v hv => h v (eval_of_matrixVal hv))

/-- **Transfer to a geometric implication**: if the matrices of `Φ` classically imply the
geometric implication `G` over modal formulas, then `⋀Φ′ ➝ G′` is derivable. -/
def transferG (Φ : List (Modal.Formula ℕ)) (G : GeoImp (Modal.Formula ℕ))
    (h : ∀ v, (∀ ψ ∈ Φ, matrixVal v ψ = true) → G.eval v = true) :
    𝓢 ⊢! ⋀(Φ.map reverseTranslate) ➝ G.toFormula reverseTranslate :=
  C_trans (toDistinguishedAll 𝓢 Φ)
    (barr 𝓢 reverseTranslate _ G fun v hv => h v (eval_of_matrixVal hv))

/-! ## Gödel's lemmas -/

/-- **Lemmas 1, 2 and 5**: formulas with classically equivalent matrices have
intuitionistically equivalent translations. -/
def reverseTranslate_equiv_of_classical {φ ψ : Modal.Formula ℕ}
    (h : ∀ v, matrixVal v φ = matrixVal v ψ) :
    𝓢 ⊢! reverseTranslate φ ⭤ reverseTranslate ψ :=
  E_intro
    (transferF 𝓢 [φ] ψ fun v hv => (h v) ▸ hv φ List.mem_cons_self)
    (transferF 𝓢 [ψ] φ fun v hv => (h v).symm ▸ hv ψ List.mem_cons_self)

/-- **Lemma 10** (closure under modus ponens): `(A ⊃ C)′ ∧ A′ ⊃ C′`. -/
def reverseTranslate_mp (φ ψ : Modal.Formula ℕ) :
    𝓢 ⊢! reverseTranslate (φ ➝ ψ) ⋏ reverseTranslate φ ➝ reverseTranslate ψ :=
  transferF 𝓢 [φ ➝ ψ, φ] ψ fun v hv => by
    have h₁ := hv _ List.mem_cons_self
    have h₂ := hv φ (List.mem_cons_of_mem _ List.mem_cons_self)
    rw [matrixVal_imp, h₂] at h₁
    exact h₁

/-- **Lemma 12**: the translation of a formula whose matrix is a classical tautology is
intuitionistically provable. -/
def reverseTranslate_of_tautology (φ : Modal.Formula ℕ) (h : ∀ v, matrixVal v φ = true) :
    𝓢 ⊢! reverseTranslate φ :=
  transferF 𝓢 [] φ (fun v _ => h v) ⨀ verum

/-- **Lemma 4**: `(A ∧ C)′ ≡ A′ ∧ C′`. -/
def reverseTranslate_and (φ ψ : Modal.Formula ℕ) :
    𝓢 ⊢! reverseTranslate (φ ⋏ ψ) ⭤ reverseTranslate φ ⋏ reverseTranslate ψ :=
  E_intro
    (right_K_intro
      (transferF 𝓢 [φ ⋏ ψ] φ fun v hv => by
        have h := hv _ List.mem_cons_self
        rw [matrixVal_and] at h
        exact (Bool.and_eq_true_iff.mp h).1)
      (transferF 𝓢 [φ ⋏ ψ] ψ fun v hv => by
        have h := hv _ List.mem_cons_self
        rw [matrixVal_and] at h
        exact (Bool.and_eq_true_iff.mp h).2))
    (transferF 𝓢 [φ, ψ] (φ ⋏ ψ) fun v hv => by
      rw [matrixVal_and, hv φ List.mem_cons_self,
        hv ψ (List.mem_cons_of_mem _ List.mem_cons_self)]
      rfl)

/-- `⊥′ ≡ ⊥`. -/
def reverseTranslate_bot : 𝓢 ⊢! reverseTranslate ⊥ ⭤ ⊥ :=
  E_intro
    (C_trans (transferG 𝓢 [⊥] ⟨[], []⟩ fun v hv => absurd (hv ⊥ List.mem_cons_self)
      (by rw [matrixVal_bot]; decide)) (verumImp 𝓢 ⊥))
    efq

/-- **Lemma 6**: `(¬□A)′ ≡ ¬A′`. -/
def reverseTranslate_neg_box (φ : Modal.Formula ℕ) :
    𝓢 ⊢! reverseTranslate (∼□φ) ⭤ ∼reverseTranslate φ :=
  E_intro
    (transferG 𝓢 [∼□φ] ⟨[□φ], []⟩ fun v hv => by
      have h := hv _ List.mem_cons_self
      rw [matrixVal_neg, matrixVal_box] at h
      change (!(v (□φ) && true) || false) = true
      cases hb : v (□φ)
      · rfl
      · rw [hb] at h; exact absurd h (by decide))
    (transfer 𝓢 [⟨[□φ], []⟩] (∼□φ) fun v hv => by
      have h := hv _ List.mem_cons_self
      change (!(v (□φ) && true) || false) = true at h
      rw [matrixVal_neg, matrixVal_box]
      cases hb : v (□φ)
      · rfl
      · rw [hb] at h; exact absurd h (by decide))

/-- **Lemma 7**: `(□A ∨ □C)′ ≡ A′ ∨ C′`. -/
def reverseTranslate_or_box (φ ψ : Modal.Formula ℕ) :
    𝓢 ⊢! reverseTranslate (□φ ⋎ □ψ) ⭤ reverseTranslate φ ⋎ reverseTranslate ψ :=
  E_intro
    (C_trans (transferG 𝓢 [□φ ⋎ □ψ] ⟨[], [□φ, □ψ]⟩ fun v hv => by
      have h := hv _ List.mem_cons_self
      rw [matrixVal_or, matrixVal_box, matrixVal_box] at h
      change (!true || (v (□φ) || (v (□ψ) || false))) = true
      rw [Bool.or_false]
      exact h) (verumImp 𝓢 _))
    (C_trans implyK (transfer 𝓢 [⟨[], [□φ, □ψ]⟩] (□φ ⋎ □ψ) fun v hv => by
      have h := hv _ List.mem_cons_self
      change (!true || (v (□φ) || (v (□ψ) || false))) = true at h
      rw [Bool.or_false] at h
      rw [matrixVal_or, matrixVal_box, matrixVal_box]
      exact h))

/-- **Lemma 8**: `(□A ⊃ □C)′ ≡ A′ ⊃ C′`. -/
def reverseTranslate_imp_box (φ ψ : Modal.Formula ℕ) :
    𝓢 ⊢! reverseTranslate (□φ ➝ □ψ) ⭤ (reverseTranslate φ ➝ reverseTranslate ψ) :=
  E_intro
    (transferG 𝓢 [□φ ➝ □ψ] ⟨[□φ], [□ψ]⟩ fun v hv => by
      have h := hv _ List.mem_cons_self
      rw [matrixVal_imp, matrixVal_box, matrixVal_box] at h
      change (!(v (□φ) && true) || (v (□ψ) || false)) = true
      rw [Bool.and_true, Bool.or_false]
      exact h)
    (transfer 𝓢 [⟨[□φ], [□ψ]⟩] (□φ ➝ □ψ) fun v hv => by
      have h := hv _ List.mem_cons_self
      change (!(v (□φ) && true) || (v (□ψ) || false)) = true at h
      rw [Bool.and_true, Bool.or_false] at h
      rw [matrixVal_imp, matrixVal_box, matrixVal_box]
      exact h)

/-- `⋀(a :: l) ➝ b` from `a ➝ ⋀l ➝ b`. -/
def conjCons_imp {a b : Propositional.Formula ℕ} {l : List (Propositional.Formula ℕ)}
    (h : 𝓢 ⊢! a ➝ ⋀l ➝ b) : 𝓢 ⊢! ⋀(a :: l) ➝ b :=
  mdp₁ (C_trans (left_Conj₂_intro List.mem_cons_self) h)
    (CConj₂Conj₂ (List.subset_cons_self a l))

/-- The implications `□A ∧ Γ ⊃ Δ` for the distinguished implications `Γ ⊃ Δ` of `A`. -/
def axiomTPremises (φ : Modal.Formula ℕ) : List (GeoImp (Modal.Formula ℕ)) :=
  (distinguished φ).map fun g => ⟨□φ :: g.ante, g.cons⟩

/-- **Lemma 11**: the translation of the axiom `□A ⊃ A` is provable. Since `(□A)′ = A′`,
each implication `□A ∧ Γ ⊃ Δ` of `axiomTPremises` translates to a consequence of `A′` and
its distinguished matrix; classically these implications give `□A ⊃ A`. -/
def reverseTranslate_axiomT (φ : Modal.Formula ℕ) :
    𝓢 ⊢! reverseTranslate (□φ ➝ φ) :=
  transfer 𝓢 (axiomTPremises φ) (□φ ➝ φ) (fun v hv => by
      rw [matrixVal_imp, matrixVal_box]
      cases hb : v (□φ)
      · rfl
      · refine (distinguished_iff φ v).mp fun g hg => ?_
        have h := hv _ (List.mem_map_of_mem (f := fun g : GeoImp (Modal.Formula ℕ) =>
          (⟨□φ :: g.ante, g.cons⟩ : GeoImp _)) hg)
        change (!(v (□φ) && g.ante.all v) || g.cons.any v) = true at h
        rw [hb, Bool.true_and] at h
        exact h) ⨀
    Conj₂_intro _ fun χ hχ =>
      let g := (distinguished φ).chooseX
        (fun g => GeoImp.toFormula reverseTranslate ⟨□φ :: g.ante, g.cons⟩ = χ)
        (by
          obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hχ
          obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
          exact ⟨g, hg, rfl⟩)
      g.2.2 ▸ conjCons_imp 𝓢
        (C_trans (toNormalForm 𝓢 φ) (left_Conj'_intro g.2.1 (GeoImp.toFormula reverseTranslate)))

/-- **Lemma 13**, axiom 4: the translation of `□A ⊃ □□A` is provable. -/
def reverseTranslate_axiomFour (φ : Modal.Formula ℕ) :
    𝓢 ⊢! reverseTranslate (□φ ➝ □□φ) :=
  transfer 𝓢 [⟨[□φ], [□□φ]⟩] (□φ ➝ □□φ) (fun v hv => by
      have h := hv _ List.mem_cons_self
      change (!(v (□φ) && true) || (v (□□φ) || false)) = true at h
      rw [Bool.and_true, Bool.or_false] at h
      rw [matrixVal_imp, matrixVal_box, matrixVal_box]
      exact h) ⨀
    (C_id : 𝓢 ⊢! reverseTranslate φ ➝ reverseTranslate φ)

/-- **Lemma 13**, axiom K: the translation of `□(A ⊃ C) ⊃ □A ⊃ □C` is provable; the
single premise is Lemma 10. -/
def reverseTranslate_axiomK (φ ψ : Modal.Formula ℕ) :
    𝓢 ⊢! reverseTranslate (□(φ ➝ ψ) ➝ □φ ➝ □ψ) :=
  transfer 𝓢 [⟨[□(φ ➝ ψ), □φ], [□ψ]⟩] (□(φ ➝ ψ) ➝ □φ ➝ □ψ) (fun v hv => by
      have h := hv _ List.mem_cons_self
      change (!(v (□(φ ➝ ψ)) && (v (□φ) && true)) || (v (□ψ) || false)) = true at h
      rw [matrixVal_imp, matrixVal_imp, matrixVal_box, matrixVal_box, matrixVal_box]
      revert h
      cases v (□(φ ➝ ψ)) <;> cases v (□φ) <;> cases v (□ψ) <;> decide) ⨀
    reverseTranslate_mp 𝓢 φ ψ

/-- **Lemma 12**, the axiom `A ⊃ C ⊃ A`. -/
def reverseTranslate_implyK (φ ψ : Modal.Formula ℕ) :
    𝓢 ⊢! reverseTranslate (φ ➝ ψ ➝ φ) :=
  reverseTranslate_of_tautology 𝓢 _ fun v => by
    simp only [matrixVal_imp]
    cases matrixVal v φ <;> cases matrixVal v ψ <;> rfl

/-- **Lemma 12**, the axiom `(A ⊃ C ⊃ D) ⊃ (A ⊃ C) ⊃ A ⊃ D`. -/
def reverseTranslate_implyS (φ ψ χ : Modal.Formula ℕ) :
    𝓢 ⊢! reverseTranslate ((φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ) :=
  reverseTranslate_of_tautology 𝓢 _ fun v => by
    simp only [matrixVal_imp]
    cases matrixVal v φ <;> cases matrixVal v ψ <;> cases matrixVal v χ <;> rfl

/-- **Lemma 12**, the axiom `(¬C ⊃ ¬A) ⊃ A ⊃ C`. -/
def reverseTranslate_elimContra (φ ψ : Modal.Formula ℕ) :
    𝓢 ⊢! reverseTranslate ((∼ψ ➝ ∼φ) ➝ (φ ➝ ψ)) :=
  reverseTranslate_of_tautology 𝓢 _ fun v => by
    simp only [matrixVal_imp, matrixVal_neg]
    cases matrixVal v φ <;> cases matrixVal v ψ <;> rfl

/-! ## Theorem 63 -/

/-- **Gödel's Theorem 63**, as a proof transformation: an S4 derivation of `A` from the
assumptions `Δ` becomes a derivation of `A′` in `𝓢`, given derivations in `𝓢` of the
translations of the assumptions. Modus ponens is Lemma 10, necessitation is `(□A)′ = A′`. -/
def s4ToInt {Δ : List (Modal.Formula ℕ)}
    (hyps : (δ : Modal.Formula ℕ) → δ ∈ Δ → 𝓢 ⊢! reverseTranslate δ) :
    {φ : Modal.Formula ℕ} → S4Deriv Δ φ → 𝓢 ⊢! reverseTranslate φ
  | _, .hyp h => hyps _ h
  | _, .implyK φ ψ => reverseTranslate_implyK 𝓢 φ ψ
  | _, .implyS φ ψ χ => reverseTranslate_implyS 𝓢 φ ψ χ
  | _, .elimContra φ ψ => reverseTranslate_elimContra 𝓢 φ ψ
  | _, .axiomK φ ψ => reverseTranslate_axiomK 𝓢 φ ψ
  | _, .axiomT φ => reverseTranslate_axiomT 𝓢 φ
  | _, .axiomFour φ => reverseTranslate_axiomFour 𝓢 φ
  | _, .mdp d₁ d₂ => reverseTranslate_mp 𝓢 _ _ ⨀ K_intro (s4ToInt hyps d₁) (s4ToInt hyps d₂)
  | _, .nec (φ := φ) d => (s4ToInt hyps d : 𝓢 ⊢! reverseTranslate φ)

/-- `′` respects S4-provable implication: `S4 ⊢ A ⊃ C` gives `A′ ⊃ C′`. -/
def reverseTranslate_mono {φ ψ : Modal.Formula ℕ} (d : S4Deriv [] (φ ➝ ψ)) :
    𝓢 ⊢! reverseTranslate φ ➝ reverseTranslate ψ :=
  CC_of_CK (reverseTranslate_mp 𝓢 φ ψ) ⨀ s4ToInt 𝓢 (fun _ h => absurd h List.not_mem_nil) d

end Transfer

/-- Theorem 63 for derivations from assumptions: an S4 derivation of `A` from `Δ` becomes an
intuitionistic derivation of `A′` from `Δ′`. -/
def s4ToIntDeriv {Δ : List (Modal.Formula ℕ)} {φ : Modal.Formula ℕ} (d : S4Deriv Δ φ) :
    IntDeriv (Δ.map reverseTranslate) (reverseTranslate φ) :=
  s4ToInt (⟨Δ.map reverseTranslate⟩ : IntH)
    (fun _ h => PropDeriv.hyp (List.mem_map_of_mem h)) d

/-- **Gödel's Theorem 63**: if `S4 ⊢ A` then `Int ⊢ A′` (Foundation's systems). -/
theorem provable_reverseTranslate {φ : Modal.Formula ℕ} (h : Modal.S4 ⊢ φ) :
    Propositional.Int ⊢ reverseTranslate φ :=
  (S4Deriv.nonempty_of_provable h).elim fun d =>
    ⟨s4ToInt Propositional.Int (fun _ h => absurd h List.not_mem_nil) d⟩

/-! ## The translation does not commute with substitution -/

/-- Gödel's remark, first half: `(p ⊃ □p)′` is intuitionistically provable (it is equivalent
to `p ⊃ p`), although `p ⊃ □p` is not a theorem of S4 (`not_provable_imp_box_atom`). -/
def reverseTranslate_imp_box_atom (a : ℕ) :
    IntDeriv [] (reverseTranslate (.atom a ➝ □(.atom a))) :=
  transfer (⟨[]⟩ : IntH) [⟨[.atom a], [□(.atom a)]⟩] (.atom a ➝ □(.atom a)) (fun v hv => by
      have h := hv _ List.mem_cons_self
      change (!(v (.atom a) && true) || (v (□(.atom a)) || false)) = true at h
      rw [Bool.and_true, Bool.or_false] at h
      exact h) ⨀
    PropDeriv.selfImp _

/-- Gödel's remark, second half: `(¬p ⊃ □¬p)′` is intuitionistically equivalent to `p ∨ ¬p`.
Since `p ∨ ¬p` is not intuitionistically provable (`not_provable_lem₀`), the provability of
`(A ⊃ □A)′` is not closed under substitution. -/
def reverseTranslate_neg_imp_box_neg (a : ℕ) :
    IntDeriv [] (reverseTranslate (∼(.atom a) ➝ □(∼(.atom a))) ⭤ (#a ⋎ ∼#a)) :=
  have hneg : IntDeriv [] (reverseTranslate (∼(.atom a)) ⭤ ∼#a) :=
    E_intro (𝓢 := (⟨[]⟩ : IntH))
      (transferG (⟨[]⟩ : IntH) [∼(.atom a)] ⟨[.atom a], []⟩ fun v hv => by
        have h := hv _ List.mem_cons_self
        rw [matrixVal_neg] at h
        change (!(v (.atom a) && true) || false) = true
        change (!(v (.atom a))) = true at h
        rw [Bool.and_true, Bool.or_false]
        exact h)
      (transfer (⟨[]⟩ : IntH) [⟨[.atom a], []⟩] (∼(.atom a)) fun v hv => by
        have h := hv _ List.mem_cons_self
        change (!(v (.atom a) && true) || false) = true at h
        rw [Bool.and_true, Bool.or_false] at h
        rw [matrixVal_neg]
        exact h)
  E_intro (𝓢 := (⟨[]⟩ : IntH))
    (C_trans
      (C_trans (transferG (⟨[]⟩ : IntH) [∼(.atom a) ➝ □(∼(.atom a))]
        ⟨[], [.atom a, □(∼(.atom a))]⟩ fun v hv => by
          have h := hv _ List.mem_cons_self
          rw [matrixVal_imp, matrixVal_neg, matrixVal_box] at h
          change (!true || (v (.atom a) || (v (□(∼(.atom a))) || false))) = true
          change (!!v (.atom a) || v (□(∼(.atom a)))) = true at h
          rw [Bool.not_not] at h
          rw [Bool.or_false]
          exact h) (verumImp (⟨[]⟩ : IntH) _))
      (CAA_of_C_right (K_left hneg)))
    (C_trans (CAA_of_C_right (K_right hneg))
      (C_trans implyK (transfer (⟨[]⟩ : IntH) [⟨[], [.atom a, □(∼(.atom a))]⟩]
        (∼(.atom a) ➝ □(∼(.atom a))) fun v hv => by
          have h := hv _ List.mem_cons_self
          change (!true || (v (.atom a) || (v (□(∼(.atom a))) || false))) = true at h
          rw [Bool.or_false] at h
          rw [matrixVal_imp, matrixVal_neg, matrixVal_box]
          change (!!v (.atom a) || v (□(∼(.atom a)))) = true
          rw [Bool.not_not]
          exact h)))

/-- Consequently `(¬p ⊃ □¬p)′` is not intuitionistically provable, while `(p ⊃ □p)′` is. -/
theorem not_provable_reverseTranslate_neg_imp_box_neg :
    ¬ Propositional.Int ⊢
      reverseTranslate (∼(Modal.Formula.atom 0) ➝ □(∼(Modal.Formula.atom 0))) := by
  intro h
  obtain ⟨d⟩ := IntDeriv.nonempty_of_provable h
  exact not_nonempty_intDeriv_lem₀
    ⟨K_left (𝓢 := (⟨[]⟩ : IntH)) (reverseTranslate_neg_imp_box_neg 0) ⨀ d⟩

/-- `p ⊃ □p` is not a theorem of S4: its substitution instance `¬p ⊃ □¬p` would be one, and
Theorem 63 would give an intuitionistic derivation of `(¬p ⊃ □¬p)′`, hence of `p ∨ ¬p`. -/
theorem not_provable_imp_box_atom :
    ¬ Modal.S4 ⊢ (Modal.Formula.atom 0 ➝ □(Modal.Formula.atom 0)) := by
  intro h
  obtain ⟨d⟩ := S4Deriv.nonempty_of_provable h
  have d' : S4Deriv [] (∼(Modal.Formula.atom 0) ➝ □(∼(Modal.Formula.atom 0))) :=
    d.subst fun _ => ∼(Modal.Formula.atom 0)
  exact not_nonempty_intDeriv_lem₀
    ⟨K_left (𝓢 := (⟨[]⟩ : IntH)) (reverseTranslate_neg_imp_box_neg 0) ⨀ s4ToIntDeriv d'⟩

end Mettapedia.Logic.ModalCompanion
