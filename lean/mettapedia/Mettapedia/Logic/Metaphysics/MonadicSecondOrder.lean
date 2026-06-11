import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Set.Basic

/-!
# Monadic second-order logic over the Boolean-algebra signature, with standard and Henkin semantics

A minimal monadic second-order (MSO) language over the signature `(⊥, ⊤, ᶜ, ⊓, ⊔, ≤, =)`,
interpreted in an arbitrary Boolean algebra `M`. The point of the file is the *pair* of
semantics for one syntax:

* **standard (full) semantics** — set quantifiers range over all of `Set M`
  (`𝒮 = Set.univ`);
* **Henkin (general-model) semantics** — set quantifiers range over a designated family
  `𝒮 : Set (Set M)` closed under comprehension (`HenkinFamily`).

Satisfaction `Sat` is *relativized*: the family `𝒮` is consulted only at second-order
binders, so `Sat` is a plain non-dependent function and every standard model is literally
a Henkin model over the universal family (`HenkinFamily.univ`).

Open formulas whose free set variables are assigned values outside `𝒮` receive a truth
value as well; this is harmless and out of scope — every theorem downstream evaluates
sentences, or valuations explicitly assumed to lie in `𝒮`.

Main definitions and results:

* `Sat`, `SatSentence` — relativized satisfaction.
* `HenkinFamily` — a second-order quantifier domain closed under comprehension with
  parameters; `HenkinFamily.univ` — the standard semantics is the Henkin model over the
  universal family.
* `SOQuantFree`, `sat_soqf_congr` — formulas without set quantifiers do not see `𝒮`.
* `sat_allSO_anti` — Π¹₁ sentences pass downward to smaller quantifier domains
  (the "perspectival latitude" lemma).

No proof calculus is defined; "consistency" statements downstream are *satisfiability*
(model-existence) statements, relative to Lean's metatheory.
-/

namespace Mettapedia.Logic.Metaphysics

universe u

/-! ## Syntax -/

/-- First-order terms over the Boolean-algebra signature, with `n` free
first-order variables. -/
inductive BATerm (n : ℕ) : Type
  | fvar (i : Fin n) : BATerm n
  | bot : BATerm n
  | top : BATerm n
  | compl (t : BATerm n) : BATerm n
  | inf (t s : BATerm n) : BATerm n
  | sup (t s : BATerm n) : BATerm n

variable {M : Type u} [BooleanAlgebra M]

/-- Evaluation of a term in a Boolean algebra under a first-order valuation. -/
def BATerm.eval (vF : Fin n → M) : BATerm n → M
  | .fvar i => vF i
  | .bot => ⊥
  | .top => ⊤
  | .compl t => (t.eval vF)ᶜ
  | .inf t s => t.eval vF ⊓ s.eval vF
  | .sup t s => t.eval vF ⊔ s.eval vF

@[simp] theorem BATerm.eval_fvar (vF : Fin n → M) (i : Fin n) :
    (BATerm.fvar i).eval vF = vF i := rfl
@[simp] theorem BATerm.eval_bot (vF : Fin n → M) :
    (BATerm.bot).eval vF = ⊥ := rfl
@[simp] theorem BATerm.eval_top (vF : Fin n → M) :
    (BATerm.top).eval vF = ⊤ := rfl
@[simp] theorem BATerm.eval_compl (vF : Fin n → M) (t : BATerm n) :
    (BATerm.compl t).eval vF = (t.eval vF)ᶜ := rfl
@[simp] theorem BATerm.eval_inf (vF : Fin n → M) (t s : BATerm n) :
    (BATerm.inf t s).eval vF = t.eval vF ⊓ s.eval vF := rfl
@[simp] theorem BATerm.eval_sup (vF : Fin n → M) (t s : BATerm n) :
    (BATerm.sup t s).eval vF = t.eval vF ⊔ s.eval vF := rfl

/-- Monadic second-order formulas over the Boolean-algebra signature, with `n` free
first-order and `m` free (monadic) second-order variables. Binders use `Fin.cons`:
the innermost bound variable is index `0`. -/
inductive MSO : ℕ → ℕ → Type
  | eq {n m} (t s : BATerm n) : MSO n m
  | le {n m} (t s : BATerm n) : MSO n m
  | mem {n m} (t : BATerm n) (X : Fin m) : MSO n m
  | fls {n m} : MSO n m
  | imp {n m} (φ ψ : MSO n m) : MSO n m
  | and {n m} (φ ψ : MSO n m) : MSO n m
  | or {n m} (φ ψ : MSO n m) : MSO n m
  | not {n m} (φ : MSO n m) : MSO n m
  | allFO {n m} (φ : MSO (n + 1) m) : MSO n m
  | exFO {n m} (φ : MSO (n + 1) m) : MSO n m
  | allSO {n m} (φ : MSO n (m + 1)) : MSO n m
  | exSO {n m} (φ : MSO n (m + 1)) : MSO n m

/-! ## Relativized satisfaction (one definition, two semantics) -/

/-- Satisfaction of an MSO formula in a Boolean algebra `M`, with second-order
quantifiers relativized to the family `𝒮 : Set (Set M)`. Taking `𝒮 = Set.univ` gives
the **standard (full) semantics**; taking `𝒮` from a `HenkinFamily` gives the
**Henkin (general-model) semantics**. -/
def Sat (𝒮 : Set (Set M)) : ∀ {n m}, (Fin n → M) → (Fin m → Set M) → MSO n m → Prop
  | _, _, vF, _, .eq t s => t.eval vF = s.eval vF
  | _, _, vF, _, .le t s => t.eval vF ≤ s.eval vF
  | _, _, vF, vS, .mem t X => t.eval vF ∈ vS X
  | _, _, _, _, .fls => False
  | _, _, vF, vS, .imp φ ψ => Sat 𝒮 vF vS φ → Sat 𝒮 vF vS ψ
  | _, _, vF, vS, .and φ ψ => Sat 𝒮 vF vS φ ∧ Sat 𝒮 vF vS ψ
  | _, _, vF, vS, .or φ ψ => Sat 𝒮 vF vS φ ∨ Sat 𝒮 vF vS ψ
  | _, _, vF, vS, .not φ => ¬ Sat 𝒮 vF vS φ
  | _, _, vF, vS, .allFO φ => ∀ a : M, Sat 𝒮 (Fin.cons a vF) vS φ
  | _, _, vF, vS, .exFO φ => ∃ a : M, Sat 𝒮 (Fin.cons a vF) vS φ
  | _, _, vF, vS, .allSO φ => ∀ X ∈ 𝒮, Sat 𝒮 vF (Fin.cons X vS) φ
  | _, _, vF, vS, .exSO φ => ∃ X ∈ 𝒮, Sat 𝒮 vF (Fin.cons X vS) φ

section SatSimp

variable {𝒮 : Set (Set M)} {n m : ℕ} (vF : Fin n → M) (vS : Fin m → Set M)

@[simp] theorem sat_eq (t s : BATerm n) :
    Sat 𝒮 vF vS (.eq t s) ↔ t.eval vF = s.eval vF := Iff.rfl
@[simp] theorem sat_le (t s : BATerm n) :
    Sat 𝒮 vF vS (.le t s) ↔ t.eval vF ≤ s.eval vF := Iff.rfl
@[simp] theorem sat_mem (t : BATerm n) (X : Fin m) :
    Sat 𝒮 vF vS (.mem t X) ↔ t.eval vF ∈ vS X := Iff.rfl
@[simp] theorem sat_fls : Sat 𝒮 vF vS (.fls) ↔ False := Iff.rfl
@[simp] theorem sat_imp (φ ψ : MSO n m) :
    Sat 𝒮 vF vS (.imp φ ψ) ↔ (Sat 𝒮 vF vS φ → Sat 𝒮 vF vS ψ) := Iff.rfl
@[simp] theorem sat_and (φ ψ : MSO n m) :
    Sat 𝒮 vF vS (.and φ ψ) ↔ Sat 𝒮 vF vS φ ∧ Sat 𝒮 vF vS ψ := Iff.rfl
@[simp] theorem sat_or (φ ψ : MSO n m) :
    Sat 𝒮 vF vS (.or φ ψ) ↔ Sat 𝒮 vF vS φ ∨ Sat 𝒮 vF vS ψ := Iff.rfl
@[simp] theorem sat_not (φ : MSO n m) :
    Sat 𝒮 vF vS (.not φ) ↔ ¬ Sat 𝒮 vF vS φ := Iff.rfl
@[simp] theorem sat_allFO (φ : MSO (n + 1) m) :
    Sat 𝒮 vF vS (.allFO φ) ↔ ∀ a : M, Sat 𝒮 (Fin.cons a vF) vS φ := Iff.rfl
@[simp] theorem sat_exFO (φ : MSO (n + 1) m) :
    Sat 𝒮 vF vS (.exFO φ) ↔ ∃ a : M, Sat 𝒮 (Fin.cons a vF) vS φ := Iff.rfl
@[simp] theorem sat_allSO (φ : MSO n (m + 1)) :
    Sat 𝒮 vF vS (.allSO φ) ↔ ∀ X ∈ 𝒮, Sat 𝒮 vF (Fin.cons X vS) φ := Iff.rfl
@[simp] theorem sat_exSO (φ : MSO n (m + 1)) :
    Sat 𝒮 vF vS (.exSO φ) ↔ ∃ X ∈ 𝒮, Sat 𝒮 vF (Fin.cons X vS) φ := Iff.rfl

end SatSimp

/-- Satisfaction of a sentence (no free variables of either sort). -/
def SatSentence (𝒮 : Set (Set M)) (φ : MSO 0 0) : Prop :=
  Sat 𝒮 Fin.elim0 Fin.elim0 φ

/-! ## Henkin families (general models) -/

/-- A **Henkin family** on a Boolean algebra `M`: a domain `𝒮` for the second-order
quantifiers, closed under comprehension with parameters of both sorts. Every standard
model is the Henkin model over `Set.univ` (`HenkinFamily.univ`). -/
structure HenkinFamily (M : Type u) [BooleanAlgebra M] : Type u where
  /-- The range of the second-order quantifiers. -/
  family : Set (Set M)
  /-- Comprehension with parameters: every set defined by an MSO formula (over
  parameters of both sorts, the comprehension variable being first-order index `0`)
  belongs to the family. -/
  comprehension : ∀ {n m : ℕ} (φ : MSO (n + 1) m) (vF : Fin n → M) (vS : Fin m → Set M),
    (∀ i, vS i ∈ family) → {a : M | Sat family (Fin.cons a vF) vS φ} ∈ family

/-- The universal family: the standard (full) semantics is a Henkin model. -/
def HenkinFamily.univ (M : Type u) [BooleanAlgebra M] : HenkinFamily M where
  family := Set.univ
  comprehension _ _ _ _ := Set.mem_univ _

@[simp] theorem HenkinFamily.univ_family :
    (HenkinFamily.univ M).family = Set.univ := rfl

/-! ## Formulas without second-order quantifiers do not see the family -/

/-- A formula is second-order-quantifier-free when it contains no `allSO`/`exSO`. -/
def SOQuantFree : ∀ {n m : ℕ}, MSO n m → Prop
  | _, _, .eq _ _ => True
  | _, _, .le _ _ => True
  | _, _, .mem _ _ => True
  | _, _, .fls => True
  | _, _, .imp φ ψ => SOQuantFree φ ∧ SOQuantFree ψ
  | _, _, .and φ ψ => SOQuantFree φ ∧ SOQuantFree ψ
  | _, _, .or φ ψ => SOQuantFree φ ∧ SOQuantFree ψ
  | _, _, .not φ => SOQuantFree φ
  | _, _, .allFO φ => SOQuantFree φ
  | _, _, .exFO φ => SOQuantFree φ
  | _, _, .allSO _ => False
  | _, _, .exSO _ => False

/-- Satisfaction of a second-order-quantifier-free formula is independent of the
quantifier domain. -/
theorem sat_soqf_congr {𝒮 𝒮' : Set (Set M)} :
    ∀ {n m : ℕ} (φ : MSO n m) (_ : SOQuantFree φ) (vF : Fin n → M) (vS : Fin m → Set M),
      Sat 𝒮 vF vS φ ↔ Sat 𝒮' vF vS φ
  | _, _, .eq _ _, _, _, _ => Iff.rfl
  | _, _, .le _ _, _, _, _ => Iff.rfl
  | _, _, .mem _ _, _, _, _ => Iff.rfl
  | _, _, .fls, _, _, _ => Iff.rfl
  | _, _, .imp φ ψ, h, vF, vS =>
      imp_congr (sat_soqf_congr φ h.1 vF vS) (sat_soqf_congr ψ h.2 vF vS)
  | _, _, .and φ ψ, h, vF, vS =>
      and_congr (sat_soqf_congr φ h.1 vF vS) (sat_soqf_congr ψ h.2 vF vS)
  | _, _, .or φ ψ, h, vF, vS =>
      or_congr (sat_soqf_congr φ h.1 vF vS) (sat_soqf_congr ψ h.2 vF vS)
  | _, _, .not φ, h, vF, vS => not_congr (sat_soqf_congr φ h vF vS)
  | _, _, .allFO φ, h, vF, vS =>
      forall_congr' fun a => sat_soqf_congr φ h (Fin.cons a vF) vS
  | _, _, .exFO φ, h, vF, vS =>
      exists_congr fun a => sat_soqf_congr φ h (Fin.cons a vF) vS

/-- **Perspectival latitude (Π¹₁ direction).** A universally-second-order sentence with a
second-order-quantifier-free matrix passes downward from a larger to a smaller quantifier
domain: each Henkin perspective sees fewer sets to refute it. -/
theorem sat_allSO_anti {𝒮 𝒮' : Set (Set M)} (hsub : 𝒮 ⊆ 𝒮') {n m : ℕ}
    (ψ : MSO n (m + 1)) (hψ : SOQuantFree ψ) (vF : Fin n → M) (vS : Fin m → Set M)
    (h : Sat 𝒮' vF vS (.allSO ψ)) : Sat 𝒮 vF vS (.allSO ψ) := by
  intro X hX
  exact (sat_soqf_congr ψ hψ vF (Fin.cons X vS)).mpr (h X (hsub hX))

end Mettapedia.Logic.Metaphysics
