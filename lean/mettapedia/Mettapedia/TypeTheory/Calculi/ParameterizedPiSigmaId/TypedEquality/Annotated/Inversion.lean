import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Validity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Reduction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.AlgorithmSoundness

/-!
# Inversion for the annotated judgment, from injectivity of the type formers

`CFormerFacts` is injectivity and no-confusion of the annotated type formers:
two equal types that are both universes (or other heads), dependent function
types, dependent pair types or identity types have the same former and equal
components. It is the part of the facts about weak-head forms of types
(`Normalization.FormFacts`) that concerns formers, stated for the annotated
calculus. It is a hypothesis here; a model of the annotated calculus supplies it.

From it, as for the unannotated judgment (`Normalization/Preservation.lean`):

* a type usable at a dependent function type is one, with an equal domain and a
  codomain usable at the other's, and a dependent function type is usable only
  at dependent function types (`CBelow.pi_inv`, `CBelow.pi_source`); likewise
  for pair types, which are covariant in both components; a universe is usable
  only at universes cumulatively above it; an identity type only at equal types;
* an abstraction typed at `Π A B` has a domain equal to `A` (`CTyped.lam_inv`);
* **subject reduction** of the head steps of functions and pairs: a head step of
  a typed term is an equality at its type (`CWhStep.equal`);
* a typed term is never stuck: no application of a non-abstraction and no
  projection of a non-pair is typed (`CStuck.not_typed`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open Normalization (LevelModel HeadSame CumulativeAlgebra)
open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {R : Rules Head}

/-! ## The facts -/

/-- The type formers: heads, dependent function and pair types, identity types. -/
inductive CFormer : {n : Nat} → CTm Head n → Prop
  | head {n : Nat} (h : Head) : CFormer (.head h : CTm Head n)
  | pi {n : Nat} (A : CTm Head n) (B : CTm Head (n + 1)) : CFormer (.pi A B)
  | sigma {n : Nat} (A : CTm Head n) (B : CTm Head (n + 1)) : CFormer (.sigma A B)
  | id {n : Nat} (A a b : CTm Head n) : CFormer (.id A a b)

/-- Two type formers with the same former and equal components. -/
def CFormersMatch (P : ChurchRules R) {n : Nat} (Γ : CCtx Head n) (A B : CTm Head n) : Prop :=
  (∃ h h', A = .head h ∧ B = .head h' ∧ HeadSame R h h') ∨
  (∃ A₁ B₁ A₂ B₂, A = .pi A₁ B₁ ∧ B = .pi A₂ B₂ ∧ CTypeEq P Γ A₁ A₂ ∧
    CTypeEq P (.snoc Γ A₁) B₁ B₂) ∨
  (∃ A₁ B₁ A₂ B₂, A = .sigma A₁ B₁ ∧ B = .sigma A₂ B₂ ∧ CTypeEq P Γ A₁ A₂ ∧
    CTypeEq P (.snoc Γ A₁) B₁ B₂) ∨
  (∃ C x y C' x' y', A = .id C x y ∧ B = .id C' x' y' ∧ CTypeEq P Γ C C' ∧
    CEqual P Γ x x' C ∧ CEqual P Γ y y' C)

/-- **Injectivity and no-confusion of the type formers** of the annotated
calculus: equal type formers of a formed context match. -/
structure CFormerFacts (P : ChurchRules R) : Prop where
  forms : ∀ {n : Nat} {Γ : CCtx Head n} {A B : CTm Head n}, CTypeEq P Γ A B →
    CCtxFormed P Γ → CFormer A → CFormer B → CFormersMatch P Γ A B

section Match

variable {P : ChurchRules R} {n : Nat} {Γ : CCtx Head n} {B : CTm Head n}

theorem CFormersMatch.head_left {h : Head} (m : CFormersMatch P Γ (.head h) B) :
    ∃ h', B = .head h' ∧ HeadSame R h h' := by
  rcases m with ⟨_, h', e, rfl, same⟩ | ⟨_, _, _, _, e, _⟩ | ⟨_, _, _, _, e, _⟩ |
    ⟨_, _, _, _, _, _, e, _⟩
  · cases e
    exact ⟨h', rfl, same⟩
  all_goals cases e

theorem CFormersMatch.pi_left {A₁ : CTm Head n} {B₁ : CTm Head (n + 1)}
    (m : CFormersMatch P Γ (.pi A₁ B₁) B) :
    ∃ A₂ B₂, B = .pi A₂ B₂ ∧ CTypeEq P Γ A₁ A₂ ∧ CTypeEq P (.snoc Γ A₁) B₁ B₂ := by
  rcases m with ⟨_, _, e, _⟩ | ⟨_, _, A₂, B₂, e, rfl, eA, eB⟩ | ⟨_, _, _, _, e, _⟩ |
    ⟨_, _, _, _, _, _, e, _⟩
  · cases e
  · cases e
    exact ⟨A₂, B₂, rfl, eA, eB⟩
  all_goals cases e

theorem CFormersMatch.sigma_left {A₁ : CTm Head n} {B₁ : CTm Head (n + 1)}
    (m : CFormersMatch P Γ (.sigma A₁ B₁) B) :
    ∃ A₂ B₂, B = .sigma A₂ B₂ ∧ CTypeEq P Γ A₁ A₂ ∧ CTypeEq P (.snoc Γ A₁) B₁ B₂ := by
  rcases m with ⟨_, _, e, _⟩ | ⟨_, _, _, _, e, _⟩ | ⟨_, _, A₂, B₂, e, rfl, eA, eB⟩ |
    ⟨_, _, _, _, _, _, e, _⟩
  · cases e
  · cases e
  · cases e
    exact ⟨A₂, B₂, rfl, eA, eB⟩
  · cases e

theorem CFormersMatch.id_left {C x y : CTm Head n} (m : CFormersMatch P Γ (.id C x y) B) :
    ∃ C' x' y', B = .id C' x' y' ∧ CTypeEq P Γ C C' ∧ CEqual P Γ x x' C ∧ CEqual P Γ y y' C := by
  rcases m with ⟨_, _, e, _⟩ | ⟨_, _, _, _, e, _⟩ | ⟨_, _, _, _, e, _⟩ |
    ⟨_, _, _, C', x', y', e, rfl, eC, ex, ey⟩
  · cases e
  · cases e
  · cases e
  · cases e
    exact ⟨C', x', y', rfl, eC, ex, ey⟩

end Match

/-! ## Injectivity and discrimination -/

section Consequences

variable {P : ChurchRules R} (facts : CFormerFacts P) {n : Nat} {Γ : CCtx Head n}
include facts

theorem CTypeEq.pi_injective {A A' : CTm Head n} {B B' : CTm Head (n + 1)}
    (equal : CTypeEq P Γ (.pi A B) (.pi A' B')) (formed : CCtxFormed P Γ) :
    CTypeEq P Γ A A' ∧ CTypeEq P (.snoc Γ A) B B' := by
  obtain ⟨_, _, e, eA, eB⟩ := (facts.forms equal formed (.pi _ _) (.pi _ _)).pi_left
  cases e
  exact ⟨eA, eB⟩

theorem CTypeEq.sigma_injective {A A' : CTm Head n} {B B' : CTm Head (n + 1)}
    (equal : CTypeEq P Γ (.sigma A B) (.sigma A' B')) (formed : CCtxFormed P Γ) :
    CTypeEq P Γ A A' ∧ CTypeEq P (.snoc Γ A) B B' := by
  obtain ⟨_, _, e, eA, eB⟩ := (facts.forms equal formed (.sigma _ _) (.sigma _ _)).sigma_left
  cases e
  exact ⟨eA, eB⟩

theorem CTypeEq.id_injective {A A' a a' b b' : CTm Head n}
    (equal : CTypeEq P Γ (.id A a b) (.id A' a' b')) (formed : CCtxFormed P Γ) :
    CTypeEq P Γ A A' ∧ CEqual P Γ a a' A ∧ CEqual P Γ b b' A := by
  obtain ⟨_, _, _, e, eA, ea, eb⟩ := (facts.forms equal formed (.id _ _ _) (.id _ _ _)).id_left
  cases e
  exact ⟨eA, ea, eb⟩

theorem CTypeEq.head_injective {h h' : Head} (equal : CTypeEq P Γ (.head h) (.head h'))
    (formed : CCtxFormed P Γ) : HeadSame R h h' := by
  obtain ⟨_, e, same⟩ := (facts.forms equal formed (.head _) (.head _)).head_left
  cases e
  exact same

theorem CTypeEq.pi_ne_sigma {A A' : CTm Head n} {B B' : CTm Head (n + 1)}
    (formed : CCtxFormed P Γ) : ¬ CTypeEq P Γ (.pi A B) (.sigma A' B') := fun equal => by
  obtain ⟨_, _, e, -⟩ := (facts.forms equal formed (.pi _ _) (.sigma _ _)).pi_left
  cases e

theorem CTypeEq.pi_ne_id {A C a b : CTm Head n} {B : CTm Head (n + 1)}
    (formed : CCtxFormed P Γ) : ¬ CTypeEq P Γ (.pi A B) (.id C a b) := fun equal => by
  obtain ⟨_, _, e, -⟩ := (facts.forms equal formed (.pi _ _) (.id _ _ _)).pi_left
  cases e

theorem CTypeEq.pi_ne_head {A : CTm Head n} {B : CTm Head (n + 1)} {h : Head}
    (formed : CCtxFormed P Γ) : ¬ CTypeEq P Γ (.pi A B) (.head h) := fun equal => by
  obtain ⟨_, _, e, -⟩ := (facts.forms equal formed (.pi _ _) (.head _)).pi_left
  cases e

theorem CTypeEq.sigma_ne_id {A C a b : CTm Head n} {B : CTm Head (n + 1)}
    (formed : CCtxFormed P Γ) : ¬ CTypeEq P Γ (.sigma A B) (.id C a b) := fun equal => by
  obtain ⟨_, _, e, -⟩ := (facts.forms equal formed (.sigma _ _) (.id _ _ _)).sigma_left
  cases e

theorem CTypeEq.sigma_ne_head {A : CTm Head n} {B : CTm Head (n + 1)} {h : Head}
    (formed : CCtxFormed P Γ) : ¬ CTypeEq P Γ (.sigma A B) (.head h) := fun equal => by
  obtain ⟨_, _, e, -⟩ := (facts.forms equal formed (.sigma _ _) (.head _)).sigma_left
  cases e

theorem CTypeEq.id_ne_head {A a b : CTm Head n} {h : Head} (formed : CCtxFormed P Γ) :
    ¬ CTypeEq P Γ (.id A a b) (.head h) := fun equal => by
  obtain ⟨_, _, _, e, -⟩ := (facts.forms equal formed (.id _ _ _) (.head _)).id_left
  cases e

end Consequences

/-! ## Inversion of subtyping -/

section Below

variable {P : ChurchRules R} (facts : CFormerFacts P) (levels : LevelModel R L)
include facts levels

/-- A type usable at a dependent function type is one, with an equal domain and
a codomain usable at the other's. -/
theorem CBelow.pi_inv {n : Nat} {Γ : CCtx Head n} {X T : CTm Head n} (le : CBelow P Γ X T)
    (formed : CCtxFormed P Γ) {A' : CTm Head n} {B' : CTm Head (n + 1)}
    (eT : CTypeEq P Γ T (.pi A' B')) :
    ∃ A B, CTypeEq P Γ X (.pi A B) ∧ CTypeEq P Γ A A' ∧ CBelow P (.snoc Γ A) B B' := by
  refine CBelow.induction (motive := fun n Γ X T => CCtxFormed P Γ →
      ∀ {A' : CTm Head n} {B' : CTm Head (n + 1)}, CTypeEq P Γ T (.pi A' B') →
        ∃ A B, CTypeEq P Γ X (.pi A B) ∧ CTypeEq P Γ A A' ∧ CBelow P (.snoc Γ A) B B')
    ?equal ?univ ?pi ?sigma ?trans le formed eT
  case equal =>
    intro n Γ X T u e hu formed A' B' eT
    have eX : CTypeEq P Γ X (.pi A' B') := CTypeEq.trans levels ⟨u, hu, e⟩ eT
    obtain ⟨typeA, typeB⟩ := CIsType.pi_parts (CTypeEq.isType levels eT formed).2
    exact ⟨A', B', eX, CIsType.refl typeA, CIsType.below_refl typeB⟩
  case univ =>
    intro n Γ u v _ formed A' B' eT
    exact absurd eT.symm (CTypeEq.pi_ne_head facts formed)
  case pi =>
    intro n Γ A A₁ B B₁ u u₁ w tPi hu _ _ eA hw leB _ formed A' B' eT
    obtain ⟨eA', eB'⟩ := CTypeEq.pi_injective facts eT formed
    have eAA₁ : CTypeEq P Γ A A₁ := ⟨w, hw, eA⟩
    exact ⟨A, B, CIsType.refl ⟨u, hu, tPi⟩, CTypeEq.trans levels eAA₁ eA',
      .subTrans leB (CBelow.ctxConv eB'.below eAA₁.symm)⟩
  case sigma =>
    intro n Γ A A₁ B B₁ u u₁ _ _ _ _ _ _ _ _ formed A' B' eT
    exact absurd eT.symm (CTypeEq.pi_ne_sigma facts formed)
  case trans =>
    intro n Γ X Y T _ _ ih₁ ih₂ formed A' B' eT
    obtain ⟨A₁, B₁, eY, eA₁, leB₁⟩ := ih₂ formed eT
    obtain ⟨A₀, B₀, eX, eA₀, leB₀⟩ := ih₁ formed eY
    exact ⟨A₀, B₀, eX, CTypeEq.trans levels eA₀ eA₁,
      .subTrans leB₀ (CBelow.ctxConv leB₁ eA₀.symm)⟩

/-- A type usable at a dependent pair type is one, with a domain and a codomain
usable at the other's. -/
theorem CBelow.sigma_inv {n : Nat} {Γ : CCtx Head n} {X T : CTm Head n} (le : CBelow P Γ X T)
    (formed : CCtxFormed P Γ) {A' : CTm Head n} {B' : CTm Head (n + 1)}
    (eT : CTypeEq P Γ T (.sigma A' B')) :
    ∃ A B, CTypeEq P Γ X (.sigma A B) ∧ CBelow P Γ A A' ∧ CBelow P (.snoc Γ A) B B' := by
  refine CBelow.induction (motive := fun n Γ X T => CCtxFormed P Γ →
      ∀ {A' : CTm Head n} {B' : CTm Head (n + 1)}, CTypeEq P Γ T (.sigma A' B') →
        ∃ A B, CTypeEq P Γ X (.sigma A B) ∧ CBelow P Γ A A' ∧ CBelow P (.snoc Γ A) B B')
    ?equal ?univ ?pi ?sigma ?trans le formed eT
  case equal =>
    intro n Γ X T u e hu formed A' B' eT
    have eX : CTypeEq P Γ X (.sigma A' B') := CTypeEq.trans levels ⟨u, hu, e⟩ eT
    obtain ⟨typeA, typeB⟩ := CIsType.sigma_parts (CTypeEq.isType levels eT formed).2
    exact ⟨A', B', eX, CIsType.below_refl typeA, CIsType.below_refl typeB⟩
  case univ =>
    intro n Γ u v _ formed A' B' eT
    exact absurd eT.symm (CTypeEq.sigma_ne_head facts formed)
  case pi =>
    intro n Γ A A₁ B B₁ u u₁ w _ _ _ _ _ _ _ _ formed A' B' eT
    exact absurd eT (CTypeEq.pi_ne_sigma facts formed)
  case sigma =>
    intro n Γ A A₁ B B₁ u u₁ tS hu _ _ leA leB _ _ formed A' B' eT
    obtain ⟨eA', eB'⟩ := CTypeEq.sigma_injective facts eT formed
    exact ⟨A, B, CIsType.refl ⟨u, hu, tS⟩, .subTrans leA eA'.below,
      .subTrans leB (CBelow.ctxBelow eB'.below leA)⟩
  case trans =>
    intro n Γ X Y T _ _ ih₁ ih₂ formed A' B' eT
    obtain ⟨A₁, B₁, eY, leA₁, leB₁⟩ := ih₂ formed eT
    obtain ⟨A₀, B₀, eX, leA₀, leB₀⟩ := ih₁ formed eY
    exact ⟨A₀, B₀, eX, .subTrans leA₀ leA₁, .subTrans leB₀ (CBelow.ctxBelow leB₁ leA₀)⟩

/-- A dependent function type is usable only at dependent function types with
an equal domain and a codomain its own is usable at. -/
theorem CBelow.pi_source {n : Nat} {Γ : CCtx Head n} {X T : CTm Head n} (le : CBelow P Γ X T)
    (formed : CCtxFormed P Γ) {A : CTm Head n} {B : CTm Head (n + 1)}
    (eX : CTypeEq P Γ X (.pi A B)) :
    ∃ A' B', CTypeEq P Γ T (.pi A' B') ∧ CTypeEq P Γ A A' ∧ CBelow P (.snoc Γ A) B B' := by
  refine CBelow.induction (motive := fun n Γ X T => CCtxFormed P Γ →
      ∀ {A : CTm Head n} {B : CTm Head (n + 1)}, CTypeEq P Γ X (.pi A B) →
        ∃ A' B', CTypeEq P Γ T (.pi A' B') ∧ CTypeEq P Γ A A' ∧ CBelow P (.snoc Γ A) B B')
    ?equal ?univ ?pi ?sigma ?trans le formed eX
  case equal =>
    intro n Γ X T u e hu formed A B eX
    have eT : CTypeEq P Γ T (.pi A B) := CTypeEq.trans levels (CTypeEq.symm ⟨u, hu, e⟩) eX
    obtain ⟨typeA, typeB⟩ := CIsType.pi_parts (CTypeEq.isType levels eX formed).2
    exact ⟨A, B, eT, CIsType.refl typeA, CIsType.below_refl typeB⟩
  case univ =>
    intro n Γ u v _ formed A B eX
    exact absurd eX.symm (CTypeEq.pi_ne_head facts formed)
  case pi =>
    intro n Γ A₀ A₁ B₀ B₁ u u₁ w _ _ tPi₁ hu₁ eA hw leB _ formed A B eX
    obtain ⟨eA₀, eB₀⟩ := CTypeEq.pi_injective facts eX formed
    have eA₀₁ : CTypeEq P Γ A₀ A₁ := ⟨w, hw, eA⟩
    exact ⟨A₁, B₁, CIsType.refl ⟨u₁, hu₁, tPi₁⟩, CTypeEq.trans levels eA₀.symm eA₀₁,
      CBelow.ctxConv (CDerivable.subTrans eB₀.symm.below leB) eA₀⟩
  case sigma =>
    intro n Γ A₀ A₁ B₀ B₁ u u₁ _ _ _ _ _ _ _ _ formed A B eX
    exact absurd eX (CTypeEq.pi_ne_sigma facts formed ∘ CTypeEq.symm)
  case trans =>
    intro n Γ X Y T _ _ ih₁ ih₂ formed A B eX
    obtain ⟨A₁, B₁, eY, eA₁, leB₁⟩ := ih₁ formed eX
    obtain ⟨A₂, B₂, eT, eA₂, leB₂⟩ := ih₂ formed eY
    exact ⟨A₂, B₂, eT, CTypeEq.trans levels eA₁ eA₂,
      .subTrans leB₁ (CBelow.ctxConv leB₂ eA₁.symm)⟩

/-- A dependent pair type is usable only at dependent pair types with a domain
and a codomain its own are usable at. -/
theorem CBelow.sigma_source {n : Nat} {Γ : CCtx Head n} {X T : CTm Head n} (le : CBelow P Γ X T)
    (formed : CCtxFormed P Γ) {A : CTm Head n} {B : CTm Head (n + 1)}
    (eX : CTypeEq P Γ X (.sigma A B)) :
    ∃ A' B', CTypeEq P Γ T (.sigma A' B') ∧ CBelow P Γ A A' ∧ CBelow P (.snoc Γ A) B B' := by
  refine CBelow.induction (motive := fun n Γ X T => CCtxFormed P Γ →
      ∀ {A : CTm Head n} {B : CTm Head (n + 1)}, CTypeEq P Γ X (.sigma A B) →
        ∃ A' B', CTypeEq P Γ T (.sigma A' B') ∧ CBelow P Γ A A' ∧ CBelow P (.snoc Γ A) B B')
    ?equal ?univ ?pi ?sigma ?trans le formed eX
  case equal =>
    intro n Γ X T u e hu formed A B eX
    have eT : CTypeEq P Γ T (.sigma A B) := CTypeEq.trans levels (CTypeEq.symm ⟨u, hu, e⟩) eX
    obtain ⟨typeA, typeB⟩ := CIsType.sigma_parts (CTypeEq.isType levels eX formed).2
    exact ⟨A, B, eT, CIsType.below_refl typeA, CIsType.below_refl typeB⟩
  case univ =>
    intro n Γ u v _ formed A B eX
    exact absurd eX.symm (CTypeEq.sigma_ne_head facts formed)
  case pi =>
    intro n Γ A₀ A₁ B₀ B₁ u u₁ w _ _ _ _ _ _ _ _ formed A B eX
    exact absurd eX (CTypeEq.pi_ne_sigma facts formed)
  case sigma =>
    intro n Γ A₀ A₁ B₀ B₁ u u₁ _ _ tS₁ hu₁ leA leB _ _ formed A B eX
    obtain ⟨eA₀, eB₀⟩ := CTypeEq.sigma_injective facts eX formed
    exact ⟨A₁, B₁, CIsType.refl ⟨u₁, hu₁, tS₁⟩, .subTrans eA₀.symm.below leA,
      CBelow.ctxConv (CDerivable.subTrans eB₀.symm.below leB) eA₀⟩
  case trans =>
    intro n Γ X Y T _ _ ih₁ ih₂ formed A B eX
    obtain ⟨A₁, B₁, eY, leA₁, leB₁⟩ := ih₁ formed eX
    obtain ⟨A₂, B₂, eT, leA₂, leB₂⟩ := ih₂ formed eY
    exact ⟨A₂, B₂, eT, .subTrans leA₁ leA₂, .subTrans leB₁ (CBelow.ctxBelow leB₂ leA₁)⟩

/-- A universe is usable only at universes cumulatively above it. -/
theorem CBelow.universe_cumulative (algebra : CumulativeAlgebra R) {n : Nat} {Γ : CCtx Head n}
    {X T : CTm Head n} (le : CBelow P Γ X T) (formed : CCtxFormed P Γ) {w : Head}
    (hw : R.isUniverse w) (eX : CTypeEq P Γ X (.head w)) :
    ∃ v, R.isUniverse v ∧ CTypeEq P Γ T (.head v) ∧ R.cumulative w v := by
  refine CBelow.induction (motive := fun n Γ X T => CCtxFormed P Γ → ∀ {w : Head},
      R.isUniverse w → CTypeEq P Γ X (.head w) →
        ∃ v, R.isUniverse v ∧ CTypeEq P Γ T (.head v) ∧ R.cumulative w v)
    ?equal ?univ ?pi ?sigma ?trans le formed hw eX
  case equal =>
    intro n Γ X T u e hu formed w hw eX
    exact ⟨w, hw, CTypeEq.trans levels (CTypeEq.symm ⟨u, hu, e⟩) eX, levels.cumulative_refl hw⟩
  case univ =>
    intro n Γ u₀ v₀ c formed w hw eX
    have same := CTypeEq.head_injective facts eX formed
    obtain ⟨_, hv₀, _⟩ := levels.cumulative_universe c
    exact ⟨v₀, hv₀, CIsType.refl (CIsType.head_of_universe levels hv₀),
      algebra.same_left (HeadSame.symm levels same) c⟩
  case pi =>
    intro n Γ A₀ A₁ B₀ B₁ _ _ _ _ _ _ _ _ _ _ _ formed w hw eX
    exact absurd eX (CTypeEq.pi_ne_head facts formed)
  case sigma =>
    intro n Γ A₀ A₁ B₀ B₁ _ _ _ _ _ _ _ _ _ _ formed w hw eX
    exact absurd eX (CTypeEq.sigma_ne_head facts formed)
  case trans =>
    intro n Γ X Y T _ _ ih₁ ih₂ formed w hw eX
    obtain ⟨v₁, hv₁, eY, c₁⟩ := ih₁ formed hw eX
    obtain ⟨v, hv, eT, c₂⟩ := ih₂ formed hv₁ eY
    exact ⟨v, hv, eT, algebra.trans c₁ c₂⟩

/-- An identity type is usable only at types equal to it. -/
theorem CBelow.id_eq {n : Nat} {Γ : CCtx Head n} {X T : CTm Head n} (le : CBelow P Γ X T)
    (formed : CCtxFormed P Γ) {C a b : CTm Head n} (eX : CTypeEq P Γ X (.id C a b)) :
    CTypeEq P Γ T (.id C a b) := by
  refine CBelow.induction (motive := fun n Γ X T => CCtxFormed P Γ →
      ∀ {C a b : CTm Head n}, CTypeEq P Γ X (.id C a b) → CTypeEq P Γ T (.id C a b))
    ?equal ?univ ?pi ?sigma ?trans le formed eX
  case equal =>
    intro n Γ X T u e hu formed C a b eX
    exact CTypeEq.trans levels (CTypeEq.symm ⟨u, hu, e⟩) eX
  case univ =>
    intro n Γ u v _ formed C a b eX
    exact absurd eX.symm (CTypeEq.id_ne_head facts formed)
  case pi =>
    intro n Γ A₀ A₁ B₀ B₁ _ _ _ _ _ _ _ _ _ _ _ formed C a b eX
    exact absurd eX (CTypeEq.pi_ne_id facts formed)
  case sigma =>
    intro n Γ A₀ A₁ B₀ B₁ _ _ _ _ _ _ _ _ _ _ formed C a b eX
    exact absurd eX (CTypeEq.sigma_ne_id facts formed)
  case trans =>
    intro n Γ X Y T _ _ ih₁ ih₂ formed C a b eX
    exact ih₂ formed (ih₁ formed eX)

/-- A chain from a dependent function type to another relates their domains by
equality and their codomains by subtyping. -/
theorem CBelow.pi_parts {n : Nat} {Γ : CCtx Head n} {A A₁ : CTm Head n}
    {B B₁ : CTm Head (n + 1)} (le : CBelow P Γ (.pi A B) (.pi A₁ B₁))
    (formed : CCtxFormed P Γ) : CTypeEq P Γ A A₁ ∧ CBelow P (.snoc Γ A) B B₁ := by
  have type₁ := (CBelow.isTypes levels le formed).2
  obtain ⟨A₀, B₀, eX, eA, leB⟩ := CBelow.pi_inv facts levels le formed (CIsType.refl type₁)
  obtain ⟨eA', eB'⟩ := CTypeEq.pi_injective facts eX formed
  exact ⟨CTypeEq.trans levels eA' eA, .subTrans eB'.below (CBelow.ctxConv leB eA'.symm)⟩

/-- A chain from a dependent pair type to another relates their domains and
their codomains by subtyping. -/
theorem CBelow.sigma_parts {n : Nat} {Γ : CCtx Head n} {A A₁ : CTm Head n}
    {B B₁ : CTm Head (n + 1)} (le : CBelow P Γ (.sigma A B) (.sigma A₁ B₁))
    (formed : CCtxFormed P Γ) : CBelow P Γ A A₁ ∧ CBelow P (.snoc Γ A) B B₁ := by
  have type₁ := (CBelow.isTypes levels le formed).2
  obtain ⟨A₀, B₀, eX, leA, leB⟩ := CBelow.sigma_inv facts levels le formed (CIsType.refl type₁)
  obtain ⟨eA', eB'⟩ := CTypeEq.sigma_injective facts eX formed
  exact ⟨.subTrans eA'.below leA, .subTrans eB'.below (CBelow.ctxConv leB eA'.symm)⟩

end Below

/-! ## Inversion of typings of introductions -/

section Introductions

variable {P : ChurchRules R} (facts : CFormerFacts P) (levels : LevelModel R L)
include facts levels

/-- An abstraction typed at a dependent function type has a domain equal to the
type's, and a body typed at the codomain. -/
theorem CTyped.lam_inv {n : Nat} {Γ : CCtx Head n} {D A : CTm Head n}
    {body B : CTm Head (n + 1)} (typing : CTyped P Γ (.lam D body) (.pi A B))
    (formed : CCtxFormed P Γ) :
    CTypeEq P Γ D A ∧ CTyped P (.snoc Γ A) body B := by
  obtain ⟨E, u, w, _, _, tPi, hu, tb, le⟩ := typing.generation
  have below := CTypeLe.toBelow le (CTyped.isType levels typing formed)
  obtain ⟨eD, leE⟩ := CBelow.pi_parts facts levels below formed
  exact ⟨eD, CTyped.ctxConv (.sub tb leE) eD⟩

/-- A pair typed at a dependent pair type has typed components. -/
theorem CTyped.pair_inv {n : Nat} {Γ : CCtx Head n} {A a b : CTm Head n} {B : CTm Head (n + 1)}
    (typing : CTyped P Γ (.pair a b) (.sigma A B)) (formed : CCtxFormed P Γ) :
    CTyped P Γ a A ∧ CTyped P Γ b (CTm.inst0 a B) := by
  obtain ⟨A', B', u, tS, hu, ta, tb, le⟩ := typing.generation
  have below := CTypeLe.toBelow le (CTyped.isType levels typing formed)
  obtain ⟨leA, leB⟩ := CBelow.sigma_parts facts levels below formed
  exact ⟨.sub ta leA, .sub tb (CBelow.instantiate leB ta)⟩

end Introductions

/-! ## Subject reduction of head steps -/

section Contractions

variable {P : ChurchRules R} (facts : CFormerFacts P) (levels : LevelModel R L)
include facts levels

theorem CTyped.beta_equal {n : Nat} {Γ : CCtx Head n} {D a T : CTm Head n}
    {body : CTm Head (n + 1)} (formed : CCtxFormed P Γ)
    (typing : CTyped P Γ (.app (.lam D body) a) T) :
    CEqual P Γ (.app (.lam D body) a) (CTm.inst0 a body) T := by
  obtain ⟨A, B, tf, ta, le⟩ := typing.generation
  obtain ⟨E, u, w, _, _, tPi, hu, tb, leF⟩ := tf.generation
  have below := CTypeLe.toBelow leF (CTyped.isType levels tf formed)
  obtain ⟨eD, leE⟩ := CBelow.pi_parts facts levels below formed
  have taD : CTyped P Γ a D := CTyped.convType ta eD.symm
  exact CEqual.subsume (.subEq (.betaPi tPi hu tb taD) (CBelow.instantiate leE taD)) le

theorem CTyped.fstPair_equal {n : Nat} {Γ : CCtx Head n} {a b T : CTm Head n}
    (formed : CCtxFormed P Γ) (typing : CTyped P Γ (.fst (.pair a b)) T) :
    CEqual P Γ (.fst (.pair a b)) a T := by
  obtain ⟨A, B, tp, le⟩ := typing.generation
  obtain ⟨ta, tb⟩ := CTyped.pair_inv facts levels tp formed
  obtain ⟨w, hw, tS⟩ := CTyped.isType levels tp formed
  exact CEqual.subsume (.betaFst tS hw ta tb) le

theorem CTyped.sndPair_equal {n : Nat} {Γ : CCtx Head n} {a b T : CTm Head n}
    (formed : CCtxFormed P Γ) (typing : CTyped P Γ (.snd (.pair a b)) T) :
    CEqual P Γ (.snd (.pair a b)) b T := by
  obtain ⟨A, B, tp, le⟩ := typing.generation
  obtain ⟨ta, tb⟩ := CTyped.pair_inv facts levels tp formed
  obtain ⟨w, hw, tS⟩ := CTyped.isType levels tp formed
  obtain ⟨_, family⟩ := CIsType.sigma_parts ⟨w, hw, tS⟩
  have change : CTypeEq P Γ (CTm.inst0 a B) (CTm.inst0 (.fst (.pair a b)) B) :=
    CIsType.instantiateEq family ta (.symm (.betaFst tS hw ta tb))
  exact CEqual.subsume (CEqual.convType (.betaSnd tS hw ta tb) change) le

/-- **Subject reduction** of the head steps of functions and pairs: a head step
of a typed term is an equality at its type. -/
theorem CWhStep.equal {n : Nat} {Γ : CCtx Head n} {t u T : CTm Head n}
    (formed : CCtxFormed P Γ) (step : CWhStep t u) (typing : CTyped P Γ t T) :
    CEqual P Γ t u T := by
  induction step generalizing T with
  | beta D body a => exact CTyped.beta_equal facts levels formed typing
  | fstPair a b => exact CTyped.fstPair_equal facts levels formed typing
  | sndPair a b => exact CTyped.sndPair_equal facts levels formed typing
  | appFun _ ih =>
      obtain ⟨A, B, tf, ta, le⟩ := typing.generation
      exact CEqual.subsume (.appCong (ih tf) (.refl ta)) le
  | fst _ ih =>
      obtain ⟨A, B, tp, le⟩ := typing.generation
      exact CEqual.subsume (.fstCong (ih tp)) le
  | snd _ ih =>
      obtain ⟨A, B, tp, le⟩ := typing.generation
      exact CEqual.subsume (.sndCong (ih tp)) le

end Contractions

/-! ## Typed terms are not stuck -/

section Stuck

variable {P : ChurchRules R} (facts : CFormerFacts P) (levels : LevelModel R L)
  (algebra : CumulativeAlgebra R)
include facts levels algebra

/-- The type of an introduction or a type former is below a dependent function
type only for an abstraction. -/
private theorem intro_not_below_pi {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {f A : CTm Head n} {B : CTm Head (n + 1)} (intro : CIntro f) (notLam : ∀ D b, f ≠ .lam D b)
    (typing : CTyped P Γ f (.pi A B)) : False := by
  have typePi := CTyped.isType levels typing formed
  have universeCase : ∀ {w : Head}, R.isUniverse w → CTypeLe P Γ (.head w) (.pi A B) → False :=
    fun hw le => by
      obtain ⟨v, _, e, _⟩ := CBelow.universe_cumulative facts levels algebra
        (CTypeLe.toBelow le typePi) formed hw (CIsType.refl (CIsType.head_of_universe levels hw))
      exact CTypeEq.pi_ne_head facts formed e
  cases intro with
  | head h =>
      obtain ⟨u, typing', le⟩ := typing.generation
      exact universeCase (levels.ground_typing typing') le
  | pi D E =>
      obtain ⟨_, _, _, _, _, _, _, join, le⟩ := typing.generation
      exact universeCase (levels.join_level join).1 le
  | sigma D E =>
      obtain ⟨_, _, _, _, _, _, _, join, le⟩ := typing.generation
      exact universeCase (levels.join_level join).1 le
  | id C x y =>
      obtain ⟨_, _, hu, _, _, le⟩ := typing.generation
      exact universeCase hu le
  | lam D b => exact notLam D b rfl
  | pair x y =>
      obtain ⟨D, E, u, tS, hu, _, _, le⟩ := typing.generation
      obtain ⟨_, _, e, _⟩ := CBelow.sigma_source facts levels (CTypeLe.toBelow le typePi) formed
        (CIsType.refl ⟨u, hu, tS⟩)
      exact CTypeEq.pi_ne_sigma facts formed e
  | refl x =>
      obtain ⟨D, tx, le⟩ := typing.generation
      have e := CBelow.id_eq facts levels (CTypeLe.toBelow le typePi) formed
        (CIsType.refl (CTyped.isType levels (.reflIntro tx) formed))
      exact CTypeEq.pi_ne_id facts formed e

/-- The type of an introduction or a type former is below a dependent pair type
only for a pair. -/
private theorem intro_not_below_sigma {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {p A : CTm Head n} {B : CTm Head (n + 1)} (intro : CIntro p) (notPair : ∀ a b, p ≠ .pair a b)
    (typing : CTyped P Γ p (.sigma A B)) : False := by
  have typeSigma := CTyped.isType levels typing formed
  have universeCase : ∀ {w : Head}, R.isUniverse w → CTypeLe P Γ (.head w) (.sigma A B) →
      False := fun hw le => by
    obtain ⟨v, _, e, _⟩ := CBelow.universe_cumulative facts levels algebra
      (CTypeLe.toBelow le typeSigma) formed hw (CIsType.refl (CIsType.head_of_universe levels hw))
    exact CTypeEq.sigma_ne_head facts formed e
  cases intro with
  | head h =>
      obtain ⟨u, typing', le⟩ := typing.generation
      exact universeCase (levels.ground_typing typing') le
  | pi D E =>
      obtain ⟨_, _, _, _, _, _, _, join, le⟩ := typing.generation
      exact universeCase (levels.join_level join).1 le
  | sigma D E =>
      obtain ⟨_, _, _, _, _, _, _, join, le⟩ := typing.generation
      exact universeCase (levels.join_level join).1 le
  | id C x y =>
      obtain ⟨_, _, hu, _, _, le⟩ := typing.generation
      exact universeCase hu le
  | lam D b =>
      obtain ⟨E, u, _, _, _, tPi, hu, _, le⟩ := typing.generation
      obtain ⟨_, _, e, _⟩ := CBelow.pi_source facts levels (CTypeLe.toBelow le typeSigma) formed
        (CIsType.refl ⟨u, hu, tPi⟩)
      exact CTypeEq.pi_ne_sigma facts formed e.symm
  | pair x y => exact notPair x y rfl
  | refl x =>
      obtain ⟨D, tx, le⟩ := typing.generation
      have e := CBelow.id_eq facts levels (CTypeLe.toBelow le typeSigma) formed
        (CIsType.refl (CTyped.isType levels (.reflIntro tx) formed))
      exact CTypeEq.sigma_ne_id facts formed e

/-- **Typed terms are not stuck.** -/
theorem CStuck.not_typed {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {t T : CTm Head n} (stuck : CStuck t) (typing : CTyped P Γ t T) : False := by
  induction stuck generalizing T with
  | app intro notLam =>
      obtain ⟨_, _, tf, _, _⟩ := typing.generation
      exact intro_not_below_pi facts levels algebra formed intro notLam tf
  | fst intro notPair =>
      obtain ⟨_, _, tp, _⟩ := typing.generation
      exact intro_not_below_sigma facts levels algebra formed intro notPair tp
  | snd intro notPair =>
      obtain ⟨_, _, tp, _⟩ := typing.generation
      exact intro_not_below_sigma facts levels algebra formed intro notPair tp
  | appStuck _ ih =>
      obtain ⟨_, _, tf, _, _⟩ := typing.generation
      exact ih tf
  | fstStuck _ ih =>
      obtain ⟨_, _, tp, _⟩ := typing.generation
      exact ih tp
  | sndStuck _ ih =>
      obtain ⟨_, _, tp, _⟩ := typing.generation
      exact ih tp

end Stuck

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
