import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentOccursFullUnder

/-!
# Decomposing type formers under abstractions

R94 decomposed type formers at a universe only. A store equation of the dynamic pattern fragment may
compare formers **under abstractions**: `λ x̄. Π B C ≐ λ x̄. Π B' C'` at `Π x̄. U`. Equal abstractions
have equal bodies (`lam_equal_inv`), and the bodies decompose at the universe, so the equation has
exactly the solutions of its **pieces**, each closed again under the abstractions:

* Π and Σ: `λ x̄. B ≐ λ x̄. B'` at `Π x̄. U`, and the family twin `λ x̄ y. C : Π x̄. Π B U` against
  `λ x̄ y. C' : Π x̄. Π B' U`;
* identity types: the carriers at `Π x̄. U`, and each endpoint pair, each endpoint at its own
  carrier under the abstractions;
* pairs at `Π x̄. Σ A B`: the first components at `Π x̄. A`, and the second components, each at the
  family instantiated at its own first component under the abstractions.

`underParts` reads the pieces from the codes (`Piece`), with no budget; the pieces are typed
(`underParts_typed`), the reading is kept by substitution (`underParts_subst`), it is exact at every
formed context (`underParts_exact`), and the pieces weigh two less in normal weight than the
equation (`underParts_weight`): abstractions weigh nothing, and the normal form of `λ x̄. F` is
`λ x̄. N` for the normal form `N` of `F`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSpinesMany

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentFragment ContextualDependentInPlace
open ContextualDependentRigidFormers ContextualDependentEtaLong ContextualDependentOccursCheck
open ContextualDependentRank ContextualDependentOccursFull

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Pieces -/

/-- **A piece of a decomposition**: an equation between two judged terms, each at its own type. -/
structure Piece (Head : Type) (n : Nat) where
  leftType : Tm Head n
  left : Tm Head n
  rightType : Tm Head n
  right : Tm Head n

namespace Piece

/-- Close a piece under one abstraction. -/
def under {n : Nat} (D : Tm Head n) (piece : Piece Head (n + 1)) : Piece Head n :=
  ⟨.pi D piece.leftType, .lam piece.left, .pi D piece.rightType, .lam piece.right⟩

/-- Substitute into a piece. -/
def subst {n m : Nat} (σ : Sub Head n m) (piece : Piece Head n) : Piece Head m :=
  ⟨Presentation.subst σ piece.leftType, Presentation.subst σ piece.left, Presentation.subst σ piece.rightType,
    Presentation.subst σ piece.right⟩

/-- A piece holds: its types are equal and its terms are equal. -/
def Holds (R : Rules Head) {n : Nat} (Γ : Ctx Head n) (piece : Piece Head n) : Prop :=
  TypeEq R Γ piece.leftType piece.rightType ∧ Equal R Γ piece.left piece.right piece.leftType

/-- Both terms of a piece have their types. -/
def Typed (R : Rules Head) {n : Nat} (Γ : Ctx Head n) (piece : Piece Head n) : Prop :=
  TypedEquality.Typed R Γ piece.left piece.leftType ∧ TypedEquality.Typed R Γ piece.right piece.rightType

theorem subst_under {n m : Nat} (σ : Sub Head n m) (D : Tm Head n) (piece : Piece Head (n + 1)) :
    (piece.under D).subst σ = (piece.subst (liftSub σ)).under (Presentation.subst σ D) := rfl

end Piece

/-! ## Reading the pieces -/

/-- The pieces of an equation between two formers at a universe. -/
def baseParts {n : Nat} (u : Head) : Tm Head n → Tm Head n → Option (List (Piece Head n))
  | .pi B C, .pi B' C' => some [⟨.head u, B, .head u, B'⟩, ⟨.pi B (.head u), .lam C, .pi B' (.head u), .lam C'⟩]
  | .sigma B C, .sigma B' C' => some [⟨.head u, B, .head u, B'⟩, ⟨.pi B (.head u), .lam C, .pi B' (.head u), .lam C'⟩]
  | .id C a b, .id C' a' b' => some [⟨.head u, C, .head u, C'⟩, ⟨C, a, C', a'⟩, ⟨C, b, C', b'⟩]
  | _, _ => none

variable [∀ head, Decidable (S.R.isUniverse head)]

/-- **The pieces of an equation between formers under abstractions**, read from the annotation and the
two sides; no budget. -/
def underParts : {n : Nat} → Tm Head n → Tm Head n → Tm Head n → Option (List (Piece Head n))
  | _, .head u, left, right => if S.R.isUniverse u then baseParts u left right else none
  | _, .sigma A B, .pair a b, .pair a' b' => some [⟨A, a, A, a'⟩, ⟨inst0 a B, b, inst0 a' B, b'⟩]
  | _, .pi D T, .lam left, .lam right => (underParts T left right).map (List.map (Piece.under D))
  | _, _, _, _ => none

/-- **At a Σ annotation the reading accepts pairs only.** -/
theorem underParts_sigma_cases {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)} {left right : Tm Head n}
    {pieces : List (Piece Head n)} (found : underParts (S := S) (.sigma A B) left right = some pieces) :
    ∃ a b a' b', left = .pair a b ∧ right = .pair a' b' ∧
      pieces = [⟨A, a, A, a'⟩, ⟨inst0 a B, b, inst0 a' B, b'⟩] := by
  cases left with
  | pair a b =>
      cases right with
      | pair a' b' =>
          simp only [underParts, Option.some.injEq] at found
          exact ⟨a, b, a', b', rfl, rfl, found.symm⟩
      | _ => simp [underParts] at found
  | _ => simp [underParts] at found

theorem underParts_head {n : Nat} {u : Head} {left right : Tm Head n} {pieces : List (Piece Head n)}
    (found : underParts (S := S) (.head u) left right = some pieces) :
    S.R.isUniverse u ∧ baseParts u left right = some pieces := by
  unfold underParts at found
  split at found
  · rename_i universal
    exact ⟨universal, found⟩
  · cases found

theorem underParts_pi {n : Nat} {D : Tm Head n} {T left right : Tm Head (n + 1)} {pieces : List (Piece Head n)}
    (found : underParts (S := S) (.pi D T) (.lam left) (.lam right) = some pieces) :
    ∃ inner, underParts (S := S) T left right = some inner ∧ pieces = inner.map (Piece.under D) := by
  simp only [underParts] at found
  obtain ⟨inner, computed, rfl⟩ := Option.map_eq_some_iff.mp found
  exact ⟨inner, computed, rfl⟩

/-- **At a Π annotation the reading accepts abstractions only.** -/
theorem underParts_pi_cases {n : Nat} {D : Tm Head n} {T : Tm Head (n + 1)} {left right : Tm Head n}
    {pieces : List (Piece Head n)} (found : underParts (S := S) (.pi D T) left right = some pieces) :
    ∃ l r inner, left = .lam l ∧ right = .lam r ∧ underParts (S := S) T l r = some inner ∧
      pieces = inner.map (Piece.under D) := by
  cases left with
  | lam l =>
      cases right with
      | lam r =>
          obtain ⟨inner, computed, rfl⟩ := underParts_pi found
          exact ⟨l, r, inner, rfl, rfl, computed, rfl⟩
      | _ => simp [underParts] at found
  | _ => simp [underParts] at found

/-- **The reading is kept by substitution.** -/
theorem underParts_subst : ∀ {n : Nat} (annotation left right : Tm Head n) {pieces : List (Piece Head n)},
    underParts (S := S) annotation left right = some pieces →
    ∀ {m : Nat} (σ : Sub Head n m),
      underParts (S := S) (Presentation.subst σ annotation) (Presentation.subst σ left)
        (Presentation.subst σ right) = some (pieces.map (Piece.subst σ))
  | _, .head u, left, right, pieces, found, _, σ => by
      obtain ⟨universal, base⟩ := underParts_head found
      have shaped : ∀ {left right : Tm Head _} {pieces : List (Piece Head _)}, baseParts u left right = some pieces →
          baseParts u (Presentation.subst σ left) (Presentation.subst σ right) = some (pieces.map (Piece.subst σ)) := by
        intro left right pieces base
        cases left <;> cases right <;> simp only [baseParts, reduceCtorEq, Option.some.injEq] at base <;>
          (subst base; rfl)
      simp only [underParts, Presentation.subst, universal, if_true]
      exact shaped base
  | _, .pi D T, left, right, pieces, found, _, σ => by
      obtain ⟨l, r, inner, rfl, rfl, computed, rfl⟩ := underParts_pi_cases found
      have below := underParts_subst T l r computed (liftSub σ)
      simp only [Presentation.subst, underParts, below, Option.map_some, List.map_map]
      rfl
  | _, .sigma A B, left, right, pieces, found, _, σ => by
      obtain ⟨a, b, a', b', rfl, rfl, rfl⟩ := underParts_sigma_cases found
      simp only [Presentation.subst, underParts, List.map_cons, List.map_nil, Piece.subst, subst_inst0]
  | _, .var _, _, _, _, found, _, _ | _, .const _, _, _, _, found, _, _
  | _, .id _ _ _, _, _, _, found, _, _ | _, .lam _, _, _, _, found, _, _ | _, .app _ _, _, _, _, found, _, _
  | _, .pair _ _, _, _, _, found, _, _ | _, .fst _, _, _, _, found, _, _ | _, .snd _, _, _, _, found, _, _
  | _, .refl _, _, _, _, found, _, _ => by simp [underParts] at found

/-! ## Typing, exactness and weight -/

section Theory

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

omit [∀ head, Decidable (S.R.isUniverse head)] in
/-- A Π type over a type with a codomain that is a type. -/
theorem pi_formed {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {D : Tm Head n} {T : Tm Head (n + 1)}
    (isD : IsType S.R Γ D) (isT : IsType S.R (.snoc Γ D) T) : ∃ w, S.R.isUniverse w ∧ TypedEquality.Typed S.R Γ (.pi D T) (.head w) := by
  obtain ⟨u, hu, tD⟩ := isD
  obtain ⟨v, hv, tT⟩ := isT
  obtain ⟨w, joined⟩ := S.levels.join_exists hu hv
  have _ := formed
  exact ⟨w, (S.levels.join_level joined).1, .piForm tD hu tT hv joined⟩

omit [∀ head, Decidable (S.R.isUniverse head)] in
/-- A universe as a codomain. -/
theorem universe_pi_formed {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {B : Tm Head n} {u : Head}
    (hu : S.R.isUniverse u) (tB : TypedEquality.Typed S.R Γ B (.head u)) :
    ∃ w, S.R.isUniverse w ∧ TypedEquality.Typed S.R Γ (.pi B (.head u)) (.head w) :=
  pi_formed formed ⟨u, hu, tB⟩ (universe_isType _ hu)

omit [∀ head, Decidable (S.R.isUniverse head)] in
include facts algebra in
theorem baseParts_typed {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {u : Head} (hu : S.R.isUniverse u)
    {left right : Tm Head n} {pieces : List (Piece Head n)} (found : baseParts u left right = some pieces)
    (tl : TypedEquality.Typed S.R Γ left (.head u)) (tr : TypedEquality.Typed S.R Γ right (.head u)) :
    ∀ piece ∈ pieces, piece.Typed S.R Γ := by
  have binderCase : ∀ (isPi : Bool) {B B' : Tm Head n} {C C' : Tm Head (n + 1)},
      TypedEquality.Typed S.R Γ (binder isPi B C) (.head u) → TypedEquality.Typed S.R Γ (binder isPi B' C') (.head u) →
      ∀ piece ∈ ([⟨.head u, B, .head u, B'⟩, ⟨.pi B (.head u), .lam C, .pi B' (.head u), .lam C'⟩] :
        List (Piece Head n)), piece.Typed S.R Γ := by
    intro isPi B B' C C' tl tr
    obtain ⟨tB, tC⟩ := binder_typed facts algebra isPi formed tl
    obtain ⟨tB', tC'⟩ := binder_typed facts algebra isPi formed tr
    obtain ⟨w, hw, tPi⟩ := universe_pi_formed formed hu tB
    obtain ⟨w', hw', tPi'⟩ := universe_pi_formed formed hu tB'
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨⟨tB, tB'⟩, ⟨.lamIntro tPi hw tC, .lamIntro tPi' hw' tC'⟩⟩
  cases left <;> cases right <;> simp only [baseParts, reduceCtorEq, Option.some.injEq] at found <;> subst found
  · exact binderCase true tl tr
  · exact binderCase false tl tr
  · obtain ⟨tC, ta, tb⟩ := id_typed tl
    obtain ⟨tC', ta', tb'⟩ := id_typed tr
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨⟨tC, tC'⟩, ⟨ta, ta'⟩, ⟨tb, tb'⟩⟩

omit [∀ head, Decidable (S.R.isUniverse head)] in
theorem Piece.typed_under {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {D : Tm Head n} (isD : IsType S.R Γ D)
    {piece : Piece Head (n + 1)} (typed : piece.Typed S.R (.snoc Γ D)) : (piece.under D).Typed S.R Γ := by
  have formedD := formed.snoc isD
  obtain ⟨w, hw, tPi⟩ := pi_formed formed isD (Typed.isType typed.1 formedD)
  obtain ⟨w', hw', tPi'⟩ := pi_formed formed isD (Typed.isType typed.2 formedD)
  exact ⟨.lamIntro tPi hw typed.1, .lamIntro tPi' hw' typed.2⟩

include facts algebra in
/-- **The pieces are typed.** -/
theorem underParts_typed : ∀ {n : Nat} (annotation left right : Tm Head n) {Γ : Ctx Head n} {pieces : List (Piece Head n)},
    CtxFormed S.R Γ → underParts (S := S) annotation left right = some pieces →
    TypedEquality.Typed S.R Γ left annotation → TypedEquality.Typed S.R Γ right annotation →
    ∀ piece ∈ pieces, piece.Typed S.R Γ
  | _, .head u, left, right, Γ, pieces, formed, found, tl, tr => by
      obtain ⟨universal, base⟩ := underParts_head found
      exact baseParts_typed facts algebra formed universal base tl tr
  | _, .pi D T, left, right, Γ, pieces, formed, found, tl, tr => by
      obtain ⟨l, r, inner, rfl, rfl, computed, rfl⟩ := underParts_pi_cases found
      obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
      have below := underParts_typed T l r (formed.snoc ⟨u, hu, tD⟩) computed (Typed.lam_inv facts tl formed)
        (Typed.lam_inv facts tr formed)
      intro piece member
      obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
      exact Piece.typed_under formed ⟨u, hu, tD⟩ (below original inside)
  | _, .sigma A B, left, right, Γ, pieces, formed, found, tl, tr => by
      obtain ⟨a, b, a', b', rfl, rfl, rfl⟩ := underParts_sigma_cases found
      obtain ⟨ta, tb⟩ := Typed.pair_inv facts tl formed
      obtain ⟨ta', tb'⟩ := Typed.pair_inv facts tr formed
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨⟨ta, ta'⟩, ⟨tb, tb'⟩⟩
  | _, .var _, _, _, _, _, _, found, _, _ | _, .const _, _, _, _, _, _, found, _, _
  | _, .id _ _ _, _, _, _, _, _, found, _, _
  | _, .lam _, _, _, _, _, _, found, _, _ | _, .app _ _, _, _, _, _, _, found, _, _
  | _, .pair _ _, _, _, _, _, _, found, _, _ | _, .fst _, _, _, _, _, _, found, _, _
  | _, .snd _, _, _, _, _, _, found, _, _ | _, .refl _, _, _, _, _, _, found, _, _ => by
      simp [underParts] at found

omit [∀ head, Decidable (S.R.isUniverse head)] in
include facts in
/-- A piece holds under one abstraction exactly when it holds under the domain. -/
theorem Piece.holds_under {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {D : Tm Head n} (isD : IsType S.R Γ D)
    {piece : Piece Head (n + 1)} (typed : piece.Typed S.R (.snoc Γ D)) :
    (piece.under D).Holds S.R Γ ↔ piece.Holds S.R (.snoc Γ D) := by
  obtain ⟨w, hw, tPi⟩ := pi_formed formed isD (Typed.isType typed.1 (formed.snoc isD))
  unfold Piece.Holds Piece.under
  dsimp only
  rw [ContextualDependentRigid.typeEq_pi_iff facts formed]
  constructor
  · rintro ⟨⟨_, types⟩, terms⟩
    exact ⟨types, lam_equal_inv facts formed terms⟩
  · rintro ⟨types, terms⟩
    exact ⟨⟨isD.refl, types⟩, .lamCong tPi hw terms⟩

omit [∀ head, Decidable (S.R.isUniverse head)] in
include facts roots heads algebra complete in
/-- **Formers at a universe decompose exactly** into their pieces. -/
theorem baseParts_exact {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {u : Head} (hu : S.R.isUniverse u)
    {left right : Tm Head n} {pieces : List (Piece Head n)} (found : baseParts u left right = some pieces)
    (tl : TypedEquality.Typed S.R Γ left (.head u)) (tr : TypedEquality.Typed S.R Γ right (.head u)) :
    Equal S.R Γ left right (.head u) ↔ ∀ piece ∈ pieces, piece.Holds S.R Γ := by
  have uType : TypeEq S.R Γ (.head u) (.head u) := universe_typeEq Γ hu
  have binderCase : ∀ (isPi : Bool) {B B' : Tm Head n} {C C' : Tm Head (n + 1)},
      TypedEquality.Typed S.R Γ (binder isPi B C) (.head u) → TypedEquality.Typed S.R Γ (binder isPi B' C') (.head u) →
      (Equal S.R Γ (binder isPi B C) (binder isPi B' C') (.head u) ↔
        ∀ piece ∈ ([⟨.head u, B, .head u, B'⟩, ⟨.pi B (.head u), .lam C, .pi B' (.head u), .lam C'⟩] :
          List (Piece Head n)), piece.Holds S.R Γ) := by
    intro isPi B B' C C' tl tr
    obtain ⟨tB, tC⟩ := binder_typed facts algebra isPi formed tl
    obtain ⟨tB', tC'⟩ := binder_typed facts algebra isPi formed tr
    obtain ⟨w, hw, tPi⟩ := universe_pi_formed formed hu tB
    have formedB : CtxFormed S.R (.snoc Γ B) := formed.snoc ⟨u, hu, tB⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Piece.Holds]
    constructor
    · intro same
      obtain ⟨domains, families⟩ :=
        (typeEq_binder_iff facts isPi formed).mp ⟨u, hu, same⟩
      have tC'' := Typed.stable tC' (CtxEq.snoc (CtxEq.refl Γ formed) domains)
      exact ⟨⟨uType, equal_of_typeEq facts roots heads algebra complete formed hu tB tB' domains⟩,
        (ContextualDependentRigid.typeEq_pi_iff facts formed).mpr ⟨domains, (universe_isType _ hu).refl⟩,
        .lamCong tPi hw (equal_of_typeEq facts roots heads algebra complete formedB hu tC tC'' families)⟩
    · rintro ⟨⟨_, domainsEqual⟩, _, lambdas⟩
      have bodies := lam_equal_inv facts formed lambdas
      exact equal_of_typeEq facts roots heads algebra complete formed hu tl tr
        ((typeEq_binder_iff facts isPi formed).mpr ⟨⟨u, hu, domainsEqual⟩, ⟨u, hu, bodies⟩⟩)
  cases left <;> cases right <;> simp only [baseParts, reduceCtorEq, Option.some.injEq] at found <;> subst found
  · exact binderCase true tl tr
  · exact binderCase false tl tr
  · rename_i C a b C' a' b'
    obtain ⟨tC, _, _⟩ := id_typed tl
    obtain ⟨tC', _, _⟩ := id_typed tr
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Piece.Holds]
    constructor
    · intro same
      obtain ⟨carriers, lefts, rights⟩ :=
        (ContextualDependentRigid.typeEq_id_iff facts formed).mp ⟨u, hu, same⟩
      exact ⟨⟨uType, equal_of_typeEq facts roots heads algebra complete formed hu tC tC' carriers⟩,
        ⟨carriers, lefts⟩, ⟨carriers, rights⟩⟩
    · rintro ⟨⟨_, carriers⟩, ⟨_, lefts⟩, ⟨_, rights⟩⟩
      exact .idCong carriers hu lefts rights

include facts roots heads algebra complete in
/-- **Formers under abstractions decompose exactly** into their pieces, at every formed context. -/
theorem underParts_exact : ∀ {n : Nat} (annotation left right : Tm Head n) {Γ : Ctx Head n}
    {pieces : List (Piece Head n)}, CtxFormed S.R Γ → underParts (S := S) annotation left right = some pieces →
    TypedEquality.Typed S.R Γ left annotation → TypedEquality.Typed S.R Γ right annotation →
    (Equal S.R Γ left right annotation ↔ ∀ piece ∈ pieces, piece.Holds S.R Γ)
  | _, .head u, left, right, Γ, pieces, formed, found, tl, tr => by
      obtain ⟨universal, base⟩ := underParts_head found
      exact baseParts_exact facts roots heads algebra complete formed universal base tl tr
  | _, .pi D T, left, right, Γ, pieces, formed, found, tl, tr => by
      obtain ⟨l, r, inner, rfl, rfl, computed, rfl⟩ := underParts_pi_cases found
      obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
      have isD : IsType S.R Γ D := ⟨u, hu, tD⟩
      have formedD := formed.snoc isD
      have tl' := Typed.lam_inv facts tl formed
      have tr' := Typed.lam_inv facts tr formed
      have below := underParts_exact T l r formedD computed tl' tr'
      have typed := underParts_typed facts algebra T l r formedD computed tl' tr'
      obtain ⟨w, hw, tPi⟩ := Typed.isType tl formed
      constructor
      · intro same piece member
        obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
        exact (Piece.holds_under facts formed isD (typed original inside)).mpr
          (below.mp (lam_equal_inv facts formed same) original inside)
      · intro held
        exact .lamCong tPi hw (below.mpr fun original inside =>
          (Piece.holds_under facts formed isD (typed original inside)).mp
            (held _ (List.mem_map.mpr ⟨original, inside, rfl⟩)))
  | _, .sigma A B, left, right, Γ, pieces, formed, found, tl, tr => by
      obtain ⟨a, b, a', b', rfl, rfl, rfl⟩ := underParts_sigma_cases found
      obtain ⟨ta, tb⟩ := Typed.pair_inv facts tl formed
      obtain ⟨ta', tb'⟩ := Typed.pair_inv facts tr formed
      obtain ⟨u, hu, tSigma⟩ := Typed.isType tl formed
      obtain ⟨_, v, _, _, _, tB, hv, _, _⟩ := tSigma.generation
      have pairs := ContextualDependentRigid.equal_pair_iff tSigma hu tB hv ta tb ta' tb'
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Piece.Holds]
      rw [pairs]
      constructor
      · rintro ⟨firsts, seconds⟩
        exact ⟨⟨(Typed.isType ta formed).refl, firsts⟩,
          ⟨ContextualDependentRigid.second_types_of_first tB hv ta firsts, seconds⟩⟩
      · rintro ⟨⟨_, firsts⟩, ⟨_, seconds⟩⟩
        exact ⟨firsts, seconds⟩
  | _, .var _, _, _, _, _, _, found, _, _ | _, .const _, _, _, _, _, _, found, _, _
  | _, .id _ _ _, _, _, _, _, _, found, _, _
  | _, .lam _, _, _, _, _, _, found, _, _ | _, .app _ _, _, _, _, _, _, found, _, _
  | _, .pair _ _, _, _, _, _, _, found, _, _ | _, .fst _, _, _, _, _, _, found, _, _
  | _, .snd _, _, _, _, _, _, found, _, _ | _, .refl _, _, _, _, _, _, found, _, _ => by
      simp [underParts] at found

/-! ### Weights -/

/-- A judged term has a normal form of the given weight. -/
def HasWeight (S : Setting Head L) {n : Nat} (Γ : Ctx Head n) (t T : Tm Head n) (w : Nat) : Prop :=
  ∃ v, NormalForm S.R S.roles Γ t v T ∧ weight v = w

/-- The pieces have normal forms of the given total weight. -/
def PiecesWeigh (S : Setting Head L) {n : Nat} (Γ : Ctx Head n) : List (Piece Head n) → Nat → Prop
  | [], w => w = 0
  | piece :: rest, w => ∃ a b c, HasWeight S Γ piece.left piece.leftType a ∧
      HasWeight S Γ piece.right piece.rightType b ∧ PiecesWeigh S Γ rest c ∧ w = a + b + c

omit [∀ head, Decidable (S.R.isUniverse head)] in
/-- The normal form of an abstraction is the abstraction of the normal form. -/
theorem HasWeight.under {n : Nat} {Γ : Ctx Head n} {D : Tm Head n} {t T : Tm Head (n + 1)} {w v : Head}
    {a : Nat} (hv : S.R.isUniverse v) (tPi : TypedEquality.Typed S.R Γ (.pi D T) (.head v)) (isD : IsType S.R Γ D)
    (weighs : HasWeight S (.snoc Γ D) t T a) : HasWeight S Γ (.lam t) (.pi D T) a := by
  obtain ⟨body, normal, weighed⟩ := weighs
  have _ := w
  exact ⟨.lam body, ⟨.lam (IsType.refl ⟨v, hv, tPi⟩) isD (.lamIntro tPi hv normal.1.typed) normal.1,
    .lamCong tPi hv normal.2⟩, weighed⟩

omit [∀ head, Decidable (S.R.isUniverse head)] in
theorem PiecesWeigh.under {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {D : Tm Head n} (isD : IsType S.R Γ D) :
    ∀ {pieces : List (Piece Head (n + 1))} {w : Nat}, (∀ piece ∈ pieces, piece.Typed S.R (.snoc Γ D)) →
      PiecesWeigh S (.snoc Γ D) pieces w → PiecesWeigh S Γ (pieces.map (Piece.under D)) w
  | [], _, _, weighs => weighs
  | piece :: rest, w, typed, ⟨a, b, c, left, right, others, total⟩ => by
      have formedD := formed.snoc isD
      obtain ⟨v, hv, tPi⟩ := pi_formed formed isD (Typed.isType (typed piece List.mem_cons_self).1 formedD)
      obtain ⟨v', hv', tPi'⟩ := pi_formed formed isD (Typed.isType (typed piece List.mem_cons_self).2 formedD)
      exact ⟨a, b, c, HasWeight.under (w := v) hv tPi isD left, HasWeight.under (w := v) hv' tPi' isD right,
        PiecesWeigh.under formed isD (fun other member => typed other (List.mem_cons_of_mem _ member)) others, total⟩

omit [∀ head, Decidable (S.R.isUniverse head)] in
include facts roots heads algebra rigid complete in
/-- **Formers at a universe weigh two more than their pieces.** -/
theorem baseParts_weight {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {u : Head} (hu : S.R.isUniverse u)
    {left right : Tm Head n} {pieces : List (Piece Head n)} (found : baseParts u left right = some pieces)
    (tl : TypedEquality.Typed S.R Γ left (.head u)) (tr : TypedEquality.Typed S.R Γ right (.head u)) :
    ∃ w wl wr, PiecesWeigh S Γ pieces w ∧ HasWeight S Γ left (.head u) wl ∧ HasWeight S Γ right (.head u) wr ∧
      w + 2 = wl + wr := by
  have binderCase : ∀ (isPi : Bool) {B B' : Tm Head n} {C C' : Tm Head (n + 1)},
      TypedEquality.Typed S.R Γ (binder isPi B C) (.head u) → TypedEquality.Typed S.R Γ (binder isPi B' C') (.head u) →
      ∃ w wl wr, PiecesWeigh S Γ [⟨.head u, B, .head u, B'⟩, ⟨.pi B (.head u), .lam C, .pi B' (.head u), .lam C'⟩] w ∧
        HasWeight S Γ (binder isPi B C) (.head u) wl ∧ HasWeight S Γ (binder isPi B' C') (.head u) wr ∧
        w + 2 = wl + wr := by
    intro isPi B B' C C' tl tr
    obtain ⟨tB, tC⟩ := binder_typed facts algebra isPi formed tl
    obtain ⟨tB', tC'⟩ := binder_typed facts algebra isPi formed tr
    obtain ⟨D, lD, nB⟩ := universe_normalForm facts roots heads algebra rigid complete formed hu tB
    obtain ⟨D', lD', nB'⟩ := universe_normalForm facts roots heads algebra rigid complete formed hu tB'
    obtain ⟨E, lE, nC⟩ := universe_normalForm facts roots heads algebra rigid complete (formed.snoc ⟨_, hu, tB⟩) hu tC
    obtain ⟨E', lE', nC'⟩ :=
      universe_normalForm facts roots heads algebra rigid complete (formed.snoc ⟨_, hu, tB'⟩) hu tC'
    obtain ⟨w₁, hw₁, tPi⟩ := universe_pi_formed formed hu tB
    obtain ⟨w₂, hw₂, tPi'⟩ := universe_pi_formed formed hu tB'
    refine ⟨weight D + weight D' + (weight E + weight E' + 0), weight D + weight E + 1, weight D' + weight E' + 1,
      ⟨weight D, weight D', weight E + weight E' + 0, ⟨D, nB, rfl⟩, ⟨D', nB', rfl⟩,
        ⟨weight E, weight E', 0, ⟨.lam E, family_normalForm hw₁ tPi ⟨_, hu, tB⟩ nC, rfl⟩,
          ⟨.lam E', family_normalForm hw₂ tPi' ⟨_, hu, tB'⟩ nC', rfl⟩, rfl, rfl⟩, rfl⟩,
      ⟨binder isPi D E, binder_normalForm facts roots heads algebra complete isPi formed hu tB tC lD nB lE nC,
        binder_weight isPi D E⟩,
      ⟨binder isPi D' E', binder_normalForm facts roots heads algebra complete isPi formed hu tB' tC' lD' nB' lE' nC',
        binder_weight isPi D' E'⟩, by omega⟩
  cases left <;> cases right <;> simp only [baseParts, reduceCtorEq, Option.some.injEq] at found <;> subst found
  · exact binderCase true tl tr
  · exact binderCase false tl tr
  · rename_i C a b C' a' b'
    obtain ⟨tC, ta, tb⟩ := id_typed tl
    obtain ⟨tC', ta', tb'⟩ := id_typed tr
    obtain ⟨N, lN, nC⟩ := universe_normalForm facts roots heads algebra rigid complete formed hu tC
    obtain ⟨N', lN', nC'⟩ := universe_normalForm facts roots heads algebra rigid complete formed hu tC'
    obtain ⟨na, nA⟩ := long_exists facts roots heads algebra rigid complete formed ta
    obtain ⟨nb, nB⟩ := long_exists facts roots heads algebra rigid complete formed tb
    obtain ⟨na', nA'⟩ := long_exists facts roots heads algebra rigid complete formed ta'
    obtain ⟨nb', nB'⟩ := long_exists facts roots heads algebra rigid complete formed tb'
    refine ⟨weight N + weight N' + (weight na + weight na' + (weight nb + weight nb' + 0)),
      weight N + weight na + weight nb + 1, weight N' + weight na' + weight nb' + 1,
      ⟨weight N, weight N', _, ⟨N, nC, rfl⟩, ⟨N', nC', rfl⟩,
        ⟨weight na, weight na', _, ⟨na, nA, rfl⟩, ⟨na', nA', rfl⟩,
          ⟨weight nb, weight nb', 0, ⟨nb, nB, rfl⟩, ⟨nb', nB', rfl⟩, rfl, rfl⟩, rfl⟩, rfl⟩,
      ⟨.id N na nb, id_normalForm hu lN nC nA nB (universe_typeEq Γ hu), rfl⟩,
      ⟨.id N' na' nb', id_normalForm hu lN' nC' nA' nB' (universe_typeEq Γ hu), rfl⟩, by omega⟩

include facts roots heads algebra rigid complete in
/-- **Formers under abstractions weigh two more than their pieces.** -/
theorem underParts_weight : ∀ {n : Nat} (annotation left right : Tm Head n) {Γ : Ctx Head n}
    {pieces : List (Piece Head n)}, CtxFormed S.R Γ → underParts (S := S) annotation left right = some pieces →
    TypedEquality.Typed S.R Γ left annotation → TypedEquality.Typed S.R Γ right annotation →
    ∃ w wl wr, PiecesWeigh S Γ pieces w ∧ HasWeight S Γ left annotation wl ∧ HasWeight S Γ right annotation wr ∧
      w + 2 = wl + wr
  | _, .head u, left, right, Γ, pieces, formed, found, tl, tr => by
      obtain ⟨universal, base⟩ := underParts_head found
      exact baseParts_weight facts roots heads algebra rigid complete formed universal base tl tr
  | _, .pi D T, left, right, Γ, pieces, formed, found, tl, tr => by
      obtain ⟨l, r, inner, rfl, rfl, computed, rfl⟩ := underParts_pi_cases found
      obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
      have isD : IsType S.R Γ D := ⟨u, hu, tD⟩
      have formedD := formed.snoc isD
      have tl' := Typed.lam_inv facts tl formed
      have tr' := Typed.lam_inv facts tr formed
      obtain ⟨w, wl, wr, weighs, left, right, total⟩ :=
        underParts_weight T l r formedD computed tl' tr'
      have typed := underParts_typed facts algebra T l r formedD computed tl' tr'
      obtain ⟨v, hv, tPi⟩ := Typed.isType tl formed
      exact ⟨w, wl, wr, PiecesWeigh.under formed isD typed weighs, HasWeight.under (w := v) hv tPi isD left,
        HasWeight.under (w := v) hv tPi isD right, total⟩
  | _, .sigma A B, left, right, Γ, pieces, formed, found, tl, tr => by
      obtain ⟨a, b, a', b', rfl, rfl, rfl⟩ := underParts_sigma_cases found
      obtain ⟨ta, tb⟩ := Typed.pair_inv facts tl formed
      obtain ⟨ta', tb'⟩ := Typed.pair_inv facts tr formed
      obtain ⟨u, hu, tSigma⟩ := Typed.isType tl formed
      obtain ⟨_, v, _, _, _, tB, hv, _, _⟩ := tSigma.generation
      obtain ⟨na, nA⟩ := long_exists facts roots heads algebra rigid complete formed ta
      obtain ⟨nb, nB⟩ := long_exists facts roots heads algebra rigid complete formed tb
      obtain ⟨na', nA'⟩ := long_exists facts roots heads algebra rigid complete formed ta'
      obtain ⟨nb', nB'⟩ := long_exists facts roots heads algebra rigid complete formed tb'
      refine ⟨weight na + weight na' + (weight nb + weight nb' + 0), weight na + weight nb + 1,
        weight na' + weight nb' + 1,
        ⟨weight na, weight na', _, ⟨na, nA, rfl⟩, ⟨na', nA', rfl⟩,
          ⟨weight nb, weight nb', 0, ⟨nb, nB, rfl⟩, ⟨nb', nB', rfl⟩, rfl, rfl⟩, rfl⟩,
        ⟨.pair na nb, pair_normalForm tSigma hu tB hv ta nA nB, rfl⟩,
        ⟨.pair na' nb', pair_normalForm tSigma hu tB hv ta' nA' nB', rfl⟩, by omega⟩
  | _, .var _, _, _, _, _, _, found, _, _ | _, .const _, _, _, _, _, _, found, _, _
  | _, .id _ _ _, _, _, _, _, _, found, _, _
  | _, .lam _, _, _, _, _, _, found, _, _ | _, .app _ _, _, _, _, _, _, found, _, _
  | _, .pair _ _, _, _, _, _, _, found, _, _ | _, .fst _, _, _, _, _, _, found, _, _
  | _, .snd _, _, _, _, _, _, found, _, _ | _, .refl _, _, _, _, _, _, found, _, _ => by
      simp [underParts] at found

end Theory

end ContextualDependentSpinesMany
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
