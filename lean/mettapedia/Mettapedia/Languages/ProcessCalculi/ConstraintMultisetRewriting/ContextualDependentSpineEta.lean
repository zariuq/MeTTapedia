import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEliminationsUnder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentStrengthening

/-!
# Elimination spines at every type, through η

R107's reader of elimination spines is exact at a base type (`ContextualDependentEliminations.elim_exact`): two neutral
spines equal at a base type are compared by the algorithm as spines. At a type that is a Π or Σ type up to reduction, the
algorithm first η-expands: it applies both spines to a fresh variable, or projects both, and compares again. A
**descent** follows these steps to the comparison of the two spines as spines, after a renaming into the context with
the fresh variables (`descends`): every algorithmic comparison of two neutral terms ends, after an injective renaming
compatible with the declarations, in their comparison as spines.

The reader commutes with such renamings (`elimParts_rename`), and the equality of its pieces reflects along them, so
**two elimination spines of one local are equal at any type exactly when their pieces hold** (`elim_exact_any`). No
condition on the type is needed: a base type that a solution instantiates with a Π or Σ type is covered.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSpineEta

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentSpinesMany ContextualDependentEliminations

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## The descent of an algorithmic comparison of neutral terms -/

/-- **What an algorithmic comparison of neutral terms descends to**: for types, their comparison as spines; for terms,
their comparison as spines after an injective renaming, compatible with the declarations, into a formed context; for
spines, the comparison itself. -/
def Descends (S : Setting Head L) : AlgorithmicStatement Head → Prop
  | .types Γ A B => CtxFormed S.R Γ → Neutral S.roles A → Neutral S.roles B →
      ∃ U, Algorithmic S.R S.roles (.spines Γ A B U)
  | .typesW Γ A B => CtxFormed S.R Γ → Neutral S.roles A → Neutral S.roles B →
      ∃ U, Algorithmic S.R S.roles (.spines Γ A B U)
  | .terms Γ l r _ => CtxFormed S.R Γ → Neutral S.roles l → Neutral S.roles r →
      ∃ (m : Nat) (Δ : Ctx Head m) (ρ : Ren _ m), CtxFormed S.R Δ ∧ CtxRen Γ Δ ρ ∧ Function.Injective ρ ∧
        ∃ U, Algorithmic S.R S.roles (.spines Δ (Presentation.rename ρ l) (Presentation.rename ρ r) U)
  | .termsW Γ l r _ => CtxFormed S.R Γ → Neutral S.roles l → Neutral S.roles r →
      ∃ (m : Nat) (Δ : Ctx Head m) (ρ : Ren _ m), CtxFormed S.R Δ ∧ CtxRen Γ Δ ρ ∧ Function.Injective ρ ∧
        ∃ U, Algorithmic S.R S.roles (.spines Δ (Presentation.rename ρ l) (Presentation.rename ρ r) U)
  | .spines Γ l r U => Algorithmic S.R S.roles (.spines Γ l r U)
  | .spinesW Γ l r U => Algorithmic S.R S.roles (.spinesW Γ l r U)

/-- Reflexivity is not neutral. -/
theorem refl_not_neutral {n : Nat} {x : Tm Head n} (neutral : Neutral S.roles (.refl x)) : False := by
  rcases neutral.shape with ⟨_, same⟩ | ⟨_, same⟩ | ⟨_, _, same⟩ | ⟨_, same⟩ | ⟨_, same⟩ <;> cases same

/-- A comparison as spines, at the identity renaming. -/
theorem spines_at_id {n : Nat} {Γ : Ctx Head n} {l r U : Tm Head n} (formed : CtxFormed S.R Γ)
    (spines : Algorithmic S.R S.roles (.spines Γ l r U)) :
    ∃ (m : Nat) (Δ : Ctx Head m) (ρ : Ren n m), CtxFormed S.R Δ ∧ CtxRen Γ Δ ρ ∧ Function.Injective ρ ∧
      ∃ U, Algorithmic S.R S.roles (.spines Δ (Presentation.rename ρ l) (Presentation.rename ρ r) U) :=
  ⟨n, Γ, idRen, formed, CtxRen.id Γ, fun _ _ same => same, U, by rw [rename_id, rename_id]; exact spines⟩

/-- **The descent**: every algorithmic comparison of neutral terms ends in their comparison as spines. -/
theorem descends {statement : AlgorithmicStatement Head} (derivation : Algorithmic S.R S.roles statement) :
    Descends S statement := by
  induction derivation with
  | types leftRed rightRed _ _ _ ih =>
      intro formed leftNeutral rightNeutral
      have leftSame := WhRed.eq_of_whnf (S := S) (leftNeutral.whnf S.shape) leftRed.red
      have rightSame := WhRed.eq_of_whnf (S := S) (rightNeutral.whnf S.shape) rightRed.red
      subst leftSame
      subst rightSame
      exact ih formed leftNeutral rightNeutral
  | heads => intro _ leftNeutral _; exact absurd rfl (leftNeutral.not_former.1 _)
  | pi => intro _ leftNeutral _; exact absurd rfl (leftNeutral.not_former.2.1 _ _)
  | sigma => intro _ leftNeutral _; exact absurd rfl (leftNeutral.not_former.2.2.1 _ _)
  | id => intro _ leftNeutral _; exact absurd rfl (leftNeutral.not_former.2.2.2 _ _ _)
  | inductiveType role => intro _ leftNeutral _; exact absurd rfl (leftNeutral.ne_inductive role)
  | neutralTypes _ _ _ spines _ =>
      intro _ _ _
      cases spines with
      | spinesW inner _ _ => exact ⟨_, inner⟩
  | terms _ _ leftRed rightRed _ ih =>
      intro formed leftNeutral rightNeutral
      have leftSame := WhRed.eq_of_whnf (S := S) (leftNeutral.whnf S.shape) leftRed.red
      have rightSame := WhRed.eq_of_whnf (S := S) (rightNeutral.whnf S.shape) rightRed.red
      subst leftSame
      subst rightSame
      exact ih formed leftNeutral rightNeutral
  | univ _ _ _ _ ih =>
      intro formed leftNeutral rightNeutral
      obtain ⟨U, spines⟩ := ih formed leftNeutral rightNeutral
      exact spines_at_id formed spines
  | @eta n Γ f g A B isA _ _ _ _ _ ih =>
      intro formed leftNeutral rightNeutral
      obtain ⟨m, Δ, ρ, formedΔ, compatible, injective, U, spines⟩ := ih (formed.snoc isA)
        (.app (leftNeutral.rename wk)) (.app (rightNeutral.rename wk))
      simp only [Presentation.rename] at spines
      cases spines with
      | app inner _ =>
          cases inner with
          | spinesW prefixSpines _ _ =>
              rw [rename_comp, rename_comp] at prefixSpines
              exact ⟨m, Δ, fun index => ρ (wk index), formedΔ, CtxRen.comp (CtxRen.wk Γ A) compatible,
                injective.comp (Fin.succ_injective _), _, prefixSpines⟩
  | sigmaEta _ _ _ _ _ _ ih _ =>
      intro formed leftNeutral rightNeutral
      obtain ⟨m, Δ, ρ, formedΔ, compatible, injective, U, spines⟩ := ih formed (.fst leftNeutral)
        (.fst rightNeutral)
      simp only [Presentation.rename] at spines
      cases spines with
      | fst inner =>
          cases inner with
          | spinesW prefixSpines _ _ => exact ⟨m, Δ, ρ, formedΔ, compatible, injective, _, prefixSpines⟩
  | refl => intro _ leftNeutral _; exact (refl_not_neutral leftNeutral).elim
  | spine _ _ _ _ _ inner _ =>
      intro formed _ _
      cases inner with
      | spinesW spines _ _ => exact spines_at_id formed spines
  | var i => exact .var i
  | const typeOf typed => exact .const typeOf typed
  | app inner terms _ _ => exact .app inner terms
  | fst inner _ => exact .fst inner
  | snd inner _ => exact .snd inner
  | spinesW inner red form _ => exact .spinesW inner red form

/-! ## The reader under renamings -/

/-- Rename a piece. -/
def renamePiece {n m : Nat} (ρ : Ren n m) (piece : Piece Head n) : Piece Head m :=
  ⟨Presentation.rename ρ piece.leftType, Presentation.rename ρ piece.left, Presentation.rename ρ piece.rightType,
    Presentation.rename ρ piece.right⟩

/-- **The reader commutes with injective renamings compatible with the declarations.** -/
theorem elimParts_rename {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m}
    (compatible : CtxRen Γ Δ ρ) (injective : Function.Injective ρ) :
    ∀ (left right : Tm Head n) {pieces : List (Piece Head n)} {TL TR : Tm Head n},
      elimParts Γ left right = some (pieces, TL, TR) →
      elimParts Δ (Presentation.rename ρ left) (Presentation.rename ρ right) =
        some (pieces.map (renamePiece ρ), Presentation.rename ρ TL, Presentation.rename ρ TR)
  | .var h, right, pieces, TL, TR, found => by
      cases right
      all_goals first | cases found | skip
      rename_i h'
      simp only [elimParts] at found
      split at found
      · rename_i same
        subst same
        cases found
        simp only [Presentation.rename, elimParts, List.map_nil, compatible h, if_true]
      · cases found
  | .app f a, right, pieces, TL, TR, found => by
      cases right
      all_goals first | cases found | skip
      rename_i g b
      obtain ⟨prefixPieces, DL, EL, DR, ER, read, result⟩ := appStep_some found
      cases result
      have below := elimParts_rename compatible injective f g read
      simp only [Presentation.rename, elimParts, below, appStep, List.map_append, List.map_cons, List.map_nil,
        rename_inst0]
      rfl
  | .fst p, right, pieces, TL, TR, found => by
      cases right
      all_goals first | cases found | skip
      rename_i q
      obtain ⟨prefixPieces, AL, BL, AR, BR, read, result⟩ := fstStep_some found
      cases result
      have below := elimParts_rename compatible injective p q read
      simp only [Presentation.rename, elimParts, below, fstStep]
  | .snd p, right, pieces, TL, TR, found => by
      cases right
      all_goals first | cases found | skip
      rename_i q
      obtain ⟨prefixPieces, AL, BL, AR, BR, read, result⟩ := sndStep_some found
      cases result
      have below := elimParts_rename compatible injective p q read
      simp only [Presentation.rename, elimParts, below, sndStep, rename_inst0]
  | .const _, _, _, _, _, found => by cases found
  | .head _, _, _, _, _, found => by cases found
  | .pi _ _, _, _, _, _, found => by cases found
  | .sigma _ _, _, _, _, _, found => by cases found
  | .id _ _ _, _, _, _, _, found => by cases found
  | .lam _, _, _, _, _, found => by cases found
  | .pair _ _, _, _, _, _, found => by cases found
  | .refl _, _, _, _, _, found => by cases found

/-! ## Exactness at every type -/

section Exactness

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- A piece that holds after an injective compatible renaming holds. -/
theorem piece_reflects {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m}
    (compatible : CtxRen Γ Δ ρ) (injective : Function.Injective ρ) (formedΓ : CtxFormed S.R Γ)
    (formedΔ : CtxFormed S.R Δ) {piece : Piece Head n} (typed : piece.Typed S.R Γ)
    (held : (renamePiece ρ piece).Holds S.R Δ) : piece.Holds S.R Γ := by
  have types := ContextualDependentStrengthening.typeEq_reflects facts roots heads algebra
    (ContextualDependentScopeConsequence.root_reflection rigid) complete injective compatible formedΓ formedΔ
    (Typed.isType typed.1 formedΓ) (Typed.isType typed.2 formedΓ) held.1
  exact ⟨types, ContextualDependentStrengthening.equal_reflects facts roots heads algebra
    (ContextualDependentScopeConsequence.root_reflection rigid) complete injective compatible formedΓ formedΔ
    typed.1 (Typed.convType typed.2 types.symm) held.2⟩

include facts roots heads algebra rigid complete in
/-- **Elimination spines of one local decompose exactly at every type**: two typed spines read together are equal at a
type exactly when every piece holds. The type need not be a base type. -/
theorem elim_exact_any {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {left right : Tm Head n}
    {pieces : List (Piece Head n)} {TL TR C : Tm Head n} (found : elimParts Γ left right = some (pieces, TL, TR))
    (tl : TypedEquality.Typed S.R Γ left C) (tr : TypedEquality.Typed S.R Γ right C) :
    Equal S.R Γ left right C ↔ ∀ piece ∈ pieces, piece.Holds S.R Γ := by
  obtain ⟨tlL, principalL, _⟩ := elimParts_typed facts formed left right found tl
  obtain ⟨trR, _, _⟩ := elimParts_typed facts formed right left (elimParts_swap Γ left right found) tr
  have typed := elimParts_pieces_typed facts formed found tl tr
  constructor
  · intro same
    obtain ⟨leftNeutral, rightNeutral⟩ := elimParts_neutral (roles := S.roles) Γ left right found
    obtain ⟨m, Δ, ρ, formedΔ, compatible, injective, U, spines⟩ :=
      descends (complete formed same) formed leftNeutral rightNeutral
    have renamed := elimParts_rename compatible injective left right found
    have holds := (elimParts_holds facts roots heads algebra formedΔ _ _ renamed spines (tlL.rename compatible)
      (trR.rename compatible) (fun piece member => by
        obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
        exact ⟨(typed original inside).1.rename compatible, (typed original inside).2.rename compatible⟩)).2.2
    intro piece member
    exact piece_reflects facts roots heads algebra rigid complete compatible injective formed formedΔ
      (typed piece member) (holds _ (List.mem_map.mpr ⟨piece, member, rfl⟩))
  · intro held
    exact .subEq (elimParts_congr left right found held) (TypeLe.toBelow (principalL C tl) (Typed.isType tl formed))

end Exactness

end ContextualDependentSpineEta
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
