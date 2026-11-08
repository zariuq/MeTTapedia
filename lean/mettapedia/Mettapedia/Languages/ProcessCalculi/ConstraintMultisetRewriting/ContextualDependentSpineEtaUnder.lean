import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSpineEta

/-!
# Elimination spines at a flexible base, under abstractions

R107's reader under abstractions requires the base type to be rigid (`rigidBase`: a universe, an identity type or a
local), so that every substitution fixing the locals keeps it a base type and the reading at a base type stays exact.
With exactness at every type (`elim_exact_any`) the base may be **any variable**, for instance a metavariable that a
solution instantiates with a Π type, as in `λ g. g X ≐ λ g. g A` at `(U0 → A) → A`.

The reader (`elimAnyUnder`) reads the abstractions of the annotation as R107's, and at the base accepts a universe, an
identity type or any variable (`baseShape`); the base shape is used only for the weight, in the store's own context. At
every substitution that fixes the locals, the reading is exact (`elimAnyUnder_exact_subst`): the reading of the spines
is kept (R107's `elimLocal_subst`) and the reader is exact at the instantiated type, whatever it is. The pieces are typed
(`elimAnyUnder_typed`) and weigh at least two less than the two sides (`elimAnyUnder_weight`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSpineEta

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentFragment ContextualDependentDecisiveFragment
open ContextualDependentRigidFormers ContextualDependentEtaLong ContextualDependentRank
open ContextualDependentSpinesMany ContextualDependentConversionBudget ContextualDependentFragmentDecisive
open ContextualDependentRigidDecomposition ContextualDependentConstantHeadsProjections ContextualDependentOccursFull
open ContextualDependentEliminations

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## The reader -/

section Reading

variable {n : Nat}

/-- **Base shapes**: a universe, an identity type, or any variable. -/
def baseShape : Tm Head n → Bool
  | .head _ => true
  | .id _ _ _ => true
  | .var _ => true
  | .const _ | .pi _ _ | .sigma _ _ | .lam _ | .app _ _ | .pair _ _ | .fst _ | .snd _ | .refl _ => false

theorem baseShape_spec {C : Tm Head n} (base : baseShape C = true) : BaseType S C := by
  cases C with
  | head u => exact .inr (.inl ⟨u, rfl⟩)
  | id X a b => exact .inl ⟨X, a, b, rfl⟩
  | var j => exact .inr (.inr (.var j))
  | _ => simp [baseShape] at base

/-- **The pieces of two elimination spines of one local at a base shape**, under the abstractions read so far. -/
def elimAnyBase (locals : List (Tm Head n)) (C left right : Tm Head n) : Option (List (Piece Head n)) :=
  if baseShape C then (elimLocal locals left right).map (·.1) else none

theorem elimAnyBase_spec {locals : List (Tm Head n)} {C left right : Tm Head n} {pieces : List (Piece Head n)}
    (found : elimAnyBase locals C left right = some pieces) :
    baseShape C = true ∧ ∃ TL TR, elimLocal locals left right = some (pieces, TL, TR) := by
  unfold elimAnyBase at found
  split at found
  · rename_i base
    obtain ⟨⟨pieces', TL, TR⟩, read, same⟩ := Option.map_eq_some_iff.mp found
    cases same
    exact ⟨base, TL, TR, read⟩
  · cases found

end Reading

/-- **Elimination spines of one local at a base shape, under abstractions.** -/
def elimAnyUnder : {n : Nat} → List (Tm Head n) → Tm Head n → Tm Head n → Tm Head n → Option (List (Piece Head n))
  | _, locals, .pi D T, .lam left, .lam right =>
      (elimAnyUnder (Presentation.rename wk D :: locals.map (Presentation.rename wk)) T left right).map
        (List.map (Piece.under D))
  | _, locals, C, left, right => elimAnyBase locals C left right

theorem elimAnyUnder_cases {n : Nat} {locals : List (Tm Head n)} {annotation left right : Tm Head n}
    {pieces : List (Piece Head n)} (found : elimAnyUnder locals annotation left right = some pieces) :
    (∃ D T l r inner, annotation = .pi D T ∧ left = .lam l ∧ right = .lam r ∧
      elimAnyUnder (Presentation.rename wk D :: locals.map (Presentation.rename wk)) T l r = some inner ∧
      pieces = inner.map (Piece.under D)) ∨ elimAnyBase locals annotation left right = some pieces := by
  cases annotation with
  | pi D T =>
      cases left with
      | lam l =>
          cases right with
          | lam r =>
              simp only [elimAnyUnder, Option.map_eq_some_iff] at found
              obtain ⟨inner, computed, rfl⟩ := found
              exact .inl ⟨D, T, l, r, inner, rfl, rfl, rfl, computed, rfl⟩
          | _ => exact .inr (by simpa [elimAnyUnder] using found)
      | _ => exact .inr (by simpa [elimAnyUnder] using found)
  | _ => exact .inr (by simpa [elimAnyUnder] using found)

section Theory

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

/-- The locals read under one more abstraction, after a substitution lifted past it. -/
theorem locals_lift {n m : Nat} (σ : Sub Head n m) (D : Tm Head n) (locals : List (Tm Head n)) :
    (Presentation.rename wk D :: locals.map (Presentation.rename wk)).map (Presentation.subst (liftSub σ)) =
      Presentation.rename wk (Presentation.subst σ D) ::
        (locals.map (Presentation.subst σ)).map (Presentation.rename wk) := by
  rw [List.map_cons, subst_liftSub_wk, List.map_map, List.map_map]
  congr 1
  congr 1
  funext t
  exact subst_liftSub_wk σ t

include facts roots heads algebra rigid complete in
/-- **The reading is exact at every substitution that fixes the locals**, whatever the instantiated base becomes. -/
theorem elimAnyUnder_exact_subst : ∀ {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n)
    {pieces : List (Piece Head n)}, elimAnyUnder locals annotation left right = some pieces →
    ∀ {m : Nat} (σ : Sub Head n m) {Γ : Ctx Head m}, Fixes σ locals.length → locals.length ≤ m →
      CtxFormed S.R Γ → LocalTypes Γ (locals.map (Presentation.subst σ)) →
      TypedEquality.Typed S.R Γ (Presentation.subst σ left) (Presentation.subst σ annotation) →
      TypedEquality.Typed S.R Γ (Presentation.subst σ right) (Presentation.subst σ annotation) →
      (Equal S.R Γ (Presentation.subst σ left) (Presentation.subst σ right) (Presentation.subst σ annotation) ↔
        ∀ piece ∈ pieces, (piece.subst σ).Holds S.R Γ) := by
  intro locals annotation left right pieces found m σ Γ fixes bound formed types tl tr
  rcases elimAnyUnder_cases found with ⟨D, T, l, r, inner, rfl, rfl, rfl, computed, rfl⟩ | base
  · change TypedEquality.Typed S.R Γ (.lam (Presentation.subst (liftSub σ) l))
      (.pi (Presentation.subst σ D) (Presentation.subst (liftSub σ) T)) at tl
    change TypedEquality.Typed S.R Γ (.lam (Presentation.subst (liftSub σ) r))
      (.pi (Presentation.subst σ D) (Presentation.subst (liftSub σ) T)) at tr
    obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
    have isD : IsType S.R Γ (Presentation.subst σ D) := ⟨u, hu, tD⟩
    have formedD := formed.snoc isD
    have tl' := Typed.lam_inv facts tl formed
    have tr' := Typed.lam_inv facts tr formed
    have typesD := types.under (Presentation.subst σ D)
    rw [← locals_lift] at typesD
    have below := elimAnyUnder_exact_subst _ T l r computed (liftSub σ) (by simpa using fixes.lift)
      (by simp; omega) formedD typesD tl' tr'
    have typed : ∀ piece ∈ inner, (piece.subst (liftSub σ)).Typed S.R (.snoc Γ (Presentation.subst σ D)) := by
      intro piece member
      have pieceTyped := elimAnyUnder_typed_subst _ T l r computed (liftSub σ) (by simpa using fixes.lift)
        (by simp; omega) formedD typesD tl' tr'
      exact pieceTyped piece member
    obtain ⟨w, hw, tPi⟩ := Typed.isType tl formed
    change Equal S.R Γ (.lam (Presentation.subst (liftSub σ) l)) (.lam (Presentation.subst (liftSub σ) r))
      (.pi (Presentation.subst σ D) (Presentation.subst (liftSub σ) T)) ↔ _
    constructor
    · intro same piece member
      obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
      rw [Piece.subst_under]
      exact (Piece.holds_under facts formed isD (typed original inside)).mpr
        (below.mp (lam_equal_inv facts formed same) original inside)
    · intro held
      exact .lamCong tPi hw (below.mpr fun original inside =>
        (Piece.holds_under facts formed isD (typed original inside)).mp (by
          have := held _ (List.mem_map.mpr ⟨original, inside, rfl⟩)
          rwa [Piece.subst_under] at this))
  · obtain ⟨_, TL, TR, read⟩ := elimAnyBase_spec base
    have moved := elimLocal_subst σ fixes bound left right read
    exact (elim_exact_any facts roots heads algebra rigid complete formed (elimLocal_parts types _ _ moved) tl
      tr).trans List.forall_mem_map
where
  /-- The pieces read at a substitution are typed. -/
  elimAnyUnder_typed_subst : ∀ {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n)
      {pieces : List (Piece Head n)}, elimAnyUnder locals annotation left right = some pieces →
      ∀ {m : Nat} (σ : Sub Head n m) {Γ : Ctx Head m}, Fixes σ locals.length → locals.length ≤ m →
        CtxFormed S.R Γ → LocalTypes Γ (locals.map (Presentation.subst σ)) →
        TypedEquality.Typed S.R Γ (Presentation.subst σ left) (Presentation.subst σ annotation) →
        TypedEquality.Typed S.R Γ (Presentation.subst σ right) (Presentation.subst σ annotation) →
        ∀ piece ∈ pieces, (piece.subst σ).Typed S.R Γ := by
    intro n locals annotation left right pieces found m σ Γ fixes bound formed types tl tr
    rcases elimAnyUnder_cases found with ⟨D, T, l, r, inner, rfl, rfl, rfl, computed, rfl⟩ | base
    · change TypedEquality.Typed S.R Γ (.lam (Presentation.subst (liftSub σ) l))
        (.pi (Presentation.subst σ D) (Presentation.subst (liftSub σ) T)) at tl
      change TypedEquality.Typed S.R Γ (.lam (Presentation.subst (liftSub σ) r))
        (.pi (Presentation.subst σ D) (Presentation.subst (liftSub σ) T)) at tr
      obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
      have isD : IsType S.R Γ (Presentation.subst σ D) := ⟨u, hu, tD⟩
      have typesD := types.under (Presentation.subst σ D)
      rw [← locals_lift] at typesD
      have below := elimAnyUnder_typed_subst _ T l r computed (liftSub σ) (by simpa using fixes.lift)
        (by simp; omega) (formed.snoc isD) typesD (Typed.lam_inv facts tl formed) (Typed.lam_inv facts tr formed)
      intro piece member
      obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
      rw [Piece.subst_under]
      exact Piece.typed_under formed isD (below original inside)
    · obtain ⟨_, TL, TR, read⟩ := elimAnyBase_spec base
      have moved := elimLocal_subst σ fixes bound left right read
      intro piece member
      exact elimParts_pieces_typed facts formed (elimLocal_parts types _ _ moved) tl tr _
        (List.mem_map.mpr ⟨piece, member, rfl⟩)

include facts in
/-- **The pieces of elimination spines at a base shape are typed.** -/
theorem elimAnyUnder_typed : ∀ {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n)
    {Γ : Ctx Head n} {pieces : List (Piece Head n)}, CtxFormed S.R Γ → LocalTypes Γ locals →
    elimAnyUnder locals annotation left right = some pieces →
    TypedEquality.Typed S.R Γ left annotation → TypedEquality.Typed S.R Γ right annotation →
    ∀ piece ∈ pieces, piece.Typed S.R Γ := by
  intro n locals annotation left right Γ pieces formed types found tl tr
  rcases elimAnyUnder_cases found with ⟨D, T, l, r, inner, rfl, rfl, rfl, computed, rfl⟩ | base
  · obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
    have below := elimAnyUnder_typed _ T l r (formed.snoc ⟨u, hu, tD⟩) (types.under D) computed
      (Typed.lam_inv facts tl formed) (Typed.lam_inv facts tr formed)
    intro piece member
    obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
    exact Piece.typed_under formed ⟨u, hu, tD⟩ (below original inside)
  · obtain ⟨_, TL, TR, read⟩ := elimAnyBase_spec base
    exact elimParts_pieces_typed facts formed (elimLocal_parts types left right read) tl tr

include facts roots heads algebra rigid complete in
/-- **Elimination spines at a base shape weigh more than their pieces**, in the store's own context. -/
theorem elimAnyUnder_weight : ∀ {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n)
    {Γ : Ctx Head n} {pieces : List (Piece Head n)}, CtxFormed S.R Γ → LocalTypes Γ locals →
    elimAnyUnder locals annotation left right = some pieces →
    TypedEquality.Typed S.R Γ left annotation → TypedEquality.Typed S.R Γ right annotation →
    ∃ w wl wr, PiecesWeigh S Γ pieces w ∧ HasWeight S Γ left annotation wl ∧ HasWeight S Γ right annotation wr ∧
      w + 2 ≤ wl + wr := by
  intro n locals annotation left right Γ pieces formed types found tl tr
  rcases elimAnyUnder_cases found with ⟨D, T, l, r, inner, rfl, rfl, rfl, computed, rfl⟩ | base
  · obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
    have isD : IsType S.R Γ D := ⟨u, hu, tD⟩
    have formedD := formed.snoc isD
    have tl' := Typed.lam_inv facts tl formed
    have tr' := Typed.lam_inv facts tr formed
    obtain ⟨w, wl, wr, weighs, left, right, total⟩ :=
      elimAnyUnder_weight _ T l r formedD (types.under D) computed tl' tr'
    have typed := elimAnyUnder_typed facts _ T l r formedD (types.under D) computed tl' tr'
    obtain ⟨v, hv, tPi⟩ := Typed.isType tl formed
    exact ⟨w, wl, wr, PiecesWeigh.under formed isD typed weighs, HasWeight.under (w := v) hv tPi isD left,
      HasWeight.under (w := v) hv tPi isD right, total⟩
  · obtain ⟨shape, TL, TR, read⟩ := elimAnyBase_spec base
    exact elim_weight facts roots heads algebra complete rigid formed (elimLocal_parts types left right read)
      (baseShape_spec shape) tl tr

end Theory

end ContextualDependentSpineEta
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
