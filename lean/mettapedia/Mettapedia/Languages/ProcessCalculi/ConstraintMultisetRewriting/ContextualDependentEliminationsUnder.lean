import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEliminations

/-!
# Elimination spines under abstractions

A store equation is read under the abstractions of its annotation, as R97 and R99 read spines and projections. The
head of an elimination spine must be one of the locals bound so far, with its type read from them (`elimLocal`), and
the base type must be rigid there (`rigidBase`), so that the reading is kept by every substitution that fixes the
locals (`elimLocal_subst`, `elimUnder_subst`). Under each abstraction the pieces are closed by `Piece.under`.

The reading at the base agrees with the reader over the context (`elimLocal_parts`), so it is typed, exact and lowers
the weight there (`elimBase_typed`, `elimBase_exact`, `elimBase_weight`), and so under abstractions
(`elimUnder_typed`, `elimUnder_exact`, `elimUnder_weight`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEliminations

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentFragment ContextualDependentDecisiveFragment
open ContextualDependentRigidFormers ContextualDependentEtaLong ContextualDependentRank
open ContextualDependentSpinesMany ContextualDependentConversionBudget ContextualDependentFragmentDecisive
open ContextualDependentRigidDecomposition ContextualDependentConstantHeadsProjections ContextualDependentOccursFull

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## The reader at the locals -/

section Locals

variable {n : Nat}

/-- **The reader with the head's type read from the locals.** -/
def elimLocal (locals : List (Tm Head n)) : Tm Head n → Tm Head n → Option (Read Head n)
  | .var h, .var h' => if h = h' then (locals[h.val]?).map fun T => ([], T, T) else none
  | .app f a, .app g b => appStep a b (elimLocal locals f g)
  | .fst p, .fst q => fstStep (elimLocal locals p q)
  | .snd p, .snd q => sndStep p q (elimLocal locals p q)
  | _, _ => none

/-- **At the locals of a context, the reader is the reader over the context.** -/
theorem elimLocal_parts {Γ : Ctx Head n} {locals : List (Tm Head n)} (types : LocalTypes Γ locals) :
    ∀ (left right : Tm Head n) {read : Read Head n},
      elimLocal locals left right = some read → elimParts Γ left right = some read
  | .var h, right, read, found => by
      cases right
      all_goals first | cases found | skip
      rename_i h'
      simp only [elimLocal] at found
      split at found
      · rename_i same
        subst same
        obtain ⟨T, looked, rfl⟩ := Option.map_eq_some_iff.mp found
        obtain ⟨_, same⟩ := types h.val T looked
        simp only [elimParts, if_true]
        rw [show h = ⟨h.val, h.isLt⟩ from rfl, same]
      · cases found
  | .app f a, right, read, found => by
      cases right
      all_goals first | cases found | skip
      rename_i g b
      obtain ⟨prefixPieces, DL, EL, DR, ER, prefixRead, result⟩ := appStep_some found
      subst result
      change appStep a b (elimParts Γ f g) = _
      rw [elimLocal_parts types f g prefixRead]
      rfl
  | .fst p, right, read, found => by
      cases right
      all_goals first | cases found | skip
      rename_i q
      obtain ⟨prefixPieces, AL, BL, AR, BR, prefixRead, result⟩ := fstStep_some found
      subst result
      change fstStep (elimParts Γ p q) = _
      rw [elimLocal_parts types p q prefixRead]
      rfl
  | .snd p, right, read, found => by
      cases right
      all_goals first | cases found | skip
      rename_i q
      obtain ⟨prefixPieces, AL, BL, AR, BR, prefixRead, result⟩ := sndStep_some found
      subst result
      change sndStep p q (elimParts Γ p q) = _
      rw [elimLocal_parts types p q prefixRead]
      rfl
  | .const _, _, _, found => by cases found
  | .head _, _, _, found => by cases found
  | .pi _ _, _, _, found => by cases found
  | .sigma _ _, _, _, found => by cases found
  | .id _ _ _, _, _, found => by cases found
  | .lam _, _, _, found => by cases found
  | .pair _ _, _, _, found => by cases found
  | .refl _, _, _, found => by cases found

/-- **The reading at the locals is kept by substitutions that fix them.** -/
theorem elimLocal_subst {m : Nat} (σ : Sub Head n m) {locals : List (Tm Head n)} (fixes : Fixes σ locals.length)
    (bound : locals.length ≤ m) :
    ∀ (left right : Tm Head n) {pieces : List (Piece Head n)} {TL TR : Tm Head n},
      elimLocal locals left right = some (pieces, TL, TR) →
      elimLocal (locals.map (Presentation.subst σ)) (Presentation.subst σ left) (Presentation.subst σ right) =
        some (pieces.map (Piece.subst σ), Presentation.subst σ TL, Presentation.subst σ TR)
  | .var h, right, pieces, TL, TR, found => by
      cases right
      all_goals first | cases found | skip
      rename_i h'
      simp only [elimLocal] at found
      split at found
      · rename_i same
        subst same
        obtain ⟨T, looked, result⟩ := Option.map_eq_some_iff.mp found
        cases result
        have small : h.val < locals.length := (List.getElem?_eq_some_iff.mp looked).1
        have image : σ h = .var ⟨h.val, by omega⟩ := fixes h.val h.isLt (by omega) small
        change elimLocal (locals.map (Presentation.subst σ)) (σ h) (σ h) = _
        rw [image]
        simp only [elimLocal, if_true, List.getElem?_map, looked, Option.map_some, List.map_nil]
      · cases found
  | .app f a, right, pieces, TL, TR, found => by
      cases right
      all_goals first | cases found | skip
      rename_i g b
      obtain ⟨prefixPieces, DL, EL, DR, ER, prefixRead, result⟩ := appStep_some found
      cases result
      change appStep (Presentation.subst σ a) (Presentation.subst σ b)
        (elimLocal (locals.map (Presentation.subst σ)) (Presentation.subst σ f) (Presentation.subst σ g)) = _
      rw [elimLocal_subst σ fixes bound f g prefixRead]
      simp only [Presentation.subst, appStep, subst_inst0, List.map_append, List.map_cons, List.map_nil, Piece.subst]
  | .fst p, right, pieces, TL, TR, found => by
      cases right
      all_goals first | cases found | skip
      rename_i q
      obtain ⟨prefixPieces, AL, BL, AR, BR, prefixRead, result⟩ := fstStep_some found
      cases result
      change fstStep (elimLocal (locals.map (Presentation.subst σ)) (Presentation.subst σ p)
        (Presentation.subst σ q)) = _
      rw [elimLocal_subst σ fixes bound p q prefixRead]
      rfl
  | .snd p, right, pieces, TL, TR, found => by
      cases right
      all_goals first | cases found | skip
      rename_i q
      obtain ⟨prefixPieces, AL, BL, AR, BR, prefixRead, result⟩ := sndStep_some found
      cases result
      change sndStep (Presentation.subst σ p) (Presentation.subst σ q)
        (elimLocal (locals.map (Presentation.subst σ)) (Presentation.subst σ p) (Presentation.subst σ q)) = _
      rw [elimLocal_subst σ fixes bound p q prefixRead]
      simp only [Presentation.subst, sndStep, subst_inst0]
  | .const _, _, _, _, _, found => by cases found
  | .head _, _, _, _, _, found => by cases found
  | .pi _ _, _, _, _, _, found => by cases found
  | .sigma _ _, _, _, _, _, found => by cases found
  | .id _ _ _, _, _, _, _, found => by cases found
  | .lam _, _, _, _, _, found => by cases found
  | .pair _ _, _, _, _, _, found => by cases found
  | .refl _, _, _, _, _, found => by cases found

/-- **The pieces of two elimination spines of one local at a rigid base type**, under the abstractions read so far. -/
def elimBase (locals : List (Tm Head n)) (C left right : Tm Head n) : Option (List (Piece Head n)) :=
  if rigidBase locals.length C then (elimLocal locals left right).map (·.1) else none

theorem elimBase_spec {locals : List (Tm Head n)} {C left right : Tm Head n} {pieces : List (Piece Head n)}
    (found : elimBase locals C left right = some pieces) :
    rigidBase locals.length C = true ∧ ∃ TL TR, elimLocal locals left right = some (pieces, TL, TR) := by
  unfold elimBase at found
  split at found
  · rename_i base
    obtain ⟨⟨pieces', TL, TR⟩, read, same⟩ := Option.map_eq_some_iff.mp found
    cases same
    exact ⟨base, TL, TR, read⟩
  · cases found

theorem elimBase_subst {m : Nat} (σ : Sub Head n m) {locals : List (Tm Head n)} (fixes : Fixes σ locals.length)
    (bound : locals.length ≤ m) {C left right : Tm Head n} {pieces : List (Piece Head n)}
    (found : elimBase locals C left right = some pieces) :
    elimBase (locals.map (Presentation.subst σ)) (Presentation.subst σ C) (Presentation.subst σ left)
      (Presentation.subst σ right) = some (pieces.map (Piece.subst σ)) := by
  obtain ⟨base, TL, TR, read⟩ := elimBase_spec found
  unfold elimBase
  rw [List.length_map, if_pos (rigidBase_subst fixes bound base), elimLocal_subst σ fixes bound left right read]
  rfl

end Locals

/-! ## Under abstractions -/

/-- **Elimination spines of one local under abstractions**, read from the annotation and the two sides. -/
def elimUnder : {n : Nat} → List (Tm Head n) → Tm Head n → Tm Head n → Tm Head n → Option (List (Piece Head n))
  | _, locals, .pi D T, .lam left, .lam right =>
      (elimUnder (Presentation.rename wk D :: locals.map (Presentation.rename wk)) T left right).map
        (List.map (Piece.under D))
  | _, locals, C, left, right => elimBase locals C left right

theorem elimUnder_cases {n : Nat} {locals : List (Tm Head n)} {annotation left right : Tm Head n}
    {pieces : List (Piece Head n)} (found : elimUnder locals annotation left right = some pieces) :
    (∃ D T l r inner, annotation = .pi D T ∧ left = .lam l ∧ right = .lam r ∧
      elimUnder (Presentation.rename wk D :: locals.map (Presentation.rename wk)) T l r = some inner ∧
      pieces = inner.map (Piece.under D)) ∨ elimBase locals annotation left right = some pieces := by
  cases annotation with
  | pi D T =>
      cases left with
      | lam l =>
          cases right with
          | lam r =>
              simp only [elimUnder, Option.map_eq_some_iff] at found
              obtain ⟨inner, computed, rfl⟩ := found
              exact .inl ⟨D, T, l, r, inner, rfl, rfl, rfl, computed, rfl⟩
          | _ => exact .inr (by simpa [elimUnder] using found)
      | _ => exact .inr (by simpa [elimUnder] using found)
  | _ => exact .inr (by simpa [elimUnder] using found)

theorem elimUnder_base {n : Nat} {locals : List (Tm Head n)} {C left right : Tm Head n}
    (notPi : ∀ D T, C ≠ .pi D T) : elimUnder locals C left right = elimBase locals C left right := by
  cases C with
  | pi D T => exact absurd rfl (notPi D T)
  | _ => simp [elimUnder]

/-- **The reading is kept by substitutions that fix the locals.** -/
theorem elimUnder_subst : ∀ {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n)
    {pieces : List (Piece Head n)}, elimUnder locals annotation left right = some pieces →
    ∀ {m : Nat} (σ : Sub Head n m), Fixes σ locals.length → locals.length ≤ m →
      elimUnder (locals.map (Presentation.subst σ)) (Presentation.subst σ annotation)
        (Presentation.subst σ left) (Presentation.subst σ right) = some (pieces.map (Piece.subst σ)) := by
  intro n locals annotation left right pieces found m σ fixes bound
  rcases elimUnder_cases found with ⟨D, T, l, r, inner, rfl, rfl, rfl, computed, rfl⟩ | base
  · have below := elimUnder_subst _ T l r computed (liftSub σ) (by simpa using fixes.lift) (by simp; omega)
    have localsSame : (Presentation.rename wk D :: locals.map (Presentation.rename wk)).map
        (Presentation.subst (liftSub σ)) =
        Presentation.rename wk (Presentation.subst σ D) :: (locals.map (Presentation.subst σ)).map
          (Presentation.rename wk) := by
      rw [List.map_cons, subst_liftSub_wk, List.map_map, List.map_map]
      congr 1
      congr 1
      funext t
      exact subst_liftSub_wk σ t
    rw [localsSame] at below
    simp only [List.map_map] at below
    simp only [Presentation.subst, elimUnder, List.map_map]
    rw [below]
    simp only [Option.map_some, List.map_map]
    rfl
  · obtain ⟨rigidC, _⟩ := elimBase_spec base
    have notPi' := rigidBase_not_pi (rigidBase_subst (n := n) fixes bound rigidC)
    rw [elimUnder_base notPi']
    exact elimBase_subst σ fixes bound base

section UnderTheory

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts in
theorem elimBase_typed {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {locals : List (Tm Head n)}
    (types : LocalTypes Γ locals) {C left right : Tm Head n} {pieces : List (Piece Head n)}
    (found : elimBase locals C left right = some pieces) (tl : TypedEquality.Typed S.R Γ left C)
    (tr : TypedEquality.Typed S.R Γ right C) : ∀ piece ∈ pieces, piece.Typed S.R Γ := by
  obtain ⟨_, TL, TR, read⟩ := elimBase_spec found
  exact elimParts_pieces_typed facts formed (elimLocal_parts types left right read) tl tr

include facts roots heads algebra complete in
theorem elimBase_exact {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {locals : List (Tm Head n)}
    (types : LocalTypes Γ locals) {C left right : Tm Head n} {pieces : List (Piece Head n)}
    (found : elimBase locals C left right = some pieces) (tl : TypedEquality.Typed S.R Γ left C)
    (tr : TypedEquality.Typed S.R Γ right C) :
    Equal S.R Γ left right C ↔ ∀ piece ∈ pieces, piece.Holds S.R Γ := by
  obtain ⟨rigidC, TL, TR, read⟩ := elimBase_spec found
  exact elim_exact facts roots heads algebra complete formed (elimLocal_parts types left right read)
    (rigidBase_spec rigidC) tl tr

include facts roots heads algebra rigid complete in
theorem elimBase_weight {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {locals : List (Tm Head n)}
    (types : LocalTypes Γ locals) {C left right : Tm Head n} {pieces : List (Piece Head n)}
    (found : elimBase locals C left right = some pieces) (tl : TypedEquality.Typed S.R Γ left C)
    (tr : TypedEquality.Typed S.R Γ right C) :
    ∃ w wl wr, PiecesWeigh S Γ pieces w ∧ HasWeight S Γ left C wl ∧ HasWeight S Γ right C wr ∧ w + 2 ≤ wl + wr := by
  obtain ⟨rigidC, TL, TR, read⟩ := elimBase_spec found
  exact elim_weight facts roots heads algebra complete rigid formed (elimLocal_parts types left right read)
    (rigidBase_spec rigidC) tl tr

include facts in
/-- **The pieces of elimination spines under abstractions are typed.** -/
theorem elimUnder_typed : ∀ {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n)
    {Γ : Ctx Head n} {pieces : List (Piece Head n)}, CtxFormed S.R Γ → LocalTypes Γ locals →
    elimUnder locals annotation left right = some pieces →
    TypedEquality.Typed S.R Γ left annotation → TypedEquality.Typed S.R Γ right annotation →
    ∀ piece ∈ pieces, piece.Typed S.R Γ
  | _, locals, .pi D T, left, right, Γ, pieces, formed, types, found, tl, tr => by
      rcases elimUnder_cases found with ⟨D', T', l, r, inner, same, rfl, rfl, computed, rfl⟩ | base
      · injection same with _ sameD sameT
        subst sameD
        subst sameT
        obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
        have below := elimUnder_typed _ T l r (formed.snoc ⟨u, hu, tD⟩) (types.under D) computed
          (Typed.lam_inv facts tl formed) (Typed.lam_inv facts tr formed)
        intro piece member
        obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
        exact Piece.typed_under formed ⟨u, hu, tD⟩ (below original inside)
      · exact elimBase_typed facts formed types base tl tr
  | _, locals, .var _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .const _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .head _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .sigma _ _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .id _ _ _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .lam _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .app _ _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .pair _ _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .fst _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .snd _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .refl _, left, right, Γ, pieces, formed, types, found, tl, tr => by
      rcases elimUnder_cases found with ⟨_, _, _, _, _, same, _⟩ | base
      · cases same
      · exact elimBase_typed facts formed types base tl tr

include facts roots heads algebra complete in
/-- **Elimination spines under abstractions decompose exactly** into their pieces, at every formed context. -/
theorem elimUnder_exact : ∀ {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n)
    {Γ : Ctx Head n} {pieces : List (Piece Head n)}, CtxFormed S.R Γ → LocalTypes Γ locals →
    elimUnder locals annotation left right = some pieces →
    TypedEquality.Typed S.R Γ left annotation → TypedEquality.Typed S.R Γ right annotation →
    (Equal S.R Γ left right annotation ↔ ∀ piece ∈ pieces, piece.Holds S.R Γ)
  | _, locals, .pi D T, left, right, Γ, pieces, formed, types, found, tl, tr => by
      rcases elimUnder_cases found with ⟨D', T', l, r, inner, same, rfl, rfl, computed, rfl⟩ | base
      · injection same with _ sameD sameT
        subst sameD
        subst sameT
        obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
        have isD : IsType S.R Γ D := ⟨u, hu, tD⟩
        have formedD := formed.snoc isD
        have tl' := Typed.lam_inv facts tl formed
        have tr' := Typed.lam_inv facts tr formed
        have below := elimUnder_exact _ T l r formedD (types.under D) computed tl' tr'
        have typed := elimUnder_typed facts _ T l r formedD (types.under D) computed tl' tr'
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
      · exact elimBase_exact facts roots heads algebra complete formed types base tl tr
  | _, locals, .var _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .const _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .head _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .sigma _ _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .id _ _ _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .lam _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .app _ _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .pair _ _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .fst _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .snd _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .refl _, left, right, Γ, pieces, formed, types, found, tl, tr => by
      rcases elimUnder_cases found with ⟨_, _, _, _, _, same, _⟩ | base
      · cases same
      · exact elimBase_exact facts roots heads algebra complete formed types base tl tr

include facts roots heads algebra rigid complete in
/-- **Elimination spines under abstractions weigh more than their pieces.** -/
theorem elimUnder_weight : ∀ {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n)
    {Γ : Ctx Head n} {pieces : List (Piece Head n)}, CtxFormed S.R Γ → LocalTypes Γ locals →
    elimUnder locals annotation left right = some pieces →
    TypedEquality.Typed S.R Γ left annotation → TypedEquality.Typed S.R Γ right annotation →
    ∃ w wl wr, PiecesWeigh S Γ pieces w ∧ HasWeight S Γ left annotation wl ∧ HasWeight S Γ right annotation wr ∧
      w + 2 ≤ wl + wr
  | _, locals, .pi D T, left, right, Γ, pieces, formed, types, found, tl, tr => by
      rcases elimUnder_cases found with ⟨D', T', l, r, inner, same, rfl, rfl, computed, rfl⟩ | base
      · injection same with _ sameD sameT
        subst sameD
        subst sameT
        obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
        have isD : IsType S.R Γ D := ⟨u, hu, tD⟩
        have formedD := formed.snoc isD
        have tl' := Typed.lam_inv facts tl formed
        have tr' := Typed.lam_inv facts tr formed
        obtain ⟨w, wl, wr, weighs, left, right, total⟩ :=
          elimUnder_weight _ T l r formedD (types.under D) computed tl' tr'
        have typed := elimUnder_typed facts _ T l r formedD (types.under D) computed tl' tr'
        obtain ⟨v, hv, tPi⟩ := Typed.isType tl formed
        exact ⟨w, wl, wr, PiecesWeigh.under formed isD typed weighs, HasWeight.under (w := v) hv tPi isD left,
          HasWeight.under (w := v) hv tPi isD right, total⟩
      · exact elimBase_weight facts roots heads algebra rigid complete formed types base tl tr
  | _, locals, .var _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .const _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .head _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .sigma _ _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .id _ _ _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .lam _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .app _ _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .pair _ _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .fst _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .snd _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .refl _, left, right, Γ, pieces, formed, types, found, tl, tr => by
      rcases elimUnder_cases found with ⟨_, _, _, _, _, same, _⟩ | base
      · cases same
      · exact elimBase_weight facts roots heads algebra rigid complete formed types base tl tr

end UnderTheory

end ContextualDependentEliminations
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
