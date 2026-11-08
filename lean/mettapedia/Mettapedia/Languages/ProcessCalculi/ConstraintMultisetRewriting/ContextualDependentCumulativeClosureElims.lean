import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosureProjections

/-!
# Closure of the cumulative round: elimination spines

R99's decomposition of elimination spines (`elimsWeighed`, at a rigid base type) and its decomposition at a base shape
(`flexWeighed`) read `λ z̄. e ≐ λ z̄. e'` for two elimination spines of one local, mixing applications and projections
(`elimLocal`), with one argument piece per application, each at the domains of the two literal prefix types.

* **Reducts.** Reduction keeps an elimination spine an elimination spine and keeps its head rigid (`flexHead_star`), so
  a normal Miller elimination spine of a rigid local has normal Miller arguments (`elimLocal_reducts`).
* **Stratification.** When the pieces of a prefix hold, the two literal prefix types are equal; the next domains are
  then equal, and a second projection instantiates the two families at equal first projections
  (`elimParts_internal`). Under abstractions this is read at every substitution that fixes the locals
  (`elimUnder_internal`, `elimAnyUnder_internal_subst`).

So both decompositions keep the permuted class (`decomposeElims_keeps`, `decomposeFlex_keeps`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCumulativeClosure

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentFragment ContextualDependentRank
open ContextualDependentMillerClosure ContextualDependentShortClosure ContextualDependentDynamicFragment
open ContextualDependentExecutableJoin ContextualDependentSpinesMany ContextualDependentRigidFormers
open ContextualDependentClosure ContextualDependentConstantHeadsProjections ContextualDependentEliminations
open ContextualDependentSpineEta
open ContextualDependentGeneralPattern (liftFlexible)

/-! ## Reducts of elimination spines -/

section Reducts

variable {Head : Type} {R : Rules Head} (empty : R.computation = RootComputation.empty)
include empty

/-- **A step keeps the head of an elimination spine rigid.** -/
theorem flexHead_step {n : Nat} {mark : Fin n → Bool} :
    ∀ {f f' : Tm Head n}, Elim f → flexHead mark (spineHead f) = false → StrongNormalization.Reduces R f f' →
      flexHead mark (spineHead f') = false
  | .var _, _, _, _, step => by
      cases step with
      | root impossible => exact False.elim (no_root empty impossible)
  | .const _, _, _, _, step => by
      cases step with
      | root impossible => exact False.elim (no_root empty impossible)
  | .app g b, _, elim, head, step => by
      cases elim with
      | app inner =>
          cases step with
          | root impossible => exact False.elim (no_root empty impossible)
          | betaPi body _ => exact False.elim (Elim.not_lam inner)
          | congAppFun s =>
              have inside := flexHead_step (f := g) inner head s
              exact inside
          | congAppArg _ => exact head
  | .fst p, _, elim, _, step => by
      cases elim with
      | fst inner =>
          cases step with
          | root impossible => exact False.elim (no_root empty impossible)
          | betaSigmaFst => exact False.elim (Elim.not_pair inner)
          | congFst _ => rfl
  | .snd p, _, elim, _, step => by
      cases elim with
      | snd inner =>
          cases step with
          | root impossible => exact False.elim (no_root empty impossible)
          | betaSigmaSnd => exact False.elim (Elim.not_pair inner)
          | congSnd _ => rfl
  | .head _, _, elim, _, _ | .pi _ _, _, elim, _, _ | .sigma _ _, _, elim, _, _ | .id _ _ _, _, elim, _, _
  | .lam _, _, elim, _, _ | .pair _ _, _, elim, _, _ | .refl _, _, elim, _, _ => by cases elim

theorem flexHead_star {n : Nat} {mark : Fin n → Bool} {f f' : Tm Head n} (elim : Elim f)
    (head : flexHead mark (spineHead f) = false) (steps : Star (R := R) f f') :
    flexHead mark (spineHead f') = false := by
  induction steps with
  | refl => exact head
  | tail before step ih => exact flexHead_step empty (elim.star empty before) ih step

/-- A normal Miller application of a rigid elimination spine has a normal Miller function and argument. -/
theorem MarkedReduct.of_app {n : Nat} {mark : Fin n → Bool} {f a : Tm Head n} (elim : Elim f)
    (head : flexHead mark (spineHead f) = false) (outer : MarkedReduct R mark (.app f a)) :
    MarkedReduct R mark f ∧ MarkedReduct R mark a := by
  obtain ⟨X, toX, normalX, millerX⟩ := outer
  obtain ⟨f', a', rfl, toF, toA, _⟩ := star_app_inv empty elim toX
  obtain ⟨_, normalF, normalA⟩ := (normal_app_iff empty).mp normalX
  obtain ⟨millerF, millerA⟩ := decompose_app (flexHead_star empty elim head toF) millerX
  exact ⟨⟨f', toF, normalF, millerF⟩, ⟨a', toA, normalA, millerA⟩⟩

end Reducts

section Local

variable {Head : Type} {n : Nat}

/-- **A reading at the locals reads elimination spines of rigid locals.** -/
theorem elimLocal_head {locals : List (Tm Head n)} {mark : Fin n → Bool}
    (localsRigid : ∀ j : Fin n, j.val < locals.length → mark j = false) :
    ∀ (left right : Tm Head n) {read : Read Head n}, elimLocal locals left right = some read →
      Elim left ∧ Elim right ∧ flexHead mark (spineHead left) = false ∧ flexHead mark (spineHead right) = false
  | .var h, right, read, found => by
      cases right
      all_goals first | cases found | skip
      rename_i h'
      simp only [elimLocal] at found
      split at found
      · rename_i same
        subst same
        obtain ⟨T, looked, _⟩ := Option.map_eq_some_iff.mp found
        have small : h.val < locals.length := (List.getElem?_eq_some_iff.mp looked).1
        exact ⟨.var h, .var h, localsRigid h small, localsRigid h small⟩
      · cases found
  | .app f a, right, read, found => by
      cases right
      all_goals first | cases found | skip
      rename_i g b
      obtain ⟨_, _, _, _, _, prefixRead, _⟩ := appStep_some found
      obtain ⟨elimF, elimG, headF, headG⟩ := elimLocal_head localsRigid f g prefixRead
      exact ⟨.app elimF, .app elimG, headF, headG⟩
  | .fst p, right, read, found => by
      cases right
      all_goals first | cases found | skip
      rename_i q
      obtain ⟨_, _, _, _, _, prefixRead, _⟩ := fstStep_some found
      obtain ⟨elimP, elimQ, _, _⟩ := elimLocal_head localsRigid p q prefixRead
      exact ⟨.fst elimP, .fst elimQ, rfl, rfl⟩
  | .snd p, right, read, found => by
      cases right
      all_goals first | cases found | skip
      rename_i q
      obtain ⟨_, _, _, _, _, prefixRead, _⟩ := sndStep_some found
      obtain ⟨elimP, elimQ, _, _⟩ := elimLocal_head localsRigid p q prefixRead
      exact ⟨.snd elimP, .snd elimQ, rfl, rfl⟩
  | .const _, _, _, found => by cases found
  | .head _, _, _, found => by cases found
  | .pi _ _, _, _, found => by cases found
  | .sigma _ _, _, _, found => by cases found
  | .id _ _ _, _, _, found => by cases found
  | .lam _, _, _, found => by cases found
  | .pair _ _, _, _, found => by cases found
  | .refl _, _, _, found => by cases found

variable {R : Rules Head} (empty : R.computation = RootComputation.empty)
include empty

/-- **The arguments of two elimination spines of rigid locals have Miller normal reducts** when the spines do. -/
theorem elimLocal_reducts {locals : List (Tm Head n)} {mark : Fin n → Bool}
    (localsRigid : ∀ j : Fin n, j.val < locals.length → mark j = false) :
    ∀ (left right : Tm Head n) {read : Read Head n}, elimLocal locals left right = some read →
      MarkedReduct R mark left → MarkedReduct R mark right →
      ∀ piece ∈ read.1, MarkedReduct R mark piece.left ∧ MarkedReduct R mark piece.right
  | .var h, right, read, found, _, _ => by
      cases right
      all_goals first | cases found | skip
      rename_i h'
      simp only [elimLocal] at found
      split at found
      · obtain ⟨T, _, rfl⟩ := Option.map_eq_some_iff.mp found
        intro piece member
        cases member
      · cases found
  | .app f a, right, read, found, leftReduct, rightReduct => by
      cases right
      all_goals first | cases found | skip
      rename_i g b
      obtain ⟨prefixPieces, DL, EL, DR, ER, prefixRead, result⟩ := appStep_some found
      subst result
      obtain ⟨elimF, elimG, headF, headG⟩ := elimLocal_head localsRigid f g prefixRead
      obtain ⟨rf, ra⟩ := MarkedReduct.of_app empty elimF headF leftReduct
      obtain ⟨rg, rb⟩ := MarkedReduct.of_app empty elimG headG rightReduct
      intro piece member
      rcases List.mem_append.mp member with inPrefix | isLast
      · exact elimLocal_reducts localsRigid f g prefixRead rf rg piece inPrefix
      · rw [List.mem_singleton.mp isLast]
        exact ⟨ra, rb⟩
  | .fst p, right, read, found, leftReduct, rightReduct => by
      cases right
      all_goals first | cases found | skip
      rename_i q
      obtain ⟨prefixPieces, AL, BL, AR, BR, prefixRead, result⟩ := fstStep_some found
      subst result
      obtain ⟨elimP, elimQ, _, _⟩ := elimLocal_head localsRigid p q prefixRead
      have inner := elimLocal_reducts localsRigid p q prefixRead
        (MarkedReduct.of_project empty true elimP leftReduct) (MarkedReduct.of_project empty true elimQ rightReduct)
      exact inner
  | .snd p, right, read, found, leftReduct, rightReduct => by
      cases right
      all_goals first | cases found | skip
      rename_i q
      obtain ⟨prefixPieces, AL, BL, AR, BR, prefixRead, result⟩ := sndStep_some found
      subst result
      obtain ⟨elimP, elimQ, _, _⟩ := elimLocal_head localsRigid p q prefixRead
      have inner := elimLocal_reducts localsRigid p q prefixRead
        (MarkedReduct.of_project empty false elimP leftReduct)
        (MarkedReduct.of_project empty false elimQ rightReduct)
      exact inner
  | .const _, _, _, found, _, _ => by cases found
  | .head _, _, _, found, _, _ => by cases found
  | .pi _ _, _, _, found, _, _ => by cases found
  | .sigma _ _, _, _, found, _, _ => by cases found
  | .id _ _ _, _, _, found, _, _ => by cases found
  | .lam _, _, _, found, _, _ => by cases found
  | .pair _ _, _, _, found, _, _ => by cases found
  | .refl _, _, _, found, _, _ => by cases found

end Local

section Pieces

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

theorem lifted_rigid {n : Nat} {mark : Fin n → Bool} (D : Tm Head n) {locals : List (Tm Head n)}
    (localsRigid : ∀ j : Fin n, j.val < locals.length → mark j = false) :
    ∀ j : Fin (n + 1), j.val < (Presentation.rename wk D :: locals.map (Presentation.rename wk)).length →
      liftFlexible mark j = false := by
  intro j
  refine Fin.cases (motive := fun j : Fin (n + 1) =>
    j.val < (Presentation.rename wk D :: locals.map (Presentation.rename wk)).length →
      liftFlexible mark j = false) ?_ (fun j small => ?_) j
  · intro _
    rfl
  · change mark j = false
    simp only [List.length_cons, List.length_map, Fin.val_succ] at small
    exact localsRigid j (by omega)

/-- **The pieces of elimination spines under abstractions have Miller normal reducts.** -/
theorem elimUnder_reducts (empty : S.R.computation = RootComputation.empty) :
    ∀ {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n) {pieces : List (Piece Head n)}
      (mark : Fin n → Bool), (∀ j : Fin n, j.val < locals.length → mark j = false) →
      elimUnder locals annotation left right = some pieces →
      MarkedReduct S.R mark left → MarkedReduct S.R mark right →
      ∀ piece ∈ pieces, MarkedReduct S.R mark piece.left ∧ MarkedReduct S.R mark piece.right := by
  intro n locals annotation left right pieces mark localsRigid found leftReduct rightReduct
  rcases elimUnder_cases found with ⟨D, T, l, r, inner, rfl, rfl, rfl, computed, rfl⟩ | base
  · intro piece member
    obtain ⟨original, inInner, rfl⟩ := List.mem_map.mp member
    obtain ⟨pl, pr⟩ := elimUnder_reducts empty _ T l r (liftFlexible mark) (lifted_rigid D localsRigid) computed
      (MarkedReduct.of_lam empty leftReduct) (MarkedReduct.of_lam empty rightReduct) original inInner
    exact ⟨MarkedReduct.lam empty pl, MarkedReduct.lam empty pr⟩
  · obtain ⟨_, TL, TR, read⟩ := elimBase_spec base
    exact elimLocal_reducts empty localsRigid left right read leftReduct rightReduct

/-- **The pieces of elimination spines at a base shape under abstractions have Miller normal reducts.** -/
theorem elimAnyUnder_reducts (empty : S.R.computation = RootComputation.empty) :
    ∀ {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n) {pieces : List (Piece Head n)}
      (mark : Fin n → Bool), (∀ j : Fin n, j.val < locals.length → mark j = false) →
      elimAnyUnder locals annotation left right = some pieces →
      MarkedReduct S.R mark left → MarkedReduct S.R mark right →
      ∀ piece ∈ pieces, MarkedReduct S.R mark piece.left ∧ MarkedReduct S.R mark piece.right := by
  intro n locals annotation left right pieces mark localsRigid found leftReduct rightReduct
  rcases elimAnyUnder_cases found with ⟨D, T, l, r, inner, rfl, rfl, rfl, computed, rfl⟩ | base
  · intro piece member
    obtain ⟨original, inInner, rfl⟩ := List.mem_map.mp member
    obtain ⟨pl, pr⟩ := elimAnyUnder_reducts empty _ T l r (liftFlexible mark) (lifted_rigid D localsRigid)
      computed (MarkedReduct.of_lam empty leftReduct) (MarkedReduct.of_lam empty rightReduct) original inInner
    exact ⟨MarkedReduct.lam empty pl, MarkedReduct.lam empty pr⟩
  · obtain ⟨_, TL, TR, read⟩ := elimAnyBase_spec base
    exact elimLocal_reducts empty localsRigid left right read leftReduct rightReduct

variable (facts : FormFacts S.R S.roles)
include facts

/-- **Elimination spines are stratified along their prefixes**: the domains of a piece are equal types once the
pieces before it hold, and the two literal types are equal once every piece holds. -/
theorem elimParts_internal {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) :
    ∀ (left right : Tm Head n) {pieces : List (Piece Head n)} {TL TR : Tm Head n},
      elimParts Γ left right = some (pieces, TL, TR) →
      TypedEquality.Typed S.R Γ left TL → TypedEquality.Typed S.R Γ right TR →
      (∀ piece ∈ pieces, piece.Typed S.R Γ) →
      (∀ (first last : List (Piece Head n)) (piece : Piece Head n), pieces = first ++ piece :: last →
        (∀ q ∈ first, q.Holds S.R Γ) → TypeEq S.R Γ piece.leftType piece.rightType) ∧
      ((∀ q ∈ pieces, q.Holds S.R Γ) → TypeEq S.R Γ TL TR)
  | .var h, right, pieces, TL, TR, found, tl, _, _ => by
      cases right
      all_goals first | cases found | skip
      simp only [elimParts] at found
      split at found
      · cases found
        have isT := Typed.isType tl formed
        exact ⟨fun first last piece split => absurd split.symm (by simp), fun _ => isT.refl⟩
      · cases found
  | .app f a, right, pieces, TL, TR, found, tl, tr, typed => by
      cases right
      all_goals first | cases found | skip
      rename_i g b
      obtain ⟨prefixPieces, DL, EL, DR, ER, read, result⟩ := appStep_some found
      cases result
      obtain ⟨A₁, B₁, tf, _, _⟩ := Typed.generation tl
      obtain ⟨tfL, _, _⟩ := elimParts_typed facts formed f g read tf
      obtain ⟨A₂, B₂, tg, _, _⟩ := Typed.generation tr
      obtain ⟨tgR, _, _⟩ := elimParts_typed facts formed g f (elimParts_swap Γ f g read) tg
      obtain ⟨prefixInternal, prefixFinal⟩ := elimParts_internal formed f g read tfL tgR
        (fun piece member => typed piece (List.mem_append_left _ member))
      obtain ⟨ta, tb⟩ := typed _ (List.mem_append_right _ List.mem_cons_self)
      refine ⟨fun first last piece split held => ?_, fun held => ?_⟩
      · rcases List.eq_nil_or_concat last with rfl | ⟨middle, final, rfl⟩
        · obtain ⟨samePrefix, sameLast⟩ := List.append_inj' split (by simp)
          simp only [List.cons.injEq, and_true] at sameLast
          subst sameLast
          subst samePrefix
          exact ((ContextualDependentRigid.typeEq_pi_iff facts formed).mp (prefixFinal held)).1
        · have split' : prefixPieces ++ [⟨DL, a, DR, b⟩] = (first ++ piece :: middle) ++ [final] := by
            rw [split]
            simp
          obtain ⟨samePrefix, _⟩ := List.append_inj' split' (by simp)
          exact prefixInternal first middle piece samePrefix held
      · have prefixTypes := prefixFinal (fun q member => held q (List.mem_append_left _ member))
        obtain ⟨domainsLR, codomainsLR⟩ := (ContextualDependentRigid.typeEq_pi_iff facts formed).mp prefixTypes
        have firsts : Equal S.R Γ a b DL := (held _ (List.mem_append_right _ List.mem_cons_self)).2
        obtain ⟨_, ⟨v', hv', tER⟩⟩ := IsType.pi_parts (Typed.isType tgR formed)
        have tER' := Typed.stable tER (CtxEq.snoc (CtxEq.refl Γ formed) domainsLR)
        exact TypeEq.trans S.levels (TypeEq.instantiate codomainsLR ta) (TypeEq.of_instantiateEq tER' hv' ta firsts)
  | .fst p, right, pieces, TL, TR, found, tl, tr, typed => by
      cases right
      all_goals first | cases found | skip
      rename_i q
      obtain ⟨prefixPieces, AL, BL, AR, BR, read, result⟩ := fstStep_some found
      cases result
      obtain ⟨A₁, B₁, tp, _⟩ := Typed.generation tl
      obtain ⟨tpL, _, _⟩ := elimParts_typed facts formed p q read tp
      obtain ⟨A₂, B₂, tq, _⟩ := Typed.generation tr
      obtain ⟨tqR, _, _⟩ := elimParts_typed facts formed q p (elimParts_swap Γ p q read) tq
      obtain ⟨prefixInternal, prefixFinal⟩ := elimParts_internal formed p q read tpL tqR typed
      exact ⟨prefixInternal, fun held =>
        ((ContextualDependentRigid.typeEq_sigma_iff facts formed).mp (prefixFinal held)).1⟩
  | .snd p, right, pieces, TL, TR, found, tl, tr, typed => by
      cases right
      all_goals first | cases found | skip
      rename_i q
      obtain ⟨prefixPieces, AL, BL, AR, BR, read, result⟩ := sndStep_some found
      cases result
      obtain ⟨A₁, B₁, tp, _⟩ := Typed.generation tl
      obtain ⟨tpL, _, _⟩ := elimParts_typed facts formed p q read tp
      obtain ⟨A₂, B₂, tq, _⟩ := Typed.generation tr
      obtain ⟨tqR, _, _⟩ := elimParts_typed facts formed q p (elimParts_swap Γ p q read) tq
      obtain ⟨prefixInternal, prefixFinal⟩ := elimParts_internal formed p q read tpL tqR typed
      refine ⟨prefixInternal, fun held => ?_⟩
      obtain ⟨domainsLR, codomainsLR⟩ := (ContextualDependentRigid.typeEq_sigma_iff facts formed).mp (prefixFinal held)
      have tFst : TypedEquality.Typed S.R Γ (.fst p) AL := Derivable.fstElim tpL
      have firsts : Equal S.R Γ (.fst p) (.fst q) AL := .fstCong (elimParts_congr p q read held)
      obtain ⟨_, ⟨v', hv', tBR⟩⟩ := IsType.sigma_parts (Typed.isType tqR formed)
      have tBR' := Typed.stable tBR (CtxEq.snoc (CtxEq.refl Γ formed) domainsLR)
      exact TypeEq.trans S.levels (TypeEq.instantiate codomainsLR tFst) (TypeEq.of_instantiateEq tBR' hv' tFst firsts)
  | .const _, _, _, _, _, found, _, _, _ => by cases found
  | .head _, _, _, _, _, found, _, _, _ => by cases found
  | .pi _ _, _, _, _, _, found, _, _, _ => by cases found
  | .sigma _ _, _, _, _, _, found, _, _, _ => by cases found
  | .id _ _ _, _, _, _, _, found, _, _, _ => by cases found
  | .lam _, _, _, _, _, found, _, _, _ => by cases found
  | .pair _ _, _, _, _, _, found, _, _, _ => by cases found
  | .refl _, _, _, _, _, found, _, _, _ => by cases found

/-- The stratification of a reading at the locals, from typed spines at any types. -/
theorem elimLocal_internal {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {locals : List (Tm Head n)}
    (types : LocalTypes Γ locals) {left right C D : Tm Head n} {pieces : List (Piece Head n)} {TL TR : Tm Head n}
    (read : elimLocal locals left right = some (pieces, TL, TR)) (tl : TypedEquality.Typed S.R Γ left C)
    (tr : TypedEquality.Typed S.R Γ right D) :
    ∀ (first last : List (Piece Head n)) (piece : Piece Head n), pieces = first ++ piece :: last →
      (∀ q ∈ first, q.Holds S.R Γ) → TypeEq S.R Γ piece.leftType piece.rightType := by
  have parts := elimLocal_parts types left right read
  have tlL := (elimParts_typed facts formed left right parts tl).1
  have trR := (elimParts_typed facts formed right left (elimParts_swap Γ left right parts) tr).1
  exact (elimParts_internal facts formed left right parts tlL trR
    (elimParts_pieces_typed facts formed parts tl tr)).1

/-- **The pieces of elimination spines under abstractions are stratified among themselves.** -/
theorem elimUnder_internal : ∀ {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n)
    {Γ : Ctx Head n} {pieces : List (Piece Head n)}, CtxFormed S.R Γ → LocalTypes Γ locals →
    elimUnder locals annotation left right = some pieces →
    TypedEquality.Typed S.R Γ left annotation → TypedEquality.Typed S.R Γ right annotation →
    ∀ (first last : List (Piece Head n)) (piece : Piece Head n), pieces = first ++ piece :: last →
      (∀ q ∈ first, q.Holds S.R Γ) → TypeEq S.R Γ piece.leftType piece.rightType := by
  intro n locals annotation left right Γ pieces formed types found tl tr first last piece split held
  rcases elimUnder_cases found with ⟨D, T, l, r, inner, rfl, rfl, rfl, computed, rfl⟩ | base
  · obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
    have isD : IsType S.R Γ D := ⟨u, hu, tD⟩
    have formedD := formed.snoc isD
    have tl' := Typed.lam_inv facts tl formed
    have tr' := Typed.lam_inv facts tr formed
    have typed := elimUnder_typed facts _ T l r formedD (types.under D) computed tl' tr'
    obtain ⟨first', rest', innerSplit, rfl, mapped⟩ := List.map_eq_append_iff.mp split
    obtain ⟨piece', last', rfl, rfl, rfl⟩ := List.map_eq_cons_iff.mp mapped
    have held' : ∀ q ∈ first', q.Holds S.R (.snoc Γ D) := fun q member =>
      (Piece.holds_under facts formed isD (typed q (by rw [innerSplit]; exact List.mem_append_left _ member))).mp
        (held (q.under D) (List.mem_map.mpr ⟨q, member, rfl⟩))
    have below := elimUnder_internal _ T l r formedD (types.under D) computed tl' tr' first' last' piece'
      innerSplit held'
    exact (ContextualDependentRigid.typeEq_pi_iff facts formed).mpr ⟨isD.refl, below⟩
  · obtain ⟨_, TL, TR, read⟩ := elimBase_spec base
    exact elimLocal_internal facts formed types read tl tr first last piece split held

theorem elimAnyBase_internal_subst {n : Nat} {locals : List (Tm Head n)} {annotation left right : Tm Head n}
    {pieces : List (Piece Head n)} (base : elimAnyBase locals annotation left right = some pieces)
    {m : Nat} (σ : Sub Head n m) {Γ : Ctx Head m} (fixes : Fixes σ locals.length) (bound : locals.length ≤ m)
    (formed : CtxFormed S.R Γ) (types : LocalTypes Γ (locals.map (Presentation.subst σ)))
    (tl : TypedEquality.Typed S.R Γ (Presentation.subst σ left) (Presentation.subst σ annotation))
    (tr : TypedEquality.Typed S.R Γ (Presentation.subst σ right) (Presentation.subst σ annotation))
    (first last : List (Piece Head n)) (piece : Piece Head n) (split : pieces = first ++ piece :: last)
    (held : ∀ q ∈ first, (q.subst σ).Holds S.R Γ) :
    TypeEq S.R Γ (Presentation.subst σ piece.leftType) (Presentation.subst σ piece.rightType) := by
  obtain ⟨_, TL, TR, read⟩ := elimAnyBase_spec base
  have moved := elimLocal_subst σ fixes bound left right read
  exact elimLocal_internal facts formed types moved tl tr (first.map (Piece.subst σ)) (last.map (Piece.subst σ))
    (piece.subst σ) (by rw [split]; simp) (fun q member => by
      obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
      exact held original inside)

/-- **The pieces of elimination spines at a base shape are stratified at every substitution fixing the locals.** -/
theorem elimAnyUnder_internal_subst : ∀ {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n)
    {pieces : List (Piece Head n)}, elimAnyUnder locals annotation left right = some pieces →
    ∀ {m : Nat} (σ : Sub Head n m) {Γ : Ctx Head m}, Fixes σ locals.length → locals.length ≤ m →
      CtxFormed S.R Γ → LocalTypes Γ (locals.map (Presentation.subst σ)) →
      TypedEquality.Typed S.R Γ (Presentation.subst σ left) (Presentation.subst σ annotation) →
      TypedEquality.Typed S.R Γ (Presentation.subst σ right) (Presentation.subst σ annotation) →
      ∀ (first last : List (Piece Head n)) (piece : Piece Head n), pieces = first ++ piece :: last →
        (∀ q ∈ first, (q.subst σ).Holds S.R Γ) →
        TypeEq S.R Γ (Presentation.subst σ piece.leftType) (Presentation.subst σ piece.rightType)
  | _, locals, .pi D T, left, right, pieces, found, _, σ, Γ, fixes, bound, formed, types, tl, tr, first, last, piece,
      split, held => by
    rcases elimAnyUnder_cases found with ⟨D', T', l, r, inner, same, rfl, rfl, computed, rfl⟩ | base
    · injection same with _ sameD sameT
      subst sameD
      subst sameT
      change TypedEquality.Typed S.R Γ (.lam (Presentation.subst (liftSub σ) l))
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
      have typed := elimAnyUnder_exact_subst.elimAnyUnder_typed_subst facts _ T l r
        computed (liftSub σ) (by simpa using fixes.lift) (by simp; omega) formedD typesD tl' tr'
      obtain ⟨first', rest', innerSplit, rfl, mapped⟩ := List.map_eq_append_iff.mp split
      obtain ⟨piece', last', rfl, rfl, rfl⟩ := List.map_eq_cons_iff.mp mapped
      have held' : ∀ q ∈ first', (q.subst (liftSub σ)).Holds S.R (.snoc Γ (Presentation.subst σ D)) := by
        intro q member
        have outer := held (q.under D) (List.mem_map.mpr ⟨q, member, rfl⟩)
        rw [Piece.subst_under] at outer
        exact (Piece.holds_under facts formed isD
          (typed q (by rw [innerSplit]; exact List.mem_append_left _ member))).mp outer
      have below := elimAnyUnder_internal_subst _ T l r computed (liftSub σ) (by simpa using fixes.lift)
        (by simp; omega) formedD typesD tl' tr' first' last' piece' innerSplit held'
      change TypeEq S.R Γ (.pi (Presentation.subst σ D) (Presentation.subst (liftSub σ) piece'.leftType))
        (.pi (Presentation.subst σ D) (Presentation.subst (liftSub σ) piece'.rightType))
      exact (ContextualDependentRigid.typeEq_pi_iff facts formed).mpr ⟨isD.refl, below⟩
    · exact elimAnyBase_internal_subst facts base σ fixes bound formed types tl tr first last piece split held
  | _, locals, .var _, left, right, pieces, found, _, σ, Γ, fixes, bound, formed, types, tl, tr, first, last, piece,
      split, held
  | _, locals, .const _, left, right, pieces, found, _, σ, Γ, fixes, bound, formed, types, tl, tr, first, last, piece,
      split, held
  | _, locals, .head _, left, right, pieces, found, _, σ, Γ, fixes, bound, formed, types, tl, tr, first, last, piece,
      split, held
  | _, locals, .sigma _ _, left, right, pieces, found, _, σ, Γ, fixes, bound, formed, types, tl, tr, first, last,
      piece, split, held
  | _, locals, .id _ _ _, left, right, pieces, found, _, σ, Γ, fixes, bound, formed, types, tl, tr, first, last,
      piece, split, held
  | _, locals, .lam _, left, right, pieces, found, _, σ, Γ, fixes, bound, formed, types, tl, tr, first, last, piece,
      split, held
  | _, locals, .app _ _, left, right, pieces, found, _, σ, Γ, fixes, bound, formed, types, tl, tr, first, last,
      piece, split, held
  | _, locals, .pair _ _, left, right, pieces, found, _, σ, Γ, fixes, bound, formed, types, tl, tr, first, last,
      piece, split, held
  | _, locals, .fst _, left, right, pieces, found, _, σ, Γ, fixes, bound, formed, types, tl, tr, first, last, piece,
      split, held
  | _, locals, .snd _, left, right, pieces, found, _, σ, Γ, fixes, bound, formed, types, tl, tr, first, last, piece,
      split, held
  | _, locals, .refl _, left, right, pieces, found, _, σ, Γ, fixes, bound, formed, types, tl, tr, first, last, piece,
      split, held => by
    rcases elimAnyUnder_cases found with ⟨_, _, _, _, _, same, _⟩ | base
    · cases same
    · exact elimAnyBase_internal_subst facts base σ fixes bound formed types tl tr first last piece split held

end Pieces

/-! ## The decompositions of elimination spines -/

section Splice

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **Replacing an equation by pieces with Miller reducts, stratified at every substitution, keeps the permuted
class**: the common shape of the splices of this file. -/
theorem PermutedMiller.splice_reading (rigid : ∀ name, S.roles name = .rigid)
    (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R)
    {Θ : Context S.R} {before after : EquationStore (TotalTerm Θ)}
    {equation : Equation (TotalTerm Θ)} (permuted : PermutedMiller S.levels (before ++ equation :: after))
    {pieces : List (Piece Head Θ.arity)}
    (reducts : MarkedReduct S.R (fun _ => true) equation.1.2.code →
      MarkedReduct S.R (fun _ => true) equation.2.2.code →
      ∀ piece ∈ pieces, MarkedReduct S.R (fun _ => true) piece.left ∧ MarkedReduct S.R (fun _ => true) piece.right)
    (internal : ∀ {Δ : Context S.R} (σ : Δ ⟶ Θ) (first last : List (Piece Head Θ.arity))
      (piece : Piece Head Θ.arity), pieces = first ++ piece :: last →
      (∀ q ∈ first, (q.subst σ.substitution).Holds S.R Δ.raw) →
      TypeEq S.R Δ.raw (Presentation.subst σ.substitution piece.leftType)
        (Presentation.subst σ.substitution piece.rightType))
    (pieceEquations : EquationStore (TotalTerm Θ)) (codes : pieceEquations.map codePiece = pieces)
    (exact : ∀ {Δ : Context S.R} (σ : Δ ⟶ Θ),
      (frames S.levels).Models σ pieceEquations ↔ (frames S.levels).Solves σ equation) :
    PermutedMiller S.levels (before ++ (pieceEquations ++ after)) := by
  have empty := computation_empty rigid
  have front : PermutedMiller S.levels (equation :: (before ++ after)) := permuted.perm List.perm_middle
  have spliced := front.splice_of (pieces := pieceEquations) fun before' after' stratified => by
    obtain ⟨leftReduct, rightReduct⟩ := side_reduct rigid sn (stratified before' after' equation rfl).1
    have pieceReducts := reducts leftReduct rightReduct
    refine StratifiedMiller.splice stratified exact ?_ ?_
    · intro piece member
      have inPieces : codePiece piece ∈ pieces := by
        rw [← codes]
        exact List.mem_map_of_mem member
      obtain ⟨pieceLeft, pieceRight⟩ := pieceReducts _ inPieces
      exact sides_of_reducts empty pieceLeft pieceRight
    · intro first last piece split Δ σ solved
      rw [models_append_iff] at solved
      have pieceSplit : pieces = first.map codePiece ++ codePiece piece :: last.map codePiece := by
        rw [← codes, split]
        simp
      exact internal σ (first.map codePiece) (last.map codePiece) (codePiece piece) pieceSplit (fun q member => by
        obtain ⟨original, inFirst, rfl⟩ := List.mem_map.mp member
        exact (solves_raw σ original).mp (solved.2 original inFirst))
  exact spliced.perm (by
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.perm_append_comm.append_right after)

end Splice

section Rule

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

theorem elimsWeighed_codes (fuel : Nat) {Θ : Context S.R} {equation : Equation (TotalTerm Θ)}
    {weighed : WeighedParts facts roots heads algebra rigid complete equation}
    (found : elimsWeighed facts roots heads algebra rigid complete declared choices reducer fuel equation =
      some weighed) :
    equation.2.1.code = equation.1.1.code ∧
      elimUnder [] equation.1.1.code equation.1.2.code equation.2.2.code =
        some (weighed.val.val.map codePiece) := by
  unfold elimsWeighed at found
  split at found
  · rename_i same
    split at found
    · rename_i pieces computed
      obtain ⟨store, formed, rfl⟩ := Option.map_eq_some_iff.mp found
      refine ⟨same, computed.trans ?_⟩
      exact congrArg some (formPieces_codes facts roots heads algebra rigid complete declared choices reducer fuel
        pieces _ formed).symm
    · cases found
  · cases found

theorem flexWeighed_codes (fuel : Nat) {Θ : Context S.R} {equation : Equation (TotalTerm Θ)}
    {weighed : WeighedParts facts roots heads algebra rigid complete equation}
    (found : flexWeighed facts roots heads algebra rigid complete declared choices reducer fuel equation =
      some weighed) :
    equation.2.1.code = equation.1.1.code ∧
      elimAnyUnder [] equation.1.1.code equation.1.2.code equation.2.2.code =
        some (weighed.val.val.map codePiece) := by
  unfold flexWeighed at found
  split at found
  · rename_i same
    split at found
    · rename_i pieces computed
      obtain ⟨store, formed, rfl⟩ := Option.map_eq_some_iff.mp found
      refine ⟨same, computed.trans ?_⟩
      exact congrArg some (formPieces_codes facts roots heads algebra rigid complete declared choices reducer fuel
        pieces _ formed).symm
    · cases found
  · cases found

theorem elimsWeighed_keeps (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    WeighedKeeps facts roots heads algebra rigid complete
      (elimsWeighed facts roots heads algebra rigid complete declared choices reducer fuel equation) := by
  intro weighed found before after permuted
  obtain ⟨same, codes⟩ := elimsWeighed_codes facts roots heads algebra rigid complete declared choices reducer fuel
    found
  have empty := computation_empty rigid
  refine PermutedMiller.splice_reading rigid sn permuted
    (elimUnder_reducts empty [] _ _ _ (fun _ => true) (fun _ small => absurd small (Nat.not_lt_zero _)) codes)
    (fun {Δ} σ first last piece split held => ?_) weighed.val.val rfl fun σ => (weighed.val.property σ).symm
  have tl := equation.1.2.typed.substitute σ.typed
  have tr := equation.2.2.typed.substitute σ.typed
  rw [same] at tr
  have read := elimUnder_subst [] _ _ _ codes σ.substitution (fun _ _ _ small => absurd small (Nat.not_lt_zero _))
    (Nat.zero_le _)
  rw [List.map_nil] at read
  exact elimUnder_internal facts [] _ _ _ Δ.formed (LocalTypes.nil _) read tl tr
    (first.map (Piece.subst σ.substitution)) (last.map (Piece.subst σ.substitution)) (piece.subst σ.substitution)
    (by rw [split]; simp) (fun q member => by
      obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
      exact held original inside)

theorem flexWeighed_keeps (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    WeighedKeeps facts roots heads algebra rigid complete
      (flexWeighed facts roots heads algebra rigid complete declared choices reducer fuel equation) := by
  intro weighed found before after permuted
  obtain ⟨same, codes⟩ := flexWeighed_codes facts roots heads algebra rigid complete declared choices reducer fuel
    found
  have empty := computation_empty rigid
  refine PermutedMiller.splice_reading rigid sn permuted
    (elimAnyUnder_reducts empty [] _ _ _ (fun _ => true) (fun _ small => absurd small (Nat.not_lt_zero _)) codes)
    (fun {Δ} σ first last piece split held => ?_) weighed.val.val rfl fun σ => (weighed.val.property σ).symm
  have tl := equation.1.2.typed.substitute σ.typed
  have tr := equation.2.2.typed.substitute σ.typed
  rw [same] at tr
  exact elimAnyUnder_internal_subst facts [] _ _ _ codes σ.substitution
    (fun _ _ _ small => absurd small (Nat.not_lt_zero _)) (Nat.zero_le _) Δ.formed (LocalTypes.nil _) tl tr
    first last piece split held

theorem decomposeElims_position (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ), PositionKeeps facts roots heads algebra rigid complete
      (decomposeElims facts roots heads algebra rigid complete declared choices reducer fuel problem)
  | [] => fun _ found => by cases found
  | equation :: rest => by
      simp only [decomposeElims]
      exact decomposeStep_keeps facts roots heads algebra rigid complete equation rest
        (elimsWeighed_keeps facts roots heads algebra rigid complete declared choices reducer sn fuel equation)
        (decomposeElims_position sn fuel rest)

theorem decomposeFlex_position (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ), PositionKeeps facts roots heads algebra rigid complete
      (decomposeFlex facts roots heads algebra rigid complete declared choices reducer fuel problem)
  | [] => fun _ found => by cases found
  | equation :: rest => by
      simp only [decomposeFlex]
      exact decomposeStep_keeps facts roots heads algebra rigid complete equation rest
        (flexWeighed_keeps facts roots heads algebra rigid complete declared choices reducer sn fuel equation)
        (decomposeFlex_position sn fuel rest)

/-- **R99's decomposition of elimination spines keeps the permuted class** on a strongly normalizing package. -/
theorem decomposeElims_keeps (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) (permuted : PermutedMiller S.levels problem) :
    DecomposedKeeps (fun problem => PermutedMiller S.levels problem) facts roots heads algebra rigid complete
      (decomposeElims facts roots heads algebra rigid complete declared choices reducer fuel problem) :=
  (decomposeElims_position facts roots heads algebra rigid complete declared choices reducer sn fuel
    problem).decomposed facts roots heads algebra rigid complete permuted

/-- **The decomposition of elimination spines at a base shape keeps the permuted class** on a strongly normalizing
package. -/
theorem decomposeFlex_keeps (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) (permuted : PermutedMiller S.levels problem) :
    DecomposedKeeps (fun problem => PermutedMiller S.levels problem) facts roots heads algebra rigid complete
      (decomposeFlex facts roots heads algebra rigid complete declared choices reducer fuel problem) :=
  (decomposeFlex_position facts roots heads algebra rigid complete declared choices reducer sn fuel
    problem).decomposed facts roots heads algebra rigid complete permuted

end Rule

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
