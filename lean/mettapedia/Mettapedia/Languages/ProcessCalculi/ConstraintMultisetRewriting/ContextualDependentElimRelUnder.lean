import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentElimRelPieces

/-!
# Elimination spines of one local under abstractions, and the executable reading

**The reading under abstractions** (`ElimSpines`). Under the same abstractions, two elimination spines of one bound
local, applications and projections in any order, read along types that reduce to Π and Σ types (`ElimRel`), with no
condition on the base type; with `check`, the annotation under the abstractions is a base type as it stands. It
contains R124's reading of application spines and of one projection above them (`SpineRel.elimSpines`).

* Its pieces are typed (`ElimSpines.typed`), it is exact at every formed context whatever the annotation under the
  abstractions is (`ElimSpines.exact`), its pieces are stratified among themselves (`ElimSpines.internal`) and have
  Miller reducts (`ElimSpines.reducts`).
* It is kept by every substitution that fixes the locals, whatever the substitution makes of the base type
  (`ElimSpines.subst`).
* At a base type as it stands the sides weigh at least two more than the pieces (`ElimSpines.weight`).

**The executable reading** (`elimPartsN`, `elimsUnderN`) takes the reducer's reduct of the type read at every step.
It is a reading (`elimsUnderN_rel`), and eventually constant in the budget (`elimsUnderN_const`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaDepth

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentFragment ContextualDependentInPlace
open ContextualDependentRigidFormers ContextualDependentEtaLong ContextualDependentOccursCheck
open ContextualDependentRank ContextualDependentOccursFull ContextualDependentRigidDecomposition
open ContextualDependentSpinesMany ContextualDependentDecisiveFragment
open ContextualDependentEliminations (Read appStep fstStep sndStep appStep_some fstStep_some sndStep_some)
open ContextualDependentConstantHeadsProjections (project)

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## The reading under abstractions -/

/-- **Two elimination spines of one bound local under the same abstractions, read along types that reduce to Π and Σ
types.** With `check`, the annotation under the abstractions is a base type as it stands. -/
inductive ElimSpines (R : Rules Head) (check : Bool) : {n : Nat} → List (Tm Head n) → Tm Head n → Tm Head n →
    Tm Head n → List (Piece Head n) → Prop
  | under {n : Nat} {locals : List (Tm Head n)} {D : Tm Head n} {T l r : Tm Head (n + 1)}
      {pieces : List (Piece Head (n + 1))} :
      ElimSpines R check (Presentation.rename wk D :: locals.map (Presentation.rename wk)) T l r pieces →
      ElimSpines R check locals (.pi D T) (.lam l) (.lam r) (pieces.map (Piece.under D))
  | base {n : Nat} {locals : List (Tm Head n)} {C left right : Tm Head n} {h : Fin n} {T TL TR : Tm Head n}
      {pieces : List (Piece Head n)} :
      (check = true → anyBase C = true) → h.val < locals.length → locals[h.val]? = some T →
      ElimRel R (.var h) T left right pieces TL TR → ElimSpines R check locals C left right pieces

/-- A type below a pair type reduces to a pair type. -/
theorem reduces_sigma_of_le (facts : FormFacts S.R S.roles) {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {type first : Tm Head n} {second : Tm Head (n + 1)} (isType : IsType S.R Γ type)
    (isSigma : IsType S.R Γ (.sigma first second)) (le : TypeLe S.R Γ type (.sigma first second)) :
    ∃ AL BL, Reduces S.R type (.sigma AL BL) := by
  obtain ⟨form, red, isForm⟩ := facts.typeForm isType formed
  obtain ⟨A₀, B₀, same, _, _⟩ := Below.sigma_inv facts (TypeLe.toBelow le isSigma) formed (IsType.refl isSigma)
  obtain ⟨AL, BL, shape, _, _⟩ := (facts.forms
    (TypeEq.trans S.levels (TypeEq.symm red.typeEq) same).symm formed (.inr (.inr (.inl ⟨_, _, rfl⟩)))
      isForm).sigma_left
  subst shape
  exact ⟨AL, BL, red.red.reduces⟩

/-- **R124's reading is a case of this one**: application spines, and one projection above them. -/
theorem SpineRel.elimSpines (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
    (heads : HeadPreserving S.R) {check : Bool} {n : Nat} {locals : List (Tm Head n)}
    {annotation left right : Tm Head n} {pieces : List (Piece Head n)}
    (read : SpineRel S.R check locals annotation left right pieces) :
    ∀ {Γ : Ctx Head n}, CtxFormed S.R Γ → LocalTypes Γ locals →
      TypedEquality.Typed S.R Γ left annotation → TypedEquality.Typed S.R Γ right annotation →
      ElimSpines S.R check locals annotation left right pieces := by
  induction read with
  | @under n locals D T l r inner reading ih =>
      intro Γ formed types tl tr
      obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
      exact .under (ih (formed.snoc ⟨u, hu, tD⟩) (types.under D) (Typed.lam_inv facts tl formed)
        (Typed.lam_inv facts tr formed))
  | @base n locals C h as bs T F pieces based small _ looked read =>
      intro Γ formed types tl tr
      obtain ⟨F', spines⟩ := ElimRel.of_argRel (head := .var h) (type := T) .nil read
      exact .base based small looked (by simpa using spines)
  | @proj n locals C h first as bs T F pieces based small _ looked read =>
      intro Γ formed types tl tr
      have headType := types.head looked
      subst headType
      have th : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
      have principal : ∀ U, TypedEquality.Typed S.R Γ (.var h) U → TypeLe S.R Γ (Ctx.lookup Γ h) U :=
        fun U typed => Typed.generation typed
      obtain ⟨F', spines⟩ := ElimRel.of_argRel (head := .var h) (type := Ctx.lookup Γ h) .nil read
      simp only [List.nil_append] at spines
      obtain ⟨A, B, tp, _⟩ := ContextualDependentConstantHeadsProjections.project_generation tl
      obtain ⟨A', B', tq, _⟩ := ContextualDependentConstantHeadsProjections.project_generation tr
      obtain ⟨tpF, principalP, _⟩ := spines.typed_left facts roots heads formed th principal tp
      obtain ⟨tqF, principalQ, _⟩ := spines.swap.typed_left facts roots heads formed th principal tq
      obtain ⟨AL, BL, redL⟩ := reduces_sigma_of_le facts formed (Typed.isType tpF formed)
        (Typed.isType tp formed) (principalP _ tp)
      obtain ⟨AR, BR, redR⟩ := reduces_sigma_of_le facts formed (Typed.isType tqF formed)
        (Typed.isType tq formed) (principalQ _ tq)
      obtain ⟨FL, FR, projected⟩ := ElimRel.of_projection first spines redL redR
      exact .base based small looked projected

section Theory

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads in
/-- **The pieces are typed.** -/
theorem ElimSpines.typed {check : Bool} {n : Nat} {locals : List (Tm Head n)} {annotation left right : Tm Head n}
    {pieces : List (Piece Head n)} (read : ElimSpines S.R check locals annotation left right pieces) :
    ∀ {Γ : Ctx Head n}, CtxFormed S.R Γ → LocalTypes Γ locals →
      TypedEquality.Typed S.R Γ left annotation → TypedEquality.Typed S.R Γ right annotation →
      ∀ piece ∈ pieces, piece.Typed S.R Γ := by
  induction read with
  | @under n locals D T l r inner _ ih =>
      intro Γ formed types tl tr
      obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
      have below := ih (formed.snoc ⟨u, hu, tD⟩) (types.under D) (Typed.lam_inv facts tl formed)
        (Typed.lam_inv facts tr formed)
      intro piece member
      obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
      exact Piece.typed_under formed ⟨u, hu, tD⟩ (below original inside)
  | @base n locals C left right h T TL TR pieces _ _ looked read =>
      intro Γ formed types tl tr
      have headType := types.head looked
      subst headType
      exact read.pieces_typed facts roots heads formed (.var h) (fun U typed => Typed.generation typed) tl tr

include facts roots heads algebra rigid complete in
/-- **The reading is exact at every formed context**, whatever the annotation under the abstractions is. -/
theorem ElimSpines.exact {check : Bool} {n : Nat} {locals : List (Tm Head n)} {annotation left right : Tm Head n}
    {pieces : List (Piece Head n)} (read : ElimSpines S.R check locals annotation left right pieces) :
    ∀ {Γ : Ctx Head n}, CtxFormed S.R Γ → LocalTypes Γ locals →
      TypedEquality.Typed S.R Γ left annotation → TypedEquality.Typed S.R Γ right annotation →
      (Equal S.R Γ left right annotation ↔ ∀ piece ∈ pieces, piece.Holds S.R Γ) := by
  induction read with
  | @under n locals D T l r inner reading ih =>
      intro Γ formed types tl tr
      obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
      have isD : IsType S.R Γ D := ⟨u, hu, tD⟩
      have formedD := formed.snoc isD
      have tl' := Typed.lam_inv facts tl formed
      have tr' := Typed.lam_inv facts tr formed
      have below := ih formedD (types.under D) tl' tr'
      have typed := reading.typed facts roots heads formedD (types.under D) tl' tr'
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
  | @base n locals C left right h T TL TR pieces _ _ looked read =>
      intro Γ formed types tl tr
      have headType := types.head looked
      subst headType
      exact read.exact facts roots heads algebra rigid complete formed tl tr

include facts roots heads algebra rigid complete in
/-- **The sides weigh more than the pieces**, when the annotation under the abstractions is a base type as it
stands. -/
theorem ElimSpines.weight {n : Nat} {locals : List (Tm Head n)} {annotation left right : Tm Head n}
    {pieces : List (Piece Head n)} (read : ElimSpines S.R true locals annotation left right pieces) :
    ∀ {Γ : Ctx Head n}, CtxFormed S.R Γ → LocalTypes Γ locals →
      TypedEquality.Typed S.R Γ left annotation → TypedEquality.Typed S.R Γ right annotation →
      ∃ w wl wr, PiecesWeigh S Γ pieces w ∧ HasWeight S Γ left annotation wl ∧
        HasWeight S Γ right annotation wr ∧ w + 2 ≤ wl + wr := by
  induction read with
  | @under n locals D T l r inner reading ih =>
      intro Γ formed types tl tr
      obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
      have isD : IsType S.R Γ D := ⟨u, hu, tD⟩
      have formedD := formed.snoc isD
      have tl' := Typed.lam_inv facts tl formed
      have tr' := Typed.lam_inv facts tr formed
      obtain ⟨w, wl, wr, weighs, left, right, total⟩ := ih formedD (types.under D) tl' tr'
      have typed := reading.typed facts roots heads formedD (types.under D) tl' tr'
      obtain ⟨v, hv, tPi⟩ := Typed.isType tl formed
      exact ⟨w, wl, wr, PiecesWeigh.under formed isD typed weighs, HasWeight.under (w := v) hv tPi isD left,
        HasWeight.under (w := v) hv tPi isD right, total⟩
  | @base n locals C left right h T TL TR pieces based _ looked read =>
      intro Γ formed types tl tr
      have headType := types.head looked
      subst headType
      exact read.weight facts roots heads algebra rigid complete formed (anyBase_spec rigid (based rfl)) tl tr

include facts roots heads in
/-- **The pieces are stratified among themselves.** -/
theorem ElimSpines.internal {check : Bool} {n : Nat} {locals : List (Tm Head n)}
    {annotation left right : Tm Head n} {pieces : List (Piece Head n)}
    (read : ElimSpines S.R check locals annotation left right pieces) :
    ∀ {Γ : Ctx Head n}, CtxFormed S.R Γ → LocalTypes Γ locals →
      TypedEquality.Typed S.R Γ left annotation → TypedEquality.Typed S.R Γ right annotation →
      ∀ (first last : List (Piece Head n)) (piece : Piece Head n), pieces = first ++ piece :: last →
        (∀ q ∈ first, q.Holds S.R Γ) → TypeEq S.R Γ piece.leftType piece.rightType := by
  induction read with
  | @under n locals D T l r inner reading ih =>
      intro Γ formed types tl tr first last piece split held
      obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
      have isD : IsType S.R Γ D := ⟨u, hu, tD⟩
      have formedD := formed.snoc isD
      have tl' := Typed.lam_inv facts tl formed
      have tr' := Typed.lam_inv facts tr formed
      have typed := reading.typed facts roots heads formedD (types.under D) tl' tr'
      obtain ⟨first', rest', innerSplit, rfl, mapped⟩ := List.map_eq_append_iff.mp split
      obtain ⟨piece', last', rfl, rfl, rfl⟩ := List.map_eq_cons_iff.mp mapped
      have held' : ∀ q ∈ first', q.Holds S.R (.snoc Γ D) := fun q member =>
        (Piece.holds_under facts formed isD (typed q (by rw [innerSplit]; exact List.mem_append_left _ member))).mp
          (held (q.under D) (List.mem_map.mpr ⟨q, member, rfl⟩))
      have below := ih formedD (types.under D) tl' tr' first' last' piece' innerSplit held'
      exact (ContextualDependentRigid.typeEq_pi_iff facts formed).mpr ⟨isD.refl, below⟩
  | @base n locals C left right h T TL TR pieces _ _ looked read =>
      intro Γ formed types tl tr
      have headType := types.head looked
      subst headType
      have th : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
      have principal : ∀ U, TypedEquality.Typed S.R Γ (.var h) U → TypeLe S.R Γ (Ctx.lookup Γ h) U :=
        fun U typed => Typed.generation typed
      obtain ⟨tlL, _, _⟩ := read.typed_left facts roots heads formed th principal tl
      obtain ⟨trR, _, _⟩ := read.swap.typed_left facts roots heads formed th principal tr
      exact (read.internal facts roots heads formed tlL trR
        (read.pieces_typed facts roots heads formed th principal tl tr)).1

end Theory

/-- **The reading is kept by substitutions that fix the locals**; the base type may become anything. -/
theorem ElimSpines.subst {R : Rules Head} {check : Bool} {n : Nat} {locals : List (Tm Head n)}
    {annotation left right : Tm Head n} {pieces : List (Piece Head n)}
    (read : ElimSpines R check locals annotation left right pieces) :
    ∀ {m : Nat} (σ : Sub Head n m), Fixes σ locals.length → locals.length ≤ m →
      ElimSpines R false (locals.map (Presentation.subst σ)) (Presentation.subst σ annotation)
        (Presentation.subst σ left) (Presentation.subst σ right) (pieces.map (Piece.subst σ)) := by
  induction read with
  | @under n locals D T l r inner reading ih =>
      intro m σ fixes bound
      have below := ih (liftSub σ) (by simpa using fixes.lift) (by simp; omega)
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
      have mapped : (inner.map (Piece.under D)).map (Piece.subst σ) =
          (inner.map (Piece.subst (liftSub σ))).map (Piece.under (Presentation.subst σ D)) := by
        simp only [List.map_map]
        rfl
      rw [mapped]
      exact .under below
  | @base n locals C left right h T TL TR pieces _ small looked read =>
      intro m σ fixes bound
      have hm : h.val < m := by omega
      have fixedHead : σ h = .var ⟨h.val, hm⟩ := fixes h.val h.isLt hm small
      have moved := read.subst σ
      simp only [Presentation.subst, fixedHead] at moved
      refine .base (h := ⟨h.val, hm⟩) (T := Presentation.subst σ T) (fun impossible => by cases impossible) ?_ ?_
        moved
      · simpa using small
      · simp only [List.getElem?_map, looked, Option.map_some]

/-- **The pieces have Miller normal reducts** when the two sides do, the locals rigid. -/
theorem ElimSpines.reducts (empty : S.R.computation = RootComputation.empty) {check : Bool} {n : Nat}
    {locals : List (Tm Head n)} {annotation left right : Tm Head n} {pieces : List (Piece Head n)}
    (read : ElimSpines S.R check locals annotation left right pieces) :
    ∀ (mark : Fin n → Bool), (∀ j : Fin n, j.val < locals.length → mark j = false) →
      ContextualDependentCumulativeClosure.MarkedReduct S.R mark left →
      ContextualDependentCumulativeClosure.MarkedReduct S.R mark right →
      ∀ piece ∈ pieces, ContextualDependentCumulativeClosure.MarkedReduct S.R mark piece.left ∧
        ContextualDependentCumulativeClosure.MarkedReduct S.R mark piece.right := by
  induction read with
  | @under n locals D T l r inner reading ih =>
      intro mark localsRigid leftReduct rightReduct
      have lifted : ∀ j : Fin (n + 1),
          j.val < (Presentation.rename wk D :: locals.map (Presentation.rename wk)).length →
            ContextualDependentGeneralPattern.liftFlexible mark j = false := by
        intro j
        refine Fin.cases (motive := fun j : Fin (n + 1) =>
          j.val < (Presentation.rename wk D :: locals.map (Presentation.rename wk)).length →
            ContextualDependentGeneralPattern.liftFlexible mark j = false) ?_ (fun j small => ?_) j
        · intro _
          rfl
        · change mark j = false
          simp only [List.length_cons, List.length_map, Fin.val_succ] at small
          exact localsRigid j (by omega)
      intro piece member
      obtain ⟨original, inInner, rfl⟩ := List.mem_map.mp member
      obtain ⟨pl, pr⟩ := ih (ContextualDependentGeneralPattern.liftFlexible mark) lifted
        (ContextualDependentCumulativeClosure.MarkedReduct.of_lam empty leftReduct)
        (ContextualDependentCumulativeClosure.MarkedReduct.of_lam empty rightReduct) original inInner
      exact ⟨ContextualDependentCumulativeClosure.MarkedReduct.lam empty pl,
        ContextualDependentCumulativeClosure.MarkedReduct.lam empty pr⟩
  | @base n locals C left right h T TL TR pieces _ small _ read =>
      intro mark localsRigid leftReduct rightReduct
      exact read.reducts empty (localsRigid h small) leftReduct rightReduct

/-! ## The executable reading -/

section Executable

variable (reducer : ExecutableReduction.Reducer S.R)

/-- The reducer's reducts of the two types of a read. -/
def normalRead (fuel : Nat) {n : Nat} (read : Option (Read Head n)) : Option (Read Head n) :=
  read.map fun found => (found.1, normalCode reducer fuel found.2.1, normalCode reducer fuel found.2.2)

/-- **The argument pieces of two elimination spines of one local, along the reducer's reducts of the types read**:
the types returned are reducts. -/
def elimPartsN (fuel : Nat) {n : Nat} (locals : List (Tm Head n)) : Tm Head n → Tm Head n → Option (Read Head n)
  | .var h, .var h' =>
      if h = h' then (locals[h.val]?).map fun T => ([], normalCode reducer fuel T, normalCode reducer fuel T)
      else none
  | .app f a, .app g b => normalRead reducer fuel (appStep a b (elimPartsN fuel locals f g))
  | .fst p, .fst q => normalRead reducer fuel (fstStep (elimPartsN fuel locals p q))
  | .snd p, .snd q => normalRead reducer fuel (sndStep p q (elimPartsN fuel locals p q))
  | _, _ => none

/-- **The executable reading reads elimination spines of one local**, and the types it returns are reducts of the
types read. -/
theorem elimPartsN_rel (fuel : Nat) {n : Nat} (locals : List (Tm Head n)) :
    ∀ (left right : Tm Head n) {read : Read Head n}, elimPartsN reducer fuel locals left right = some read →
      ∃ (h : Fin n) (T TL TR : Tm Head n), h.val < locals.length ∧ locals[h.val]? = some T ∧
        ElimRel S.R (.var h) T left right read.1 TL TR ∧ Reduces S.R TL read.2.1 ∧ Reduces S.R TR read.2.2
  | .var h, right, read, found => by
      cases right
      all_goals first | cases found | skip
      rename_i h'
      simp only [elimPartsN] at found
      split at found
      · rename_i same
        subst same
        obtain ⟨T, looked, rfl⟩ := Option.map_eq_some_iff.mp found
        exact ⟨h, T, T, T, (List.getElem?_eq_some_iff.mp looked).1, looked, .nil,
          normalCode_reduces reducer fuel T, normalCode_reduces reducer fuel T⟩
      · cases found
  | .app f a, right, read, found => by
      cases right
      all_goals first | cases found | skip
      rename_i g b
      simp only [elimPartsN, normalRead, Option.map_eq_some_iff] at found
      obtain ⟨stepped, computed, rfl⟩ := found
      obtain ⟨prefixPieces, DL, EL, DR, ER, prefixRead, result⟩ := appStep_some computed
      subst result
      obtain ⟨h, T, TL, TR, small, looked, rel, redL, redR⟩ := elimPartsN_rel fuel locals f g prefixRead
      exact ⟨h, T, _, _, small, looked, .app rel redL redR, normalCode_reduces reducer fuel _,
        normalCode_reduces reducer fuel _⟩
  | .fst p, right, read, found => by
      cases right
      all_goals first | cases found | skip
      rename_i q
      simp only [elimPartsN, normalRead, Option.map_eq_some_iff] at found
      obtain ⟨stepped, computed, rfl⟩ := found
      obtain ⟨prefixPieces, AL, BL, AR, BR, prefixRead, result⟩ := fstStep_some computed
      subst result
      obtain ⟨h, T, TL, TR, small, looked, rel, redL, redR⟩ := elimPartsN_rel fuel locals p q prefixRead
      exact ⟨h, T, _, _, small, looked, .fst rel redL redR, normalCode_reduces reducer fuel _,
        normalCode_reduces reducer fuel _⟩
  | .snd p, right, read, found => by
      cases right
      all_goals first | cases found | skip
      rename_i q
      simp only [elimPartsN, normalRead, Option.map_eq_some_iff] at found
      obtain ⟨stepped, computed, rfl⟩ := found
      obtain ⟨prefixPieces, AL, BL, AR, BR, prefixRead, result⟩ := sndStep_some computed
      subst result
      obtain ⟨h, T, TL, TR, small, looked, rel, redL, redR⟩ := elimPartsN_rel fuel locals p q prefixRead
      exact ⟨h, T, _, _, small, looked, .snd rel redL redR, normalCode_reduces reducer fuel _,
        normalCode_reduces reducer fuel _⟩
  | .const _, _, _, found => by cases found
  | .head _, _, _, found => by cases found
  | .pi _ _, _, _, found => by cases found
  | .sigma _ _, _, _, found => by cases found
  | .id _ _ _, _, _, found => by cases found
  | .lam _, _, _, found => by cases found
  | .pair _ _, _, _, found => by cases found
  | .refl _, _, _, found => by cases found

/-- **Elimination spines of one local at a base type as it stands**, along the reducer's reducts. -/
def elimBaseN (fuel : Nat) {n : Nat} (locals : List (Tm Head n)) (C left right : Tm Head n) :
    Option (List (Piece Head n)) :=
  if anyBase C then (elimPartsN reducer fuel locals left right).map fun read => read.1 else none

/-- **Elimination spines of one local under abstractions, along the reducer's reducts of the types read**, at a base
type as it stands. -/
def elimsUnderN (fuel : Nat) : {n : Nat} → List (Tm Head n) → Tm Head n → Tm Head n → Tm Head n →
    Option (List (Piece Head n))
  | _, locals, .pi D T, .lam left, .lam right =>
      (elimsUnderN fuel (Presentation.rename wk D :: locals.map (Presentation.rename wk)) T left right).map
        (List.map (Piece.under D))
  | _, locals, C, left, right => elimBaseN reducer fuel locals C left right

theorem elimsUnderN_base (fuel : Nat) {n : Nat} {locals : List (Tm Head n)} {annotation left right : Tm Head n}
    (notUnder : ¬ ∃ D T l r, annotation = .pi D T ∧ left = .lam l ∧ right = .lam r) :
    elimsUnderN reducer fuel locals annotation left right =
      elimBaseN reducer fuel locals annotation left right := by
  cases annotation with
  | pi D T =>
      cases left with
      | lam l =>
          cases right with
          | lam r => exact absurd ⟨D, T, l, r, rfl, rfl, rfl⟩ notUnder
          | _ => rfl
      | _ => rfl
  | _ => rfl

/-- **The executable reading is a checked reading.** -/
theorem elimsUnderN_rel (fuel : Nat) {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n)
    {pieces : List (Piece Head n)} (found : elimsUnderN reducer fuel locals annotation left right = some pieces) :
    ElimSpines S.R true locals annotation left right pieces := by
  by_cases view : ∃ D T l r, annotation = .pi D T ∧ left = .lam l ∧ right = .lam r
  · obtain ⟨D, T, l, r, rfl, rfl, rfl⟩ := view
    simp only [elimsUnderN, Option.map_eq_some_iff] at found
    obtain ⟨inner, computed, rfl⟩ := found
    exact .under (elimsUnderN_rel fuel _ T l r computed)
  · rw [elimsUnderN_base reducer fuel view] at found
    unfold elimBaseN at found
    split at found
    · rename_i based
      obtain ⟨read, computed, rfl⟩ := Option.map_eq_some_iff.mp found
      obtain ⟨h, T, TL, TR, small, looked, rel, _, _⟩ := elimPartsN_rel reducer fuel locals left right computed
      exact .base (fun _ => based) small looked rel
    · cases found
termination_by sizeOf annotation

/-! ### Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  ContextualDependentConversionBudget.Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
theorem normalRead_const {n : Nat} (read : Option (Read Head n)) :
    EventuallyConst fun fuel => normalRead reducer fuel read := by
  cases read with
  | none => exact EventuallyConst.const _
  | some found =>
      exact EventuallyConst.comp (fun types : Tm Head n × Tm Head n => some (found.1, types.1, types.2))
        (EventuallyConst.pair (normalCode_const reducer stable found.2.1) (normalCode_const reducer stable found.2.2))

include stable in
theorem elimPartsN_const {n : Nat} (locals : List (Tm Head n)) :
    ∀ (left right : Tm Head n), EventuallyConst fun fuel => elimPartsN reducer fuel locals left right
  | .var h, .var h' => by
      by_cases same : h = h'
      · subst same
        cases looked : locals[h.val]? with
        | none =>
            exact EventuallyConst.of_eq (fun fuel => by simp [elimPartsN, looked])
              (EventuallyConst.const (none : Option (Read Head n)))
        | some T =>
            refine EventuallyConst.of_eq (g := fun fuel => some (([] : List (Piece Head n)),
              (normalCode reducer fuel T, normalCode reducer fuel T).1,
              (normalCode reducer fuel T, normalCode reducer fuel T).2))
              (fun fuel => by simp [elimPartsN, looked]) ?_
            exact EventuallyConst.comp (fun types : Tm Head n × Tm Head n =>
              some (([] : List (Piece Head n)), types.1, types.2))
              (EventuallyConst.pair (normalCode_const reducer stable T) (normalCode_const reducer stable T))
      · exact EventuallyConst.of_eq (fun fuel => by simp [elimPartsN, same])
          (EventuallyConst.const (none : Option (Read Head n)))
  | .app f a, .app g b =>
      EventuallyConst.dep (h := fun fuel => elimPartsN reducer fuel locals f g)
        (k := fun fuel read => normalRead reducer fuel (appStep a b read)) (elimPartsN_const locals f g)
        (fun read => normalRead_const reducer stable (appStep a b read))
  | .fst p, .fst q =>
      EventuallyConst.dep (h := fun fuel => elimPartsN reducer fuel locals p q)
        (k := fun fuel read => normalRead reducer fuel (fstStep read)) (elimPartsN_const locals p q)
        (fun read => normalRead_const reducer stable (fstStep read))
  | .snd p, .snd q =>
      EventuallyConst.dep (h := fun fuel => elimPartsN reducer fuel locals p q)
        (k := fun fuel read => normalRead reducer fuel (sndStep p q read)) (elimPartsN_const locals p q)
        (fun read => normalRead_const reducer stable (sndStep p q read))
  | .var _, .const _ | .var _, .head _ | .var _, .pi _ _ | .var _, .sigma _ _ | .var _, .id _ _ _
  | .var _, .lam _ | .var _, .app _ _ | .var _, .pair _ _ | .var _, .fst _ | .var _, .snd _ | .var _, .refl _
  | .app _ _, .var _ | .app _ _, .const _ | .app _ _, .head _ | .app _ _, .pi _ _ | .app _ _, .sigma _ _
  | .app _ _, .id _ _ _ | .app _ _, .lam _ | .app _ _, .pair _ _ | .app _ _, .fst _ | .app _ _, .snd _
  | .app _ _, .refl _
  | .fst _, .var _ | .fst _, .const _ | .fst _, .head _ | .fst _, .pi _ _ | .fst _, .sigma _ _
  | .fst _, .id _ _ _ | .fst _, .lam _ | .fst _, .app _ _ | .fst _, .pair _ _ | .fst _, .snd _ | .fst _, .refl _
  | .snd _, .var _ | .snd _, .const _ | .snd _, .head _ | .snd _, .pi _ _ | .snd _, .sigma _ _
  | .snd _, .id _ _ _ | .snd _, .lam _ | .snd _, .app _ _ | .snd _, .pair _ _ | .snd _, .fst _ | .snd _, .refl _
  | .const _, _ | .head _, _ | .pi _ _, _ | .sigma _ _, _ | .id _ _ _, _ | .lam _, _ | .pair _ _, _
  | .refl _, _ => EventuallyConst.const (none : Option (Read Head n))

include stable in
/-- **The executable reading is eventually constant in the budget.** -/
theorem elimsUnderN_const {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n) :
    EventuallyConst fun fuel => elimsUnderN reducer fuel locals annotation left right := by
  by_cases view : ∃ D T l r, annotation = .pi D T ∧ left = .lam l ∧ right = .lam r
  · obtain ⟨D, T, l, r, rfl, rfl, rfl⟩ := view
    exact EventuallyConst.comp (Option.map (List.map (Piece.under D))) (elimsUnderN_const _ T l r)
  · refine EventuallyConst.of_eq (fun fuel => elimsUnderN_base reducer fuel view) ?_
    unfold elimBaseN
    by_cases based : anyBase annotation = true
    · simp only [based, if_true]
      exact EventuallyConst.comp (Option.map fun read : Read Head n => read.1)
        (elimPartsN_const reducer stable locals left right)
    · simp only [based]
      exact EventuallyConst.const _
termination_by sizeOf annotation

omit stable in
/-- The executable reading of one equation's sides, with its checked reading. -/
def readElims (fuel : Nat) {n : Nat} (annotation left right : Tm Head n) :
    Option {pieces : List (Piece Head n) // ElimSpines S.R true [] annotation left right pieces} :=
  match found : elimsUnderN reducer fuel [] annotation left right with
  | some pieces => some ⟨pieces, elimsUnderN_rel reducer fuel [] annotation left right found⟩
  | none => none

omit stable in
theorem readElims_val (fuel : Nat) {n : Nat} (annotation left right : Tm Head n) :
    (readElims reducer fuel annotation left right).map Subtype.val =
      elimsUnderN reducer fuel [] annotation left right := by
  unfold readElims
  split
  · rename_i pieces found
    exact found.symm
  · rename_i found
    exact found.symm

include stable in
theorem readElims_const {n : Nat} (annotation left right : Tm Head n) :
    EventuallyConst fun fuel => readElims reducer fuel annotation left right :=
  EventuallyConst.of_injective (g := Option.map Subtype.val) (Option.map_injective Subtype.val_injective)
    (EventuallyConst.of_eq (fun fuel => readElims_val reducer fuel annotation left right)
      (elimsUnderN_const reducer stable [] annotation left right))

end Executable

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
