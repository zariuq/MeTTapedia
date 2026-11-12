import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCensusReadsSpines
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSpineEta

/-!
# Spines of one local decompose at every type

The readings between two spines of one local test the base type: a universe, an identity type or a bound local
(`rigidBase`). A base type that is an application is refused, and the Σ family is stuck on such stores
(`ContextualDependentEtaDepth.BaseControls`). The test is not needed for the solutions.

* **Exactness at every type** (`argRel_exact_any`). The algorithmic comparison of two neutral terms, at whatever
  type, descends to their comparison as spines after an injective renaming (R110's `descends`); the argument pieces,
  read along types that reduce to Π types, hold there and are reflected back. So two typed spines of one variable are
  equal at a type exactly when their argument pieces hold: the type need not be a base type. The same holds for equal
  projections of two spines (`projRel_exact_any`).
* **The reading** (`SpineRel`): under the same abstractions, two spines of one bound local, or equal projections of
  two such spines, their argument pieces read along types that reduce to Π types, with no condition on the base type.
  It contains R121's reading at a rigid base (`LocalSpines.anySpines`). It is kept by every substitution that fixes
  the locals (`SpineRel.subst`), it is exact at every formed context (`SpineRel.exact`), its pieces are typed
  (`SpineRel.typed`), stratified among themselves (`SpineRel.internal`) and have Miller reducts (`SpineRel.reducts`).
* **The weight** is taken on the store as it is: when the annotation under the abstractions is now a base type, a
  universe, an identity type or a neutral type (`anyBase`), the sides weigh more than the pieces (`SpineRel.weight`).
  What a solution later makes of the base type does not matter for exactness.
* **The executable reading** (`spinesUnderN`) takes the reducer's reduct of every instantiated type; it is a reading
  (`spinesUnderN_rel`), eventually constant in the budget (`spinesUnderN_const`), and complete on the tower: at a
  normal annotation, typed sides of the shape (`AnySpines`) are read from some budget on
  (`tower_spinesUnderN_reads`).
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
open ContextualDependentConstantHeads (skeleton skeleton_neutral)
open ContextualDependentSpineEta (descends piece_reflects renamePiece)
open ContextualDependentConstantHeadsProjections (project readProjection readProjection_spec readProjection_project
  subst_project project_generation project_congr project_neutral spines_project_inv)

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## The argument pieces under a renaming -/

/-- **The reading is kept by every renaming.** -/
theorem ArgRel.rename {R : Rules Head} {n m : Nat} (ρ : Ren n m) {TL TR F : Tm Head n} {as bs : List (Tm Head n)}
    {pieces : List (Piece Head n)} (read : ArgRel R TL TR as bs pieces F) :
    ArgRel R (Presentation.rename ρ TL) (Presentation.rename ρ TR) (as.map (Presentation.rename ρ))
      (bs.map (Presentation.rename ρ)) (pieces.map (renamePiece ρ)) (Presentation.rename ρ F) := by
  induction read generalizing m with
  | nil TL TR => exact .nil _ _
  | cons left right _ ih =>
      have inner := ih ρ
      rw [rename_inst0, rename_inst0] at inner
      exact .cons (Reduces.rename' left ρ) (Reduces.rename' right ρ) inner

/-! ## Exactness at every type -/

section Exactness

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **Spines of one variable decompose exactly at every type**, along types that reduce to Π types: two typed spines
are equal at a type exactly when their argument pieces hold. The type need not be a base type. -/
theorem argRel_exact_any {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (h : Fin n)
    {as bs : List (Tm Head n)} {T C F : Tm Head n} {pieces : List (Piece Head n)} (headType : Ctx.lookup Γ h = T)
    (read : ArgRel S.R T T as bs pieces F)
    (tl : TypedEquality.Typed S.R Γ (appSpine (.var h) as) C) (tr : TypedEquality.Typed S.R Γ (appSpine (.var h) bs) C) :
    Equal S.R Γ (appSpine (.var h) as) (appSpine (.var h) bs) C ↔ ∀ piece ∈ pieces, piece.Holds S.R Γ := by
  have principal : ∀ U, TypedEquality.Typed S.R Γ (.var h) U → TypeLe S.R Γ T U := by
    intro U typed
    have le : TypeLe S.R Γ (Ctx.lookup Γ h) U := Typed.generation typed
    rwa [headType] at le
  have th : TypedEquality.Typed S.R Γ (.var h) T := by
    have typed : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
    rwa [headType] at typed
  obtain ⟨typed, final⟩ := read.typed facts roots heads formed principal th principal th tl tr
  obtain ⟨sameL, sameR⟩ := read.sides
  have length : as.length = bs.length := by rw [← sameL, ← sameR, List.length_map, List.length_map]
  have isT := Typed.isType th formed
  constructor
  · intro same
    obtain ⟨m, Δ, ρ, formedΔ, compatible, injective, U, spines⟩ :=
      descends (complete formed same) formed (neutral_appSpine h as) (neutral_appSpine h bs)
    rw [rename_appSpine, rename_appSpine] at spines
    have args := spines_inv (S := S) (ρ h) (as.map (Presentation.rename ρ)) (bs.map (Presentation.rename ρ))
      (by rw [List.length_map, List.length_map]; exact length) spines
    rw [compatible h, headType] at args
    obtain ⟨u, hu, tT⟩ := isT
    have isT' : IsType S.R Δ (Presentation.rename ρ T) := ⟨u, hu, tT.rename compatible⟩
    have holds := (read.rename ρ).holds facts roots heads algebra formedΔ args isT'.refl isT'.refl isT' isT'
      (fun piece member => by
        obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
        exact ⟨(typed original inside).1.rename compatible, (typed original inside).2.rename compatible⟩)
    intro piece member
    exact piece_reflects facts roots heads algebra rigid complete compatible injective formed formedΔ
      (typed piece member) (holds _ (List.mem_map.mpr ⟨piece, member, rfl⟩))
  · intro held
    exact .subEq (read.congr facts roots heads formed isT typed held (.refl th))
      (TypeLe.toBelow final (Typed.isType tl formed))

omit [UniverseLevel.LevelOrder L] in
theorem rename_project {n m : Nat} (ρ : Ren n m) (first : Bool) (p : Tm Head n) :
    Presentation.rename ρ (project first p) = project first (Presentation.rename ρ p) := by
  cases first <;> rfl

include facts roots heads algebra rigid complete in
/-- **Equal projections of two spines of one variable decompose exactly at every type**, along types that reduce to
Π types. -/
theorem projRel_exact_any {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (h : Fin n) (first : Bool)
    {as bs : List (Tm Head n)} {T C F : Tm Head n} {pieces : List (Piece Head n)} (headType : Ctx.lookup Γ h = T)
    (read : ArgRel S.R T T as bs pieces F)
    (tl : TypedEquality.Typed S.R Γ (project first (appSpine (.var h) as)) C)
    (tr : TypedEquality.Typed S.R Γ (project first (appSpine (.var h) bs)) C) :
    Equal S.R Γ (project first (appSpine (.var h) as)) (project first (appSpine (.var h) bs)) C ↔
      ∀ piece ∈ pieces, piece.Holds S.R Γ := by
  have principal : ∀ U, TypedEquality.Typed S.R Γ (.var h) U → TypeLe S.R Γ T U := by
    intro U typed
    have le : TypeLe S.R Γ (Ctx.lookup Γ h) U := Typed.generation typed
    rwa [headType] at le
  have th : TypedEquality.Typed S.R Γ (.var h) T := by
    have typed : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
    rwa [headType] at typed
  obtain ⟨A, B, tp, le⟩ := project_generation tl
  obtain ⟨A', B', tq, _⟩ := project_generation tr
  obtain ⟨left, final⟩ := read.typed_left facts roots heads formed principal th tp
  obtain ⟨F', swapped⟩ := read.swap
  obtain ⟨right, _⟩ := swapped.typed_left facts roots heads formed principal th tq
  have typed : ∀ piece ∈ pieces, piece.Typed S.R Γ := fun piece member =>
    ⟨left piece member, right _ (List.mem_map.mpr ⟨piece, member, rfl⟩)⟩
  obtain ⟨sameL, sameR⟩ := read.sides
  have length : as.length = bs.length := by rw [← sameL, ← sameR, List.length_map, List.length_map]
  have isT := Typed.isType th formed
  constructor
  · intro same
    obtain ⟨m, Δ, ρ, formedΔ, compatible, injective, U, spines⟩ :=
      descends (complete formed same) formed (project_neutral first (neutral_appSpine h as))
        (project_neutral first (neutral_appSpine h bs))
    rw [rename_project, rename_project] at spines
    obtain ⟨U', prefixSpines⟩ := spines_project_inv first spines
    rw [rename_appSpine, rename_appSpine] at prefixSpines
    have args := spines_inv (S := S) (ρ h) (as.map (Presentation.rename ρ)) (bs.map (Presentation.rename ρ))
      (by rw [List.length_map, List.length_map]; exact length) prefixSpines
    rw [compatible h, headType] at args
    obtain ⟨u, hu, tT⟩ := isT
    have isT' : IsType S.R Δ (Presentation.rename ρ T) := ⟨u, hu, tT.rename compatible⟩
    have holds := (read.rename ρ).holds facts roots heads algebra formedΔ args isT'.refl isT'.refl isT' isT'
      (fun piece member => by
        obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
        exact ⟨(typed original inside).1.rename compatible, (typed original inside).2.rename compatible⟩)
    intro piece member
    exact piece_reflects facts roots heads algebra rigid complete compatible injective formed formedΔ
      (typed piece member) (holds _ (List.mem_map.mpr ⟨piece, member, rfl⟩))
  · intro held
    have congr := read.congr facts roots heads formed isT typed held (.refl th)
    have atSigma : Equal S.R Γ (appSpine (.var h) as) (appSpine (.var h) bs) (.sigma A B) :=
      .subEq congr (TypeLe.toBelow final (Typed.isType tp formed))
    exact project_congr atSigma le (Typed.isType tl formed)

end Exactness

/-! ## The reading, with no condition on the base type -/

/-- The types at which a neutral term is its own η-long form: a universe, an identity type, a variable, or a neutral
type. -/
def anyBase {n : Nat} (C : Tm Head n) : Bool :=
  ContextualDependentSpineEta.baseShape C || (skeleton C).isSome

theorem anyBase_spec (rigid : ∀ name, S.roles name = .rigid) {n : Nat} {C : Tm Head n} (base : anyBase C = true) :
    BaseType S C := by
  rcases Bool.or_eq_true_iff.mp base with shape | neutral
  · exact ContextualDependentSpineEta.baseShape_spec shape
  · obtain ⟨s, found⟩ := Option.isSome_iff_exists.mp neutral
    exact .inr (.inr (skeleton_neutral rigid found))

theorem anyBase_not_pi {n : Nat} {C : Tm Head n} (base : anyBase C = true) : ∀ D T, C ≠ .pi D T := by
  intro D T same
  subst same
  exact Bool.false_ne_true base

/-- **Two spines of one bound local under the same abstractions, read along types that reduce to Π types.** With
`check`, the annotation under the abstractions is a base type as it stands. -/
inductive SpineRel (R : Rules Head) (check : Bool) : {n : Nat} → List (Tm Head n) → Tm Head n → Tm Head n →
    Tm Head n → List (Piece Head n) → Prop
  | under {n : Nat} {locals : List (Tm Head n)} {D : Tm Head n} {T l r : Tm Head (n + 1)}
      {pieces : List (Piece Head (n + 1))} :
      SpineRel R check (Presentation.rename wk D :: locals.map (Presentation.rename wk)) T l r pieces →
      SpineRel R check locals (.pi D T) (.lam l) (.lam r) (pieces.map (Piece.under D))
  | base {n : Nat} {locals : List (Tm Head n)} {C : Tm Head n} {h : Fin n} {as bs : List (Tm Head n)}
      {T F : Tm Head n} {pieces : List (Piece Head n)} :
      (check = true → anyBase C = true) → h.val < locals.length → as ≠ [] → locals[h.val]? = some T →
      ArgRel R T T as bs pieces F →
      SpineRel R check locals C (appSpine (.var h) as) (appSpine (.var h) bs) pieces
  | proj {n : Nat} {locals : List (Tm Head n)} {C : Tm Head n} {h : Fin n} {first : Bool}
      {as bs : List (Tm Head n)} {T F : Tm Head n} {pieces : List (Piece Head n)} :
      (check = true → anyBase C = true) → h.val < locals.length → as ≠ [] → locals[h.val]? = some T →
      ArgRel R T T as bs pieces F →
      SpineRel R check locals C (project first (appSpine (.var h) as)) (project first (appSpine (.var h) bs))
        pieces

section Theory

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads in
/-- **The pieces are typed.** -/
theorem SpineRel.typed {check : Bool} {n : Nat} {locals : List (Tm Head n)} {annotation left right : Tm Head n}
    {pieces : List (Piece Head n)} (read : SpineRel S.R check locals annotation left right pieces) :
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
  | @base n locals C h as bs T F pieces _ _ _ looked read =>
      intro Γ formed types tl tr
      have headType := types.head looked
      have principal : ∀ U, TypedEquality.Typed S.R Γ (.var h) U → TypeLe S.R Γ T U := by
        intro U typed
        have le : TypeLe S.R Γ (Ctx.lookup Γ h) U := Typed.generation typed
        rwa [headType] at le
      have th : TypedEquality.Typed S.R Γ (.var h) T := by
        have typed : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
        rwa [headType] at typed
      exact (read.typed facts roots heads formed principal th principal th tl tr).1
  | @proj n locals C h first as bs T F pieces _ _ _ looked read =>
      intro Γ formed types tl tr
      exact projRel_typed facts roots heads formed h first (types.head looked) read tl tr

include facts roots heads algebra rigid complete in
/-- **The reading is exact at every formed context**, whatever the annotation under the abstractions is. -/
theorem SpineRel.exact {check : Bool} {n : Nat} {locals : List (Tm Head n)} {annotation left right : Tm Head n}
    {pieces : List (Piece Head n)} (read : SpineRel S.R check locals annotation left right pieces) :
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
  | @base n locals C h as bs T F pieces _ _ _ looked read =>
      intro Γ formed types tl tr
      exact argRel_exact_any facts roots heads algebra rigid complete formed h (types.head looked) read tl tr
  | @proj n locals C h first as bs T F pieces _ _ _ looked read =>
      intro Γ formed types tl tr
      exact projRel_exact_any facts roots heads algebra rigid complete formed h first (types.head looked) read tl tr

include facts roots heads algebra rigid complete in
/-- **The sides weigh more than the pieces**, when the annotation under the abstractions is a base type as it
stands. -/
theorem SpineRel.weight {n : Nat} {locals : List (Tm Head n)} {annotation left right : Tm Head n}
    {pieces : List (Piece Head n)} (read : SpineRel S.R true locals annotation left right pieces) :
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
  | @base n locals C h as bs T F pieces based _ _ looked read =>
      intro Γ formed types tl tr
      exact argRel_weight facts roots heads algebra rigid complete formed h (types.head looked) read
        (anyBase_spec rigid (based rfl)) tl tr
  | @proj n locals C h first as bs T F pieces based _ _ looked read =>
      intro Γ formed types tl tr
      exact projRel_weight facts roots heads algebra rigid complete formed h first (types.head looked) read
        (anyBase_spec rigid (based rfl)) tl tr

include facts roots heads in
/-- **The pieces are stratified among themselves.** -/
theorem SpineRel.internal {check : Bool} {n : Nat} {locals : List (Tm Head n)} {annotation left right : Tm Head n}
    {pieces : List (Piece Head n)} (read : SpineRel S.R check locals annotation left right pieces) :
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
  | @base n locals C h as bs T F pieces _ _ _ looked read =>
      intro Γ formed types tl tr
      have headType := types.head looked
      have th : TypedEquality.Typed S.R Γ (.var h) T := by
        have typedVar : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
        rwa [headType] at typedVar
      have principal : ∀ U, TypedEquality.Typed S.R Γ (.var h) U → TypeLe S.R Γ T U := by
        intro U typed
        have le : TypeLe S.R Γ (Ctx.lookup Γ h) U := Typed.generation typed
        rwa [headType] at le
      have typed := (read.typed facts roots heads formed principal th principal th tl tr).1
      have isT := Typed.isType th formed
      exact read.internal facts roots heads formed isT.refl isT isT typed
  | @proj n locals C h first as bs T F pieces _ _ _ looked read =>
      intro Γ formed types tl tr
      have headType := types.head looked
      have th : TypedEquality.Typed S.R Γ (.var h) T := by
        have typedVar : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
        rwa [headType] at typedVar
      have typed := projRel_typed facts roots heads formed h first headType read tl tr
      have isT := Typed.isType th formed
      exact read.internal facts roots heads formed isT.refl isT isT typed

end Theory

/-- **The reading is kept by substitutions that fix the locals**; the base type may become anything. -/
theorem SpineRel.subst {R : Rules Head} {check : Bool} {n : Nat} {locals : List (Tm Head n)}
    {annotation left right : Tm Head n} {pieces : List (Piece Head n)}
    (read : SpineRel R check locals annotation left right pieces) :
    ∀ {m : Nat} (σ : Sub Head n m), Fixes σ locals.length → locals.length ≤ m →
      SpineRel R false (locals.map (Presentation.subst σ)) (Presentation.subst σ annotation)
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
  | @base n locals C h as bs T F pieces _ small nonempty looked read =>
      intro m σ fixes bound
      have hm : h.val < m := by omega
      have fixedHead : σ h = .var ⟨h.val, hm⟩ := fixes h.val h.isLt hm small
      rw [subst_appSpine, subst_appSpine]
      simp only [Presentation.subst, fixedHead]
      refine .base (h := ⟨h.val, hm⟩) (T := Presentation.subst σ T) (F := Presentation.subst σ F)
        (fun impossible => by cases impossible) ?_ ?_ ?_ (read.subst σ)
      · simpa using small
      · simpa using nonempty
      · simp only [List.getElem?_map, looked, Option.map_some]
  | @proj n locals C h first as bs T F pieces _ small nonempty looked read =>
      intro m σ fixes bound
      have hm : h.val < m := by omega
      have fixedHead : σ h = .var ⟨h.val, hm⟩ := fixes h.val h.isLt hm small
      rw [subst_project, subst_project, subst_appSpine, subst_appSpine]
      simp only [Presentation.subst, fixedHead]
      refine .proj (h := ⟨h.val, hm⟩) (T := Presentation.subst σ T) (F := Presentation.subst σ F)
        (fun impossible => by cases impossible) ?_ ?_ ?_ (read.subst σ)
      · simpa using small
      · simpa using nonempty
      · simp only [List.getElem?_map, looked, Option.map_some]

/-- **The pieces have Miller normal reducts** when the two sides do, the locals rigid. -/
theorem SpineRel.reducts (empty : S.R.computation = RootComputation.empty) {check : Bool} {n : Nat}
    {locals : List (Tm Head n)} {annotation left right : Tm Head n} {pieces : List (Piece Head n)}
    (read : SpineRel S.R check locals annotation left right pieces) :
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
  | @base n locals C h as bs T F pieces _ small _ _ read =>
      intro mark localsRigid leftReduct rightReduct
      obtain ⟨sameL, sameR⟩ := read.sides
      have rigidHead := localsRigid h small
      intro piece member
      refine ⟨ContextualDependentCumulativeClosure.MarkedReduct.of_spine empty h rigidHead as leftReduct _ ?_,
        ContextualDependentCumulativeClosure.MarkedReduct.of_spine empty h rigidHead bs rightReduct _ ?_⟩
      · rw [← sameL]
        exact List.mem_map_of_mem member
      · rw [← sameR]
        exact List.mem_map_of_mem member
  | @proj n locals C h first as bs T F pieces _ small _ _ read =>
      intro mark localsRigid leftReduct rightReduct
      obtain ⟨sameL, sameR⟩ := read.sides
      have rigidHead := localsRigid h small
      have leftSpine := ContextualDependentCumulativeClosure.MarkedReduct.of_project empty first
        (ContextualDependentCumulativeClosure.elim_appSpine as (.var h)) leftReduct
      have rightSpine := ContextualDependentCumulativeClosure.MarkedReduct.of_project empty first
        (ContextualDependentCumulativeClosure.elim_appSpine bs (.var h)) rightReduct
      intro piece member
      refine ⟨ContextualDependentCumulativeClosure.MarkedReduct.of_spine empty h rigidHead as leftSpine _ ?_,
        ContextualDependentCumulativeClosure.MarkedReduct.of_spine empty h rigidHead bs rightSpine _ ?_⟩
      · rw [← sameL]
        exact List.mem_map_of_mem member
      · rw [← sameR]
        exact List.mem_map_of_mem member

/-! ## The shape -/

/-- **Two spines of one bound local under the same abstractions**, with equally many arguments and at least one, or
equal projections of two such spines, at an annotation that is a base type as it stands. -/
inductive AnySpines {Head : Type} : Nat → {n : Nat} → Tm Head n → Tm Head n → Tm Head n → Prop
  | under {depth n : Nat} {D : Tm Head n} {T l r : Tm Head (n + 1)} :
      AnySpines (depth + 1) T l r → AnySpines depth (.pi D T) (.lam l) (.lam r)
  | base {depth n : Nat} {C : Tm Head n} {h : Fin n} {as bs : List (Tm Head n)} :
      anyBase C = true → h.val < depth → as ≠ [] → as.length = bs.length →
      AnySpines depth C (appSpine (.var h) as) (appSpine (.var h) bs)
  | proj {depth n : Nat} {C : Tm Head n} {h : Fin n} {first : Bool} {as bs : List (Tm Head n)} :
      anyBase C = true → h.val < depth → as ≠ [] → as.length = bs.length →
      AnySpines depth C (project first (appSpine (.var h) as)) (project first (appSpine (.var h) bs))

/-- **The shape of the rigid readings is a shape at a base type**: R121's row is inside this one. -/
theorem LocalSpines.anySpines {Head : Type} {depth n : Nat} {annotation left right : Tm Head n}
    (shape : LocalSpines depth annotation left right) : AnySpines depth annotation left right := by
  induction shape with
  | under _ ih => exact .under ih
  | @base depth n C h as bs rigidB small nonempty same =>
      refine .base ?_ small nonempty same
      cases C <;> first | rfl | exact absurd rigidB Bool.false_ne_true
  | @proj depth n C h first as bs rigidB small nonempty same =>
      refine .proj ?_ small nonempty same
      cases C <;> first | rfl | exact absurd rigidB Bool.false_ne_true

/-- **Every checked reading has the shape.** -/
theorem SpineRel.anySpines {R : Rules Head} {n : Nat} {locals : List (Tm Head n)} {annotation left right : Tm Head n}
    {pieces : List (Piece Head n)} (read : SpineRel R true locals annotation left right pieces) :
    AnySpines locals.length annotation left right := by
  induction read with
  | under _ ih =>
      simp only [List.length_cons, List.length_map] at ih
      exact .under ih
  | base based small nonempty _ args =>
      obtain ⟨sameL, sameR⟩ := args.sides
      exact .base (based rfl) small nonempty (by rw [← sameL, ← sameR, List.length_map, List.length_map])
  | proj based small nonempty _ args =>
      obtain ⟨sameL, sameR⟩ := args.sides
      exact .proj (based rfl) small nonempty (by rw [← sameL, ← sameR, List.length_map, List.length_map])

/-! ## The executable reading -/

section Executable

variable (reducer : ExecutableReduction.Reducer S.R)

/-- The shape of two spines of one local at a base type as it stands: the local's type and the two argument lists. -/
def anyShape {n : Nat} (locals : List (Tm Head n)) (C left right : Tm Head n) :
    Option (Tm Head n × List (Tm Head n) × List (Tm Head n)) :=
  if anyBase C then
    match spineOf left, spineOf right with
    | some (h, as), some (h', bs) =>
        if h = h' ∧ h.val < locals.length ∧ 0 < as.length then (locals[h.val]?).map fun T => (T, as, bs) else none
    | _, _ => none
  else none

theorem anyShape_spec {n : Nat} {locals : List (Tm Head n)} {C left right T : Tm Head n}
    {as bs : List (Tm Head n)} (found : anyShape locals C left right = some (T, as, bs)) :
    ∃ h : Fin n, anyBase C = true ∧ left = appSpine (.var h) as ∧ right = appSpine (.var h) bs ∧
      h.val < locals.length ∧ as ≠ [] ∧ locals[h.val]? = some T := by
  unfold anyShape at found
  by_cases base : anyBase C = true
  · rw [if_pos base] at found
    cases sl : spineOf left with
    | none => rw [sl] at found; cases found
    | some readL =>
        obtain ⟨h, as'⟩ := readL
        cases sr : spineOf right with
        | none => rw [sl, sr] at found; cases found
        | some readR =>
            obtain ⟨h', bs'⟩ := readR
            rw [sl, sr] at found
            dsimp only at found
            by_cases cond : h = h' ∧ h.val < locals.length ∧ 0 < as'.length
            · rw [if_pos cond] at found
              obtain ⟨rfl, small, positive⟩ := cond
              obtain ⟨T', looked, same⟩ := Option.map_eq_some_iff.mp found
              simp only [Prod.mk.injEq] at same
              obtain ⟨rfl, rfl, rfl⟩ := same
              exact ⟨h, base, spineOf_spec sl, spineOf_spec sr, small, List.length_pos_iff.mp positive, looked⟩
            · rw [if_neg cond] at found
              cases found
  · rw [if_neg base] at found
    cases found

/-- The shape of two equal projections of spines of one local at a base type as it stands. -/
def anyProjShape {n : Nat} (locals : List (Tm Head n)) (C left right : Tm Head n) :
    Option (Tm Head n × List (Tm Head n) × List (Tm Head n)) :=
  match readProjection left, readProjection right with
  | some (first, l), some (first', r) => if first = first' then anyShape locals C l r else none
  | _, _ => none

theorem anyProjShape_spec {n : Nat} {locals : List (Tm Head n)} {C left right T : Tm Head n}
    {as bs : List (Tm Head n)} (found : anyProjShape locals C left right = some (T, as, bs)) :
    ∃ (first : Bool) (h : Fin n), anyBase C = true ∧
      left = project first (appSpine (.var h) as) ∧ right = project first (appSpine (.var h) bs) ∧
      h.val < locals.length ∧ as ≠ [] ∧ locals[h.val]? = some T := by
  unfold anyProjShape at found
  cases rl : readProjection left with
  | none => rw [rl] at found; cases found
  | some readL =>
      obtain ⟨first, l⟩ := readL
      cases rr : readProjection right with
      | none => rw [rl, rr] at found; cases found
      | some readR =>
          obtain ⟨first', r⟩ := readR
          rw [rl, rr] at found
          dsimp only at found
          by_cases same : first = first'
          · rw [if_pos same] at found
            subst same
            obtain ⟨h, base, rfl, rfl, small, nonempty, looked⟩ := anyShape_spec found
            exact ⟨first, h, base, readProjection_spec rl, readProjection_spec rr, small, nonempty, looked⟩
          · rw [if_neg same] at found
            cases found

/-- **Spines of one local, or equal projections of them, at a base type as it stands, along the reducer's reducts of
the instantiated types.** -/
def spineBaseN (fuel : Nat) {n : Nat} (locals : List (Tm Head n)) (C left right : Tm Head n) :
    Option (List (Piece Head n)) :=
  ((anyShape locals C left right).bind fun shape => argPartsN reducer fuel shape.1 shape.1 shape.2.1 shape.2.2).or
    ((anyProjShape locals C left right).bind fun shape =>
      argPartsN reducer fuel shape.1 shape.1 shape.2.1 shape.2.2)

/-- **Spines of one local under abstractions, along the reducer's reducts of the instantiated types**, at a base type
as it stands. -/
def spinesUnderN (fuel : Nat) : {n : Nat} → List (Tm Head n) → Tm Head n → Tm Head n → Tm Head n →
    Option (List (Piece Head n))
  | _, locals, .pi D T, .lam left, .lam right =>
      (spinesUnderN fuel (Presentation.rename wk D :: locals.map (Presentation.rename wk)) T left right).map
        (List.map (Piece.under D))
  | _, locals, C, left, right => spineBaseN reducer fuel locals C left right

theorem spinesUnderN_base (fuel : Nat) {n : Nat} {locals : List (Tm Head n)} {annotation left right : Tm Head n}
    (notUnder : ¬ ∃ D T l r, annotation = .pi D T ∧ left = .lam l ∧ right = .lam r) :
    spinesUnderN reducer fuel locals annotation left right =
      spineBaseN reducer fuel locals annotation left right := by
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
theorem spinesUnderN_rel (fuel : Nat) {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n)
    {pieces : List (Piece Head n)} (found : spinesUnderN reducer fuel locals annotation left right = some pieces) :
    SpineRel S.R true locals annotation left right pieces := by
  by_cases view : ∃ D T l r, annotation = .pi D T ∧ left = .lam l ∧ right = .lam r
  · obtain ⟨D, T, l, r, rfl, rfl, rfl⟩ := view
    simp only [spinesUnderN, Option.map_eq_some_iff] at found
    obtain ⟨inner, computed, rfl⟩ := found
    exact .under (spinesUnderN_rel fuel _ T l r computed)
  · rw [spinesUnderN_base reducer fuel view] at found
    unfold spineBaseN at found
    cases spineRead : (anyShape locals annotation left right).bind fun shape =>
        argPartsN reducer fuel shape.1 shape.1 shape.2.1 shape.2.2 with
    | some read =>
        rw [spineRead] at found
        cases found
        obtain ⟨⟨T, as, bs⟩, shaped, computed⟩ := Option.bind_eq_some_iff.mp spineRead
        obtain ⟨h, based, rfl, rfl, small, nonempty, looked⟩ := anyShape_spec shaped
        obtain ⟨F, rel⟩ := argPartsN_rel reducer fuel as bs computed .refl .refl
        exact .base (fun _ => based) small nonempty looked rel
    | none =>
        rw [spineRead] at found
        obtain ⟨⟨T, as, bs⟩, shaped, computed⟩ := Option.bind_eq_some_iff.mp found
        obtain ⟨first, h, based, rfl, rfl, small, nonempty, looked⟩ := anyProjShape_spec shaped
        obtain ⟨F, rel⟩ := argPartsN_rel reducer fuel as bs computed .refl .refl
        exact .proj (fun _ => based) small nonempty looked rel
termination_by sizeOf annotation

/-! ### Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  ContextualDependentConversionBudget.Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
/-- **The executable reading is eventually constant in the budget.** -/
theorem spinesUnderN_const {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n) :
    EventuallyConst fun fuel => spinesUnderN reducer fuel locals annotation left right := by
  by_cases view : ∃ D T l r, annotation = .pi D T ∧ left = .lam l ∧ right = .lam r
  · obtain ⟨D, T, l, r, rfl, rfl, rfl⟩ := view
    exact EventuallyConst.comp (Option.map (List.map (Piece.under D))) (spinesUnderN_const _ T l r)
  · refine EventuallyConst.of_eq (fun fuel => spinesUnderN_base reducer fuel view) ?_
    unfold spineBaseN
    have spines : EventuallyConst fun fuel => (anyShape locals annotation left right).bind fun shape =>
        argPartsN reducer fuel shape.1 shape.1 shape.2.1 shape.2.2 := by
      cases anyShape locals annotation left right with
      | none => exact EventuallyConst.const _
      | some shape => exact argPartsN_const reducer stable _ _ _ _
    have projections : EventuallyConst fun fuel => (anyProjShape locals annotation left right).bind fun shape =>
        argPartsN reducer fuel shape.1 shape.1 shape.2.1 shape.2.2 := by
      cases anyProjShape locals annotation left right with
      | none => exact EventuallyConst.const _
      | some shape => exact argPartsN_const reducer stable _ _ _ _
    exact EventuallyConst.comp (fun pair : Option (List (Piece Head n)) × Option (List (Piece Head n)) =>
      pair.1.or pair.2) (EventuallyConst.pair spines projections)
termination_by sizeOf annotation

omit stable in
/-- The executable reading of one equation's sides, with its checked reading. -/
def readSpines (fuel : Nat) {n : Nat} (annotation left right : Tm Head n) :
    Option {pieces : List (Piece Head n) // SpineRel S.R true [] annotation left right pieces} :=
  match found : spinesUnderN reducer fuel [] annotation left right with
  | some pieces => some ⟨pieces, spinesUnderN_rel reducer fuel [] annotation left right found⟩
  | none => none

omit stable in
theorem readSpines_val (fuel : Nat) {n : Nat} (annotation left right : Tm Head n) :
    (readSpines reducer fuel annotation left right).map Subtype.val =
      spinesUnderN reducer fuel [] annotation left right := by
  unfold readSpines
  split
  · rename_i pieces found
    exact found.symm
  · rename_i found
    exact found.symm

include stable in
theorem readSpines_const {n : Nat} (annotation left right : Tm Head n) :
    EventuallyConst fun fuel => readSpines reducer fuel annotation left right :=
  EventuallyConst.of_injective (g := Option.map Subtype.val) (Option.map_injective Subtype.val_injective)
    (EventuallyConst.of_eq (fun fuel => readSpines_val reducer fuel annotation left right)
      (spinesUnderN_const reducer stable [] annotation left right))

end Executable

/-! ## The tower: completeness of the executable reading -/

section Tower

open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls
open ContextualDependentAcceptance4
open ContextualDependentDynamicFragment (normal_pi_iff)
open ContextualDependentExecutableJoin (Normal)

/-- **The row at every base type**: at a normal annotation, with normal types of the locals read so far, typed sides
that are spines of one bound local at a base type as it stands are read along the reducts of the instantiated types
from some budget on. -/
theorem tower_spinesUnderN_reads {depth n : Nat} {annotation left right : Tower.Tm n}
    (shape : AnySpines depth annotation left right) :
    ∀ {Γ : Ctx (LevelTower.Head Nat) n} {locals : List (Tower.Tm n)}, CtxFormed setting.R Γ →
      LocalTypes Γ locals → locals.length = depth → (∀ T ∈ locals, Normal setting.R T) →
      Normal setting.R annotation → TypedEquality.Typed setting.R Γ left annotation →
      TypedEquality.Typed setting.R Γ right annotation →
      ∃ bound, ∀ larger, bound ≤ larger →
        (spinesUnderN (S := setting) ContextualDependentInversion.Controls.reducer larger locals annotation left
          right).isSome := by
  have empty : setting.R.computation = RootComputation.empty := rfl
  induction shape with
  | @under depth n D T l r _ ih =>
      intro Γ locals formed types length normalLocals normalA tl tr
      obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
      obtain ⟨normalD, normalT⟩ := (normal_pi_iff empty).mp normalA
      obtain ⟨bound, reads⟩ := ih (formed.snoc ⟨u, hu, tD⟩) (types.under D)
        (by simp only [List.length_cons, List.length_map, length])
        (fun T' member => by
          rcases List.mem_cons.mp member with rfl | later
          · exact (ContextualDependentNormalizing.normal_rename_iff empty wk D).mpr normalD
          · obtain ⟨T₀, inside, rfl⟩ := List.mem_map.mp later
            exact (ContextualDependentNormalizing.normal_rename_iff empty wk T₀).mpr (normalLocals T₀ inside))
        normalT (Typed.lam_inv TowerModel.facts tl formed) (Typed.lam_inv TowerModel.facts tr formed)
      refine ⟨bound, fun larger enough => ?_⟩
      simp only [spinesUnderN, Option.isSome_map]
      exact reads larger enough
  | @base depth n C h as bs based small nonempty same =>
      intro Γ locals formed types length normalLocals _ tl tr
      subst length
      have looked : locals[h.val]? = some locals[h.val] := List.getElem?_eq_getElem small
      have headType := types.head looked
      have nonemptyR : bs ≠ [] := fun nil => nonempty (List.eq_nil_of_length_eq_zero (by rw [same, nil]; rfl))
      have baseC : BaseType setting C := anyBase_spec ContextualDependentPiSpine.Controls.rigid based
      obtain ⟨UL, argsL⟩ := spineArgs_of_typed TowerModel.complete formed h baseC nonempty tl
      obtain ⟨UR, argsR⟩ := spineArgs_of_typed TowerModel.complete formed h baseC nonemptyR tr
      rw [headType] at argsL argsR
      have th : TypedEquality.Typed setting.R Γ (.var h) locals[h.val] := by
        have typedVar : TypedEquality.Typed setting.R Γ (.var h) (Ctx.lookup Γ h) := .var h
        rwa [headType] at typedVar
      have isT := Typed.isType th formed
      have normalT := normalLocals _ (List.getElem_mem small)
      obtain ⟨bound, reads⟩ := tower_argPartsN_reads formed as bs argsL argsR same .refl normalT isT.refl .refl
        normalT isT.refl
      refine ⟨bound, fun larger enough => ?_⟩
      rw [spinesUnderN_base _ _ (fun ⟨D, T, l, r, isPi, _, _⟩ => anyBase_not_pi based D T isPi)]
      have shaped : anyShape locals C (appSpine (.var h) as) (appSpine (.var h) bs) =
          some (locals[h.val], as, bs) := by
        unfold anyShape
        rw [if_pos based, spineOf_appSpine, spineOf_appSpine]
        dsimp only
        rw [if_pos ⟨rfl, small, List.length_pos_iff.mpr nonempty⟩, looked]
        rfl
      unfold spineBaseN
      rw [shaped]
      simp only [Option.bind_some, Option.isSome_or, reads larger enough, Bool.true_or]
  | @proj depth n C h first as bs based small nonempty same =>
      intro Γ locals formed types length normalLocals _ tl tr
      subst length
      have looked : locals[h.val]? = some locals[h.val] := List.getElem?_eq_getElem small
      have headType := types.head looked
      have baseC : BaseType setting C := anyBase_spec ContextualDependentPiSpine.Controls.rigid based
      obtain ⟨UL, argsL⟩ := spineArgs_of_projection TowerModel.complete formed h first baseC tl
      obtain ⟨UR, argsR⟩ := spineArgs_of_projection TowerModel.complete formed h first baseC tr
      rw [headType] at argsL argsR
      have th : TypedEquality.Typed setting.R Γ (.var h) locals[h.val] := by
        have typedVar : TypedEquality.Typed setting.R Γ (.var h) (Ctx.lookup Γ h) := .var h
        rwa [headType] at typedVar
      have isT := Typed.isType th formed
      have normalT := normalLocals _ (List.getElem_mem small)
      obtain ⟨bound, reads⟩ := tower_argPartsN_reads formed as bs argsL argsR same .refl normalT isT.refl .refl
        normalT isT.refl
      refine ⟨bound, fun larger enough => ?_⟩
      rw [spinesUnderN_base _ _ (fun ⟨D, T, l, r, isPi, _, _⟩ => anyBase_not_pi based D T isPi)]
      have shaped : anyProjShape locals C (project first (appSpine (.var h) as))
          (project first (appSpine (.var h) bs)) = some (locals[h.val], as, bs) := by
        unfold anyProjShape
        rw [readProjection_project, readProjection_project]
        dsimp only
        rw [if_pos rfl]
        unfold anyShape
        rw [if_pos based, spineOf_appSpine, spineOf_appSpine]
        dsimp only
        rw [if_pos ⟨rfl, small, List.length_pos_iff.mpr nonempty⟩, looked]
        rfl
      unfold spineBaseN
      rw [shaped]
      simp only [Option.bind_some, Option.isSome_or, reads larger enough, Bool.or_true]

end Tower

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
