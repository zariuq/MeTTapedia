import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIdEndpoints

/-!
# Spines headed by a projection

Under the abstractions of an equation, at a rigid base type, two **projections of spines of one local**,
`fst (g a₁ … aₖ) ≐ fst (g b₁ … bₖ)` (or `snd`), hold exactly when the arguments are equal along the
literal Π types of the local's prefixes: the algorithmic comparison compares two projections by their
projected spines (`spines` of `fst`/`snd`), and two spines of one local argument by argument (R97's
`spines_inv`). So the equation has exactly the solutions of R97's argument pieces of the projected spines
(`proj_exact`). Its normal form is the projection of the normal spine, so it weighs at least two more than
its pieces (`proj_weight`), and its decomposition is a committed step of the weight rank.

The **projections round** is the endpoints round, and when that round is stuck, one committed
decomposition of a projection spine on the prepared store with homogeneous twins.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentConstantHeadsProjections

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentFragment ContextualDependentDecisiveFragment
open ContextualDependentRigidFormers ContextualDependentEtaLong ContextualDependentRank
open ContextualDependentSpinesMany ContextualDependentConversionBudget ContextualDependentFragmentDecisive
open ContextualDependentOccursFull ContextualDependentTwinsUnder ContextualDependentConstantHeads
open ContextualDependentCensusPairEta ContextualDependentIdEndpoints ContextualDependentRigidDecomposition

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Projections -/

/-- The first (`true`) or second (`false`) projection. -/
def project {n : Nat} : Bool → Tm Head n → Tm Head n
  | true, p => .fst p
  | false, p => .snd p

/-- Read a projection. -/
def readProjection {n : Nat} : Tm Head n → Option (Bool × Tm Head n)
  | .fst p => some (true, p)
  | .snd p => some (false, p)
  | _ => none

theorem readProjection_spec {n : Nat} {t p : Tm Head n} {first : Bool}
    (read : readProjection t = some (first, p)) : t = project first p := by
  cases t <;> simp_all [readProjection, project]

theorem readProjection_project {n : Nat} (first : Bool) (p : Tm Head n) :
    readProjection (project first p) = some (first, p) := by
  cases first <;> rfl

theorem subst_project {n m : Nat} (σ : Sub Head n m) (first : Bool) (p : Tm Head n) :
    Presentation.subst σ (project first p) = project first (Presentation.subst σ p) := by
  cases first <;> rfl

/-- **The argument pieces of two projections of spines of one local**, under the abstractions read so far. -/
def projBase {n : Nat} (locals : List (Tm Head n)) (C left right : Tm Head n) : Option (List (Piece Head n)) :=
  match readProjection left, readProjection right with
  | some (first, l), some (first', r) => if first = first' then dependentBase locals C l r else none
  | _, _ => none

theorem projBase_spec {n : Nat} {locals : List (Tm Head n)} {C left right : Tm Head n}
    {pieces : List (Piece Head n)} (found : projBase locals C left right = some pieces) :
    ∃ first l r, left = project first l ∧ right = project first r ∧ dependentBase locals C l r = some pieces := by
  unfold projBase at found
  cases readL : readProjection left with
  | none => rw [readL] at found; cases found
  | some readingL =>
      obtain ⟨first, l⟩ := readingL
      cases readR : readProjection right with
      | none => rw [readL, readR] at found; cases found
      | some readingR =>
          obtain ⟨first', r⟩ := readingR
          rw [readL, readR] at found
          dsimp only at found
          by_cases same : first = first'
          · rw [if_pos same] at found
            subst same
            exact ⟨first, l, r, readProjection_spec readL, readProjection_spec readR, found⟩
          · rw [if_neg same] at found
            cases found

/-! ## Exactness and weight at a base type -/

section Theory

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

/-- The type of a projected term. -/
theorem project_generation {n : Nat} {Γ : Ctx Head n} {first : Bool} {p C : Tm Head n}
    (typed : TypedEquality.Typed S.R Γ (project first p) C) :
    ∃ A B, TypedEquality.Typed S.R Γ p (.sigma A B) ∧
      TypeLe S.R Γ (if first then A else inst0 (.fst p) B) C := by
  cases first with
  | true =>
      obtain ⟨A, B, tp, le⟩ := Typed.generation (show TypedEquality.Typed S.R Γ (.fst p) C from typed)
      exact ⟨A, B, tp, le⟩
  | false =>
      obtain ⟨A, B, tp, le⟩ := Typed.generation (show TypedEquality.Typed S.R Γ (.snd p) C from typed)
      exact ⟨A, B, tp, le⟩

/-- Projections are congruent, and keep the subtyping of their type. -/
theorem project_congr {n : Nat} {Γ : Ctx Head n} {first : Bool} {p q A C : Tm Head n} {B : Tm Head (n + 1)}
    (same : Equal S.R Γ p q (.sigma A B)) (le : TypeLe S.R Γ (if first then A else inst0 (.fst p) B) C)
    (isC : IsType S.R Γ C) : Equal S.R Γ (project first p) (project first q) C := by
  cases first with
  | true => exact .subEq (.fstCong same) (TypeLe.toBelow le isC)
  | false => exact .subEq (.sndCong same) (TypeLe.toBelow le isC)

/-- A projection of a neutral term is neutral. -/
theorem project_neutral {n : Nat} (first : Bool) {p : Tm Head n} (neutral : Neutral S.roles p) :
    Neutral S.roles (project first p) := by
  cases first with
  | true => exact .fst neutral
  | false => exact .snd neutral

/-- The algorithmic comparison of two projections compares their projected terms as spines. -/
theorem spines_project_inv {n : Nat} {Γ : Ctx Head n} (first : Bool) {p q U : Tm Head n}
    (derivation : Algorithmic S.R S.roles (.spines Γ (project first p) (project first q) U)) :
    ∃ U', Algorithmic S.R S.roles (.spines Γ p q U') := by
  cases first with
  | true =>
      cases derivation with
      | fst inner =>
          cases inner with
          | spinesW prefixSpines _ _ => exact ⟨_, prefixSpines⟩
  | false =>
      cases derivation with
      | snd inner =>
          cases inner with
          | spinesW prefixSpines _ _ => exact ⟨_, prefixSpines⟩

include facts roots heads algebra complete in
/-- **Projections of spines of one local decompose exactly** at a base type. -/
theorem proj_exact {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (h : Fin n) (first : Bool)
    {as bs : List (Tm Head n)} {T C : Tm Head n} {pieces : List (Piece Head n)} (headType : Ctx.lookup Γ h = T)
    (found : argParts T T as bs = some pieces) (base : BaseType S C)
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
  obtain ⟨left, final⟩ := argParts_typed_left facts formed as bs found principal th tp
  obtain ⟨right, _⟩ := argParts_typed_left facts formed bs as (argParts_swap as bs found) principal th tq
  have typed : ∀ piece ∈ pieces, piece.Typed S.R Γ := fun piece member =>
    ⟨left piece member, right _ (List.mem_map.mpr ⟨piece, member, rfl⟩)⟩
  obtain ⟨sameL, sameR⟩ := argParts_sides as bs found
  have length : as.length = bs.length := by rw [← sameL, ← sameR, List.length_map, List.length_map]
  have isT := Typed.isType th formed
  constructor
  · intro same
    obtain ⟨U, spines⟩ := terms_neutral_spines base (project_neutral first (neutral_appSpine h as))
      (project_neutral first (neutral_appSpine h bs)) (complete formed same)
    obtain ⟨U', prefixSpines⟩ := spines_project_inv first spines
    have args := spines_inv (S := S) h as bs length prefixSpines
    rw [headType] at args
    exact argParts_holds facts roots heads algebra formed as bs found args isT.refl isT isT typed
  · intro held
    have congr := argParts_congr as bs found held (.refl th)
    have atSigma : Equal S.R Γ (appSpine (.var h) as) (appSpine (.var h) bs) (.sigma A B) :=
      .subEq congr (TypeLe.toBelow final (Typed.isType tp formed))
    exact project_congr atSigma le (Typed.isType tl formed)

include facts roots heads algebra rigid complete in
/-- **The normal form of a projection of a spine** is the projection of the normal spine. -/
theorem proj_side {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (h : Fin n) (first : Bool)
    {cs ds : List (Tm Head n)} {T C : Tm Head n} {pieces : List (Piece Head n)} (headType : Ctx.lookup Γ h = T)
    (found : argParts T T cs ds = some pieces) (base : BaseType S C)
    (typedC : TypedEquality.Typed S.R Γ (project first (appSpine (.var h) cs)) C) :
    ∃ ws, ArgWeights S Γ cs (pieces.map (·.leftType)) ws ∧
      HasWeight S Γ (project first (appSpine (.var h) cs)) C (2 + ws.sum + pieces.length) := by
  have principal : ∀ U, TypedEquality.Typed S.R Γ (.var h) U → TypeLe S.R Γ T U := by
    intro U typed
    have le : TypeLe S.R Γ (Ctx.lookup Γ h) U := Typed.generation typed
    rwa [headType] at le
  have th : TypedEquality.Typed S.R Γ (.var h) T := by
    have typed : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
    rwa [headType] at typed
  have longHead : Long S.R S.roles (.spine Γ (.var h) T) := by
    refine .var h ?_
    rw [headType]
    exact IsType.refl (Typed.isType th formed)
  have baseC := BaseType.base facts formed base
  have isC := Typed.isType typedC formed
  obtain ⟨A₀, B₀, tp, le⟩ := project_generation typedC
  obtain ⟨typed, final⟩ := argParts_typed_left facts formed cs ds found principal th tp
  obtain ⟨ns, ws, weights, longSpine, equalSpine, weighed⟩ :=
    argParts_normal facts roots heads algebra rigid complete formed cs ds found longHead (.refl th) typed
  have isSigma := Typed.isType tp formed
  have belowSigma := TypeLe.toBelow final isSigma
  obtain ⟨A, B, eF, leA, leB⟩ := Below.sigma_inv facts belowSigma formed (IsType.refl isSigma)
  have atSigma : Equal S.R Γ (appSpine (.var h) cs) (appSpine (.var h) ns) (.sigma A₀ B₀) := .subEq equalSpine belowSigma
  have equalC := project_congr atSigma le isC
  have typedN := (Equal.typed equalC formed).2
  have isAB : IsType S.R Γ (.sigma A B) := by
    obtain ⟨uF, huF, eqF⟩ := eF
    exact ⟨uF, huF, (Equal.typed eqF formed).2⟩
  obtain ⟨⟨u, hu, tA⟩, ⟨v, hv, tB⟩⟩ := IsType.sigma_parts isAB
  have nSigma : TypedEquality.Typed S.R Γ (appSpine (.var h) ns) (.sigma A B) :=
    Typed.convType longSpine.spine_typed eF
  refine ⟨ws, weights, project first (appSpine (.var h) ns), ⟨?_, equalC⟩, ?_⟩
  · cases first with
    | true =>
        have longFst : Long S.R S.roles (.spine Γ (.fst (appSpine (.var h) ns)) A) :=
          .fst longSpine eF (IsType.refl ⟨u, hu, tA⟩)
        exact .neutral longFst (.subTrans leA (TypeLe.toBelow le isC)) typedN baseC
    | false =>
        have tFst : TypedEquality.Typed S.R Γ (.fst (appSpine (.var h) ns)) A := Derivable.fstElim nSigma
        have isU : IsType S.R Γ (inst0 (.fst (appSpine (.var h) ns)) B) := ⟨v, hv, Typed.instantiate tB tFst⟩
        have longSnd : Long S.R S.roles (.spine Γ (.snd (appSpine (.var h) ns)) (inst0 (.fst (appSpine (.var h) ns)) B)) :=
          .snd longSpine eF (IsType.refl isU)
        obtain ⟨⟨u₀, hu₀, tA₀⟩, ⟨v₀, hv₀, tB₀⟩⟩ := IsType.sigma_parts isSigma
        have tFst₀ : TypedEquality.Typed S.R Γ (.fst (appSpine (.var h) ns)) A₀ := .sub tFst leA
        have stepB : Below S.R Γ (inst0 (.fst (appSpine (.var h) ns)) B) (inst0 (.fst (appSpine (.var h) ns)) B₀) :=
          Derivable.substitutes leB (SubstMor.single tFst)
        have firsts : Equal S.R Γ (.fst (appSpine (.var h) ns)) (.fst (appSpine (.var h) cs)) A₀ :=
          .symm (.fstCong atSigma)
        have stepEq : TypeEq S.R Γ (inst0 (.fst (appSpine (.var h) ns)) B₀) (inst0 (.fst (appSpine (.var h) cs)) B₀) :=
          TypeEq.of_instantiateEq tB₀ hv₀ tFst₀ firsts
        exact .neutral longSnd (.subTrans stepB (.subTrans stepEq.below (TypeLe.toBelow le isC))) typedN baseC
  · cases first <;>
    · simp only [project, ContextualDependentRank.weight, weighed]
      omega

include facts roots heads algebra rigid complete in
/-- **Projections of spines of one local weigh more than their argument pieces.** -/
theorem proj_weight {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (h : Fin n) (first : Bool)
    {as bs : List (Tm Head n)} {T C : Tm Head n} {pieces : List (Piece Head n)} (headType : Ctx.lookup Γ h = T)
    (found : argParts T T as bs = some pieces) (base : BaseType S C)
    (tl : TypedEquality.Typed S.R Γ (project first (appSpine (.var h) as)) C)
    (tr : TypedEquality.Typed S.R Γ (project first (appSpine (.var h) bs)) C) :
    ∃ w wl wr, PiecesWeigh S Γ pieces w ∧ HasWeight S Γ (project first (appSpine (.var h) as)) C wl ∧
      HasWeight S Γ (project first (appSpine (.var h) bs)) C wr ∧ w + 2 ≤ wl + wr := by
  obtain ⟨sameL, sameR⟩ := argParts_sides as bs found
  obtain ⟨ws, weights, left⟩ :=
    proj_side facts roots heads algebra rigid complete formed h first headType found base tl
  obtain ⟨ws', weights', right⟩ :=
    proj_side facts roots heads algebra rigid complete formed h first headType (argParts_swap as bs found) base tr
  rw [← sameL] at weights
  rw [List.map_map, ← sameR] at weights'
  have pieces := ArgWeights.piecesOf (S := S) weights (by simpa [Function.comp_def] using weights')
  refine ⟨ws.sum + ws'.sum, _, _, pieces, left, right, ?_⟩
  simp only [List.length_map]
  omega

include facts in
/-- **The argument pieces of two projections of spines are typed.** -/
theorem proj_typed {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (h : Fin n) (first : Bool)
    {as bs : List (Tm Head n)} {T C : Tm Head n} {pieces : List (Piece Head n)} (headType : Ctx.lookup Γ h = T)
    (found : argParts T T as bs = some pieces)
    (tl : TypedEquality.Typed S.R Γ (project first (appSpine (.var h) as)) C)
    (tr : TypedEquality.Typed S.R Γ (project first (appSpine (.var h) bs)) C) :
    ∀ piece ∈ pieces, piece.Typed S.R Γ := by
  have principal : ∀ U, TypedEquality.Typed S.R Γ (.var h) U → TypeLe S.R Γ T U := by
    intro U typed
    have le : TypeLe S.R Γ (Ctx.lookup Γ h) U := Typed.generation typed
    rwa [headType] at le
  have th : TypedEquality.Typed S.R Γ (.var h) T := by
    have typed : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
    rwa [headType] at typed
  obtain ⟨A, B, tp, _⟩ := project_generation tl
  obtain ⟨A', B', tq, _⟩ := project_generation tr
  obtain ⟨left, _⟩ := argParts_typed_left facts formed as bs found principal th tp
  obtain ⟨right, _⟩ := argParts_typed_left facts formed bs as (argParts_swap as bs found) principal th tq
  exact fun piece member => ⟨left piece member, right _ (List.mem_map.mpr ⟨piece, member, rfl⟩)⟩

end Theory

/-! ## Projection spines under abstractions -/

/-- **Projections of spines of one local under abstractions**, read from the annotation and the two sides. -/
def projUnder : {n : Nat} → List (Tm Head n) → Tm Head n → Tm Head n → Tm Head n → Option (List (Piece Head n))
  | _, locals, .pi D T, .lam left, .lam right =>
      (projUnder (Presentation.rename wk D :: locals.map (Presentation.rename wk)) T left right).map
        (List.map (Piece.under D))
  | _, locals, C, left, right => projBase locals C left right

theorem projUnder_cases {n : Nat} {locals : List (Tm Head n)} {annotation left right : Tm Head n}
    {pieces : List (Piece Head n)} (found : projUnder locals annotation left right = some pieces) :
    (∃ D T l r inner, annotation = .pi D T ∧ left = .lam l ∧ right = .lam r ∧
      projUnder (Presentation.rename wk D :: locals.map (Presentation.rename wk)) T l r = some inner ∧
      pieces = inner.map (Piece.under D)) ∨ projBase locals annotation left right = some pieces := by
  cases annotation with
  | pi D T =>
      cases left with
      | lam l =>
          cases right with
          | lam r =>
              simp only [projUnder, Option.map_eq_some_iff] at found
              obtain ⟨inner, computed, rfl⟩ := found
              exact .inl ⟨D, T, l, r, inner, rfl, rfl, rfl, computed, rfl⟩
          | _ => exact .inr (by simpa [projUnder] using found)
      | _ => exact .inr (by simpa [projUnder] using found)
  | _ => exact .inr (by simpa [projUnder] using found)

theorem projUnder_base {n : Nat} {locals : List (Tm Head n)} {C left right : Tm Head n}
    (notPi : ∀ D T, C ≠ .pi D T) : projUnder locals C left right = projBase locals C left right := by
  cases C with
  | pi D T => exact absurd rfl (notPi D T)
  | _ => simp [projUnder]

/-- **The reading is kept by substitutions that fix the locals.** -/
theorem projUnder_subst : ∀ {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n)
    {pieces : List (Piece Head n)}, projUnder locals annotation left right = some pieces →
    ∀ {m : Nat} (σ : Sub Head n m), Fixes σ locals.length → locals.length ≤ m →
      projUnder (locals.map (Presentation.subst σ)) (Presentation.subst σ annotation)
        (Presentation.subst σ left) (Presentation.subst σ right) = some (pieces.map (Piece.subst σ)) := by
  intro n locals annotation left right pieces found m σ fixes bound
  rcases projUnder_cases found with ⟨D, T, l, r, inner, rfl, rfl, rfl, computed, rfl⟩ | base
  · have below := projUnder_subst _ T l r computed (liftSub σ) (by simpa using fixes.lift) (by simp; omega)
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
    simp only [Presentation.subst, projUnder, List.map_map]
    rw [below]
    simp only [Option.map_some, List.map_map]
    rfl
  · obtain ⟨first, l, r, rfl, rfl, inner⟩ := projBase_spec base
    obtain ⟨h, as, bs, T, rigidC, _, _, _, _, _, _⟩ := dependentBase_spec inner
    have notPi := rigidBase_not_pi rigidC
    have notPi' := rigidBase_not_pi (rigidBase_subst (n := n) fixes bound rigidC)
    have moved := dependentUnder_subst locals annotation l r (by rw [dependentUnder_base notPi]; exact inner) σ fixes
      bound
    rw [dependentUnder_base notPi'] at moved
    rw [projUnder_base notPi']
    unfold projBase
    rw [subst_project, subst_project, readProjection_project, readProjection_project]
    simp only [if_true]
    exact moved

section UnderTheory

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts in
theorem projBase_typed {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {locals : List (Tm Head n)}
    (types : LocalTypes Γ locals) {C left right : Tm Head n} {pieces : List (Piece Head n)}
    (found : projBase locals C left right = some pieces) (tl : TypedEquality.Typed S.R Γ left C)
    (tr : TypedEquality.Typed S.R Γ right C) : ∀ piece ∈ pieces, piece.Typed S.R Γ := by
  obtain ⟨first, l, r, rfl, rfl, inner⟩ := projBase_spec found
  obtain ⟨h, as, bs, T, _, rfl, rfl, _, _, looked, read⟩ := dependentBase_spec inner
  exact proj_typed facts formed h first (types.head looked) read tl tr

include facts roots heads algebra complete in
theorem projBase_exact {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {locals : List (Tm Head n)}
    (types : LocalTypes Γ locals) {C left right : Tm Head n} {pieces : List (Piece Head n)}
    (found : projBase locals C left right = some pieces) (tl : TypedEquality.Typed S.R Γ left C)
    (tr : TypedEquality.Typed S.R Γ right C) :
    Equal S.R Γ left right C ↔ ∀ piece ∈ pieces, piece.Holds S.R Γ := by
  obtain ⟨first, l, r, rfl, rfl, inner⟩ := projBase_spec found
  obtain ⟨h, as, bs, T, rigidC, rfl, rfl, _, _, looked, read⟩ := dependentBase_spec inner
  exact proj_exact facts roots heads algebra complete formed h first (types.head looked) read (rigidBase_spec rigidC)
    tl tr

include facts roots heads algebra rigid complete in
theorem projBase_weight {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {locals : List (Tm Head n)}
    (types : LocalTypes Γ locals) {C left right : Tm Head n} {pieces : List (Piece Head n)}
    (found : projBase locals C left right = some pieces) (tl : TypedEquality.Typed S.R Γ left C)
    (tr : TypedEquality.Typed S.R Γ right C) :
    ∃ w wl wr, PiecesWeigh S Γ pieces w ∧ HasWeight S Γ left C wl ∧ HasWeight S Γ right C wr ∧ w + 2 ≤ wl + wr := by
  obtain ⟨first, l, r, rfl, rfl, inner⟩ := projBase_spec found
  obtain ⟨h, as, bs, T, rigidC, rfl, rfl, _, _, looked, read⟩ := dependentBase_spec inner
  exact proj_weight facts roots heads algebra rigid complete formed h first (types.head looked) read
    (rigidBase_spec rigidC) tl tr

include facts in
/-- **The pieces of projection spines under abstractions are typed.** -/
theorem projUnder_typed : ∀ {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n)
    {Γ : Ctx Head n} {pieces : List (Piece Head n)}, CtxFormed S.R Γ → LocalTypes Γ locals →
    projUnder locals annotation left right = some pieces →
    TypedEquality.Typed S.R Γ left annotation → TypedEquality.Typed S.R Γ right annotation →
    ∀ piece ∈ pieces, piece.Typed S.R Γ
  | _, locals, .pi D T, left, right, Γ, pieces, formed, types, found, tl, tr => by
      rcases projUnder_cases found with ⟨D', T', l, r, inner, same, rfl, rfl, computed, rfl⟩ | base
      · injection same with _ sameD sameT
        subst sameD
        subst sameT
        obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
        have below := projUnder_typed _ T l r (formed.snoc ⟨u, hu, tD⟩) (types.under D) computed
          (Typed.lam_inv facts tl formed) (Typed.lam_inv facts tr formed)
        intro piece member
        obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
        exact Piece.typed_under formed ⟨u, hu, tD⟩ (below original inside)
      · exact projBase_typed facts formed types base tl tr
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
      rcases projUnder_cases found with ⟨_, _, _, _, _, same, _⟩ | base
      · cases same
      · exact projBase_typed facts formed types base tl tr

include facts roots heads algebra complete in
/-- **Projection spines under abstractions decompose exactly** into their pieces, at every formed context. -/
theorem projUnder_exact : ∀ {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n)
    {Γ : Ctx Head n} {pieces : List (Piece Head n)}, CtxFormed S.R Γ → LocalTypes Γ locals →
    projUnder locals annotation left right = some pieces →
    TypedEquality.Typed S.R Γ left annotation → TypedEquality.Typed S.R Γ right annotation →
    (Equal S.R Γ left right annotation ↔ ∀ piece ∈ pieces, piece.Holds S.R Γ)
  | _, locals, .pi D T, left, right, Γ, pieces, formed, types, found, tl, tr => by
      rcases projUnder_cases found with ⟨D', T', l, r, inner, same, rfl, rfl, computed, rfl⟩ | base
      · injection same with _ sameD sameT
        subst sameD
        subst sameT
        obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
        have isD : IsType S.R Γ D := ⟨u, hu, tD⟩
        have formedD := formed.snoc isD
        have tl' := Typed.lam_inv facts tl formed
        have tr' := Typed.lam_inv facts tr formed
        have below := projUnder_exact _ T l r formedD (types.under D) computed tl' tr'
        have typed := projUnder_typed facts _ T l r formedD (types.under D) computed tl' tr'
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
      · exact projBase_exact facts roots heads algebra complete formed types base tl tr
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
      rcases projUnder_cases found with ⟨_, _, _, _, _, same, _⟩ | base
      · cases same
      · exact projBase_exact facts roots heads algebra complete formed types base tl tr

include facts roots heads algebra rigid complete in
/-- **Projection spines under abstractions weigh more than their pieces.** -/
theorem projUnder_weight : ∀ {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n)
    {Γ : Ctx Head n} {pieces : List (Piece Head n)}, CtxFormed S.R Γ → LocalTypes Γ locals →
    projUnder locals annotation left right = some pieces →
    TypedEquality.Typed S.R Γ left annotation → TypedEquality.Typed S.R Γ right annotation →
    ∃ w wl wr, PiecesWeigh S Γ pieces w ∧ HasWeight S Γ left annotation wl ∧ HasWeight S Γ right annotation wr ∧
      w + 2 ≤ wl + wr
  | _, locals, .pi D T, left, right, Γ, pieces, formed, types, found, tl, tr => by
      rcases projUnder_cases found with ⟨D', T', l, r, inner, same, rfl, rfl, computed, rfl⟩ | base
      · injection same with _ sameD sameT
        subst sameD
        subst sameT
        obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
        have isD : IsType S.R Γ D := ⟨u, hu, tD⟩
        have formedD := formed.snoc isD
        have tl' := Typed.lam_inv facts tl formed
        have tr' := Typed.lam_inv facts tr formed
        obtain ⟨w, wl, wr, weighs, left, right, total⟩ :=
          projUnder_weight _ T l r formedD (types.under D) computed tl' tr'
        have typed := projUnder_typed facts _ T l r formedD (types.under D) computed tl' tr'
        obtain ⟨v, hv, tPi⟩ := Typed.isType tl formed
        exact ⟨w, wl, wr, PiecesWeigh.under formed isD typed weighs, HasWeight.under (w := v) hv tPi isD left,
          HasWeight.under (w := v) hv tPi isD right, total⟩
      · exact projBase_weight facts roots heads algebra rigid complete formed types base tl tr
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
      rcases projUnder_cases found with ⟨_, _, _, _, _, same, _⟩ | base
      · cases same
      · exact projBase_weight facts roots heads algebra rigid complete formed types base tl tr

end UnderTheory

end ContextualDependentConstantHeadsProjections
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
