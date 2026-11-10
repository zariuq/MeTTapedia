import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthArgParts

/-!
# The piece family: decompositions at normal annotations

The annotations of the pieces of a decomposition are instances of the equation's annotation, or of a local's type at
the arguments before them, so they need not be normal: `Id U0 ((λ k. k X) (λ w. w)) ((λ k. k X) (λ w. w))` in
`PieceControls.pieceStore`. The executable former of types reads a redex only when its argument synthesizes, so such a
piece is not formed and the decomposition does not fire (`PieceControls.pieceType_not_formed`).

The **decomposition at normal annotations** forms each piece at the reducer's reducts of its annotations
(`normalPiece`), types equal to the annotations (`normalCode_typeEq`), and reads the store back as a store of the
original pieces (`transferStore`): related pieces, with the same sides and equal annotations (`PieceRelated`), hold
together under every substitution into a formed context (`PieceRelated.holds_iff`) and weigh the same
(`piecesWeigh_related`). Replacing an equation by store equations related to its pieces keeps the permuted Miller class
(`PermutedMiller.splice_related`), so the decompositions at normal annotations, under abstractions (`underNormal`),
between spines of one local (`spineNormal`), and between spines of one local or their projections read along the
reducts of the instantiated types (`argsNormal`, with `finishArgs`), keep it (`underNormal_keeps`, `spineNormal_keeps`,
`argsNormal_keeps`).

**The piece round** (`pieceRound`) is the skeleton round; when that is stuck, the decomposition at normal annotations of
the η-long prepared store (`normalRound`), committed. The family is conservative over the skeleton family
(`piece_run_of_skeleton`), eventually constant (`pieceRound_const`), closed in the permuted Miller class
(`pieceRound_closure`), and so decides every store of the dynamic pattern fragment as soon as its round is eventually not
stuck on nonempty stores of the class (`piece_decided_of_firing`, `tower_piece_decided_of_firing`), in particular as
soon as one of its readers reads (`PieceReads`, `tower_piece_decided_of_pieceReads`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaDepth

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRank ContextualDependentConversionBudget ContextualDependentDynamicFragment
open ContextualDependentIntersectionGeneral ContextualDependentMillerClosure ContextualDependentOpenedNormal
open ContextualDependentAcceptance4 ContextualDependentCoverageReadersHalf ContextualDependentTwinsUnder
open ContextualDependentConstantHeads ContextualDependentCumulativeClosure
open ContextualDependentSpinesMany ContextualDependentShortClosure ContextualDependentClosure ContextualDependentEtaLong
open ContextualDependentRigidFormers

/-! ## Lists related pointwise -/

theorem forall₂_mem {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {a}, a ∈ l₁ → ∃ b ∈ l₂, R a b
  | [], [], .nil, _, member => absurd member List.not_mem_nil
  | a' :: as, b' :: bs, .cons head tail, a, member => by
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨b', List.mem_cons_self, head⟩
      · obtain ⟨b, inB, related⟩ := forall₂_mem tail later
        exact ⟨b, List.mem_cons_of_mem _ inB, related⟩

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {b}, b ∈ l₂ → ∃ a ∈ l₁, R a b
  | [], [], .nil, _, member => absurd member List.not_mem_nil
  | a' :: as, b' :: bs, .cons head tail, b, member => by
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨a', List.mem_cons_self, head⟩
      · obtain ⟨a, inA, related⟩ := forall₂_mem_right tail later
        exact ⟨a, List.mem_cons_of_mem _ inA, related⟩

theorem forall₂_split {α β : Type} {R : α → β → Prop} :
    ∀ (first : List α) {x : α} {last : List α} {l₂ : List β}, List.Forall₂ R (first ++ x :: last) l₂ →
      ∃ first' y last', l₂ = first' ++ y :: last' ∧ List.Forall₂ R first first' ∧ R x y
  | [], x, last, l₂, related => by
      cases related with
      | cons head tail => exact ⟨[], _, _, rfl, .nil, head⟩
  | a :: as, x, last, l₂, related => by
      cases related with
      | cons head tail =>
          obtain ⟨first', y, last', rfl, before, here⟩ := forall₂_split as tail
          exact ⟨_ :: first', y, last', rfl, .cons head before, here⟩

theorem forall₂_of_map {α β γ : Type} {f : α → γ} {R : γ → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R (l₁.map f) l₂ → List.Forall₂ (fun a b => R (f a) b) l₁ l₂
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons head tail => .cons head (forall₂_of_map tail)

theorem forall₂_map_self {α β : Type} {f : α → β} {R : β → α → Prop} :
    ∀ {l : List α}, (∀ a ∈ l, R (f a) a) → List.Forall₂ R (l.map f) l
  | [], _ => .nil
  | a :: _, each => .cons (each a List.mem_cons_self)
      (forall₂_map_self fun other member => each other (List.mem_cons_of_mem _ member))

/-! ## Pieces with equal annotations -/

section Related

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **Two related pieces**: the same sides, and equal annotations. -/
def PieceRelated (R : Rules Head) {n : Nat} (Γ : Ctx Head n) (q p : Piece Head n) : Prop :=
  q.left = p.left ∧ q.right = p.right ∧ TypeEq R Γ q.leftType p.leftType ∧ TypeEq R Γ q.rightType p.rightType

/-- **Related pieces hold together**, under every substitution into a formed context. -/
theorem PieceRelated.holds_iff {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {σ : Sub Head n m}
    {q p : Piece Head n} (related : PieceRelated S.R Γ q p) (typed : SubstMor S.R Γ Δ σ) :
    (q.subst σ).Holds S.R Δ ↔ (p.subst σ).Holds S.R Δ := by
  obtain ⟨sameLeft, sameRight, leftEq, rightEq⟩ := related
  have l := ContextualDependentWeightPrune.typeEq_subst leftEq typed
  have r := ContextualDependentWeightPrune.typeEq_subst rightEq typed
  unfold Piece.Holds Piece.subst
  dsimp only
  rw [sameLeft, sameRight]
  constructor
  · rintro ⟨types, equal⟩
    exact ⟨TypeEq.trans S.levels (TypeEq.trans S.levels (TypeEq.symm l) types) r, Equal.convType equal l⟩
  · rintro ⟨types, equal⟩
    exact ⟨TypeEq.trans S.levels (TypeEq.trans S.levels l types) (TypeEq.symm r), Equal.convType equal (TypeEq.symm l)⟩

/-- A normal form at a type is one at every equal type. -/
theorem hasWeight_convType {n : Nat} {Γ : Ctx Head n} {t T T' : Tm Head n} {a : Nat}
    (weighs : HasWeight S Γ t T a) (equal : TypeEq S.R Γ T T') : HasWeight S Γ t T' a := by
  obtain ⟨v, ⟨long, same⟩, weight⟩ := weighs
  exact ⟨v, ⟨Long.convType S.levels long equal, Equal.convType same equal⟩, weight⟩

/-- **Related pieces weigh the same.** -/
theorem piecesWeigh_related {n : Nat} {Γ : Ctx Head n} :
    ∀ {qs ps : List (Piece Head n)}, List.Forall₂ (PieceRelated S.R Γ) qs ps → ∀ {w : Nat},
      PiecesWeigh S Γ ps w → PiecesWeigh S Γ qs w
  | [], [], .nil, _, weighs => weighs
  | _ :: _, _ :: _, .cons related rest, _, weighs => by
      obtain ⟨a, b, c, left, right, others, total⟩ := weighs
      obtain ⟨sameLeft, sameRight, leftEq, rightEq⟩ := related
      refine ⟨a, b, c, ?_, ?_, piecesWeigh_related rest others, total⟩
      · rw [sameLeft]
        exact hasWeight_convType left (TypeEq.symm leftEq)
      · rw [sameRight]
        exact hasWeight_convType right (TypeEq.symm rightEq)

theorem holds_related {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {σ : Sub Head n m}
    (typed : SubstMor S.R Γ Δ σ) :
    ∀ {qs ps : List (Piece Head n)}, List.Forall₂ (PieceRelated S.R Γ) qs ps →
      ((∀ q ∈ qs, (q.subst σ).Holds S.R Δ) ↔ ∀ p ∈ ps, (p.subst σ).Holds S.R Δ)
  | [], [], .nil => by simp
  | _ :: _, _ :: _, .cons related rest => by
      rw [List.forall_mem_cons, List.forall_mem_cons, PieceRelated.holds_iff related typed, holds_related typed rest]

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

/-- **A store of related pieces is a store of the pieces**: the same solutions and the same weight. -/
def transferStore {Θ : Context S.R} {qs ps : List (Piece Head Θ.arity)}
    (related : List.Forall₂ (PieceRelated S.R Θ.raw) qs ps)
    (store : PieceStore facts roots heads algebra rigid complete qs) :
    PieceStore facts roots heads algebra rigid complete ps :=
  ⟨store.val, fun σ => (store.property.1 σ).trans (holds_related σ.typed related),
    fun w weighs => store.property.2 w (piecesWeigh_related related weighs)⟩

end Related

/-! ## Annotations at their normal forms -/

section Normal

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
variable (reducer : ExecutableReduction.Reducer S.R)

/-- A piece with both annotations at the reducer's reducts. -/
def normalPiece (fuel : Nat) {n : Nat} (piece : Piece Head n) : Piece Head n :=
  ⟨normalCode reducer fuel piece.leftType, piece.left, normalCode reducer fuel piece.rightType, piece.right⟩

include facts roots heads in
theorem normalPiece_related (fuel : Nat) {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {piece : Piece Head n} (typed : piece.Typed S.R Γ) :
    PieceRelated S.R Γ (normalPiece reducer fuel piece) piece :=
  ⟨rfl, rfl, TypeEq.symm (normalCode_typeEq facts roots heads reducer fuel formed (Typed.isType typed.1 formed)),
    TypeEq.symm (normalCode_typeEq facts roots heads reducer fuel formed (Typed.isType typed.2 formed))⟩

include facts roots heads in
theorem normalPiece_typed (fuel : Nat) {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {piece : Piece Head n} (typed : piece.Typed S.R Γ) : (normalPiece reducer fuel piece).Typed S.R Γ :=
  ⟨Typed.convType typed.1 (normalCode_typeEq facts roots heads reducer fuel formed (Typed.isType typed.1 formed)),
    Typed.convType typed.2 (normalCode_typeEq facts roots heads reducer fuel formed (Typed.isType typed.2 formed))⟩

/-- Typed pieces related to the given ones. -/
abbrev RelatedPieces {Θ : Context S.R} (pieces : List (Piece Head Θ.arity)) :=
  {qs : List (Piece Head Θ.arity) // (∀ q ∈ qs, q.Typed S.R Θ.raw) ∧ List.Forall₂ (PieceRelated S.R Θ.raw) qs pieces}

/-- **The pieces with their annotations at the reducer's reducts.** -/
def normalPieces (fuel : Nat) {Θ : Context S.R} (pieces : List (Piece Head Θ.arity))
    (typed : ∀ piece ∈ pieces, piece.Typed S.R Θ.raw) : RelatedPieces pieces :=
  ⟨pieces.map (normalPiece reducer fuel), fun q member => by
      obtain ⟨piece, inside, rfl⟩ := List.mem_map.mp member
      exact normalPiece_typed facts roots heads reducer fuel Θ.formed (typed piece inside),
    forall₂_map_self fun piece inside => normalPiece_related facts roots heads reducer fuel Θ.formed
      (typed piece inside)⟩

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (declared : DeclaredTypesFormed S.R) (choices : ExecutableChecking.HeadChoices S.R)

/-- Form related pieces as store equations, read as a store of the pieces. -/
def formRelated (fuel : Nat) {Θ : Context S.R} {pieces : List (Piece Head Θ.arity)}
    (related : RelatedPieces pieces) : Option (PieceStore facts roots heads algebra rigid complete pieces) :=
  (formPieces facts roots heads algebra rigid complete declared choices reducer fuel related.val
    related.property.1).map (transferStore facts roots heads algebra rigid complete related.property.2)

/-- **Form the pieces at the normal forms of their annotations.** -/
def formNormal (fuel : Nat) {Θ : Context S.R} (pieces : List (Piece Head Θ.arity))
    (typed : ∀ piece ∈ pieces, piece.Typed S.R Θ.raw) :
    Option (PieceStore facts roots heads algebra rigid complete pieces) :=
  formRelated facts roots heads algebra rigid complete reducer declared choices fuel
    (normalPieces facts roots heads reducer fuel pieces typed)

/-- **The decomposition under abstractions, at normal annotations.** -/
def underNormal (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    Option (WeighedParts facts roots heads algebra rigid complete equation) :=
  if same : equation.2.1.code = equation.1.1.code then
    match found : underParts (S := S) equation.1.1.code equation.1.2.code equation.2.2.code with
    | some pieces =>
        (formNormal facts roots heads algebra rigid complete reducer declared choices fuel pieces
          (underParts_typed facts algebra _ _ _ Θ.formed found equation.1.2.typed
            (by have tr := equation.2.2.typed; rw [same] at tr; exact tr))).map
          (finishUnder facts roots heads algebra rigid complete equation same found)
    | none => none
  else none

/-- **The decomposition between spines of one local, at normal annotations.** -/
def spineNormal (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    Option (WeighedParts facts roots heads algebra rigid complete equation) :=
  if same : equation.2.1.code = equation.1.1.code then
    match found : dependentUnder [] equation.1.1.code equation.1.2.code equation.2.2.code with
    | some pieces =>
        (formNormal facts roots heads algebra rigid complete reducer declared choices fuel pieces
          (dependentUnder_typed facts [] _ _ _ Θ.formed (LocalTypes.nil _) found equation.1.2.typed
            (by have tr := equation.2.2.typed; rw [same] at tr; exact tr))).map
          (finishSpine facts roots heads algebra rigid complete equation same found)
    | none => none
  else none

/-- Finish the decomposition between spines of one local read along the reducts of the instantiated types. -/
def finishArgs {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (same : equation.2.1.code = equation.1.1.code)
    {pieces : List (Piece Head Θ.arity)}
    (read : DepRel S.R [] equation.1.1.code equation.1.2.code equation.2.2.code pieces)
    (store : PieceStore facts roots heads algebra rigid complete pieces) :
    WeighedParts facts roots heads algebra rigid complete equation :=
  ⟨⟨store.val, fun {Δ} σ => by
      have tl := equation.1.2.typed.substitute σ.typed
      have tr := equation.2.2.typed.substitute σ.typed
      rw [same] at tr
      have moved := read.subst σ.substitution (fun _ _ _ small => absurd small (Nat.not_lt_zero _))
        (Nat.zero_le _)
      rw [List.map_nil] at moved
      have exactly := moved.exact facts roots heads algebra complete Δ.formed (LocalTypes.nil _) tl tr
      rw [solves_raw, same, store.property.1 σ]
      constructor
      · rintro ⟨_, held⟩ piece member
        exact exactly.mp held _ (List.mem_map.mpr ⟨piece, member, rfl⟩)
      · intro held
        refine ⟨(Typed.isType tl Δ.formed).refl, exactly.mpr fun piece member => ?_⟩
        obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
        exact held original inside⟩, by
    have tr := equation.2.2.typed
    rw [same] at tr
    obtain ⟨w, wl, wr, weighs, ⟨v, nv, wv⟩, ⟨v', nv', wv'⟩, total⟩ :=
      read.weight facts roots heads algebra rigid complete Θ.formed (LocalTypes.nil _) equation.1.2.typed tr
    have left := sideWeight_eq facts roots heads algebra rigid complete equation.1 nv
    have right := sideWeight_eq facts roots heads algebra rigid complete equation.2 (by rw [same]; exact nv')
    change storeWeight facts roots heads algebra rigid complete store.val <
      sideWeight facts roots heads algebra rigid complete equation.1 +
        sideWeight facts roots heads algebra rigid complete equation.2
    rw [store.property.2 w weighs, left, right]
    omega⟩

/-- **The decomposition between spines of one local along the reducts of the instantiated types**, at normal
annotations. -/
def argsNormal (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    Option (WeighedParts facts roots heads algebra rigid complete equation) :=
  if same : equation.2.1.code = equation.1.1.code then
    (readArgs reducer fuel equation.1.1.code equation.1.2.code equation.2.2.code).bind fun read =>
      (formNormal facts roots heads algebra rigid complete reducer declared choices fuel read.val
        (read.property.typed facts roots heads Θ.formed (LocalTypes.nil _) equation.1.2.typed
          (by have tr := equation.2.2.typed; rw [same] at tr; exact tr))).map
        (finishArgs facts roots heads algebra rigid complete equation same read.property)
  else none

/-- Any decomposition at normal annotations: under abstractions, between spines of one local, or between spines of
one local along the reducts of the instantiated types. -/
def normalWeighed (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    Option (WeighedParts facts roots heads algebra rigid complete equation) :=
  (underNormal facts roots heads algebra rigid complete reducer declared choices fuel equation).or
    ((spineNormal facts roots heads algebra rigid complete reducer declared choices fuel equation).or
      (argsNormal facts roots heads algebra rigid complete reducer declared choices fuel equation))

/-- **Decompose the first equation that decomposes at normal annotations.** -/
def decomposeNormal (fuel : Nat) {Θ : Context S.R} :
    (problem : EquationStore (TotalTerm Θ)) → Option (Decomposed facts roots heads algebra rigid complete problem)
  | [] => none
  | equation :: rest => decomposeStep facts roots heads algebra rigid complete equation rest
      (normalWeighed facts roots heads algebra rigid complete reducer declared choices fuel equation,
        decomposeNormal fuel rest)

/-- A committed decomposition as a round. -/
def decomposedRound {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} :
    Option (Decomposed facts roots heads algebra rigid complete problem) →
      Round S.levels (weightRank facts roots heads algebra rigid complete) problem
  | some found => .progress ((Update.pending S.levels found.val).rephrase found.property.1)
      (below_of_weight facts roots heads algebra rigid complete found.property.2)
  | none => .stuck

/-- **The decomposition round at normal annotations.** -/
def normalRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  decomposedRound facts roots heads algebra rigid complete
    (decomposeNormal facts roots heads algebra rigid complete reducer declared choices fuel problem)

/-! ### The codes of the decompositions -/

/-- **Formed related pieces are related to the pieces.** -/
theorem formRelated_codes (fuel : Nat) {Θ : Context S.R} {pieces : List (Piece Head Θ.arity)}
    (related : RelatedPieces pieces) {store : PieceStore facts roots heads algebra rigid complete pieces}
    (formed : formRelated facts roots heads algebra rigid complete reducer declared choices fuel related = some store) :
    List.Forall₂ (fun e p => PieceRelated S.R Θ.raw (codePiece e) p) store.val pieces := by
  obtain ⟨inner, computed, rfl⟩ := Option.map_eq_some_iff.mp formed
  have codes := formPieces_codes facts roots heads algebra rigid complete declared choices reducer fuel related.val
    related.property.1 computed
  have relatedCodes := related.property.2
  rw [← codes] at relatedCodes
  exact forall₂_of_map relatedCodes

theorem underNormal_codes (fuel : Nat) {Θ : Context S.R} {equation : Equation (TotalTerm Θ)}
    {weighed : WeighedParts facts roots heads algebra rigid complete equation}
    (found : underNormal facts roots heads algebra rigid complete reducer declared choices fuel equation =
      some weighed) :
    ∃ pieces, underParts (S := S) equation.1.1.code equation.1.2.code equation.2.2.code = some pieces ∧
      List.Forall₂ (fun e p => PieceRelated S.R Θ.raw (codePiece e) p) weighed.val.val pieces := by
  unfold underNormal at found
  split at found
  · split at found
    · rename_i pieces computed
      obtain ⟨store, formed, rfl⟩ := Option.map_eq_some_iff.mp found
      exact ⟨pieces, computed, formRelated_codes facts roots heads algebra rigid complete reducer declared choices fuel
        _ formed⟩
    · cases found
  · cases found

theorem spineNormal_codes (fuel : Nat) {Θ : Context S.R} {equation : Equation (TotalTerm Θ)}
    {weighed : WeighedParts facts roots heads algebra rigid complete equation}
    (found : spineNormal facts roots heads algebra rigid complete reducer declared choices fuel equation =
      some weighed) :
    equation.2.1.code = equation.1.1.code ∧
      ∃ pieces, dependentUnder [] equation.1.1.code equation.1.2.code equation.2.2.code = some pieces ∧
        List.Forall₂ (fun e p => PieceRelated S.R Θ.raw (codePiece e) p) weighed.val.val pieces := by
  unfold spineNormal at found
  split at found
  · rename_i same
    split at found
    · rename_i pieces computed
      obtain ⟨store, formed, rfl⟩ := Option.map_eq_some_iff.mp found
      exact ⟨same, pieces, computed, formRelated_codes facts roots heads algebra rigid complete reducer declared choices
        fuel _ formed⟩
    · cases found
  · cases found

theorem argsNormal_codes (fuel : Nat) {Θ : Context S.R} {equation : Equation (TotalTerm Θ)}
    {weighed : WeighedParts facts roots heads algebra rigid complete equation}
    (found : argsNormal facts roots heads algebra rigid complete reducer declared choices fuel equation =
      some weighed) :
    equation.2.1.code = equation.1.1.code ∧
      ∃ pieces, DepRel S.R [] equation.1.1.code equation.1.2.code equation.2.2.code pieces ∧
        List.Forall₂ (fun e p => PieceRelated S.R Θ.raw (codePiece e) p) weighed.val.val pieces := by
  unfold argsNormal at found
  split at found
  · rename_i same
    obtain ⟨read, _, formedSome⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨store, formed, rfl⟩ := Option.map_eq_some_iff.mp formedSome
    exact ⟨same, read.val, read.property, formRelated_codes facts roots heads algebra rigid complete reducer
      declared choices fuel _ formed⟩
  · cases found

/-! ### Closure -/

include rigid in
omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
/-- **Replacing an equation by store equations related to its pieces keeps the Miller class**, when the pieces have
Miller reducts and are stratified among themselves. -/
theorem StratifiedMiller.splice_related (sn : StronglyNormalizing S.R) {Θ : Context S.R}
    {before after : EquationStore (TotalTerm Θ)} {equation : Equation (TotalTerm Θ)}
    (stratified : StratifiedMiller S.levels (before ++ equation :: after)) {pieces : List (Piece Head Θ.arity)}
    (reducts : MarkedReduct S.R (fun _ => true) equation.1.2.code → MarkedReduct S.R (fun _ => true) equation.2.2.code →
      ∀ piece ∈ pieces, MarkedReduct S.R (fun _ => true) piece.left ∧ MarkedReduct S.R (fun _ => true) piece.right)
    (internal : ∀ {Δ : Context S.R} (σ : Δ ⟶ Θ) (first last : List (Piece Head Θ.arity)) (piece : Piece Head Θ.arity),
      pieces = first ++ piece :: last → (∀ q ∈ first, (q.subst σ.substitution).Holds S.R Δ.raw) →
        TypeEq S.R Δ.raw (subst σ.substitution piece.leftType) (subst σ.substitution piece.rightType))
    (pieceEquations : EquationStore (TotalTerm Θ))
    (related : List.Forall₂ (fun e p => PieceRelated S.R Θ.raw (codePiece e) p) pieceEquations pieces)
    (exact : ∀ {Δ : Context S.R} (σ : Δ ⟶ Θ),
      (frames S.levels).Models σ pieceEquations ↔ (frames S.levels).Solves σ equation) :
    StratifiedMiller S.levels (before ++ (pieceEquations ++ after)) := by
  have empty := computation_empty rigid
  obtain ⟨leftReduct, rightReduct⟩ := side_reduct rigid sn (stratified before after equation rfl).1
  have pieceReducts := reducts leftReduct rightReduct
  refine StratifiedMiller.splice stratified exact ?_ ?_
  · intro e member
    obtain ⟨p, inPieces, sameLeft, sameRight, _, _⟩ := forall₂_mem related member
    obtain ⟨pieceLeft, pieceRight⟩ := pieceReducts p inPieces
    have left : e.1.2.code = p.left := sameLeft
    have right : e.2.2.code = p.right := sameRight
    exact sides_of_reducts empty (left ▸ pieceLeft) (right ▸ pieceRight)
  · intro first last e split Δ σ solved
    rw [models_append_iff] at solved
    rw [split] at related
    obtain ⟨first', p, last', rfl, before', _, _, leftEq, rightEq⟩ := forall₂_split first related
    have held : ∀ q ∈ first', (q.subst σ.substitution).Holds S.R Δ.raw := by
      intro q member
      obtain ⟨e', inFirst, rel⟩ := forall₂_mem_right before' member
      exact (PieceRelated.holds_iff rel σ.typed).mp ((solves_raw σ e').mp (solved.2 e' inFirst))
    have inner := internal σ first' last' p rfl held
    have l := ContextualDependentWeightPrune.typeEq_subst leftEq σ.typed
    have r := ContextualDependentWeightPrune.typeEq_subst rightEq σ.typed
    exact TypeEq.trans S.levels (TypeEq.trans S.levels l inner) (TypeEq.symm r)

include rigid in
omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
/-- **The same at every position of the permuted class.** -/
theorem PermutedMiller.splice_related (sn : StronglyNormalizing S.R) {Θ : Context S.R}
    {before after : EquationStore (TotalTerm Θ)} {equation : Equation (TotalTerm Θ)}
    (permuted : PermutedMiller S.levels (before ++ equation :: after)) {pieces : List (Piece Head Θ.arity)}
    (reducts : MarkedReduct S.R (fun _ => true) equation.1.2.code → MarkedReduct S.R (fun _ => true) equation.2.2.code →
      ∀ piece ∈ pieces, MarkedReduct S.R (fun _ => true) piece.left ∧ MarkedReduct S.R (fun _ => true) piece.right)
    (internal : ∀ {Δ : Context S.R} (σ : Δ ⟶ Θ) (first last : List (Piece Head Θ.arity)) (piece : Piece Head Θ.arity),
      pieces = first ++ piece :: last → (∀ q ∈ first, (q.subst σ.substitution).Holds S.R Δ.raw) →
        TypeEq S.R Δ.raw (subst σ.substitution piece.leftType) (subst σ.substitution piece.rightType))
    (pieceEquations : EquationStore (TotalTerm Θ))
    (related : List.Forall₂ (fun e p => PieceRelated S.R Θ.raw (codePiece e) p) pieceEquations pieces)
    (exact : ∀ {Δ : Context S.R} (σ : Δ ⟶ Θ),
      (frames S.levels).Models σ pieceEquations ↔ (frames S.levels).Solves σ equation) :
    PermutedMiller S.levels (before ++ (pieceEquations ++ after)) := by
  have front : PermutedMiller S.levels (equation :: (before ++ after)) := permuted.perm List.perm_middle
  have spliced := front.splice_of (pieces := pieceEquations) fun _ _ stratified =>
    StratifiedMiller.splice_related rigid sn stratified reducts internal pieceEquations related exact
  exact spliced.perm (by
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.perm_append_comm.append_right after)

/-- **The decomposition under abstractions at normal annotations keeps the class.** -/
theorem underNormal_keeps (sn : StronglyNormalizing S.R) (fuel : Nat) {Θ : Context S.R}
    (equation : Equation (TotalTerm Θ)) :
    WeighedKeeps facts roots heads algebra rigid complete
      (underNormal facts roots heads algebra rigid complete reducer declared choices fuel equation) := by
  intro weighed found before after permuted
  obtain ⟨pieces, computed, related⟩ := underNormal_codes facts roots heads algebra rigid complete reducer declared
    choices fuel found
  have empty := computation_empty rigid
  exact PermutedMiller.splice_related rigid sn permuted
    (fun leftReduct rightReduct => underParts_reducts empty _ _ _ (fun _ => true) computed leftReduct rightReduct)
    (fun {Δ} σ first last piece split held => underParts_internal facts algebra _ _ _ computed σ.substitution Δ.formed
      (equation.1.1.reindex σ).isType first last piece split held)
    weighed.val.val related fun σ => (weighed.val.property σ).symm

/-- **The decomposition between spines of one local at normal annotations keeps the class.** -/
theorem spineNormal_keeps (sn : StronglyNormalizing S.R) (fuel : Nat) {Θ : Context S.R}
    (equation : Equation (TotalTerm Θ)) :
    WeighedKeeps facts roots heads algebra rigid complete
      (spineNormal facts roots heads algebra rigid complete reducer declared choices fuel equation) := by
  intro weighed found before after permuted
  obtain ⟨same, pieces, computed, related⟩ := spineNormal_codes facts roots heads algebra rigid complete reducer
    declared choices fuel found
  have empty := computation_empty rigid
  refine PermutedMiller.splice_related rigid sn permuted
    (fun leftReduct rightReduct => dependentUnder_reducts empty [] _ _ _ (fun _ => true)
      (fun _ small => absurd small (Nat.not_lt_zero _)) computed leftReduct rightReduct)
    (fun {Δ} σ first last piece split held => ?_) weighed.val.val related fun σ => (weighed.val.property σ).symm
  have tl := equation.1.2.typed.substitute σ.typed
  have tr := equation.2.2.typed.substitute σ.typed
  rw [same] at tr
  have read := dependentUnder_subst [] _ _ _ computed σ.substitution
    (fun _ _ _ small => absurd small (Nat.not_lt_zero _)) (Nat.zero_le _)
  rw [List.map_nil] at read
  exact dependentUnder_internal facts [] _ _ _ Δ.formed (LocalTypes.nil _) read tl tr
    (first.map (Piece.subst σ.substitution)) (last.map (Piece.subst σ.substitution)) (piece.subst σ.substitution)
    (by rw [split]; simp)
    (fun q member => by
      obtain ⟨q', inFirst, rfl⟩ := List.mem_map.mp member
      exact held q' inFirst)

/-- **The decomposition between spines of one local along the reducts of the instantiated types keeps the
class.** -/
theorem argsNormal_keeps (sn : StronglyNormalizing S.R) (fuel : Nat) {Θ : Context S.R}
    (equation : Equation (TotalTerm Θ)) :
    WeighedKeeps facts roots heads algebra rigid complete
      (argsNormal facts roots heads algebra rigid complete reducer declared choices fuel equation) := by
  intro weighed found before after permuted
  obtain ⟨same, pieces, read, related⟩ := argsNormal_codes facts roots heads algebra rigid complete reducer
    declared choices fuel found
  have empty := computation_empty rigid
  refine PermutedMiller.splice_related rigid sn permuted
    (fun leftReduct rightReduct => read.reducts empty (fun _ => true)
      (fun _ small => absurd small (Nat.not_lt_zero _)) leftReduct rightReduct)
    (fun {Δ} σ first last piece split held => ?_) weighed.val.val related fun σ => (weighed.val.property σ).symm
  have tl := equation.1.2.typed.substitute σ.typed
  have tr := equation.2.2.typed.substitute σ.typed
  rw [same] at tr
  have moved := read.subst σ.substitution (fun _ _ _ small => absurd small (Nat.not_lt_zero _)) (Nat.zero_le _)
  rw [List.map_nil] at moved
  exact moved.internal facts roots heads Δ.formed (LocalTypes.nil _) tl tr
    (first.map (Piece.subst σ.substitution)) (last.map (Piece.subst σ.substitution)) (piece.subst σ.substitution)
    (by rw [split]; simp)
    (fun q member => by
      obtain ⟨q', inFirst, rfl⟩ := List.mem_map.mp member
      exact held q' inFirst)

theorem normalWeighed_keeps (sn : StronglyNormalizing S.R) (fuel : Nat) {Θ : Context S.R}
    (equation : Equation (TotalTerm Θ)) :
    WeighedKeeps facts roots heads algebra rigid complete
      (normalWeighed facts roots heads algebra rigid complete reducer declared choices fuel equation) :=
  (underNormal_keeps facts roots heads algebra rigid complete reducer declared choices sn fuel equation).or
    facts roots heads algebra rigid complete
    ((spineNormal_keeps facts roots heads algebra rigid complete reducer declared choices sn fuel equation).or
      facts roots heads algebra rigid complete
      (argsNormal_keeps facts roots heads algebra rigid complete reducer declared choices sn fuel equation))

theorem decomposeNormal_keeps (sn : StronglyNormalizing S.R) (fuel : Nat) {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ), PositionKeeps facts roots heads algebra rigid complete
      (decomposeNormal facts roots heads algebra rigid complete reducer declared choices fuel problem)
  | [] => fun _ found => by cases found
  | equation :: rest => decomposeStep_keeps facts roots heads algebra rigid complete equation rest
      (normalWeighed_keeps facts roots heads algebra rigid complete reducer declared choices sn fuel equation)
      (decomposeNormal_keeps sn fuel rest)

/-- **The decomposition round at normal annotations keeps the class.** -/
theorem normalRound_keeps (sn : StronglyNormalizing S.R) (fuel : Nat) {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} (permuted : PermutedMiller S.levels problem)
    (update : Update S.levels problem)
    (smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
      (weightRank facts roots heads algebra rigid complete problem))
    (fired : normalRound facts roots heads algebra rigid complete reducer declared choices fuel problem =
      .progress update smaller) :
    PermutedMiller S.levels update.remaining := by
  unfold normalRound at fired
  cases computed : decomposeNormal facts roots heads algebra rigid complete reducer declared choices fuel problem with
  | none =>
      rw [computed] at fired
      cases fired
  | some found =>
      rw [computed] at fired
      cases fired
      exact decomposeNormal_keeps facts roots heads algebra rigid complete reducer declared choices sn fuel problem
        found computed [] permuted

/-! ### Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
theorem normalPiece_const {n : Nat} (piece : Piece Head n) :
    EventuallyConst fun fuel => normalPiece reducer fuel piece :=
  EventuallyConst.comp (fun pair : Tm Head n × Tm Head n => (⟨pair.1, piece.left, pair.2, piece.right⟩ : Piece Head n))
    (EventuallyConst.pair (normalCode_const reducer stable piece.leftType)
      (normalCode_const reducer stable piece.rightType))

include stable in
omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
theorem map_normalPiece_const {n : Nat} :
    ∀ pieces : List (Piece Head n), EventuallyConst fun fuel => pieces.map (normalPiece reducer fuel)
  | [] => EventuallyConst.const _
  | piece :: rest => EventuallyConst.comp (fun pair : Piece Head n × List (Piece Head n) => pair.1 :: pair.2)
      (EventuallyConst.pair (normalPiece_const reducer stable piece) (map_normalPiece_const rest))

include stable in
omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
theorem normalPieces_const {Θ : Context S.R} (pieces : List (Piece Head Θ.arity))
    (typed : ∀ piece ∈ pieces, piece.Typed S.R Θ.raw) :
    EventuallyConst fun fuel => normalPieces facts roots heads reducer fuel pieces typed :=
  EventuallyConst.of_injective (g := Subtype.val) Subtype.val_injective (map_normalPiece_const reducer stable pieces)

include stable in
theorem formNormal_const {Θ : Context S.R} (pieces : List (Piece Head Θ.arity))
    (typed : ∀ piece ∈ pieces, piece.Typed S.R Θ.raw) :
    EventuallyConst fun fuel =>
      formNormal facts roots heads algebra rigid complete reducer declared choices fuel pieces typed :=
  EventuallyConst.dep (h := fun fuel => normalPieces facts roots heads reducer fuel pieces typed)
    (k := fun fuel related => formRelated facts roots heads algebra rigid complete reducer declared choices fuel related)
    (normalPieces_const facts roots heads reducer stable pieces typed)
    (fun related => EventuallyConst.comp
      (Option.map (transferStore facts roots heads algebra rigid complete related.property.2))
      (formPieces_const facts roots heads algebra rigid complete declared choices reducer stable related.val
        related.property.1))

include stable in
theorem underNormal_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      underNormal facts roots heads algebra rigid complete reducer declared choices fuel equation := by
  unfold underNormal
  by_cases same : equation.2.1.code = equation.1.1.code
  · simp only [same, dite_true]
    split
    · rename_i pieces found
      exact EventuallyConst.comp _ (formNormal_const facts roots heads algebra rigid complete reducer declared choices
        stable pieces _)
    · exact EventuallyConst.const _
  · simp only [same, dite_false]
    exact EventuallyConst.const _

include stable in
theorem spineNormal_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      spineNormal facts roots heads algebra rigid complete reducer declared choices fuel equation := by
  unfold spineNormal
  by_cases same : equation.2.1.code = equation.1.1.code
  · simp only [same, dite_true]
    split
    · rename_i pieces found
      exact EventuallyConst.comp _ (formNormal_const facts roots heads algebra rigid complete reducer declared choices
        stable pieces _)
    · exact EventuallyConst.const _
  · simp only [same, dite_false]
    exact EventuallyConst.const _

include stable in
theorem argsNormal_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      argsNormal facts roots heads algebra rigid complete reducer declared choices fuel equation := by
  unfold argsNormal
  by_cases same : equation.2.1.code = equation.1.1.code
  · simp only [same, dite_true]
    exact EventuallyConst.dep
      (h := fun fuel => readArgs reducer fuel equation.1.1.code equation.1.2.code equation.2.2.code)
      (k := fun fuel found => found.bind fun read =>
        (formNormal facts roots heads algebra rigid complete reducer declared choices fuel read.val
          (read.property.typed facts roots heads Θ.formed (LocalTypes.nil _) equation.1.2.typed
            (by have tr := equation.2.2.typed; rw [same] at tr; exact tr))).map
          (finishArgs facts roots heads algebra rigid complete equation same read.property))
      (readArgs_const reducer stable _ _ _)
      (fun found => by
        cases found with
        | none => exact EventuallyConst.const _
        | some read =>
            simp only [Option.bind_some]
            exact EventuallyConst.comp _ (formNormal_const facts roots heads algebra rigid complete reducer declared
              choices stable read.val _))
  · simp only [same, dite_false]
    exact EventuallyConst.const _

include stable in
theorem decomposeNormal_const {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ), EventuallyConst fun fuel =>
      decomposeNormal facts roots heads algebra rigid complete reducer declared choices fuel problem
  | [] => EventuallyConst.const _
  | equation :: rest =>
      EventuallyConst.comp (decomposeStep facts roots heads algebra rigid complete equation rest)
        (EventuallyConst.pair
          (EventuallyConst.comp (fun triple : Option (WeighedParts facts roots heads algebra rigid complete equation) ×
              Option (WeighedParts facts roots heads algebra rigid complete equation) ×
              Option (WeighedParts facts roots heads algebra rigid complete equation) =>
                triple.1.or (triple.2.1.or triple.2.2))
            (EventuallyConst.pair
              (underNormal_const facts roots heads algebra rigid complete reducer declared choices stable equation)
              (EventuallyConst.pair
                (spineNormal_const facts roots heads algebra rigid complete reducer declared choices stable equation)
                (argsNormal_const facts roots heads algebra rigid complete reducer declared choices stable equation))))
          (decomposeNormal_const rest))

include stable in
theorem normalRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      normalRound facts roots heads algebra rigid complete reducer declared choices fuel problem :=
  EventuallyConst.comp (decomposedRound facts roots heads algebra rigid complete)
    (decomposeNormal_const facts roots heads algebra rigid complete reducer declared choices stable problem)

end Normal

/-! ## The piece family -/

section Rule

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)
  (strengthening : EqualStrengthening S.R)

/-- **The piece round**: the skeleton round; when it is stuck, the decomposition at normal annotations of the η-long
prepared store. -/
noncomputable def pieceRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  orElse (skeletonRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (liftCollapsed facts roots heads algebra rigid complete
      (longUpdate facts roots heads algebra reducer root rootComplete fuel problem)
      (longUpdate_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem)
      (normalRound facts roots heads algebra rigid complete reducer declared choices fuel
        (longUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining))

/-- **The piece family**, at the weight rank. -/
noncomputable def pieceFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := pieceRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening fuel

/-! ### Conservativity and readers -/

theorem pieceRound_eq_of_skeleton (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : skeletonRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem ≠ .stuck) :
    pieceRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem =
      skeletonRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem := by
  unfold pieceRound
  cases computed : skeletonRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem with
  | stuck => exact absurd computed moving
  | progress update smaller => rfl
  | refuted absent => rfl

/-- **Every run that the skeleton family decides, the piece family decides with the same outcome.** -/
theorem piece_run_of_skeleton (fuel rounds : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (decided : (run ((skeletonFamily facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening).solver fuel) problem rounds).Decided) :
    run ((pieceFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening).solver fuel) problem rounds =
      run ((skeletonFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening).solver fuel) problem rounds :=
  ContextualDependentAcceptance.drive_conservative (weightRank facts roots heads algebra rigid complete)
    (fun problem => skeletonRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (fun problem => pieceRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (fun _ moving => pieceRound_eq_of_skeleton facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening fuel moving)
    rounds _ decided

/-- **The piece reader**: the round moves wherever the decomposition at normal annotations reads the η-long prepared
store. -/
theorem pieceRound_not_stuck_of_normal (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (read : (decomposeNormal facts roots heads algebra rigid complete reducer declared choices fuel
      (longUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining).isSome) :
    pieceRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ≠ .stuck := by
  unfold pieceRound
  obtain ⟨found, computed⟩ := Option.isSome_iff_exists.mp read
  cases skeletonRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem with
  | stuck =>
      refine liftCollapsed_not_stuck facts roots heads algebra rigid complete _
        (longUpdate_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem) ?_
      unfold normalRound
      rw [computed]
      exact fun impossible => by cases impossible
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

/-- **The piece family's readers**: a reader of the skeleton family, or the decomposition at normal annotations of the
η-long prepared store. -/
def PieceReads (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  SkeletonReads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ∨
    (decomposeNormal facts roots heads algebra rigid complete reducer declared choices fuel
      (longUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining).isSome

theorem pieceRound_not_stuck_of_pieceReads (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (reads : PieceReads facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem) :
    pieceRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ≠ .stuck := by
  rcases reads with skeleton | normal
  · have moving := skeletonRound_not_stuck_of_skeletonReads facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening fuel skeleton
    rw [pieceRound_eq_of_skeleton facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel moving]
    exact moving
  · exact pieceRound_not_stuck_of_normal facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening fuel normal

/-! ### Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

theorem pieceRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (pieceRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem) =
      (roundView (skeletonRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening fuel problem)).or
        (liftView (longUpdate facts roots heads algebra reducer root rootComplete fuel problem)
          (roundView (normalRound facts roots heads algebra rigid complete reducer declared choices fuel
            (longUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining))) := by
  unfold pieceRound
  rw [roundView_orElse, liftCollapsed_view]

include stable in
/-- **The piece round is eventually constant on every store.** -/
theorem pieceRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => pieceRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => pieceRound_view facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening fuel problem) ?_
  exact EventuallyConst.comp (fun pair : Option (Option (Update S.levels problem)) ×
      Option (Option (Update S.levels problem)) => pair.1.or pair.2)
    (EventuallyConst.pair
      (EventuallyConst.comp roundView (skeletonRound_const facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening stable problem))
      (EventuallyConst.dep (h := fun fuel => longUpdate facts roots heads algebra reducer root rootComplete fuel problem)
        (k := fun fuel prepared => liftView prepared
          (roundView (normalRound facts roots heads algebra rigid complete reducer declared choices fuel
            prepared.remaining)))
        (longUpdate_const facts roots heads algebra reducer root rootComplete stable problem)
        (fun prepared => EventuallyConst.comp (fun round => liftView prepared (roundView round))
          (normalRound_const facts roots heads algebra rigid complete reducer declared choices stable
            prepared.remaining))))

include stable in
/-- **The piece family settles** on every class on which, from some budget on, its round is not stuck and keeps the
class. -/
noncomputable def pieceSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        pieceRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete strengthening larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          pieceRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete strengthening larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (pieceFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening) :=
  Settled.ofConst _ (fun problem => pieceRound_const facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening stable problem) holds eventual

/-! ### Closure -/

variable (sn : StronglyNormalizing S.R)
  (directed : ∀ (fuel : Nat) {n : Nat} (term : Tm Head n) (result : ExecutableReduction.Result S.R term),
    reducer fuel term = some result → ContextualDependentExecutableJoin.Star (R := S.R) term result.val)

include sn directed in
/-- **Closure of the piece round** at every budget. -/
theorem pieceRound_closure (fuel : Nat) :
    RoundKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      pieceRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem := by
  intro Θ problem update smaller permuted fired
  change orElse (skeletonRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (liftCollapsed facts roots heads algebra rigid complete
      (longUpdate facts roots heads algebra reducer root rootComplete fuel problem)
      (longUpdate_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem)
      (normalRound facts roots heads algebra rigid complete reducer declared choices fuel
        (longUpdate facts roots heads algebra reducer root rootComplete fuel problem).remaining)) =
      .progress update smaller at fired
  cases computed : skeletonRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem with
  | stuck =>
      rw [computed] at fired
      exact liftCollapsed_keeps facts roots heads algebra rigid complete (fun problem => PermutedMiller S.levels problem)
        (longUpdate facts roots heads algebra reducer root rootComplete fuel problem)
        (longUpdate_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem)
        (fun first firstSmaller inner => normalRound_keeps facts roots heads algebra rigid complete reducer declared
          choices sn fuel (longUpdate_keeps facts roots heads algebra rigid reducer root rootComplete sn fuel permuted)
          first firstSmaller inner) fired
  | progress first firstSmaller =>
      rw [computed] at fired
      cases fired
      exact skeletonRound_closure facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening sn directed fuel _ _ _ permuted computed
  | refuted absent =>
      rw [computed] at fired
      cases fired

include sn directed stable in
/-- **Acceptance for the piece family from firing**: on a strongly normalizing package without root computation whose
reducer returns reducts and is monotone in its budget, and where typed equality strengthens past an unused variable,
the family decides every store of the dynamic pattern fragment, with a principal answer or a certified refutation,
constant at every larger budget, as soon as its round is eventually not stuck on nonempty stores of the permuted
class. -/
theorem piece_decided_of_firing
    (firing : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller S.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger →
        pieceRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening larger problem ≠ .stuck)
    {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run ((pieceFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
        run ((pieceFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening).solver budget) problem budget ∧
      ((∃ state finished, run ((pieceFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
              .solved state finished ∧ (frames S.levels).Principal problem state.answer) ∨
        (∃ absent, run ((pieceFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete strengthening).solver larger) problem larger =
              .refuted absent)) :=
  (pieceSettledOfConst facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening stable (fun problem => PermutedMiller S.levels problem)
    (fun held nonempty => by
      obtain ⟨bound, fires⟩ := firing held nonempty
      exact ⟨bound, fun larger enough => ⟨fires larger enough, fun {update} {smaller} fired =>
        pieceRound_closure facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening sn directed larger _ update smaller held
          fired⟩⟩)).decided
    (permutedMiller_of_fragment inside)

end Rule

/-! ## The tower -/

open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls

/-- The piece family of the tower controls. -/
noncomputable def pieceTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  pieceFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening

/-- Readers of the tower's piece family at one budget. -/
abbrev TowerPieceReads (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  PieceReads (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening fuel problem

/-- **Acceptance for the tower's piece family from firing**, on every store of the dynamic pattern fragment. -/
theorem tower_piece_decided_of_firing
    (firing : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller setting.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger → pieceTower.round larger problem ≠ .stuck)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (pieceTower.solver larger) problem larger = run (pieceTower.solver budget) problem budget ∧
      ((∃ state finished, run (pieceTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (pieceTower.solver larger) problem larger = .refuted absent)) :=
  piece_decided_of_firing (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening
    ContextualDependentDecisiveFragment.Controls.stable tower_stronglyNormalizing tower_reducer_directed firing inside

/-- **Acceptance for the tower's piece family from eventual reading**, on every store of the dynamic pattern
fragment. -/
theorem tower_piece_decided_of_pieceReads
    (reads : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller setting.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger → TowerPieceReads larger problem)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (pieceTower.solver larger) problem larger = run (pieceTower.solver budget) problem budget ∧
      ((∃ state finished, run (pieceTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (pieceTower.solver larger) problem larger = .refuted absent)) :=
  tower_piece_decided_of_firing (fun permuted nonempty => by
      obtain ⟨bound, eventually⟩ := reads permuted nonempty
      exact ⟨bound, fun larger enough => pieceRound_not_stuck_of_pieceReads (S := setting) TowerModel.facts
        TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentPiSpine.Controls.rigid
        TowerModel.complete ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
        ContextualDependentInversion.Controls.reducer (fun _ => none)
        ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
        ContextualDependentGeneralPattern.DispatchControls.certifyNormal
        ContextualDependentNormalCheckingTower.head_typing_unique
        (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening larger
        (eventually larger enough)⟩)
    inside

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
