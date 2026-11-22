import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFragmentDecisiveClash
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRankPrepared

/-!
# The ranked round with decomposition under abstractions

The pieces of `underParts` become store equations once their annotations are formed at the budget
(`formPieces`). The decomposition of one store equation under its abstractions (`underWeighed`) has
exactly the equation's solutions and weighs two less, so it is a committed step of the weight rank.

The **ranked abstraction round** is the ranked occurs round of the occurs check under abstractions,
with one more decomposition: when the full occurs round is stuck and the conversion scan removes
nothing, the first equation of the **prepared** store between rigid formers is decomposed at a universe
(R94's `formerParts`) or under its abstractions (`underWeighed`), and the decomposition is committed.
Preparation keeps the normal weight (`prepare_weight`), so the committed step lowers the weight rank of
the original store.
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
open ContextualDependentRank ContextualDependentOccursFull ContextualDependentDecisiveFragment
open ContextualDependentConversionBudget

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

/-! ## Pieces as store equations -/

/-- A store for a list of pieces: its solutions are those of the pieces, and its normal weight is
theirs. -/
abbrev PieceStore {Θ : Context S.R} (pieces : List (Piece Head Θ.arity)) :=
  {store : EquationStore (TotalTerm Θ) //
    (∀ {Δ : Context S.R} (σ : Δ ⟶ Θ), (frames S.levels).Models σ store ↔
      ∀ piece ∈ pieces, (piece.subst σ.substitution).Holds S.R Δ.raw) ∧
    ∀ w, PiecesWeigh S Θ.raw pieces w → storeWeight facts roots heads algebra rigid complete store = w}

include facts roots heads algebra complete in
/-- One more piece in front of a piece store. -/
def consPiece {Θ : Context S.R} (piece : Piece Head Θ.arity) {rest : List (Piece Head Θ.arity)}
    (leftType : {type : TypeOver Θ // type.code = piece.leftType})
    (rightType : {type : TypeOver Θ // type.code = piece.rightType}) (typed : piece.Typed S.R Θ.raw)
    (store : PieceStore facts roots heads algebra rigid complete rest) :
    PieceStore facts roots heads algebra rigid complete (piece :: rest) :=
  ⟨(⟨leftType.val, ⟨piece.left, by rw [leftType.property]; exact typed.1⟩⟩,
      ⟨rightType.val, ⟨piece.right, by rw [rightType.property]; exact typed.2⟩⟩) :: store.val,
    fun σ => by
      rw [models_cons, store.property.1 σ, List.forall_mem_cons, solves_raw]
      simp only [leftType.property, rightType.property, Piece.Holds, Piece.subst],
    fun w ⟨a, b, c, ⟨v, nv, wv⟩, ⟨v', nv', wv'⟩, others, total⟩ => by
      simp only [storeWeight, equationWeight]
      rw [sideWeight_mk facts roots heads algebra rigid complete _ _ _ leftType.property nv,
        sideWeight_mk facts roots heads algebra rigid complete _ _ _ rightType.property nv',
        store.property.2 c others]
      omega⟩

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (declared : DeclaredTypesFormed S.R) (choices : ExecutableChecking.HeadChoices S.R)
  (reducer : ExecutableReduction.Reducer S.R)

/-- One step of forming pieces: both annotations and the rest. -/
def formStep {Θ : Context S.R} (piece : Piece Head Θ.arity) {rest : List (Piece Head Θ.arity)}
    (typed : piece.Typed S.R Θ.raw)
    (triple : Option {type : TypeOver Θ // type.code = piece.leftType} ×
      Option {type : TypeOver Θ // type.code = piece.rightType} ×
      Option (PieceStore facts roots heads algebra rigid complete rest)) :
    Option (PieceStore facts roots heads algebra rigid complete (piece :: rest)) :=
  match triple with
  | (some leftType, some rightType, some store) =>
      some (consPiece facts roots heads algebra rigid complete piece leftType rightType typed store)
  | _ => none

/-- **Form the pieces as store equations**: every annotation is formed at the budget. -/
def formPieces (fuel : Nat) {Θ : Context S.R} :
    (pieces : List (Piece Head Θ.arity)) → (∀ piece ∈ pieces, piece.Typed S.R Θ.raw) →
      Option (PieceStore facts roots heads algebra rigid complete pieces)
  | [], _ => some ⟨[], fun _ => by simp [Frames.Models], fun w weighs => by
      simp only [PiecesWeigh] at weighs
      simp [storeWeight, weighs]⟩
  | piece :: rest, typed => formStep facts roots heads algebra rigid complete piece (typed piece List.mem_cons_self)
      (ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Θ piece.leftType,
        ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Θ piece.rightType,
        formPieces fuel rest fun other member => typed other (List.mem_cons_of_mem _ member))

/-! ## The decomposition of one equation under its abstractions -/

/-- Finish the decomposition of one equation from its pieces. -/
def finishUnder {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (same : equation.2.1.code = equation.1.1.code)
    {pieces : List (Piece Head Θ.arity)}
    (found : underParts (S := S) equation.1.1.code equation.1.2.code equation.2.2.code = some pieces)
    (store : PieceStore facts roots heads algebra rigid complete pieces) :
    WeighedParts facts roots heads algebra rigid complete equation :=
  ⟨⟨store.val, fun {Δ} σ => by
      have tl := equation.1.2.typed.substitute σ.typed
      have tr := equation.2.2.typed.substitute σ.typed
      rw [same] at tr
      have exact := underParts_exact facts roots heads algebra complete _ _ _ Δ.formed
        (underParts_subst _ _ _ found σ.substitution) tl tr
      rw [solves_raw, same, store.property.1 σ]
      constructor
      · rintro ⟨_, held⟩ piece member
        exact exact.mp held _ (List.mem_map.mpr ⟨piece, member, rfl⟩)
      · intro held
        refine ⟨(Typed.isType tl Δ.formed).refl, exact.mpr fun piece member => ?_⟩
        obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
        exact held original inside⟩, by
    have tr := equation.2.2.typed
    rw [same] at tr
    obtain ⟨w, wl, wr, weighs, ⟨v, nv, wv⟩, ⟨v', nv', wv'⟩, total⟩ :=
      underParts_weight facts roots heads algebra rigid complete _ _ _ Θ.formed found equation.1.2.typed tr
    have left := sideWeight_eq facts roots heads algebra rigid complete equation.1 nv
    have right := sideWeight_eq facts roots heads algebra rigid complete equation.2 (by rw [same]; exact nv')
    change storeWeight facts roots heads algebra rigid complete store.val <
      sideWeight facts roots heads algebra rigid complete equation.1 +
        sideWeight facts roots heads algebra rigid complete equation.2
    rw [store.property.2 w weighs, left, right]
    omega⟩

/-- Finish the decomposition of one equation between spines of one local. -/
def finishSpine {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (same : equation.2.1.code = equation.1.1.code)
    {pieces : List (Piece Head Θ.arity)}
    (found : dependentUnder [] equation.1.1.code equation.1.2.code equation.2.2.code = some pieces)
    (store : PieceStore facts roots heads algebra rigid complete pieces) :
    WeighedParts facts roots heads algebra rigid complete equation :=
  ⟨⟨store.val, fun {Δ} σ => by
      have tl := equation.1.2.typed.substitute σ.typed
      have tr := equation.2.2.typed.substitute σ.typed
      rw [same] at tr
      have read := dependentUnder_subst [] _ _ _ found σ.substitution
        (fun _ _ _ small => absurd small (Nat.not_lt_zero _)) (Nat.zero_le _)
      rw [List.map_nil] at read
      have exact := dependentUnder_exact facts roots heads algebra complete [] _ _ _ Δ.formed (LocalTypes.nil _) read
        tl tr
      rw [solves_raw, same, store.property.1 σ]
      constructor
      · rintro ⟨_, held⟩ piece member
        exact exact.mp held _ (List.mem_map.mpr ⟨piece, member, rfl⟩)
      · intro held
        refine ⟨(Typed.isType tl Δ.formed).refl, exact.mpr fun piece member => ?_⟩
        obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
        exact held original inside⟩, by
    have tr := equation.2.2.typed
    rw [same] at tr
    obtain ⟨w, wl, wr, weighs, ⟨v, nv, wv⟩, ⟨v', nv', wv'⟩, total⟩ :=
      dependentUnder_weight facts roots heads algebra rigid complete [] _ _ _ Θ.formed (LocalTypes.nil _) found
        equation.1.2.typed tr
    have left := sideWeight_eq facts roots heads algebra rigid complete equation.1 nv
    have right := sideWeight_eq facts roots heads algebra rigid complete equation.2 (by rw [same]; exact nv')
    change storeWeight facts roots heads algebra rigid complete store.val <
      sideWeight facts roots heads algebra rigid complete equation.1 +
        sideWeight facts roots heads algebra rigid complete equation.2
    rw [store.property.2 w weighs, left, right]
    omega⟩

/-- **The decomposition of one store equation under its abstractions**, with its weight. -/
def underWeighed (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    Option (WeighedParts facts roots heads algebra rigid complete equation) :=
  if same : equation.2.1.code = equation.1.1.code then
    match found : underParts (S := S) equation.1.1.code equation.1.2.code equation.2.2.code with
    | some pieces =>
        (formPieces facts roots heads algebra rigid complete declared choices reducer fuel pieces
          (underParts_typed facts algebra _ _ _ Θ.formed found equation.1.2.typed
            (by have tr := equation.2.2.typed; rw [same] at tr; exact tr))).map
          (finishUnder facts roots heads algebra rigid complete equation same found)
    | none => none
  else none

/-- **The decomposition of one store equation between spines of one local**, with its weight. -/
def spineWeighed (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    Option (WeighedParts facts roots heads algebra rigid complete equation) :=
  if same : equation.2.1.code = equation.1.1.code then
    match found : dependentUnder [] equation.1.1.code equation.1.2.code equation.2.2.code with
    | some pieces =>
        (formPieces facts roots heads algebra rigid complete declared choices reducer fuel pieces
          (dependentUnder_typed facts [] _ _ _ Θ.formed (LocalTypes.nil _) found equation.1.2.typed
            (by have tr := equation.2.2.typed; rw [same] at tr; exact tr))).map
          (finishSpine facts roots heads algebra rigid complete equation same found)
    | none => none
  else none

/-- Any decomposition: at a universe first, then formers under abstractions, then spines of a local. -/
def anyWeighed (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    Option (WeighedParts facts roots heads algebra rigid complete equation) :=
  (weighedParts facts roots heads algebra rigid complete declared choices reducer fuel equation).or
    ((underWeighed facts roots heads algebra rigid complete declared choices reducer fuel equation).or
      (spineWeighed facts roots heads algebra rigid complete declared choices reducer fuel equation))

/-- **Decompose the first decomposable equation**, at a universe or under abstractions. -/
def decomposeAny (fuel : Nat) {Θ : Context S.R} :
    (problem : EquationStore (TotalTerm Θ)) → Option (Decomposed facts roots heads algebra rigid complete problem)
  | [] => none
  | equation :: rest => decomposeStep facts roots heads algebra rigid complete equation rest
      (anyWeighed facts roots heads algebra rigid complete declared choices reducer fuel equation,
        decomposeAny fuel rest)

/-! ## The round -/

variable (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)

/-- The rest of a round: the conversion scan, then one committed decomposition of the prepared store,
which lowers the weight rank because preparation keeps the normal weight (`prepare_weight`). -/
def anyRest (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  if shorter : (Conversion.scan facts roots heads algebra reducer fuel problem).length < problem.length then
    .progress (conversion facts roots heads algebra reducer fuel problem)
      (below_of_weight facts roots heads algebra rigid complete
        (scan_weight_lt facts roots heads algebra rigid complete reducer fuel problem shorter))
  else
    match decomposeAny facts roots heads algebra rigid complete declared choices reducer fuel
        (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).remaining with
    | some found => .progress ((ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).then
          ((Update.pending S.levels found.val).rephrase found.property.1))
        (below_of_prepared facts roots heads algebra rigid complete root rootComplete fuel found.property.2)
    | none => .stuck

/-- The refutations read on a prepared store: the occurs check under abstractions, then rigid clashes
under abstractions. -/
def refutationOf {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (prepared : Update S.levels problem) :
    Option (PLift (¬ (frames S.levels).Solvable problem)) :=
  (underOf facts roots heads algebra rigid complete prepared).or
    (ContextualDependentFragmentDecisive.clashOf facts complete prepared)

/-- The refutations on the prepared store. -/
def refutedPrepared (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Option (PLift (¬ (frames S.levels).Solvable problem)) :=
  refutationOf facts roots heads algebra rigid complete
    (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem)

/-- **One ranked abstraction round**: the occurs check and rigid clashes under abstractions; then the full
occurs round, keeping its refutations and the progress that removes a declaration; otherwise the
conversion scan, then one committed decomposition at a universe or under abstractions. -/
def anyRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  match refutedPrepared facts roots heads algebra rigid complete root rootComplete fuel problem with
  | some absent => .refuted absent.down
  | none =>
      match occursFullRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete fuel problem with
      | .refuted absent => .refuted absent
      | .progress update _ =>
          if lower : update.target.arity < Θ.arity then
            .progress update (below_of_arity facts roots heads algebra rigid complete lower)
          else anyRest facts roots heads algebra rigid complete declared choices reducer root rootComplete fuel problem
      | .stuck => anyRest facts roots heads algebra rigid complete declared choices reducer root rootComplete fuel problem

/-- **The ranked abstraction family**, at the weight rank. -/
noncomputable def anyFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel

/-! ## Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
theorem formPieces_const {Θ : Context S.R} :
    ∀ (pieces : List (Piece Head Θ.arity)) (typed : ∀ piece ∈ pieces, piece.Typed S.R Θ.raw),
      EventuallyConst fun fuel =>
        formPieces facts roots heads algebra rigid complete declared choices reducer fuel pieces typed
  | [], _ => EventuallyConst.const _
  | piece :: rest, typed =>
      EventuallyConst.comp (formStep facts roots heads algebra rigid complete piece (typed piece List.mem_cons_self))
        (EventuallyConst.pair (formType_const facts roots heads algebra declared choices reducer stable piece.leftType)
          (EventuallyConst.pair (formType_const facts roots heads algebra declared choices reducer stable piece.rightType)
            (formPieces_const rest fun other member => typed other (List.mem_cons_of_mem _ member))))

include stable in
theorem underWeighed_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      underWeighed facts roots heads algebra rigid complete declared choices reducer fuel equation := by
  unfold underWeighed
  by_cases same : equation.2.1.code = equation.1.1.code
  · simp only [same, dite_true]
    split
    · rename_i pieces found
      exact EventuallyConst.comp _ (formPieces_const facts roots heads algebra rigid complete declared choices reducer
        stable pieces _)
    · exact EventuallyConst.const _
  · simp only [same, dite_false]
    exact EventuallyConst.const _

include stable in
theorem spineWeighed_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      spineWeighed facts roots heads algebra rigid complete declared choices reducer fuel equation := by
  unfold spineWeighed
  by_cases same : equation.2.1.code = equation.1.1.code
  · simp only [same, dite_true]
    split
    · rename_i pieces found
      exact EventuallyConst.comp _ (formPieces_const facts roots heads algebra rigid complete declared choices reducer
        stable pieces _)
    · exact EventuallyConst.const _
  · simp only [same, dite_false]
    exact EventuallyConst.const _

include stable in
theorem anyWeighed_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      anyWeighed facts roots heads algebra rigid complete declared choices reducer fuel equation :=
  EventuallyConst.comp (fun triple : Option (WeighedParts facts roots heads algebra rigid complete equation) ×
      Option (WeighedParts facts roots heads algebra rigid complete equation) ×
      Option (WeighedParts facts roots heads algebra rigid complete equation) => triple.1.or (triple.2.1.or triple.2.2))
    (EventuallyConst.pair
      (weighedParts_const facts roots heads algebra rigid complete declared choices reducer stable equation)
      (EventuallyConst.pair
        (underWeighed_const facts roots heads algebra rigid complete declared choices reducer stable equation)
        (spineWeighed_const facts roots heads algebra rigid complete declared choices reducer stable equation)))

include stable in
theorem decomposeAny_const {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ),
      EventuallyConst fun fuel =>
        decomposeAny facts roots heads algebra rigid complete declared choices reducer fuel problem
  | [] => EventuallyConst.const _
  | equation :: rest =>
      EventuallyConst.comp (decomposeStep facts roots heads algebra rigid complete equation rest)
        (EventuallyConst.pair
          (anyWeighed_const facts roots heads algebra rigid complete declared choices reducer stable equation)
          (decomposeAny_const rest))

/-- The view of the rest of a round, from a prepared store. -/
def preparedView {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) (prepared : Update S.levels problem)
    (scanned : EquationStore (TotalTerm Θ)) (converted : Update S.levels problem)
    (found : Option (Decomposed facts roots heads algebra rigid complete prepared.remaining)) :
    Option (Option (Update S.levels problem)) :=
  if scanned.length < problem.length then some (some converted)
  else found.map fun found => some (prepared.then ((Update.pending S.levels found.val).rephrase found.property.1))

theorem anyRest_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (anyRest facts roots heads algebra rigid complete declared choices reducer root rootComplete fuel problem) =
      preparedView facts roots heads algebra rigid complete problem
        (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem)
        (Conversion.scan facts roots heads algebra reducer fuel problem)
        (conversion facts roots heads algebra reducer fuel problem)
        (decomposeAny facts roots heads algebra rigid complete declared choices reducer fuel
          (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).remaining) := by
  unfold anyRest preparedView
  by_cases shorter : (Conversion.scan facts roots heads algebra reducer fuel problem).length < problem.length
  · rw [dif_pos shorter, if_pos shorter]
    rfl
  · rw [dif_neg shorter, if_neg shorter]
    cases decomposeAny facts roots heads algebra rigid complete declared choices reducer fuel
      (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).remaining <;> rfl

include stable in
theorem anyRest_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      anyRest facts roots heads algebra rigid complete declared choices reducer root rootComplete fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => anyRest_view facts roots heads algebra rigid complete declared choices
    reducer root rootComplete fuel problem) ?_
  exact EventuallyConst.dep (h := fun fuel => ContextualDependentNormalizing.prepare root rootComplete facts roots heads
      fuel problem)
    (k := fun fuel prepared => preparedView facts roots heads algebra rigid complete problem prepared
      (Conversion.scan facts roots heads algebra reducer fuel problem)
      (conversion facts roots heads algebra reducer fuel problem)
      (decomposeAny facts roots heads algebra rigid complete declared choices reducer fuel prepared.remaining))
    (prepare_const root rootComplete facts roots heads problem)
    (fun prepared => EventuallyConst.comp
      (fun triple => preparedView facts roots heads algebra rigid complete problem prepared triple.1 triple.2.1
        triple.2.2)
      (EventuallyConst.pair (scan_const facts roots heads algebra reducer stable problem)
        (EventuallyConst.pair (conversion_const facts roots heads algebra reducer stable problem)
          (decomposeAny_const facts roots heads algebra rigid complete declared choices reducer stable
            prepared.remaining))))

theorem anyRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem) =
      (fun pair : Bool × Option (Option (Update S.levels problem)) => if pair.1 then some none else pair.2)
        ((refutedPrepared facts roots heads algebra rigid complete root rootComplete fuel problem).isSome,
          rankedView (roundView (occursFullRound facts roots heads algebra rigid complete declared choices reducer root
              normalizes certifyNormal headTypingUnique rootComplete fuel problem))
            (roundView (anyRest facts roots heads algebra rigid complete declared choices reducer root rootComplete fuel
              problem))) := by
  unfold anyRound
  split
  · rename_i absent computed
    simp only [computed, Option.isSome_some, if_true, roundView]
  · rename_i computed
    simp only [computed, Option.isSome_none, Bool.false_eq_true, if_false]
    split
    · rename_i absent computed'
      simp only [computed', roundView, rankedView]
    · rename_i update smaller computed'
      by_cases lower : update.target.arity < Θ.arity
      · simp only [computed', roundView, rankedView, dif_pos lower, if_pos lower]
      · simp only [computed', roundView, rankedView, dif_neg lower, if_neg lower]
    · rename_i computed'
      simp only [computed', roundView, rankedView]

include stable in
/-- **The ranked abstraction round is eventually constant on every store.** -/
theorem anyRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => anyRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => anyRound_view facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete fuel problem) ?_
  exact EventuallyConst.comp
    (fun triple : Bool × Option (Option (Update S.levels problem)) × Option (Option (Update S.levels problem)) =>
      if triple.1 then some none else rankedView triple.2.1 triple.2.2)
    (EventuallyConst.pair
      (EventuallyConst.comp (fun prepared => (refutationOf facts roots heads algebra rigid complete prepared).isSome)
        (prepare_const root rootComplete facts roots heads problem))
      (EventuallyConst.pair
        (EventuallyConst.comp roundView (occursFullRound_const facts roots heads algebra rigid complete declared choices
          reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem))
        (EventuallyConst.comp roundView (anyRest_const facts roots heads algebra rigid complete declared choices reducer
          root rootComplete stable problem))))

include stable in
/-- **The ranked abstraction family settles** on every class of stores on which, at each nonempty store
and from some budget on, its round is not stuck and keeps every residual store in the class. -/
noncomputable def anySettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
            headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
              headTypingUnique rootComplete larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (anyFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => anyRound_const facts roots heads algebra rigid complete declared choices reducer
    root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

end ContextualDependentSpinesMany
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
