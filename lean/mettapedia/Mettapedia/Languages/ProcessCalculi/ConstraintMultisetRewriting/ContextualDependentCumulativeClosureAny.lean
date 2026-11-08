import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosureExpanded

/-!
# Closure of the cumulative round: R99's committed decomposition

R99's decomposition round commits to the first equation of the store that decomposes (`decomposeAny`): at a universe
(R94's `formerParts`), under abstractions (`underWeighed`), or between spines of one local (`spineWeighed`). The
decomposed store is the store with that equation replaced by its pieces (`decomposeAny_spec`), so the class is kept as
soon as every one of the three decompositions keeps it at every position (`decomposeAny_keeps`).

The first two read the pieces of `underParts`: R94's identity, binder and pair pieces are exactly the pieces of
`underParts` at a universe and at a Σ type (`formerParts_codes`), and the formed pieces of `underWeighed` have the
codes of `underParts` (`underWeighed_codes`). On a strongly normalizing package without root computation, an equation
with Miller sides has closed normal Miller reducts of both codes (`side_reduct`), and the pieces of `underParts` then
have such reducts too (`underParts_reducts`), whatever the reducts of the codes themselves; the pieces are stratified
among themselves (R116's `underParts_internal`), so the replacement keeps the permuted class
(`PermutedMiller.splice_underReducts`, `weighedParts_keeps`, `underWeighed_keeps`).
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
open ContextualDependentClosure
open ContextualDependentGeneralPattern (liftFlexible)

/-! ## Reducts of formers -/

section Reducts

variable {Head : Type} {R : Rules Head} (empty : R.computation = RootComputation.empty)
include empty

theorem star_pair_inv {n : Nat} {a b X : Tm Head n} (steps : Star (R := R) (.pair a b) X) :
    ∃ a' b', X = .pair a' b' ∧ Star (R := R) a a' ∧ Star (R := R) b b' := by
  induction steps with
  | refl => exact ⟨a, b, rfl, .refl, .refl⟩
  | tail _ step ih =>
      obtain ⟨a', b', rfl, first, second⟩ := ih
      cases step with
      | root impossible => exact False.elim (no_root empty impossible)
      | congPairFst inner => exact ⟨_, b', rfl, first.tail inner, second⟩
      | congPairSnd inner => exact ⟨a', _, rfl, first, second.tail inner⟩

theorem MarkedReduct.of_pi {n : Nat} {mark : Fin n → Bool} {B : Tm Head n} {C : Tm Head (n + 1)}
    (outer : MarkedReduct R mark (.pi B C)) : MarkedReduct R mark B ∧ MarkedReduct R (liftFlexible mark) C := by
  obtain ⟨X, toX, normalX, millerX⟩ := outer
  obtain ⟨B', C', rfl, toB, toC⟩ := star_pi_inv empty toX
  obtain ⟨normalB, normalC⟩ := (normal_pi_iff empty).mp normalX
  simp only [miller, Bool.and_eq_true] at millerX
  exact ⟨⟨B', toB, normalB, millerX.1⟩, ⟨C', toC, normalC, millerX.2⟩⟩

theorem MarkedReduct.of_sigma {n : Nat} {mark : Fin n → Bool} {B : Tm Head n} {C : Tm Head (n + 1)}
    (outer : MarkedReduct R mark (.sigma B C)) :
    MarkedReduct R mark B ∧ MarkedReduct R (liftFlexible mark) C := by
  obtain ⟨X, toX, normalX, millerX⟩ := outer
  obtain ⟨B', C', rfl, toB, toC⟩ := star_sigma_inv empty toX
  obtain ⟨normalB, normalC⟩ := (normal_sigma_iff empty).mp normalX
  simp only [miller, Bool.and_eq_true] at millerX
  exact ⟨⟨B', toB, normalB, millerX.1⟩, ⟨C', toC, normalC, millerX.2⟩⟩

theorem MarkedReduct.of_id {n : Nat} {mark : Fin n → Bool} {C a b : Tm Head n}
    (outer : MarkedReduct R mark (.id C a b)) :
    MarkedReduct R mark C ∧ MarkedReduct R mark a ∧ MarkedReduct R mark b := by
  obtain ⟨X, toX, normalX, millerX⟩ := outer
  obtain ⟨C', a', b', rfl, toC, toA, toB⟩ := star_id_inv empty toX
  obtain ⟨normalC, normalA, normalB⟩ := (normal_id_iff empty).mp normalX
  simp only [miller, Bool.and_eq_true] at millerX
  exact ⟨⟨C', toC, normalC, millerX.1.1⟩, ⟨a', toA, normalA, millerX.1.2⟩, ⟨b', toB, normalB, millerX.2⟩⟩

theorem MarkedReduct.of_pair {n : Nat} {mark : Fin n → Bool} {a b : Tm Head n}
    (outer : MarkedReduct R mark (.pair a b)) : MarkedReduct R mark a ∧ MarkedReduct R mark b := by
  obtain ⟨X, toX, normalX, millerX⟩ := outer
  obtain ⟨a', b', rfl, toA, toB⟩ := star_pair_inv empty toX
  obtain ⟨normalA, normalB⟩ := (normal_pair_iff empty).mp normalX
  simp only [miller, Bool.and_eq_true] at millerX
  exact ⟨⟨a', toA, normalA, millerX.1⟩, ⟨b', toB, normalB, millerX.2⟩⟩

/-- **The pieces of a former equation at a universe have Miller normal reducts** when the two formers do. -/
theorem baseParts_reducts {n : Nat} {u : Head} (mark : Fin n → Bool) {left right : Tm Head n}
    {pieces : List (Piece Head n)} (found : baseParts u left right = some pieces)
    (leftReduct : MarkedReduct R mark left) (rightReduct : MarkedReduct R mark right) :
    ∀ piece ∈ pieces, MarkedReduct R mark piece.left ∧ MarkedReduct R mark piece.right := by
  cases left with
  | pi B C =>
      cases right with
      | pi B' C' =>
          simp only [baseParts, Option.some.injEq] at found
          subst found
          obtain ⟨rB, rC⟩ := MarkedReduct.of_pi empty leftReduct
          obtain ⟨rB', rC'⟩ := MarkedReduct.of_pi empty rightReduct
          intro piece member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact ⟨rB, rB'⟩
          · exact ⟨MarkedReduct.lam empty rC, MarkedReduct.lam empty rC'⟩
      | _ => simp [baseParts] at found
  | sigma B C =>
      cases right with
      | sigma B' C' =>
          simp only [baseParts, Option.some.injEq] at found
          subst found
          obtain ⟨rB, rC⟩ := MarkedReduct.of_sigma empty leftReduct
          obtain ⟨rB', rC'⟩ := MarkedReduct.of_sigma empty rightReduct
          intro piece member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact ⟨rB, rB'⟩
          · exact ⟨MarkedReduct.lam empty rC, MarkedReduct.lam empty rC'⟩
      | _ => simp [baseParts] at found
  | id C a b =>
      cases right with
      | id C' a' b' =>
          simp only [baseParts, Option.some.injEq] at found
          subst found
          obtain ⟨rC, ra, rb⟩ := MarkedReduct.of_id empty leftReduct
          obtain ⟨rC', ra', rb'⟩ := MarkedReduct.of_id empty rightReduct
          intro piece member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact ⟨rC, rC'⟩
          · exact ⟨ra, ra'⟩
          · exact ⟨rb, rb'⟩
      | _ => simp [baseParts] at found
  | _ => simp [baseParts] at found

end Reducts

section Under

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L} [∀ head, Decidable (S.R.isUniverse head)]
variable (empty : S.R.computation = RootComputation.empty)
include empty

/-- **The pieces of formers under abstractions have Miller normal reducts** when the two sides do, at every marking,
whatever the reducts of the sides themselves. -/
theorem underParts_reducts : ∀ {n : Nat} (annotation left right : Tm Head n) {pieces : List (Piece Head n)}
    (mark : Fin n → Bool), underParts (S := S) annotation left right = some pieces →
    MarkedReduct S.R mark left → MarkedReduct S.R mark right →
    ∀ piece ∈ pieces, MarkedReduct S.R mark piece.left ∧ MarkedReduct S.R mark piece.right
  | _, .head u, left, right, pieces, mark, found, leftReduct, rightReduct => by
      obtain ⟨-, base⟩ := underParts_head found
      exact baseParts_reducts empty mark base leftReduct rightReduct
  | _, .pi D T, left, right, pieces, mark, found, leftReduct, rightReduct => by
      obtain ⟨l, r, inner, rfl, rfl, computed, rfl⟩ := underParts_pi_cases found
      intro piece member
      obtain ⟨original, inInner, rfl⟩ := List.mem_map.mp member
      obtain ⟨pl, pr⟩ := underParts_reducts T l r (liftFlexible mark) computed
        (MarkedReduct.of_lam empty leftReduct) (MarkedReduct.of_lam empty rightReduct) original inInner
      exact ⟨MarkedReduct.lam empty pl, MarkedReduct.lam empty pr⟩
  | _, .sigma A B, left, right, pieces, mark, found, leftReduct, rightReduct => by
      obtain ⟨a, b, a', b', rfl, rfl, rfl⟩ := underParts_sigma_cases found
      obtain ⟨ra, rb⟩ := MarkedReduct.of_pair empty leftReduct
      obtain ⟨ra', rb'⟩ := MarkedReduct.of_pair empty rightReduct
      intro piece member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ⟨ra, ra'⟩
      · exact ⟨rb, rb'⟩
  | _, .var _, _, _, _, _, found, _, _ | _, .const _, _, _, _, _, found, _, _
  | _, .id _ _ _, _, _, _, _, found, _, _ | _, .lam _, _, _, _, _, found, _, _
  | _, .app _ _, _, _, _, _, found, _, _ | _, .pair _ _, _, _, _, _, found, _, _
  | _, .fst _, _, _, _, _, found, _, _ | _, .snd _, _, _, _, _, found, _, _
  | _, .refl _, _, _, _, _, found, _, _ => by simp [underParts] at found

end Under

/-! ## Replacing an equation by the pieces of `underParts` -/

section Splice

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L} [∀ head, Decidable (S.R.isUniverse head)]

/-- **Replacing an equation between formers by its pieces keeps the Miller class** on a strongly normalizing package,
whatever the reducts of the equation's codes: R116's splice (`StratifiedMiller.splice_underParts`) without its
normality hypotheses. -/
theorem StratifiedMiller.splice_underReducts (rigid : ∀ name, S.roles name = .rigid)
    (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (facts : FormFacts S.R S.roles)
    (algebra : CumulativeAlgebra S.R) {Θ : Context S.R} {before after : EquationStore (TotalTerm Θ)}
    {equation : Equation (TotalTerm Θ)} (stratified : StratifiedMiller S.levels (before ++ equation :: after))
    {pieces : List (Piece Head Θ.arity)}
    (found : underParts (S := S) equation.1.1.code equation.1.2.code equation.2.2.code = some pieces)
    (pieceEquations : EquationStore (TotalTerm Θ)) (codes : pieceEquations.map codePiece = pieces)
    (exact : ∀ {Δ : Context S.R} (σ : Δ ⟶ Θ),
      (frames S.levels).Models σ pieceEquations ↔ (frames S.levels).Solves σ equation) :
    StratifiedMiller S.levels (before ++ (pieceEquations ++ after)) := by
  have empty := computation_empty rigid
  obtain ⟨leftReduct, rightReduct⟩ := side_reduct rigid sn (stratified before after equation rfl).1
  have reducts := underParts_reducts empty _ _ _ (fun _ => true) found leftReduct rightReduct
  refine StratifiedMiller.splice stratified exact ?_ ?_
  · intro piece member
    have inPieces : codePiece piece ∈ pieces := by
      rw [← codes]
      exact List.mem_map_of_mem member
    obtain ⟨pieceLeft, pieceRight⟩ := reducts _ inPieces
    exact sides_of_reducts empty pieceLeft pieceRight
  · intro first last piece split Δ σ solved
    rw [models_append_iff] at solved
    have pieceSplit : pieces = first.map codePiece ++ codePiece piece :: last.map codePiece := by
      rw [← codes, split]
      simp
    exact underParts_internal facts algebra _ _ _ found σ.substitution Δ.formed (equation.1.1.reindex σ).isType
      (first.map codePiece) (last.map codePiece) (codePiece piece) pieceSplit (fun q member => by
        obtain ⟨original, inFirst, rfl⟩ := List.mem_map.mp member
        exact (solves_raw σ original).mp (solved.2 original inFirst))

/-- **Replacing an equation between formers by its pieces keeps the permuted class** at every position. -/
theorem PermutedMiller.splice_underReducts (rigid : ∀ name, S.roles name = .rigid)
    (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (facts : FormFacts S.R S.roles)
    (algebra : CumulativeAlgebra S.R) {Θ : Context S.R} {before after : EquationStore (TotalTerm Θ)}
    {equation : Equation (TotalTerm Θ)} (permuted : PermutedMiller S.levels (before ++ equation :: after))
    {pieces : List (Piece Head Θ.arity)}
    (found : underParts (S := S) equation.1.1.code equation.1.2.code equation.2.2.code = some pieces)
    (pieceEquations : EquationStore (TotalTerm Θ)) (codes : pieceEquations.map codePiece = pieces)
    (exact : ∀ {Δ : Context S.R} (σ : Δ ⟶ Θ),
      (frames S.levels).Models σ pieceEquations ↔ (frames S.levels).Solves σ equation) :
    PermutedMiller S.levels (before ++ (pieceEquations ++ after)) := by
  have front : PermutedMiller S.levels (equation :: (before ++ after)) := permuted.perm List.perm_middle
  have spliced := front.splice_of (pieces := pieceEquations) fun _ _ stratified =>
    StratifiedMiller.splice_underReducts rigid sn facts algebra stratified found pieceEquations codes exact
  exact spliced.perm (by
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.perm_append_comm.append_right after)

end Splice

/-! ## The codes of the decompositions -/

section Codes

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
theorem formStep_some {Θ : Context S.R} (piece : Piece Head Θ.arity) {rest : List (Piece Head Θ.arity)}
    (typed : piece.Typed S.R Θ.raw)
    (triple : Option {type : TypeOver Θ // type.code = piece.leftType} ×
      Option {type : TypeOver Θ // type.code = piece.rightType} ×
      Option (PieceStore facts roots heads algebra rigid complete rest))
    {store : PieceStore facts roots heads algebra rigid complete (piece :: rest)}
    (formed : formStep facts roots heads algebra rigid complete piece typed triple = some store) :
    ∃ leftType rightType inner, triple = (some leftType, some rightType, some inner) ∧
      store = consPiece facts roots heads algebra rigid complete piece leftType rightType typed inner := by
  obtain ⟨_ | leftType, _ | rightType, _ | inner⟩ := triple <;> try cases formed
  exact ⟨leftType, rightType, inner, rfl, rfl⟩

/-- **Formed pieces have the codes of their pieces.** -/
theorem formPieces_codes (fuel : Nat) {Θ : Context S.R} :
    ∀ (pieces : List (Piece Head Θ.arity)) (typed : ∀ piece ∈ pieces, piece.Typed S.R Θ.raw)
      {store : PieceStore facts roots heads algebra rigid complete pieces},
      formPieces facts roots heads algebra rigid complete declared choices reducer fuel pieces typed = some store →
      store.val.map codePiece = pieces
  | [], _, store, formed => by
      simp only [formPieces, Option.some.injEq] at formed
      subst formed
      rfl
  | piece :: rest, typed, store, formed => by
      simp only [formPieces] at formed
      obtain ⟨leftType, rightType, inner, computed, rfl⟩ :=
        formStep_some facts roots heads algebra rigid complete piece _ _ formed
      simp only [Prod.mk.injEq] at computed
      change codePiece _ :: inner.val.map codePiece = piece :: rest
      rw [formPieces_codes fuel rest _ computed.2.2]
      congr 1
      change Piece.mk leftType.val.code piece.left rightType.val.code piece.right = piece
      rw [leftType.property, rightType.property]

/-- **The decomposition under abstractions has the codes of `underParts`.** -/
theorem underWeighed_codes (fuel : Nat) {Θ : Context S.R} {equation : Equation (TotalTerm Θ)}
    {weighed : WeighedParts facts roots heads algebra rigid complete equation}
    (found : underWeighed facts roots heads algebra rigid complete declared choices reducer fuel equation =
      some weighed) :
    underParts (S := S) equation.1.1.code equation.1.2.code equation.2.2.code =
      some (weighed.val.val.map codePiece) := by
  unfold underWeighed at found
  split at found
  · split at found
    · rename_i pieces computed
      obtain ⟨store, formed, rfl⟩ := Option.map_eq_some_iff.mp found
      refine computed.trans ?_
      exact congrArg some (formPieces_codes facts roots heads algebra rigid complete declared choices reducer fuel
        pieces _ formed).symm
    · cases found
  · cases found

omit [DecidableEq Head] [DecidableRel S.R.headEq] [DecidableRel S.R.cumulative] in
theorem baseParts_binder (isPi : Bool) {n : Nat} (u : Head) (A A' : Tm Head n) (B B' : Tm Head (n + 1)) :
    baseParts u (binder isPi A B) (binder isPi A' B') =
      some [⟨.head u, A, .head u, A'⟩, ⟨.pi A (.head u), .lam B, .pi A' (.head u), .lam B'⟩] := by
  cases isPi <;> rfl

/-- **R94's identity decomposition has the codes of `underParts`.** -/
theorem idParts_codes (fuel : Nat) {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} {parts : Parts equation}
    (found : idParts facts roots heads algebra complete declared choices reducer fuel equation = some parts) :
    underParts (S := S) equation.1.1.code equation.1.2.code equation.2.2.code = some (parts.val.map codePiece) := by
  unfold idParts at found
  split at found
  · cases found
  · rename_i shape _
    obtain ⟨carrier, -, found⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨carrier', -, rfl⟩ := Option.map_eq_some_iff.mp found
    rw [shape.annotation, shape.leftCode, shape.rightCode]
    simp only [underParts, if_pos shape.universal, baseParts, IdShape.parts, List.map_cons, List.map_nil, codePiece,
      carrier.property, carrier'.property, shape.annotation]

/-- **R94's binder decomposition has the codes of `underParts`.** -/
theorem binderParts_codes (fuel : Nat) {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} {parts : Parts equation}
    (found : binderParts facts roots heads algebra complete declared choices reducer fuel equation = some parts) :
    underParts (S := S) equation.1.1.code equation.1.2.code equation.2.2.code = some (parts.val.map codePiece) := by
  unfold binderParts at found
  split at found
  · cases found
  · rename_i shape _
    obtain ⟨family, -, found⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨family', -, rfl⟩ := Option.map_eq_some_iff.mp found
    rw [shape.annotation, shape.leftCode, shape.rightCode]
    simp only [underParts, if_pos shape.universal, baseParts_binder, BinderShape.parts, List.map_cons, List.map_nil,
      codePiece, family.property, family'.property, shape.annotation]

/-- **R94's pair decomposition has the codes of `underParts`.** -/
theorem pairParts_codes (fuel : Nat) {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} {parts : Parts equation}
    (found : pairParts facts roots heads algebra declared choices reducer fuel equation = some parts) :
    underParts (S := S) equation.1.1.code equation.1.2.code equation.2.2.code = some (parts.val.map codePiece) := by
  unfold pairParts at found
  split at found
  · cases found
  · rename_i shape _
    obtain ⟨domain, -, found⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨fibre, -, found⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨fibre', -, rfl⟩ := Option.map_eq_some_iff.mp found
    rw [shape.annotation, shape.leftCode, shape.rightCode]
    simp only [underParts, PairShape.parts, List.map_cons, List.map_nil, codePiece, domain.property, fibre.property,
      fibre'.property]

/-- **R94's former decomposition has the codes of `underParts`.** -/
theorem formerParts_codes (fuel : Nat) {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} {parts : Parts equation}
    (found : formerParts facts roots heads algebra complete declared choices reducer fuel equation = some parts) :
    underParts (S := S) equation.1.1.code equation.1.2.code equation.2.2.code = some (parts.val.map codePiece) := by
  unfold formerParts at found
  cases idFound : idParts facts roots heads algebra complete declared choices reducer fuel equation with
  | some found' =>
      rw [idFound, Option.some_or] at found
      cases found
      exact idParts_codes facts roots heads algebra complete declared choices reducer fuel idFound
  | none =>
      rw [idFound, Option.none_or] at found
      cases binderFound : binderParts facts roots heads algebra complete declared choices reducer fuel equation with
      | some found' =>
          rw [binderFound, Option.some_or] at found
          cases found
          exact binderParts_codes facts roots heads algebra complete declared choices reducer fuel binderFound
      | none =>
          rw [binderFound, Option.none_or] at found
          exact pairParts_codes facts roots heads algebra declared choices reducer fuel found

end Codes

/-! ## The committed decomposition -/

section Committed

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

/-- **A decomposition of one equation keeps the class at every position.** -/
def WeighedKeeps {Θ : Context S.R} {equation : Equation (TotalTerm Θ)}
    (found : Option (WeighedParts facts roots heads algebra rigid complete equation)) : Prop :=
  ∀ weighed, found = some weighed → ∀ before after : EquationStore (TotalTerm Θ),
    PermutedMiller S.levels (before ++ equation :: after) →
      PermutedMiller S.levels (before ++ (weighed.val.val ++ after))

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
theorem WeighedKeeps.or {Θ : Context S.R} {equation : Equation (TotalTerm Θ)}
    {first second : Option (WeighedParts facts roots heads algebra rigid complete equation)}
    (keepsFirst : WeighedKeeps facts roots heads algebra rigid complete first)
    (keepsSecond : WeighedKeeps facts roots heads algebra rigid complete second) :
    WeighedKeeps facts roots heads algebra rigid complete (first.or second) := by
  intro weighed found
  cases first with
  | some chosen => exact keepsFirst weighed found
  | none => exact keepsSecond weighed found

/-- **The committed decomposition replaces one equation by its pieces.** -/
theorem decomposeAny_spec (fuel : Nat) {Θ : Context S.R} :
    ∀ (problem : EquationStore (TotalTerm Θ)) {decomposed : Decomposed facts roots heads algebra rigid complete problem},
      decomposeAny facts roots heads algebra rigid complete declared choices reducer fuel problem = some decomposed →
      ∃ (before after : EquationStore (TotalTerm Θ)) (equation : Equation (TotalTerm Θ))
        (weighed : WeighedParts facts roots heads algebra rigid complete equation),
        problem = before ++ equation :: after ∧
        anyWeighed facts roots heads algebra rigid complete declared choices reducer fuel equation = some weighed ∧
        decomposed.val = before ++ (weighed.val.val ++ after)
  | [], _, found => by cases found
  | equation :: rest, decomposed, found => by
      simp only [decomposeAny] at found
      unfold decomposeStep at found
      dsimp only at found
      split at found
      · rename_i weighed computed
        cases found
        exact ⟨[], rest, equation, weighed, rfl, computed, rfl⟩
      · obtain ⟨inner, innerFound, rfl⟩ := Option.map_eq_some_iff.mp found
        obtain ⟨before, after, chosen, weighed, split, computed, value⟩ := decomposeAny_spec fuel rest innerFound
        refine ⟨equation :: before, after, chosen, weighed, by rw [split]; rfl, computed, ?_⟩
        change equation :: inner.val = _
        rw [value]
        rfl

/-- **The committed decomposition keeps the class** when each of its decompositions does. -/
theorem decomposeAny_keeps (fuel : Nat)
    (each : ∀ {Θ : Context S.R} (equation : Equation (TotalTerm Θ)),
      WeighedKeeps facts roots heads algebra rigid complete
        (anyWeighed facts roots heads algebra rigid complete declared choices reducer fuel equation))
    {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) (permuted : PermutedMiller S.levels problem) :
    DecomposedKeeps (fun problem => PermutedMiller S.levels problem) facts roots heads algebra rigid complete
      (decomposeAny facts roots heads algebra rigid complete declared choices reducer fuel problem) := by
  intro decomposed found
  obtain ⟨before, after, equation, weighed, rfl, computed, value⟩ :=
    decomposeAny_spec facts roots heads algebra rigid complete declared choices reducer fuel problem found
  show PermutedMiller S.levels decomposed.val
  rw [value]
  exact each equation weighed computed before after permuted

/-- **R94's former decomposition keeps the class** on a strongly normalizing package. -/
theorem weighedParts_keeps (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    WeighedKeeps facts roots heads algebra rigid complete
      (weighedParts facts roots heads algebra rigid complete declared choices reducer fuel equation) := by
  intro weighed found before after permuted
  have former : formerParts facts roots heads algebra complete declared choices reducer fuel equation =
      some weighed.val := by
    rw [← weighedParts_val facts roots heads algebra rigid complete declared choices reducer fuel equation, found]
    rfl
  exact PermutedMiller.splice_underReducts rigid sn facts algebra permuted
    (formerParts_codes facts roots heads algebra complete declared choices reducer fuel former) weighed.val.val rfl
    fun σ => (weighed.val.property σ).symm

/-- **The decomposition under abstractions keeps the class** on a strongly normalizing package. -/
theorem underWeighed_keeps (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    WeighedKeeps facts roots heads algebra rigid complete
      (underWeighed facts roots heads algebra rigid complete declared choices reducer fuel equation) := by
  intro weighed found before after permuted
  exact PermutedMiller.splice_underReducts rigid sn facts algebra permuted
    (underWeighed_codes facts roots heads algebra rigid complete declared choices reducer fuel found) weighed.val.val
    rfl fun σ => (weighed.val.property σ).symm

/-- **R99's committed decomposition keeps the class** on a strongly normalizing package, when the decomposition
between spines of one local does. -/
theorem decomposeAny_keeps_of_spine (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    (spine : ∀ {Θ : Context S.R} (equation : Equation (TotalTerm Θ)),
      WeighedKeeps facts roots heads algebra rigid complete
        (spineWeighed facts roots heads algebra rigid complete declared choices reducer fuel equation))
    {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) (permuted : PermutedMiller S.levels problem) :
    DecomposedKeeps (fun problem => PermutedMiller S.levels problem) facts roots heads algebra rigid complete
      (decomposeAny facts roots heads algebra rigid complete declared choices reducer fuel problem) :=
  decomposeAny_keeps facts roots heads algebra rigid complete declared choices reducer fuel
    (fun equation => (weighedParts_keeps facts roots heads algebra rigid complete declared choices reducer sn fuel
      equation).or facts roots heads algebra rigid complete
      ((underWeighed_keeps facts roots heads algebra rigid complete declared choices reducer sn fuel equation).or
        facts roots heads algebra rigid complete (spine equation)))
    problem permuted

end Committed

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
