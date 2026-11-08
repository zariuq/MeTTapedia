import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosureSpine

/-!
# Closure of the cumulative round: projection spines, and committed searches in general

A committed search of R99's kind (`decomposeStep` over the store) keeps the class at every position as soon as its
decomposition of one equation does (`decomposeStep_keeps`): the decomposed equation's pieces replace it in place, and
the equations before it are carried along.

R99's decomposition of projections of spines (`projWeighed`) reads `λ z̄. π (x ā) ≐ λ z̄. π (x b̄)` for one projection
`π` and a local `x` (`projUnder`), with the argument pieces of the two spines. A normal Miller projection of a rigid
spine is a projection of a normal Miller spine (`MarkedReduct.of_project`), so the pieces have Miller normal reducts
(`projUnder_reducts`); they are stratified as the arguments of `x` are (`projUnder_internal`). So the decomposition
keeps the permuted class (`decomposeProjections_keeps`).
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
open ContextualDependentClosure ContextualDependentConstantHeadsProjections
open ContextualDependentGeneralPattern (liftFlexible)

/-! ## Committed searches -/

section Search

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

/-- **A committed search keeps the class at every position.** -/
def PositionKeeps {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (found : Option (Decomposed facts roots heads algebra rigid complete problem)) : Prop :=
  ∀ decomposed, found = some decomposed → ∀ before : EquationStore (TotalTerm Θ),
    PermutedMiller S.levels (before ++ problem) → PermutedMiller S.levels (before ++ decomposed.val)

/-- **One step of a committed search keeps the class** when its decomposition does and the search of the rest
does. -/
theorem decomposeStep_keeps {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (rest : EquationStore (TotalTerm Θ))
    {weighed : Option (WeighedParts facts roots heads algebra rigid complete equation)}
    {later : Option (Decomposed facts roots heads algebra rigid complete rest)}
    (here : WeighedKeeps facts roots heads algebra rigid complete weighed)
    (there : PositionKeeps facts roots heads algebra rigid complete later) :
    PositionKeeps facts roots heads algebra rigid complete
      (decomposeStep facts roots heads algebra rigid complete equation rest (weighed, later)) := by
  intro decomposed found before permuted
  unfold decomposeStep at found
  dsimp only at found
  cases weighed with
  | some chosen =>
      dsimp only at found
      cases found
      exact here chosen rfl before rest permuted
  | none =>
      dsimp only at found
      obtain ⟨inner, innerFound, rfl⟩ := Option.map_eq_some_iff.mp found
      have moved := there inner innerFound (before ++ [equation]) (by simpa using permuted)
      change PermutedMiller S.levels (before ++ equation :: inner.val)
      simpa using moved

theorem PositionKeeps.decomposed {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    {found : Option (Decomposed facts roots heads algebra rigid complete problem)}
    (keeps : PositionKeeps facts roots heads algebra rigid complete found)
    (permuted : PermutedMiller S.levels problem) :
    DecomposedKeeps (fun problem => PermutedMiller S.levels problem) facts roots heads algebra rigid complete found :=
  fun decomposed computed => keeps decomposed computed [] permuted

end Search

/-! ## Reducts of projections -/

section Reducts

variable {Head : Type} {R : Rules Head} (empty : R.computation = RootComputation.empty)
include empty

theorem MarkedReduct.of_project {n : Nat} {mark : Fin n → Bool} (first : Bool) {p : Tm Head n} (elim : Elim p)
    (outer : MarkedReduct R mark (project first p)) : MarkedReduct R mark p := by
  obtain ⟨X, toX, normalX, millerX⟩ := outer
  cases first with
  | true =>
      obtain ⟨p', rfl, toP, _⟩ := star_fst_inv empty elim toX
      obtain ⟨_, normalP⟩ := (normal_fst_iff empty).mp normalX
      simp only [miller, Bool.and_eq_true] at millerX
      exact ⟨p', toP, normalP, millerX.2⟩
  | false =>
      obtain ⟨p', rfl, toP, _⟩ := star_snd_inv empty elim toX
      obtain ⟨_, normalP⟩ := (normal_snd_iff empty).mp normalX
      simp only [miller, Bool.and_eq_true] at millerX
      exact ⟨p', toP, normalP, millerX.2⟩

end Reducts

section Pieces

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **The pieces of projections of spines of one local have Miller normal reducts** when the two sides do, the
locals rigid. -/
theorem projUnder_reducts (empty : S.R.computation = RootComputation.empty) :
    ∀ {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n) {pieces : List (Piece Head n)}
      (mark : Fin n → Bool), (∀ j : Fin n, j.val < locals.length → mark j = false) →
      projUnder locals annotation left right = some pieces →
      MarkedReduct S.R mark left → MarkedReduct S.R mark right →
      ∀ piece ∈ pieces, MarkedReduct S.R mark piece.left ∧ MarkedReduct S.R mark piece.right := by
  intro n locals annotation left right pieces mark localsRigid found leftReduct rightReduct
  rcases projUnder_cases found with ⟨D, T, l, r, inner, rfl, rfl, rfl, computed, rfl⟩ | base
  · have lifted : ∀ j : Fin (n + 1),
        j.val < (Presentation.rename wk D :: locals.map (Presentation.rename wk)).length →
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
    intro piece member
    obtain ⟨original, inInner, rfl⟩ := List.mem_map.mp member
    obtain ⟨pl, pr⟩ := projUnder_reducts empty _ T l r (liftFlexible mark) lifted computed
      (MarkedReduct.of_lam empty leftReduct) (MarkedReduct.of_lam empty rightReduct) original inInner
    exact ⟨MarkedReduct.lam empty pl, MarkedReduct.lam empty pr⟩
  · obtain ⟨first, l, r, rfl, rfl, inner⟩ := projBase_spec base
    obtain ⟨h, as, bs, T, _, rfl, rfl, small, _, _, read⟩ := dependentBase_spec inner
    obtain ⟨sameL, sameR⟩ := argParts_sides as bs read
    have rigidHead := localsRigid h small
    have spineL := MarkedReduct.of_project empty first (elim_appSpine as (Elim.var h)) leftReduct
    have spineR := MarkedReduct.of_project empty first (elim_appSpine bs (Elim.var h)) rightReduct
    intro piece member
    refine ⟨MarkedReduct.of_spine empty h rigidHead as spineL _ ?_,
      MarkedReduct.of_spine empty h rigidHead bs spineR _ ?_⟩
    · rw [← sameL]
      exact List.mem_map_of_mem member
    · rw [← sameR]
      exact List.mem_map_of_mem member

variable (facts : FormFacts S.R S.roles)
include facts

theorem projBase_internal {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {locals : List (Tm Head n)}
    (types : LocalTypes Γ locals) {C left right : Tm Head n} {pieces : List (Piece Head n)}
    (found : projBase locals C left right = some pieces) (tl : TypedEquality.Typed S.R Γ left C)
    (tr : TypedEquality.Typed S.R Γ right C) :
    ∀ (first last : List (Piece Head n)) (piece : Piece Head n), pieces = first ++ piece :: last →
      (∀ q ∈ first, q.Holds S.R Γ) → TypeEq S.R Γ piece.leftType piece.rightType := by
  have typed := projBase_typed facts formed types found tl tr
  obtain ⟨_, l, r, rfl, rfl, inner⟩ := projBase_spec found
  obtain ⟨h, as, bs, T, _, rfl, rfl, _, _, looked, read⟩ := dependentBase_spec inner
  have headType := types.head looked
  have th : TypedEquality.Typed S.R Γ (.var h) T := by
    have typedVar : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
    rwa [headType] at typedVar
  have isT := Typed.isType th formed
  exact argParts_internal facts formed as bs read isT.refl isT isT typed

/-- **The pieces of projections of spines of one local under abstractions are stratified among themselves.** -/
theorem projUnder_internal : ∀ {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n)
    {Γ : Ctx Head n} {pieces : List (Piece Head n)}, CtxFormed S.R Γ → LocalTypes Γ locals →
    projUnder locals annotation left right = some pieces →
    TypedEquality.Typed S.R Γ left annotation → TypedEquality.Typed S.R Γ right annotation →
    ∀ (first last : List (Piece Head n)) (piece : Piece Head n), pieces = first ++ piece :: last →
      (∀ q ∈ first, q.Holds S.R Γ) → TypeEq S.R Γ piece.leftType piece.rightType := by
  intro n locals annotation left right Γ pieces formed types found tl tr first last piece split held
  rcases projUnder_cases found with ⟨D, T, l, r, inner, rfl, rfl, rfl, computed, rfl⟩ | base
  · obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
    have isD : IsType S.R Γ D := ⟨u, hu, tD⟩
    have formedD := formed.snoc isD
    have tl' := Typed.lam_inv facts tl formed
    have tr' := Typed.lam_inv facts tr formed
    have typed := projUnder_typed facts _ T l r formedD (types.under D) computed tl' tr'
    obtain ⟨first', rest', innerSplit, rfl, mapped⟩ := List.map_eq_append_iff.mp split
    obtain ⟨piece', last', rfl, rfl, rfl⟩ := List.map_eq_cons_iff.mp mapped
    have held' : ∀ q ∈ first', q.Holds S.R (.snoc Γ D) := fun q member =>
      (Piece.holds_under facts formed isD (typed q (by rw [innerSplit]; exact List.mem_append_left _ member))).mp
        (held (q.under D) (List.mem_map.mpr ⟨q, member, rfl⟩))
    have below := projUnder_internal _ T l r formedD (types.under D) computed tl' tr' first' last' piece'
      innerSplit held'
    exact (ContextualDependentRigid.typeEq_pi_iff facts formed).mpr ⟨isD.refl, below⟩
  · exact projBase_internal facts formed types base tl tr first last piece split held

end Pieces

/-! ## The decomposition of projection spines -/

section Rule

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **Replacing an equation between projections of spines of one local by its pieces keeps the permuted class** on a
strongly normalizing package, at every position. -/
theorem PermutedMiller.splice_proj (rigid : ∀ name, S.roles name = .rigid)
    (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (facts : FormFacts S.R S.roles)
    {Θ : Context S.R} {before after : EquationStore (TotalTerm Θ)}
    {equation : Equation (TotalTerm Θ)} (permuted : PermutedMiller S.levels (before ++ equation :: after))
    (same : equation.2.1.code = equation.1.1.code) {pieces : List (Piece Head Θ.arity)}
    (found : projUnder [] equation.1.1.code equation.1.2.code equation.2.2.code = some pieces)
    (pieceEquations : EquationStore (TotalTerm Θ)) (codes : pieceEquations.map codePiece = pieces)
    (exact : ∀ {Δ : Context S.R} (σ : Δ ⟶ Θ),
      (frames S.levels).Models σ pieceEquations ↔ (frames S.levels).Solves σ equation) :
    PermutedMiller S.levels (before ++ (pieceEquations ++ after)) := by
  have empty := computation_empty rigid
  have front : PermutedMiller S.levels (equation :: (before ++ after)) := permuted.perm List.perm_middle
  have spliced := front.splice_of (pieces := pieceEquations) fun before' after' stratified => by
    obtain ⟨leftReduct, rightReduct⟩ := side_reduct rigid sn (stratified before' after' equation rfl).1
    have reducts := projUnder_reducts empty [] _ _ _ (fun _ => true)
      (fun _ small => absurd small (Nat.not_lt_zero _)) found leftReduct rightReduct
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
      have tl := equation.1.2.typed.substitute σ.typed
      have tr := equation.2.2.typed.substitute σ.typed
      rw [same] at tr
      have read := projUnder_subst [] _ _ _ found σ.substitution
        (fun _ _ _ small => absurd small (Nat.not_lt_zero _)) (Nat.zero_le _)
      rw [List.map_nil] at read
      exact projUnder_internal facts [] _ _ _ Δ.formed (LocalTypes.nil _) read tl tr
        ((first.map codePiece).map (Piece.subst σ.substitution))
        ((last.map codePiece).map (Piece.subst σ.substitution)) ((codePiece piece).subst σ.substitution)
        (by rw [pieceSplit]; simp)
        (fun q member => by
          obtain ⟨q', inFirst, rfl⟩ := List.mem_map.mp member
          obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inFirst
          exact (solves_raw σ original).mp (solved.2 original inOriginal))
  exact spliced.perm (by
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.perm_append_comm.append_right after)

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

theorem projWeighed_codes (fuel : Nat) {Θ : Context S.R} {equation : Equation (TotalTerm Θ)}
    {weighed : WeighedParts facts roots heads algebra rigid complete equation}
    (found : projWeighed facts roots heads algebra rigid complete declared choices reducer fuel equation =
      some weighed) :
    equation.2.1.code = equation.1.1.code ∧
      projUnder [] equation.1.1.code equation.1.2.code equation.2.2.code =
        some (weighed.val.val.map codePiece) := by
  unfold projWeighed at found
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

theorem projWeighed_keeps (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    WeighedKeeps facts roots heads algebra rigid complete
      (projWeighed facts roots heads algebra rigid complete declared choices reducer fuel equation) := by
  intro weighed found before after permuted
  obtain ⟨same, codes⟩ := projWeighed_codes facts roots heads algebra rigid complete declared choices reducer fuel
    found
  exact PermutedMiller.splice_proj rigid sn facts permuted same codes weighed.val.val rfl
    fun σ => (weighed.val.property σ).symm

theorem decomposeProjections_position (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ), PositionKeeps facts roots heads algebra rigid complete
      (decomposeProjections facts roots heads algebra rigid complete declared choices reducer fuel problem)
  | [] => fun _ found => by cases found
  | equation :: rest => by
      simp only [decomposeProjections]
      exact decomposeStep_keeps facts roots heads algebra rigid complete equation rest
        (projWeighed_keeps facts roots heads algebra rigid complete declared choices reducer sn fuel equation)
        (decomposeProjections_position sn fuel rest)

/-- **R99's decomposition of projection spines keeps the permuted class** on a strongly normalizing package. -/
theorem decomposeProjections_keeps (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) (permuted : PermutedMiller S.levels problem) :
    DecomposedKeeps (fun problem => PermutedMiller S.levels problem) facts roots heads algebra rigid complete
      (decomposeProjections facts roots heads algebra rigid complete declared choices reducer fuel problem) :=
  (decomposeProjections_position facts roots heads algebra rigid complete declared choices reducer sn fuel
    problem).decomposed facts roots heads algebra rigid complete permuted

end Rule

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
