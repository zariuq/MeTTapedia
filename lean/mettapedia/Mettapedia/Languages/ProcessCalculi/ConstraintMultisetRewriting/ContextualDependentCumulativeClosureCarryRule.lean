import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosureCarryInPlace

/-!
# Closure of the cumulative round: carrying outcomes, and R86's in-place rule

Separation keeps the codes of a store (`separate_codes`), and the strengthened equations of a store with Miller sides
have Miller sides (`separate_sides`). A carried outcome lifts the answer past the newest declaration, keeps the
unstrengthened equations in front and rephrases along the separation, so it is shaped whenever the outcome on the
strengthened store is (`carry_shape`). By induction on the depth every depth of R86's in-place rule is shaped
(`inPlaceAt_shape`), and the in-place rule is stable (`inPlace_stable`).
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
open ContextualDependentInPlace (separate separation carry weakened_codes)

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

/-! ## Separation -/

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
theorem weakened_codePiece {Γ : Context S.R} (type : TypeOver Γ) {equation : Equation (TotalTerm (extend Γ type))}
    (left : {strong : TotalTerm Γ // Presentation.rename wk strong.1.code = equation.1.1.code ∧
      Presentation.rename wk strong.2.code = equation.1.2.code})
    (right : {strong : TotalTerm Γ // Presentation.rename wk strong.1.code = equation.2.1.code ∧
      Presentation.rename wk strong.2.code = equation.2.2.code}) :
    codePiece ((left.val.reindex (projectionHom Γ type)), (right.val.reindex (projectionHom Γ type))) =
      codePiece equation := by
  obtain ⟨leftType, leftTerm⟩ := weakened_codes type left
  obtain ⟨rightType, rightTerm⟩ := weakened_codes type right
  simp only [codePiece, leftType, leftTerm, rightType, rightTerm]

/-- **Separation keeps the codes of a store**, up to order. -/
theorem separate_codes (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ) :
    ∀ problem : EquationStore (TotalTerm (extend Γ type)),
      (problem.map codePiece).Perm
        (((separate facts roots heads algebra declared choices reducer fuel type problem).2 ++
          (frames S.levels).applyStore (projectionHom Γ type)
            (separate facts roots heads algebra declared choices reducer fuel type problem).1).map codePiece)
  | [] => by simp [separate, Interface.Frames.applyStore]
  | equation :: rest => by
      have ih := separate_codes fuel type rest
      simp only [separate]
      split
      · rename_i left right _ _
        change (codePiece equation :: rest.map codePiece).Perm
          (((separate facts roots heads algebra declared choices reducer fuel type rest).2 ++
            ((left.val.reindex (projectionHom Γ type)), (right.val.reindex (projectionHom Γ type))) ::
              (frames S.levels).applyStore (projectionHom Γ type)
                (separate facts roots heads algebra declared choices reducer fuel type rest).1).map codePiece)
        rw [List.map_append, List.map_cons, weakened_codePiece type left right]
        rw [List.map_append] at ih
        exact (ih.cons _).trans List.perm_middle.symm
      · exact ih.cons _

include rigid in
/-- **The strengthened equations of a store with Miller sides have Miller sides.** -/
theorem separate_sides (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat) {Γ : Context S.R}
    (type : TypeOver Γ) :
    ∀ problem : EquationStore (TotalTerm (extend Γ type)), (∀ equation ∈ problem, FragmentSidesMiller equation) →
      ∀ equation ∈ (separate facts roots heads algebra declared choices reducer fuel type problem).1,
        FragmentSidesMiller equation
  | [], _ => by simp [separate]
  | equation :: rest, sides => by
      have empty := computation_empty rigid
      have ih := separate_sides sn fuel type rest fun other member => sides other (List.mem_cons_of_mem _ member)
      simp only [separate]
      split
      · rename_i left right _ _
        intro strong member
        rcases List.mem_cons.mp member with rfl | inner
        · obtain ⟨leftReduct, rightReduct⟩ := side_reduct rigid sn (sides equation List.mem_cons_self)
          refine sides_of_reducts empty ?_ ?_
          · exact body_reduct rigid sn left.val.2 (by rw [left.property.2]) leftReduct
          · exact body_reduct rigid sn right.val.2 (by rw [right.property.2]) rightReduct
        · exact ih strong inner
      · exact ih

/-! ## Carrying -/

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
/-- **A carried outcome is shaped** when the outcome on the strengthened store is. -/
theorem carry_shape {Γ : Context S.R} (type : TypeOver Γ) {strong : EquationStore (TotalTerm Γ)}
    {problem weak : EquationStore (TotalTerm (extend Γ type))}
    (same : (frames S.levels).Equivalent problem (weak ++ (frames S.levels).applyStore (projectionHom Γ type) strong))
    (codes : (problem.map codePiece).Perm
      ((weak ++ (frames S.levels).applyStore (projectionHom Γ type) strong).map codePiece))
    (strongSides : (∀ equation ∈ problem, FragmentSidesMiller equation) →
      ∀ equation ∈ strong, FragmentSidesMiller equation)
    {found : Option (Found strong)} (shaped : SolvedShape found) : SolvedShape (found.map (carry type same)) := by
  intro update smaller fired sides
  obtain ⟨inner, computed, moved⟩ := Option.map_eq_some_iff.mp fired
  cases inner with
  | solved solved solvedSmaller =>
      cases moved
      exact ((((shaped solved solvedSmaller computed (strongSides sides)).lift type).keepLeft weak).rephrase same
        codes)
  | refuted absent => cases moved

include rigid in
/-- **Every depth of R86's in-place rule is shaped.** -/
theorem inPlaceAt_shape (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat) :
    ∀ (depth : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)),
      SolvedShape (ContextualDependentInPlace.inPlaceAt facts roots heads algebra declared choices reducer rigid
        complete root normalizes certifyNormal headTypingUnique fuel depth problem)
  | 0, _, problem => firstRule_shape facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique sn fuel problem
  | depth + 1, Θ, problem => by
      simp only [ContextualDependentInPlace.inPlaceAt]
      split
      · exact SolvedShape.none
      · rename_i view _
        exact SolvedShape.throughNewest view problem _ fun stored =>
          carry_shape view.type (separation facts roots heads algebra declared choices reducer fuel view.type
            stored).property
            (separate_codes facts roots heads algebra declared choices reducer fuel view.type stored)
            (separate_sides facts roots heads algebra rigid declared choices reducer sn fuel view.type stored)
            (inPlaceAt_shape sn fuel depth _)

include rigid in
theorem inPlaceSearch_shape (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    ∀ depths : List Nat, SolvedShape (ContextualDependentInPlace.inPlaceSearch facts roots heads algebra declared
      choices reducer rigid complete root normalizes certifyNormal headTypingUnique fuel problem depths)
  | [] => SolvedShape.none
  | depth :: rest => by
      intro update smaller fired
      simp only [ContextualDependentInPlace.inPlaceSearch] at fired
      split at fired
      · rename_i found computed
        cases fired
        exact inPlaceAt_shape facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique sn fuel depth problem update smaller computed
      · exact inPlaceSearch_shape sn fuel problem rest update smaller fired

include rigid in
/-- **R86's in-place rule is stable** on a strongly normalizing package. -/
theorem inPlace_stable (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat) :
    InPlaceStable facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique fuel :=
  fun _ parts => SolvedShape.stable rigid sn
    (inPlaceSearch_shape facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique sn fuel parts _)

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
