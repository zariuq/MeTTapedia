import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosureCarry

/-!
# Closure of the cumulative round: R86's in-place rule

R86's in-place rule (`ContextualDependentInPlace.inPlaceRule`) tries every depth below the newest declaration: at
depth `0` R76's first rule, at depth `d + 1` it separates the store at the newest declaration, solves the
strengthened equations at depth `d`, and carries the outcome back.

* R76's first rule is shaped on stores with Miller sides (`firstRule_shape`): its pattern searches are drops under
  reducing answers, and its pruning and exchange reindex the whole store along reducing answers.
* Separation keeps the codes (`separate_codes`): a strengthened equation weakened back has the original codes, and
  strengthened equations of a store with Miller sides have Miller sides (`separate_sides`).
* So a carried outcome is shaped when the outcome on the strengthened store is (`carry_shape`), every depth is
  shaped (`inPlaceAt_shape`), and the in-place rule is stable (`inPlace_stable`).
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
open ContextualDependentPiSpine ContextualDependentScope ContextualDependentGeneralPattern ContextualDependentHereditary

/-! ## Shaped outcomes -/

section Solved

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **Every solved outcome is shaped** on stores with Miller sides. -/
def SolvedShape {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (found : Option (Found problem)) : Prop :=
  ∀ update smaller, found = some (.solved update smaller) → (∀ equation ∈ problem, FragmentSidesMiller equation) →
    Shape update

theorem SolvedShape.stable (rigid : ∀ name, S.roles name = .rigid)
    (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} {found : Option (Found problem)} (shaped : SolvedShape found) :
    SolvedStable found :=
  fun update smaller fired before permuted =>
    (shaped update smaller fired fun _ member => permuted.sides_of_mem (List.mem_append_right _ member)).stable
      rigid sn before permuted

theorem SolvedShape.none {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} :
    SolvedShape (Option.none : Option (Found problem)) := fun _ _ fired => by cases fired

theorem SolvedShape.dite {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {c : Prop} {decided : Decidable c}
    {yes : c → Option (Found problem)} {no : ¬ c → Option (Found problem)} (shapedYes : ∀ h, SolvedShape (yes h))
    (shapedNo : ∀ h, SolvedShape (no h)) : SolvedShape (@dite _ c decided yes no) := by
  cases decided with
  | isTrue h => exact shapedYes h
  | isFalse h => exact shapedNo h

theorem solvedShape_keepLeft {Θ : Context S.R} {rest : EquationStore (TotalTerm Θ)} (equation : Equation (TotalTerm Θ))
    {found : Option (Found rest)} (shaped : SolvedShape found) : SolvedShape (found.map (Found.keepLeft equation)) := by
  intro update smaller fired sides
  obtain ⟨inner, computed, same⟩ := Option.map_eq_some_iff.mp fired
  cases inner with
  | solved moved movedSmaller =>
      cases same
      exact (shaped moved movedSmaller computed fun other member => sides other (List.mem_cons_of_mem _ member)).keepLeft
        [equation]
  | refuted absent => cases same

theorem SolvedShape.throughNewest {Θ : Context S.R} (view : Newest Θ) (problem : EquationStore (TotalTerm Θ))
    (solve : (stored : EquationStore (TotalTerm (extend view.base view.type))) → Option (Found stored))
    (shaped : ∀ stored, SolvedShape (solve stored)) : SolvedShape (throughNewest view problem solve) := by
  rcases view with ⟨base, type, same⟩
  subst same
  exact shaped problem

theorem SolvedShape.throughTwo {Θ : Context S.R} (outer : Newest Θ) (inner : Newest outer.base)
    (problem : EquationStore (TotalTerm Θ))
    (solve : {Γ₀ : Context S.R} → (older : TypeOver Γ₀) → (newer : TypeOver (extend Γ₀ older)) →
      (stored : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) → Option (Found stored))
    (shaped : ∀ {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
      (stored : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))), SolvedShape (solve older newer stored)) :
    SolvedShape (throughTwo outer inner problem solve) := by
  cases outer with
  | mk base newer same =>
      cases inner with
      | mk base₀ older same₀ =>
          change base = extend base₀ older at same₀
          subst same₀
          subst same
          exact shaped older newer problem

/-- **The residual store of a shaped update has Miller sides** when the original store has. -/
theorem Shape.sides (rigid : ∀ name, S.roles name = .rigid)
    (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} {update : Update S.levels problem} (shape : Shape update)
    (sides : ∀ equation ∈ problem, FragmentSidesMiller equation) :
    ∀ equation ∈ update.remaining, FragmentSidesMiller equation := by
  have empty := computation_empty rigid
  obtain ⟨valid, codes, _, good⟩ := shape
  intro residual member
  have inCodes : codePiece residual ∈ (update.remaining ++ valid).map codePiece :=
    List.mem_map_of_mem (List.mem_append_left _ member)
  obtain ⟨image, imageMember, same⟩ := List.mem_map.mp (codes.symm.subset inCodes)
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp imageMember
  obtain ⟨leftReduct, rightReduct⟩ := side_reduct rigid sn (sides original originalMember)
  have reindexed : FragmentSidesMiller (original.1.reindex update.answer, original.2.reindex update.answer) :=
    sides_of_reducts empty (good.closedPreserving empty _ leftReduct) (good.closedPreserving empty _ rightReduct)
  simp only [codePiece, ContextualDependentSpinesMany.Piece.mk.injEq] at same
  exact fragmentSidesMiller_of_codes rigid sn same.2.1 same.2.2.2 reindexed

end Solved

/-! ## R76's first rule is shaped -/

section First

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

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
include rigid in
theorem prune_shape {Γ : Context S.R} {type keptType : TypeOver Γ}
    {spine : ContextualDependentPiSpine.Spine type} {kept : ContextualDependentPiSpine.Spine keptType}
    (restriction : ContextualDependentPrune.Restriction spine kept)
    (problem : EquationStore (TotalTerm (extend Γ type))) :
    ∀ forced, Shape (ContextualDependentPrune.prune S.levels restriction problem forced) :=
  fun _ => shape_of_reindex rfl (.of_pattern (pruneAnswer (computation_empty rigid) restriction))

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
include rigid in
theorem exchange_shape {Γ : Context S.R} (first next : TypeOver Γ)
    (problem : EquationStore (TotalTerm (ContextualDependentParameterExchange.context first next))) :
    Shape (ContextualDependentPrune.exchange S.levels first next problem) := by
  have renames : ∀ i, (ContextualDependentParameterExchange.swap next first).substitution i = .var (swapRen i) := by
    intro i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
    · exact ContextualDependentParameterExchange.swap_zero next first
    · exact ContextualDependentParameterExchange.swap_one next first
    · exact ContextualDependentParameterExchange.swap_older next first i
  exact shape_of_reindex rfl
    (.of_pattern (PatternAnswer.ofRenaming (computation_empty rigid) swapRen swapRen_injective renames 0))

include rigid in
theorem patternRule_shape (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    SolvedShape (patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal fuel problem) :=
  fun update smaller fired sides => shape_of_drop
    (patternRule_drops facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
      sn fuel problem sides update smaller fired)

include rigid in
theorem searchStore_shape (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Γ : Context S.R} (type : TypeOver Γ) (problem : EquationStore (TotalTerm (extend Γ type))) :
    SolvedShape (searchStore rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal fuel type problem) :=
  fun update smaller fired sides => shape_of_drop
    (searchStore_drops facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
      sn fuel type problem sides update smaller fired)

include rigid in
theorem tryPrune_shape (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    {scopeType : TypeOver (extend (extend Γ₀ older) newer)} (scope : Spine scopeType)
    (active : Active scope.target) (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend (extend Γ₀ older) newer),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend (extend Γ₀ older) newer)))
    (spine : Spine newer) (recognized : Recognized spine scope active) :
    SolvedShape (tryPrune rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel older newer scope active equation view rest spine recognized) := by
  unfold tryPrune
  try dsimp only
  split <;> try exact SolvedShape.none
  split <;> try exact SolvedShape.none
  split <;> try exact SolvedShape.none
  split <;> try exact SolvedShape.none
  refine SolvedShape.dite (fun _ => ?_) (fun _ => SolvedShape.none)
  refine SolvedShape.dite (fun _ => ?_) (fun _ => SolvedShape.none)
  try dsimp only
  refine SolvedShape.dite (fun _ => ?_) (fun _ => SolvedShape.none)
  refine SolvedShape.dite (fun _ => ?_) (fun _ => SolvedShape.none)
  try dsimp only
  split <;> try exact SolvedShape.none
  split <;> try exact SolvedShape.none
  split <;> try exact SolvedShape.none
  split <;> try exact SolvedShape.none
  refine SolvedShape.dite (fun _ => ?_) (fun _ => SolvedShape.none)
  refine SolvedShape.dite (fun _ => ?_) (fun _ => SolvedShape.none)
  refine SolvedShape.dite (fun _ => ?_) (fun _ => SolvedShape.none)
  try dsimp only
  refine SolvedShape.dite (fun _ => ?_) (fun _ => SolvedShape.none)
  try dsimp only
  split
  · exact SolvedShape.none
  · rename_i solved solvedSmaller computed
    intro update smaller fired sides
    cases fired
    refine Shape.then (Shape.then (prune_shape rigid _ _ _) (exchange_shape rigid _ _ _)) ?_
    exact searchStore_shape facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal sn fuel _ _ _ _ computed
      (Shape.sides rigid sn (Shape.then (prune_shape rigid _ _ _) (exchange_shape rigid _ _ _)) sides)
  · exact fun _ _ fired => by cases fired

include rigid in
theorem pruneActive_shape (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    {scopeType : TypeOver (extend (extend Γ₀ older) newer)} (scope : Spine scopeType)
    (active : Active scope.target) (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend (extend Γ₀ older) newer),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) :
    SolvedShape (pruneActive rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel older newer scope active equation view rest) := by
  unfold pruneActive
  split <;> try exact SolvedShape.none
  split <;> try exact SolvedShape.none
  split <;> try exact SolvedShape.none
  exact tryPrune_shape facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
    headTypingUnique sn fuel older newer scope active equation view rest _ _

include rigid in
theorem pruneEquation_shape (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
    (rest : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) :
    SolvedShape (pruneEquation rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel older newer equation rest) := by
  intro update smaller fired
  unfold pruneEquation at fired
  split at fired
  · cases fired
  rename_i scope active view _
  dsimp only at fired
  split at fired
  · rename_i inner computed
    cases fired
    exact pruneActive_shape facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique sn fuel older newer scope active equation view rest update smaller computed
  · exact pruneActive_shape facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique sn fuel older newer scope ⟨active.type, active.right, active.left⟩ equation
      (fun solution => (view solution).trans (toScoped_swap scope active solution).symm) rest update smaller fired

include rigid in
theorem pruneSearch_shape (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older)) :
    ∀ problem : EquationStore (TotalTerm (extend (extend Γ₀ older) newer)),
      SolvedShape (pruneSearch rigid facts complete roots heads algebra declared choices reducer root normalizes
        certifyNormal headTypingUnique fuel older newer problem)
  | [] => fun _ _ fired => by cases fired
  | equation :: rest => by
      intro update smaller fired
      simp only [pruneSearch] at fired
      split at fired
      · rename_i found computed
        cases fired
        exact pruneEquation_shape facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique sn fuel older newer equation rest update smaller computed
      · exact solvedShape_keepLeft equation (pruneSearch_shape sn fuel older newer rest) update smaller fired

include rigid in
theorem pruneRule_shape (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    SolvedShape (pruneRule rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel problem) := by
  unfold pruneRule
  split
  · exact SolvedShape.none
  split
  · exact SolvedShape.none
  exact SolvedShape.throughTwo _ _ problem _ fun older newer stored =>
    pruneSearch_shape facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique sn fuel older newer stored

include rigid in
theorem exchangeAt_shape (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    (problem : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) :
    SolvedShape (exchangeAt rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal fuel older newer problem) := by
  cases problem with
  | nil => exact fun _ _ fired => by cases fired
  | cons equation rest =>
      intro update smaller fired sides
      unfold exchangeAt at fired
      cases inverted : ContextualDependentInversion.invert (withoutNewest Γ₀.arity) newer.code with
      | none =>
          rw [inverted] at fired
          cases fired
      | some code =>
          rw [inverted] at fired
          dsimp only at fired
          split at fired
          · cases fired
          · split at fired
            · rename_i same
              obtain ⟨sameCode, sameLevel⟩ := same
              have independent := TypeOver.ext sameCode sameLevel
              subst independent
              dsimp only at fired
              split at fired
              · cases fired
              · rename_i solved solvedSmaller computed
                cases fired
                refine Shape.then (exchange_shape rigid _ _ _) ?_
                exact searchStore_shape facts roots heads algebra rigid complete declared choices reducer root
                  normalizes certifyNormal sn fuel _ _ _ _ computed
                  (Shape.sides rigid sn (exchange_shape rigid _ _ _) sides)
              · cases fired
            · cases fired

include rigid in
theorem exchangeRule_shape (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    SolvedShape (exchangeRule rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal fuel problem) := by
  unfold exchangeRule
  split
  · exact SolvedShape.none
  split
  · exact SolvedShape.none
  exact SolvedShape.throughTwo _ _ problem _ fun older newer stored =>
    exchangeAt_shape facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal sn fuel older newer stored

include rigid in
/-- **R76's first rule is shaped** on stores with Miller sides. -/
theorem firstRule_shape (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    SolvedShape (ContextualDependentDecisiveFragment.firstRule rigid facts complete roots heads algebra declared
      choices reducer root normalizes certifyNormal headTypingUnique fuel problem) := by
  unfold ContextualDependentDecisiveFragment.firstRule
  split
  · rename_i found computed
    intro update smaller fired
    cases fired
    exact patternRule_shape facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal sn fuel problem update smaller computed
  · split
    · rename_i found computed
      intro update smaller fired
      cases fired
      exact pruneRule_shape facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique sn fuel problem update smaller computed
    · exact exchangeRule_shape facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal sn fuel problem

end First

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
