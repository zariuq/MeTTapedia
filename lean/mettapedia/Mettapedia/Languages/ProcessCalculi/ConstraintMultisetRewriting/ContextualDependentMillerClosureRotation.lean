import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentMillerClosureInPlace

/-!
# The stratified Miller class under rotation, then intersection

Every progress of the older intersection rule (rotation along a renaming isomorphism, then general intersection at the
new newest metavariable) drops the first equation under a pattern answer: the intersection's pattern answer, read
through the rotation's renaming, is a pattern answer (`PatternAnswer.comp`, the renaming a permutation), and the
rotated store is the store renamed, in its order (`headDrop_renamingIso`). So the class is closed under it
(`stratifiedMiller_olderIntersectRule`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentMillerClosure

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRank ContextualDependentIntersection ContextualDependentIntersectionGeneral
open ContextualDependentDynamicFragment ContextualDependentShortClosure ContextualDependentHereditary
open ContextualDependentPermutation

/-! ## Pattern answers read through a permutation -/

section Permutation

variable {Head : Type} {R : Rules Head}

/-- A left inverse of a map of a finite type to itself is a right inverse. -/
theorem right_inverse_of_left {n : Nat} (π π' : Fin n → Fin n) (left : ∀ i, π' (π i) = i) : ∀ t, π (π' t) = t := by
  have injective : Function.Injective π := fun i j same => by rw [← left i, ← left j, same]
  intro t
  obtain ⟨i, rfl⟩ := Finite.surjective_of_injective injective t
  rw [left]

theorem right_inverse_of_left' {n n' : Nat} (same : n' = n) (π : Fin n → Fin n') (π' : Fin n' → Fin n)
    (left : ∀ i, π' (π i) = i) : ∀ t, π (π' t) = t := by
  subst same
  exact right_inverse_of_left π π' left

/-- **A pattern answer read through a bijection of its source variables is a pattern answer.** -/
def PatternAnswer.comp {n n' m : Nat} {σ : Sub Head n' m}
    (answer : PatternAnswer R (bodyFlexible (o := n') 0) (bodyFlexible (o := m) 0) σ) (π : Fin n → Fin n')
    (π' : Fin n' → Fin n) (left : ∀ i, π' (π i) = i) (right : ∀ t, π (π' t) = t) :
    PatternAnswer R (bodyFlexible (o := n) 0) (bodyFlexible (o := m) 0) fun i => σ (π i) where
  target := π' answer.target
  flexibleTarget := rfl
  rename i hi := answer.rename (π i) fun same => hi (by rw [← same, left])
  injective := by
    intro i j hi hj same
    have := answer.injective _ _ _ _ same
    rw [← left i, ← left j, this]
  respects := fun _ _ => rfl
  others := fun i _ => answer.others (π i) _
  outerArity := answer.outerArity
  outer := answer.outer
  outerInjective := answer.outerInjective
  outerFlexible := fun _ => rfl
  value := answer.value
  solution := by
    change σ (π (π' answer.target)) = _
    rw [right]
    exact answer.solution
  valueMiller := answer.valueMiller
  valueNormal := answer.valueNormal

end Permutation

/-! ## Rotation, then a drop -/

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- Instantiating twice is instantiating by the composite. -/
theorem applyStore_comp {A B C : Context S.R} (σ : B ⟶ A) (τ : C ⟶ B) :
    ∀ store : EquationStore (TotalTerm A),
      (frames S.levels).applyStore τ ((frames S.levels).applyStore σ store) = (frames S.levels).applyStore (τ ≫ σ) store
  | [] => rfl
  | equation :: rest => by
      change ((equation.1.reindex σ).reindex τ, (equation.2.reindex σ).reindex τ) ::
          (frames S.levels).applyStore τ ((frames S.levels).applyStore σ rest) =
        (equation.1.reindex (τ ≫ σ), equation.2.reindex (τ ≫ σ)) :: (frames S.levels).applyStore (τ ≫ σ) rest
      rw [applyStore_comp σ τ rest]
      rw [show equation.1.reindex (τ ≫ σ) = (equation.1.reindex σ).reindex τ from
          (frames S.levels).act_comp τ σ equation.1,
        show equation.2.reindex (τ ≫ σ) = (equation.2.reindex σ).reindex τ from
          (frames S.levels).act_comp τ σ equation.2]

/-- **A drop under a pattern answer after a renaming isomorphism is a drop under a pattern answer.** -/
theorem headDrop_renamingIso {Θ : Context S.R} {Θ' : Context S.R} (same : Θ'.arity = Θ.arity)
    (problem : EquationStore (TotalTerm Θ)) (π : Ren Θ.arity Θ'.arity) (π' : Ren Θ'.arity Θ.arity)
    (forth : CtxRen Θ.raw Θ'.raw π) (back : CtxRen Θ'.raw Θ.raw π') (inverse : ∀ i, π' (π i) = i)
    (update : Update S.levels (ofRenamingIso S.levels problem π π' forth back inverse).remaining)
    (drops : HeadDrop (ofRenamingIso S.levels problem π π' forth back inverse).remaining update) :
    HeadDrop problem ((ofRenamingIso S.levels problem π π' forth back inverse).then update) := by
  obtain ⟨first', rest', σ', listed, answered, remaining, valid, ⟨answer⟩⟩ := drops
  cases problem with
  | nil => cases listed
  | cons first rest =>
      change (first.1.reindex (renamingHom π forth), first.2.reindex (renamingHom π forth)) ::
        (frames S.levels).applyStore (renamingHom π forth) rest = first' :: rest' at listed
      obtain ⟨firstSame, restSame⟩ := List.cons.inj listed
      subst firstSame restSame answered
      have permuted : PatternAnswer S.R (bodyFlexible (o := Θ.arity) 0) (bodyFlexible (o := update.target.arity) 0)
          (update.answer ≫ renamingHom π forth).substitution :=
        PatternAnswer.comp answer π π' inverse (right_inverse_of_left' same π π' inverse)
      refine ⟨first, rest, update.answer ≫ renamingHom π forth, rfl, rfl, ?_, ?_, ⟨permuted⟩⟩
      · change update.remaining = _
        rw [remaining]
        exact applyStore_comp (renamingHom π forth) update.answer rest
      · intro Δ τ
        refine (ContextualDependentInPlace.solves_of_codes τ ?_ ?_ ?_ ?_).mp (valid τ)
        · exact subst_subComp _ _ _
        · exact subst_subComp _ _ _
        · exact subst_subComp _ _ _
        · exact subst_subComp _ _ _

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
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

include rigid in
/-- **Every rotation, then intersection, drops the first equation under a pattern answer.** -/
theorem rotateIntersect_headDrop (fuel depth : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    {found : Progress facts roots heads algebra rigid complete problem}
    (fired : rotateIntersect facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel depth problem = some found) :
    HeadDrop problem found.val := by
  unfold rotateIntersect at fired
  split at fired
  · cases fired
  split at fired
  · cases fired
  split at fired
  · split at fired
    · split at fired
      · dsimp only at fired
        split at fired
        · rename_i progress computed
          cases fired
          have drops := generalIntersectRule_headDrop facts roots heads algebra rigid complete declared choices reducer
            root normalizes headTypingUnique fuel _ computed
          exact headDrop_renamingIso (by rfl) problem _ _ _ _ _ _ drops
        · cases fired
      · cases fired
    · cases fired
  · cases fired

include rigid in
theorem rotateIntersectSearch_headDrop (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    ∀ (depths : List Nat) {found : Progress facts roots heads algebra rigid complete problem},
      rotateIntersectSearch facts roots heads algebra rigid complete declared choices reducer root normalizes
        headTypingUnique fuel problem depths = some found → HeadDrop problem found.val
  | [], _, fired => by cases fired
  | depth :: rest, found, fired => by
      simp only [rotateIntersectSearch] at fired
      split at fired
      · rename_i progress computed
        cases fired
        exact rotateIntersect_headDrop facts roots heads algebra rigid complete declared choices reducer root
          normalizes headTypingUnique fuel depth problem computed
      · exact rotateIntersectSearch_headDrop fuel problem rest fired

include rigid in
/-- **The stratified Miller class is closed under every progress of the older intersection rule.** -/
theorem stratifiedMiller_olderIntersectRule (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (stratified : StratifiedMiller S.levels problem) (opened : OpenedNormal problem)
    {found : Progress facts roots heads algebra rigid complete problem}
    (fired : olderIntersectRule facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel problem = some found) :
    StratifiedMiller S.levels found.val.remaining :=
  stratifiedMiller_of_headDrop rigid stratified opened
    (rotateIntersectSearch_headDrop facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel problem _ fired)

end ContextualDependentMillerClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
