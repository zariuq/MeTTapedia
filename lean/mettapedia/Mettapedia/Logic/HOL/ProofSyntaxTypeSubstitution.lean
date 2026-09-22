import Mettapedia.Logic.HOL.ProofSyntaxStructural
import Mettapedia.Logic.HOL.TypeSubstitutionDerivation

/-!
# Type substitution on retained HOL proofs

Substituting simple types transforms the supplied proof tree, not just its
proposition-valued admission. Every extensional HOL rule is retained, including
the exact hypothesis occurrence and ordered premises. Constants are interpreted
at their substituted types. This is an interpretation of HOL proofs; it does
not identify object-theory equality with the host's conversion judgment.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.ProofSyntax

universe u u' v v'

variable {Base : Type u} {Base' : Type u'}
  {Const : Ty Base → Type v} {Const' : Ty Base' → Type v'}

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Retype all payloads while keeping the supplied derivation and its selected
hypothesis occurrences. No proof search or choice of another derivation occurs. -/
def mapTypes
    (σ : Base → Ty Base')
    (constants : ∀ {A}, Const A → Const' (Ty.substitute σ A))
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
    ProofSyntax Const Δ φ →
      ProofSyntax Const' (Δ.map (HOL.mapTypes σ constants))
        (HOL.mapTypes σ constants φ)
  | .hyp occurrence => by
      exact castIndices rfl (by simp) (ProofSyntax.hyp (Const := Const')
        (Δ := Δ.map (HOL.mapTypes σ constants))
        ⟨occurrence.val, by simp⟩)
  | .topI => .topI
  | .botE proof => .botE (mapTypes σ constants proof)
  | .andI left right => .andI (mapTypes σ constants left) (mapTypes σ constants right)
  | .andEL proof => .andEL (mapTypes σ constants proof)
  | .andER proof => .andER (mapTypes σ constants proof)
  | .orIL proof => .orIL (mapTypes σ constants proof)
  | .orIR proof => .orIR (mapTypes σ constants proof)
  | .orE cases left right => .orE (mapTypes σ constants cases)
      (mapTypes σ constants left) (mapTypes σ constants right)
  | .impI proof => .impI (mapTypes σ constants proof)
  | .impE function argument => .impE (mapTypes σ constants function) (mapTypes σ constants argument)
  | .notI proof => .notI (mapTypes σ constants proof)
  | .notE negative positive => .notE (mapTypes σ constants negative) (mapTypes σ constants positive)
  | .allI proof => by
      exact .allI (castIndices (by
        simp only [Ty.substitute, weakenHyps, List.map_map,
          Function.comp_def, HOL.mapTypes_weaken]) rfl (mapTypes σ constants proof))
  | .allE term proof => by
      exact castIndices rfl (by simp only [HOL.mapTypes_instantiate])
        (ProofSyntax.allE (HOL.mapTypes σ constants term) (mapTypes σ constants proof))
  | .exI term proof => by
      apply ProofSyntax.exI (HOL.mapTypes σ constants term)
      exact castIndices rfl (by simp only [Ty.substitute, HOL.mapTypes_instantiate])
        (mapTypes σ constants proof)
  | .exE existential body => by
      exact .exE (mapTypes σ constants existential) (castIndices (by
        simp only [Ty.substitute, List.map_cons, weakenHyps, List.map_map,
          Function.comp_def, HOL.mapTypes_weaken])
        (by simp only [HOL.mapTypes_weaken]) (mapTypes σ constants body))
  | .eqRefl term => .eqRefl (HOL.mapTypes σ constants term)
  | .eqSymm proof => .eqSymm (mapTypes σ constants proof)
  | .eqTrans left right => .eqTrans (mapTypes σ constants left) (mapTypes σ constants right)
  | .eqPropI forward backward => .eqPropI (mapTypes σ constants forward) (mapTypes σ constants backward)
  | .eqPropEL proof => .eqPropEL (mapTypes σ constants proof)
  | .eqPropER proof => .eqPropER (mapTypes σ constants proof)
  | .eqApp term proof => .eqApp (HOL.mapTypes σ constants term) (mapTypes σ constants proof)
  | .eqAppArg term proof => .eqAppArg (HOL.mapTypes σ constants term) (mapTypes σ constants proof)
  | .eqLam proof => by
      exact .eqLam (castIndices (by
        simp only [Ty.substitute, weakenHyps,
          List.map_map, Function.comp_def, HOL.mapTypes_weaken]) rfl
          (mapTypes σ constants proof))
  | .funExt proof => by
      apply ProofSyntax.funExt
      exact castIndices rfl (by simp only [Ty.substitute, HOL.mapTypes,
        HOL.mapTypes_weaken, Var.mapTypes]) (mapTypes σ constants proof)
  | .beta term body => by
      exact castIndices rfl (by simp only [HOL.mapTypes, HOL.mapTypes_instantiate])
        (ProofSyntax.beta (HOL.mapTypes σ constants term) (HOL.mapTypes σ constants body))
  | .eta term => by
      exact castIndices rfl (by simp only [HOL.mapTypes, HOL.mapTypes_weaken, Var.mapTypes])
        (ProofSyntax.eta (HOL.mapTypes σ constants term))

/-- Erasing the transformed tree establishes the existing transported judgment. -/
theorem mapTypes_derivable
    (σ : Base → Ty Base')
    (constants : ∀ {A}, Const A → Const' (Ty.substitute σ A))
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (proof : ProofSyntax Const Δ φ) :
    ExtDerivation Const' (Δ.map (HOL.mapTypes σ constants))
      (HOL.mapTypes σ constants φ) :=
  (mapTypes σ constants proof).erase

private theorem observe_nodeCount_castIndices
    {Γ : Ctx Base} {Δ Δ' : List (Formula Const Γ)} {φ ψ : Formula Const Γ}
    (assumptions : Δ = Δ') (conclusion : φ = ψ)
    (proof : ProofSyntax Const Δ φ) :
    (castIndices assumptions conclusion proof).observe.nodeCount = proof.observe.nodeCount :=
  nodeCount_castIndices assumptions conclusion proof

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Retyping does not introduce, erase or duplicate proof steps. -/
theorem nodeCount_mapTypes
    (σ : Base → Ty Base')
    (constants : ∀ {A}, Const A → Const' (Ty.substitute σ A))
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (proof : ProofSyntax Const Δ φ) :
    (mapTypes σ constants proof).nodeCount = proof.nodeCount := by
  induction proof <;>
    simp only [mapTypes]
  all_goals try rw [nodeCount_castIndices]
  all_goals first
    | rfl
    | (change 1 + _ = 1 + _
       simp_all [nodeCount, Fin.sum_univ_succ, observe_nodeCount_castIndices])

set_option backward.isDefEq.respectTransparency false in
/-- Each rule tag, including the selected hypothesis occurrence, survives
specialization. The recursive definition retains its ordered premises too. -/
theorem rootObservation_mapTypes
    (σ : Base → Ty Base')
    (constants : ∀ {A}, Const A → Const' (Ty.substitute σ A))
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (proof : ProofSyntax Const Δ φ) :
    (mapTypes σ constants proof).rootObservation = proof.rootObservation := by
  cases proof <;> simp only [mapTypes]
  all_goals try rw [rootObservation_castIndices]
  all_goals rfl

namespace TypeSubstitutionControls

variable (σ : Base → Ty Base')
    (constants : ∀ {A}, Const A → Const' (Ty.substitute σ A))
    {Γ : Ctx Base} (φ : Formula Const Γ)

/-- Specializing even to the same target types does not merge two different
assumption occurrences of an identical formula. -/
theorem duplicate_occurrences_remain_distinct :
    mapTypes σ constants (Controls.firstOccurrence φ) ≠
      mapTypes σ constants (Controls.secondOccurrence φ) := by
  intro equal
  have observed := congrArg rootObservation equal
  rw [rootObservation_mapTypes, rootObservation_mapTypes] at observed
  change RuleObservation.mk .hyp (some 0) = RuleObservation.mk .hyp (some 1) at observed
  cases observed

/-- A direct proof and a detour are still different supplied proofs after
specialization, even though both establish the same target implication. -/
theorem detour_remains_distinct :
    mapTypes σ constants (Controls.direct φ) ≠
      mapTypes σ constants (Controls.detour φ) := by
  intro equal
  have counted := congrArg nodeCount equal
  rw [nodeCount_mapTypes, nodeCount_mapTypes,
    (Controls.counts φ).1, (Controls.counts φ).2] at counted
  omega

open TypeSubstitutionExample

/-- A supplied quantified beta proof is specialized to a function domain. -/
def sourceBeta : ProofSyntax (NoConstants Unit) [] (quantifiedBeta (.base ())) :=
  .allI (.beta (.var (.vz : Var [.base ()] (.base ()))) (.var .vz))

def functionBeta : ProofSyntax (NoConstants Unit) []
    (quantifiedBeta (.arr (.base ()) (.base ()))) :=
  mapTypes functionInterpretation (noConstantsMap functionInterpretation)
    sourceBeta

theorem functionBeta_two_nodes : functionBeta.nodeCount = 2 := by
  exact (nodeCount_mapTypes functionInterpretation
    (noConstantsMap functionInterpretation) sourceBeta).trans (by rfl)

end TypeSubstitutionControls

#print axioms mapTypes
#print axioms mapTypes_derivable
#print axioms nodeCount_mapTypes
#print axioms rootObservation_mapTypes
#print axioms TypeSubstitutionControls.duplicate_occurrences_remain_distinct
#print axioms TypeSubstitutionControls.detour_remains_distinct
#print axioms TypeSubstitutionControls.functionBeta_two_nodes

end Mettapedia.Logic.HOL.ProofSyntax
