import Mettapedia.SetTheory.Profiles.ProfileIndexedCalculus
import Mettapedia.Logic.HOL.ImpredicativeProofTranslation

/-!
# Retained material deductions interpreted as typed HOL proofs

The material calculus is embedded using an explicit environment of typed
object terms. Its binders, substitution and assumption occurrences are
preserved. The existing impredicative translation then removes the derived
logical connectives from the target proof. This is a proof interpretation;
qualification of a native byte reader remains a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ProfileNativeProofCompilation

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.Logic

inductive MaterialBase where
  | set

def setType : HOL.Ty MaterialBase := .base .set

inductive MaterialConstant : HOL.Ty MaterialBase → Type where
  | member : MaterialConstant (.arr setType (.arr setType .prop))

abbrev Environment (count : Nat) (context : HOL.Ctx MaterialBase) :=
  Fin count → HOL.Term MaterialConstant context setType

def bindEnvironment {count : Nat} {context : HOL.Ctx MaterialBase}
    (environment : Environment count context) : Environment (count+1) (setType :: context) :=
  Fin.cases (.var .vz) (fun index => HOL.weaken (environment index))

def formula {count : Nat} {context : HOL.Ctx MaterialBase}
    (body : ContextualMaterialLogic.Formula count) (environment : Environment count context) :
    HOL.Formula MaterialConstant context :=
  match body with
  | .bottom => .bot
  | .equal first second => .eq (environment first) (environment second)
  | .member child parent => .app (.app (.const .member) (environment child)) (environment parent)
  | .both left right => .and (formula left environment) (formula right environment)
  | .either left right => .or (formula left environment) (formula right environment)
  | .imply left right => .imp (formula left environment) (formula right environment)
  | .all body => .all (formula body (bindEnvironment environment))
  | .exist body => .ex (formula body (bindEnvironment environment))

theorem formula_substitute {count target : Nat} {context : HOL.Ctx MaterialBase}
    (indices : Fin count → Fin target) (body : ContextualMaterialLogic.Formula count)
    (environment : Environment target context) :
    formula (ContextualMaterialLogic.substitute indices body) environment =
      formula body (fun index => environment (indices index)) := by
  induction body generalizing target context with
  | bottom => rfl
  | equal => rfl
  | member => rfl
  | both left right leftIH rightIH => simp only [ContextualMaterialLogic.substitute, formula, leftIH, rightIH]
  | either left right leftIH rightIH => simp only [ContextualMaterialLogic.substitute, formula, leftIH, rightIH]
  | imply left right leftIH rightIH => simp only [ContextualMaterialLogic.substitute, formula, leftIH, rightIH]
  | all body ih =>
      simp only [ContextualMaterialLogic.substitute, formula, ih]
      congr 2
      funext index
      exact Fin.cases rfl (fun _ => rfl) index
  | exist body ih =>
      simp only [ContextualMaterialLogic.substitute, formula, ih]
      congr 2
      funext index
      exact Fin.cases rfl (fun _ => rfl) index

theorem formula_rename {count : Nat} {context target : HOL.Ctx MaterialBase}
    (rho : HOL.Rename MaterialBase context target) (body : ContextualMaterialLogic.Formula count)
    (environment : Environment count context) :
    HOL.rename rho (formula body environment) =
      formula body (fun index => HOL.rename rho (environment index)) := by
  induction body generalizing context target with
  | bottom => rfl
  | equal => rfl
  | member => rfl
  | both left right leftIH rightIH => simp only [formula, HOL.rename, leftIH, rightIH]
  | either left right leftIH rightIH => simp only [formula, HOL.rename, leftIH, rightIH]
  | imply left right leftIH rightIH => simp only [formula, HOL.rename, leftIH, rightIH]
  | all body ih =>
      simp only [formula, HOL.rename, ih]
      congr 2
      funext index
      refine Fin.cases rfl (fun index => ?_) index
      exact HOL.ExtDerivation.rename_weaken rho (environment index)
  | exist body ih =>
      simp only [formula, HOL.rename, ih]
      congr 2
      funext index
      refine Fin.cases rfl (fun index => ?_) index
      exact HOL.ExtDerivation.rename_weaken rho (environment index)

theorem formula_termSubstitution {count : Nat} {context target : HOL.Ctx MaterialBase}
    (substitution : HOL.Subst MaterialConstant context target) (body : ContextualMaterialLogic.Formula count)
    (environment : Environment count context) :
    HOL.subst substitution (formula body environment) =
      formula body (fun index => HOL.subst substitution (environment index)) := by
  induction body generalizing context target with
  | bottom => rfl
  | equal => rfl
  | member => rfl
  | both left right leftIH rightIH => simp only [formula, HOL.subst, leftIH, rightIH]
  | either left right leftIH rightIH => simp only [formula, HOL.subst, leftIH, rightIH]
  | imply left right leftIH rightIH => simp only [formula, HOL.subst, leftIH, rightIH]
  | all body ih =>
      simp only [formula, HOL.subst, ih]
      congr 2
      funext index
      refine Fin.cases rfl (fun index => ?_) index
      exact HOL.subst_weaken substitution (environment index)
  | exist body ih =>
      simp only [formula, HOL.subst, ih]
      congr 2
      funext index
      refine Fin.cases rfl (fun index => ?_) index
      exact HOL.subst_weaken substitution (environment index)

theorem formula_weaken {count : Nat} {context : HOL.Ctx MaterialBase}
    (body : ContextualMaterialLogic.Formula count) (environment : Environment count context) :
    formula (ContextualMaterialLogic.weakenFormula body) (bindEnvironment environment) =
      HOL.weaken (formula body environment) := by
  rw [ContextualMaterialLogic.weakenFormula, formula_substitute]
  exact (formula_rename HOL.Rename.weaken body environment).symm

theorem formula_instantiate {count : Nat} {context : HOL.Ctx MaterialBase}
    (body : ContextualMaterialLogic.Formula (count+1)) (index : Fin count)
    (environment : Environment count context) :
    HOL.instantiate (environment index) (formula body (bindEnvironment environment)) =
      formula (ContextualMaterialLogic.substitute (ContextualMaterialLogic.instantiate index) body) environment := by
  rw [HOL.instantiate, formula_termSubstitution, formula_substitute]
  congr 1
  funext bound
  refine Fin.cases rfl (fun bound => ?_) bound
  exact HOL.instantiate_weaken (environment index) (environment bound)

def hypotheses {count : Nat} {context : HOL.Ctx MaterialBase}
    (assumptions : List (ContextualMaterialLogic.Formula count)) (environment : Environment count context) :
    List (HOL.Formula MaterialConstant context) := assumptions.map (fun body => formula body environment)

theorem hypotheses_weaken {count : Nat} {context : HOL.Ctx MaterialBase}
    (assumptions : List (ContextualMaterialLogic.Formula count)) (environment : Environment count context) :
    hypotheses (assumptions.map ContextualMaterialLogic.weakenFormula) (bindEnvironment environment) =
      HOL.weakenHyps (σ := setType) (hypotheses assumptions environment) := by
  simp [hypotheses, HOL.weakenHyps, List.map_map, Function.comp_def, formula_weaken]

def equalityElimination {count : Nat} {context : HOL.Ctx MaterialBase}
    {assumptions : List (ContextualMaterialLogic.Formula count)}
    {body : ContextualMaterialLogic.Formula (count+1)} {first second : Fin count}
    (environment : Environment count context)
    (same : HOL.ProofSyntax MaterialConstant (hypotheses assumptions environment)
      (.eq (environment first) (environment second)))
    (previous : HOL.ProofSyntax MaterialConstant (hypotheses assumptions environment)
      (formula (ContextualMaterialLogic.substitute (ContextualMaterialLogic.instantiate first) body)
        environment)) :
    HOL.ProofSyntax MaterialConstant (hypotheses assumptions environment)
      (formula (ContextualMaterialLogic.substitute (ContextualMaterialLogic.instantiate second) body)
        environment) := by
  let predicate := formula body (bindEnvironment environment)
  have firstBeta := HOL.ProofSyntax.beta (Δ := hypotheses assumptions environment)
    (environment first) predicate
  have secondBeta := HOL.ProofSyntax.beta (Δ := hypotheses assumptions environment)
    (environment second) predicate
  have application := HOL.ProofSyntax.eqAppArg (.lam predicate) same
  have equality := HOL.ProofSyntax.eqTrans (HOL.ProofSyntax.eqSymm firstBeta)
    (HOL.ProofSyntax.eqTrans application secondBeta)
  have premiseProof := HOL.ProofSyntax.castIndices rfl
    (formula_instantiate body first environment).symm previous
  exact HOL.ProofSyntax.castIndices rfl (formula_instantiate body second environment)
    (HOL.ProofSyntax.impE (HOL.ProofSyntax.eqPropEL equality) premiseProof)

/-- Every material rule is translated as a retained proof constructor or
an explicit equality-transport derivation. Assumption positions are retained
even when the formulas at two positions are equal. -/
def proof {count : Nat} {context : HOL.Ctx MaterialBase}
    {assumptions : List (ContextualMaterialLogic.Formula count)}
    {conclusion : ContextualMaterialLogic.Formula count}
    (deduction : GraphRealizedDeduction.Proof assumptions conclusion)
    (environment : Environment count context) :
    HOL.ProofSyntax MaterialConstant (hypotheses assumptions environment) (formula conclusion environment) :=
  match deduction with
  | .hypothesis index => by
      exact HOL.ProofSyntax.castIndices rfl (by simp only [hypotheses, List.get_eq_getElem, List.getElem_map, Fin.cast])
        (HOL.ProofSyntax.hyp (Δ := hypotheses assumptions environment) (index.cast (by simp [hypotheses])))
  | .weakening previous positions same =>
      HOL.ProofSyntax.mono
        (({ index := positions, get_eq := same } : HOL.ProofSyntax.OccurrenceMap _ _).map
          (fun body => formula body environment)) (proof previous environment)
  | .bottomElim previous => .botE (proof previous environment)
  | .bothIntro left right => .andI (proof left environment) (proof right environment)
  | .bothLeft previous => .andEL (proof previous environment)
  | .bothRight previous => .andER (proof previous environment)
  | .eitherLeft previous => .orIL (proof previous environment)
  | .eitherRight previous => .orIR (proof previous environment)
  | .eitherElim previous left right =>
      .orE (proof previous environment) (proof left environment) (proof right environment)
  | .implyIntro previous => .impI (proof previous environment)
  | .implyElim previous premise => .impE (proof previous environment) (proof premise environment)
  | .allIntro previous => .allI (HOL.ProofSyntax.castIndices
      (hypotheses_weaken _ environment) rfl (proof previous (bindEnvironment environment)))
  | .allElim previous index => HOL.ProofSyntax.castIndices rfl
      (formula_instantiate _ index environment) (.allE (environment index) (proof previous environment))
  | .existIntro index previous => .exI (environment index)
      (HOL.ProofSyntax.castIndices rfl (formula_instantiate _ index environment).symm
        (proof previous environment))
  | .existElim previous branch => .exE (proof previous environment)
      (HOL.ProofSyntax.castIndices (by
        simp only [hypotheses, List.map_cons, List.map_map, Function.comp_def,
          formula_weaken, HOL.weakenHyps])
        (formula_weaken _ environment) (proof branch (bindEnvironment environment)))
  | .equalRefl index => .eqRefl (environment index)
  | .equalElim same previous => equalityElimination environment (proof same environment) (proof previous environment)

/-- Expansion is the existing rule-by-rule HOL construction, applied to the
translated material proof. It does not assume a compiled conclusion. -/
def coreProof {count : Nat} {context : HOL.Ctx MaterialBase}
    {assumptions : List (ContextualMaterialLogic.Formula count)}
    {conclusion : ContextualMaterialLogic.Formula count}
    (deduction : GraphRealizedDeduction.Proof assumptions conclusion)
    (environment : Environment count context) :
    HOL.ProofSyntax MaterialConstant
      ((hypotheses assumptions environment).map HOL.ImpredicativeConnectives.expand)
      (HOL.ImpredicativeConnectives.expand (formula conclusion environment)) :=
  HOL.ImpredicativeConnectives.expandProof (proof deduction environment)

theorem coreProof_isCore {count : Nat} {context : HOL.Ctx MaterialBase}
    {assumptions : List (ContextualMaterialLogic.Formula count)}
    {conclusion : ContextualMaterialLogic.Formula count}
    (deduction : GraphRealizedDeduction.Proof assumptions conclusion)
    (environment : Environment count context) :
    HOL.ImpredicativeConnectives.IsCoreProof (coreProof deduction environment) :=
  HOL.ImpredicativeConnectives.expandProof_isCore (proof deduction environment)

theorem proof_derivable {count : Nat} {context : HOL.Ctx MaterialBase}
    {assumptions : List (ContextualMaterialLogic.Formula count)}
    {conclusion : ContextualMaterialLogic.Formula count}
    (deduction : GraphRealizedDeduction.Proof assumptions conclusion)
    (environment : Environment count context) :
    HOL.ExtDerivation MaterialConstant (hypotheses assumptions environment) (formula conclusion environment) :=
  (proof deduction environment).erase

/-- A compiled profile deduction keeps its original rule declarations,
including their adoption trees and origins, alongside the target proof. -/
structure Receipt (profile : ProfileIndexedCalculus.Profile)
    {count : Nat} (assumptions : List (ContextualMaterialLogic.Formula count))
    (conclusion : ContextualMaterialLogic.Formula count)
    (context : HOL.Ctx MaterialBase) (environment : Environment count context) where
  declarations : List (ProfileIndexedCalculus.Declaration profile count)
  target : HOL.ProofSyntax MaterialConstant
    (hypotheses (ProfileIndexedCalculus.declarationFormulas declarations ++ assumptions) environment)
    (formula conclusion environment)

def compileDerivation {profile : ProfileIndexedCalculus.Profile} {count : Nat}
    {assumptions : List (ContextualMaterialLogic.Formula count)}
    {conclusion : ContextualMaterialLogic.Formula count} {context : HOL.Ctx MaterialBase}
    (derivation : ProfileIndexedCalculus.Derivation profile assumptions conclusion)
    (environment : Environment count context) : Receipt profile assumptions conclusion context environment :=
  ⟨derivation.declarations, proof derivation.proof environment⟩

theorem compileDerivation_origins {profile : ProfileIndexedCalculus.Profile} {count : Nat}
    {assumptions : List (ContextualMaterialLogic.Formula count)}
    {conclusion : ContextualMaterialLogic.Formula count} {context : HOL.Ctx MaterialBase}
    (derivation : ProfileIndexedCalculus.Derivation profile assumptions conclusion)
    (environment : Environment count context) :
    (compileDerivation derivation environment).declarations.map ProfileIndexedCalculus.Declaration.origin =
      derivation.origins := rfl

namespace Controls

def reflexiveExistence : GraphRealizedDeduction.Proof (count := 0) []
    (ContextualMaterialLogic.Formula.all (.exist (.equal 0 1))) :=
  .allIntro (.existIntro 0 (.equalRefl 0))

def memberWitness : GraphRealizedDeduction.Proof (count := 0) []
    (ContextualMaterialLogic.Formula.all (.imply (.member 0 0) (.exist (.member 0 1)))) :=
  .allIntro (.implyIntro (.existIntro 0 (.hypothesis 0)))

def memberWitnessTarget : HOL.ProofSyntax MaterialConstant []
    (formula (.all (.imply (.member 0 0) (.exist (.member 0 1)))) (context := []) Fin.elim0) :=
  proof memberWitness Fin.elim0

theorem memberWitnessTarget_core :
    HOL.ImpredicativeConnectives.IsCoreProof (coreProof memberWitness (context := []) Fin.elim0) :=
  coreProof_isCore memberWitness Fin.elim0

theorem duplicate_hypotheses_remain_distinct {count : Nat} {context : HOL.Ctx MaterialBase}
    (body : ContextualMaterialLogic.Formula count) (environment : Environment count context) :
    proof (GraphRealizedDeduction.Proof.hypothesis (assumptions := [body, body]) 0) environment ≠
      proof (GraphRealizedDeduction.Proof.hypothesis (assumptions := [body, body]) 1) environment := by
  intro same
  have observed := congrArg HOL.ProofSyntax.rootObservation same
  change (⟨.hyp, some 0⟩ : HOL.ProofSyntax.RuleObservation) = ⟨.hyp, some 1⟩ at observed
  cases observed

end Controls

end Mettapedia.SetTheory.Profiles.ProfileNativeProofCompilation
