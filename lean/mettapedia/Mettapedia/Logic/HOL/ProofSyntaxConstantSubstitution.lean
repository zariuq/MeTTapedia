import Mettapedia.Logic.HOL.ProofSyntaxStructural
import Mettapedia.Logic.HOL.Syntax.ConstantSubstitutionComposition

/-!
# Closed definitions in retained HOL proofs

Constant interpretation traverses all 29 rules of the retained calculus. It
keeps ordered premises and the exact position of every hypothesis occurrence,
including duplicate formulas which become identical after expansion. It does
not obtain a new receipt from proposition-valued derivability.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.ProofSyntax

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v} {Const' : Ty Base → Type w}
  {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}

/-- Interpret constants by closed typed terms while retaining the proof. -/
def substConst {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (images : ∀ {type}, Const type → ClosedTerm Const' type)
    (proof : ProofSyntax Const Δ φ) :
    ProofSyntax Const' (Δ.map (HOL.substConst images)) (HOL.substConst images φ) :=
  match proof with
  | .hyp occurrence => castIndices rfl (by simp)
      (ProofSyntax.hyp (Const := Const') (Δ := Δ.map (HOL.substConst images))
        (occurrence.cast (by simp)))
  | .topI => .topI
  | .botE proof => .botE (substConst images proof)
  | .andI left right => .andI (substConst images left) (substConst images right)
  | .andEL proof => .andEL (substConst images proof)
  | .andER proof => .andER (substConst images proof)
  | .orIL proof => .orIL (substConst images proof)
  | .orIR proof => .orIR (substConst images proof)
  | .orE cases left right =>
      .orE (substConst images cases) (substConst images left) (substConst images right)
  | .impI proof => .impI (substConst images proof)
  | .impE function argument => .impE (substConst images function) (substConst images argument)
  | .notI proof => .notI (substConst images proof)
  | .notE negative positive => .notE (substConst images negative) (substConst images positive)
  | .allI proof => .allI (castIndices
      (ExtDerivation.substConst_weakenHyps images _).symm rfl (substConst images proof))
  | .allE term proof => castIndices rfl (HOL.substConst_instantiate images term _).symm
      (ProofSyntax.allE (HOL.substConst images term) (substConst images proof))
  | .exI term proof => .exI (HOL.substConst images term)
      (castIndices rfl (HOL.substConst_instantiate images term _) (substConst images proof))
  | .exE existsProof body => .exE (substConst images existsProof)
      (castIndices (by simp [List.map, ExtDerivation.substConst_weakenHyps])
        (HOL.substConst_weaken images _) (substConst images body))
  | .eqRefl term => .eqRefl (HOL.substConst images term)
  | .eqSymm proof => .eqSymm (substConst images proof)
  | .eqTrans left right => .eqTrans (substConst images left) (substConst images right)
  | .eqPropI forward backward =>
      .eqPropI (substConst images forward) (substConst images backward)
  | .eqPropEL proof => .eqPropEL (substConst images proof)
  | .eqPropER proof => .eqPropER (substConst images proof)
  | .eqApp term proof => .eqApp (HOL.substConst images term) (substConst images proof)
  | .eqAppArg function proof =>
      .eqAppArg (HOL.substConst images function) (substConst images proof)
  | .eqLam proof => .eqLam (castIndices
      (ExtDerivation.substConst_weakenHyps images _).symm rfl (substConst images proof))
  | .funExt proof => .funExt (castIndices rfl
      (by simp [HOL.substConst, HOL.substConst_weaken]) (substConst images proof))
  | .beta term body => castIndices rfl
      (by simp [HOL.substConst, HOL.substConst_instantiate])
      (ProofSyntax.beta (Δ := Δ.map (HOL.substConst images))
        (HOL.substConst images term) (HOL.substConst images body))
  | .eta function => castIndices rfl
      (by simp [HOL.substConst, HOL.substConst_weaken])
      (ProofSyntax.eta (Δ := Δ.map (HOL.substConst images)) (HOL.substConst images function))

theorem substConst_erasure
    (images : ∀ {type}, Const type → ClosedTerm Const' type)
    (proof : ProofSyntax Const Δ φ) :
    ExtDerivation Const' (Δ.map (HOL.substConst images)) (HOL.substConst images φ) :=
  (substConst images proof).erase

/-- Embed a supplied proof into a larger constant signature. -/
def mapConst
    (constants : ∀ {type}, Const type → Const' type)
    (proof : ProofSyntax Const Δ φ) :
    ProofSyntax Const' (Δ.map (HOL.mapConst constants)) (HOL.mapConst constants φ) :=
  castIndices (by
    clear proof
    induction Δ with
    | nil => rfl
    | cons head tail ih =>
        simp only [List.map_cons, HOL.substConst_constant_images, ih])
    (HOL.substConst_constant_images constants φ)
    (substConst (fun constant => .const (constants constant)) proof)

set_option backward.isDefEq.respectTransparency false in
/-- Rule and hypothesis position survive expansion, even if images coincide. -/
theorem substConst_rootObservation
    (images : ∀ {type}, Const type → ClosedTerm Const' type)
    (proof : ProofSyntax Const Δ φ) :
    (substConst images proof).rootObservation = proof.rootObservation := by
  cases proof <;> dsimp only [substConst] <;>
    first | (simp only [rootObservation_castIndices] <;> rfl) | rfl

set_option backward.isDefEq.respectTransparency false in
theorem substConst_nodeCount
    (images : ∀ {type}, Const type → ClosedTerm Const' type)
    (proof : ProofSyntax Const Δ φ) :
    (substConst images proof).nodeCount = proof.nodeCount := by
  have count_cast {Γ : Ctx Base} {Δ Δ' : List (Formula Const' Γ)}
      {φ ψ : Formula Const' Γ} (assumptions : Δ = Δ') (conclusion : φ = ψ)
      (proof : ProofSyntax Const' Δ φ) :
      (castIndices assumptions conclusion proof).observe.nodeCount = proof.observe.nodeCount :=
    nodeCount_castIndices assumptions conclusion proof
  induction proof with
  | hyp occurrence =>
      dsimp only [substConst]
      simp only [nodeCount_castIndices]
      rfl
  | topI | eqRefl _ => rfl
  | beta _ _ | eta _ =>
      dsimp only [substConst]
      simp only [nodeCount_castIndices]
      rfl
  | _ =>
      dsimp only [substConst]
      try simp only [nodeCount_castIndices]
      change 1 + _ = 1 + _
      simp_all [nodeCount, weakenHyps]

/-- Forget sequents while retaining the complete ordered rule tree and every
local hypothesis occurrence. This observation does not retain rule terms. -/
inductive RuleTree where
  | node (rule : RuleObservation) (children : List RuleTree)

def ruleTree {Judgment : Type v}
    (tree : Mettapedia.Logic.Derivation Judgment RuleObservation) :
    RuleTree :=
  match tree with
  | .node _ rule _ children => .node rule (List.ofFn (fun index => ruleTree (children index)))

@[simp] theorem ruleTree_castIndices
    {Δ' : List (Formula Const Γ)} {ψ : Formula Const Γ}
    (assumptions : Δ = Δ') (conclusion : φ = ψ) (proof : ProofSyntax Const Δ φ) :
    ruleTree (castIndices assumptions conclusion proof).observe = ruleTree proof.observe := by
  cases assumptions
  cases conclusion
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem substConst_ruleTree
    (images : ∀ {type}, Const type → ClosedTerm Const' type)
    (proof : ProofSyntax Const Δ φ) :
    ruleTree (substConst images proof).observe = ruleTree proof.observe := by
  induction proof <;> dsimp only [substConst]
  all_goals try simp only [ruleTree_castIndices]
  all_goals
    first
    | rfl
    | (change RuleTree.node _ _ = RuleTree.node _ _
       congr 1
       simp_all only [List.ofFn_succ, List.ofFn_zero,
         List.get_eq_getElem, List.getElem_cons_zero, List.getElem_cons_succ,
         Fin.val_zero, Fin.val_succ, ruleTree_castIndices])

end Mettapedia.Logic.HOL.ProofSyntax
