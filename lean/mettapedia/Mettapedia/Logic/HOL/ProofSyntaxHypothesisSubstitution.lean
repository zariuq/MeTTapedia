import Mettapedia.Logic.HOL.ProofSyntaxAppend

/-!
# Supplied hypothesis proofs through every retained HOL rule

Each source hypothesis occurrence receives an actual target proof. Logical
assumptions introduced under a rule remain local; object binders rename the
supplied proofs capture-safely. The construction neither selects a proof from
mere derivability nor conflates repeated hypothesis formulas.

Replacing a hypothesis can add nodes or duplicate a supplied proof tree.
The input proofs remain the provenance of that operation; the output tree
alone does not establish that its branches are independent observations.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.ProofSyntax

universe u v

variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}

def HypothesisSubstitution (source target : List (Formula Const Γ)) :=
  ∀ occurrence : Fin source.length, ProofSyntax Const target (source.get occurrence)

namespace HypothesisSubstitution

variable {source target : List (Formula Const Γ)}

def lift (substitution : HypothesisSubstitution source target) (head : Formula Const Γ) :
    HypothesisSubstitution (head :: source) (head :: target) :=
  Fin.cases (.hyp 0) (fun occurrence => prepend head (substitution occurrence))

def weaken (substitution : HypothesisSubstitution source target) (type : Ty Base) :
    HypothesisSubstitution (weakenHyps (σ := type) source) (weakenHyps (σ := type) target) :=
  fun occurrence =>
    let original : Fin source.length :=
      occurrence.cast (by simp only [weakenHyps, List.length_map])
    castIndices rfl (by
      change HOL.weaken (source.get original) = (source.map HOL.weaken).get occurrence
      change HOL.weaken source[original.val] = (source.map HOL.weaken)[occurrence.val]
      simp only [List.getElem_map, original, Fin.val_cast])
      (ProofSyntax.rename Rename.weaken (substitution original))

def identity (source : List (Formula Const Γ)) : HypothesisSubstitution source source :=
  fun occurrence => .hyp occurrence

/-- Supply the two blocks by their own occurrence positions. -/
def append : (left right target : List (Formula Const Γ)) →
    HypothesisSubstitution left target → HypothesisSubstitution right target →
    HypothesisSubstitution (left ++ right) target
  | [], _, _, _, rightProofs => rightProofs
  | _ :: left, right, target, leftProofs, rightProofs =>
      Fin.cases (leftProofs 0)
        (append left right target (fun occurrence => leftProofs occurrence.succ) rightProofs)

end HypothesisSubstitution

/-- A closed derivation can be used below any sequence of object binders. -/
def weakenContext {formula : ClosedFormula Const} : (context : Ctx Base) →
    ProofSyntax Const [] formula → ProofSyntax Const [] (HOL.weakenCtx context formula)
  | [], proof => proof
  | _ :: context, proof => ProofSyntax.rename Rename.weaken (weakenContext context proof)

theorem weakenContext_nodeCount {formula : ClosedFormula Const}
    (context : Ctx Base) (proof : ProofSyntax Const [] formula) :
    (weakenContext context proof).nodeCount = proof.nodeCount := by
  induction context with
  | nil => rfl
  | cons type context ih =>
      change (ProofSyntax.rename Rename.weaken (weakenContext context proof)).nodeCount = _
      rw [rename_nodeCount, ih]

def emptyOccurrenceMap (target : List (Formula Const Γ)) : OccurrenceMap [] target where
  index occurrence := Fin.elim0 occurrence
  get_eq occurrence := Fin.elim0 occurrence

/-- Actual proof substitution, including all extensional and binder rules. -/
def substituteHypotheses {Γ : Ctx Base} {source target : List (Formula Const Γ)}
    {conclusion : Formula Const Γ} (substitution : HypothesisSubstitution source target)
    (proof : ProofSyntax Const source conclusion) : ProofSyntax Const target conclusion :=
  match proof with
  | .hyp occurrence => substitution occurrence
  | .topI => .topI
  | .botE proof => .botE (substituteHypotheses substitution proof)
  | .andI left right =>
      .andI (substituteHypotheses substitution left) (substituteHypotheses substitution right)
  | .andEL proof => .andEL (substituteHypotheses substitution proof)
  | .andER proof => .andER (substituteHypotheses substitution proof)
  | .orIL proof => .orIL (substituteHypotheses substitution proof)
  | .orIR proof => .orIR (substituteHypotheses substitution proof)
  | .orE cases left right => .orE (substituteHypotheses substitution cases)
      (substituteHypotheses (substitution.lift _) left)
      (substituteHypotheses (substitution.lift _) right)
  | .impI proof => .impI (substituteHypotheses (substitution.lift _) proof)
  | .impE function argument =>
      .impE (substituteHypotheses substitution function) (substituteHypotheses substitution argument)
  | .notI proof => .notI (substituteHypotheses (substitution.lift _) proof)
  | .notE negative positive =>
      .notE (substituteHypotheses substitution negative) (substituteHypotheses substitution positive)
  | .allI proof => .allI (substituteHypotheses (substitution.weaken _) proof)
  | .allE term proof => .allE term (substituteHypotheses substitution proof)
  | .exI term proof => .exI term (substituteHypotheses substitution proof)
  | .exE existsProof body => .exE (substituteHypotheses substitution existsProof)
      (substituteHypotheses ((substitution.weaken _).lift _) body)
  | .eqRefl term => .eqRefl term
  | .eqSymm proof => .eqSymm (substituteHypotheses substitution proof)
  | .eqTrans left right =>
      .eqTrans (substituteHypotheses substitution left) (substituteHypotheses substitution right)
  | .eqPropI forward backward => .eqPropI (substituteHypotheses substitution forward)
      (substituteHypotheses substitution backward)
  | .eqPropEL proof => .eqPropEL (substituteHypotheses substitution proof)
  | .eqPropER proof => .eqPropER (substituteHypotheses substitution proof)
  | .eqApp term proof => .eqApp term (substituteHypotheses substitution proof)
  | .eqAppArg function proof => .eqAppArg function (substituteHypotheses substitution proof)
  | .eqLam proof => .eqLam (substituteHypotheses (substitution.weaken _) proof)
  | .funExt proof => .funExt (substituteHypotheses substitution proof)
  | .beta term body => .beta term body
  | .eta function => .eta function

theorem substituteHypotheses_erasure {source target : List (Formula Const Γ)}
    {conclusion : Formula Const Γ} (substitution : HypothesisSubstitution source target)
    (proof : ProofSyntax Const source conclusion) : ExtDerivation Const target conclusion :=
  (substituteHypotheses substitution proof).erase

end Mettapedia.Logic.HOL.ProofSyntax
