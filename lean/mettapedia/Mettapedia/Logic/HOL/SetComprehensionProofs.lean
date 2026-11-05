import Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation
import Mettapedia.Logic.HOL.ProofSyntaxConstantSubstitution
import Mettapedia.Logic.HOL.ProofSyntaxCongruence

/-!
# Retained proofs for material-set comprehension

Separation, image and powerset laws are specialized from the existing set
axioms. Lambda predicates and mappings reduce by explicit HOL beta proofs.
The resulting constructors operate in arbitrary contexts and constant
extensions, and retain their supplied axiom proofs. In particular, the
singleton truth code has proof-producing introduction and reflection rules;
no semantic validity oracle is used to construct a proof.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.SetComprehensionProofs

open ContextualTrinity
open Mettapedia.Logic.HOL.Embedding
universe v
variable {Const : Ty Unit → Type v}
abbrev Core (Const : Ty Unit → Type v) := ∀ {type}, ZFSetHenkinInterpretation.Symbol type → Const type
variable (core : Core Const)
variable {Γ : Ctx Unit} {Δ : List (Formula Const Γ)}

private theorem substVariables {type : Ty Unit} (term : Term Const Γ type) :
    HOL.subst (fun {_} index => Term.var index) term = term := subst_id term

private theorem substSuccessors {type added : Ty Unit} (term : Term Const Γ type) :
    HOL.subst (fun {_} index => Term.var (Var.vs (σ := added) index)) term =
      HOL.rename Rename.weaken term := subst_ofRename Rename.weaken term

private theorem instantiateRenamed {type added : Ty Unit}
    (point : Term Const Γ added) (term : Term Const Γ type) :
    HOL.subst (Subst.single point) (HOL.rename Rename.weaken term) = term :=
  instantiate_weaken point term

private theorem liftDropsSecond {type added outer : Ty Unit}
    (point : Term Const Γ added) (term : Term Const Γ type) :
    HOL.subst (Subst.lift (σ := outer) (Subst.single point))
      (HOL.subst (fun {_} index => Term.var (Var.vs (Var.vs index))) term) =
        HOL.rename Rename.weaken term := by
  have twice : HOL.subst (fun {_} index => Term.var (Var.vs (Var.vs index))) term =
      weaken (σ := outer) (weaken (σ := added) term) := by
    exact (subst_ofRename (fun {_} index => Var.vs (Var.vs index)) term).trans
      (rename_comp Rename.weaken Rename.weaken term).symm
  rw [twice, subst_weaken]
  change weaken (instantiate point (weaken term)) = weaken term
  rw [instantiate_weaken]

attribute [local simp] substVariables substSuccessors instantiateRenamed liftDropsSecond

private theorem observeCast {conclusion result : Formula Const Γ}
    {assumptions : List (Formula Const Γ)} (same : Δ = assumptions) (equal : conclusion = result)
    (proof : ProofSyntax Const Δ conclusion) :
    (proof.castIndices same equal).observe = proof.observe := by
  cases same
  cases equal
  rfl

attribute [local simp] observeCast

def member (value bound : Term Const Γ ZFSetHenkinInterpretation.set) : Formula Const Γ :=
  .app (.app (.const (core .member)) value) bound

def separate (bound : Term Const Γ ZFSetHenkinInterpretation.set) (predicate : Term Const Γ ZFSetHenkinInterpretation.predicate) :
    Term Const Γ ZFSetHenkinInterpretation.set := .app (.app (.const (core .separate)) bound) predicate

def image (bound : Term Const Γ ZFSetHenkinInterpretation.set) (function : Term Const Γ ZFSetHenkinInterpretation.mapping) :
    Term Const Γ ZFSetHenkinInterpretation.set := .app (.app (.const (core .replace)) bound) function

def power (bound : Term Const Γ ZFSetHenkinInterpretation.set) : Term Const Γ ZFSetHenkinInterpretation.set :=
  .app (.const (core .power)) bound

def familyUnion (bound : Term Const Γ ZFSetHenkinInterpretation.set) (family : Term Const Γ ZFSetHenkinInterpretation.mapping) :
    Term Const Γ ZFSetHenkinInterpretation.set := .app (.const (core .union)) (image core bound family)

def included (left right : Term Const Γ ZFSetHenkinInterpretation.set) : Formula Const Γ :=
  .all (.imp (member core (.var .vz) (weaken left))
    (member core (.var .vz) (weaken right)))

def truthCode (proposition : Formula Const Γ) : Term Const Γ ZFSetHenkinInterpretation.set :=
  separate core (power core (.const (core .empty))) (.lam (weaken proposition))

def lawAt (law : ClosedFormula ZFSetHenkinInterpretation.Symbol) : Formula Const Γ :=
  HOL.rename (fun {type} (index : Var [] type) => nomatch index) (mapConst core law)

theorem lawAt_eq_weakenCtx (law : ClosedFormula ZFSetHenkinInterpretation.Symbol) :
    lawAt (Γ := Γ) core law = weakenCtx Γ (mapConst core law) :=
  rename_weakenCtx (Γ' := []) (Δ' := Γ) (fun {_} index => nomatch index) (mapConst core law)

def separation (bound : Term Const Γ ZFSetHenkinInterpretation.set) (predicate : Term Const Γ ZFSetHenkinInterpretation.predicate)
    (point : Term Const Γ ZFSetHenkinInterpretation.set)
    (law : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.separationLaw)) :
    ProofSyntax Const Δ (.and
      (.imp (member core point (separate core bound predicate))
        (.and (member core point bound) (.app predicate point)))
      (.imp (.and (member core point bound) (.app predicate point))
        (member core point (separate core bound predicate)))) := by
  apply ProofSyntax.castIndices rfl ?_
    (.allE point (.allE predicate (.allE bound law)))
  dsimp only [lawAt, ZFSetHenkinInterpretation.separationLaw, ZFSetHenkinInterpretation.iffFormula, ZFSetHenkinInterpretation.member, ZFSetHenkinInterpretation.separate,
    member, separate, weakenCtx, mapConst, instantiate, HOL.subst, Subst.single,
    Subst.lift, weaken, HOL.rename, Rename.lift, Rename.weaken, subst_weaken, instantiate_weaken]
  simp only [HOL.subst_rename, HOL.subst, Subst.single, Subst.lift, Rename.weaken, HOL.rename]
  simp

def powerset (bound point : Term Const Γ ZFSetHenkinInterpretation.set)
    (law : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.powerLaw)) :
    ProofSyntax Const Δ (.and
      (.imp (member core point (power core bound)) (included core point bound))
      (.imp (included core point bound) (member core point (power core bound)))) := by
  apply ProofSyntax.castIndices rfl ?_ (.allE point (.allE bound law))
  dsimp only [lawAt, ZFSetHenkinInterpretation.powerLaw, ZFSetHenkinInterpretation.iffFormula, ZFSetHenkinInterpretation.member, member, power,
    included, weakenCtx, mapConst, instantiate, HOL.subst, Subst.single,
    Subst.lift, weaken, HOL.rename, Rename.lift, Rename.weaken, subst_weaken, instantiate_weaken]
  simp only [HOL.subst_rename, HOL.subst, Subst.single, Subst.lift, Rename.weaken, HOL.rename]
  simp

def replacement (bound : Term Const Γ ZFSetHenkinInterpretation.set) (function : Term Const Γ ZFSetHenkinInterpretation.mapping)
    (point : Term Const Γ ZFSetHenkinInterpretation.set)
    (law : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.replacementLaw)) :
    ProofSyntax Const Δ (.and
      (.imp (member core point (image core bound function))
        (.ex (.and (member core (.var .vz) (weaken bound))
          (.eq (.app (weaken function) (.var .vz)) (weaken point)))))
      (.imp (.ex (.and (member core (.var .vz) (weaken bound))
          (.eq (.app (weaken function) (.var .vz)) (weaken point))))
        (member core point (image core bound function)))) := by
  apply ProofSyntax.castIndices rfl ?_
    (.allE point (.allE function (.allE bound law)))
  dsimp only [lawAt, ZFSetHenkinInterpretation.replacementLaw, ZFSetHenkinInterpretation.iffFormula, ZFSetHenkinInterpretation.member, ZFSetHenkinInterpretation.replace,
    member, image, weakenCtx, mapConst, instantiate, HOL.subst, Subst.single,
    Subst.lift, weaken, HOL.rename, Rename.lift, Rename.weaken, subst_weaken, instantiate_weaken]
  simp only [HOL.subst_rename, HOL.subst, Subst.single, Subst.lift, Rename.weaken, HOL.rename]
  simp

def extensionality (left right : Term Const Γ ZFSetHenkinInterpretation.set)
    (law : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.extensionality)) :
    ProofSyntax Const Δ (.imp
      (.all (.and
        (.imp (member core (.var .vz) (weaken left))
          (member core (.var .vz) (weaken right)))
        (.imp (member core (.var .vz) (weaken right))
          (member core (.var .vz) (weaken left)))))
      (.eq left right)) := by
  apply ProofSyntax.castIndices rfl ?_ (.allE right (.allE left law))
  dsimp only [lawAt, ZFSetHenkinInterpretation.extensionality, ZFSetHenkinInterpretation.iffFormula, ZFSetHenkinInterpretation.member, member,
    weakenCtx, mapConst, instantiate, HOL.subst, Subst.single,
    Subst.lift, weaken, HOL.rename, Rename.lift, Rename.weaken, subst_weaken, instantiate_weaken]
  simp only [HOL.subst_rename, HOL.subst, Subst.single, Subst.lift, Rename.weaken, HOL.rename]
  simp

def union (bound point : Term Const Γ ZFSetHenkinInterpretation.set)
    (law : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.unionLaw)) :
    ProofSyntax Const Δ (.and
      (.imp (member core point (.app (.const (core .union)) bound))
        (.ex (.and (member core (.var .vz) (weaken bound))
          (member core (weaken point) (.var .vz)))))
      (.imp (.ex (.and (member core (.var .vz) (weaken bound))
          (member core (weaken point) (.var .vz))))
        (member core point (.app (.const (core .union)) bound)))) := by
  apply ProofSyntax.castIndices rfl ?_ (.allE point (.allE bound law))
  dsimp only [lawAt, ZFSetHenkinInterpretation.unionLaw, ZFSetHenkinInterpretation.iffFormula,
    ZFSetHenkinInterpretation.member, member, mapConst, instantiate, HOL.subst,
    Subst.single, Subst.lift, weaken, HOL.rename, Rename.lift, Rename.weaken]
  simp only [HOL.subst_rename, HOL.subst, Subst.single, Subst.lift, Rename.weaken, HOL.rename]
  simp

def imageIntro (bound : Term Const Γ ZFSetHenkinInterpretation.set)
    (function : Term Const Γ ZFSetHenkinInterpretation.mapping)
    (point : Term Const Γ ZFSetHenkinInterpretation.set)
    (law : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.replacementLaw))
    (inBound : ProofSyntax Const Δ (member core point bound)) :
    ProofSyntax Const Δ (member core (.app function point) (image core bound function)) := by
  apply ProofSyntax.impE (.andER (replacement core bound function (.app function point) law))
  apply ProofSyntax.exI point
  apply ProofSyntax.castIndices rfl ?_ (.andI inBound (.eqRefl (.app function point)))
  simp [instantiate, member, HOL.subst, Subst.single, weaken]

def familyUnionIntro (bound : Term Const Γ ZFSetHenkinInterpretation.set)
    (family : Term Const Γ ZFSetHenkinInterpretation.mapping)
    (index point : Term Const Γ ZFSetHenkinInterpretation.set)
    (unionLaw : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.unionLaw))
    (replacementLaw : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.replacementLaw))
    (inBound : ProofSyntax Const Δ (member core index bound))
    (inFibre : ProofSyntax Const Δ (member core point (.app family index))) :
    ProofSyntax Const Δ (member core point (familyUnion core bound family)) := by
  apply ProofSyntax.impE (.andER (union core (image core bound family) point unionLaw))
  apply ProofSyntax.exI (.app family index)
  apply ProofSyntax.castIndices rfl ?_
    (.andI (imageIntro core bound family index replacementLaw inBound) inFibre)
  simp [instantiate, member, HOL.subst, Subst.single, weaken]

/-- The only reduction used for a comprehension body is the retained beta
rule. The source binder and its actual instantiation remain in the result. -/
def separationIntro (bound point : Term Const Γ ZFSetHenkinInterpretation.set)
    (body : Formula Const (ZFSetHenkinInterpretation.set :: Γ))
    (law : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.separationLaw))
    (inBound : ProofSyntax Const Δ (member core point bound))
    (satisfies : ProofSyntax Const Δ (instantiate point body)) :
    ProofSyntax Const Δ (member core point (separate core bound (.lam body))) :=
  .impE (.andER (separation core bound (.lam body) point law))
    (.andI inBound (.impE (.eqPropER (.beta point body)) satisfies))

def separationElim (bound point : Term Const Γ ZFSetHenkinInterpretation.set)
    (body : Formula Const (ZFSetHenkinInterpretation.set :: Γ))
    (law : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.separationLaw))
    (admitted : ProofSyntax Const Δ (member core point (separate core bound (.lam body)))) :
    ProofSyntax Const Δ (.and (member core point bound) (instantiate point body)) := by
  have parts := ProofSyntax.impE (.andEL (separation core bound (.lam body) point law)) admitted
  exact .andI (.andEL parts) (.impE (.eqPropEL (.beta point body)) (.andER parts))

/-- Selecting the property directly retains the supplied membership proof
once; constructing both components first would duplicate it. -/
def separationProperty (bound point : Term Const Γ ZFSetHenkinInterpretation.set)
    (body : Formula Const (ZFSetHenkinInterpretation.set :: Γ))
    (law : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.separationLaw))
    (admitted : ProofSyntax Const Δ (member core point (separate core bound (.lam body)))) :
    ProofSyntax Const Δ (instantiate point body) :=
  .impE (.eqPropEL (.beta point body))
    (.andER (.impE (.andEL (separation core bound (.lam body) point law)) admitted))

def emptyInPowerEmpty (law : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.powerLaw)) :
    ProofSyntax Const Δ (member core (.const (core .empty))
      (power core (.const (core .empty)))) :=
  .impE (.andER (powerset core (.const (core .empty)) (.const (core .empty)) law))
    (.allI (.impI (.hyp 0)))

def truthIntro (proposition : Formula Const Γ)
    (powerLaw : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.powerLaw))
    (separationLaw : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.separationLaw))
    (proof : ProofSyntax Const Δ proposition) :
    ProofSyntax Const Δ (member core (.const (core .empty)) (truthCode core proposition)) :=
  separationIntro core _ _ (weaken proposition) separationLaw (emptyInPowerEmpty core powerLaw)
    (ProofSyntax.castIndices rfl (instantiate_weaken _ proposition).symm proof)

/-- Reflection consumes a proof of membership; it does not extract a proof
from the denotation of the code. Any member is sufficient. -/
def truthReflect (proposition : Formula Const Γ) (point : Term Const Γ ZFSetHenkinInterpretation.set)
    (separationLaw : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.separationLaw))
    (proof : ProofSyntax Const Δ (member core point (truthCode core proposition))) :
    ProofSyntax Const Δ proposition :=
  ProofSyntax.castIndices rfl (instantiate_weaken point proposition)
    (separationProperty core _ point (weaken proposition) separationLaw proof)

def identityIntro (point : Term Const Γ ZFSetHenkinInterpretation.set)
    (powerLaw : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.powerLaw))
    (separationLaw : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.separationLaw)) :
    ProofSyntax Const Δ (member core (.const (core .empty)) (truthCode core (.eq point point))) :=
  truthIntro core _ powerLaw separationLaw (.eqRefl point)

def identityReflect (left right witness : Term Const Γ ZFSetHenkinInterpretation.set)
    (separationLaw : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.separationLaw))
    (proof : ProofSyntax Const Δ (member core witness (truthCode core (.eq left right)))) :
    ProofSyntax Const Δ (.eq left right) :=
  truthReflect core _ witness separationLaw proof

/-- Equality of propositions transports their entire separated set codes. -/
def truthCongr {left right : Formula Const Γ}
    (equal : ProofSyntax Const Δ (.eq left right)) :
    ProofSyntax Const Δ (.eq (truthCode core left) (truthCode core right)) :=
  .eqAppArg (.app (.const (core .separate)) (power core (.const (core .empty))))
    (.eqLam (ProofSyntax.rename Rename.weaken equal))

theorem separation_free (bound : Term Const Γ ZFSetHenkinInterpretation.set)
    (predicate : Term Const Γ ZFSetHenkinInterpretation.predicate)
    (point : Term Const Γ ZFSetHenkinInterpretation.set)
    (law : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.separationLaw)) :
    (separation core bound predicate point law).FunctionExtensionalityFree ↔
      law.FunctionExtensionalityFree := by
  simp [separation, ProofSyntax.FunctionExtensionalityFree]

theorem powerset_free (bound point : Term Const Γ ZFSetHenkinInterpretation.set)
    (law : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.powerLaw)) :
    (powerset core bound point law).FunctionExtensionalityFree ↔ law.FunctionExtensionalityFree := by
  simp [powerset, ProofSyntax.FunctionExtensionalityFree]

theorem separationIntro_free (bound point : Term Const Γ ZFSetHenkinInterpretation.set)
    (body : Formula Const (ZFSetHenkinInterpretation.set :: Γ))
    (law : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.separationLaw))
    (inBound : ProofSyntax Const Δ (member core point bound))
    (satisfies : ProofSyntax Const Δ (instantiate point body))
    (lawFree : law.FunctionExtensionalityFree) (boundFree : inBound.FunctionExtensionalityFree)
    (bodyFree : satisfies.FunctionExtensionalityFree) :
    (separationIntro core bound point body law inBound satisfies).FunctionExtensionalityFree := by
  simp [separationIntro, ProofSyntax.FunctionExtensionalityFree, separation_free, lawFree,
    boundFree, bodyFree]

theorem separationElim_free (bound point : Term Const Γ ZFSetHenkinInterpretation.set)
    (body : Formula Const (ZFSetHenkinInterpretation.set :: Γ))
    (law : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.separationLaw))
    (admitted : ProofSyntax Const Δ (member core point (separate core bound (.lam body))))
    (lawFree : law.FunctionExtensionalityFree) (proofFree : admitted.FunctionExtensionalityFree) :
    (separationElim core bound point body law admitted).FunctionExtensionalityFree := by
  simp [separationElim, ProofSyntax.FunctionExtensionalityFree, separation_free, lawFree, proofFree]

theorem emptyInPowerEmpty_free (law : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.powerLaw))
    (lawFree : law.FunctionExtensionalityFree) :
    (emptyInPowerEmpty core law).FunctionExtensionalityFree := by
  simp [emptyInPowerEmpty, ProofSyntax.FunctionExtensionalityFree, powerset_free, lawFree]

theorem truthIntro_free (proposition : Formula Const Γ)
    (powerLaw : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.powerLaw))
    (separationLaw : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.separationLaw))
    (proof : ProofSyntax Const Δ proposition)
    (powerFree : powerLaw.FunctionExtensionalityFree)
    (separationFree : separationLaw.FunctionExtensionalityFree)
    (proofFree : proof.FunctionExtensionalityFree) :
    (truthIntro core proposition powerLaw separationLaw proof).FunctionExtensionalityFree := by
  apply separationIntro_free <;> simp [emptyInPowerEmpty_free, powerFree, separationFree, proofFree]

theorem truthReflect_free (proposition : Formula Const Γ) (point : Term Const Γ ZFSetHenkinInterpretation.set)
    (law : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.separationLaw))
    (proof : ProofSyntax Const Δ (member core point (truthCode core proposition)))
    (lawFree : law.FunctionExtensionalityFree) (proofFree : proof.FunctionExtensionalityFree) :
    (truthReflect core proposition point law proof).FunctionExtensionalityFree := by
  simp [truthReflect, separationProperty, ProofSyntax.FunctionExtensionalityFree,
    separation_free, lawFree, proofFree]

theorem truthIntro_nodeCount (proposition : Formula Const Γ)
    (powerLaw : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.powerLaw))
    (separationLaw : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.separationLaw))
    (proof : ProofSyntax Const Δ proposition) :
    (truthIntro core proposition powerLaw separationLaw proof).nodeCount =
      powerLaw.nodeCount + separationLaw.nodeCount + proof.nodeCount + 16 := by
  simp [truthIntro, separationIntro, emptyInPowerEmpty, separation, powerset,
    ProofSyntax.nodeCount, ProofSyntax.observe]
  omega

theorem truthReflect_nodeCount (proposition : Formula Const Γ)
    (point : Term Const Γ ZFSetHenkinInterpretation.set)
    (separationLaw : ProofSyntax Const Δ (lawAt core ZFSetHenkinInterpretation.separationLaw))
    (proof : ProofSyntax Const Δ (member core point (truthCode core proposition))) :
    (truthReflect core proposition point separationLaw proof).nodeCount =
      separationLaw.nodeCount + proof.nodeCount + 9 := by
  simp [truthReflect, separationProperty, separation, ProofSyntax.nodeCount,
    ProofSyntax.observe]
  omega

end Mettapedia.Logic.HOL.SetComprehensionProofs
