import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.CodedHOL
import Mettapedia.Logic.HOL.SetComprehensionProofs
import Mettapedia.Logic.HOL.DefinitionHistoryProofConservativity

/-!
# Expanding coded truth into material sets, with retained proofs

The truth-code symbol expands to separation of the canonical singleton. The
expansion preserves the denotation of every generated term and judgment in
the independently constructed set model. Introduction and reflection below
produce HOL proof syntax from the existing powerset and separation laws.

This is the proof-irrelevant set reading of identity, not reflection of
intensional source equality. Trace operations and universe laws still need
their own retained derivations for a complete source-proof translation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.CodedHOL
namespace TruthProofs
open Mettapedia.Logic Mettapedia.Logic.HOL
open Presentation TypedEquality.Annotated
open HOL.Embedding
open SetComprehensionProofs (Core)
universe u
variable {Head : Type}

def core : Core (Symbol Head) := Symbol.core

def body : ClosedTerm (Symbol Head) (.prop ⇒ object) :=
  .lam (SetComprehensionProofs.truthCode core (.var .vz))

/-- A fresh name for the body is an ordinary acyclic HOL definition. -/
def definition : DefinitionHistory (Symbol Head) (DefinedConst (Symbol Head) (.prop ⇒ object)) :=
  .add .nil (.prop ⇒ object) body

def images : {type : Ty Unit} → Symbol Head type → ClosedTerm (Symbol Head) type
  | _, .truth => body
  | _, symbol => .const symbol

def expand {Γ : Ctx Unit} {type : Ty Unit} (term : Term (Symbol Head) Γ type) :=
  HOL.substConst images term

private theorem powerEmpty : ZFSet.powerset (∅ : ZFSet.{u}) = {∅} := by
  apply ZFSet.ext
  intro x
  rw [ZFSet.mem_powerset, ZFSet.mem_singleton]
  constructor
  · intro included
    apply ZFSet.ext
    intro y
    constructor
    · intro hy
      exact False.elim (ZFSet.notMem_empty y (included hy))
    · intro hy
      exact False.elim (ZFSet.notMem_empty y hy)
  · rintro rfl
    exact ZFSet.empty_subset _

variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})

theorem denote_truthCode {Γ : Ctx Unit} (proposition : Formula (Symbol Head) Γ)
    (valuation : (model heads constants).Valuation Γ) :
    (model heads constants).denote (SetComprehensionProofs.truthCode core proposition) valuation =
      ZFSetTraceProofDecoding.truthCode ((model heads constants).denote proposition valuation).down := by
  change ZFSet.sep (fun point =>
    ((model heads constants).denote (HOL.weaken proposition)
      ((model heads constants).extend (σ := object) valuation point)).down)
      (ZFSet.powerset ∅) = _
  simp_rw [HOL.Soundness.denote_weaken]
  rw [powerEmpty]
  rfl

theorem images_agree {type : Ty Unit} (symbol : Symbol Head type) :
    (model heads constants).denote (images symbol) (fun index => nomatch index) =
      (model heads constants).constDen symbol := by
  cases symbol <;> try rfl
  funext proposition
  exact denote_truthCode heads constants (.var .vz) _

/-- This covers every HOL term, including formulas, not just source images. -/
theorem denote_expand {Γ : Ctx Unit} {type : Ty Unit} (term : Term (Symbol Head) Γ type)
    (valuation : (model heads constants).Valuation Γ) :
    (model heads constants).denote (expand term) valuation =
      (model heads constants).denote term valuation :=
  HenkinModel.denote_substConst_of_constantAgreement images (model heads constants)
    (fun {type} symbol =>
      (HenkinModel.denote_closed_valuation_eq (model heads constants) (images symbol) _ _).trans
        (images_agree heads constants (type := type) symbol)) term valuation

theorem denote_expand_readAt {n : Nat} {Γ : Ctx Unit} (source : CTm Head n)
    (bound : Fin n → Term (Symbol Head) Γ object)
    (valuation : (model heads constants).Valuation Γ) :
    (model heads constants).denote (expand (AnnotatedCodedReading.readAt operations bound source)) valuation =
      ev heads constants source (fun i => (model heads constants).denote (bound i) valuation) :=
  (denote_expand heads constants _ valuation).trans (denote_readAt heads constants source bound valuation)

variable {Γ : Ctx Unit} {Δ : List (Formula (Symbol Head) Γ)}

theorem weaken_body (context : Ctx Unit) :
    HOL.weakenCtx context (body : ClosedTerm (Symbol Head) (.prop ⇒ object)) =
      .lam (SetComprehensionProofs.truthCode core (.var .vz)) := by
  induction context with
  | nil => rfl
  | cons type context ih => rw [HOL.weakenCtx_cons, ih]; rfl

/-- The expansion has an actual beta-conversion receipt at every context. -/
def application (proposition : Formula (Symbol Head) Γ) :
    ProofSyntax (Symbol Head) Δ (.eq (.app (HOL.weakenCtx Γ body) proposition)
      (SetComprehensionProofs.truthCode core proposition)) := by
  apply ProofSyntax.castIndices rfl ?_
    (ProofSyntax.beta proposition (SetComprehensionProofs.truthCode core (.var .vz)))
  simp only [weaken_body]
  rfl

def reflexivityAt {n : Nat} (type source : CTm Head n)
    (bound : Fin n → Term (Symbol Head) Γ object)
    (powerLaw : ProofSyntax (Symbol Head) Δ
      (SetComprehensionProofs.lawAt core ZFSetHenkinInterpretation.powerLaw))
    (separationLaw : ProofSyntax (Symbol Head) Δ
      (SetComprehensionProofs.lawAt core ZFSetHenkinInterpretation.separationLaw)) :
    ProofSyntax (Symbol Head) Δ
      (memberAt (expand (AnnotatedCodedReading.readAt operations bound (.refl source)))
        (expand (AnnotatedCodedReading.readAt operations bound (.id type source source)))) := by
  let point := expand (AnnotatedCodedReading.readAt operations bound source)
  have equality := application (Δ := Δ) (.eq point point)
  have codeProof := SetComprehensionProofs.identityIntro core point powerLaw separationLaw
  have membership := ProofSyntax.eqAppArg
    (.app (.const (.core .member)) (.const (.core .empty))) equality
  apply ProofSyntax.castIndices rfl ?_ (.impE (.eqPropER membership) codeProof)
  simp only [point, memberAt, expand, AnnotatedCodedReading.readAt, operations,
    HOL.weakenCtx_const, HOL.substConst, images]

/-- This is the exact expanded target judgment, including its original
source-context guard. It constructs a retained proof of the reflexivity
rule's conclusion; it is not the interpreter for the other source rules. -/
def reflexivityJudgment {n : Nat} (context : CCtx Head n) (type source : CTm Head n)
    (bound : Fin n → Term (Symbol Head) Γ object)
    (powerLaw : ProofSyntax (Symbol Head) Δ
      (SetComprehensionProofs.lawAt core ZFSetHenkinInterpretation.powerLaw))
    (separationLaw : ProofSyntax (Symbol Head) Δ
      (SetComprehensionProofs.lawAt core ZFSetHenkinInterpretation.separationLaw)) :
    ProofSyntax (Symbol Head) Δ (expand (judgmentAt (.typing context (.refl source)
      (.id type source source)) bound)) := by
  let guard := expand (contextAt context bound)
  apply ProofSyntax.castIndices rfl ?_
    (ProofSyntax.impI (reflexivityAt type source bound
      (powerLaw.prepend guard) (separationLaw.prepend guard)))
  simp only [guard, judgmentAt, statementContext, statementAt, expand, HOL.substConst,
    memberAt, images, HOL.weakenCtx_const]

theorem reflexivityAt_free {n : Nat} (type source : CTm Head n)
    (bound : Fin n → Term (Symbol Head) Γ object)
    (powerLaw : ProofSyntax (Symbol Head) Δ
      (SetComprehensionProofs.lawAt core ZFSetHenkinInterpretation.powerLaw))
    (separationLaw : ProofSyntax (Symbol Head) Δ
      (SetComprehensionProofs.lawAt core ZFSetHenkinInterpretation.separationLaw))
    (powerFree : powerLaw.FunctionExtensionalityFree)
    (separationFree : separationLaw.FunctionExtensionalityFree) :
    (reflexivityAt type source bound powerLaw separationLaw).FunctionExtensionalityFree := by
  simp only [reflexivityAt, ProofSyntax.functionExtensionalityFree_castIndices,
    ProofSyntax.FunctionExtensionalityFree]
  constructor
  · simp [application, ProofSyntax.FunctionExtensionalityFree]
  · exact SetComprehensionProofs.truthIntro_free _ _ _ _ _ powerFree separationFree trivial

theorem reflexivityJudgment_free {n : Nat} (context : CCtx Head n) (type source : CTm Head n)
    (bound : Fin n → Term (Symbol Head) Γ object)
    (powerLaw : ProofSyntax (Symbol Head) Δ
      (SetComprehensionProofs.lawAt core ZFSetHenkinInterpretation.powerLaw))
    (separationLaw : ProofSyntax (Symbol Head) Δ
      (SetComprehensionProofs.lawAt core ZFSetHenkinInterpretation.separationLaw))
    (powerFree : powerLaw.FunctionExtensionalityFree)
    (separationFree : separationLaw.FunctionExtensionalityFree) :
    (reflexivityJudgment context type source bound powerLaw separationLaw).FunctionExtensionalityFree := by
  simp only [reflexivityJudgment, ProofSyntax.functionExtensionalityFree_castIndices,
    ProofSyntax.FunctionExtensionalityFree]
  apply reflexivityAt_free <;> simp [ProofSyntax.prepend, powerFree, separationFree]

def identityRefl {n : Nat} (source : CTm Head n)
    (bound : Fin n → Term (Symbol Head) Γ object)
    (powerLaw : ProofSyntax (Symbol Head) Δ
      (SetComprehensionProofs.lawAt core ZFSetHenkinInterpretation.powerLaw))
    (separationLaw : ProofSyntax (Symbol Head) Δ
      (SetComprehensionProofs.lawAt core ZFSetHenkinInterpretation.separationLaw)) :
    ProofSyntax (Symbol Head) Δ (memberAt (.const (.core .empty))
      (SetComprehensionProofs.truthCode core (.eq
        (AnnotatedCodedReading.readAt operations bound source)
        (AnnotatedCodedReading.readAt operations bound source)))) :=
  SetComprehensionProofs.identityIntro core _ powerLaw separationLaw

def identityReflect (left right witness : Term (Symbol Head) Γ object)
    (separationLaw : ProofSyntax (Symbol Head) Δ
      (SetComprehensionProofs.lawAt core ZFSetHenkinInterpretation.separationLaw))
    (proof : ProofSyntax (Symbol Head) Δ
      (memberAt witness (SetComprehensionProofs.truthCode core (.eq left right)))) :
    ProofSyntax (Symbol Head) Δ (.eq left right) :=
  SetComprehensionProofs.identityReflect core left right witness separationLaw proof

theorem expand_subst {Ξ : Ctx Unit} {type : Ty Unit}
    (substitution : HOL.Subst (Symbol Head) Γ Ξ) (term : Term (Symbol Head) Γ type) :
    expand (HOL.subst substitution term) =
      HOL.subst (fun index => expand (substitution index)) (expand term) :=
  (HOL.substConst_subst images substitution term).symm

end TruthProofs
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.CodedHOL
