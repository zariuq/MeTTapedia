import Mettapedia.Languages.HOLLight.AdmittedNonbottomCompilation
import Mettapedia.Logic.HOL.IndexedConstructorNonbottom
import Mettapedia.Logic.HOL.ContextualInductionSchema

/-!
# A constructor method compiled with an abstract child condition

The finite source inventory supplies the original field cases and result
indices. The child condition is a parameter, and membership in the whole
family is not an ambient hypothesis. Specialization supplies the actual
recursive child condition before the method is closed and joined to induction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.AdmittedConstructorMethodCompilation

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open HOL Mettapedia.GSLT.LanguageDef

abbrev number := AdmittedContainerGeneratedControls.number
abbrev space := AdmittedContainerGeneratedControls.space
abbrev payload := FiniteConstructorEncoding.payloadType AdmittedNonbottomCompilation.constructors.fields
abbrev context : Ctx AdmittedContainerGeneratedControls.BaseCode :=
  (payload ⇒ .prop) :: (number ⇒ space) :: payload :: number :: AdmittedNonbottomCompilation.inputContext

def scope : HOL.Subst AdmittedContainerGeneratedControls.Symbol AdmittedNonbottomCompilation.inputContext context :=
  Subst.ofRename (fun index => .vs (.vs (.vs (.vs index))))

def constructors := AdmittedNonbottomCompilation.constructors.subst scope

def construct : HOL.Term AdmittedContainerGeneratedControls.Symbol context
    (number ⇒ payload ⇒ (number ⇒ space) ⇒ space) := .const .construct
def bottom : HOL.Term AdmittedContainerGeneratedControls.Symbol context space := .const .bottom
def tag : HOL.Term AdmittedContainerGeneratedControls.Symbol context number := .var (.vs (.vs (.vs .vz)))
def data : HOL.Term AdmittedContainerGeneratedControls.Symbol context payload := .var (.vs (.vs .vz))
def children : HOL.Term AdmittedContainerGeneratedControls.Symbol context (number ⇒ space) := .var (.vs .vz)
def condition : HOL.Term AdmittedContainerGeneratedControls.Symbol context (payload ⇒ .prop) := .var .vz
def property : HOL.Term AdmittedContainerGeneratedControls.Symbol context (space ⇒ constructors.index ⇒ .prop) :=
  ConstructorNonbottom.motive bottom constructors.index
def shape : HOL.Formula AdmittedContainerGeneratedControls.Symbol context :=
  .app (.app constructors.shapeProgram tag) data
def child : HOL.Formula AdmittedContainerGeneratedControls.Symbol context := .app condition data
def assumptions : List (HOL.Formula AdmittedContainerGeneratedControls.Symbol context) :=
  [child, shape, ConstructorInjectivity.statement construct, ConstructorNonbottom.separation construct bottom]
def conclusion : HOL.Formula AdmittedContainerGeneratedControls.Symbol context :=
  .app (IndexedPredicateInduction.lift (constructors.rootProgram construct) property)
    (.app (.app (.app construct tag) data) children)

def separation : ProofSyntax AdmittedContainerGeneratedControls.Symbol assumptions
    (ConstructorNonbottom.separation construct bottom) := .hyp ⟨3, by simp [assumptions]⟩

def cases : constructors.IndexedCases construct children condition property assumptions :=
  constructors.nonbottomIndexedCases bottom construct children condition separation

theorem cases_free {Ξ : Ctx AdmittedContainerGeneratedControls.BaseCode}
    (images : HOL.Subst AdmittedContainerGeneratedControls.Symbol context Ξ) occurrence arguments :
    (cases images occurrence arguments).FunctionExtensionalityFree :=
  constructors.nonbottomIndexedCases_free bottom construct children condition separation trivial images occurrence arguments

def proof : ProofSyntax AdmittedContainerGeneratedControls.Symbol assumptions conclusion :=
  constructors.constructorCases_lift construct tag data children condition property cases
    (.hyp ⟨2, by simp [assumptions]⟩) (.hyp ⟨1, by simp [assumptions]⟩) (.hyp ⟨0, by simp [assumptions]⟩)

theorem proof_free : proof.FunctionExtensionalityFree :=
  constructors.constructorCases_lift_free construct tag data children condition property cases _ _ _
    cases_free trivial trivial trivial

def closedAssumptions : List (HOL.Formula AdmittedContainerGeneratedControls.Symbol
    AdmittedNonbottomCompilation.inputContext) :=
  [AdmittedContainerInductionControls.injectivity, AdmittedContainerInductionControls.separation]

def closedConclusion : HOL.Formula AdmittedContainerGeneratedControls.Symbol
    AdmittedNonbottomCompilation.inputContext :=
  .all (.all (.all (.all (.imp shape (.imp child conclusion)))))

def closedProof : ProofSyntax AdmittedContainerGeneratedControls.Symbol closedAssumptions closedConclusion := by
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  apply ProofSyntax.impI
  apply ProofSyntax.castIndices ?_ rfl proof
  rfl

theorem closedProof_free : closedProof.FunctionExtensionalityFree := by
  unfold closedProof
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact proof_free

def family : RecursiveSpacePredicate.Contextual AdmittedContainerGeneratedControls.Symbol
    AdmittedNonbottomCompilation.inputContext :=
  AdmittedNonbottomCompilation.positions.contextual AdmittedNonbottomCompilation.bottom
    AdmittedNonbottomCompilation.constructor

def lifted : HOL.Term AdmittedContainerGeneratedControls.Symbol AdmittedNonbottomCompilation.inputContext
    (space ⇒ .prop) :=
  IndexedPredicateInduction.lift
    (AdmittedNonbottomCompilation.constructors.rootProgram AdmittedNonbottomCompilation.constructor)
    (ConstructorNonbottom.motive AdmittedNonbottomCompilation.bottom AdmittedNonbottomCompilation.constructors.index)

theorem closedConclusion_source : closedConclusion = family.parametricMethod lifted := by
  have shapeSame : constructors.shapeProgram = HOL.subst scope AdmittedNonbottomCompilation.constructors.shapeProgram :=
    (AdmittedNonbottomCompilation.constructors.shapeProgram_subst scope).symm
  have constructSame : HOL.subst scope AdmittedNonbottomCompilation.constructor = construct := rfl
  have rootSame : constructors.rootProgram construct =
      HOL.subst scope (AdmittedNonbottomCompilation.constructors.rootProgram AdmittedNonbottomCompilation.constructor) := by
    simpa only [constructors, constructSame] using
      (AdmittedNonbottomCompilation.constructors.rootProgram_subst AdmittedNonbottomCompilation.constructor scope).symm
  have propertySame : property = HOL.subst scope
      (ConstructorNonbottom.motive AdmittedNonbottomCompilation.bottom AdmittedNonbottomCompilation.constructors.index) := by
    rw [ConstructorNonbottom.subst_motive]
    rfl
  have liftSame : IndexedPredicateInduction.lift (constructors.rootProgram construct) property =
      HOL.subst scope lifted := by
    rw [rootSame, propertySame, ← IndexedPredicateInduction.subst_lift]
    rfl
  unfold closedConclusion shape child conclusion
  rw [shapeSame, liftSame]
  simp only [family, RecursiveSpacePredicate.Contextual.parametricMethod,
    RecursiveSpacePredicate.Contextual.constructorScope, RecursiveSpacePredicate.Contextual.constructorTag,
    RecursiveSpacePredicate.Contextual.constructorPayload, RecursiveSpacePredicate.Contextual.constructorChildren,
    RecursiveSpacePredicate.Contextual.constructorRenaming,
    RecursiveSpacePredicate.Contextual.shapeAt, RecursiveSpacePredicate.Contextual.constructValue,
    RecursiveSpacePredicate.Contextual.subst, IndexedConstructorGuards.PositionPrograms.contextual,
    scope, subst_ofRename, weaken, HOL.rename, Rename.weaken, rename_comp, construct,
    AdmittedNonbottomCompilation.constructor, AdmittedNonbottomCompilation.constructors, tag, data, children, condition]

variable (operations : AdmittedMembershipCompilation.Operations)

def names (prefixName : String) : ReverseTranslation.Naming
    (context.map (HOL.Ty.substitute (AdmittedMembershipCompilation.interpretation operations).types)) :=
  ReverseTranslation.Naming.cons (.global (prefixName ++ "_condition"))
    (ReverseTranslation.Naming.cons (.global (prefixName ++ "_children"))
      (ReverseTranslation.Naming.cons (.global (prefixName ++ "_payload"))
        (ReverseTranslation.Naming.cons (.global (prefixName ++ "_tag"))
          (ReverseTranslation.Naming.cons (.global (prefixName ++ "_index"))
            (ReverseTranslation.Naming.cons (.global (prefixName ++ "_value")) ReverseTranslation.Naming.empty)))))

@[irreducible, noinline] def compile (prefixName : String) :=
  InterpretedCompilation.compile (AdmittedMembershipCompilation.interpretation operations)
    proof proof_free (names operations prefixName) ("admitted-constructor-method", 0)

def closedNames (prefixName : String) : ReverseTranslation.Naming
    (AdmittedNonbottomCompilation.inputContext.map
      (HOL.Ty.substitute (AdmittedMembershipCompilation.interpretation operations).types)) :=
  ReverseTranslation.Naming.cons (.global (prefixName ++ "_index"))
    (ReverseTranslation.Naming.cons (.global (prefixName ++ "_value")) ReverseTranslation.Naming.empty)

@[irreducible, noinline] def compileClosed (prefixName : String) :=
  InterpretedCompilation.compile (AdmittedMembershipCompilation.interpretation operations)
    closedProof closedProof_free (closedNames operations prefixName) ("admitted-closed-constructor-method", 0)

#print axioms cases_free
#print axioms proof_free
#print axioms compile
#print axioms closedProof_free
#print axioms compileClosed

end Mettapedia.Languages.HOLLight.AdmittedConstructorMethodCompilation
