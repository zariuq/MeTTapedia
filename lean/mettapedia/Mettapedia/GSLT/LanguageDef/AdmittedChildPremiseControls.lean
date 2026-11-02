import Mettapedia.Logic.HOL.OrderedConstructorChildExistence
import Mettapedia.GSLT.LanguageDef.AdmittedContainerInductionControls
import Mettapedia.Tools.StageData

/-!
# Original admitted Vector child-premise construction

The original Cons description supplies its actual field guard and child
position. Its strengthened child condition and Peano facts remain explicit
premises. Lookup, child membership and the non-bottom motive are retained
under one slot witness, with an open child-array variable.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.AdmittedChildPremiseControls

open Mettapedia.Logic Mettapedia.Logic.HOL
open IndexedContainerPositionTerms FiniteConstructorEncoding CurriedPredicates
open IndexedConstructorGuards OrderedPositionPrograms SuccessorOrder
open AdmittedContainerHOL AdmittedContainerGeneratedControls
open AdmittedContainerInductionControls (initial num ctor bottom motive)

noncomputable section

abbrev context : Ctx BaseCode := [number ⇒ space]
def zero : ClosedTerm Symbol number := .const .zero
def successor : ClosedTerm Symbol (number ⇒ number) := .const .successor
def one : Term Symbol context number := .app (weakenCtx context successor) (weakenCtx context zero)
def constructors := inventory block registered guards (initial (Γ := context)) num
def plans := FieldGuards.plans (reading := reading) (codes block registered) (initial (Γ := context))
def positions := PositionPrograms.ofSegments constructors zero successor plans
def signature := positions.contextual (bottom (Γ := context)) ctor
def sourceArguments : Arguments Symbol context
    (reading.fields (codeAt reading (codes block registered) consOccurrence)) :=
  (.const .zero, .const .flagTrue, PUnit.unit)
def arguments := inventoryArguments reading (codes block registered) consOccurrence sourceArguments
def children : Term Symbol context (number ⇒ space) := .var .vz
def target : Term Symbol context number := .const .zero
def conditions : Formula Symbol context := signature.childConditions
  (PredicateFixedPoint.intersection signature.least (IndexedPredicateInduction.lift (constructors.rootProgram ctor) motive))
  (encode constructors.fields consOccurrence arguments) children
def assumptions : List (Formula Symbol context) :=
  [conditions, NaturalNumeralProofs.separation (weakenCtx context zero) (weakenCtx context successor),
    NaturalNumeralProofs.injectivity (weakenCtx context successor),
    NaturalRecursionProofs.inductionPrinciple (weakenCtx context zero) (weakenCtx context successor)]
def peano : PeanoEvidence successor zero assumptions where
  separation := .hyp (Δ := assumptions) ⟨1, by decide⟩
  injectivity := .hyp (Δ := assumptions) ⟨2, by decide⟩
  induction := .hyp (Δ := assumptions) ⟨3, by decide⟩

def fields : guards.Evidence assumptions
    (codeAt reading (codes block registered) consOccurrence) initial sourceArguments :=
  ⟨.impE (.eqPropER (.beta _ _)) .topI, .impE (.eqPropER (.beta _ _)) .topI, PUnit.unit⟩

def allowed : ProofSyntax Symbol assumptions
    (applyArguments _ (constructors.allowed consOccurrence) arguments) :=
  guards.inventoryFieldProof (codes block registered) initial num consOccurrence sourceArguments fields

def fieldIndex : Term Symbol context number :=
  applyFields _ ((plans consOccurrence).get ⟨0, by decide⟩).2 arguments

def sourceIndexApplication : Term Symbol context number :=
  .app (.app (.lam (.lam (.var (.vs .vz)))) target) (.const .flagTrue)

theorem fieldIndex_source : fieldIndex = sourceIndexApplication :=
  eq_of_heq (stagedHEq% fieldIndex, sourceIndexApplication)

def indexBeta : ProofSyntax Symbol assumptions (.eq fieldIndex target) :=
  ProofSyntax.castIndices rfl (congrArg (fun term => Term.eq term target) fieldIndex_source.symm)
    (show ProofSyntax Symbol assumptions (.eq sourceIndexApplication target) from
      CurriedGuardProgramProofs.beta2 (.var (.vs .vz)) target (.const .flagTrue))

theorem indexBeta_free : indexBeta.FunctionExtensionalityFree := by
  unfold indexBeta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact CurriedGuardProgramProofs.beta2_free _ _ _

def countBeta : ProofSyntax Symbol assumptions (.eq
    (applyFields _ ((plans consOccurrence).get ⟨0, by decide⟩).1 arguments) one) := by
  apply ProofSyntax.castIndices rfl ?_
    (CurriedGuardProgramProofs.beta2 (weaken (weaken one)) target (.const .flagTrue))
  rfl

theorem countBeta_free : countBeta.FunctionExtensionalityFree := by
  unfold countBeta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact CurriedGuardProgramProofs.beta2_free _ _ _

def related : ProofSyntax Symbol assumptions
    (applyArguments _ (.app (.app (fieldGraph zero successor _ (plans consOccurrence)) target) target) arguments) := by
  apply ProofSyntax.impE (.eqPropER (fieldGraph_beta zero successor _ (plans consOccurrence) target target arguments))
  apply compileAt_here
  · exact .impE (.eqPropER (.eqAppArg (.app (weakenCtx context (less successor)) target) countBeta))
      (lessNext successor target)
  · apply ProofSyntax.eqSymm
    apply ProofSyntax.castIndices rfl ?_ indexBeta
    exact stagedProof% (Eq.refl (Term.eq fieldIndex target))

theorem related_free : related.FunctionExtensionalityFree := by
  unfold related
  constructor
  · exact fieldGraph_beta_free _ _ _ _ _ _ _
  · apply compileAt_here_free
    · exact ⟨countBeta_free, lessNext_free _ _⟩
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      exact indexBeta_free

theorem peano_free : peano.Free := by
  simp only [PeanoEvidence.Free, peano, ProofSyntax.FunctionExtensionalityFree, and_self]

theorem fields_free : guards.EvidenceFree assumptions
    (codeAt reading (codes block registered) consOccurrence) initial sourceArguments fields := by
  change _ ∧ _ ∧ True
  simp only [fields, ProofSyntax.FunctionExtensionalityFree, and_self]

theorem allowed_free : allowed.FunctionExtensionalityFree :=
  guards.inventoryFieldProof_free (codes block registered) initial num consOccurrence sourceArguments fields fields_free

def conditionProof : ProofSyntax Symbol assumptions conditions := .hyp ⟨0, by decide⟩

theorem conditionProof_free : conditionProof.FunctionExtensionalityFree := by
  simp only [conditionProof, ProofSyntax.FunctionExtensionalityFree]

def selectedChild := PositionPrograms.childAtFromLookup constructors zero successor plans bottom ctor motive
  consOccurrence arguments children target target peano conditionProof allowed related

theorem selectedChild_free : selectedChild.FunctionExtensionalityFree :=
  PositionPrograms.childAtFromLookup_free constructors zero successor plans bottom ctor motive
    consOccurrence arguments children target target peano conditionProof allowed related
    peano_free conditionProof_free allowed_free related_free

def positionExists := PositionPrograms.originalLookupExistsFromPlan constructors zero successor plans
  consOccurrence arguments target
  (lookupExists_intro zero successor (fieldTerms _ (plans consOccurrence) Subst.id arguments) Subst.id target target
    (.impE (.eqPropEL (fieldGraph_beta zero successor _ (plans consOccurrence) target target arguments)) related))

theorem positionExists_free : positionExists.FunctionExtensionalityFree := by
  apply PositionPrograms.originalLookupExistsFromPlan_free
  apply lookupExists_intro_free
  exact ⟨fieldGraph_beta_free _ _ _ _ _ _ _, related_free⟩

def selectedChildExists := PositionPrograms.originalChildExistsFromLookup constructors zero successor plans bottom ctor motive
  consOccurrence arguments children target peano conditionProof allowed positionExists

theorem selectedChildExists_free : selectedChildExists.FunctionExtensionalityFree :=
  PositionPrograms.originalChildExistsFromLookup_free constructors zero successor plans bottom ctor motive
    consOccurrence arguments children target peano conditionProof allowed positionExists
    peano_free conditionProof_free allowed_free positionExists_free

def selectedNonbottom : ProofSyntax Symbol assumptions (.not (.eq (.app children target) bottom)) :=
  .impE (.eqPropEL (AdmittedContainerInductionControls.motive_beta (.app children target) target))
    (.andER (.andER selectedChild))

theorem selectedNonbottom_free : selectedNonbottom.FunctionExtensionalityFree :=
  ⟨AdmittedContainerInductionControls.motive_beta_free _ _, selectedChild_free⟩

#print axioms selectedChild_free
#print axioms selectedChildExists_free
#print axioms selectedNonbottom_free

end
end Mettapedia.GSLT.LanguageDef.AdmittedChildPremiseControls
