import Mettapedia.GSLT.LanguageDef.AdmittedContainerProofControls
import Mettapedia.Logic.HOL.RetainedConstructorProofControls
import Mettapedia.Languages.HOLLight.InterpretedCompilation
import Mettapedia.Tools.StageData

/-!
# Native compilation of complete admitted Vector membership schemas

Finite constructor descriptors and parent evidence are extracted from the
admitted source with checked definitional equality. The explicit interpretation supplies
native arithmetic, element and recursive-space operations. Each schema keeps
its complete child-condition hypothesis; no primitive datatype fact is added.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.AdmittedMembershipCompilation
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open HOL
open Mettapedia.GSLT.LanguageDef
open AdmittedContainerProofControls
open ReverseTranslation

local macro "stageMember% " value:term : term =>
  `(stageValue% [Mettapedia.GSLT.LanguageDef.AdmittedContainerProofControls,
    Mettapedia.GSLT.LanguageDef.AdmittedContainerGeneratedControls,
    Mettapedia.GSLT.LanguageDef.AdmittedContainerPredicateControls,
    Mettapedia.GSLT.LanguageDef.AdmittedContainerProofs,
    Mettapedia.GSLT.LanguageDef.AdmittedContainerPredicate,
    Mettapedia.GSLT.LanguageDef.AdmittedContainerGenerated,
    Mettapedia.GSLT.LanguageDef.AdmittedContainerHOL,
    Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLRealization,
    Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLTerms,
    Mettapedia.GSLT.LanguageDef.IndexedInductiveNatVec,
    Mettapedia.GSLT.LanguageDef.PositiveInductiveBlockBridge,
    Mettapedia.Logic.HOL.IndexedContainerPositionTerms,
    Mettapedia.Logic.HOL.IndexedContainerFieldGuards,
    Mettapedia.Logic.HOL.IndexedConstructorTerms,
    Mettapedia.Logic.HOL.IndexedConstructorGuards,
    Mettapedia.Logic.HOL.ConstructorDataPredicates,
    Mettapedia.Logic.HOL.CurriedPredicates,
    Mettapedia.Logic.HOL.FiniteConstructorEncoding,
    Mettapedia.TypeTheory.IndexedPositiveContainer,
    List, Fin] $value)

def descriptor : HOL.RecursiveSpacePredicate.Contextual AdmittedContainerGeneratedControls.Symbol
    AdmittedContainerProofControls.Open.context :=
  stagedData% (stageMember% AdmittedContainerProofControls.Open.signature)
def rootTerm : HOL.Term AdmittedContainerGeneratedControls.Symbol AdmittedContainerProofControls.Open.context
    (AdmittedContainerGeneratedControls.space ⇒ AdmittedContainerGeneratedControls.number ⇒ .prop) :=
  stagedData% (stageMember% (AdmittedContainerProofControls.Open.sourceInventory.rootProgram AdmittedContainerProofControls.Open.construct))
def tag : HOL.Term AdmittedContainerGeneratedControls.Symbol AdmittedContainerProofControls.Open.context descriptor.number :=
  stagedData% (stageMember% (AdmittedContainerProofControls.Open.numeral AdmittedContainerGeneratedControls.consOccurrence.val))
def data : HOL.Term AdmittedContainerGeneratedControls.Symbol AdmittedContainerProofControls.Open.context descriptor.payload :=
  stagedData% (stageMember% (HOL.IndexedContainerPositionTerms.payloadTerm AdmittedContainerGeneratedControls.reading
    (AdmittedContainerHOL.codes AdmittedContainerGeneratedControls.block AdmittedContainerGeneratedControls.registered)
    AdmittedContainerGeneratedControls.consOccurrence AdmittedContainerProofControls.Open.arguments))
def children : HOL.Term AdmittedContainerGeneratedControls.Symbol AdmittedContainerProofControls.Open.context
    (descriptor.number ⇒ descriptor.space) :=
  stagedData% (stageMember% AdmittedContainerProofControls.Open.children)
def target : HOL.Term AdmittedContainerGeneratedControls.Symbol AdmittedContainerProofControls.Open.context AdmittedContainerGeneratedControls.number :=
  stagedData% (stageMember% AdmittedContainerProofControls.Open.index)
def shapeEvidence : HOL.ProofSyntax AdmittedContainerGeneratedControls.Symbol []
    (descriptor.shapeAt tag data) :=
  stagedData% (stageMember% AdmittedContainerProofControls.Open.parentShape)
def rootEvidence : HOL.ProofSyntax AdmittedContainerGeneratedControls.Symbol []
    (.app (.app rootTerm (descriptor.constructValue tag data children)) target) :=
  stagedData% (stageMember% AdmittedContainerProofControls.Open.parentRoot)

theorem descriptor_source : HEq descriptor AdmittedContainerProofControls.Open.signature :=
  stagedHEq% descriptor, AdmittedContainerProofControls.Open.signature
theorem rootTerm_source : rootTerm = AdmittedContainerProofControls.Open.sourceInventory.rootProgram AdmittedContainerProofControls.Open.construct :=
  eq_of_heq (stagedHEq% rootTerm, (AdmittedContainerProofControls.Open.sourceInventory.rootProgram AdmittedContainerProofControls.Open.construct))
theorem tag_source : tag = AdmittedContainerProofControls.Open.numeral AdmittedContainerGeneratedControls.consOccurrence.val :=
  eq_of_heq (stagedHEq% tag, (AdmittedContainerProofControls.Open.numeral AdmittedContainerGeneratedControls.consOccurrence.val))
theorem data_source : data = HOL.IndexedContainerPositionTerms.payloadTerm AdmittedContainerGeneratedControls.reading
    (AdmittedContainerHOL.codes AdmittedContainerGeneratedControls.block AdmittedContainerGeneratedControls.registered)
    AdmittedContainerGeneratedControls.consOccurrence AdmittedContainerProofControls.Open.arguments :=
  eq_of_heq (stagedHEq% data, (HOL.IndexedContainerPositionTerms.payloadTerm AdmittedContainerGeneratedControls.reading
    (AdmittedContainerHOL.codes AdmittedContainerGeneratedControls.block AdmittedContainerGeneratedControls.registered)
    AdmittedContainerGeneratedControls.consOccurrence AdmittedContainerProofControls.Open.arguments))
theorem children_source : children = AdmittedContainerProofControls.Open.children :=
  eq_of_heq (stagedHEq% children, AdmittedContainerProofControls.Open.children)
theorem target_source : target = AdmittedContainerProofControls.Open.index :=
  eq_of_heq (stagedHEq% target, AdmittedContainerProofControls.Open.index)
theorem rootEvidence_source : HEq rootEvidence AdmittedContainerProofControls.Open.parentRoot :=
  stagedHEq% rootEvidence, AdmittedContainerProofControls.Open.parentRoot
theorem shapeEvidence_free : shapeEvidence.FunctionExtensionalityFree := stagedProof% AdmittedContainerProofControls.Open.parentShape_free
theorem rootEvidence_free : rootEvidence.FunctionExtensionalityFree := stagedProof% AdmittedContainerProofControls.Open.parentRoot_free

private theorem descriptor_fields
    {first second : HOL.RecursiveSpacePredicate.Contextual AdmittedContainerGeneratedControls.Symbol AdmittedContainerProofControls.Open.context}
    (same : first = second) : HEq first.least second.least ∧ HEq first.construct second.construct ∧
      HEq first.active second.active ∧ HEq first.validEdge second.validEdge ∧ HEq first.bottom second.bottom := by
  cases same
  exact ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

private theorem least_source : descriptor.least = AdmittedContainerProofControls.Open.signature.least :=
  eq_of_heq (descriptor_fields (eq_of_heq descriptor_source)).1
private theorem construct_source : descriptor.construct = AdmittedContainerProofControls.Open.construct :=
  eq_of_heq (descriptor_fields (eq_of_heq descriptor_source)).2.1
private theorem active_source : descriptor.active = AdmittedContainerProofControls.Open.signature.active :=
  eq_of_heq (descriptor_fields (eq_of_heq descriptor_source)).2.2.1
private theorem edge_source : descriptor.validEdge = AdmittedContainerProofControls.Open.signature.validEdge :=
  eq_of_heq (descriptor_fields (eq_of_heq descriptor_source)).2.2.2.1
private theorem bottom_source : descriptor.bottom = AdmittedContainerProofControls.Open.bottom :=
  eq_of_heq (descriptor_fields (eq_of_heq descriptor_source)).2.2.2.2

def conditions : HOL.Formula AdmittedContainerGeneratedControls.Symbol AdmittedContainerProofControls.Open.context :=
  descriptor.childConditions descriptor.least data children
def conclusion : HOL.Formula AdmittedContainerGeneratedControls.Symbol AdmittedContainerProofControls.Open.context :=
  .app (.app (descriptor.memberProgram rootTerm) (descriptor.constructValue tag data children)) target

def childPremise : HOL.ProofSyntax AdmittedContainerGeneratedControls.Symbol [conditions] conditions := .hyp ⟨0, by decide⟩
theorem childPremise_free : childPremise.FunctionExtensionalityFree := by
  simp only [childPremise, HOL.ProofSyntax.FunctionExtensionalityFree]

def consProof : HOL.ProofSyntax AdmittedContainerGeneratedControls.Symbol [conditions] conclusion :=
  descriptor.member_intro rootTerm tag data children target
    (shapeEvidence.prepend conditions) childPremise (rootEvidence.prepend conditions)

theorem consProof_free : consProof.FunctionExtensionalityFree := by
  apply HOL.RecursiveSpacePredicate.Contextual.member_intro_free
  · exact (HOL.ProofSyntax.functionExtensionalityFree_mono _ _).mpr shapeEvidence_free
  · exact childPremise_free
  · exact (HOL.ProofSyntax.functionExtensionalityFree_mono _ _).mpr rootEvidence_free

private theorem value_source : descriptor.constructValue tag data children = AdmittedContainerProofControls.Open.value := by
  unfold HOL.RecursiveSpacePredicate.Contextual.constructValue
  rw [construct_source, tag_source, data_source, children_source]
  rfl

private theorem program_source : descriptor.memberProgram rootTerm = AdmittedContainerProofControls.Open.program := by
  unfold HOL.RecursiveSpacePredicate.Contextual.memberProgram CurriedGuardProgramProofs.conjunctionProgram
  rw [least_source, rootTerm_source]
  rfl

theorem cons_conclusion_source : conclusion = .app
    (.app AdmittedContainerProofControls.Open.program AdmittedContainerProofControls.Open.value)
    AdmittedContainerProofControls.Open.index := by
  unfold conclusion
  rw [program_source, value_source, target_source]

theorem cons_hypothesis_source : conditions = AdmittedContainerProofControls.Open.conditions := by
  unfold conditions AdmittedContainerProofControls.Open.conditions HOL.RecursiveSpacePredicate.Contextual.childConditions
  rw [least_source, data_source, children_source, active_source, edge_source, bottom_source]
  rfl

structure Operations where
  number : HOL.Ty AtomicTy
  element : HOL.Ty AtomicTy
  space : HOL.Ty AtomicTy
  zero : HOL.ClosedTerm Symbol number
  successor : HOL.ClosedTerm Symbol (number ⇒ number)
  addition : HOL.ClosedTerm Symbol (number ⇒ number ⇒ number)
  head : HOL.ClosedTerm Symbol element
  bottom : HOL.ClosedTerm Symbol space
  construct : HOL.ClosedTerm Symbol (number ⇒ HOL.FiniteConstructorEncoding.payloadType [[], [number, element]] ⇒
    (number ⇒ space) ⇒ space)

variable (operations : Operations)
def types : AdmittedContainerGeneratedControls.BaseCode → HOL.Ty AtomicTy
  | .number => operations.number
  | .element => operations.element
  | .space => operations.space

def constants : {type : HOL.Ty AdmittedContainerGeneratedControls.BaseCode} →
    AdmittedContainerGeneratedControls.Symbol type → HOL.ClosedTerm Symbol (HOL.Ty.substitute (types operations) type)
  | _, .zero => operations.zero
  | _, .successor => operations.successor
  | _, .addition => operations.addition
  | _, .flagTrue => operations.head
  | _, .bottom => operations.bottom
  | _, .construct => operations.construct

def interpretation : HOL.TermInterpretation AdmittedContainerGeneratedControls.BaseCode
    AdmittedContainerGeneratedControls.Symbol AtomicTy Symbol := ⟨types operations, constants operations⟩

def sourceNames : Naming (AdmittedContainerProofControls.Open.context.map (HOL.Ty.substitute (types operations))) :=
  Naming.cons (.global "__member_children") (Naming.cons (.global "__member_construct")
    (Naming.cons (.global "__member_bottom") (Naming.cons (.global "__member_head")
      (Naming.cons (.global "__member_length") Naming.empty))))

abbrev NativeContext (operations : Operations) :=
  AdmittedContainerProofControls.Open.context.map (HOL.Ty.substitute (interpretation operations).types)

section Parents
variable (callerNames : Naming (NativeContext operations))

@[noinline] opaque compiledParentShape : RetainedCompilation.Compiled (Γ := NativeContext operations) emptyAxiomPolicy callerNames []
    (HOL.ImpredicativeConnectives.expand (Γ := NativeContext operations) (τ := .prop) ((interpretation operations).term
      (Γ := AdmittedContainerProofControls.Open.context) (type := .prop) (descriptor.shapeAt tag data))) :=
  stagedData% (InterpretedCompilation.compile (interpretation operations)
    shapeEvidence shapeEvidence_free callerNames ("admitted-parent-shape", 0))

@[noinline] opaque compiledParentRoot : RetainedCompilation.Compiled (Γ := NativeContext operations) emptyAxiomPolicy callerNames []
    (HOL.ImpredicativeConnectives.expand (Γ := NativeContext operations) (τ := .prop) ((interpretation operations).term
      (Γ := AdmittedContainerProofControls.Open.context) (type := .prop)
      (.app (.app rootTerm (descriptor.constructValue tag data children)) target))) :=
  stagedData% (InterpretedCompilation.compile (interpretation operations)
    rootEvidence rootEvidence_free callerNames ("admitted-parent-root", 0))

def parentShape : RetainedCompilation.CheckedProof emptyAxiomPolicy :=
  (compiledParentShape operations callerNames).proof
def parentRoot : RetainedCompilation.CheckedProof emptyAxiomPolicy :=
  (compiledParentRoot operations callerNames).proof

end Parents

def compiledCons (callerNames : Naming (AdmittedContainerProofControls.Open.context.map (HOL.Ty.substitute (types operations)))) :=
  InterpretedCompilation.compile (interpretation operations) consProof consProof_free callerNames ("admitted-cons-membership", 0)

theorem cons_accepted (callerNames : Naming (AdmittedContainerProofControls.Open.context.map (HOL.Ty.substitute (types operations)))) :
    (ProofSystem.checker emptyAxiomPolicy).check (compiledCons operations callerNames).proof.result
      (compiledCons operations callerNames).proof.certificate = true := (compiledCons operations callerNames).proof.accepted

theorem cons_hypotheses (callerNames : Naming (AdmittedContainerProofControls.Open.context.map (HOL.Ty.substitute (types operations)))) :
    (compiledCons operations callerNames).proof.result.sequent.hyp =
      reverseHypotheses callerNames
        ([AdmittedContainerProofControls.Open.conditions].map (interpretation operations).term |>.map HOL.ImpredicativeConnectives.expand) :=
  by simpa only [cons_hypothesis_source] using (compiledCons operations callerNames).hypotheses_exact

theorem cons_conclusion (callerNames : Naming (AdmittedContainerProofControls.Open.context.map (HOL.Ty.substitute (types operations)))) :
    (compiledCons operations callerNames).proof.result.sequent.concl = reverseCanonical callerNames
      (HOL.ImpredicativeConnectives.expand ((interpretation operations).term
        (.app (.app AdmittedContainerProofControls.Open.program AdmittedContainerProofControls.Open.value)
          AdmittedContainerProofControls.Open.index))) := by
  simpa only [cons_conclusion_source] using (compiledCons operations callerNames).conclusion_exact

def logicalInterpretation : HOL.TermInterpretation Unit HOL.RetainedConstructorProofControls.Symbol AtomicTy Symbol where
  types _ := .prop
  constants := fun {_} impossible => nomatch impossible

def compiledSeparation (origin : String) := InterpretedCompilation.compile logicalInterpretation
  HOL.RetainedConstructorProofControls.Payload.nullarySeparation
  HOL.RetainedConstructorProofControls.Payload.nullarySeparation_free Naming.empty (origin, 0)

def logicalNames : Naming [.prop, .prop, .prop, .prop] :=
  Naming.cons (.global "__field_a") (Naming.cons (.global "__field_b")
    (Naming.cons (.global "__field_c") (Naming.cons (.global "__field_d") Naming.empty)))

def compiledReadout (callerNames : Naming [.prop, .prop, .prop, .prop]) := InterpretedCompilation.compile logicalInterpretation
  HOL.RetainedConstructorProofControls.Payload.programReadout
  HOL.RetainedConstructorProofControls.Payload.programReadout_free callerNames ("constructor-program-readout", 0)

def compiledTelescope (origin : String) := InterpretedCompilation.compile logicalInterpretation
  HOL.RetainedConstructorProofControls.Telescope.eliminated
  HOL.RetainedConstructorProofControls.Telescope.eliminated_free Naming.empty (origin, 0)

def indexedNames : Naming [.prop, .prop, .prop ⇒ .prop ⇒ .prop, .prop ⇒ .prop ⇒ .prop] :=
  Naming.cons (.global "__point") (Naming.cons (.global "__index")
    (Naming.cons (.global "__root") (Naming.cons (.global "__motive") Naming.empty)))

def compiledIndexed (callerNames : Naming [.prop, .prop, .prop ⇒ .prop ⇒ .prop, .prop ⇒ .prop ⇒ .prop]) :=
  InterpretedCompilation.compile logicalInterpretation HOL.RetainedConstructorProofControls.Indexed.atTarget
    HOL.RetainedConstructorProofControls.Indexed.atTarget_free callerNames ("indexed-motive-target", 0)

#print axioms cons_conclusion_source
#print axioms cons_accepted
#print axioms cons_hypotheses
end Mettapedia.Languages.HOLLight.AdmittedMembershipCompilation
