import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.PacketQuotationExtensions

/-!
# Constructor results for checked type-definition quotation

Sorting is discharged by its existing correctness law. The output data is
the existing context extension and source equation construction; the theorem
relates this materialized result to the original admission function.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.PacketQuotationTypeDefinitions

open Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open DefinitionAdapters SignatureFormation

theorem sorted_global_parameters (source : SourceTerm) (names : List String)
    (distinct : names.Nodup) (ordered : names.Pairwise (· ≤ ·))
    (support : (names.map Name.global).toFinset = (source.toDB []).typeVariables) :
    sortedParameters source = names.map Name.global := by
  have sorted := List.mergeSort_eq_self (· ≤ ·) ordered
  simpa only [sorted] using (sortedParameters_of_global_strings source names distinct support).symm

def core (context : TheoryContext) (request : TypeOperatorDefinitionRequest)
    (predicate witness : CanonicalTerm)
    (application : CanonicalTerm.ApplicationSemantics predicate witness request.existence.sequent.concl)
    (bool : request.existence.sequent.concl.IsBool)
    (function : context.signature.typeOperators TypeOp.function = some 2)
    (carrier : TypeFormed context.signature witness.ty)
    (fresh : TypeNamesFresh context.names request) : ContextTypeDefinitionResult :=
  { context := context.typeDefinitionExtension request witness.ty function carrier fresh
    predicate := predicate
    witness := witness
    output := makeTypeOperatorDefinition request predicate witness application bool }

def materialized (context : TheoryContext) (request : TypeOperatorDefinitionRequest)
    (predicate witness : CanonicalTerm)
    (application : CanonicalTerm.ApplicationSemantics predicate witness request.existence.sequent.concl)
    (bool : request.existence.sequent.concl.IsBool)
    (function : context.signature.typeOperators TypeOp.function = some 2)
    (carrier : TypeFormed context.signature witness.ty)
    (fresh : TypeNamesFresh context.names request) : SourceTypeDefinitionResult :=
  ⟨core context request predicate witness application bool function carrier fresh,
    makePointwiseTypeOperatorDefinition request predicate witness application bool⟩

theorem core_admitted (context : TheoryContext) (instances : InstanceWitnesses)
    (request : TypeOperatorDefinitionRequest) (predicate witness : CanonicalTerm)
    (application : CanonicalTerm.ApplicationSemantics predicate witness request.existence.sequent.concl)
    (bool : request.existence.sequent.concl.IsBool)
    (function : context.signature.typeOperators TypeOp.function = some 2)
    (carrier : TypeFormed context.signature witness.ty)
    (fresh : TypeNamesFresh context.names request)
    (inputs : annotationsFormedB context.signature instances predicate.term = true ∧
      annotationsFormedB context.signature instances witness.term = true)
    (sourceChecked : request.predicateSource.check = some predicate)
    (empty : request.existence.sequent.hyp = ∅)
    (closed : predicate.term.HasNoFreeVariables)
    (distinct : request.typeVariables.Nodup)
    (support : request.typeVariables.toFinset = predicate.term.typeVariables)
    (sorted : request.typeVariables = sortedParameters request.predicateSource) :
    admitTypeInTheory context instances request =
      some (core context request predicate witness application bool function carrier fresh) := by
  rw [admitTypeInTheory_eq_fromApplication _ _ _ _ _ application]
  have represented := (typeFormedB_eq_true_iff context.signature witness.ty).mpr carrier
  have checked := checkTypeOperatorDefinition_eq_make request predicate witness application bool
    sourceChecked empty closed distinct support
  have names : TypeNamesFresh context.names request ∧
      request.typeVariables = sortedParameters request.predicateSource := ⟨fresh, sorted⟩
  simp only [admitTypeInTheoryFromApplication, if_pos inputs, dif_pos represented,
    dif_pos function, dif_pos fresh, admitType, if_pos names, checked]
  rfl

theorem materialized_admitted (context : TheoryContext) (instances : InstanceWitnesses)
    (request : TypeOperatorDefinitionRequest) (predicate witness : CanonicalTerm)
    (application : CanonicalTerm.ApplicationSemantics predicate witness request.existence.sequent.concl)
    (bool : request.existence.sequent.concl.IsBool)
    (function : context.signature.typeOperators TypeOp.function = some 2)
    (carrier : TypeFormed context.signature witness.ty)
    (fresh : TypeNamesFresh context.names request)
    (inputs : annotationsFormedB context.signature instances predicate.term = true ∧
      annotationsFormedB context.signature instances witness.term = true)
    (sourceChecked : request.predicateSource.check = some predicate)
    (empty : request.existence.sequent.hyp = ∅)
    (closed : predicate.term.HasNoFreeVariables)
    (distinct : request.typeVariables.Nodup)
    (support : request.typeVariables.toFinset = predicate.term.typeVariables)
    (sorted : request.typeVariables = sortedParameters request.predicateSource) :
    admitSourceTypeInTheory context instances request =
      some (materialized context request predicate witness application bool function carrier fresh) := by
  have admitted := core_admitted context instances request predicate witness application bool
    function carrier fresh inputs sourceChecked empty closed distinct support sorted
  unfold admitSourceTypeInTheory
  rw [CanonicalTerm.applicationView?_eq_some _ _ _ application]
  have known : admitTypeInTheoryFromApplication context instances request predicate witness application =
      some (core context request predicate witness application bool function carrier fresh) := by
    rw [← admitTypeInTheory_eq_fromApplication _ _ _ _ _ application]
    exact admitted
  simp only [known]
  rw [dif_pos ((CanonicalTerm.isBoolB_eq_true_iff _).mpr bool)]
  rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.PacketQuotationTypeDefinitions
