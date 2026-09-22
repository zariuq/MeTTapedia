import Mettapedia.GSLT.LanguageDef.GSLTILRouteEquipment
import Mettapedia.GSLT.LanguageDef.GSLTILWireCells
import Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageOperationNIKAdmission
import Mettapedia.GSLT.Dynamics.RevisionedOccurrenceExactImage

/-!
# The layered GSLT-IL crown for the selected candidate operation fragment

GSLT-IL has two compatible route layers.  Its ambient authored routes are
proof-relevant relations: they may be partial, nondeterministic, and retain
several occurrences with the same visible endpoints.  A typed fragment may
additionally be represented by a direct map.  Representation earns native
execution and the companion/conjoint laws; it is not required for a raw route
to remain meaningful.

This module joins the existing components for the current finite candidate
language-operation fragment.  A single decoded endpoint-indexed program
determines:

* a declaration-aware typed candidate term;
* an operational GSLT-IL route;
* a structural action on language-indexed `Data`;
* an exact companion representation of that action;
* capture-avoiding substitution coherence; and
* an observation-preserving, revision-admissible NIK refinement.

Composition retains the intermediate value and both relation witnesses in
the loose layer while the represented action executes by ordinary function
composition.  Two negative boundaries prevent overstatement: raw authored
commands possess no global functional elaborator, and the existing candidate
returned-fibre image does not decode every GSLT-IL command.
-/

open Mettapedia.TypeTheory.Calculi.StagedScopedReflective

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.GSLTILLayeredCrown

open _root_.CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment
open Mettapedia.GSLT.LanguageDef.NIKObservedRefinement
open Mettapedia.Languages.MeTTa.Experimental.StagedReflective
open Mettapedia.Languages.MeTTa.PrimeCandidates.StagedReflectiveInstances
open Mettapedia.Languages.MeTTa.PrimeCandidates.Language (needRevisionKeying)
open Mettapedia.Languages.MeTTa.PrimeCandidates.DataFibration
open Mettapedia.Languages.MeTTa.PrimeCandidates.DataFibration.ValidatedLanguageData
open Mettapedia.Languages.MeTTa.PrimeCandidates.IndexedLanguageChange
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageOperationSyntax
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageOperationFactorization
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageOperationNIKAdmission
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Represented Data execution -/

/-- The source Data fibre selected by one intrinsic language endpoint. -/
abbrev DataAt (language : Language) :=
  FibreTranslation.AllData (fibre (currentLanguagePresentation language))

/-- The proof-relevant Data execution of a candidate operation path.  Identity
retains equality evidence; every primitive route adds its intermediate Data
value and a primitive execution witness.  This relation is generated from
the path structure rather than defined as the graph of the final direct map. -/
def dataExecution {source target : Language}
    (program : Program source target) : Loose (DataAt source) (DataAt target) :=
  @Quiver.Path.rec Language _ source
    (fun endpoint _ => Loose (DataAt source) (DataAt endpoint))
    identity
    (fun _ generator priorRelation =>
      comp priorRelation
        (companion (runProgram (Quiver.Hom.toPath generator))))
    target program

/-- Every operation path in the selected typed fragment earns an exact direct
representation.  The proof follows the authored path and composes the
representations of its primitive steps. -/
def dataExecutionRepresentation {source target : Language}
    (program : Program source target) : Representation (dataExecution program) :=
  @Quiver.Path.rec Language _ source
    (fun _ path => Representation (dataExecution path))
    { map := _root_.id
      exact := fun _ _ => Equiv.refl _ }
    (fun _ generator priorRepresentation =>
      Representation.horizontalComp priorRepresentation
        (Representation.companionSelf
          (runProgram (Quiver.Hom.toPath generator))))
    target program

/-- The direct map extracted from the path-generated relation is exactly the
existing candidate Data execution, not a second evaluator. -/
theorem dataExecutionRepresentation_map {source target : Language}
    (program : Program source target) :
    (dataExecutionRepresentation program).map = runProgram program := by
  induction program with
  | nil =>
      change (_root_.id : DataAt source → DataAt source) =
        runProgram (identityProgram source)
      funext value
      exact (run_identity source value).symm
  | @cons middle last prior generator inductionHypothesis =>
      change
        (Representation.horizontalComp (dataExecutionRepresentation prior)
          (Representation.companionSelf
            (runProgram (Quiver.Hom.toPath generator)))).map =
          runProgram (Quiver.Path.cons prior generator)
      rw [Representation.horizontalComp_map]
      rw [inductionHypothesis]
      funext value
      exact (run_comp prior (Quiver.Hom.toPath generator) value).symm

/-- Loose composition preserves the intermediate Data value and both
witnesses, while remaining exactly equivalent to the direct action of the
composed candidate program. -/
def dataExecutionCompEquiv {first middle last : Language}
    (earlier : Program first middle) (later : Program middle last)
    (source : DataAt first) (target : DataAt last) :
    comp (dataExecution earlier) (dataExecution later) source target ≃
      dataExecution (Quiver.Path.comp earlier later) source target := by
  let compositeRepresentation :=
    Representation.horizontalComp (dataExecutionRepresentation earlier)
      (dataExecutionRepresentation later)
  have mapEqual : compositeRepresentation.map =
      (dataExecutionRepresentation
        (Quiver.Path.comp earlier later)).map := by
    rw [Representation.horizontalComp_map,
      dataExecutionRepresentation_map,
      dataExecutionRepresentation_map,
      dataExecutionRepresentation_map]
    funext value
    exact (run_comp earlier later value).symm
  exact (compositeRepresentation.exact source target).trans
    (mapEqual ▸
      (dataExecutionRepresentation
        (Quiver.Path.comp earlier later)).exact source target).symm

/-! ## One program, all semantic projections -/

/-- The complete realization earned by one independently decoded candidate
language-operation program.  Every field is indexed by that same program, so
the typing, structural action, operational route, and admitted observation
cannot silently select different transformations. -/
structure SelectedRouteRealization
    (model : LanguageOperationNIKAdmission.CandidateModel)
    (decoded : currentOperationSignature.DecodedProgram) where
  typed :
    HasTypeDecl operationDeclEnv .nil (encodeProgram decoded.program)
      (routeType (languageTerm decoded.source) (languageTerm decoded.target))
  dataRepresented : Representation (dataExecution decoded.program)
  dataMapAgreement : dataRepresented.map = runProgram decoded.program
  substitutionCoherent : ∀ (depth : Nat) (replacement body : Pattern),
    Mettapedia.GSLT.LanguageDef.mapPattern
        (CurrentExecution.actionOfDecoded decoded).structuralRoute.symbols
        (instantiateBVarAt depth replacement body) =
      instantiateBVarAt depth
        (Mettapedia.GSLT.LanguageDef.mapPattern
          (CurrentExecution.actionOfDecoded decoded).structuralRoute.symbols
          replacement)
        (Mettapedia.GSLT.LanguageDef.mapPattern
          (CurrentExecution.actionOfDecoded decoded).structuralRoute.symbols
          body)
  observed : ∀ sourceMeaning : StateAt model decoded.source → Prop,
    ObservedRefinement (sourceObserved model decoded.program sourceMeaning)
      (targetImageObserved model decoded.program sourceMeaning)
  operationalAgreement :
    ∀ sourceMeaning : StateAt model decoded.source → Prop,
      ((observed sourceMeaning).refinement.realization.mapTerm) =
        transportTerm (diagram model)
          (CurrentExecution.actionOfDecoded decoded).operationalRoute

/-- Construct the full selected-fragment realization without a second
checker, route hierarchy, or execution semantics. -/
def realize (model : LanguageOperationNIKAdmission.CandidateModel)
    (decoded : currentOperationSignature.DecodedProgram) :
    SelectedRouteRealization model decoded where
  typed := encodeProgram_typed decoded.program
  dataRepresented := dataExecutionRepresentation decoded.program
  dataMapAgreement := dataExecutionRepresentation_map decoded.program
  substitutionCoherent := by
    intro depth replacement body
    exact
      Mettapedia.Languages.MeTTa.PrimeCandidates.InternalDataTransport.transport_commutes_with_instantiation
        (CurrentExecution.actionOfDecoded decoded).structuralRoute
        depth replacement body
  observed := fun sourceMeaning =>
    programObservedRefinement model decoded.program sourceMeaning
  operationalAgreement := by
    intro sourceMeaning
    exact decoded_refinement_uses_compiled_route model decoded sourceMeaning

/-- The represented Data action carries the companion binding equation.  It
is therefore a genuine tight/loose interface, not merely a function stored
beside an unrelated relation. -/
theorem dataExecution_companion_binding {source target : Language}
    (program : Program source target) :
    Cell.vcomp (companionUnit (runProgram program))
        (companionCounit (runProgram program)) =
      tightCell (runProgram program) :=
  companion_vertical_triangle (runProgram program)

/-! ## Initiality on the represented fragment -/

/-- Any interpretation insensitive to surface spelling factors uniquely
through the decoded endpoint-indexed route program. -/
theorem selected_initial_factorization {Target : Type}
    (interpretation :
      LanguageOperationFactorization.Signature.InvariantInterpretation
        currentOperationSignature Target) :
    ∃! factor : currentOperationSignature.DecodedProgram → Target,
      ∀ operation : currentOperationSignature.RecognizedOperation,
        factor operation.decoded = interpretation.apply operation :=
  LanguageOperationFactorization.Signature.InvariantInterpretation.existsUnique_factor
    interpretation

/-! ## The non-collapse boundary -/

/-- The selected typed fragment is directly representable, but the authored
command language remains relational: one surface command can carry distinct
valid elaboration occurrences. -/
theorem represented_fragment_does_not_functionalize_raw_commands :
    (∀ (source target : Language) (program : Program source target),
      Nonempty (Representation (dataExecution program))) ∧
    ∃ program : Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax.Program,
      ¬ ∃ elaborate : Pattern → Pattern,
        ∀ surface internal,
          Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax.Elaborates
              program surface internal ↔
            elaborate surface = internal := by
  constructor
  · intro source target program
    exact ⟨dataExecutionRepresentation program⟩
  · exact
      Mettapedia.GSLT.LanguageDef.GSLTIL.WireCells.exists_program_without_global_functional_elaboration

/-- candidate's current returned-fibre image is a genuine strict fragment, even
though selected route programs already enjoy the complete represented layer. -/
theorem returned_fibre_remains_strict
    (model : Mettapedia.Languages.MeTTa.PrimeCandidates.Language.Model)
    (claim :
      RevisionedOccurrenceProofFlow.Claim model.base.source
        (needRevisionKeying model)) :
    ¬ ∃ decode :
        Mettapedia.GSLT.IndexedOperational.Command
            (RevisionedOccurrenceReturnedFibre.diagram
              model.base.source (needRevisionKeying model)) →
          RevisionedOccurrenceProofFlow.Claim model.base.source
            (needRevisionKeying model),
      ∀ command,
        RevisionedOccurrenceReturnedFibre.encodeClaim
            model.base.source (needRevisionKeying model) (decode command) = command :=
  Mettapedia.GSLT.Dynamics.RevisionedOccurrenceExactImage.returned_fragment_has_no_full_command_decode
    model.base.source (needRevisionKeying model) claim

#print axioms dataExecutionCompEquiv
#print axioms dataExecutionRepresentation_map
#print axioms realize
#print axioms dataExecution_companion_binding
#print axioms selected_initial_factorization
#print axioms represented_fragment_does_not_functionalize_raw_commands
#print axioms returned_fibre_remains_strict

end Mettapedia.Languages.MeTTa.PrimeCandidates.GSLTILLayeredCrown
