import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalRealizations

/-!
# A private prefix copy retains its instances beside independent later constraints

The prefix and ambient declarations are disjoint summands. The ambient
problem must be solvable; its equations do not bind the copied prefix's
private declarations. Arbitrary contextual arities and residual equations
are retained. Additional model arities receive actual fresh generators.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixIsolation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching ContextualConditionalRealizations

variable {S : Signature} {Prefix Ambient Next : Type}
    (savedDecl : Prefix → MetaArity S) (ambient : Ambient → MetaArity S)
    {next : Next → MetaArity S} {Γ : Ctx S} {sort : S.Srt}

abbrev combined := ContextualSelectionViews.source savedDecl ambient

def problem (saved : ContextualResidual.Problem savedDecl) (current : ContextualResidual.Problem ambient) :
    ContextualResidual.Problem (combined savedDecl ambient) :=
  ContextualResidual.mapProblem (ContextualStoredRows.privateSource savedDecl ambient) saved ++
    ContextualResidual.mapProblem (ContextualSelectionViews.capturedSource savedDecl ambient) current

theorem extend_model (saved : ContextualResidual.Problem savedDecl) (current : ContextualResidual.Problem ambient)
    (consistent : ∃ (Future : Type) (future : Future → MetaArity S) (candidate : Assignment ambient future),
      ContextualResidual.Models candidate current)
    (images : Assignment savedDecl next) (model : ContextualResidual.Models images saved) :
    ∃ (Extra : Type) (extra : Extra → MetaArity S)
      (both : Assignment (combined savedDecl ambient) (ContextualPrefixModels.extended extra next)),
      ContextualResidual.Models both (problem savedDecl ambient saved current) ∧
      Assignment.compose both (ContextualStoredRows.privateSource savedDecl ambient) =
        Assignment.compose (ContextualPrefixModels.inclusion extra next) images := by
  obtain ⟨Future, future, other, currentModel⟩ := consistent
  let added := Extension.withLocals future next
  let savedImages := Assignment.compose added.assignment images
  let ambientImages := Assignment.compose (ContextualStoredRows.privateSource future next) other
  let both := valuation savedDecl ambient savedImages ambientImages
  refine ⟨Future, future, both, ?_, ?_⟩
  · apply (ContextualResidual.models_append both _ _).mpr
    constructor
    · apply (ContextualResidual.models_mapProblem _ _ _).mpr
      erw [valuation_private]
      exact ContextualResidual.models_compose model added.assignment
    · apply (ContextualResidual.models_mapProblem _ _ _).mpr
      erw [valuation_captures]
      exact ContextualResidual.models_compose currentModel (ContextualStoredRows.privateSource future next)
  · exact valuation_private savedDecl ambient savedImages ambientImages

theorem instances_iff (saved : ContextualResidual.Problem savedDecl) (current : ContextualResidual.Problem ambient)
    (consistent : ∃ (Future : Type) (future : Future → MetaArity S) (candidate : Assignment ambient future),
      ContextualResidual.Models candidate current)
    (value : Term (signature S savedDecl) Γ sort) (pattern : Term (signature S next) Γ sort) :
    ContextualPublication.SourceInstances (problem savedDecl ambient saved current)
        (instantiate (ContextualStoredRows.privateSource savedDecl ambient) value) next pattern ↔
      ContextualPublication.SourceInstances saved value next pattern := by
  constructor
  · rintro ⟨extension, images, model, same⟩
    have prefixModel := (ContextualResidual.models_mapProblem _ _ _).mp
      ((ContextualResidual.models_append images _ _).mp model).1
    exact ⟨extension, Assignment.compose images (ContextualStoredRows.privateSource savedDecl ambient), prefixModel,
      (Assignment.instantiate_compose images _ value).trans same⟩
  · rintro ⟨extension, images, model, same⟩
    obtain ⟨Extra, extra, both, jointModel, projected⟩ := extend_model savedDecl ambient saved current consistent images model
    let added := Extension.withLocals extra extension.declarations
    refine ⟨extension.trans added, both, jointModel, ?_⟩
    erw [← Assignment.instantiate_compose, projected, Assignment.instantiate_compose]
    exact (congrArg (instantiate added.assignment) same).trans
      (by erw [Extension.trans_assignment, Assignment.instantiate_compose]; rfl)

theorem asks_iff {Local O : Type} (locals : Local → MetaArity S)
    (saved : ContextualResidual.Problem savedDecl) (current : ContextualResidual.Problem ambient)
    (consistent : ∃ (Future : Type) (future : Future → MetaArity S) (candidate : Assignment ambient future),
      ContextualResidual.Models candidate current)
    (rows : O → ContextualConditionalRows.Row locals savedDecl Γ sort) (world : Finset O)
    (check : Check (Term (signature S savedDecl) Γ sort)) :
    ContextualConditionalGuards.Ask locals (problem savedDecl ambient saved current)
        (fun occurrence => (rows occurrence).map locals savedDecl (ContextualStoredRows.privateSource savedDecl ambient))
        world (check.map (instantiate (ContextualStoredRows.privateSource savedDecl ambient))) ↔
      ContextualConditionalGuards.Ask locals saved rows world check := by
  constructor
  · intro asked Future future candidate model
    obtain ⟨Extra, extra, both, jointModel, projected⟩ := extend_model savedDecl ambient saved current consistent candidate model
    have held := (ContextualConditionalGuards.holds_transport locals
      (ContextualStoredRows.privateSource savedDecl ambient) both rows world check).mp
      (asked _ _ both jointModel)
    rw [projected] at held
    exact (ContextualConditionalNaturality.holds_inclusion_iff locals extra candidate rows world check).mp held
  · intro asked Future future candidate model
    have savedModel := (ContextualResidual.models_mapProblem _ _ _).mp
      ((ContextualResidual.models_append candidate _ _).mp model).1
    exact (ContextualConditionalGuards.holds_transport locals
      (ContextualStoredRows.privateSource savedDecl ambient) candidate rows world check).mpr
      (asked _ _ _ savedModel)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixIsolation
