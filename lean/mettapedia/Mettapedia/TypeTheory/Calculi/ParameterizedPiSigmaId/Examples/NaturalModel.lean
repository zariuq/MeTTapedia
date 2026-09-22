import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.SyntacticNaturalModel
import Mettapedia.GSLT.Core.LooseRelationCompanions
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.ContextualSections

/-! # Concrete examples of SyntacticNaturalModel -/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace SyntacticNaturalModel

open CategoryTheory
open SyntacticContextual
namespace TowerExamples

open SyntacticContextual.TowerExamples

/-- The empty Tower context has its canonical native construction spine. -/
def emptySpine : ComprehensionSpine empty := .empty

/-- Extending by `U₁` constructs its newest variable without any lookup or
typing side condition. -/
def universeOneVariable :
    Variable (.snoc emptySpine universeOne)
      (universeOne.reindex (projectionHom empty universeOne)) :=
  .newest emptySpine universeOne

@[simp] theorem universeOneVariable_code :
    universeOneVariable.term.code = (.var 0 : Tower.Tm 1) :=
  universeOneVariable.term_code

/-- Negative control: an empty comprehension spine has no variable at any
formed type.  This is constructor-level impossibility, not failed lookup. -/
theorem no_variable_in_empty (type : TypeOver empty) :
    IsEmpty (Variable emptySpine type) := by
  constructor
  intro nativeVar
  cases nativeVar

end TowerExamples

#print axioms TowerExamples.no_variable_in_empty

end SyntacticNaturalModel
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
