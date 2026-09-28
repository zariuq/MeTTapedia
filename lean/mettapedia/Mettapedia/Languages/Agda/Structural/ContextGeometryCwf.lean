import Mettapedia.Languages.Agda.Structural.ContextGeometry
import Mettapedia.OSLF.Syntax.BindingTelescopeCwf

/-!
# The raw structural Agda telescope CwF

This specialization packages scoped syntax and proposed type tags. Context
extension stores the actual annotated code, and substitution can change that
code. A tagged term is not a typing derivation. No formation admission or
Agda static adequacy is asserted by the raw CwF or its controls.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.ContextGeometry

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.Core.ContextualLadder

/-- The raw syntactic structure awaiting separate formation and typing admission. -/
def rawAgdaTelescopeCwfWithTerminal : CwfWithTerminal.{0, 0, 0, 0} :=
  Telescope.rawTelescopeCwfWithTerminal sig .term .type

abbrev rawAgdaTelescopeCwf : Cwf.{0, 0, 0, 0} := rawAgdaTelescopeCwfWithTerminal.toCwf

namespace CwfControls

def oneContext : rawAgdaTelescopeCwf.Ctx := ⟨1, Controls.contextOne⟩
def twoContext : rawAgdaTelescopeCwf.Ctx := ⟨2, Controls.contextTwo⟩

def dependentType : rawAgdaTelescopeCwf.Ty oneContext := Controls.dependentType

def replaceNewest : rawAgdaTelescopeCwf.Sub oneContext oneContext := Controls.replaceNewest

/-- The CwF action substitutes the whole annotated code. -/
theorem dependent_type_reindexes :
    rawAgdaTelescopeCwf.tySub dependentType replaceNewest = Controls.universeType (n := 1) 0 := rfl

/-- This dependent interface has a nonconstant raw type action. -/
theorem dependent_type_action_nontrivial :
    rawAgdaTelescopeCwf.tySub dependentType replaceNewest ≠ dependentType :=
  Controls.dependent_type_reindexing_nontrivial

/-- Context extension retains the supplied dependent declaration. -/
theorem extension_retains_declaration : rawAgdaTelescopeCwf.ext oneContext dependentType = twoContext := rfl

/-- Different raw type declarations are not identified as context objects. -/
theorem extension_distinguishes_declarations :
    rawAgdaTelescopeCwf.ext oneContext dependentType ≠
      rawAgdaTelescopeCwf.ext oneContext (Controls.universeType (n := 1) 0) := by
  intro same
  cases same

/-- The proposed tag is an index, not a certificate that this variable has that type. -/
def proposedVariable : rawAgdaTelescopeCwf.Tm oneContext dependentType := ⟨.var .zero⟩

def sameCodeDifferentTag :
    rawAgdaTelescopeCwf.Tm oneContext (Controls.universeType (n := 1) 0) := ⟨.var .zero⟩

/-- The raw interface permits the same code to be proposed at different tags. -/
theorem same_code_different_proposals :
    proposedVariable.code = sameCodeDifferentTag.code ∧
      dependentType ≠ Controls.universeType (n := 1) 0 := by
  constructor
  · rfl
  · intro same
    exact dependent_type_action_nontrivial same.symm

/-- Substitution changes the raw term code along with its proposed type tag. -/
theorem tagged_substitution_code :
    (rawAgdaTelescopeCwf.tmSub proposedVariable replaceNewest).code =
      Controls.universeTerm (n := 1) 0 := rfl

/-- The existing dependent comprehension theorem applies to this actual raw instance. -/
def dependentComprehension :
    rawAgdaTelescopeCwf.Sub oneContext (rawAgdaTelescopeCwf.ext oneContext dependentType) ≃
      rawAgdaTelescopeCwf.ComprehensionData oneContext oneContext dependentType :=
  rawAgdaTelescopeCwf.comprehensionEquiv oneContext oneContext dependentType

theorem comprehension_recovers_substitution
    (substitution : rawAgdaTelescopeCwf.Sub oneContext
      (rawAgdaTelescopeCwf.ext oneContext dependentType)) :
    dependentComprehension.symm (dependentComprehension substitution) = substitution :=
  dependentComprehension.left_inv substitution

theorem comprehension_recovers_dependent_pair
    (data : rawAgdaTelescopeCwf.ComprehensionData oneContext oneContext dependentType) :
    dependentComprehension (dependentComprehension.symm data) = data :=
  dependentComprehension.right_inv data

/-- Precomposition retains the dependent newest component through its required cast. -/
theorem dependent_comprehension_natural {source middle : rawAgdaTelescopeCwf.Ctx}
    (substitution : rawAgdaTelescopeCwf.Sub middle
      (rawAgdaTelescopeCwf.ext oneContext dependentType))
    (next : rawAgdaTelescopeCwf.Sub source middle) :
    rawAgdaTelescopeCwf.decompose dependentType (rawAgdaTelescopeCwf.compS substitution next) =
      rawAgdaTelescopeCwf.precomposeData
        (rawAgdaTelescopeCwf.decompose dependentType substitution) next :=
  rawAgdaTelescopeCwf.decompose_natural dependentType substitution next

/-- Pairing still returns the exact newly supplied raw term. -/
theorem newest_after_pair
    (substitution : rawAgdaTelescopeCwf.Sub oneContext oneContext)
    (term : rawAgdaTelescopeCwf.Tm oneContext
      (rawAgdaTelescopeCwf.tySub dependentType substitution)) :
    (rawAgdaTelescopeCwf.tmSub (rawAgdaTelescopeCwf.vz dependentType)
      (rawAgdaTelescopeCwf.pair substitution dependentType term)).code = term.code := rfl

theorem empty_is_empty_telescope :
    rawAgdaTelescopeCwfWithTerminal.empty =
      (⟨0, .nil⟩ : Telescope.Context sig .term .type) := rfl

theorem empty_substitution_unique (context : rawAgdaTelescopeCwf.Ctx)
    (substitution : rawAgdaTelescopeCwf.Sub context rawAgdaTelescopeCwfWithTerminal.empty) :
    substitution = rawAgdaTelescopeCwfWithTerminal.toEmpty context :=
  rawAgdaTelescopeCwfWithTerminal.toEmpty_unique context substitution

end CwfControls

#print axioms rawAgdaTelescopeCwfWithTerminal
#print axioms CwfControls.dependent_type_action_nontrivial
#print axioms CwfControls.extension_distinguishes_declarations
#print axioms CwfControls.dependentComprehension
#print axioms CwfControls.dependent_comprehension_natural
#print axioms CwfControls.same_code_different_proposals

end Mettapedia.Languages.Agda.Structural.ContextGeometry
