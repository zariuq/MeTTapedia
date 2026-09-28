import Mettapedia.OSLF.Syntax.CartesianModelLexRestriction
import Mettapedia.OSLF.Syntax.RhoCartesianModelSetSemantics

/-!
# Left-exact finite-presentation semantics for authored rho contexts

The general classification applies to the actual two-sorted reflective rho
context category. Its name and process representations yield left-exact
semantics; their finite-presentation element diagrams reconstruct them.
The constant Boolean interpretation remains outside the classified category.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoCartesianModelLexRestriction

open CategoryTheory CategoryTheory.Limits
open Mettapedia.OSLF.CartesianContextModels
open Mettapedia.OSLF.Binding.RhoCartesianContextModels
open Mettapedia.OSLF.Binding.RhoCartesianModelSetSemantics

private instance : HasFiniteProducts Contexts :=
  hasFiniteProducts_of_has_binary_and_terminal

/-- The rho context category has the proved relative finite-limit
classification, including its action on model morphisms. -/
noncomputable def rhoModelsEquivLexSetSemantics :
    Models Contexts ≌ LexSetSemantics Contexts :=
  cartesianModelsEquivLexSetSemantics Contexts

noncomputable def rhoExtendRestrictIso :
    restrictLexToModel Contexts ⋙ extendModelToLex Contexts ≅
      𝟭 (LexSetSemantics Contexts) :=
  extendRestrictLexIso Contexts

noncomputable def nameLexSemantics : LexSetSemantics Contexts :=
  ⟨nameSemantics, nameSemantics_preservesFiniteLimits⟩

noncomputable def processLexSemantics : LexSetSemantics Contexts :=
  ⟨processSemantics, processSemantics_preservesFiniteLimits⟩

/-- The name-sort interpretation is recovered by its own finite-presentation
solutions, including solutions at contexts with binders. -/
noncomputable def nameLexReconstructionIso :
    finitePresentationSemantics Contexts
      (reconstructLexModel Contexts nameLexSemantics) ≅ nameSemantics :=
  lexReconstructionIso Contexts nameLexSemantics

/-- The same reconstruction applies to the process-sort interpretation. -/
noncomputable def processLexReconstructionIso :
    finitePresentationSemantics Contexts
      (reconstructLexModel Contexts processLexSemantics) ≅ processSemantics :=
  lexReconstructionIso Contexts processLexSemantics

/-- A two-element constant interpretation cannot masquerade as a left-exact
rho semantics. -/
theorem bool_not_rho_lex :
    ¬ LeftExactSetSemantics Contexts
      ((Functor.const (FinitePresentationObjects Contexts)).obj Bool) :=
  constantBool_not_lex Contexts

end Mettapedia.OSLF.Binding.RhoCartesianModelLexRestriction
