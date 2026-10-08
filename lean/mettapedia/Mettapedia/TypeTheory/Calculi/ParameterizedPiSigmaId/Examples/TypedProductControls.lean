import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedContextualProducts
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.TypedContextualControls

/-!
# Varying-domain dependent function controls

A supplied universe variable is the function domain. The identity body and
its dependent type vary under context projection. Typed beta preserves the
supplied argument class although its actual redex has different syntax.
The selected native operations retain beta, eta and the nonidentity lifted
context action.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace Examples.TypedProductControls

open _root_.CategoryTheory TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.DependentTypes TypedContextual.QuotientComprehensionSyntax
open TypedContextualControls (levels sort0)

abbrev base : Context Tower.rules := empty Tower.rules

def universeType : TypeOver base :=
  ⟨sort0, .sort (.succ Tower.zero), .sort _, .headType (.sort _)⟩

abbrev typeContext := extend base universeType

def variableType : TypeOver typeContext :=
  ⟨.var 0, .sort Tower.zero, .sort _, .var 0⟩

def identityBody : Term (extend typeContext variableType)
    (variableType.reindex (projectionHom typeContext variableType)) := newest typeContext variableType

noncomputable def identity : Term typeContext
    (rawPi levels variableType (variableType.reindex (projectionHom typeContext variableType))) :=
  Products.rawLam levels identityBody

theorem actual_identity_has_varying_domain : identity.code = .lam (.var 0) ∧
    (rawPi levels variableType (variableType.reindex (projectionHom typeContext variableType))).code =
      .pi (.var 0) (.var 1) := ⟨rfl, rfl⟩

abbrev valueContext := extend typeContext variableType
def shiftedDomain := variableType.reindex (projectionHom typeContext variableType)
def value : Term valueContext shiftedDomain := newest typeContext variableType

noncomputable def suppliedFunction : Term valueContext
    (rawPi levels shiftedDomain (shiftedDomain.reindex (projectionHom valueContext shiftedDomain))) :=
  Products.rawLam levels (newest valueContext shiftedDomain)

theorem shifted_domain_is_nonconstant : shiftedDomain.code = .var 1 := rfl

theorem actual_beta_keeps_supplied_variable :
    QTerm.mk levels (Products.rawApp levels suppliedFunction value) = QTerm.mk levels value := by
  have computed := Products.rawBeta levels (newest valueContext shiftedDomain) value
  exact computed.trans (QuotientCwf.raw_newest_pair shiftedDomain (𝟙 valueContext)
    (value.cast shiftedDomain.reindex_id.symm))

theorem literal_redex_is_not_supplied_variable :
    (Products.rawApp levels suppliedFunction value).code ≠ value.code := by
  intro same
  cases same

abbrev context := (quotientProjection Tower.rules).obj valueContext
def domain : QuotientCwf.Ty levels context := QType.mk levels shiftedDomain

noncomputable def argument : QuotientCwf.Tm levels context domain := ⟨QTerm.mk levels value, rfl⟩
noncomputable def codomain := QuotientCwf.tySub domain (QuotientCwf.wk domain)
noncomputable def body := QuotientCwf.vz domain
noncomputable def function := Products.lam levels body

theorem native_beta_keeps_supplied_class : HEq (Products.app levels function argument) argument := by
  apply heq_of_value
  exact (congrArg Subtype.val (Products.beta levels body argument)).trans (selfExtend_value argument)

theorem complete_function_eta : Products.lam levels (Products.uncurry levels function) = function :=
  Products.lam_uncurry levels function

theorem complete_body_beta : Products.uncurry levels function = body := Products.uncurry_lam levels body

abbrev largerRaw := extend valueContext shiftedDomain
abbrev larger := (quotientProjection Tower.rules).obj largerRaw
def projection : larger ⟶ context := QuotientCwf.project (projectionHom valueContext shiftedDomain)

noncomputable def reindexedFunction : QuotientCwf.Tm levels larger
    (Products.pi levels (QuotientCwf.tySub domain projection)
      (QuotientCwf.tySub codomain (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf levels) projection domain))) :=
  let same : QuotientCwf.tySub (Products.pi levels domain codomain) projection =
      Products.pi levels (QuotientCwf.tySub domain projection)
        (QuotientCwf.tySub codomain (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
          (C := QuotientCwf.cwf levels) projection domain)) :=
    Products.formation_substitution levels projection domain codomain
  same ▸ QuotientCwf.tmSub function projection

theorem projection_really_changes_domain :
    (shiftedDomain.reindex (projectionHom valueContext shiftedDomain)).code = .var 2 ∧
      (shiftedDomain.reindex (projectionHom valueContext shiftedDomain)).code ≠ .var 1 := by
  constructor
  · rfl
  · intro same
    cases same

theorem native_application_commutes_with_nonidentity_projection :
    HEq (QuotientCwf.tmSub (Products.app levels function argument) projection)
      (Products.app levels reindexedFunction (QuotientCwf.tmSub argument projection)) :=
  Products.application_substitution levels projection function argument reindexedFunction
    (by unfold reindexedFunction; exact (transport_heq levels _ _).symm)

theorem function_sections_commute_with_nonidentity_projection :
    QuotientCwf.tmSub (Products.uncurry levels function)
      (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf levels) projection domain) = Products.uncurry levels reindexedFunction :=
  Products.uncurry_substitution levels projection function reindexedFunction
    (by unfold reindexedFunction; exact (transport_heq levels _ _).symm)

end Examples.TypedProductControls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
