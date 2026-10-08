import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedContextualSumElimination
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.TypedProductControls

/-!
# Dependent pair controls with a variable domain and identity codomain

The supplied pair has first component `x : X` and second component a
reflexivity term of `Id X x x`. The selected quotient domain need not retain
the original variable code: typed retyping and an actual extension comparison
admit the same supplied witnesses. Projection beta, pair eta and context
substitution keep their dependent classes; the raw second projection redex
is distinct from the supplied reflexivity syntax.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace Examples.TypedSumControls

open _root_.CategoryTheory TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.DependentTypes TypedContextual.QuotientComprehensionSyntax
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualSumComprehension
open TypedContextualControls (levels)
open TypedProductControls (valueContext shiftedDomain value context domain argument larger)

abbrev programProjection : larger ⟶ context := TypedProductControls.projection

def rawCodomain : TypeOver (extend valueContext shiftedDomain) where
  code := .id (.var 2) (.var 0) (.var 0)
  level := .sort Tower.zero
  universeWitness := .sort _
  formed := .idForm (.var 2) (.sort _) (.var 0) (.var 0)

def reflexivity : Term valueContext (rawCodomain.reindex (nativeSection value)) :=
  ⟨.refl value.code, .reflIntro value.typed⟩

noncomputable def rawValue := Sums.rawPair levels value reflexivity

theorem dependent_pair_type_is_actual :
    (rawSigma levels shiftedDomain rawCodomain).code =
      .sigma (.var 1) (.id (.var 2) (.var 0) (.var 0)) ∧
      (rawCodomain.reindex (nativeSection value)).code = .id (.var 1) (.var 0) (.var 0) := ⟨rfl, rfl⟩

theorem dependent_raw_first_beta : QTerm.mk levels (Sums.rawFst levels rawValue) = QTerm.mk levels value :=
  Sums.rawFstBeta levels value reflexivity

theorem dependent_raw_second_beta : QTerm.mk levels (Sums.rawSnd levels rawValue) = QTerm.mk levels reflexivity :=
  Sums.rawSndBeta levels value reflexivity

theorem raw_second_redex_is_not_reflexivity : (Sums.rawSnd levels rawValue).code ≠ reflexivity.code := by
  intro same
  cases same

noncomputable def domainComparison :
    extend valueContext (QuotientCwf.typeRepresentative domain) ≅ extend valueContext shiftedDomain :=
  extensionComparison (QuotientCwf.typeRepresentative domain) shiftedDomain
    ((QType.mk_eq_iff levels _ _).mp (QuotientCwf.typeRepresentative_class domain))

noncomputable def selectedCodomain : TypeOver (QuotientCwf.ext context domain).as :=
  rawCodomain.reindex domainComparison.hom

noncomputable def codomain : QuotientCwf.Ty levels (QuotientCwf.ext context domain) := QType.mk levels selectedCodomain

noncomputable def selectedArgument : Term valueContext (QuotientCwf.typeRepresentative domain) :=
  value.convertType _ ((QType.mk_eq_iff levels _ _).mp (QuotientCwf.typeRepresentative_class domain)).symm

theorem selected_argument_keeps_supplied_class : QTerm.mk levels selectedArgument = argument.val :=
  QTerm.mk_convertType value _ _

noncomputable def selectedReflexivity : Term valueContext (selectedCodomain.reindex (nativeSection selectedArgument)) where
  code := reflexivity.code
  typed := by
    change Typed Tower.rules valueContext.raw (.refl value.code)
      (subst (nativeSection selectedArgument).substitution selectedCodomain.code)
    rw [nativeSection_substitution]
    have code : selectedCodomain.code = rawCodomain.code := extensionComparison_type_code _ _ _ _
    rw [code]
    exact .reflIntro value.typed

set_option backward.isDefEq.respectTransparency false in
noncomputable def second : QuotientCwf.Tm levels context
    (QuotientCwf.tySub codomain (selfExtend (QuotientCwf.cwf levels) argument)) :=
  ⟨QTerm.mk levels selectedReflexivity, by
    change QType.mk levels (selectedCodomain.reindex (nativeSection selectedArgument)) = _
    calc
      _ = QuotientCwf.tySub codomain (QuotientCwf.project (nativeSection selectedArgument)) := rfl
      _ = _ := by rw [nativeSection_projects_of_class argument selectedArgument selected_argument_keeps_supplied_class]⟩

noncomputable def suppliedPair := Sums.pair levels argument second

theorem native_first_beta : Sums.fst levels suppliedPair = argument := Sums.fst_pair levels argument second

theorem native_second_beta : HEq (Sums.snd levels suppliedPair) second := Sums.snd_pair levels argument second

theorem native_pair_eta : Sums.pair levels (Sums.fst levels suppliedPair) (Sums.snd levels suppliedPair) = suppliedPair :=
  Sums.eta levels suppliedPair

noncomputable def reindexedPair : QuotientCwf.Tm levels larger
    (Sums.sigma levels (QuotientCwf.tySub domain programProjection)
      (QuotientCwf.tySub codomain (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf levels) programProjection domain))) :=
  let same : QuotientCwf.tySub (Sums.sigma levels domain codomain) programProjection =
      Sums.sigma levels (QuotientCwf.tySub domain programProjection)
        (QuotientCwf.tySub codomain (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
          (C := QuotientCwf.cwf levels) programProjection domain)) :=
    Sums.formation_substitution levels programProjection domain codomain
  same ▸ QuotientCwf.tmSub suppliedPair programProjection

theorem both_native_projections_commute_with_projection :
    HEq (QuotientCwf.tmSub (Sums.fst levels suppliedPair) programProjection) (Sums.fst levels reindexedPair) ∧
      HEq (QuotientCwf.tmSub (Sums.snd levels suppliedPair) programProjection) (Sums.snd levels reindexedPair) :=
  Sums.projection_substitution levels programProjection suppliedPair reindexedPair
    (by unfold reindexedPair; exact (transport_heq levels _ _).symm)

theorem selected_sum_context_comparison_is_invertible :
    pack (SumElimination.stable levels) domain codomain ≫
      unpack (SumElimination.stable levels) domain codomain =
      𝟙 (QuotientCwf.ext (QuotientCwf.ext context domain) codomain) :=
  unpack_pack (SumElimination.stable levels) domain codomain

theorem selected_sum_comparison_uses_both_actual_lifts :
    pack (SumElimination.stable levels) (QuotientCwf.tySub domain programProjection)
      (QuotientCwf.tySub codomain (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf levels) programProjection domain)) ≫
        sumReindex (SumElimination.stable levels) programProjection domain codomain =
      tupleReindex (C := QuotientCwf.cwf levels) programProjection domain codomain ≫
        pack (SumElimination.stable levels) domain codomain :=
  SumElimination.context_comparison_substitution levels programProjection domain codomain

end Examples.TypedSumControls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
