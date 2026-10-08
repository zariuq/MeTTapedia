import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveTypedQuotient
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.RetainedContextualControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerConservativity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeConversionSkeleton

/-!
# Typed quotient controls with variable domains and retained certificates

The tower discharges every qualification used by conversion descent. A
beta-redex supplying a type variable gives the same quotient substitution
and type as its reduct. A variable function and its eta expansion remain
different raw conversion classes while the typed quotient identifies them.
Finally, equal quotient points retain different supplied premise ledgers.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace Examples.TypedQuotientControls

open _root_.CategoryTheory
open FormationSensitiveRuleSignature FormationSensitiveRuleReadout
open TypedEquality TypedEquality.Normalization
open Examples.RetainedContextualControls (closed universeType universeContext variableDomain
  dependentContext dependentVariable)

abbrev setting : Setting Tower.Head Nat :=
  { TowerModel.setting (fun _ => (0 : Nat)) with R := Tower.rules }

theorem qualification : FormationSensitiveTypedQuotient.Qualification setting :=
  ⟨TowerModel.facts, TowerModel.roots, TowerModel.heads, Normalization.LevelTower.churchRosser⟩

abbrev ground {n : Nat} : Tower.Tm n := .head .legacyGround
abbrev sort0 {n : Nat} : Tower.Tm n := .head (.sort Tower.zero)
abbrev upper := LevelTower.Head.sort (.succ Tower.zero)

def identityType : FormationSensitiveRetainedContextual.TypeOver closed where
  code := .pi sort0 sort0
  level := .sort (.max (.succ Tower.zero) (.succ Tower.zero))
  universeWitness := .sort _
  formation := .node (.piForm (.sort _) (.sort _) (.sorts _ _))
    (Fin.cases universeType.formation (fun _ =>
      .node (.headType (LevelTower.HeadTyping.sort Tower.zero))
        (fun position => nomatch position)))

def identityValue : FormationSensitiveRetainedContextual.Term closed identityType :=
  ⟨.lam (.var 0), .node (.lamIntro (A := sort0) (B := sort0) identityType.universeWitness)
    (Fin.cases identityType.formation (fun _ => Tree.variableLeaf (.snoc .nil sort0) 0))⟩

def groundValue : FormationSensitiveRetainedContextual.Term closed universeType :=
  ⟨ground, RuleEvidenceControls.direct⟩

def betaValue : FormationSensitiveRetainedContextual.Term closed universeType :=
  ⟨.app identityValue.code ground, .node (.appElim (A := sort0) (B := sort0))
    (Fin.cases identityValue.evidence (fun _ => groundValue.evidence))⟩

theorem beta_reduces : Conv Tower.rules.headEq betaValue.code groundValue.code
    Tower.rules.computation :=
  .rel _ _ (.betaPi (.var 0) ground)

noncomputable def betaArrow : closed ⟶ universeContext :=
  FormationSensitiveRetainedContextual.pair
    (FormationSensitiveRetainedContextual.toEmpty closed)
      ⟨betaValue.code, betaValue.evidence⟩

noncomputable def groundArrow : closed ⟶ universeContext :=
  FormationSensitiveRetainedContextual.pair
    (FormationSensitiveRetainedContextual.toEmpty closed)
      ⟨groundValue.code, groundValue.evidence⟩

theorem beta_arrows_converted :
    FormationSensitiveContextual.homConversion Tower.rules betaArrow.erase groundArrow.erase := by
  intro index
  refine Fin.cases ?_ (fun earlier => nomatch earlier) index
  exact beta_reduces

theorem beta_arrows_same_class :
    (FormationSensitiveContextual.quotientProjection Tower.rules).map betaArrow.erase =
      (FormationSensitiveContextual.quotientProjection Tower.rules).map groundArrow.erase :=
  (FormationSensitiveContextual.quotientProjection_map_eq_iff _ _).mpr beta_arrows_converted

/-- Substitution into the actual earlier type variable computes distinct raw
codes, so quotient invariance is doing work. -/
theorem substituted_domains_differ :
    (variableDomain.reindex betaArrow).code ≠ (variableDomain.reindex groundArrow).code := by
  change Tm.app (Tm.lam (.var 0)) ground ≠ ground
  intro same
  cases same

theorem substituted_domains_same_typed_class :
    FormationSensitiveTypedQuotient.suppliedType qualification (variableDomain.reindex betaArrow) =
      FormationSensitiveTypedQuotient.suppliedType qualification
        (variableDomain.reindex groundArrow) := by
  rw [FormationSensitiveTypedQuotient.suppliedType_reindex,
    FormationSensitiveTypedQuotient.suppliedType_reindex]
  exact FormationSensitiveTypedQuotient.QType.reindex_converted
    (FormationSensitiveTypedQuotient.suppliedType qualification variableDomain)
    beta_arrows_converted

theorem beta_point_agrees :
    FormationSensitiveTypedQuotient.suppliedTerm qualification betaValue =
      FormationSensitiveTypedQuotient.suppliedTerm qualification groundValue := by
  apply Subtype.ext
  apply (FormationSensitiveTypedQuotient.QTerm.mk_eq_iff qualification _ _).mpr
  exact FormationSensitiveTypedQuotient.conversionTermEq qualification
    betaValue.erase groundValue.erase (.refl _) beta_reduces

/-- Reindexing the genuine `(X : U₀), (x : X)` certificate obeys the
quotient identity law, with its dependent annotation retained. -/
theorem dependent_certificate_identity :
    FormationSensitiveTypedQuotient.Fibre.compare qualification
      (FormationSensitiveTypedQuotient.QType.presheaf_identity qualification
        ((FormationSensitiveContextual.quotientProjection Tower.rules).obj dependentContext.erase)
        (FormationSensitiveTypedQuotient.suppliedType qualification
          (variableDomain.reindex
            (FormationSensitiveRetainedContextual.projectionHom universeContext variableDomain))))
      (FormationSensitiveTypedQuotient.Fibre.reindex qualification
        (FormationSensitiveTypedQuotient.suppliedTerm qualification dependentVariable) (𝟙 _)) =
      FormationSensitiveTypedQuotient.suppliedTerm qualification dependentVariable :=
  FormationSensitiveTypedQuotient.Fibre.reindex_id qualification _

/-! ## A typed eta equation absent from the raw quotient -/

def functionType : FormationSensitiveRetainedContextual.TypeOver universeContext where
  code := .pi (.var 0) (.var 1)
  level := .sort (.max Tower.zero Tower.zero)
  universeWitness := .sort _
  formation := .node (.piForm (.sort _) (.sort _) (.sorts _ _))
    (Fin.cases (Tree.variableLeaf universeContext.raw 0)
      (fun _ => Tree.variableLeaf (.snoc universeContext.raw (.var 0)) 1))

abbrev functionContext := FormationSensitiveRetainedContextual.extend universeContext functionType

noncomputable abbrev displayedFunctionType := functionType.reindex
  (FormationSensitiveRetainedContextual.projectionHom universeContext functionType)

noncomputable def functionValue :
    FormationSensitiveRetainedContextual.Term functionContext displayedFunctionType :=
  FormationSensitiveRetainedContextual.newest universeContext functionType

def applicationBody : Tree Tower.rules
    (judgment (.snoc functionContext.raw (.var 1))
      (.app (.var 1) (.var 0)) (.var 2)) := by
  refine .node (.appElim (A := .var 2) (B := .var 3)) ?_
  intro position
  refine Fin.cases ?_ (fun _ => ?_) position
  · exact Tree.variableLeaf (R := Tower.rules) (.snoc functionContext.raw (.var 1)) 1
  · exact Tree.variableLeaf (R := Tower.rules) (.snoc functionContext.raw (.var 1)) 0

noncomputable def etaValue :
    FormationSensitiveRetainedContextual.Term functionContext displayedFunctionType :=
  ⟨.lam (.app (.var 1) (.var 0)), .node
    (.lamIntro (A := .var 1) (B := .var 2) displayedFunctionType.universeWitness)
    (Fin.cases displayedFunctionType.formation (fun _ => applicationBody))⟩

theorem eta_typed : Equal Tower.rules functionContext.raw
    functionValue.code etaValue.code displayedFunctionType.code := by
  apply Derivable.etaPi
    (FormationSensitiveTypedQuotient.termTyped qualification functionValue.erase)
    (FormationSensitiveTypedQuotient.termTyped qualification etaValue.erase)
  change Equal Tower.rules (.snoc functionContext.raw (.var 1))
    (.app (.var 1) (.var 0))
    (.app (.lam (.app (.var 2) (.var 0))) (.var 0)) (.var 2)
  have piForm : Typed Tower.rules functionContext.raw
      (.pi (.var 1) (.var 2)) (.head (.sort (.max Tower.zero Tower.zero))) :=
    FormationSensitiveTypedQuotient.typeTyped qualification displayedFunctionType.erase
  have bodyTyped : Typed Tower.rules (.snoc functionContext.raw (.var 1))
      (.app (.var 1) (.var 0)) (.var 2) :=
    Normalization.FormationSensitive.Typing.toTyped (S := setting)
      TowerModel.facts TowerModel.roots TowerModel.heads Normalization.LevelTower.churchRosser
      (sound applicationBody)
      (.snoc (FormationSensitiveTypedQuotient.contextFormed qualification functionContext.spine.sound)
        ⟨_, .sort _, .var 1⟩)
  have compatible : CtxRen functionContext.raw (.snoc functionContext.raw (.var 1)) wk :=
    fun _ => rfl
  have betaBody : Typed Tower.rules
      (.snoc (.snoc functionContext.raw (.var 1)) (.var 2))
      (.app (.var 2) (.var 0)) (.var 3) :=
    Typed.rename bodyTyped (CtxRen.snoc compatible (Tm.var (1 : Fin 2)))
  have betaForm : Typed Tower.rules (.snoc functionContext.raw (.var 1))
      (.pi (.var 2) (.var 3)) (.head (.sort (.max Tower.zero Tower.zero))) :=
    Typed.weaken (extension := Tm.var (1 : Fin 2)) piForm
  have argumentTyped : Typed Tower.rules (.snoc functionContext.raw (.var 1))
      (.var 0) (.var 2) := .var 0
  exact Derivable.symm (Derivable.betaPi betaForm (.sort _) betaBody argumentTyped)

theorem eta_same_typed_class :
    FormationSensitiveTypedQuotient.suppliedTerm qualification functionValue =
      FormationSensitiveTypedQuotient.suppliedTerm qualification etaValue := by
  apply Subtype.ext
  apply (FormationSensitiveTypedQuotient.QTerm.mk_eq_iff qualification _ _).mpr
  exact ⟨⟨_, displayedFunctionType.universeWitness,
      .refl (FormationSensitiveTypedQuotient.typeTyped qualification displayedFunctionType.erase)⟩,
    eta_typed⟩

theorem eta_not_raw_converted :
    ¬ Conv Tower.rules.headEq functionValue.code etaValue.code Tower.rules.computation := by
  apply TowerConversionSkeleton.not_conv_of_normal_erase_ne
    (TowerConversionSkeleton.erase_var_normal 0)
  · intro target step
    cases step with
    | congLam inner =>
        cases inner with
        | congAppFun earlier => cases earlier
        | congAppArg earlier => cases earlier
  · intro same
    cases same

theorem eta_distinct_raw_classes :
    FormationSensitiveContextual.QTerm.mk functionValue.erase ≠
      FormationSensitiveContextual.QTerm.mk etaValue.erase := by
  intro same
  exact eta_not_raw_converted
    ((FormationSensitiveContextual.QTerm.mk_eq_iff _ _).mp same).2

/-- The earned raw-to-typed quotient map is surjective but need not be
injective, even in the fully qualified cumulative tower. -/
theorem quotient_value_map_not_injective :
    ¬ Function.Injective
      (FormationSensitiveTypedQuotient.QTerm.ofRaw qualification
        (context := functionContext.erase)) := by
  intro injective
  apply eta_distinct_raw_classes
  apply injective
  exact congrArg Subtype.val eta_same_typed_class

/-! ## The original supplied certificate still distinguishes origins -/

theorem retained_certificate_points_agree :
    (FormationSensitiveTypedQuotient.suppliedReadout qualification
      RetainedContextualControls.directValue).1 =
      (FormationSensitiveTypedQuotient.suppliedReadout qualification
        RetainedContextualControls.cumulativeValue).1 := by
  apply Subtype.ext
  rfl

theorem retained_certificate_ledgers_differ :
    (FormationSensitiveTypedQuotient.suppliedReadout qualification
      RetainedContextualControls.directValue).2 ≠
      (FormationSensitiveTypedQuotient.suppliedReadout qualification
        RetainedContextualControls.cumulativeValue).2 :=
  RuleEvidenceControls.readouts_distinct

end Examples.TypedQuotientControls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
