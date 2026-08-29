import Mettapedia.Languages.MeTTa.Pure.Intrinsic.DeclarationSemantics
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationSignature
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.LegacyTowerConservativity

/-!
# Compatibility of the former declaration calculus

The earlier `DeclEnv` development is represented inside the common
declaration-aware presentation.  Its constants become a Legacy-headed
signature, and its delta reduction becomes the signature root computation.
The results below are correspondence theorems, not aliases and not a second
source of authority.
-/

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace Declaration
namespace LegacyCompatibility

open Mettapedia.Languages.MeTTa.Pure.Intrinsic.DeclarationSemantics

abbrev OldEntry :=
  Mettapedia.Languages.MeTTa.Pure.Intrinsic.DeclarationEnv.DeclEntry
abbrev OldEnvironment :=
  Mettapedia.Languages.MeTTa.Pure.Intrinsic.DeclarationEnv.DeclEnv

/-- Translate an old closed declaration entry into the common grammar. -/
def ofOldEntry (entry : OldEntry) : Entry Legacy.Head where
  type := Legacy.ofPure entry.type
  value? := entry.value?.map Legacy.ofPure

/-- The former declaration environment is a Legacy-headed signature with no
extra root equations beyond delta unfolding. -/
def ofOldEnvironment (environment : OldEnvironment) : Signature Legacy.Head where
  entries := fun name => (environment.entries name).map ofOldEntry

@[simp] theorem typeOf_ofOldEnvironment (environment : OldEnvironment)
    (name : DeclName) :
    (ofOldEnvironment environment).typeOf? name =
      (Mettapedia.Languages.MeTTa.Pure.Intrinsic.DeclarationEnv.typeOf?
        environment name).map Legacy.ofPure := by
  unfold ofOldEnvironment Signature.typeOf?
    Mettapedia.Languages.MeTTa.Pure.Intrinsic.DeclarationEnv.typeOf?
  cases lookup : environment.entries name <;> simp [lookup, ofOldEntry]

@[simp] theorem valueOf_ofOldEnvironment (environment : OldEnvironment)
    (name : DeclName) :
    (ofOldEnvironment environment).valueOf? name =
      (Mettapedia.Languages.MeTTa.Pure.Intrinsic.DeclarationEnv.valueOf?
        environment name).map Legacy.ofPure := by
  unfold ofOldEnvironment Signature.valueOf?
    Mettapedia.Languages.MeTTa.Pure.Intrinsic.DeclarationEnv.valueOf?
  cases lookup : environment.entries name <;> simp [lookup, ofOldEntry]

theorem typeOf_reflect {environment : OldEnvironment} {name : DeclName}
    {type : Legacy.Tm 0}
    (lookup : (ofOldEnvironment environment).typeOf? name = some type) :
    Mettapedia.Languages.MeTTa.Pure.Intrinsic.DeclarationEnv.typeOf?
      environment name = some (Legacy.toPure type) := by
  rw [typeOf_ofOldEnvironment] at lookup
  cases oldLookup :
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.DeclarationEnv.typeOf?
        environment name with
  | none => simp [oldLookup] at lookup
  | some oldType =>
      have translated : Legacy.ofPure oldType = type := by
        simpa [oldLookup] using lookup
      simp [← translated]

theorem valueOf_reflect {environment : OldEnvironment} {name : DeclName}
    {value : Legacy.Tm 0}
    (lookup : (ofOldEnvironment environment).valueOf? name = some value) :
    Mettapedia.Languages.MeTTa.Pure.Intrinsic.DeclarationEnv.valueOf?
      environment name = some (Legacy.toPure value) := by
  rw [valueOf_ofOldEnvironment] at lookup
  cases oldLookup :
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.DeclarationEnv.valueOf?
        environment name with
  | none => simp [oldLookup] at lookup
  | some oldValue =>
      have translated : Legacy.ofPure oldValue = value := by
        simpa [oldLookup] using lookup
      simp [← translated]

@[simp] theorem ofPure_oldLiftClosed
    (term : Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax.PureTm 0) :
    Legacy.ofPure
      (Mettapedia.Languages.MeTTa.Pure.Intrinsic.DeclarationEnv.liftClosed
        (n := n) term) =
      (liftClosed (Legacy.ofPure term) : Legacy.Tm n) := by
  unfold Mettapedia.Languages.MeTTa.Pure.Intrinsic.DeclarationEnv.liftClosed
    liftClosed
  rw [Legacy.ofPure_rename]
  apply rename_ext
  intro index
  exact Fin.elim0 index

/-- Every former declaration reduction is a step of the one common
declaration-aware presentation. -/
theorem step_of_redDecl {environment : OldEnvironment}
    {left right : Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax.PureTm n}
    (reduction : RedDecl environment left right) :
    Step (extendRules Legacy.rules (ofOldEnvironment environment)).headEq
      (Legacy.ofPure left) (Legacy.ofPure right)
      (extendRules Legacy.rules (ofOldEnvironment environment)).computation := by
  induction reduction with
  | core reduction =>
      exact
        _root_.Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation.Declaration.StepCore.includeSignature
          Legacy.rules (ofOldEnvironment environment)
          (Legacy.step_of_oldRed reduction)
  | deltaConst lookup =>
      apply Step.root
      change RootStep Legacy.rules (ofOldEnvironment environment) _
        (.const _) (Legacy.ofPure
          (Mettapedia.Languages.MeTTa.Pure.Intrinsic.DeclarationEnv.liftClosed _))
      simpa only [ofPure_oldLiftClosed] using
        (RootStep.delta (base := Legacy.rules) (by
          rw [valueOf_ofOldEnvironment, lookup]
          rfl))
  | congPiDom reduction ih => exact .congPiDom ih
  | congPiCod reduction ih => exact .congPiCod ih
  | congSigmaDom reduction ih => exact .congSigmaDom ih
  | congSigmaCod reduction ih => exact .congSigmaCod ih
  | congIdTy reduction ih => exact .congIdTy ih
  | congIdLeft reduction ih => exact .congIdLeft ih
  | congIdRight reduction ih => exact .congIdRight ih
  | congLam reduction ih => exact .congLam ih
  | congAppFun reduction ih => exact .congAppFun ih
  | congAppArg reduction ih => exact .congAppArg ih
  | congPairFst reduction ih => exact .congPairFst ih
  | congPairSnd reduction ih => exact .congPairSnd ih
  | congFst reduction ih => exact .congFst ih
  | congSnd reduction ih => exact .congSnd ih
  | congRefl reduction ih => exact .congRefl ih

/-- Former declaration conversion embeds in common conversion. -/
theorem conv_of_convDecl {environment : OldEnvironment}
    {left right : Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax.PureTm n}
    (conversion : ConvDecl environment left right) :
    Conv (extendRules Legacy.rules (ofOldEnvironment environment)).headEq
      (Legacy.ofPure left) (Legacy.ofPure right)
      (extendRules Legacy.rules (ofOldEnvironment environment)).computation := by
  induction conversion with
  | rel left right reduction => exact .rel _ _ (step_of_redDecl reduction)
  | refl term => exact .refl _
  | symm left right conversion ih => exact .symm _ _ ih
  | trans left middle right first second ihFirst ihSecond =>
      exact .trans _ _ _ ihFirst ihSecond

/-- The inverse translation also commutes with declaration lifting. -/
@[simp] theorem toPure_liftClosed (term : Legacy.Tm 0) :
    Legacy.toPure (liftClosed term : Legacy.Tm n) =
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.DeclarationEnv.liftClosed
        (n := n) (Legacy.toPure term) := by
  apply Function.LeftInverse.injective (fun oldTerm =>
    Legacy.toPure_ofPure oldTerm)
  rw [Legacy.ofPure_toPure, ofPure_oldLiftClosed, Legacy.ofPure_toPure]

/-- Conversion is closed under every former declaration-reduction context. -/
theorem convDecl_map {environment : OldEnvironment}
    {sourceDepth targetDepth : Nat}
    {function :
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax.PureTm sourceDepth →
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax.PureTm targetDepth}
    (mapsStep : ∀ {left right}, RedDecl environment left right →
      RedDecl environment (function left) (function right))
    {left right :
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax.PureTm sourceDepth}
    (conversion : ConvDecl environment left right) :
    ConvDecl environment (function left) (function right) := by
  induction conversion with
  | rel left right step => exact .rel _ _ (mapsStep step)
  | refl term => exact .refl _
  | symm left right conversion ih => exact .symm _ _ ih
  | trans left middle right first second ihFirst ihSecond =>
      exact .trans _ _ _ ihFirst ihSecond

/-- A common declaration step reflects to former declaration conversion.
Head equality reflects to conversion reflexivity; delta roots reflect to the
former delta rule. -/
theorem convDecl_of_step {environment : OldEnvironment}
    {left right : Legacy.Tm n}
    (step : Step
      (extendRules Legacy.rules (ofOldEnvironment environment)).headEq
      left right
      (extendRules Legacy.rules (ofOldEnvironment environment)).computation) :
    ConvDecl environment (Legacy.toPure left) (Legacy.toPure right) := by
  change Step Legacy.HeadEq left right
    (rootComputation Legacy.rules (ofOldEnvironment environment)) at step
  induction step with
  | betaPi body argument =>
      exact redDecl_implies_conv (by
        simpa only [Legacy.toPure, Legacy.toPure_inst0] using
          (RedDecl.core
            (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Reduction.Red.betaPi
              (Legacy.toPure body) (Legacy.toPure argument))))
  | betaSigmaFst first second =>
      exact redDecl_implies_conv (by
        simpa only [Legacy.toPure] using
          (RedDecl.core
            (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Reduction.Red.betaSigmaFst
              (Legacy.toPure first) (Legacy.toPure second))))
  | betaSigmaSnd first second =>
      exact redDecl_implies_conv (by
        simpa only [Legacy.toPure] using
          (RedDecl.core
            (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Reduction.Red.betaSigmaSnd
              (Legacy.toPure first) (Legacy.toPure second))))
  | head equality =>
      cases equality
      exact .refl _
  | root computation =>
      cases computation with
      | inherited inherited => exact inherited.elim
      | delta unfolding =>
          apply redDecl_implies_conv
          simpa only [Legacy.toPure, toPure_liftClosed] using
            (RedDecl.deltaConst (valueOf_reflect unfolding))
      | declared declared => exact declared.elim
  | congPiDom step ih =>
      simpa only [Legacy.toPure] using convDecl_map
        (function := fun term =>
          .pi term (Legacy.toPure _))
        (fun reduction => RedDecl.congPiDom reduction) ih
  | congPiCod step ih =>
      simpa only [Legacy.toPure] using convDecl_map
        (function := fun term =>
          .pi (Legacy.toPure _) term)
        (fun reduction => RedDecl.congPiCod reduction) ih
  | congSigmaDom step ih =>
      simpa only [Legacy.toPure] using convDecl_map
        (function := fun term =>
          .sigma term (Legacy.toPure _))
        (fun reduction => RedDecl.congSigmaDom reduction) ih
  | congSigmaCod step ih =>
      simpa only [Legacy.toPure] using convDecl_map
        (function := fun term =>
          .sigma (Legacy.toPure _) term)
        (fun reduction => RedDecl.congSigmaCod reduction) ih
  | congIdTy step ih =>
      simpa only [Legacy.toPure] using convDecl_map
        (function := fun term =>
          .id term (Legacy.toPure _) (Legacy.toPure _))
        (fun reduction => RedDecl.congIdTy reduction) ih
  | congIdLeft step ih =>
      simpa only [Legacy.toPure] using convDecl_map
        (function := fun term =>
          .id (Legacy.toPure _) term (Legacy.toPure _))
        (fun reduction => RedDecl.congIdLeft reduction) ih
  | congIdRight step ih =>
      simpa only [Legacy.toPure] using convDecl_map
        (function := fun term =>
          .id (Legacy.toPure _) (Legacy.toPure _) term)
        (fun reduction => RedDecl.congIdRight reduction) ih
  | congLam step ih =>
      simpa only [Legacy.toPure] using convDecl_map
        (function := fun term =>
          Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax.PureTm.lam term)
        (fun reduction => RedDecl.congLam reduction) ih
  | congAppFun step ih =>
      simpa only [Legacy.toPure] using convDecl_map
        (function := fun term => .app term (Legacy.toPure _))
        (fun reduction => RedDecl.congAppFun reduction) ih
  | congAppArg step ih =>
      simpa only [Legacy.toPure] using convDecl_map
        (function := fun term => .app (Legacy.toPure _) term)
        (fun reduction => RedDecl.congAppArg reduction) ih
  | congPairFst step ih =>
      simpa only [Legacy.toPure] using convDecl_map
        (function := fun term => .pair term (Legacy.toPure _))
        (fun reduction => RedDecl.congPairFst reduction) ih
  | congPairSnd step ih =>
      simpa only [Legacy.toPure] using convDecl_map
        (function := fun term => .pair (Legacy.toPure _) term)
        (fun reduction => RedDecl.congPairSnd reduction) ih
  | congFst step ih =>
      simpa only [Legacy.toPure] using convDecl_map
        (function := fun term =>
          Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax.PureTm.fst term)
        (fun reduction => RedDecl.congFst reduction) ih
  | congSnd step ih =>
      simpa only [Legacy.toPure] using convDecl_map
        (function := fun term =>
          Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax.PureTm.snd term)
        (fun reduction => RedDecl.congSnd reduction) ih
  | congRefl step ih =>
      simpa only [Legacy.toPure] using convDecl_map
        (function := fun term =>
          Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax.PureTm.refl term)
        (fun reduction => RedDecl.congRefl reduction) ih

/-- Common conversion is reflected exactly by former declaration conversion. -/
theorem convDecl_of_conv {environment : OldEnvironment}
    {left right : Legacy.Tm n}
    (conversion : Conv
      (extendRules Legacy.rules (ofOldEnvironment environment)).headEq
      left right
      (extendRules Legacy.rules (ofOldEnvironment environment)).computation) :
    ConvDecl environment (Legacy.toPure left) (Legacy.toPure right) := by
  induction conversion with
  | rel left right step => exact convDecl_of_step step
  | refl term => exact .refl _
  | symm left right conversion ih => exact .symm _ _ ih
  | trans left middle right first second ihFirst ihSecond =>
      exact .trans _ _ _ ihFirst ihSecond

/-! ## Typing correspondence -/

theorem typeOf_toSignature {environment : OldEnvironment}
    {name : DeclName}
    {type : Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax.PureTm 0}
    (lookup :
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.DeclarationEnv.typeOf?
        environment name = some type) :
    (ofOldEnvironment environment).typeOf? name =
      some (Legacy.ofPure type) := by
  rw [typeOf_ofOldEnvironment, lookup]
  rfl

/-- Former declaration typing embeds constructor-for-constructor in the common
declaration-aware Legacy presentation. -/
theorem hasType_of_hasTypeDecl {environment : OldEnvironment}
    {context : Mettapedia.Languages.MeTTa.Pure.Intrinsic.Context.Ctx n}
    {term type : Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax.PureTm n}
    (typing : HasTypeDecl environment context term type) :
    HasType (extendRules Legacy.rules (ofOldEnvironment environment))
      (Legacy.ofPureCtx context) (Legacy.ofPure term) (Legacy.ofPure type) := by
  induction typing with
  | u0_type context =>
      exact .headType Legacy.HeadTyping.groundMarker
  | var index =>
      simpa only [Legacy.ofPure, Legacy.lookup_ofPureCtx] using
        (HasType.var
          (R := extendRules Legacy.rules (ofOldEnvironment environment))
          (Γ := Legacy.ofPureCtx _) index)
  | @const n context name oldType lookup =>
      simpa only [Legacy.ofPure, ofPure_oldLiftClosed] using
        (HasType.const
          (R := extendRules Legacy.rules (ofOldEnvironment environment))
          (Γ := Legacy.ofPureCtx context) (name := name)
          (type := Legacy.ofPure oldType)
          (combinedType_of_signature Legacy.rules
            (ofOldEnvironment environment) rfl
            (typeOf_toSignature lookup)))
  | pi_form domainTyping codomainTyping ihDomain ihCodomain =>
      exact .piForm ihDomain Legacy.IsUniverse.marker ihCodomain
        Legacy.IsUniverse.marker Legacy.Join.marker
  | sigma_form domainTyping codomainTyping ihDomain ihCodomain =>
      exact .sigmaForm ihDomain Legacy.IsUniverse.marker ihCodomain
        Legacy.IsUniverse.marker Legacy.Join.marker
  | lam_intro bodyTyping ihBody => exact .lamIntro ihBody
  | app_elim functionTyping argumentTyping ihFunction ihArgument =>
      simpa only [Legacy.ofPure, Legacy.ofPure_inst0] using
        (HasType.appElim ihFunction ihArgument)
  | pair_intro firstTyping secondTyping ihFirst ihSecond =>
      have translatedSecond := ihSecond
      rw [Legacy.ofPure_inst0] at translatedSecond
      exact .pairIntro ihFirst translatedSecond
  | fst_elim pairTyping ihPair => exact .fstElim ihPair
  | snd_elim pairTyping ihPair =>
      simpa only [Legacy.ofPure, Legacy.ofPure_inst0] using
        (HasType.sndElim ihPair)
  | id_form typeTyping leftTyping rightTyping ihType ihLeft ihRight =>
      exact .idForm ihType Legacy.IsUniverse.marker ihLeft ihRight
  | refl_intro termTyping ihTerm => exact .reflIntro ihTerm
  | conv prior conversion ihPrior =>
      exact .conv ihPrior (conv_of_convDecl conversion)

/-- Common declaration-aware Legacy typing reflects to the former declaration
judgment.  Thus the old development is a model of the common spine, not a
parallel extension that can drift semantically. -/
theorem hasTypeDecl_of_hasType {environment : OldEnvironment}
    {context : Legacy.Ctx n} {term type : Legacy.Tm n}
    (typing : HasType
      (extendRules Legacy.rules (ofOldEnvironment environment))
      context term type) :
    HasTypeDecl environment (Legacy.toPureCtx context)
      (Legacy.toPure term) (Legacy.toPure type) := by
  induction typing with
  | headType headTyping =>
      cases headTyping
      exact .u0_type _
  | @var n context index =>
      simpa only [Legacy.toPure, Legacy.lookup_toPureCtx] using
        (HasTypeDecl.var (E := environment)
          (Γ := Legacy.toPureCtx context) index)
  | @const n context name declaredType lookup =>
      have signatureLookup :
          (ofOldEnvironment environment).typeOf? name = some declaredType := by
        change combinedType Legacy.rules (ofOldEnvironment environment) name =
          some declaredType at lookup
        change (ofOldEnvironment environment).typeOf? name =
          some declaredType at lookup
        exact lookup
      simpa only [Legacy.toPure, toPure_liftClosed] using
        (HasTypeDecl.const (E := environment)
          (typeOf_reflect signatureLookup))
  | piForm domainTyping domainUniverse codomainTyping codomainUniverse join
      ihDomain ihCodomain =>
      cases domainUniverse
      cases codomainUniverse
      cases join
      exact .pi_form ihDomain ihCodomain
  | sigmaForm domainTyping domainUniverse codomainTyping codomainUniverse join
      ihDomain ihCodomain =>
      cases domainUniverse
      cases codomainUniverse
      cases join
      exact .sigma_form ihDomain ihCodomain
  | lamIntro bodyTyping ihBody => exact .lam_intro ihBody
  | appElim functionTyping argumentTyping ihFunction ihArgument =>
      simpa only [Legacy.toPure, Legacy.toPure_inst0] using
        (HasTypeDecl.app_elim ihFunction ihArgument)
  | pairIntro firstTyping secondTyping ihFirst ihSecond =>
      have oldSecond := ihSecond
      rw [Legacy.toPure_inst0] at oldSecond
      exact .pair_intro ihFirst oldSecond
  | fstElim pairTyping ihPair => exact .fst_elim ihPair
  | sndElim pairTyping ihPair =>
      simpa only [Legacy.toPure, Legacy.toPure_inst0] using
        (HasTypeDecl.snd_elim ihPair)
  | idForm typeTyping typeUniverse leftTyping rightTyping
      ihType ihLeft ihRight =>
      cases typeUniverse
      exact .id_form ihType ihLeft ihRight
  | reflIntro termTyping ihTerm => exact .refl_intro ihTerm
  | cumul prior order ihPrior => exact order.elim
  | conv prior conversion ihPrior =>
      exact .conv ihPrior (convDecl_of_conv conversion)

theorem convDecl_iff_conv {environment : OldEnvironment}
    {left right : Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax.PureTm n} :
    ConvDecl environment left right ↔
      Conv (extendRules Legacy.rules (ofOldEnvironment environment)).headEq
        (Legacy.ofPure left) (Legacy.ofPure right)
        (extendRules Legacy.rules
          (ofOldEnvironment environment)).computation := by
  constructor
  · exact conv_of_convDecl
  · intro conversion
    simpa only [Legacy.toPure_ofPure] using convDecl_of_conv conversion

theorem hasTypeDecl_iff_hasType {environment : OldEnvironment}
    {context : Mettapedia.Languages.MeTTa.Pure.Intrinsic.Context.Ctx n}
    {term type : Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax.PureTm n} :
    HasTypeDecl environment context term type ↔
      HasType (extendRules Legacy.rules (ofOldEnvironment environment))
        (Legacy.ofPureCtx context) (Legacy.ofPure term)
        (Legacy.ofPure type) := by
  constructor
  · exact hasType_of_hasTypeDecl
  · intro typing
    simpa only [Legacy.toPureCtx_ofPureCtx, Legacy.toPure_ofPure] using
      hasTypeDecl_of_hasType typing

end LegacyCompatibility
end Declaration
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
