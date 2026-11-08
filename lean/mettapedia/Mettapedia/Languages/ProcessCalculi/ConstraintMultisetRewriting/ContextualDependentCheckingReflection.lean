import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAlgorithmReflection

/-!
# Checking certificates strengthen through exact context inclusions

The comparison reflection theorem extends to cumulative subtype checks and
the existing bidirectional checking relation. Synthesis reconstructs its
inferred annotation in the smaller context. This reflection does not choose
inhabitants for discarded declarations and does not rerun the checker.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCheckingReflection

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedEquality.StrongNormalization
open ContextualDependentAlgorithmReflection

variable {Head : Type} {R : Rules Head} (reflects : ContextualDependentReductionReflection.RootReflectsInjections R.computation)

include reflects in
theorem below_reflects {m : Nat} {target : Ctx Head m} {first second : Tm Head m}
    (proof : BelowAlgorithm R target first second) :
    ∀ {n : Nat} (source : Ctx Head n) (rho : Ren n m), Function.Injective rho → CtxRen source target rho →
      ∀ left right, Presentation.rename rho left = first → Presentation.rename rho right = second →
        BelowAlgorithm R source left right := by
  induction proof with
  | conv comparison =>
      intro n source rho injective compatible left right hl hr
      exact .conv (algorithm_reflects reflects comparison source rho injective compatible left right hl hr)
  | @universes m target first second firstHead secondHead firstRed secondRed cumulative =>
      intro n source rho injective compatible left right hl hr
      subst first; subst second
      exact .universes (reduce_head reflects injective firstRed) (reduce_head reflects injective secondRed) cumulative
  | @pi m target first second domain domain' codomain codomain' firstRed secondRed domains _ ih =>
      intro n source rho injective compatible left right hl hr
      subst first; subst second
      obtain ⟨a, b, firstRed', rfl, rfl⟩ := reduce_pi reflects injective firstRed
      obtain ⟨a', b', secondRed', rfl, rfl⟩ := reduce_pi reflects injective secondRed
      exact .pi firstRed' secondRed'
        (algorithm_reflects reflects domains source rho injective compatible a a' rfl rfl)
        (ih (.snoc source a) (liftRen rho) (ContextualDependentPruning.liftRen_injective injective)
          (compatible.snoc a) b b' rfl rfl)
  | @sigma m target first second domain domain' codomain codomain' firstRed secondRed _ _ ihDomain ihBody =>
      intro n source rho injective compatible left right hl hr
      subst first; subst second
      obtain ⟨a, b, firstRed', rfl, rfl⟩ := reduce_sigma reflects injective firstRed
      obtain ⟨a', b', secondRed', rfl, rfl⟩ := reduce_sigma reflects injective secondRed
      exact .sigma firstRed' secondRed'
        (ihDomain source rho injective compatible a a' rfl rfl)
        (ihBody (.snoc source a) (liftRen rho) (ContextualDependentPruning.liftRen_injective injective)
          (compatible.snoc a) b b' rfl rfl)

def Reflects (mode : Mode) {m : Nat} (target : Ctx Head m) (term type : Tm Head m) : Prop :=
  match mode with
  | .synth => ∀ {n : Nat} (source : Ctx Head n) (rho : Ren n m),
      Function.Injective rho → CtxRen source target rho →
      ∀ original, Presentation.rename rho original = term →
        ∃ annotation, type = Presentation.rename rho annotation ∧
          CheckingAlgorithm R .synth source original annotation
  | .check => ∀ {n : Nat} (source : Ctx Head n) (rho : Ren n m),
      Function.Injective rho → CtxRen source target rho →
      ∀ original annotation, Presentation.rename rho original = term → Presentation.rename rho annotation = type →
        CheckingAlgorithm R .check source original annotation

include reflects in
theorem checking_reflects {mode : Mode} {m : Nat} {target : Ctx Head m} {term type : Tm Head m}
    (proof : CheckingAlgorithm R mode target term type) : Reflects (R := R) mode target term type := by
  induction proof with
  | @var m target index =>
      intro n source rho injective compatible original image
      obtain ⟨index', rfl, rfl⟩ := rename_eq_var image
      exact ⟨Ctx.lookup source index', compatible index', .var index'⟩
  | @const m target name type known =>
      intro n source rho injective compatible original image
      obtain rfl := TypedEquality.StrongNormalization.rename_eq_const image
      exact ⟨liftClosed type, (rename_liftClosed rho type).symm, .const known⟩
  | @head m target head level typing =>
      intro n source rho injective compatible original image
      obtain rfl := rename_eq_head image
      exact ⟨.head level, rfl, .head typing⟩
  | @pi m target domain domainType codomain codomainType first second level
      _ firstRed firstUniverse _ secondRed secondUniverse join ihDomain ihBody =>
      intro n source rho injective compatible original image
      obtain ⟨a, b, rfl, rfl, rfl⟩ := TypedEquality.StrongNormalization.rename_eq_pi image
      obtain ⟨aType, rfl, domainChecked⟩ := ihDomain source rho injective compatible a rfl
      obtain ⟨bType, rfl, bodyChecked⟩ := ihBody (.snoc source a) (liftRen rho)
        (ContextualDependentPruning.liftRen_injective injective) (compatible.snoc a) b rfl
      exact ⟨.head level, rfl, .pi domainChecked (reduce_head reflects injective firstRed) firstUniverse
        bodyChecked (reduce_head reflects (ContextualDependentPruning.liftRen_injective injective) secondRed) secondUniverse join⟩
  | @sigma m target domain domainType codomain codomainType first second level
      _ firstRed firstUniverse _ secondRed secondUniverse join ihDomain ihBody =>
      intro n source rho injective compatible original image
      obtain ⟨a, b, rfl, rfl, rfl⟩ := TypedEquality.StrongNormalization.rename_eq_sigma image
      obtain ⟨aType, rfl, domainChecked⟩ := ihDomain source rho injective compatible a rfl
      obtain ⟨bType, rfl, bodyChecked⟩ := ihBody (.snoc source a) (liftRen rho)
        (ContextualDependentPruning.liftRen_injective injective) (compatible.snoc a) b rfl
      exact ⟨.head level, rfl, .sigma domainChecked (reduce_head reflects injective firstRed) firstUniverse
        bodyChecked (reduce_head reflects (ContextualDependentPruning.liftRen_injective injective) secondRed) secondUniverse join⟩
  | @id m target carrier carrierType first second level _ red universeWitness _ _ ihCarrier ihFirst ihSecond =>
      intro n source rho injective compatible original image
      obtain ⟨a, x, y, rfl, rfl, rfl, rfl⟩ := TypedEquality.StrongNormalization.rename_eq_id image
      obtain ⟨aType, rfl, carrierChecked⟩ := ihCarrier source rho injective compatible a rfl
      exact ⟨.head level, rfl, .id carrierChecked (reduce_head reflects injective red) universeWitness
        (ihFirst source rho injective compatible x a rfl rfl)
        (ihSecond source rho injective compatible y a rfl rfl)⟩
  | @refl m target value type _ ih =>
      intro n source rho injective compatible original image
      obtain ⟨value', rfl, rfl⟩ := TypedEquality.StrongNormalization.rename_eq_refl image
      obtain ⟨type', rfl, checked⟩ := ih source rho injective compatible value' rfl
      exact ⟨.id type' value' value', rfl, .refl checked⟩
  | @app m target function argument functionType domain codomain _ red _ ihFunction ihArgument =>
      intro n source rho injective compatible original image
      obtain ⟨function', argument', rfl, rfl, rfl⟩ := TypedEquality.StrongNormalization.rename_eq_app image
      obtain ⟨functionType', rfl, functionChecked⟩ := ihFunction source rho injective compatible function' rfl
      obtain ⟨domain', codomain', red', rfl, rfl⟩ := reduce_pi reflects injective red
      exact ⟨inst0 argument' codomain', (rename_inst0 rho argument' codomain').symm,
        .app functionChecked red' (ihArgument source rho injective compatible argument' domain' rfl rfl)⟩
  | @fst m target value type domain codomain _ red ih =>
      intro n source rho injective compatible original image
      obtain ⟨value', rfl, rfl⟩ := TypedEquality.StrongNormalization.rename_eq_fst image
      obtain ⟨type', rfl, checked⟩ := ih source rho injective compatible value' rfl
      obtain ⟨domain', codomain', red', rfl, rfl⟩ := reduce_sigma reflects injective red
      exact ⟨domain', rfl, .fst checked red'⟩
  | @snd m target value type domain codomain _ red ih =>
      intro n source rho injective compatible original image
      obtain ⟨value', rfl, rfl⟩ := TypedEquality.StrongNormalization.rename_eq_snd image
      obtain ⟨type', rfl, checked⟩ := ih source rho injective compatible value' rfl
      obtain ⟨domain', codomain', red', rfl, rfl⟩ := reduce_sigma reflects injective red
      exact ⟨inst0 (.fst value') codomain', (rename_inst0 rho (.fst value') codomain').symm,
        .snd checked red'⟩
  | @redex m target argument domain body codomain _ _ ihArgument ihBody =>
      intro n source rho injective compatible original image
      obtain ⟨function', argument', rfl, functionImage, rfl⟩ := TypedEquality.StrongNormalization.rename_eq_app image
      obtain ⟨body', rfl, rfl⟩ := TypedEquality.StrongNormalization.rename_eq_lam functionImage
      obtain ⟨domain', rfl, argumentChecked⟩ := ihArgument source rho injective compatible argument' rfl
      obtain ⟨codomain', rfl, bodyChecked⟩ := ihBody (.snoc source domain') (liftRen rho)
        (ContextualDependentPruning.liftRen_injective injective) (compatible.snoc domain') body' rfl
      exact ⟨inst0 argument' codomain', (rename_inst0 rho argument' codomain').symm,
        .redex argumentChecked bodyChecked⟩
  | @lamCheck m target body type domain codomain red _ ih =>
      intro n source rho injective compatible original annotation image typeImage
      obtain ⟨body', rfl, rfl⟩ := TypedEquality.StrongNormalization.rename_eq_lam image
      subst type
      obtain ⟨domain', codomain', red', rfl, rfl⟩ := reduce_pi reflects injective red
      exact .lamCheck red' (ih (.snoc source domain') (liftRen rho)
        (ContextualDependentPruning.liftRen_injective injective) (compatible.snoc domain') body' codomain' rfl rfl)
  | @pairCheck m target first second type domain codomain red _ _ ihFirst ihSecond =>
      intro n source rho injective compatible original annotation image typeImage
      obtain ⟨first', second', rfl, rfl, rfl⟩ := TypedEquality.StrongNormalization.rename_eq_pair image
      subst type
      obtain ⟨domain', codomain', red', rfl, rfl⟩ := reduce_sigma reflects injective red
      exact .pairCheck red' (ihFirst source rho injective compatible first' domain' rfl rfl)
        (ihSecond source rho injective compatible second' (inst0 first' codomain') rfl (rename_inst0 rho first' codomain'))
  | @reflCheck m target value type carrier first second red _ firstSame secondSame ih =>
      intro n source rho injective compatible original annotation image typeImage
      obtain ⟨value', rfl, rfl⟩ := TypedEquality.StrongNormalization.rename_eq_refl image
      subst type
      obtain ⟨carrier', first', second', red', rfl, rfl, rfl⟩ := reduce_id reflects injective red
      exact .reflCheck red' (ih source rho injective compatible value' carrier' rfl rfl)
        (algorithm_reflects reflects firstSame source rho injective compatible value' first' carrier' rfl rfl rfl)
        (algorithm_reflects reflects secondSame source rho injective compatible value' second' carrier' rfl rfl rfl)
  | @switch m target value type expected _ below ih =>
      intro n source rho injective compatible original annotation image typeImage
      subst value; subst expected
      obtain ⟨type', rfl, checked⟩ := ih source rho injective compatible original rfl
      exact .switch checked (below_reflects reflects below source rho injective compatible type' annotation rfl rfl)

end ContextualDependentCheckingReflection
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
