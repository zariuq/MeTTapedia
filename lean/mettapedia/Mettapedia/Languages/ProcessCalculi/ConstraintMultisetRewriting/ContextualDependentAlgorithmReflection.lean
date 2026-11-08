import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentReductionReflection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPruning

/-!
# Reflecting algorithmic comparisons through context inclusions

An injective variable map whose declarations agree syntactically reflects
the existing conversion relation. The neutral case reconstructs its inferred
type as well as the comparison. Omitted declarations need no inhabitants.
The root computation must reflect renaming; head equalities are retained.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentAlgorithmReflection

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open TypedEquality TypedEquality.Normalization TypedEquality.StrongNormalization

variable {Head : Type} {R : Rules Head}

theorem rename_eq_var {n m : Nat} {rho : Ren n m} {term : Tm Head n} {index : Fin m}
    (image : Presentation.rename rho term = .var index) :
    ∃ original, term = .var original ∧ rho original = index := by
  cases term <;> simp only [Presentation.rename, reduceCtorEq, Tm.var.injEq] at image
  exact ⟨_, rfl, image⟩

theorem rename_eq_head {n m : Nat} {rho : Ren n m} {term : Tm Head n} {head : Head}
    (image : Presentation.rename rho term = .head head) : term = .head head := by
  cases term <;> simp only [Presentation.rename, reduceCtorEq, Tm.head.injEq] at image
  subst head
  rfl

variable (reflects : ContextualDependentReductionReflection.RootReflectsInjections R.computation)

include reflects in
theorem reduce_pi {n m : Nat} {rho : Ren n m} {term : Tm Head n}
    {domain : Tm Head m} {codomain : Tm Head (m + 1)}
    (injective : Function.Injective rho)
    (red : TypedEquality.Reduces R (Presentation.rename rho term) (.pi domain codomain)) :
    ∃ first second, TypedEquality.Reduces R term (.pi first second) ∧
      domain = Presentation.rename rho first ∧ codomain = Presentation.rename (liftRen rho) second := by
  obtain ⟨result, red, image⟩ := ContextualDependentReductionReflection.reduces_reflects reflects injective red
  obtain ⟨first, second, rfl, domainImage, codomainImage⟩ := TypedEquality.StrongNormalization.rename_eq_pi image.symm
  exact ⟨first, second, red, domainImage.symm, codomainImage.symm⟩

include reflects in
theorem reduce_sigma {n m : Nat} {rho : Ren n m} {term : Tm Head n}
    {domain : Tm Head m} {codomain : Tm Head (m + 1)}
    (injective : Function.Injective rho)
    (red : TypedEquality.Reduces R (Presentation.rename rho term) (.sigma domain codomain)) :
    ∃ first second, TypedEquality.Reduces R term (.sigma first second) ∧
      domain = Presentation.rename rho first ∧ codomain = Presentation.rename (liftRen rho) second := by
  obtain ⟨result, red, image⟩ := ContextualDependentReductionReflection.reduces_reflects reflects injective red
  obtain ⟨first, second, rfl, domainImage, codomainImage⟩ := TypedEquality.StrongNormalization.rename_eq_sigma image.symm
  exact ⟨first, second, red, domainImage.symm, codomainImage.symm⟩

include reflects in
theorem reduce_id {n m : Nat} {rho : Ren n m} {term : Tm Head n} {carrier first second : Tm Head m}
    (injective : Function.Injective rho)
    (red : TypedEquality.Reduces R (Presentation.rename rho term) (.id carrier first second)) :
    ∃ type left right, TypedEquality.Reduces R term (.id type left right) ∧
      carrier = Presentation.rename rho type ∧ first = Presentation.rename rho left ∧
      second = Presentation.rename rho right := by
  obtain ⟨result, red, image⟩ := ContextualDependentReductionReflection.reduces_reflects reflects injective red
  obtain ⟨type, left, right, rfl, ht, hl, hr⟩ := TypedEquality.StrongNormalization.rename_eq_id image.symm
  exact ⟨type, left, right, red, ht.symm, hl.symm, hr.symm⟩

include reflects in
theorem reduce_head {n m : Nat} {rho : Ren n m} {term : Tm Head n} {head : Head}
    (injective : Function.Injective rho)
    (red : TypedEquality.Reduces R (Presentation.rename rho term) (.head head)) :
    TypedEquality.Reduces R term (.head head) := by
  obtain ⟨result, red, image⟩ := ContextualDependentReductionReflection.reduces_reflects reflects injective red
  obtain rfl := rename_eq_head image.symm
  exact red

include reflects in
theorem reduce_refl {n m : Nat} {rho : Ren n m} {term : Tm Head n} {value : Tm Head m}
    (injective : Function.Injective rho)
    (red : TypedEquality.Reduces R (Presentation.rename rho term) (.refl value)) :
    ∃ original, TypedEquality.Reduces R term (.refl original) ∧ value = Presentation.rename rho original := by
  obtain ⟨result, red, image⟩ := ContextualDependentReductionReflection.reduces_reflects reflects injective red
  obtain ⟨original, rfl, same⟩ := TypedEquality.StrongNormalization.rename_eq_refl image.symm
  exact ⟨original, red, same.symm⟩

def Reflects : AlgorithmStatement Head → Prop
  | .compare (n := m) target first second type =>
      ∀ {n : Nat} (source : Ctx Head n) (rho : Ren n m), Function.Injective rho → CtxRen source target rho →
        ∀ left right annotation, Presentation.rename rho left = first → Presentation.rename rho right = second →
          Presentation.rename rho annotation = type → Algorithm R (.compare source left right annotation)
  | .neutral (n := m) target first second type =>
      ∀ {n : Nat} (source : Ctx Head n) (rho : Ren n m), Function.Injective rho → CtxRen source target rho →
        ∀ left right, Presentation.rename rho left = first → Presentation.rename rho right = second →
          ∃ annotation, type = Presentation.rename rho annotation ∧ Algorithm R (.neutral source left right annotation)
  | .types (n := m) target first second =>
      ∀ {n : Nat} (source : Ctx Head n) (rho : Ren n m), Function.Injective rho → CtxRen source target rho →
        ∀ left right, Presentation.rename rho left = first → Presentation.rename rho right = second →
          Algorithm R (.types source left right)

theorem rename_freshApp {n m : Nat} (rho : Ren n m) (term : Tm Head n) :
    Presentation.rename (liftRen rho) (.app (Presentation.rename wk term) (.var 0)) =
      .app (Presentation.rename wk (Presentation.rename rho term)) (.var 0) := by
  simp only [Presentation.rename, rename_liftRen_wk]
  rfl

include reflects in
theorem algorithm_reflects {statement : AlgorithmStatement Head} (proof : Algorithm R statement) :
    Reflects (R := R) statement := by
  induction proof with
  | @pi m target a b type domain codomain red comparison ih =>
      intro n source rho injective compatible left right annotation ha hb ht
      subst a; subst b; subst type
      obtain ⟨domain', codomain', red', rfl, rfl⟩ := reduce_pi reflects injective red
      exact .pi red' (ih (.snoc source domain') (liftRen rho)
        (ContextualDependentPruning.liftRen_injective injective) (compatible.snoc domain')
        _ _ codomain' (rename_freshApp rho left) (rename_freshApp rho right) rfl)
  | @sigma m target a b type domain codomain red _ _ ihFirst ihSecond =>
      intro n source rho injective compatible left right annotation ha hb ht
      subst a; subst b; subst type
      obtain ⟨domain', codomain', red', rfl, rfl⟩ := reduce_sigma reflects injective red
      refine .sigma red'
        (ihFirst source rho injective compatible (.fst left) (.fst right) domain' rfl rfl rfl) ?_
      exact ihSecond source rho injective compatible (.snd left) (.snd right)
        (inst0 (.fst left) codomain') rfl rfl (rename_inst0 rho (.fst left) codomain')
  | @sort m target a b type level red universeWitness _ ih =>
      intro n source rho injective compatible left right annotation ha hb ht
      subst a; subst b; subst type
      exact .sort (reduce_head reflects injective red) universeWitness
        (ih source rho injective compatible left right rfl rfl)
  | @reflexivity m target a b type carrier x y a' b' redType redFirst redSecond _ ih =>
      intro n source rho injective compatible left right annotation ha hb ht
      subst a; subst b; subst type
      obtain ⟨carrier', x', y', redType', rfl, rfl, rfl⟩ := reduce_id reflects injective redType
      obtain ⟨first, redFirst', rfl⟩ := reduce_refl reflects injective redFirst
      obtain ⟨second, redSecond', rfl⟩ := reduce_refl reflects injective redSecond
      exact .reflexivity redType' redFirst' redSecond'
        (ih source rho injective compatible first second carrier' rfl rfl rfl)
  | @neutralAt m target a b type a' b' inferred redFirst redSecond _ ih =>
      intro n source rho injective compatible left right annotation ha hb ht
      subst a; subst b; subst type
      obtain ⟨first, redFirst', rfl⟩ := ContextualDependentReductionReflection.reduces_reflects reflects injective redFirst
      obtain ⟨second, redSecond', rfl⟩ := ContextualDependentReductionReflection.reduces_reflects reflects injective redSecond
      obtain ⟨inferred', _, comparison⟩ := ih source rho injective compatible first second rfl rfl
      exact .neutralAt redFirst' redSecond' comparison
  | @var m target index =>
      intro n source rho injective compatible left right ha hb
      obtain ⟨first, rfl, firstImage⟩ := rename_eq_var ha
      obtain ⟨second, rfl, secondImage⟩ := rename_eq_var hb
      have same := injective (firstImage.trans secondImage.symm)
      subst second
      subst index
      exact ⟨Ctx.lookup source first, compatible first, .var first⟩
  | @const m target name type known =>
      intro n source rho injective compatible left right ha hb
      obtain rfl := TypedEquality.StrongNormalization.rename_eq_const ha
      obtain rfl := TypedEquality.StrongNormalization.rename_eq_const hb
      exact ⟨liftClosed type, (rename_liftClosed rho type).symm, .const known⟩
  | @app m target f g a b inferred domain codomain _ red _ ihFunction ihArgument =>
      intro n source rho injective compatible left right ha hb
      obtain ⟨function, argument, rfl, rfl, rfl⟩ := TypedEquality.StrongNormalization.rename_eq_app ha
      obtain ⟨function', argument', rfl, rfl, rfl⟩ := TypedEquality.StrongNormalization.rename_eq_app hb
      obtain ⟨inferred', rfl, functions⟩ := ihFunction source rho injective compatible function function' rfl rfl
      obtain ⟨domain', codomain', red', rfl, rfl⟩ := reduce_pi reflects injective red
      exact ⟨inst0 argument codomain', (rename_inst0 rho argument codomain').symm,
        .app functions red' (ihArgument source rho injective compatible argument argument' domain' rfl rfl rfl)⟩
  | @fst m target p q inferred domain codomain _ red ih =>
      intro n source rho injective compatible left right ha hb
      obtain ⟨pair, rfl, rfl⟩ := TypedEquality.StrongNormalization.rename_eq_fst ha
      obtain ⟨pair', rfl, rfl⟩ := TypedEquality.StrongNormalization.rename_eq_fst hb
      obtain ⟨inferred', rfl, pairs⟩ := ih source rho injective compatible pair pair' rfl rfl
      obtain ⟨domain', codomain', red', rfl, rfl⟩ := reduce_sigma reflects injective red
      exact ⟨domain', rfl, .fst pairs red'⟩
  | @snd m target p q inferred domain codomain _ red ih =>
      intro n source rho injective compatible left right ha hb
      obtain ⟨pair, rfl, rfl⟩ := TypedEquality.StrongNormalization.rename_eq_snd ha
      obtain ⟨pair', rfl, rfl⟩ := TypedEquality.StrongNormalization.rename_eq_snd hb
      obtain ⟨inferred', rfl, pairs⟩ := ih source rho injective compatible pair pair' rfl rfl
      obtain ⟨domain', codomain', red', rfl, rfl⟩ := reduce_sigma reflects injective red
      exact ⟨inst0 (.fst pair) codomain', (rename_inst0 rho (.fst pair) codomain').symm,
        .snd pairs red'⟩
  | @heads m target a b head head' redFirst redSecond same =>
      intro n source rho injective compatible left right ha hb
      subst a; subst b
      exact .heads (reduce_head reflects injective redFirst) (reduce_head reflects injective redSecond) same
  | @piTypes m target a b domain domain' codomain codomain' redFirst redSecond _ _ ihDomain ihCodomain =>
      intro n source rho injective compatible left right ha hb
      subst a; subst b
      obtain ⟨first, firstBody, redFirst', rfl, rfl⟩ := reduce_pi reflects injective redFirst
      obtain ⟨second, secondBody, redSecond', rfl, rfl⟩ := reduce_pi reflects injective redSecond
      exact .piTypes redFirst' redSecond'
        (ihDomain source rho injective compatible first second rfl rfl)
        (ihCodomain (.snoc source first) (liftRen rho)
          (ContextualDependentPruning.liftRen_injective injective) (compatible.snoc first)
          firstBody secondBody rfl rfl)
  | @sigmaTypes m target a b domain domain' codomain codomain' redFirst redSecond _ _ ihDomain ihCodomain =>
      intro n source rho injective compatible left right ha hb
      subst a; subst b
      obtain ⟨first, firstBody, redFirst', rfl, rfl⟩ := reduce_sigma reflects injective redFirst
      obtain ⟨second, secondBody, redSecond', rfl, rfl⟩ := reduce_sigma reflects injective redSecond
      exact .sigmaTypes redFirst' redSecond'
        (ihDomain source rho injective compatible first second rfl rfl)
        (ihCodomain (.snoc source first) (liftRen rho)
          (ContextualDependentPruning.liftRen_injective injective) (compatible.snoc first)
          firstBody secondBody rfl rfl)
  | @idTypes m target a b carrier carrier' x x' y y' redFirst redSecond _ _ _ ihCarrier ihLeft ihRight =>
      intro n source rho injective compatible left right ha hb
      subst a; subst b
      obtain ⟨first, firstLeft, firstRight, redFirst', rfl, rfl, rfl⟩ := reduce_id reflects injective redFirst
      obtain ⟨second, secondLeft, secondRight, redSecond', rfl, rfl, rfl⟩ := reduce_id reflects injective redSecond
      exact .idTypes redFirst' redSecond'
        (ihCarrier source rho injective compatible first second rfl rfl)
        (ihLeft source rho injective compatible firstLeft secondLeft first rfl rfl rfl)
        (ihRight source rho injective compatible firstRight secondRight first rfl rfl rfl)
  | @neutralTypes m target a b a' b' inferred redFirst redSecond _ ih =>
      intro n source rho injective compatible left right ha hb
      subst a; subst b
      obtain ⟨first, redFirst', rfl⟩ := ContextualDependentReductionReflection.reduces_reflects reflects injective redFirst
      obtain ⟨second, redSecond', rfl⟩ := ContextualDependentReductionReflection.reduces_reflects reflects injective redSecond
      obtain ⟨inferred', _, comparison⟩ := ih source rho injective compatible first second rfl rfl
      exact .neutralTypes redFirst' redSecond' comparison

end ContextualDependentAlgorithmReflection
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
