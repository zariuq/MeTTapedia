import Mettapedia.TypeTheory.ContextualCwfUniverseLift
import Mettapedia.TypeTheory.ContextualSumComprehension
import Mettapedia.TypeTheory.ContextualPiEta

/-!
# Dependent products and sums on the lifted contextual carriers

The supplied constructor operations retain their actual arguments and values
through the external carrier lift. Their beta, eta and strict substitution
laws are derived from the corresponding local equations of the original
model. The change of carrier sizes assumes no internal universe operation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCwfUniverseLift

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)

universe u v w w' uc vs wt ms
variable {C : Cwf.{u, v, w, w'}}

abbrev Raised (C : Cwf.{u, v, w, w'}) := lift.{u, v, w, w', uc, vs, wt, ms} C

theorem down_heq {α β : Type w'} (types : α = β)
    {first : ULift.{ms} α} {second : ULift.{ms} β} (same : HEq first second) :
    HEq first.down second.down := by
  cases types
  exact heq_of_eq (congrArg ULift.down (eq_of_heq same))

theorem selfExtend_readout {context : (Raised C).Ctx} {type : (Raised C).Ty context}
    (term : (Raised C).Tm context type) :
    (selfExtend (Raised C) term).down = selfExtend C term.down := by
  unfold selfExtend
  simp only [eqRec_eq_cast]
  dsimp [Raised, lift]
  exact congrArg (C.pair (C.idS context.down) type.down)
    (cast_down (congrArg (C.Tm context.down) (C.tySub_id type.down).symm) _ term)

theorem extensionSubstitution_readout {source target : (Raised C).Ctx}
    (morphism : (Raised C).Sub source target) (type : (Raised C).Ty target) :
    (TypeOver.extensionSubstitution morphism type).down =
      TypeOver.extensionSubstitution morphism.down type.down := by
  unfold TypeOver.extensionSubstitution
  dsimp [Raised, lift]
  exact congrArg (C.pair (C.compS morphism.down (C.wk (C.tySub type.down morphism.down))) type.down)
    (cast_down (congrArg (C.Tm (C.ext source.down (C.tySub type.down morphism.down)))
      (C.tySub_comp type.down morphism.down (C.wk (C.tySub type.down morphism.down))).symm) _ _)

def liftProducts (products : PiOperations C) : PiOperations (Raised C) where
  pi domain codomain := ⟨products.pi domain.down codomain.down⟩
  lam body := ⟨products.lam body.down⟩
  app {context} {_domain} {codomain} function argument :=
    ⟨cast (congrArg (C.Tm context.down)
      (congrArg (C.tySub codomain.down) (selfExtend_readout argument)).symm)
      (products.app function.down argument.down)⟩

def liftSums (sums : SigmaOperations C) : SigmaOperations (Raised C) where
  sigma domain codomain := ⟨sums.sigma domain.down codomain.down⟩
  pair {context} {_domain} {codomain} first second :=
    ⟨sums.pair first.down (cast (congrArg (C.Tm context.down)
      (congrArg (C.tySub codomain.down) (selfExtend_readout first))) second.down)⟩
  fst value := ⟨sums.fst value.down⟩
  snd {context} {_domain} {codomain} value :=
    ⟨cast (congrArg (C.Tm context.down)
      (congrArg (C.tySub codomain.down)
        (selfExtend_readout (ULift.up (sums.fst value.down)))).symm)
      (sums.snd value.down)⟩

theorem products_app_readout (products : PiOperations C)
    {context : (Raised C).Ctx} {domain : (Raised C).Ty context}
    {codomain : (Raised C).Ty ((Raised C).ext context domain)}
    (function : (Raised C).Tm context ((liftProducts products).pi domain codomain))
    (argument : (Raised C).Tm context domain) :
    HEq ((liftProducts products).app function argument).down
      (products.app function.down argument.down) := by
  unfold liftProducts
  dsimp
  exact cast_heq _ _

theorem sums_pair_readout (sums : SigmaOperations C)
    {context : (Raised C).Ctx} {domain : (Raised C).Ty context}
    {codomain : (Raised C).Ty ((Raised C).ext context domain)}
    (first : (Raised C).Tm context domain)
    (second : (Raised C).Tm context ((Raised C).tySub codomain (selfExtend (Raised C) first))) :
    (liftSums sums).pair first second =
      ULift.up (sums.pair first.down
        (cast (congrArg (C.Tm context.down)
          (congrArg (C.tySub codomain.down) (selfExtend_readout first))) second.down)) := rfl


theorem term_action_eq {source target : C.Ctx} {type : C.Ty target}
    (term : C.Tm target type) {first second : C.Sub source target} (same : first = second) :
    HEq (C.tmSub term first) (C.tmSub term second) := by
  cases same
  rfl

theorem lifted_products_beta (products : PiOperations C) (beta : PiBeta products) :
    PiBeta (liftProducts products : PiOperations (Raised C)) := by
  intro context domain codomain body argument
  apply eq_of_heq
  exact (up_heq (products_app_readout products ((liftProducts products).lam body) argument)).trans
    (up_heq ((heq_of_eq (beta body.down argument.down)).trans
      (term_action_eq body.down (selfExtend_readout argument).symm)))

set_option backward.isDefEq.respectTransparency false in
theorem lifted_products_formation (products : PiOperations C)
    (formed : StrictPiFormationSubstitution products) :
    StrictPiFormationSubstitution (liftProducts products : PiOperations (Raised C)) := by
  intro source target morphism domain codomain
  apply congrArg ULift.up
  exact (formed morphism.down domain.down codomain.down).trans
    (congrArg (products.pi (C.tySub domain.down morphism.down))
      (congrArg (C.tySub codomain.down) (extensionSubstitution_readout morphism domain).symm))

theorem product_application_heq (products : PiOperations C)
    {context : C.Ctx} {domain : C.Ty context}
    {firstBody secondBody : C.Ty (C.ext context domain)} (types : firstBody = secondBody)
    {first : C.Tm context (products.pi domain firstBody)}
    {second : C.Tm context (products.pi domain secondBody)} (same : HEq first second)
    (argument : C.Tm context domain) :
    HEq (products.app first argument) (products.app second argument) := by
  cases types
  cases same
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem lifted_products_substitution (products : PiOperations C)
    (stable : StrictPiSubstitution products) :
    StrictPiSubstitution (liftProducts products : PiOperations (Raised C)) := by
  refine ⟨lifted_products_formation products stable.1, ?_, ?_⟩
  · intro source target morphism domain codomain body
    have arrow := extensionSubstitution_readout morphism domain
    dsimp [Raised, lift, liftProducts]
    rw [arrow]
    exact up_heq (stable.2.1 morphism.down body.down)
  · intro source target morphism domain codomain function argument reindexed same
    have arrow := extensionSubstitution_readout morphism domain
    have nativeSame : HEq (C.tmSub function.down morphism.down) reindexed.down :=
      down_heq (congrArg (C.Tm source.down)
        ((stable.1 morphism.down domain.down codomain.down).trans
          (congrArg (products.pi (C.tySub domain.down morphism.down))
            (congrArg (C.tySub codomain.down) arrow.symm)))) same
    have native := stable.2.2 morphism.down function.down argument.down
      (cast (congrArg (C.Tm source.down)
        (congrArg (products.pi (C.tySub domain.down morphism.down))
          (congrArg (C.tySub codomain.down) arrow))) reindexed.down)
      (nativeSame.trans (cast_heq _ _).symm)
    exact up_heq ((TypeOver.tmSub_heq
      (congrArg (C.tySub codomain.down) (selfExtend_readout argument))
      (products_app_readout products function argument) morphism.down).trans
      (native.trans ((product_application_heq products
        (congrArg (C.tySub codomain.down) arrow.symm) (cast_heq _ _)
        (C.tmSub argument.down morphism.down)).trans
        (products_app_readout products reindexed ((Raised C).tmSub argument morphism)).symm)))


theorem genericSection_readout (products : PiOperations C)
    (formed : StrictPiFormationSubstitution products)
    {context : (Raised C).Ctx} {domain : (Raised C).Ty context}
    {codomain : (Raised C).Ty ((Raised C).ext context domain)}
    (function : (Raised C).Tm context ((liftProducts products).pi domain codomain)) :
    (ContextualPiEta.genericSection (liftProducts products)
      (lifted_products_formation products formed) function).down =
      ContextualPiEta.genericSection products formed function.down := by
  let liftedFormed : StrictPiFormationSubstitution (liftProducts products : PiOperations (Raised C)) :=
    lifted_products_formation products formed
  let liftedFunction := reindexFunction (liftProducts products) liftedFormed
    ((Raised C).wk domain) function
  have functionTypes := congrArg (C.Tm (C.ext context.down domain.down))
    (congrArg ULift.down (liftedFormed ((Raised C).wk domain) domain codomain)).symm
  have functionReadout : HEq liftedFunction.down
      (reindexFunction products formed (C.wk domain.down) function.down) :=
    (down_heq functionTypes (reindexFunction_heq (liftProducts products)
      liftedFormed ((Raised C).wk domain) function)).trans
        (reindexFunction_heq products formed (C.wk domain.down) function.down).symm
  have resultTypes := congrArg (C.Tm (C.ext context.down domain.down))
    (congrArg ULift.down (ContextualPiEta.generic_result_type (C := Raised C) domain codomain)).symm
  apply eq_of_heq
  exact (down_heq resultTypes
    (ContextualPiEta.genericSection_heq (liftProducts products) liftedFormed function)).trans
    ((products_app_readout products liftedFunction ((Raised C).vz domain)).trans
      ((product_application_heq products
        (congrArg (C.tySub codomain.down)
          (extensionSubstitution_readout ((Raised C).wk domain) domain))
        functionReadout (C.vz domain.down)).trans
        (ContextualPiEta.genericSection_heq products formed function.down).symm))

theorem lifted_products_eta (products : PiOperations C)
    (formed : StrictPiFormationSubstitution products)
    (eta : ContextualPiEta.PiEta products formed) :
    ContextualPiEta.PiEta (liftProducts products : PiOperations (Raised C))
      (lifted_products_formation products formed) := by
  intro context domain codomain function
  apply congrArg ULift.up
  exact (congrArg products.lam (genericSection_readout products formed function)).trans
    (eta function.down)

@[simp] theorem sums_fst_readout (sums : SigmaOperations C)
    {context : (Raised C).Ctx} {domain : (Raised C).Ty context}
    {codomain : (Raised C).Ty ((Raised C).ext context domain)}
    (value : (Raised C).Tm context ((liftSums sums).sigma domain codomain)) :
    ((liftSums sums).fst value).down = sums.fst value.down := rfl

theorem sums_snd_readout (sums : SigmaOperations C)
    {context : (Raised C).Ctx} {domain : (Raised C).Ty context}
    {codomain : (Raised C).Ty ((Raised C).ext context domain)}
    (value : (Raised C).Tm context ((liftSums sums).sigma domain codomain)) :
    HEq ((liftSums sums).snd value).down (sums.snd value.down) := cast_heq _ _

theorem lifted_sums_beta (sums : SigmaOperations C) (beta : SigmaBeta sums) :
    SigmaBeta (liftSums sums : SigmaOperations (Raised C)) := by
  constructor
  · intro context domain codomain first second
    exact congrArg ULift.up (beta.1 first.down _)
  · intro context domain codomain first second
    exact up_heq ((sums_snd_readout sums ((liftSums sums).pair first second)).trans
      ((beta.2 first.down _).trans (cast_heq _ _)))

theorem lifted_sums_eta (sums : SigmaOperations C) (eta : SigmaEta sums) :
    SigmaEta (liftSums sums : SigmaOperations (Raised C)) := by
  intro context domain codomain value
  apply congrArg ULift.up
  have second : cast (congrArg (C.Tm context.down)
      (congrArg (C.tySub codomain.down) (selfExtend_readout ((liftSums sums).fst value))))
        ((liftSums sums).snd value).down = sums.snd value.down :=
    eq_of_heq ((cast_heq _ _).trans (sums_snd_readout sums value))
  exact (congrArg (sums.pair (sums.fst value.down)) second).trans (eta value.down)

set_option backward.isDefEq.respectTransparency false in
theorem lifted_sums_formation (sums : SigmaOperations C)
    (formed : StrictSigmaFormationSubstitution sums) :
    StrictSigmaFormationSubstitution (liftSums sums : SigmaOperations (Raised C)) := by
  intro source target morphism domain codomain
  apply congrArg ULift.up
  exact (formed morphism.down domain.down codomain.down).trans
    (congrArg (sums.sigma (C.tySub domain.down morphism.down))
      (congrArg (C.tySub codomain.down) (extensionSubstitution_readout morphism domain).symm))


theorem sum_pair_heq (sums : SigmaOperations C)
    {context : C.Ctx} {domain : C.Ty context}
    {firstBody secondBody : C.Ty (C.ext context domain)} (types : firstBody = secondBody)
    (first : C.Tm context domain)
    {left : C.Tm context (C.tySub firstBody (selfExtend C first))}
    {right : C.Tm context (C.tySub secondBody (selfExtend C first))} (same : HEq left right) :
    HEq (sums.pair first left) (sums.pair first right) := by
  cases types
  cases same
  rfl

theorem sum_projections_heq (sums : SigmaOperations C)
    {context : C.Ctx} {domain : C.Ty context}
    {firstBody secondBody : C.Ty (C.ext context domain)} (types : firstBody = secondBody)
    {first : C.Tm context (sums.sigma domain firstBody)}
    {second : C.Tm context (sums.sigma domain secondBody)} (same : HEq first second) :
    HEq (sums.fst first) (sums.fst second) ∧ HEq (sums.snd first) (sums.snd second) := by
  cases types
  cases same
  exact ⟨HEq.rfl, HEq.rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem lifted_sums_substitution (sums : SigmaOperations C)
    (stable : StrictSigmaSubstitution sums) :
    StrictSigmaSubstitution (liftSums sums : SigmaOperations (Raised C)) := by
  refine ⟨lifted_sums_formation sums stable.1, ?_, ?_⟩
  · intro source target morphism domain codomain first second reindexed same
    let nativeSecond := cast (congrArg (C.Tm target.down)
      (congrArg (C.tySub codomain.down) (selfExtend_readout first))) second.down
    let nativeReindexed := reindexPairSecond morphism.down first.down nativeSecond
    have secondTypes : (Raised C).tySub
        ((Raised C).tySub codomain (selfExtend (Raised C) first)) morphism =
        (Raised C).tySub ((Raised C).tySub codomain
          (TypeOver.extensionSubstitution morphism domain))
          (selfExtend (Raised C) ((Raised C).tmSub first morphism)) := by
      rw [← (Raised C).tySub_comp, ← selfExtend_substitution morphism first, (Raised C).tySub_comp]
    have nativeSame : HEq (C.tmSub second.down morphism.down) reindexed.down :=
      down_heq (congrArg (C.Tm source.down) (congrArg ULift.down secondTypes)) same
    have convertedSame : HEq nativeReindexed reindexed.down :=
      (reindexPairSecond_heq morphism.down first.down nativeSecond).trans
        ((TypeOver.tmSub_heq (congrArg (C.tySub codomain.down)
          (selfExtend_readout first)).symm (cast_heq _ _) morphism.down).trans nativeSame)
    have native := stable.2.1 morphism.down first.down nativeSecond nativeReindexed
      (reindexPairSecond_heq morphism.down first.down nativeSecond).symm
    exact up_heq (native.trans
      (sum_pair_heq sums
        (congrArg (C.tySub codomain.down) (extensionSubstitution_readout morphism domain).symm)
        (C.tmSub first.down morphism.down) (convertedSame.trans (cast_heq _ _).symm)))
  · intro source target morphism domain codomain value reindexed same
    have arrow := extensionSubstitution_readout morphism domain
    let nativeReindexed := cast (congrArg (C.Tm source.down)
      (congrArg (sums.sigma (C.tySub domain.down morphism.down))
        (congrArg (C.tySub codomain.down) arrow))) reindexed.down
    have nativeSame : HEq (C.tmSub value.down morphism.down) reindexed.down :=
      down_heq (congrArg (C.Tm source.down)
        ((stable.1 morphism.down domain.down codomain.down).trans
          (congrArg (sums.sigma (C.tySub domain.down morphism.down))
            (congrArg (C.tySub codomain.down) arrow.symm)))) same
    have native := stable.2.2 morphism.down value.down nativeReindexed
      (nativeSame.trans (cast_heq _ _).symm)
    have comparison := sum_projections_heq sums
      (first := nativeReindexed) (second := reindexed.down)
      (congrArg (C.tySub codomain.down) arrow.symm) (cast_heq _ reindexed.down)
    constructor
    · exact up_heq (native.1.trans comparison.1)
    · exact up_heq ((TypeOver.tmSub_heq
        (congrArg (C.tySub codomain.down) (selfExtend_readout ((liftSums sums).fst value)))
        (sums_snd_readout sums value) morphism.down).trans
        (native.2.trans (comparison.2.trans (sums_snd_readout sums reindexed).symm)))

/-- The complete local sum data and their earned laws survive the size change. -/
def liftStableSums (sums : StableSums C) : StableSums (Raised C) where
  operations := liftSums sums.operations
  beta := lifted_sums_beta sums.operations sums.beta
  eta := lifted_sums_eta sums.operations sums.eta
  substitution := lifted_sums_substitution sums.operations sums.substitution

end Mettapedia.TypeTheory.ContextualCwfUniverseLift
