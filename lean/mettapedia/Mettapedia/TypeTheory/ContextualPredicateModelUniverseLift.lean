import Mettapedia.TypeTheory.ContextualPredicateModel
import Mettapedia.TypeTheory.ContextualCwfUniverseTypeLift

/-!
# External carrier lifts of complete local predicate models

The four contextual carriers and the predicate carrier have independent
lift parameters. Predicates keep their complete Heyting operations and
display quantifiers; ordinary proposition sections, guarded context maps
and refinement witnesses retain their original readouts. All local
equations are transported from the supplied model. This changes external
carrier sizes and introduces no internal universe or extra data choice.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualPredicateModelUniverseLift

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateCapabilities ContextualPredicateModel
open ContextualCwfUniverseLift (Raised up_heq down_heq selfExtend_readout
  extensionSubstitution_readout liftProducts liftStableSums)
open ContextualProductComparison (selfExtend)

universe c s t m p uc vs wt ms ps

/-- The order, implication and bounds are pulled back along the actual
carrier equivalence. -/
abbrev liftedHeytingAlgebra (α : Type p) [HeytingAlgebra α] :
    HeytingAlgebra (ULift.{ps} α) := Equiv.ulift.heytingAlgebra

attribute [local instance] liftedHeytingAlgebra

def liftHeytingHom {α β : Type p} [HeytingAlgebra α] [HeytingAlgebra β]
    (mapping : HeytingHom α β) : HeytingHom (ULift.{ps} α) (ULift.{ps} β) where
  toFun predicate := ULift.up (mapping predicate.down)
  map_inf' first second := congrArg ULift.up (map_inf mapping first.down second.down)
  map_sup' first second := congrArg ULift.up (map_sup mapping first.down second.down)
  map_bot' := congrArg ULift.up (map_bot mapping)
  map_himp' first second := congrArg ULift.up (map_himp mapping first.down second.down)

variable {C : Cwf.{c, s, t, m}}

def liftDoctrine (doctrine : PredicateDoctrine.{c, s, t, m, p} C) :
    PredicateDoctrine.{max c uc, max s vs, max t wt, max m ms, max p ps}
      (Raised.{c, s, t, m, uc, vs, wt, ms} C) where
  Predicate context := ULift.{ps} (doctrine.Predicate context.down)
  algebra context := liftedHeytingAlgebra (doctrine.Predicate context.down)
  reindex substitution := liftHeytingHom (doctrine.reindex substitution.down)
  reindex_id predicate := congrArg ULift.up (doctrine.reindex_id predicate.down)
  reindex_comp earlier later predicate :=
    congrArg ULift.up (doctrine.reindex_comp earlier.down later.down predicate.down)
  all type body := ULift.up (doctrine.all type.down body.down)
  some type body := ULift.up (doctrine.some type.down body.down)
  all_adjunction type body premise := doctrine.all_adjunction type.down body.down premise.down
  some_adjunction type body consequent :=
    doctrine.some_adjunction type.down body.down consequent.down
  all_reindex substitution type body := by
    change ULift.up (doctrine.reindex substitution.down (doctrine.all type.down body.down)) =
      ULift.up (doctrine.all (C.tySub type.down substitution.down)
        (doctrine.reindex (TypeOver.extensionSubstitution substitution type).down body.down))
    rw [extensionSubstitution_readout]
    exact congrArg ULift.up (doctrine.all_reindex substitution.down type.down body.down)
  some_reindex substitution type body := by
    change ULift.up (doctrine.reindex substitution.down (doctrine.some type.down body.down)) =
      ULift.up (doctrine.some (C.tySub type.down substitution.down)
        (doctrine.reindex (TypeOver.extensionSubstitution substitution type).down body.down))
    rw [extensionSubstitution_readout]
    exact congrArg ULift.up (doctrine.some_reindex substitution.down type.down body.down)

@[simp] theorem predicate_substitution_readout
    (doctrine : PredicateDoctrine.{c, s, t, m, p} C)
    {source target : (Raised.{c, s, t, m, uc, vs, wt, ms} C).Ctx}
    (substitution : (Raised C).Sub source target)
    (predicate : (liftDoctrine.{c, s, t, m, p, uc, vs, wt, ms, ps} doctrine).Predicate target) :
    ((liftDoctrine doctrine).reindex substitution predicate).down =
      doctrine.reindex substitution.down predicate.down := rfl

@[simp] theorem universal_readout (doctrine : PredicateDoctrine.{c, s, t, m, p} C)
    {context : (Raised.{c, s, t, m, uc, vs, wt, ms} C).Ctx}
    (type : (Raised C).Ty context)
    (body : (liftDoctrine.{c, s, t, m, p, uc, vs, wt, ms, ps} doctrine).Predicate
      ((Raised C).ext context type)) :
    ((liftDoctrine doctrine).all type body).down = doctrine.all type.down body.down := rfl

@[simp] theorem existential_readout (doctrine : PredicateDoctrine.{c, s, t, m, p} C)
    {context : (Raised.{c, s, t, m, uc, vs, wt, ms} C).Ctx}
    (type : (Raised C).Ty context)
    (body : (liftDoctrine.{c, s, t, m, p, uc, vs, wt, ms, ps} doctrine).Predicate
      ((Raised C).ext context type)) :
    ((liftDoctrine doctrine).some type body).down = doctrine.some type.down body.down := rfl

def liftPropositions {doctrine : PredicateDoctrine.{c, s, t, m, p} C}
    (propositions : PropositionOperations doctrine) :
    PropositionOperations (liftDoctrine.{c, s, t, m, p, uc, vs, wt, ms, ps} doctrine) where
  omega context := ULift.up (propositions.omega context.down)
  quote predicate := ULift.up (propositions.quote predicate.down)
  holds term := ULift.up (propositions.holds term.down)
  holds_quote predicate := congrArg ULift.up (propositions.holds_quote predicate.down)
  quote_holds term := congrArg ULift.up (propositions.quote_holds term.down)
  omega_substitution substitution :=
    congrArg ULift.up (propositions.omega_substitution substitution.down)
  quote_substitution substitution predicate :=
    up_heq (propositions.quote_substitution substitution.down predicate.down)
  holds_substitution substitution term transported same := by
    apply congrArg ULift.up
    exact propositions.holds_substitution substitution.down term.down transported.down
      (down_heq (congrArg (C.Tm _) (propositions.omega_substitution substitution.down)) same)

def liftAssumptions {doctrine : PredicateDoctrine.{c, s, t, m, p} C}
    (assumptions : AssumptionOperations doctrine) :
    AssumptionOperations (liftDoctrine.{c, s, t, m, p, uc, vs, wt, ms, ps} doctrine) where
  assumed context predicate := ULift.up (assumptions.assumed context.down predicate.down)
  inclusion predicate := ULift.up (assumptions.inclusion predicate.down)
  select predicate substitution guard := ULift.up (assumptions.select predicate.down
    substitution.down (congrArg ULift.down guard))
  select_beta predicate substitution guard := congrArg ULift.up
    (assumptions.select_beta predicate.down substitution.down (congrArg ULift.down guard))
  inclusion_monic predicate first second same := by
    apply ULift.ext
    exact assumptions.inclusion_monic predicate.down first.down second.down
      (congrArg ULift.down same)
  consequence assumption consequent := by
    constructor
    · intro readout
      exact (assumptions.consequence assumption.down consequent.down).mp
        (congrArg ULift.down readout)
    · intro entails
      exact congrArg ULift.up
        ((assumptions.consequence assumption.down consequent.down).mpr entails)

/-- The guard is evaluated on the actual self-extension, whose down arrow
is compared by the CwF laws rather than assumed definitionally equal. -/
theorem refinement_guard_readout (doctrine : PredicateDoctrine.{c, s, t, m, p} C)
    {context : (Raised.{c, s, t, m, uc, vs, wt, ms} C).Ctx}
    {type : (Raised C).Ty context}
    (predicate : (liftDoctrine.{c, s, t, m, p, uc, vs, wt, ms, ps} doctrine).Predicate
      ((Raised C).ext context type)) (term : (Raised C).Tm context type)
    (guard : (liftDoctrine doctrine).reindex (selfExtend (Raised C) term) predicate = ⊤) :
    doctrine.reindex (selfExtend C term.down) predicate.down = ⊤ := by
  have native := congrArg ULift.down guard
  change doctrine.reindex (selfExtend (Raised C) term).down predicate.down = ⊤ at native
  rw [selfExtend_readout] at native
  exact native

def liftRefinementIntro {doctrine : PredicateDoctrine.{c, s, t, m, p} C}
    (refinements : RefinementOperations doctrine)
    {context : (Raised.{c, s, t, m, uc, vs, wt, ms} C).Ctx}
    (type : (Raised C).Ty context)
    (predicate : (liftDoctrine.{c, s, t, m, p, uc, vs, wt, ms, ps} doctrine).Predicate
      ((Raised C).ext context type)) (term : (Raised C).Tm context type)
    (guard : (liftDoctrine doctrine).reindex (selfExtend (Raised C) term) predicate = ⊤) :
    (Raised C).Tm context (ULift.up (refinements.refined type.down predicate.down)) :=
  ULift.up (refinements.intro type.down predicate.down term.down
    (refinement_guard_readout doctrine predicate term guard))

def liftRefinementForget {doctrine : PredicateDoctrine.{c, s, t, m, p} C}
    (refinements : RefinementOperations doctrine)
    {context : (Raised.{c, s, t, m, uc, vs, wt, ms} C).Ctx}
    (type : (Raised C).Ty context)
    (predicate : (liftDoctrine.{c, s, t, m, p, uc, vs, wt, ms, ps} doctrine).Predicate
      ((Raised C).ext context type))
    (term : (Raised C).Tm context (ULift.up (refinements.refined type.down predicate.down))) :
    (Raised C).Tm context type :=
  ULift.up (refinements.forget type.down predicate.down term.down)

theorem lifted_refinement_guard {doctrine : PredicateDoctrine.{c, s, t, m, p} C}
    (refinements : RefinementOperations doctrine)
    {context : (Raised.{c, s, t, m, uc, vs, wt, ms} C).Ctx}
    (type : (Raised C).Ty context)
    (predicate : (liftDoctrine.{c, s, t, m, p, uc, vs, wt, ms, ps} doctrine).Predicate
      ((Raised C).ext context type))
    (term : (Raised C).Tm context (ULift.up (refinements.refined type.down predicate.down))) :
    (liftDoctrine doctrine).reindex
      (selfExtend (Raised C) (liftRefinementForget refinements type predicate term)) predicate = ⊤ := by
  apply ULift.ext
  change doctrine.reindex
    (selfExtend (Raised C) (liftRefinementForget refinements type predicate term)).down
    predicate.down = ⊤
  rw [selfExtend_readout]
  exact refinements.forget_guard type.down predicate.down term.down

theorem refinement_intro_predicate_heq {doctrine : PredicateDoctrine.{c, s, t, m, p} C}
    (refinements : RefinementOperations doctrine) {context : C.Ctx} (type : C.Ty context)
    {first second : doctrine.Predicate (C.ext context type)} (predicates : first = second)
    (term : C.Tm context type)
    (firstGuard : doctrine.reindex (selfExtend C term) first = ⊤)
    (secondGuard : doctrine.reindex (selfExtend C term) second = ⊤) :
    HEq (refinements.intro type first term firstGuard)
      (refinements.intro type second term secondGuard) := by
  cases predicates
  rfl

theorem refinement_forget_predicate_heq {doctrine : PredicateDoctrine.{c, s, t, m, p} C}
    (refinements : RefinementOperations doctrine) {context : C.Ctx} (type : C.Ty context)
    {first second : doctrine.Predicate (C.ext context type)} (predicates : first = second)
    {firstTerm : C.Tm context (refinements.refined type first)}
    {secondTerm : C.Tm context (refinements.refined type second)}
    (same : HEq firstTerm secondTerm) :
    HEq (refinements.forget type first firstTerm) (refinements.forget type second secondTerm) := by
  cases predicates
  cases same
  rfl

theorem lifted_refinement_formation {doctrine : PredicateDoctrine.{c, s, t, m, p} C}
    (refinements : RefinementOperations doctrine)
    {source target : (Raised.{c, s, t, m, uc, vs, wt, ms} C).Ctx}
    (substitution : (Raised C).Sub source target) (type : (Raised C).Ty target)
    (predicate : (liftDoctrine.{c, s, t, m, p, uc, vs, wt, ms, ps} doctrine).Predicate
      ((Raised C).ext target type)) :
    (Raised C).tySub (ULift.up (refinements.refined type.down predicate.down)) substitution =
      ULift.up (refinements.refined ((Raised C).tySub type substitution).down
        ((liftDoctrine doctrine).reindex (TypeOver.extensionSubstitution substitution type)
          predicate).down) := by
  apply congrArg ULift.up
  change C.tySub (refinements.refined type.down predicate.down) substitution.down =
    refinements.refined (C.tySub type.down substitution.down)
      (doctrine.reindex (TypeOver.extensionSubstitution substitution type).down predicate.down)
  rw [extensionSubstitution_readout]
  exact refinements.formation_substitution substitution.down type.down predicate.down

theorem lifted_refinement_intro_substitution
    {doctrine : PredicateDoctrine.{c, s, t, m, p} C}
    (refinements : RefinementOperations doctrine)
    {source target : (Raised.{c, s, t, m, uc, vs, wt, ms} C).Ctx}
    (substitution : (Raised C).Sub source target) (type : (Raised C).Ty target)
    (predicate : (liftDoctrine.{c, s, t, m, p, uc, vs, wt, ms, ps} doctrine).Predicate
      ((Raised C).ext target type)) (term : (Raised C).Tm target type)
    (guard : (liftDoctrine doctrine).reindex (selfExtend (Raised C) term) predicate = ⊤)
    (transportedGuard : (liftDoctrine doctrine).reindex
      (selfExtend (Raised C) ((Raised C).tmSub term substitution))
      ((liftDoctrine doctrine).reindex (TypeOver.extensionSubstitution substitution type) predicate) = ⊤) :
    HEq ((Raised C).tmSub (liftRefinementIntro refinements type predicate term guard) substitution)
      (liftRefinementIntro refinements ((Raised C).tySub type substitution)
        ((liftDoctrine doctrine).reindex (TypeOver.extensionSubstitution substitution type) predicate)
        ((Raised C).tmSub term substitution) transportedGuard) := by
  have predicateEquality := congrArg
    (fun arrow => doctrine.reindex arrow predicate.down)
    (extensionSubstitution_readout substitution type)
  have targetGuard := refinement_guard_readout doctrine
    ((liftDoctrine doctrine).reindex (TypeOver.extensionSubstitution substitution type) predicate)
    ((Raised C).tmSub term substitution) transportedGuard
  change doctrine.reindex (selfExtend C (C.tmSub term.down substitution.down))
    (doctrine.reindex (TypeOver.extensionSubstitution substitution type).down predicate.down) = ⊤ at targetGuard
  have nativeTargetGuard : doctrine.reindex (selfExtend C (C.tmSub term.down substitution.down))
      (doctrine.reindex (TypeOver.extensionSubstitution substitution.down type.down) predicate.down) = ⊤ := by
    exact (congrArg (doctrine.reindex (selfExtend C (C.tmSub term.down substitution.down)))
      predicateEquality).symm.trans targetGuard
  exact up_heq ((refinements.intro_substitution substitution.down type.down predicate.down term.down
    (refinement_guard_readout doctrine predicate term guard) nativeTargetGuard).trans
      (refinement_intro_predicate_heq refinements (C.tySub type.down substitution.down)
        predicateEquality.symm (C.tmSub term.down substitution.down) nativeTargetGuard targetGuard))

theorem lifted_refinement_forget_substitution
    {doctrine : PredicateDoctrine.{c, s, t, m, p} C}
    (refinements : RefinementOperations doctrine)
    {source target : (Raised.{c, s, t, m, uc, vs, wt, ms} C).Ctx}
    (substitution : (Raised C).Sub source target) (type : (Raised C).Ty target)
    (predicate : (liftDoctrine.{c, s, t, m, p, uc, vs, wt, ms, ps} doctrine).Predicate
      ((Raised C).ext target type))
    (term : (Raised C).Tm target (ULift.up (refinements.refined type.down predicate.down)))
    (transported : (Raised C).Tm source
      (ULift.up (refinements.refined ((Raised C).tySub type substitution).down
        ((liftDoctrine doctrine).reindex (TypeOver.extensionSubstitution substitution type) predicate).down)))
    (same : HEq ((Raised C).tmSub term substitution) transported) :
    HEq ((Raised C).tmSub (liftRefinementForget refinements type predicate term) substitution)
      (liftRefinementForget refinements ((Raised C).tySub type substitution)
        ((liftDoctrine doctrine).reindex (TypeOver.extensionSubstitution substitution type) predicate)
        transported) := by
  have predicateEquality := congrArg
    (fun arrow => doctrine.reindex arrow predicate.down)
    (extensionSubstitution_readout substitution type)
  let nativeTransported := cast (congrArg (C.Tm source.down)
    (congrArg (refinements.refined (C.tySub type.down substitution.down)) predicateEquality)) transported.down
  have typeEquality := (refinements.formation_substitution substitution.down type.down predicate.down).trans
    (congrArg (refinements.refined (C.tySub type.down substitution.down)) predicateEquality.symm)
  have nativeSame := down_heq (congrArg (C.Tm source.down) typeEquality) same
  have native := refinements.forget_substitution substitution.down type.down predicate.down term.down
    nativeTransported (nativeSame.trans (cast_heq _ _).symm)
  exact up_heq (native.trans
    (refinement_forget_predicate_heq refinements (C.tySub type.down substitution.down)
      predicateEquality.symm (cast_heq _ _)))

def liftRefinements {doctrine : PredicateDoctrine.{c, s, t, m, p} C}
    (refinements : RefinementOperations doctrine) :
    RefinementOperations (liftDoctrine.{c, s, t, m, p, uc, vs, wt, ms, ps} doctrine) where
  refined type predicate := ULift.up (refinements.refined type.down predicate.down)
  intro := liftRefinementIntro refinements
  forget := liftRefinementForget refinements
  forget_guard := lifted_refinement_guard refinements
  beta type predicate term guard := congrArg ULift.up
    (refinements.beta type.down predicate.down term.down
      (refinement_guard_readout doctrine predicate term guard))
  eta type predicate term := congrArg ULift.up
    (refinements.eta type.down predicate.down term.down)
  formation_substitution := lifted_refinement_formation refinements
  intro_substitution := lifted_refinement_intro_substitution refinements
  forget_substitution := lifted_refinement_forget_substitution refinements

variable {K : CwfWithTerminal.{c, s, t, m}}

/-- The underlying contextual lift is the existing four-carrier lift. The
fifth independent size parameter belongs only to the predicate carrier. -/
def lift (model : LocalModel.{c, s, t, m, p} K) :
    LocalModel.{max c uc, max s vs, max t wt, max m ms, max p ps}
      (ContextualCwfUniverseLift.liftWithTerminal.{c, s, t, m, uc, vs, wt, ms} K) where
  products := liftProducts model.products
  sums := liftStableSums model.sums
  doctrine := liftDoctrine model.doctrine
  propositions := liftPropositions model.propositions
  assumptions := liftAssumptions model.assumptions
  refinements := liftRefinements model.refinements

theorem qualificationLift (model : LocalModel.{c, s, t, m, p} K)
    (qualified : Qualification model) :
    Qualification (lift.{c, s, t, m, p, uc, vs, wt, ms, ps} model) where
  stableProducts := ContextualCwfUniverseLift.lifted_products_substitution
    model.products qualified.stableProducts
  productBeta := ContextualCwfUniverseLift.lifted_products_beta model.products qualified.productBeta
  productEta := ContextualCwfUniverseLift.lifted_products_eta model.products
    qualified.stableProducts.1 qualified.productEta

universe upper

/-- All model carriers may be enclosed in one common external size without
changing the universe of the generated declaration symbols. -/
abbrev commonLift (model : LocalModel.{c, s, t, m, p} K) :
    LocalModel.{max upper c s t m p, max upper c s t m p, max upper c s t m p,
      max upper c s t m p, max upper c s t m p}
      (ContextualCwfUniverseLift.commonLiftWithTerminal.{c, s, t, m, max upper c s t m p} K) :=
  lift.{c, s, t, m, p, max upper c s t m p, max upper c s t m p,
    max upper c s t m p, max upper c s t m p, max upper c s t m p} model

theorem commonQualification (model : LocalModel.{c, s, t, m, p} K)
    (qualified : Qualification model) :
    Qualification (commonLift.{c, s, t, m, p, upper} model) :=
  qualificationLift model qualified

end Mettapedia.TypeTheory.ContextualPredicateModelUniverseLift
