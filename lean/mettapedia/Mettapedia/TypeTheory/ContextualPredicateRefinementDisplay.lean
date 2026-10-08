import Mettapedia.TypeTheory.ContextualPredicateValueSubstitution
import Mettapedia.TypeTheory.ContextualComprehensionMorphism
import Mettapedia.GSLT.Core.ContextualTypeReindexingCoherence

/-!
# Actual displays of retained refinements

Forgetting the generic refined value defines a map from the complete refined
display to the ambient data display. Its substituted variable readout is
earned from the local forgetting law and the actual cartesian composition
comparison. Refinement eta then proves monicity. This result does not assume
that all predicates are context subobjects or supply monicity as a capability.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualPredicateRefinementDisplay

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateCapabilities
open ContextualComprehensionMorphism

universe c s t m p
variable {C : Cwf.{c,s,t,m}}
variable {doctrine : PredicateDoctrine.{c,s,t,m,p} C}

theorem predicate_reindex_heq {Γ Δ Γ' Δ' : C.Ctx}
    (sources : Γ = Γ') (targets : Δ = Δ')
    {predicate : doctrine.Predicate Δ} {predicate' : doctrine.Predicate Δ'}
    (predicates : HEq predicate predicate')
    {substitution : C.Sub Γ Δ} {substitution' : C.Sub Γ' Δ'}
    (arrows : HEq substitution substitution') :
    HEq (doctrine.reindex substitution predicate)
      (doctrine.reindex substitution' predicate') := by
  cases sources
  cases targets
  cases eq_of_heq predicates
  cases eq_of_heq arrows
  rfl

theorem forget_heq (operations : RefinementOperations doctrine)
    {Γ Γ' : C.Ctx} (contexts : Γ = Γ')
    {A : C.Ty Γ} {A' : C.Ty Γ'} (types : HEq A A')
    {predicate : doctrine.Predicate (C.ext Γ A)}
    {predicate' : doctrine.Predicate (C.ext Γ' A')}
    (predicates : HEq predicate predicate')
    {value : C.Tm Γ (operations.refined A predicate)}
    {value' : C.Tm Γ' (operations.refined A' predicate')}
    (values : HEq value value') :
    HEq (operations.forget A predicate value)
      (operations.forget A' predicate' value') := by
  cases contexts
  cases eq_of_heq types
  cases eq_of_heq predicates
  cases eq_of_heq values
  rfl

theorem forget_heq_injective (operations : RefinementOperations doctrine)
    {Γ : C.Ctx} {A A' : C.Ty Γ} (types : A = A')
    {predicate : doctrine.Predicate (C.ext Γ A)}
    {predicate' : doctrine.Predicate (C.ext Γ A')}
    (predicates : HEq predicate predicate')
    {value : C.Tm Γ (operations.refined A predicate)}
    {value' : C.Tm Γ (operations.refined A' predicate')}
    (forgotten : HEq (operations.forget A predicate value)
      (operations.forget A' predicate' value')) : HEq value value' := by
  cases types
  cases eq_of_heq predicates
  exact heq_of_eq
    (ContextualPredicateValueSubstitution.RefinementOperations.forget_injective
      operations A predicate (eq_of_heq forgotten))

/-- The equality-induced display comparison only changes the annotation of
the supplied arrow. -/
theorem equality_display_composite_heq {Γ Δ : C.Ctx}
    {A B : C.Ty Γ} (types : A = B) (arrow : C.Sub (C.ext Γ B) Δ) :
    HEq (C.compS arrow
      (TypeOver.isoOfValEq (A := ⟨A⟩) (B := ⟨B⟩) types).hom.substitution) arrow := by
  cases types
  change HEq (C.compS arrow (C.idS (C.ext Γ A))) arrow
  exact heq_of_eq (C.comp_id arrow)

/-- Complete cartesian lifts compose through their earned type annotation
comparison. -/
theorem extensionSubstitution_comp_heq {Γ Δ Θ : C.Ctx}
    (later : C.Sub Δ Θ) (earlier : C.Sub Γ Δ) (type : C.Ty Θ) :
    HEq (TypeOver.extensionSubstitution (C.compS later earlier) type)
      (C.compS (TypeOver.extensionSubstitution later type)
        (TypeOver.extensionSubstitution earlier (C.tySub type later))) :=
  (heq_of_eq (TypeOver.compositionObjectIso_hom_lift later earlier
    (⟨type⟩ : TypeOver C Θ)).symm).trans
      (equality_display_composite_heq (C.tySub_comp type later earlier) _)

theorem predicate_substitution_comp_heq {Γ Δ Θ : C.Ctx}
    (later : C.Sub Δ Θ) (earlier : C.Sub Γ Δ) (type : C.Ty Θ)
    (predicate : doctrine.Predicate (C.ext Θ type)) :
    HEq (doctrine.reindex (TypeOver.extensionSubstitution (C.compS later earlier) type) predicate)
      (doctrine.reindex (TypeOver.extensionSubstitution earlier (C.tySub type later))
        (doctrine.reindex (TypeOver.extensionSubstitution later type) predicate)) := by
  have contexts := congrArg (C.ext Γ) (C.tySub_comp type later earlier)
  have compared := predicate_reindex_heq (doctrine := doctrine) contexts rfl
    (predicate := predicate) (predicate' := predicate) HEq.rfl
    (extensionSubstitution_comp_heq later earlier type)
  rw [doctrine.reindex_comp] at compared
  exact compared

theorem predicate_substitution_arrow_heq {Γ Δ : C.Ctx}
    {first second : C.Sub Γ Δ} (arrows : first = second)
    (type : C.Ty Δ) (predicate : doctrine.Predicate (C.ext Δ type)) :
    HEq (doctrine.reindex (TypeOver.extensionSubstitution first type) predicate)
      (doctrine.reindex (TypeOver.extensionSubstitution second type) predicate) := by
  cases arrows
  rfl

variable (operations : RefinementOperations doctrine)

/-- The generic refined value, retyped by the actual formation law. -/
def genericRefined {Γ : C.Ctx} (type : C.Ty Γ)
    (predicate : doctrine.Predicate (C.ext Γ type)) :
    C.Tm (C.ext Γ (operations.refined type predicate))
      (operations.refined
        (C.tySub type (C.wk (operations.refined type predicate)))
        (doctrine.reindex
          (TypeOver.extensionSubstitution (C.wk (operations.refined type predicate)) type) predicate)) :=
  cast (congrArg (C.Tm (C.ext Γ (operations.refined type predicate)))
    (operations.formation_substitution (C.wk (operations.refined type predicate)) type predicate))
      (C.vz (operations.refined type predicate))

theorem genericRefined_heq {Γ : C.Ctx} (type : C.Ty Γ)
    (predicate : doctrine.Predicate (C.ext Γ type)) :
    HEq (genericRefined operations type predicate) (C.vz (operations.refined type predicate)) :=
  cast_heq _ _

def forgetGeneric {Γ : C.Ctx} (type : C.Ty Γ)
    (predicate : doctrine.Predicate (C.ext Γ type)) :
    C.Tm (C.ext Γ (operations.refined type predicate))
      (C.tySub type (C.wk (operations.refined type predicate))) :=
  operations.forget (C.tySub type (C.wk (operations.refined type predicate)))
    (doctrine.reindex
      (TypeOver.extensionSubstitution (C.wk (operations.refined type predicate)) type) predicate)
    (genericRefined operations type predicate)

def forgetDisplay {Γ : C.Ctx} (type : C.Ty Γ)
    (predicate : doctrine.Predicate (C.ext Γ type)) :
    C.Sub (C.ext Γ (operations.refined type predicate)) (C.ext Γ type) :=
  C.pair (C.wk (operations.refined type predicate)) type (forgetGeneric operations type predicate)

theorem forgetDisplay_projection {Γ : C.Ctx} (type : C.Ty Γ)
    (predicate : doctrine.Predicate (C.ext Γ type)) :
    C.compS (C.wk type) (forgetDisplay operations type predicate) =
      C.wk (operations.refined type predicate) := C.wk_pair _ _ _

theorem forgetDisplay_newest {Γ : C.Ctx} (type : C.Ty Γ)
    (predicate : doctrine.Predicate (C.ext Γ type)) :
    HEq (C.tmSub (C.vz type) (forgetDisplay operations type predicate))
      (forgetGeneric operations type predicate) :=
  (heq_of_eq (C.vz_pair _ _ _)).trans (cast_heq _ _)

/-- The supplied arrow's complete generic refined reading. -/
def refinedRead {Γ Δ : C.Ctx} (type : C.Ty Γ)
    (predicate : doctrine.Predicate (C.ext Γ type))
    (arrow : C.Sub Δ (C.ext Γ (operations.refined type predicate))) :
    C.Tm Δ (operations.refined
      (C.tySub type (C.compS (C.wk (operations.refined type predicate)) arrow))
      (doctrine.reindex
        (TypeOver.extensionSubstitution
          (C.compS (C.wk (operations.refined type predicate)) arrow) type) predicate)) :=
  cast (congrArg (C.Tm Δ) (by
    rw [← C.tySub_comp, operations.formation_substitution]))
      (C.tmSub (C.vz (operations.refined type predicate)) arrow)

theorem refinedRead_heq {Γ Δ : C.Ctx} (type : C.Ty Γ)
    (predicate : doctrine.Predicate (C.ext Γ type))
    (arrow : C.Sub Δ (C.ext Γ (operations.refined type predicate))) :
    HEq (refinedRead operations type predicate arrow)
      (C.tmSub (C.vz (operations.refined type predicate)) arrow) := cast_heq _ _

theorem forgetGeneric_substitution {Γ Δ : C.Ctx} (type : C.Ty Γ)
    (predicate : doctrine.Predicate (C.ext Γ type))
    (arrow : C.Sub Δ (C.ext Γ (operations.refined type predicate))) :
    HEq (C.tmSub (forgetGeneric operations type predicate) arrow)
      (operations.forget
        (C.tySub type (C.compS (C.wk (operations.refined type predicate)) arrow))
        (doctrine.reindex
          (TypeOver.extensionSubstitution
            (C.compS (C.wk (operations.refined type predicate)) arrow) type) predicate)
        (refinedRead operations type predicate arrow)) := by
  let weakening := C.wk (operations.refined type predicate)
  let shiftedType := C.tySub type weakening
  let shiftedPredicate := doctrine.reindex (TypeOver.extensionSubstitution weakening type) predicate
  let supplied := ContextualPredicateValueSubstitution.RefinementOperations.substitute operations
    arrow shiftedType shiftedPredicate (genericRefined operations type predicate)
  have suppliedRead : HEq supplied (refinedRead operations type predicate arrow) :=
    (ContextualPredicateValueSubstitution.RefinementOperations.substitute_heq operations
      arrow shiftedType shiftedPredicate _).trans
      ((TypeOver.tmSub_heq
        (operations.formation_substitution weakening type predicate).symm
        (genericRefined_heq operations type predicate) arrow).trans
        (refinedRead_heq operations type predicate arrow).symm)
  have step := operations.forget_substitution arrow shiftedType shiftedPredicate
    (genericRefined operations type predicate) supplied
    (ContextualPredicateValueSubstitution.RefinementOperations.substitute_heq operations
      arrow shiftedType shiftedPredicate _).symm
  exact step.trans (forget_heq operations rfl
    (heq_of_eq (C.tySub_comp type weakening arrow).symm)
    (predicate_substitution_comp_heq weakening arrow type predicate).symm suppliedRead)

/-- Reading the ambient variable through forgetting retains the exact
underlying supplied refined value. -/
theorem forgetDisplay_readout {Γ Δ : C.Ctx} (type : C.Ty Γ)
    (predicate : doctrine.Predicate (C.ext Γ type))
    (arrow : C.Sub Δ (C.ext Γ (operations.refined type predicate))) :
    HEq (C.tmSub (C.vz type) (C.compS (forgetDisplay operations type predicate) arrow))
      (operations.forget
        (C.tySub type (C.compS (C.wk (operations.refined type predicate)) arrow))
        (doctrine.reindex
          (TypeOver.extensionSubstitution
            (C.compS (C.wk (operations.refined type predicate)) arrow) type) predicate)
        (refinedRead operations type predicate arrow)) := by
  have types :
      C.tySub (C.tySub type (C.wk type)) (forgetDisplay operations type predicate) =
        C.tySub type (C.wk (operations.refined type predicate)) := by
    rw [← C.tySub_comp, forgetDisplay_projection]
  exact (TypeOver.tmSub_comp_heq (C.vz type) (forgetDisplay operations type predicate) arrow).trans
    ((TypeOver.tmSub_heq types (forgetDisplay_newest operations type predicate) arrow).trans
      (forgetGeneric_substitution operations type predicate arrow))

/-- Refinement eta and the genuine substituted forgetting readout prove
that no two distinct complete display arrows are erased by forgetting. -/
theorem forgetDisplay_monic {Γ Δ : C.Ctx} (type : C.Ty Γ)
    (predicate : doctrine.Predicate (C.ext Γ type)) :
    Function.Injective (fun arrow : C.Sub Δ (C.ext Γ (operations.refined type predicate)) =>
      C.compS (forgetDisplay operations type predicate) arrow) := by
  intro first second same
  change C.compS (forgetDisplay operations type predicate) first =
    C.compS (forgetDisplay operations type predicate) second at same
  have bases : C.compS (C.wk (operations.refined type predicate)) first =
      C.compS (C.wk (operations.refined type predicate)) second := by
    calc
      _ = C.compS (C.wk type) (C.compS (forgetDisplay operations type predicate) first) := by
        rw [← C.comp_assoc, forgetDisplay_projection]
      _ = C.compS (C.wk type) (C.compS (forgetDisplay operations type predicate) second) :=
        congrArg (C.compS (C.wk type)) same
      _ = _ := by rw [← C.comp_assoc, forgetDisplay_projection]
  have variableReadings :
      HEq (C.tmSub (C.vz type) (C.compS (forgetDisplay operations type predicate) first))
        (C.tmSub (C.vz type) (C.compS (forgetDisplay operations type predicate) second)) := by
    rw [same]
  have forgotten := (forgetDisplay_readout operations type predicate first).symm.trans
    (variableReadings.trans (forgetDisplay_readout operations type predicate second))
  have retained := forget_heq_injective operations (congrArg (C.tySub type) bases)
    (predicate_substitution_arrow_heq bases type predicate) forgotten
  exact TypeOver.substitution_ext bases
    ((refinedRead_heq operations type predicate first).symm.trans
      (retained.trans (refinedRead_heq operations type predicate second)))

end Mettapedia.TypeTheory.ContextualPredicateRefinementDisplay
