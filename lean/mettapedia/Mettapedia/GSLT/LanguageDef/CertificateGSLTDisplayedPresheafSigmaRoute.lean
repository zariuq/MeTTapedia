import Mettapedia.TypeTheory.DisplayedPresheafSigma
import Mettapedia.GSLT.LanguageDef.CertificateGSLTCanonicalRouteTrinity

/-!
# Completed routes as dependent companions of checked certificate proofs

The proof-relevant displayed family of exact certificate derivations is the
first component of a semantic dependent sum. The second component is an
actual completed operational route indexed by that very proof, using the
previously established natural route/proof isomorphism. Neither component
is inferred from modal support, and no new proof search is performed when
the retained route is read.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.TypeTheory.DisplayedPresheafSigma
open OpenSearchMachine

/-- A completed route displayed over the exact retained proof whose
operational computation produced it. The fibre contains the route itself,
not just a proposition that one exists. -/
def completedRouteOverProofFamily
    (definition : ValidatedCalculusLanguageDef) :
    DisplayedFamily (totalSpace (exactDerivationDisplayedFamily definition)) :=
  observationFibreFamily (exactDerivationTotalRouteIso definition).inv

/-- Over the context of already checked proofs, choosing their completed
routes is a natural dependent term. It reads the retained proof and uses
the established route/proof isomorphism; it does not run proof search. -/
def completedRouteOverProofTerm
    (definition : ValidatedCalculusLanguageDef) :
    (completedRouteOverProofFamily definition).sections where
  val point := by
    let iso := exactDerivationTotalRouteIso definition
    let route := iso.hom.app point.1 point.2
    have roundtrip : iso.inv.app point.1 route = point.2 := by
      exact congrArg (fun map => map point.2) (iso.hom_inv_id_app point.1)
    exact ⟨route, roundtrip⟩
  property := by
    intro source target arrow
    apply Subtype.ext
    change (canonicalRouteFace definition).map arrow.val
        ((exactDerivationTotalRouteIso definition).hom.app source.1 source.2) =
      (exactDerivationTotalRouteIso definition).hom.app target.1 target.2
    calc
      _ = (exactDerivationTotalRouteIso definition).hom.app target.1
            ((totalSpace (exactDerivationDisplayedFamily definition)).map
              arrow.val source.2) := by
        exact (congrArg (fun map => map source.2)
          ((exactDerivationTotalRouteIso definition).hom.naturality arrow.val)).symm
      _ = (exactDerivationTotalRouteIso definition).hom.app target.1 target.2 := by
        rw [arrow.property]

/-- A checked proof and its proof-indexed completed route form a genuine
semantic dependent-sum family over contextual goal-and-ledger observations. -/
def exactProofCompletedRouteSigma
    (definition : ValidatedCalculusLanguageDef) :
    DisplayedFamily (goalLedgerFace definition) :=
  sigmaDisplayed (exactDerivationDisplayedFamily definition)
    (completedRouteOverProofFamily definition)

/-- Forming the checked-proof/completed-route family commutes with every
natural change of the goal-and-ledger context. -/
theorem exactProofCompletedRouteSigma_reindex
    (definition : ValidatedCalculusLanguageDef)
    {source : Mettapedia.Computability.ComputationalTrinity.Face
      (ClassifyingContext definition)}
    (substitution : source ⟶ goalLedgerFace definition) :
    reindexDisplayed substitution (exactProofCompletedRouteSigma definition) =
      sigmaDisplayed
        (reindexDisplayed substitution (exactDerivationDisplayedFamily definition))
        (reindexDisplayed
          (totalReindexMap substitution (exactDerivationDisplayedFamily definition))
          (completedRouteOverProofFamily definition)) := by
  exact sigmaDisplayed_reindex substitution _ _

/-- An actual checked exact-ledger proof supplies the first component and
its computed completed route supplies the dependent second component. -/
def exactProofCompletedRouteReceipt
    (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition)
    (goal : Pattern)
    (ledger : List (Fin context.judgments.length))
    (proof : exactDerivationFibre definition context goal ledger) :
    (exactProofCompletedRouteSigma definition).obj
      ⟨Opposite.op context, (goal, ledger)⟩ := by
  let checked :=
    (exactDerivationDisplayedFamily_at definition context goal ledger).symm proof
  let total : (totalSpace (exactDerivationDisplayedFamily definition)).obj
      (Opposite.op context) := ⟨(goal, ledger), checked⟩
  let route := (exactDerivationTotalRouteIso definition).hom.app
    (Opposite.op context) total
  have roundtrip :
      (exactDerivationTotalRouteIso definition).inv.app
          (Opposite.op context) route = total := by
    exact congrArg (fun map => map total)
      ((exactDerivationTotalRouteIso definition).hom_inv_id_app
        (Opposite.op context))
  exact ⟨checked, ⟨route, roundtrip⟩⟩

/-- A completed canonical operational answer itself supplies the observed
goal and ledger together with a dependent pair of its checked proof and
that same route. The route is an input, not rediscovered from support. -/
def canonicalExecutionToDependentTotal
    (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition)
    (answer : CanonicalRouteAnswer definition context) :
    Σ observed : (goalLedgerFace definition).obj (Opposite.op context),
      (exactProofCompletedRouteSigma definition).obj
        ⟨Opposite.op context, observed⟩ := by
  let total := (exactDerivationTotalRouteIso definition).inv.app
    (Opposite.op context) answer
  exact ⟨total.1, ⟨total.2, ⟨answer, rfl⟩⟩⟩

/-- Read the retained operational route from a proof-indexed dependent
receipt without projecting it to modal support. -/
def dependentTotalRoute
    (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition)
    (receipt : Σ observed : (goalLedgerFace definition).obj (Opposite.op context),
      (exactProofCompletedRouteSigma definition).obj
        ⟨Opposite.op context, observed⟩) :
    CanonicalRouteAnswer definition context :=
  receipt.2.2.val

/-- The operational input can be read back exactly from its dependent
receipt. In particular, this map does not reduce a route to modal truth. -/
theorem canonicalExecutionToDependentTotal_retains
    (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition)
    (answer : CanonicalRouteAnswer definition context) :
    dependentTotalRoute definition context
        (canonicalExecutionToDependentTotal definition context answer) =
      answer := by
  rfl

/-- No two completed canonical routes collapse into the same proof-indexed
dependent receipt, even if their goal and ledger observations coincide. -/
theorem canonicalExecutionToDependentTotal_injective
    (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition) :
    Function.Injective (canonicalExecutionToDependentTotal definition context) := by
  intro first second same
  have routes := congrArg (dependentTotalRoute definition context) same
  simpa only [canonicalExecutionToDependentTotal_retains] using routes

/-- The canonicality check filters out no completed machine route, so a
raw completed execution can enter the same dependent consumer directly. -/
def completedExecutionToDependentTotal
    (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition)
    (answer : Σ goal : Pattern,
      Σ ledger : List (Fin context.judgments.length),
        Mettapedia.GSLT.Ultrainfinite.Route
          (OpenSearchMachine.Step definition context.judgments)
          ⟨[goal], []⟩ ⟨[], ledger⟩) :
    Σ observed : (goalLedgerFace definition).obj (Opposite.op context),
      (exactProofCompletedRouteSigma definition).obj
        ⟨Opposite.op context, observed⟩ :=
  canonicalExecutionToDependentTotal definition context
    ((completedRouteAnswerEquiv definition context) answer)

/-- The unfiltered completed execution's route and exact final ledger are
still present in the dependent receipt, not merely a reconstructed proof. -/
theorem completedExecutionToDependentTotal_retains_route
    (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition)
    (answer : Σ goal : Pattern,
      Σ ledger : List (Fin context.judgments.length),
        Mettapedia.GSLT.Ultrainfinite.Route
          (OpenSearchMachine.Step definition context.judgments)
          ⟨[goal], []⟩ ⟨[], ledger⟩) :
    (dependentTotalRoute definition context
      (completedExecutionToDependentTotal definition context answer)).2.val =
        answer.2 := by
  rfl

private theorem completedRoute_reconstruct_total
    (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition)
    (total : (totalSpace (exactDerivationDisplayedFamily definition)).obj
      (Opposite.op context)) :
    proofOfCanonicalRoute
        ((exactDerivationTotalRouteIso definition).hom.app
          (Opposite.op context) total) =
      (exactDerivationTotalIso definition).hom.app
        (Opposite.op context) total := by
  change (canonicalRouteProofIso definition).hom.app (Opposite.op context)
      ((canonicalRouteProofIso definition).inv.app (Opposite.op context)
        ((exactDerivationTotalIso definition).hom.app (Opposite.op context) total)) =
    (exactDerivationTotalIso definition).hom.app (Opposite.op context) total
  exact congrArg
    (fun map => map
      ((exactDerivationTotalIso definition).hom.app (Opposite.op context) total))
    ((canonicalRouteProofIso definition).inv_hom_id_app (Opposite.op context))

private theorem checkedProof_reconstruct_total
    (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition)
    (goal : Pattern)
    (ledger : List (Fin context.judgments.length))
    (proof : exactDerivationFibre definition context goal ledger) :
    (exactDerivationTotalIso definition).hom.app (Opposite.op context)
      ⟨(goal, ledger),
        (exactDerivationDisplayedFamily_at definition context goal ledger).symm proof⟩ =
      ⟨goal, proof.val⟩ := by
  rcases proof with ⟨derivation, uses⟩
  cases uses
  rfl

/-- Reading the operational component of the dependent pair reconstructs
the exact checked proof that supplied its first component. -/
theorem exactProofCompletedRouteReceipt_reconstruct
    (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition)
    (goal : Pattern)
    (ledger : List (Fin context.judgments.length))
    (proof : exactDerivationFibre definition context goal ledger) :
    proofOfCanonicalRoute
        (exactProofCompletedRouteReceipt definition context goal ledger proof).2.val =
      ⟨goal, proof.val⟩ := by
  change proofOfCanonicalRoute
      ((exactDerivationTotalRouteIso definition).hom.app (Opposite.op context)
        ⟨(goal, ledger),
          (exactDerivationDisplayedFamily_at definition context goal ledger).symm proof⟩) =
      ⟨goal, proof.val⟩
  exact (completedRoute_reconstruct_total definition context _).trans
    (checkedProof_reconstruct_total definition context goal ledger proof)

/-- The operational component is the already computed completion of the
retained proof, not an unrelated route with the same final observation. -/
theorem exactProofCompletedRouteReceipt_route
    (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition)
    (goal : Pattern)
    (ledger : List (Fin context.judgments.length))
    (proof : exactDerivationFibre definition context goal ledger) :
    ((exactProofCompletedRouteReceipt definition context goal ledger proof).2.val).2.val =
      exactDerivationRouteReceipt proof := by
  let answer : CanonicalRouteAnswer definition context :=
    (exactProofCompletedRouteReceipt definition context goal ledger proof).2.val
  have recover : answer = canonicalRouteOfProof ⟨goal, proof.val⟩ := by
    calc
      answer = canonicalRouteOfProof (proofOfCanonicalRoute answer) :=
        ((canonicalRouteProofEquiv definition context).left_inv answer).symm
      _ = canonicalRouteOfProof ⟨goal, proof.val⟩ :=
        congrArg canonicalRouteOfProof
          (exactProofCompletedRouteReceipt_reconstruct definition context goal ledger proof)
  change answer.2.val = exactDerivationRouteReceipt proof
  cases recover
  rfl

/-- Contextual proof substitution acts on the entire completed route
answer stored in the dependent pair by the existing operational action.
The proof term is bound once; the route is not found by a new search. -/
theorem exactProofCompletedRouteReceipt_reindex
    (definition : ValidatedCalculusLanguageDef)
    {source target : ClassifyingContext definition}
    (substitution : target ⟶ source)
    (goal : Pattern)
    (ledger : List (Fin source.judgments.length))
    (proof : exactDerivationFibre definition source goal ledger) :
    (canonicalRouteFace definition).map (Quiver.Hom.op substitution)
        (exactProofCompletedRouteReceipt definition source goal ledger proof).2.val =
      (exactProofCompletedRouteReceipt definition target goal
        (mapLedger substitution ledger)
        (reindexExactDerivationFibre definition substitution goal ledger proof)).2.val := by
  apply (canonicalRouteProofEquiv definition target).injective
  let oldAnswer : CanonicalRouteAnswer definition source :=
    (exactProofCompletedRouteReceipt definition source goal ledger proof).2.val
  let newAnswer : CanonicalRouteAnswer definition target :=
    (exactProofCompletedRouteReceipt definition target goal
      (mapLedger substitution ledger)
      (reindexExactDerivationFibre definition substitution goal ledger proof)).2.val
  change proofOfCanonicalRoute
      ((canonicalRouteFace definition).map (Quiver.Hom.op substitution)
        oldAnswer) = proofOfCanonicalRoute newAnswer
  have mappedProof :
      (derivationTotalFace definition).map (Quiver.Hom.op substitution)
          ⟨goal, proof.val⟩ =
        ⟨goal,
          (reindexExactDerivationFibre definition substitution goal ledger proof).val⟩ := by
    rfl
  have sourceReconstruct :=
    exactProofCompletedRouteReceipt_reconstruct
      definition source goal ledger proof
  have targetReconstruct :=
    exactProofCompletedRouteReceipt_reconstruct definition target goal
      (mapLedger substitution ledger)
      (reindexExactDerivationFibre definition substitution goal ledger proof)
  have mappedSource := congrArg
    (fun answer => (derivationTotalFace definition).map
      (Quiver.Hom.op substitution) answer) sourceReconstruct
  exact (proofOfCanonicalRoute_reindex definition
    (Quiver.Hom.op substitution) oldAnswer).trans
      (mappedSource.trans (mappedProof.trans targetReconstruct.symm))

#print axioms completedRouteOverProofFamily
#print axioms completedRouteOverProofTerm
#print axioms exactProofCompletedRouteSigma
#print axioms exactProofCompletedRouteSigma_reindex
#print axioms exactProofCompletedRouteReceipt
#print axioms canonicalExecutionToDependentTotal
#print axioms dependentTotalRoute
#print axioms canonicalExecutionToDependentTotal_retains
#print axioms canonicalExecutionToDependentTotal_injective
#print axioms completedExecutionToDependentTotal
#print axioms completedExecutionToDependentTotal_retains_route
#print axioms exactProofCompletedRouteReceipt_reconstruct
#print axioms exactProofCompletedRouteReceipt_route
#print axioms exactProofCompletedRouteReceipt_reindex

end Mettapedia.GSLT.LanguageDef.CertificateGSLT
