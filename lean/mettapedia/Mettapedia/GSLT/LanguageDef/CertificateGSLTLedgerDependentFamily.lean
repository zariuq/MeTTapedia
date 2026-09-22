import Mettapedia.GSLT.LanguageDef.CertificateGSLTLedgerPresheaf
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenSearchModalAdequacy
import Mettapedia.TypeTheory.DisplayedPresheafComprehension

/-!
# Proof-relevant exact-ledger fibres and their modal observation

The joint goal-and-ledger observation has genuine proof-term fibres. At a
fixed context, goal and ledger, an inhabitant retains the open derivation;
the equality of its computed use list is only an index check. Reindexing
binds that derivation to a contextual proof substitution and computes the
new ledger using the presheaf action.

Forgetting the proof to mere inhabitation agrees with exact-completion
closure-modal reachability. This does not identify proof terms with modal
truth or supply Prime's authored dependent formers.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open OpenSearchMachine

/-- A proof-relevant answer at one contextual goal and exact ordered
premise-use ledger. -/
def exactDerivationFibre
    (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition)
    (goal : Pattern)
    (ledger : List (Fin context.judgments.length)) : Type :=
  { derivation : OpenDerivation definition context.judgments goal //
    holeOccurrences derivation = ledger }

/-- An exact displayed proof produces its own Type-valued operational route
receipt, retaining both the route and its actual final occurrence ledger. -/
def exactDerivationRouteReceipt
    {definition : ValidatedCalculusLanguageDef}
    {context : ClassifyingContext definition}
    {goal : Pattern} {ledger : List (Fin context.judgments.length)}
    (receipt : exactDerivationFibre definition context goal ledger) :
    Σ actualLedger : List (Fin context.judgments.length),
      Mettapedia.GSLT.Ultrainfinite.Route
        (OpenSearchMachine.Step definition context.judgments)
        ⟨[goal], []⟩ ⟨[], actualLedger⟩ :=
  completeRouteReceipt receipt.val

/-- The route produced from an exact displayed proof ends at precisely the
ledger indexing that proof fibre. -/
theorem exactDerivationRouteReceipt_ledger
    {definition : ValidatedCalculusLanguageDef}
    {context : ClassifyingContext definition}
    {goal : Pattern} {ledger : List (Fin context.judgments.length)}
    (receipt : exactDerivationFibre definition context goal ledger) :
    (exactDerivationRouteReceipt receipt).1 = ledger :=
  receipt.property

/-- Reconstructing that produced route returns the same proof term stored in
the displayed family, not merely a proof of the same goal. -/
theorem exactDerivationRouteReceipt_reconstruct
    {definition : ValidatedCalculusLanguageDef}
    {context : ClassifyingContext definition}
    {goal : Pattern} {ledger : List (Fin context.judgments.length)}
    (receipt : exactDerivationFibre definition context goal ledger) :
    derivationOfCompleteRoute (exactDerivationRouteReceipt receipt).2 =
      receipt.val :=
  derivationOfCompleteRoute_runToCompletion receipt.val

/-- A closed certificate is a point of the exact displayed fibre at the
empty context. There are no possible ambient premise positions to record. -/
def closedExactDerivationFibre
    {definition : ValidatedCalculusLanguageDef} {goal : Pattern}
    (derivation : Derivation definition goal) :
    exactDerivationFibre definition ⟨[]⟩ goal [] :=
  ⟨OpenDerivation.ofClosed derivation, by
    cases used : holeOccurrences (OpenDerivation.ofClosed derivation) with
    | nil => rfl
    | cons index _ => exact index.elim0⟩

@[simp] theorem closedExactDerivationFibre_close
    {definition : ValidatedCalculusLanguageDef} {goal : Pattern}
    (derivation : Derivation definition goal) :
    (closedExactDerivationFibre derivation).val.close = derivation :=
  OpenDerivation.close_ofClosed derivation

/-- The fibre of the natural goal-and-ledger observation is exactly the
proof-relevant subtype, not a subsingleton proposition. -/
def derivationToGoalLedger_fibre
    (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition)
    (goal : Pattern)
    (ledger : List (Fin context.judgments.length)) :
    { answer : (derivationTotalFace definition).obj (Opposite.op context) //
        (derivationToGoalLedger definition).app (Opposite.op context) answer =
          (goal, ledger) } ≃
      exactDerivationFibre definition context goal ledger where
  toFun := by
    rintro ⟨⟨otherGoal, derivation⟩, same⟩
    have goalEq : otherGoal = goal := congrArg Prod.fst same
    have ledgerEq : holeOccurrences derivation = ledger :=
      congrArg Prod.snd same
    cases goalEq
    exact ⟨derivation, ledgerEq⟩
  invFun := by
    rintro ⟨derivation, uses⟩
    exact ⟨⟨goal, derivation⟩,
      congrArg (fun used => (goal, used)) uses⟩
  left_inv := by
    rintro ⟨⟨otherGoal, derivation⟩, same⟩
    cases same
    rfl
  right_inv := by
    rintro ⟨derivation, uses⟩
    cases uses
    rfl

/-- The whole family of observed goal-and-ledger fibres is a functor on the
category of elements, instantiated from the generic natural-observation
construction. It retains every certificate and its substitution action. -/
def exactDerivationDisplayedFamily
    (definition : ValidatedCalculusLanguageDef) :
    DisplayedFamily (goalLedgerFace definition) :=
  observationFibreFamily (derivationToGoalLedger definition)

/-- The generic semantic total of the goal-and-ledger-indexed proof family
recovers the original open-derivation presheaf naturally. No certificate is
chosen from mere existence, and no rule choice is forgotten. -/
def exactDerivationTotalIso (definition : ValidatedCalculusLanguageDef) :
    totalSpace (exactDerivationDisplayedFamily definition) ≅
      derivationTotalFace definition :=
  observationTotalIso (derivationToGoalLedger definition)

/-- The semantic comprehension projection is the existing exact
goal-and-ledger observation after recovering the retained authored proof. -/
theorem exactDerivationTotalIso_projection
    (definition : ValidatedCalculusLanguageDef) :
    (exactDerivationTotalIso definition).hom ≫
        derivationToGoalLedger definition =
      totalProjection (exactDerivationDisplayedFamily definition) :=
  observationTotalIso_projection (derivationToGoalLedger definition)

/-- At a concrete index, the displayed family's carrier is the exact
proof-term fibre defined above. -/
def exactDerivationDisplayedFamily_at
    (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition)
    (goal : Pattern)
    (ledger : List (Fin context.judgments.length)) :
    (exactDerivationDisplayedFamily definition).obj
        (⟨Opposite.op context, (goal, ledger)⟩ :
          (goalLedgerFace definition).Elements) ≃
      exactDerivationFibre definition context goal ledger :=
  derivationToGoalLedger_fibre definition context goal ledger

/-- The canonical displayed point of a closed checked certificate. This
construction retains the proof itself, not merely its modal inhabitation. -/
def closedExactDisplayedPoint
    {definition : ValidatedCalculusLanguageDef} {goal : Pattern}
    (derivation : Derivation definition goal) :
    (exactDerivationDisplayedFamily definition).Elements :=
  ⟨⟨Opposite.op (⟨[]⟩ : ClassifyingContext definition), (goal, [])⟩,
    (exactDerivationDisplayedFamily_at definition ⟨[]⟩ goal []).symm
      (closedExactDerivationFibre derivation)⟩

/-- Contextual proof substitution acts on an exact-ledger fibre by binding
the retained derivation; the ledger index transforms by `mapLedger`. -/
def reindexExactDerivationFibre
    (definition : ValidatedCalculusLanguageDef)
    {source target : ClassifyingContext definition}
    (substitution : target ⟶ source)
    (goal : Pattern)
    (ledger : List (Fin source.judgments.length)) :
    exactDerivationFibre definition source goal ledger →
      exactDerivationFibre definition target goal
        (mapLedger substitution ledger)
  | ⟨derivation, uses⟩ =>
      ⟨derivation.bind substitution, by
        rw [holeOccurrences_bind, uses]
        rfl⟩

/-- The proof-bearing displayed-family action commutes with the operational
route-receipt action. The latter reconstructs a route before substitution,
so this exact equation applies to routes generated from actual proof terms. -/
theorem exactDerivationRouteReceipt_reindex
    (definition : ValidatedCalculusLanguageDef)
    {source target : ClassifyingContext definition}
    (substitution : target ⟶ source)
    (goal : Pattern)
    (ledger : List (Fin source.judgments.length))
    (receipt : exactDerivationFibre definition source goal ledger) :
    mapCompleteRouteReceipt substitution (exactDerivationRouteReceipt receipt) =
      exactDerivationRouteReceipt
        (reindexExactDerivationFibre definition substitution goal ledger receipt) := by
  exact mapCompleteRouteReceipt_generated substitution receipt.val

@[simp] theorem exactDerivationFibre_transport_val
    (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition)
    (goal : Pattern)
    {oldLedger newLedger : List (Fin context.judgments.length)}
    (equal : oldLedger = newLedger)
    (receipt : exactDerivationFibre definition context goal oldLedger) :
    ((equal ▸ receipt) : exactDerivationFibre definition context goal newLedger).val =
      receipt.val := by
  cases equal
  rfl

@[simp] theorem reindexExactDerivationFibre_id
    (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition)
    (goal : Pattern)
    (ledger : List (Fin context.judgments.length))
    (receipt : exactDerivationFibre definition context goal ledger) :
    (mapLedger_id definition context.judgments ledger) ▸
      reindexExactDerivationFibre definition (𝟙 context) goal ledger receipt =
        receipt := by
  apply Subtype.ext
  rw [exactDerivationFibre_transport_val]
  exact OpenDerivation.bind_assumptionEnvironment receipt.val

/-- Exact-ledger fibre reindexing composes, including its dependent ledger
index, by proof substitution rather than reconstruction from reachability. -/
theorem reindexExactDerivationFibre_comp
    (definition : ValidatedCalculusLanguageDef)
    {first middle last : ClassifyingContext definition}
    (earlier : middle ⟶ first)
    (later : last ⟶ middle)
    (goal : Pattern)
    (ledger : List (Fin first.judgments.length))
    (receipt : exactDerivationFibre definition first goal ledger) :
    (mapLedger_comp earlier later ledger) ▸
      reindexExactDerivationFibre definition (later ≫ earlier) goal ledger receipt =
        reindexExactDerivationFibre definition later goal
          (mapLedger earlier ledger)
          (reindexExactDerivationFibre definition earlier goal ledger receipt) := by
  apply Subtype.ext
  rw [exactDerivationFibre_transport_val]
  exact (OpenDerivation.bind_assoc receipt.val earlier later).symm

/-- Reindex the fibre of the independently defined natural goal-and-ledger
observation using its actual proof-bearing presheaf action. -/
def reindexObservedGoalLedgerFibre
    (definition : ValidatedCalculusLanguageDef)
    {source target : ClassifyingContext definition}
    (substitution : target ⟶ source)
    (goal : Pattern)
    (ledger : List (Fin source.judgments.length)) :
    { answer : (derivationTotalFace definition).obj (Opposite.op source) //
        (derivationToGoalLedger definition).app (Opposite.op source) answer =
          (goal, ledger) } →
      { answer : (derivationTotalFace definition).obj (Opposite.op target) //
        (derivationToGoalLedger definition).app (Opposite.op target) answer =
          (goal, mapLedger substitution ledger) }
  | ⟨⟨otherGoal, derivation⟩, same⟩ => by
      have goalEq : otherGoal = goal := congrArg Prod.fst same
      have ledgerEq : holeOccurrences derivation = ledger :=
        congrArg Prod.snd same
      cases goalEq
      refine ⟨⟨goal, derivation.bind substitution⟩, ?_⟩
      exact congrArg (fun uses => (goal, uses))
        ((holeOccurrences_bind derivation substitution).trans
          (congrArg (mapLedger substitution) ledgerEq))

/-- The base arrow records both contextual proof substitution and the exact
transformation of the observed ordered ledger. -/
def goalLedgerSubstitution
    (definition : ValidatedCalculusLanguageDef)
    {source target : ClassifyingContext definition}
    (substitution : target ⟶ source)
    (goal : Pattern)
    (ledger : List (Fin source.judgments.length)) :=
  CategoryOfElements.homMk
    (⟨Opposite.op source, (goal, ledger)⟩ :
      (goalLedgerFace definition).Elements)
    (⟨Opposite.op target, (goal, mapLedger substitution ledger)⟩ :
      (goalLedgerFace definition).Elements)
    (Quiver.Hom.op substitution) rfl

/-- The generic displayed-family action is the direct retained-certificate
reindexing, not a newly chosen proof of mere inhabitation. -/
theorem exactDerivationDisplayedFamily_map
    (definition : ValidatedCalculusLanguageDef)
    {source target : ClassifyingContext definition}
    (substitution : target ⟶ source)
    (goal : Pattern)
    (ledger : List (Fin source.judgments.length))
    (receipt : (exactDerivationDisplayedFamily definition).obj
      (⟨Opposite.op source, (goal, ledger)⟩ :
        (goalLedgerFace definition).Elements)) :
    (exactDerivationDisplayedFamily definition).map
        (goalLedgerSubstitution definition substitution goal ledger)
        receipt =
      reindexObservedGoalLedgerFibre definition substitution goal ledger
        receipt := by
  obtain ⟨⟨otherGoal, derivation⟩, same⟩ := receipt
  have goalEq : otherGoal = goal := congrArg Prod.fst same
  cases goalEq
  apply Subtype.ext
  rfl

/-- Taking the exact proof fibre commutes with contextual substitution. This
is a comparison of two independently defined reindexing actions, not merely
a consequence of both sides being inhabited. -/
theorem derivationToGoalLedger_fibre_reindex
    (definition : ValidatedCalculusLanguageDef)
    {source target : ClassifyingContext definition}
    (substitution : target ⟶ source)
    (goal : Pattern)
    (ledger : List (Fin source.judgments.length))
    (receipt : { answer :
        (derivationTotalFace definition).obj (Opposite.op source) //
        (derivationToGoalLedger definition).app (Opposite.op source) answer =
          (goal, ledger) }) :
    derivationToGoalLedger_fibre definition target goal
        (mapLedger substitution ledger)
        (reindexObservedGoalLedgerFibre definition substitution goal ledger
          receipt) =
      reindexExactDerivationFibre definition substitution goal ledger
        (derivationToGoalLedger_fibre definition source goal ledger receipt) := by
  obtain ⟨⟨otherGoal, derivation⟩, same⟩ := receipt
  have goalEq : otherGoal = goal := congrArg Prod.fst same
  cases goalEq
  apply Subtype.ext
  rfl

/-- Only the inhabitation of the proof-relevant fibre is identified with
the extensional closure-modal completion receipt. -/
theorem exactDerivationFibre_nonempty_iff_closureDiamond
    (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition)
    (goal : Pattern)
    (ledger : List (Fin context.judgments.length)) :
    Nonempty (exactDerivationFibre definition context goal ledger) ↔
      gsltDiamond
        (OpenSearchModalAdequacy.theory definition context.judgments).closure
        (fun candidate => candidate =
          (⟨[], ledger⟩ : OpenSearchMachine.State context.judgments))
        ⟨[goal], []⟩ :=
  OpenSearchModalAdequacy.exactDischarge_iff_closureDiamond
    definition context.judgments goal ledger

/-- The operational completion observation transports along any contextual
proof substitution, with the ordered ledger index transformed accordingly.
The proof passes through a retained certificate; it is not a claim that a
primitive machine step is preserved or reflected. -/
theorem exactCompletionDiamond_reindex
    (definition : ValidatedCalculusLanguageDef)
    {source target : ClassifyingContext definition}
    (substitution : target ⟶ source)
    (goal : Pattern)
    (ledger : List (Fin source.judgments.length))
    (completion :
      gsltDiamond
        (OpenSearchModalAdequacy.theory definition source.judgments).closure
        (fun candidate => candidate =
          (⟨[], ledger⟩ : OpenSearchMachine.State source.judgments))
        ⟨[goal], []⟩) :
      gsltDiamond
        (OpenSearchModalAdequacy.theory definition target.judgments).closure
        (fun candidate => candidate =
          (⟨[], mapLedger substitution ledger⟩ :
            OpenSearchMachine.State target.judgments))
        ⟨[goal], []⟩ := by
  have sourceProof :=
    (exactDerivationFibre_nonempty_iff_closureDiamond definition source
      goal ledger).mpr completion
  exact (exactDerivationFibre_nonempty_iff_closureDiamond definition target
    goal (mapLedger substitution ledger)).mp
      (sourceProof.map (reindexExactDerivationFibre definition substitution
        goal ledger))

end Mettapedia.GSLT.LanguageDef.CertificateGSLT

#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.derivationToGoalLedger_fibre
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.exactDerivationDisplayedFamily
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.exactDerivationTotalIso
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.exactDerivationTotalIso_projection
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.exactDerivationDisplayedFamily_map
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.reindexExactDerivationFibre
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.exactDerivationRouteReceipt_ledger
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.exactDerivationRouteReceipt_reconstruct
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.exactDerivationRouteReceipt_reindex
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.reindexExactDerivationFibre_id
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.reindexExactDerivationFibre_comp
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.derivationToGoalLedger_fibre_reindex
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.exactDerivationFibre_nonempty_iff_closureDiamond
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.exactCompletionDiamond_reindex
