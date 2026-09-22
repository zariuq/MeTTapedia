import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenSearchMachine
import Mettapedia.GSLT.Core.ProofRelevantGSLT
import Mettapedia.GSLT.Core.GSLTConstructions
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Modal adequacy of open certificate search

The open-search machine's rule and assumption events give a proof-relevant
GSLT. Its proposition-valued step forgets only the choice of event, while
the bundled evidence retains rule applications and exact premise positions.

At a fixed discharge ledger, a completed finite execution exists exactly
when an open derivation with that ledger exists. The OSLF diamond of the
reflexive-transitive closure expresses the same existence statement. The
primitive diamond is deliberately not substituted for closure reachability.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenSearchModalAdequacy

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT
open Mettapedia.GSLT.ProofRelevant
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenSearchMachine
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-- Extensional one-step theory of open search. Its event witness is kept
separately by `system`; semantic steps exist exactly when such a witness
exists. -/
@[reducible] def theory (definition : ValidatedCalculusLanguageDef)
    (context : List Pattern) : GSLT where
  Term := State context
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target =>
    Nonempty (OpenSearchMachine.Step definition context source target)
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- Exact proof-relevant event authority over the search GSLT. -/
def system (definition : ValidatedCalculusLanguageDef)
    (context : List Pattern) : ProofRelevantGSLT where
  theory := theory definition context
  steps := {
    Evidence := OpenSearchMachine.Step definition context
    erases_iff := fun _ _ => Iff.rfl
  }

/-- Forgetting a Type-valued route gives precisely the proposition-valued
finite run; conversely, finite reachability guarantees some retained route. -/
theorem nonemptyRoute_iff_multiStep
    (definition : ValidatedCalculusLanguageDef)
    (context : List Pattern)
    (source target : State context) :
    Nonempty (Route (OpenSearchMachine.Step definition context)
      source target) ↔
      (theory definition context).MultiStep source target := by
  constructor
  · rintro ⟨route⟩
    induction route with
    | refl object =>
        exact @GSLT.MultiStep.refl (theory definition context) object
    | cons step rest inductionHypothesis =>
        exact @GSLT.MultiStep.step (theory definition context)
          _ _ _ ⟨step⟩ inductionHypothesis
  · intro path
    refine @GSLT.MultiStep.rec (theory definition context)
      (fun first last _ => Nonempty
        (Route (OpenSearchMachine.Step definition context) first last))
      ?_ ?_ source target path
    · intro object
      exact ⟨.refl object⟩
    · intro first middle last step _ inductionHypothesis
      obtain ⟨event⟩ := step
      obtain ⟨route⟩ := inductionHypothesis
      exact ⟨.cons event route⟩

/-- Exact-ledger derivability is finite reachability in the open-search
GSLT, without identifying individual proof trees and execution routes. -/
theorem exactDischarge_iff_multiStep
    (definition : ValidatedCalculusLanguageDef)
    (context : List Pattern) (goal : Pattern)
    (discharged : List (Fin context.length)) :
    Nonempty { derivation : OpenDerivation definition context goal //
      holeOccurrences derivation = discharged } ↔
      (theory definition context).MultiStep
        ⟨[goal], []⟩ ⟨[], discharged⟩ :=
  (exactDischargeAdequacy definition context goal discharged).trans
    (nonemptyRoute_iff_multiStep definition context _ _)

/-- A closure step of this equality-based GSLT is exactly a finite run. -/
theorem closureStep_iff_multiStep
    (definition : ValidatedCalculusLanguageDef)
    (context : List Pattern)
    (source target : State context) :
    (theory definition context).closure.Step source target ↔
      (theory definition context).MultiStep source target := by
  constructor
  · rintro ⟨reached, path, equal⟩
    subst reached
    exact path
  · intro path
    exact ⟨target, path, rfl⟩

/-- The OSLF closure diamond of the exact completed state is equivalent to
an open certificate with that precise ordered premise-use ledger. -/
theorem exactDischarge_iff_closureDiamond
    (definition : ValidatedCalculusLanguageDef)
    (context : List Pattern) (goal : Pattern)
    (discharged : List (Fin context.length)) :
    Nonempty { derivation : OpenDerivation definition context goal //
      holeOccurrences derivation = discharged } ↔
      gsltDiamond (theory definition context).closure
        (fun candidate => candidate = (⟨[], discharged⟩ : State context))
        ⟨[goal], []⟩ := by
  exact (exactDischarge_iff_multiStep definition context goal discharged).trans
    ((closureStep_iff_multiStep definition context _ _).symm.trans
      (gsltDiamond_singleton_iff_step
        (theory definition context).closure _ _).symm)

/-- Two equal judgment labels at different context positions yield distinct
accepted closure-modal targets. The modality has not quotiented away the
premise occurrence selected by the proof. -/
theorem duplicateGoal_distinctModalTargets
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    gsltDiamond (theory definition [goal, goal]).closure
      (fun candidate => candidate =
        (⟨[], [(0 : Fin 2)]⟩ : State [goal, goal]))
      ⟨[goal], []⟩ ∧
    gsltDiamond (theory definition [goal, goal]).closure
      (fun candidate => candidate =
        (⟨[], [(1 : Fin 2)]⟩ : State [goal, goal]))
      ⟨[goal], []⟩ ∧
    (⟨[], [(0 : Fin 2)]⟩ : State [goal, goal]) ≠
      (⟨[], [(1 : Fin 2)]⟩ : State [goal, goal]) := by
  constructor
  · apply (exactDischarge_iff_closureDiamond definition
      [goal, goal] goal [(0 : Fin 2)]).mp
    exact ⟨⟨.assumption 0, rfl⟩⟩
  constructor
  · apply (exactDischarge_iff_closureDiamond definition
      [goal, goal] goal [(1 : Fin 2)]).mp
    exact ⟨⟨.assumption 1, rfl⟩⟩
  · intro same
    have ledgers := congrArg State.discharged same
    simp at ledgers

/-- A primitive rule leaves the ledger alone; a primitive assumption step
can change it only when the head goal matches an actual context position. -/
theorem stepLedgerOrAssumption
    {definition : ValidatedCalculusLanguageDef}
    {context : List Pattern} {source target : State context}
    (event : OpenSearchMachine.Step definition context source target) :
    source.discharged = target.discharged ∨
      ∃ index : Fin context.length,
        source.pending.head? = some (context.get index) := by
  cases event with
  | rule ruleInstance application suffix ledger =>
      exact Or.inl rfl
  | assumption index suffix ledger =>
      exact Or.inr ⟨index, rfl⟩

/-- A primitive step cannot both introduce a nonempty discharge ledger and
finish an initially unmatched goal. Such a completion, when it exists,
requires a genuine multi-event route and hence the closure modality. -/
theorem primitiveCannotCompleteUnmatchedGoal
    (definition : ValidatedCalculusLanguageDef)
    (context : List Pattern) (goal : Pattern)
    (discharged : List (Fin context.length))
    (outside : goal ∉ context) (nonempty : discharged ≠ []) :
    ¬ (theory definition context).Step
      ⟨[goal], []⟩ ⟨[], discharged⟩ := by
  rintro ⟨event⟩
  rcases stepLedgerOrAssumption event with sameLedger | ⟨index, headMatch⟩
  · exact nonempty sameLedger.symm
  · have found : context.get index = goal := Option.some.inj headMatch.symm
    exact outside (found ▸ context.get_mem index)

end Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenSearchModalAdequacy

#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenSearchModalAdequacy.nonemptyRoute_iff_multiStep
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenSearchModalAdequacy.exactDischarge_iff_closureDiamond
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenSearchModalAdequacy.duplicateGoal_distinctModalTargets
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenSearchModalAdequacy.primitiveCannotCompleteUnmatchedGoal
