import Mettapedia.GSLT.ProofPlans.Execution
import Mettapedia.GSLT.Scope.ConsumerDescent
import Mettapedia.PLN.Evidence.BinEvNat

/-!
# Evidence records and provenance

The evidence record of a plan node is a product of independent dimensions:
formal status, certification, review, empirical support and freshness
(`EvidenceRecord`), each a finite chain, ordered componentwise.  A rule
application's record is the meet of its rule's trust record and the records of
its premises and obligations (the AND of the aggregation); alternative
derivations of one conclusion combine by join (the OR).

**A readout on top of derivations.**  The record is a pure executor of plans
(`evidenceModel`), so the readout of a completed plan is the readout of the
plan resumed on the records of the discharging derivations
(`evidence_complete`).  A plan's record is at most the record of each
obligation it uses (`evidence_le_used`): a target cannot reach a status through
a cast, or any step, whose obligation lacks it (`Controls.open_cast_caps`).
Adding an alternative never lowers a record (`alternatives_mono`).

**Evidence ranks plans; it never licenses substituting one for another.**
Even at the best record, two derivations of one goal with equal records can
differ in their provenance, and a provenance-sensitive consumer (revision,
which combines two derivations only when their evidence sets are disjoint)
accepts one and refuses the other
(`Controls.evidence_never_licenses_substitution`).

**Provenance-aware evidence avoids double counting.**  A plan that cites one
obligation twice rests twice on one source.  Counting derivation leaves counts
that source twice; counting distinct sources counts it once
(`Controls.shared_source_counted_once`), and the decision that needs two
sources separates the shared plan from the plan with two distinct sources
exactly as the double-counting control of consumer descent does
(`Controls.plan_double_counting`).  PLN revision, which adds binary evidence
counts, counts the shared observation twice over leaves and once over
distinct sources (`Controls.pln_revision_double_counts`).  Meets are idempotent, so the record itself
cannot see the sharing (`Controls.record_blind_to_sharing`): deduplication is
exact for idempotent readouts and not for counts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProofPlans.Evidence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenSearchMachine

/-! ## Evidence records -/

/-- Formal status: none, sketched, kernel-verified. -/
abbrev Formal := Fin 3
/-- Certification by a versioned decision procedure: none, certified. -/
abbrev Certified := Fin 2
/-- Review: none, author, independent, two independent. -/
abbrev Reviewed := Fin 4
/-- Empirical support: none, sampled, exhaustive over a finite domain. -/
abbrev Empirical := Fin 3
/-- Freshness: stale, fresh. -/
abbrev Fresh := Fin 2

/-- **An evidence record**: five independent chains, ordered
componentwise. -/
abbrev EvidenceRecord := Formal × Certified × Reviewed × Empirical × Fresh

/-! ## The readout -/

variable {object : Object} {L : Type} [SemilatticeInf L] [OrderTop L]

/-- The meet of an ordered vector of records; `⊤` for none. -/
def meetAll : {goals : List Pattern} → RealizationList (fun _ => L) goals → L
  | [], .nil => ⊤
  | _ :: _, .cons head tail => head ⊓ meetAll tail

theorem meetAll_le_get : {goals : List Pattern} → (values : RealizationList (fun _ => L) goals) →
    (index : Fin goals.length) → meetAll values ≤ values.get index
  | [], .nil, index => Fin.elim0 index
  | _ :: _, .cons head tail, index => by
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · exact inf_le_left
      · exact inf_le_right.trans (meetAll_le_get tail tailIndex)

/-- **The evidence readout**: a rule application's record is the meet of its
rule's trust record and its premises' records. -/
abbrev evidenceModel (trust : RuleInstance → L) : Model.{0} object where
  carrier := fun _ => L
  onRule := fun ruleInstance _ _ _ values => trust ruleInstance ⊓ meetAll values

variable (trust : RuleInstance → L)

/-- **The record of a completed plan is the plan's readout resumed on the
records of the discharging derivations.** -/
theorem evidence_complete {context : List Pattern} {goal : Pattern}
    (plan : OpenDerivation object.definition context goal)
    (evidence : DerivationList object.definition context) :
    (evidenceModel (object := object) trust).denote (plan.discharge evidence) =
      (evidenceModel trust).denoteOpen plan ((evidenceModel trust).denoteList evidence) :=
  Model.denote_discharge _ plan evidence

mutual

/-- **A plan's record is at most the record of every obligation it uses.** -/
theorem evidence_le_used {context : List Pattern} :
    {goal : Pattern} → (plan : OpenDerivation object.definition context goal) →
      (values : RealizationList (fun _ => L) context) →
      ∀ index ∈ holeOccurrences plan,
        (evidenceModel (object := object) trust).denoteOpen plan values ≤ values.get index
  | _, .assumption index, values, used, member => by
      simp only [holeOccurrences, List.mem_singleton] at member
      subst member
      exact le_rfl
  | _, .byRule _ _ children, values, used, member => by
      simp only [holeOccurrences] at member
      exact inf_le_right.trans (evidenceList_le_used children values used member)

/-- Pointwise form. -/
theorem evidenceList_le_used {context : List Pattern} :
    {goals : List Pattern} → (plans : OpenDerivationList object.definition context goals) →
      (values : RealizationList (fun _ => L) context) →
      ∀ index ∈ holeOccurrencesList plans,
        meetAll ((evidenceModel (object := object) trust).denoteOpenList plans values) ≤
          values.get index
  | _, .nil, _, _, member => by simp [holeOccurrencesList] at member
  | _, .cons head tail, values, used, member => by
      simp only [holeOccurrencesList, List.mem_append] at member
      rcases member with inHead | inTail
      · exact inf_le_left.trans (evidence_le_used head values used inHead)
      · exact inf_le_right.trans (evidenceList_le_used tail values used inTail)

end

/-- **Alternatives combine by join**: the record of a conclusion with several
derivations. -/
def alternatives {L' : Type} [SemilatticeSup L'] [OrderBot L'] {goal : Pattern}
    (readout : Derivation object.definition goal → L') :
    List (Derivation object.definition goal) → L'
  | [] => ⊥
  | derivation :: derivations => readout derivation ⊔ alternatives readout derivations

/-- Adding an alternative never lowers the record: a failed branch does not
lower a conclusion that has another derivation. -/
theorem alternatives_mono {L' : Type} [SemilatticeSup L'] [OrderBot L'] {goal : Pattern}
    (readout : Derivation object.definition goal → L')
    (derivation : Derivation object.definition goal)
    (derivations : List (Derivation object.definition goal)) :
    alternatives readout derivations ≤ alternatives readout (derivation :: derivations) :=
  le_sup_right

/-! ## Provenance -/

/-- Concatenate the stamps of an ordered vector. -/
def stampsOf : {goals : List Pattern} → RealizationList (fun _ => List RuleId) goals →
    List RuleId
  | [], .nil => []
  | _ :: _, .cons head tail => head ++ stampsOf tail

/-- **The stamp of a derivation**: the axioms it rests on, with
multiplicity. -/
abbrev stampModel : Model.{0} object where
  carrier := fun _ => List RuleId
  onRule := fun ruleInstance _ _ _ values =>
    if stampsOf values = [] then [ruleInstance.ruleId] else stampsOf values

/-- Two derivations may be revised together only when they rest on disjoint
evidence. -/
def Combinable {goal : Pattern} (first second : Derivation object.definition goal) : Prop :=
  ∀ source ∈ (stampModel (object := object)).denote first,
    source ∉ (stampModel (object := object)).denote second

instance {goal : Pattern} (first second : Derivation object.definition goal) :
    Decidable (Combinable first second) := by
  unfold Combinable
  infer_instance

/-! ## Controls -/

namespace Controls

open Fixture
open Mettapedia.GSLT.ProofPlans

/-- Every rule is fully trusted. -/
def fullTrust : RuleInstance → EvidenceRecord := fun _ => ⊤

/-- The record of a closed kernel derivation under full trust. -/
def record {goal : Pattern} (derivation : Derivation kernelDefinition goal) : EvidenceRecord :=
  (evidenceModel (object := kernel) fullTrust).denote derivation

/-- `castAB(axCastAB, axA₂)`: a third derivation of `B`. -/
def dBcast : Derivation kernelDefinition B :=
  .byRule _ (kernelApp (rule := ruleCastAB) (by simp [kernelRules]))
    (.cons dCastAB (.cons dA₂ .nil))

/-- **Evidence ranks plans; it never licenses substituting one for another.**
The derivations `ab(axA₁)` and `ab(axA₂)` of `B` have the best record, and
they differ: revision may combine `castAB(axCastAB, axA₂)` with the first and
not with the second, which shares its source `axA₂`. -/
theorem evidence_never_licenses_substitution :
    record dBA₁ = ⊤ ∧ record dBA₂ = ⊤ ∧ dBA₁ ≠ dBA₂ ∧
      Combinable (object := kernel) dBcast dBA₁ ∧ ¬ Combinable (object := kernel) dBcast dBA₂ :=
  ⟨by decide, by decide, PlanControls.dBA₁_ne_dBA₂, by decide, by decide⟩

/-- The number of derivation leaves, with multiplicity. -/
abbrev tokenModel : Model.{0} kernel where
  carrier := fun _ => ℕ
  onRule := fun _ _ _ _ values => if valueSum values = 0 then 1 else valueSum values

/-- `pair(axA₁, axA₁)`: the shared plan completed. -/
def sharedPair : Derivation kernelDefinition D := planPairShared.discharge (.cons dA₁ .nil)

/-- `pair(axA₁, axA₂)`: two distinct obligations completed. -/
def distinctPair : Derivation kernelDefinition D := planPair.discharge (.cons dA₁ (.cons dA₂ .nil))

/-- **Counting leaves counts a shared source twice; counting distinct sources
counts it once.** -/
theorem shared_source_counted_once :
    tokenModel.denote sharedPair = 2 ∧
      ((stampModel (object := kernel)).denote sharedPair).dedup.length = 1 ∧
      tokenModel.denote distinctPair = 2 ∧
      ((stampModel (object := kernel)).denote distinctPair).dedup.length = 2 := by
  decide

/-- Number the sources of the fixture. -/
def sourceNumber (source : RuleId) : ℕ :=
  if source = ruleAxA₁.id then 1 else if source = ruleAxA₂.id then 2 else 0

/-- The evidence of a derivation of `D` as answers with their sources. -/
def answersWithSources (derivation : Derivation kernelDefinition D) : List (Bool × ℕ) :=
  ((stampModel (object := kernel)).denote derivation).map fun source => (true, sourceNumber source)

open Mettapedia.GSLT.Scope.DoubleCounting in
/-- **Provenance-aware evidence avoids double counting.**  The two completed
plans have one bag of answers.  The decision that needs two pieces of
evidence accepts both when it counts derivations, and accepts only the plan
with two distinct sources when it counts sources. -/
theorem plan_double_counting :
    answers (answersWithSources sharedPair) = answers (answersWithSources distinctPair) ∧
      naiveDecision (answers (answersWithSources sharedPair)) = true ∧
      awareDecision (answersWithSources sharedPair) = false ∧
      awareDecision (answersWithSources distinctPair) = true := by
  decide

open Mettapedia.PLN.Evidence in
/-- Every axiom of the fixture is one positive observation. -/
def sourceEvidence (_source : RuleId) : BinEvNat := ⟨1, 0⟩

open Mettapedia.PLN.Evidence in
/-- Revision by count addition over the leaves of a derivation, with
multiplicity. -/
def naiveRevision {goal : Pattern} (derivation : Derivation kernelDefinition goal) : BinEvNat :=
  (((stampModel (object := kernel)).denote derivation).map sourceEvidence).sum

open Mettapedia.PLN.Evidence in
/-- Revision by count addition over the distinct sources of a derivation. -/
def awareRevision {goal : Pattern} (derivation : Derivation kernelDefinition goal) : BinEvNat :=
  (((stampModel (object := kernel)).denote derivation).dedup.map sourceEvidence).sum

open Mettapedia.PLN.Evidence in
/-- **Revision by evidence counts double counts a shared source.**  PLN
revision adds binary evidence counts.  Over the leaves of `pair(axA₁, axA₁)` it
counts the one observation `axA₁` twice; over distinct sources it counts it
once, and the two agree on `pair(axA₁, axA₂)`. -/
theorem pln_revision_double_counts :
    naiveRevision sharedPair = ⟨2, 0⟩ ∧ awareRevision sharedPair = ⟨1, 0⟩ ∧
      naiveRevision distinctPair = ⟨2, 0⟩ ∧ awareRevision distinctPair = ⟨2, 0⟩ := by
  decide

/-- **The record cannot see sharing**: the shared and the distinct plan have
the same record on the same obligation records, since meets are idempotent. -/
theorem record_blind_to_sharing (value : EvidenceRecord) :
    (evidenceModel (object := kernel) fullTrust).denoteOpen planPairShared (.cons value .nil) =
      (evidenceModel (object := kernel) fullTrust).denoteOpen planPair
        (.cons value (.cons value .nil)) :=
  rfl

/-- The record of an open cast obligation: formal status none, everything else
at its best. -/
def openObligation : EvidenceRecord := (0, ⊤)

/-- **A target cannot reach kernel status through a cast whose obligation is
open.** -/
theorem open_cast_caps :
    ((evidenceModel (object := kernel) fullTrust).denoteOpen planBypass
      (.cons openObligation .nil)).1 = 0 := by
  have capped := evidence_le_used (object := kernel) fullTrust planBypass
    (.cons openObligation .nil) ⟨0, by decide⟩ (by decide)
  have formal := capped.1
  exact Fin.le_zero_iff.mp formal

end Controls

end Mettapedia.GSLT.ProofPlans.Evidence
