import Mettapedia.GSLT.LanguageDef.ObservedOperationalRealization
import Mettapedia.Languages.MeTTa.HE.HELanguageDef
import Mettapedia.Languages.MeTTa.Prime.LanguageDef

/-!
# Evidence-carrying authority classification of presentations

A presentation earns an authority level by carrying the evidence for it, not
by a label.  The levels, each with the object that witnesses it:

* `authoredProbe`: a serialized presentation with a status notice and no
  adequacy theorem — it may be executed and read out, but it certifies
  nothing about a language;
* `semanticModel`: a presentation together with a semantic model it is
  interpreted in (a `Model` value and its interpretation), without an
  adequacy theorem relating the two;
* `exactFragment`: a presentation with an observed operational realization
  whose adequacy field is a proved two-sided, observation-indexed equation on
  a named fragment;
* `runtimeSealed`: an exact fragment whose serialized wire is byte-identical
  to a pinned exporter output — the shape of the CeTTa wire gates.

The witnesses below are the honest current state of the tree: MeTTaZero
holds `exactFragment` evidence for its query and evaluation requests; the
Prime probe and the HE presentation hold `authoredProbe` only.  No MeTTa
presentation holds `runtimeSealed` evidence, because no exporter from these
Lean presentations to a CeTTa artifact exists; the constructor is present so
that the obligation is visible, and it is deliberately uninhabited here.
-/

namespace Mettapedia.GSLT.LanguageDef.AuthorityLedger

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.ObservedOperationalRealization

/-- Authority evidence for a presentation.  Every constructor above the probe
level carries the object that justifies it. -/
inductive Evidence (language : LanguageDef) : Type 1
  | authoredProbe (notice : String)
  | semanticModel (Model : Type) (model : Model) (interpretation : String)
  | exactFragment (scope : String)
      {Surface Machine Answer Observation : Type}
      (realization : BagExact Surface Machine Answer Observation)
      (samePresentation : realization.language = language)
  | runtimeSealed (scope : String)
      {Surface Machine Answer Observation : Type}
      (realization : BagExact Surface Machine Answer Observation)
      (samePresentation : realization.language = language)
      (exporter : LanguageDef → String) (artifact : String)
      (wireIdentity : exporter language = artifact)

/-- The numeric level of a piece of evidence, for comparison only. -/
def Evidence.level {language : LanguageDef} : Evidence language → Nat
  | .authoredProbe _ => 0
  | .semanticModel _ _ _ => 1
  | .exactFragment _ _ _ => 2
  | .runtimeSealed _ _ _ _ _ _ => 3

/-! ## Positive witness: MeTTaZero query and evaluation are exact fragments -/

section MeTTaZero
open Mettapedia.Languages.MeTTa.MeTTaZero

noncomputable def zeroQueryEvidence (model : Model) (space : model.Space)
    (spaceTerm : Pattern) : Evidence language :=
  .exactFragment "query requests: atom-level `query` bag versus `zero-query` rewriting"
    (zeroQuery model space spaceTerm) rfl

noncomputable def zeroEvaluationEvidence (model : Model) (space : model.Space)
    (spaceTerm : Pattern) : Evidence language :=
  .exactFragment "evaluation requests: atom-level `evaluateOne` bag versus `zero-evaluate` rewriting"
    (zeroEvaluate model space spaceTerm) rfl

theorem zeroQueryEvidence_level (model : Model) (space : model.Space) (spaceTerm : Pattern) :
    (zeroQueryEvidence model space spaceTerm).level = 2 := rfl

end MeTTaZero

/-! ## Negative witnesses: probes without runtime authority -/

/-- The exploratory Prime presentation: explicitly work in progress. -/
def primeProbeEvidence : Evidence Mettapedia.Languages.MeTTa.Prime.LanguageDef.language :=
  .authoredProbe "metta-prime-spec-probe: exploratory presentation, not a specification; no adequacy theorem to running Prime"

/-- The HE presentation: a rule census (rule-name existence and a count of 58
rewrites) is what its simulation module proves; no state relation, no
simulation in either direction, no theorem mentions `EvalSpec`. -/
def heEvidence : Evidence Mettapedia.Languages.MeTTa.HE.LanguageDef.mettaHE :=
  .authoredProbe "mettaHE: rule-name existence and rewrite count proved; soundness/completeness claimed in prose only"

theorem primeProbeEvidence_level : primeProbeEvidence.level = 0 := rfl
theorem heEvidence_level : heEvidence.level = 0 := rfl

/-- The classification is strict: an exact fragment out-ranks a probe.  This
is the only comparison the ledger licenses; it never compares languages. -/
theorem exact_outranks_probe (model : Mettapedia.Languages.MeTTa.MeTTaZero.Model)
    (space : model.Space) (spaceTerm : Pattern) :
    primeProbeEvidence.level < (zeroQueryEvidence model space spaceTerm).level := by
  rw [primeProbeEvidence_level, zeroQueryEvidence_level]
  decide

#print axioms exact_outranks_probe

end Mettapedia.GSLT.LanguageDef.AuthorityLedger
