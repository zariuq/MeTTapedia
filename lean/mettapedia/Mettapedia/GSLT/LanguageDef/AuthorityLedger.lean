import Mettapedia.GSLT.LanguageDef.PresentationEvidence
import Mettapedia.Languages.MeTTa.HE.HELanguageDef
import Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef

/-!
# Concrete presentation evidence

This ledger supplies `exactFragment` witnesses for MeTTaZero query and
evaluation requests, using the observation-indexed equations carried by their
`BagExact` realizations.  It supplies `authoredProbe` notices for the nucleus
candidate and HE presentations.  These entries record the evidence supplied
here; they do not assert that other evidence is absent elsewhere in the tree.

The generic evidence datatype lives in `PresentationEvidence`.  Its kinds are
not ordered authority levels.  A reported model does not supply a typed
interpretation, and exact equality with an exporter result does not establish
artifact execution correctness.
-/

namespace Mettapedia.GSLT.LanguageDef.AuthorityLedger

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.ObservedOperationalRealization
open Mettapedia.GSLT.LanguageDef.PresentationEvidence

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

theorem zeroQueryEvidence_kind (model : Model) (space : model.Space) (spaceTerm : Pattern) :
    (zeroQueryEvidence model space spaceTerm).kind = .exactFragment := rfl

end MeTTaZero

/-! ## Probe notices: no operational realization is supplied by these entries -/

/-- A status notice for the exploratory nucleus candidate presentation. -/
def primeProbeEvidence : Evidence Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.language :=
  .authoredProbe "metta-prime-spec-probe: exploratory presentation; this entry supplies a status notice, not an operational realization"

/-- A notice for the HE presentation.  This entry makes no claim about which
simulation or adequacy theorems other modules provide. -/
def heEvidence : Evidence Mettapedia.Languages.MeTTa.HE.LanguageDef.mettaHE :=
  .authoredProbe "mettaHE: this entry records the presentation without supplying an operational realization"

theorem primeProbeEvidence_kind : primeProbeEvidence.kind = .authoredProbe := rfl
theorem heEvidence_kind : heEvidence.kind = .authoredProbe := rfl

/-- The exact realization and probe notice supply different kinds of
evidence.  This distinguishes these entries without ranking their languages. -/
theorem exact_and_probe_kinds_differ (model : Mettapedia.Languages.MeTTa.MeTTaZero.Model)
    (space : model.Space) (spaceTerm : Pattern) :
    primeProbeEvidence.kind ≠ (zeroQueryEvidence model space spaceTerm).kind := by
  rw [primeProbeEvidence_kind, zeroQueryEvidence_kind]
  decide

#print axioms exact_and_probe_kinds_differ

end Mettapedia.GSLT.LanguageDef.AuthorityLedger
