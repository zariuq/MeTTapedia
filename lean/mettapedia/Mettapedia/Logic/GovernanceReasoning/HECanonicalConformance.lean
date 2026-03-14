import Mettapedia.Languages.MeTTa.HE.EvalSpec
import Mettapedia.Languages.MeTTa.OSLFCore.Bridge
import Mettapedia.Logic.GovernanceReasoning.PeTTaRefinement

/-!
# HE MeTTa ↔ Governance DTS Bridge Correctness

Pattern ↔ Atom bridge correctness for governance DTS rules.

The **evaluation conformance** (proving that EvalAtom/MettaCall produce
the expected results for DTS queries) is deferred until the HE declarative
spec (EvalSpec.lean) is fully stable. Governance DTS conformance through
the PeTTa path (`PeTTaRefinement.lean`, `HERefinement.lean`) is already
proven and is the primary conformance channel.
-/

namespace Mettapedia.Logic.GovernanceReasoning.HECanonicalConformance

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Logic.GovernanceReasoning.Core
open Mettapedia.Logic.GovernanceReasoning.PeTTaRefinement

/-! ## DTS Rules as HE Equation Atoms -/

def dtsEqAtom_ob_pe : Atom :=
  .expression [.symbol "=",
    .expression [.symbol "ct-triple-for-add", .var "e",
                 .expression [.symbol "type"],
                 .expression [.symbol "permitted"]],
    .expression [.symbol "ct-triple", .var "e",
                 .expression [.symbol "type"],
                 .expression [.symbol "obligatory"]]]

def dtsEqAtom_ob_neg_not_pe : Atom :=
  .expression [.symbol "=",
    .expression [.symbol "not-ct-triple", .var "e",
                 .expression [.symbol "type"],
                 .expression [.symbol "permitted"]],
    .expression [.symbol "ct-triple", .var "e",
                 .expression [.symbol "type"],
                 .expression [.symbol "obligatory"]]]

def dtsEqAtom_not_optional : Atom :=
  .expression [.symbol "=",
    .expression [.symbol "not-ct-triple", .var "e",
                 .expression [.symbol "type"],
                 .expression [.symbol "optional"]],
    .expression [.symbol "ct-triple", .var "e",
                 .expression [.symbol "type"],
                 .expression [.symbol "obligatory"]]]

def dtsHESpace : Space := Space.ofList [
  dtsEqAtom_ob_pe,
  dtsEqAtom_ob_neg_not_pe,
  dtsEqAtom_not_optional
]

/-! ## Pattern ↔ Atom Bridge Correctness

These are kernel-checked: the inlined HE equation atoms match
`patternToAtom` applied to the PeTTa rule definitions. -/

theorem bridge_dts_ob_pe_eq :
    dtsEqAtom_ob_pe =
    .expression [.symbol "=",
      patternToAtom dtsRule_ob_implies_pe.left,
      patternToAtom dtsRule_ob_implies_pe.right] := by
  simp [dtsEqAtom_ob_pe, dtsRule_ob_implies_pe, patternToAtom]

theorem bridge_dts_ob_neg_not_pe_eq :
    dtsEqAtom_ob_neg_not_pe =
    .expression [.symbol "=",
      patternToAtom dtsRule_ob_neg_not_pe.left,
      patternToAtom dtsRule_ob_neg_not_pe.right] := by
  simp [dtsRule_ob_neg_not_pe, patternToAtom, dtsEqAtom_ob_neg_not_pe]

theorem bridge_dts_not_optional_eq :
    dtsEqAtom_not_optional =
    .expression [.symbol "=",
      patternToAtom dtsRule_not_optional.left,
      patternToAtom dtsRule_not_optional.right] := by
  simp [dtsRule_not_optional, patternToAtom, dtsEqAtom_not_optional]

/-! ## Deontic Interpretation (kernel-checked) -/

theorem he_result_ob_pe_interp :
    interpretDeontic (.apply "ct-triple"
      [.apply "soaMoor" [], .apply "type" [], .apply "obligatory" []]) =
    .modalAssertion "soaMoor" .obligatory := by
  simp [interpretDeontic]

theorem he_result_ob_pe_decode :
    atomToPattern (.expression [.symbol "ct-triple",
                   .expression [.symbol "soaMoor"],
                   .expression [.symbol "type"],
                   .expression [.symbol "obligatory"]]) =
    some (.apply "ct-triple"
      [.apply "soaMoor" [], .apply "type" [], .apply "obligatory" []]) := by
  simp [atomToPattern]

end Mettapedia.Logic.GovernanceReasoning.HECanonicalConformance
