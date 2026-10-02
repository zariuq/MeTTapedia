import Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivationCanary

/-!
# Continuous finite-inventory loading canary

Two opaque verifier-rule occurrences are loaded in order by one continuous
MM2 run, after which the exact terminal cursor releases the compressed-proof
header.  A severed second occurrence cannot release that authority.

The comparison with `FiniteInventoryLoader` is deliberately observational:
this bounded canary does not claim a general simulation theorem for arbitrary
MM2 matching spaces.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofFiniteInventoryRunCanary

open Mettapedia.GSLT.FiniteInventoryLoader
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivationCanary
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-- A second opaque rule occurrence with a different expression-local
variable.  Loading must transport it exactly, without inspecting its body. -/
def secondOpaqueRule : Atom :=
  .expression
    [.symbol "exec",
      .expression [.symbol "97", .symbol "compressed-second-probe"],
      .expression
        [.symbol ",",
          .expression [.symbol "compressed-second", .var "item"]],
      .expression
        [.symbol "O",
          .expression
            [.symbol "+",
              .expression [.symbol "compressed-second-seen", .var "item"]]]]

def twoRulePresentation : FiniteVerifierRulePresentation where
  family := "compressed-verifier-rule"
  owner := compressedVerifierRuleOwner
  endTag := "mm-compressed-verifier-rule-end"
  rules := [canaryOpaqueRule, secondOpaqueRule]

def twoRuleProgram : List Atom :=
  [sourceCompressedRuleLoadRule, sourceCompressedRuleFinishRule,
    canaryLoading 0] ++ twoRulePresentation.rows ++
      [twoRulePresentation.endRow]

def twoRuleRow0 : Atom :=
  twoRulePresentation.rows[0]'(by decide)

def twoRuleRow1 : Atom :=
  twoRulePresentation.rows[1]'(by decide)

/-- Exact state after staging occurrence zero as verifier-owned code. -/
def afterLoad0 : List Atom :=
  [sourceCompressedRuleFinishRule, twoRuleRow0, twoRuleRow1,
    twoRulePresentation.endRow, sourceCompressedRuleLoadRule,
    compressedDispatchRuleRow canaryOpaqueRule, canaryLoading 1]

/-- Exact state after staging occurrence one without activating either rule. -/
def afterLoad1 : List Atom :=
  [sourceCompressedRuleFinishRule, twoRuleRow0, twoRuleRow1,
    twoRulePresentation.endRow, compressedDispatchRuleRow canaryOpaqueRule,
    sourceCompressedRuleLoadRule, compressedDispatchRuleRow secondOpaqueRule,
    canaryLoading 2]

/-- Once no inventory row remains, scheduling the self-reloading load rule
removes that administrative shell without changing the loaded inventory. -/
def afterLoadExhausted : List Atom :=
  [sourceCompressedRuleFinishRule, twoRuleRow0, twoRuleRow1,
    twoRulePresentation.endRow, compressedDispatchRuleRow canaryOpaqueRule,
    compressedDispatchRuleRow secondOpaqueRule,
    canaryLoading 2]

/-- The terminal cursor releases the header and owner-bound dispatch request;
the opaque inventory remains staged rather than prematurely executable. -/
def afterFinish : List Atom :=
  [twoRuleRow0, twoRuleRow1, twoRulePresentation.endRow,
    compressedDispatchRuleRow canaryOpaqueRule,
    compressedDispatchRuleRow secondOpaqueRule,
    sourceCompressedRuleFinishRule, canaryHeaderControl,
    .expression [.symbol "mm-reload-compressed-dispatch", canarySource,
      canaryProofOwner]]

/-- The abstract two-occurrence loader has a genuine proof-relevant path to
its exact terminal state. -/
def abstractTwoRulePath :
    (gslt Atom).RewritePath twoRulePresentation.loaderInitial
      twoRulePresentation.loaderTerminal :=
  twoRulePresentation.loaderPath

end Mettapedia.Languages.Metamath.MM2CompressedProofFiniteInventoryRunCanary
