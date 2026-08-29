import Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivationCanary

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

def canarySource : Atom := .symbol "compressed-ordered-source"
def canaryPosition : Nat := 3

def canaryProofOwner : Atom :=
  .expression
    [.symbol "mm-source-proof-owner", canarySource, natAtom canaryPosition]

def canaryStatement : Atom :=
  .expression
    [.symbol "mm-source-theorem", .symbol "canary-site",
      .symbol "canary-label", .symbol "canary-typecode",
      .symbol "canary-body", .symbol "canary-proof",
      .symbol "canary-separator", .symbol "canary-terminator"]

def canaryRequest : Atom :=
  .expression
    [.symbol "mm-source-theorem-proof-request", canarySource,
      natAtom canaryPosition, natAtom (canaryPosition + 1), canaryStatement]

def canaryHeaderControl : Atom :=
  .expression
    [.symbol "mm-compressed-header-control", canarySource,
      canaryProofOwner, natAtom 0]

def canaryPreparedHeaderControl : Atom :=
  deferCompressedHeaderControlRow canaryHeaderControl

def canaryLoading (rulePosition : Nat) : Atom :=
  .expression
    [.symbol "mm-source-compressed-rule-loading", canarySource,
      natAtom canaryPosition, canaryProofOwner, canaryHeaderControl,
      natAtom rulePosition]

def activationProgram : List Atom :=
  [sourceCompressedProofActivateRule, canaryRequest,
   canaryPreparedHeaderControl]

def activationFinal : List Atom :=
  (cReflectiveSourceWorkQueueRunN .leaveInert 1 activationProgram).1

def foreignRequest : Atom :=
  .expression
    [.symbol "mm-source-theorem-proof-request", canarySource,
      natAtom (canaryPosition + 1), natAtom (canaryPosition + 2),
      canaryStatement]

def foreignActivationProgram : List Atom :=
  [sourceCompressedProofActivateRule, foreignRequest,
   canaryPreparedHeaderControl]

def foreignActivationFinal : List Atom :=
  (cReflectiveSourceWorkQueueRunN .leaveInert 1 foreignActivationProgram).1

/-- An opaque rule with expression-local variables. The inventory loader must
transport this exact value rather than inspect or reconstruct it. -/
def canaryOpaqueRule : Atom :=
  .expression
    [.symbol "exec",
      .expression [.symbol "98", .symbol "compressed-inventory-probe"],
      .expression
        [.symbol ",",
          .expression [.symbol "compressed-probe", .var "payload"]],
      .expression
        [.symbol "O",
          .expression
            [.symbol "+",
              .expression [.symbol "compressed-seen", .var "payload"]]]]

def canaryRuleRow : Atom :=
  linkedRow "compressed-verifier-rule" compressedVerifierRuleOwner 0 1
    canaryOpaqueRule

def loadProgram : List Atom :=
  [sourceCompressedRuleLoadRule, canaryLoading 0, canaryRuleRow]

def loadFinal : List Atom :=
  (cReflectiveSourceWorkQueueRunN .leaveInert 1 loadProgram).1

def canaryRuleEnd (position : Nat) : Atom :=
  .expression
    [.symbol "mm-compressed-verifier-rule-end", natAtom position]

def finishProgram : List Atom :=
  [sourceCompressedRuleFinishRule, canaryLoading 1, canaryRuleEnd 1]

def finishFinal : List Atom :=
  (cReflectiveSourceWorkQueueRunN .leaveInert 1 finishProgram).1

def wrongFinishProgram : List Atom :=
  [sourceCompressedRuleFinishRule, canaryLoading 1, canaryRuleEnd 2]

def wrongFinishFinal : List Atom :=
  (cReflectiveSourceWorkQueueRunN .leaveInert 1 wrongFinishProgram).1

end Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivationCanary
