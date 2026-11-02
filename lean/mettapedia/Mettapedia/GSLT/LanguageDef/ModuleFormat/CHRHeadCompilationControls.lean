import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRVariableCaptures
import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPlanReading
import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCanonicalPublication
import Mettapedia.Languages.CHR.Examples
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineCertified

/-! Controls use the actual CHR compiler and shared scoped matcher. They
separate repeated-variable equality, distinct resource positions and literal
pool identity. These are executable regression checks, complementing the
general kernel-checked readback laws. Successful head proposals still require
guards and history authorization in the controller. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.HeadCompilationControls

open Mettapedia.Languages.CHR
open Mettapedia.OSLF.MeTTaIL Syntax ScopedRuleMatching
open GeneralScopedMatchMachine

def vocabulary : Vocabulary := ⟨["signal", "other"], [.atom "a", .atom "b", .integer (-2)]⟩
def repeated : Head := ⟨"signal", [.tuple [.var 0, .var 0]]⟩
def sourceRule : Rule := ⟨"pair", [], [repeated, repeated], [], []⟩
def tuple (first second : Pattern) : Pattern := .apply "ChrTuple" [vector [first, second]]
def row (id predicate : Nat) (first second : Pattern) : Pattern := occurrence (occurrenceRef id)
  (.apply "ChrConstraint" [predicateRef predicate, vector [tuple first second]])
def completedProposals (compiled : RewriteRule) (target : Pattern) : Option (List Answer) :=
  let request : Request := ⟨compiled, {dependencies := compiled.typeContext.map (fun entry => (entry.1, []))},
    0, .left, [], 0, [], compiled.left, target⟩
  let state := run request 500 (start request)
  if complete state then some state.answers else none

def proposals (contents : List Pattern) : Option (List Answer) := do
  let compiled ← compileRule? vocabulary 0 0 sourceRule
  completedProposals compiled (request vocabulary 0 0 contents)

#guard (compileRule? vocabulary 0 0 sourceRule).isSome

-- Repeated variables agree inside tuples and across distinct heads.
#guard (proposals [row 0 0 (scalarRef 0) (scalarRef 0),
  row 1 0 (scalarRef 0) (scalarRef 0)]).map List.length == some 1
#guard (proposals [row 0 0 (scalarRef 0) (scalarRef 1),
  row 1 0 (scalarRef 0) (scalarRef 0)]).map List.length == some 0
#guard (proposals [row 0 0 (scalarRef 0) (scalarRef 0),
  row 1 0 (scalarRef 1) (scalarRef 1)]).map List.length == some 0

-- One resource cannot fill two heads; two distinct equal partners survive.
#guard (proposals [row 0 0 (scalarRef 0) (scalarRef 0)]).map List.length == some 0
#guard (proposals [row 0 0 (scalarRef 0) (scalarRef 0),
  row 1 0 (scalarRef 0) (scalarRef 0), row 2 0 (scalarRef 0) (scalarRef 0)]).map List.length == some 2
#guard (proposals [row 0 0 (scalarRef 0) (scalarRef 0),
  row 1 1 (scalarRef 0) (scalarRef 0)]).map List.length == some 0

def literalHead : Head := ⟨"signal", [.value (.integer (-2))]⟩
def literalSource : Rule := ⟨"literal", [], [literalHead], [], []⟩
def literalProposals (number : Int) : Option (List Answer) := do
  let compiled ← compileRule? vocabulary 0 0 literalSource
  completedProposals compiled (request vocabulary 0 0 [occurrence (occurrenceRef 0)
    (.apply "ChrConstraint" [predicateRef 0, vector [integer number]])])

#guard (compileRule? vocabulary 0 0 literalSource).isSome
#guard (literalProposals (-2)).map List.length == some 1
#guard (literalProposals 2).map List.length == some 0

-- Every query in the fixed prepared programs reaches the actual plan.
#guard Examples.examples.all fun sample =>
  match prepare sample.program sample.inputs with
  | .error _ => false
  | .ok prepared =>
    (plan prepared).rules.length == prepared.entries.length &&
      (plan prepared).rules.all fun selected => GeneralPremise.checkZeroDependencies selected.binding.spec

-- Canonical stores keep distinct equal resources and tuple-field order.
#guard CanonicalBags.canon (store [row 1 0 (scalarRef 0) (scalarRef 0), row 0 0 (scalarRef 0) (scalarRef 0)]) ==
  CanonicalBags.canon (store [row 0 0 (scalarRef 0) (scalarRef 0), row 1 0 (scalarRef 0) (scalarRef 0)])
#guard CanonicalBags.canon (store [row 0 0 (scalarRef 0) (scalarRef 0)]) !=
  CanonicalBags.canon (store [row 0 0 (scalarRef 0) (scalarRef 0), row 1 0 (scalarRef 0) (scalarRef 0)])
#guard CanonicalBags.canon (tuple (scalarRef 0) (scalarRef 1)) !=
  CanonicalBags.canon (tuple (scalarRef 1) (scalarRef 0))

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.HeadCompilationControls
