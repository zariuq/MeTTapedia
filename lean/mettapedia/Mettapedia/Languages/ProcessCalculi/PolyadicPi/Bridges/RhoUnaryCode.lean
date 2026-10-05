import Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedAllocationRuns
import Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedNamed

/-!
# Scoped core-rho code for unary name passing

Public source names and allocator-generated names have different concrete
representations. A generated name is the quote of its seed code, so forwarding
that name sends the seed code itself. A public atom is forwarded as its drop.
Bound names retain the drop until the input that binds them communicates.

The scoped code records contain only sort, scope and normalization facts.
Their constructors emit the existing rho syntax and supply no operational
authorization or compiler correctness assumption.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryCode

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEncodingTyping
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedServers
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedNamed
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedAllocation

/-- Reserved infrastructure channels are distinct from public source atoms. -/
inductive Reserved where
  | code | state | request | reply
  deriving DecidableEq, Repr

def Reserved.label : Reserved → String
  | .code => "rho-spine:code"
  | .state => "rho-spine:state"
  | .request => "rho-spine:request"
  | .reply => "rho-spine:reply"

/-- The values of source names in a target scope. No source syntax or source
transition relation is added. -/
inductive NameValue (depth : Nat) where
  | bound (index : Fin depth)
  | atom (label : String)
  | allocated (index : Nat)
  | reserved (channel : Reserved)
  deriving DecidableEq, Repr

def NameValue.term {depth : Nat} : NameValue depth → Pattern
  | .bound index => .bvar index
  | .atom label => .fvar ("pi-public:" ++ label)
  | .allocated index => allocatedName index
  | .reserved channel => .fvar channel.label

def NameValue.payload {depth : Nat} : NameValue depth → Pattern
  | .allocated index => seedCode index
  | name => .apply "PDrop" [name.term]

abbrev bounds (depth : Nat) : List String := List.replicate depth "Name"

theorem NameValue.typed {depth : Nat} (name : NameValue depth) :
    NameWellSorted rhoReflectivePresentation rhoAtomicNameContext (bounds depth) name.term := by
  cases name with
  | bound index =>
      apply NameWellSorted.bvar
      simp [bounds, rhoReflectivePresentation, index.isLt]
  | atom label | reserved label => exact .fvar rfl
  | allocated index => exact .quote ((seedCode_typed rhoAtomicNameContext index).weakenBoundRight _)

theorem NameValue.safe {depth : Nat} (name : NameValue depth) :
    binderSafeAt "NQuote" depth name.term = true := by
  cases name with
  | bound index => simp [NameValue.term, binderSafeAt, index.isLt]
  | atom label | reserved label => rfl
  | allocated index => simp [NameValue.term, allocatedName, binderSafeAt, seedCode_safe]

theorem NameValue.normalized {depth : Nat} (name : NameValue depth) :
    semanticNormalizeName name.term = name.term := by
  cases name with
  | bound index | atom index | reserved index => rfl
  | allocated index => exact allocatedName_normalized index

theorem NameValue.payload_typed {depth : Nat} (name : NameValue depth) :
    ProcWellSorted rhoReflectivePresentation rhoAtomicNameContext (bounds depth) name.payload := by
  cases name with
  | bound index | atom index | reserved index => exact .drop (NameValue.typed _)
  | allocated index => exact (seedCode_typed rhoAtomicNameContext index).weakenBoundRight _

theorem NameValue.payload_safe {depth : Nat} (name : NameValue depth) :
    binderSafeAt "NQuote" depth name.payload = true := by
  cases name with
  | bound index | atom index | reserved index =>
      simpa [NameValue.payload, binderSafeAt, binderSafeListAt] using (NameValue.safe _)
  | allocated index => exact seedCode_safe index depth

theorem NameValue.payload_normalized {depth : Nat} (name : NameValue depth) :
    semanticNormalizeProc name.payload = name.payload := by
  cases name with
  | bound index | atom index | reserved index => rfl
  | allocated index => exact seedCode_normalized index

/-- The emitted process really names the value being passed. -/
theorem NameValue.quote_payload {depth : Nat} (name : NameValue depth) :
    semanticNormalizeName (.apply "NQuote" [name.payload]) = name.term := by
  cases name with
  | bound index | atom index | reserved index => rfl
  | allocated index => exact allocatedName_normalized index

def NameValue.weaken {depth : Nat} : NameValue depth → NameValue (depth + 1)
  | .bound index => .bound ⟨index + 1, by omega⟩
  | .atom label => .atom label
  | .allocated index => .allocated index
  | .reserved channel => .reserved channel

def NameValue.channel (name : NameValue 0) : Channel rhoAtomicNameContext where
  term := name.term
  typed := name.typed
  safe := name.safe
  normalized := name.normalized

def reservedChannel (channel : Reserved) : Channel rhoAtomicNameContext :=
  (NameValue.reserved channel : NameValue 0).channel

/-- Code well-sorted in its declared number of name binders. -/
structure Code (depth : Nat) where
  term : Pattern
  typed : ProcWellSorted rhoReflectivePresentation rhoAtomicNameContext (bounds depth) term
  safe : binderSafeAt "NQuote" depth term = true
  normalized : semanticNormalizeProc term = term

namespace Code

def zero (depth : Nat) : Code depth where
  term := .apply "PZero" []
  typed := .unit
  safe := rfl
  normalized := rfl

def par {depth : Nat} (first second : Code depth) : Code depth where
  term := parallel [first.term, second.term]
  typed := .parallel (.cons first.typed (.cons second.typed .nil))
  safe := by simp [binderSafeAt, binderSafeListAt, first.safe, second.safe]
  normalized := by simp [semanticNormalizeProc, semanticNormalizeProcList,
    first.normalized, second.normalized]

def triple {depth : Nat} (first second third : Code depth) : Code depth where
  term := parallel [first.term, second.term, third.term]
  typed := .parallel (.cons first.typed (.cons second.typed (.cons third.typed .nil)))
  safe := by simp [binderSafeAt, binderSafeListAt, first.safe, second.safe, third.safe]
  normalized := by simp [semanticNormalizeProc, semanticNormalizeProcList,
    first.normalized, second.normalized, third.normalized]

def emit {depth : Nat} (channel : NameValue depth) (payload : Code depth) : Code depth where
  term := send channel.term payload.term
  typed := .output channel.typed payload.typed
  safe := by simp [binderSafeAt, binderSafeListAt, channel.safe, payload.safe]
  normalized := by simp [semanticNormalizeProc, channel.normalized, payload.normalized]

def datum {depth : Nat} (name : NameValue depth) : Code depth where
  term := name.payload
  typed := name.payload_typed
  safe := name.payload_safe
  normalized := name.payload_normalized

def sendName {depth : Nat} (channel datum : NameValue depth) : Code depth :=
  emit channel (Code.datum datum)

def listen {depth : Nat} (channel : NameValue depth) (body : Code (depth + 1)) : Code depth where
  term := receive channel.term body.term
  typed := .input channel.typed (by simpa [bounds, List.replicate_succ, rhoReflectivePresentation] using body.typed)
  safe := by simpa [binderSafeAt, binderSafeListAt, channel.safe] using body.safe
  normalized := by simp [semanticNormalizeProc, channel.normalized, body.normalized]

/-- Allocate one fresh name and bind it in the supplied scoped body. -/
def reserve {depth : Nat} (body : Code (depth + 1)) : Code depth :=
  par (sendName (.reserved .request) (.reserved .reply)) (listen (.reserved .reply) body)

def handler (body : Code 1) : Handler rhoAtomicNameContext where
  term := body.term
  typed := body.typed
  safe := body.safe
  normalized := body.normalized

end Code

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryCode
