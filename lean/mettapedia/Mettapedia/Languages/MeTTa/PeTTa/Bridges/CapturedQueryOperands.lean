import Mettapedia.Languages.MeTTa.PeTTa.Bridges.LiteralQuerySource

/-!
# Query operands forced by the reached source equations

One actual principal unifier reads all operand positions. Admission requires
a canonical handle, a plain closed literal pattern and an inert scalar
payload. The resulting readings hold in every model of the reached equations,
not just in a chosen convenient assignment. Consistent equation extensions
therefore preserve them. The original invocation and equations are retained.

This is a prepared-invocation boundary. Reading an authored effectful operand
as syntax does not evaluate it; such an operand is not admitted as a handle.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedQueryOperands

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination

structure Arguments where
  location : Atom
  pattern : Atom
  payload : Atom

def Arguments.atoms (arguments : Arguments) : List Atom :=
  [arguments.location, arguments.pattern, arguments.payload]

def values (request : LiteralQuerySource.Request) : List Atom :=
  [Effects.handleValue request.handle, request.pattern, request.payload]

structure Captured (bindings : Equations) (arguments : Arguments) where
  request : LiteralQuerySource.Request
  principal : Environment
  resolved : resolve bindings = some principal
  models : ∀ environment, Solves environment bindings →
    arguments.atoms.map (EagerDFS.Destination.read environment) = values request

/-- Closed materializations of the actual principal unifier are forced by
the original equations. The existing unifier's model theorem supplies this
fact; no ground-answer oracle is assumed. -/
theorem resolved_forces {bindings : Equations} {principal : Environment}
    (resolved : resolve bindings = some principal) (source value : Atom)
    (readValue : EagerDFS.Destination.read principal source = value)
    (closed : ∀ environment, EagerDFS.Destination.read environment value = value)
    (environment : Environment) (solved : Solves environment bindings) :
    EagerDFS.Destination.read environment source = value := by
  have preserved := resolve_read_preserves resolved environment solved source
  rw [readValue, closed] at preserved
  exact preserved.symm

theorem request_fields (handle : NamedSpaces.Handle) (pattern payload : Atom)
    (request : LiteralQuerySource.Request)
    (selected : LiteralQuerySource.ofPattern handle pattern payload = some request) :
    request.handle = handle ∧ request.pattern = pattern ∧ request.payload = payload := by
  unfold LiteralQuerySource.ofPattern at selected
  split at selected
  · split at selected
    · split at selected
      · cases Option.some.inj selected
        exact ⟨rfl, rfl, rfl⟩
      · contradiction
    · contradiction
  · contradiction

def fromResolved (bindings : Equations) (arguments : Arguments) (principal : Environment)
    (resolved : resolve bindings = some principal) : Option (Captured bindings arguments) :=
  match handleRead : Effects.readHandle (EagerDFS.Destination.read principal arguments.location) with
  | none => none
  | some handle =>
      match selected : LiteralQuerySource.ofPattern handle
          (EagerDFS.Destination.read principal arguments.pattern)
          (EagerDFS.Destination.read principal arguments.payload) with
      | none => none
      | some request => some {
          request, principal, resolved
          models := by
            intro environment solved
            obtain ⟨handleEq, patternEq, payloadEq⟩ := request_fields _ _ _ request selected
            have locationRead : EagerDFS.Destination.read principal arguments.location =
                Effects.handleValue request.handle := by
              rw [handleEq]
              exact (LiteralQuerySource.handle_readback _ handle handleRead).symm
            have location := resolved_forces resolved arguments.location _ locationRead
              (LiteralQuerySource.read_handle request.handle) environment solved
            have pattern := resolved_forces resolved arguments.pattern _ patternEq.symm
              (LiteralQuerySource.read_pattern request) environment solved
            have payload := resolved_forces resolved arguments.payload _ payloadEq.symm
              (LiteralQuerySource.read_payload request) environment solved
            simp only [Arguments.atoms, values, List.map_cons, List.map_nil, location, pattern, payload] }

def capture (bindings : Equations) (arguments : Arguments) : Option (Captured bindings arguments) :=
  match resolved : resolve bindings with
  | none => none
  | some principal => fromResolved bindings arguments principal resolved

theorem inconsistent_refuses (bindings : Equations) (arguments : Arguments)
    (inconsistent : resolve bindings = none) : capture bindings arguments = none := by
  unfold capture
  split
  · rfl
  · rename_i principal resolved
    rw [inconsistent] at resolved
    contradiction

theorem Captured.operands {bindings : Equations} {arguments : Arguments}
    (captured : Captured bindings arguments) :
    arguments.atoms.map (EagerDFS.Destination.read captured.principal) = values captured.request :=
  captured.models _ (resolve_sound captured.resolved)

/-- Revalidation solves the new reached equations. Contradictory extensions
cannot obtain a usable certificate merely because every model would satisfy
a vacuous implication. -/
def Captured.extend {bindings : Equations} {arguments : Arguments}
    (captured : Captured bindings arguments) (added : Equations) :
    Option (Captured (bindings ++ added) arguments) :=
  match resolved : resolve (bindings ++ added) with
  | none => none
  | some principal => some {
      request := captured.request
      principal, resolved
      models := fun environment solved => captured.models environment
        (fun pair member => solved pair (List.mem_append_left added member)) }

theorem Captured.extension_refuses_inconsistent {bindings : Equations} {arguments : Arguments}
    (captured : Captured bindings arguments) (added : Equations)
    (inconsistent : resolve (bindings ++ added) = none) : captured.extend added = none := by
  unfold Captured.extend
  split
  · rfl
  · rename_i principal resolved
    rw [inconsistent] at resolved
    contradiction

theorem Captured.extension_keeps_request {bindings : Equations} {arguments : Arguments}
    (captured : Captured bindings arguments) (added : Equations)
    (next : Captured (bindings ++ added) arguments) (extended : captured.extend added = some next) :
    next.request = captured.request := by
  unfold Captured.extend at extended
  split at extended
  · contradiction
  · cases Option.some.inj extended
    rfl

/-- The original, unrewritten operand tuple invokes the declared query at
the selected current space. Capturing bindings does not supply a snapshot. -/
theorem Captured.primitive_query {bindings : Equations} {arguments : Arguments}
    (captured : Captured bindings arguments) (state : Effects.State)
    (reading : LiteralQuerySource.PreparedRead captured.request state) :
    StdLib.apply state "match" (arguments.atoms.map (EagerDFS.Destination.read captured.principal)) =
      .ok (state, SpaceSemantics.query reading.rows captured.request.pattern captured.request.payload) := by
  rw [captured.operands]
  exact ConstantQuerySource.primitive_query state captured.request.handle reading.rows
    captured.request.pattern captured.request.payload reading.snapshot

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedQueryOperands
