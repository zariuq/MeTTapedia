import Mettapedia.Logic.Prolog.Core

/-!
# Prolog Runtime-Error Specification (ISO Boundary Layer)

The `PrologGoal` AST in `Core.lean` is intentionally typed and only represents
callable goals. Therefore, malformed-callability cases from ISO suites (e.g.
`\+ 3`, `findall(_, 4, _)`, `findall(_, G, S)` with uninstantiated `G`) are not
directly representable inside `PrologEval`.

This file formalizes the expected runtime-error classes for those boundary IDs so
the adaptation is explicit and theorem-level, instead of being implicit comments.
-/

namespace Mettapedia.Logic.Prolog

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Runtime-error classes tracked for the current ISO boundary cases. -/
inductive RuntimeErrorClass where
  | instantiationError
  | typeErrorCallable (culprit : Pattern)
  deriving Repr, DecidableEq

namespace RuntimeErrorClass

def instantiation : RuntimeErrorClass := .instantiationError
def callable3 : RuntimeErrorClass := .typeErrorCallable (.apply "3" [])
def callable4 : RuntimeErrorClass := .typeErrorCallable (.apply "4" [])

end RuntimeErrorClass

/-- ISO runtime-error expectations for currently out-of-model callable checks. -/
def isoRuntimeErrorSpec : String → Option RuntimeErrorClass
  | "iso_not_1_06"    => some RuntimeErrorClass.callable3
  | "iso_not_1_07"    => some RuntimeErrorClass.instantiation
  | "iso_findall_3_07" => some RuntimeErrorClass.instantiation
  | "iso_findall_3_08" => some RuntimeErrorClass.callable4
  | _                 => none

/-- `\+ 3` callability error class. -/
theorem iso_not_1_06_runtime_error :
    isoRuntimeErrorSpec "iso_not_1_06" = some RuntimeErrorClass.callable3 := rfl

/-- `\+ G` with uninstantiated `G` instantiation error class. -/
theorem iso_not_1_07_runtime_error :
    isoRuntimeErrorSpec "iso_not_1_07" = some RuntimeErrorClass.instantiation := rfl

/-- `findall(_, G, _)` with uninstantiated `G` instantiation error class. -/
theorem iso_findall_3_07_runtime_error :
    isoRuntimeErrorSpec "iso_findall_3_07" = some RuntimeErrorClass.instantiation := rfl

/-- `findall(_, 4, _)` callability error class. -/
theorem iso_findall_3_08_runtime_error :
    isoRuntimeErrorSpec "iso_findall_3_08" = some RuntimeErrorClass.callable4 := rfl

/-- Example non-error ID has no runtime-error entry in this boundary layer. -/
theorem iso_true_0_01_no_runtime_error :
    isoRuntimeErrorSpec "iso_true_0_01" = none := rfl

end Mettapedia.Logic.Prolog

