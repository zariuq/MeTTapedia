import Mettapedia.Languages.MeTTa.Prime.NativeInteractionInterpretation
import Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

/-!
# MeTTa-authored endpoints for Prime interaction computations

This module demonstrates the compile-time path from authored MeTTa syntax to
the existing Prime-native interaction interpretation:

```text
MeTTa expression text
        ↓ compile-time parser and structural embedding
Mettapedia Pattern
        ↓ StagedReflectiveTm.pattern
closed MeTTa Native term
        ↓ rhoInterpretation
exact rho interaction endpoint
```

The quotation does not infer a dependent type or create a rho reduction.  It
constructs the runtime-pattern fragment already accepted by MeTTa Native;
the intrinsic typing and interaction witnesses remain separate proof
obligations.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeInteractionSyntax

open Mettapedia.Languages.MeTTa.StagedReflective
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionInterpretation
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

/-- A request endpoint authored in PeTTa expression syntax and embedded as a
closed MeTTa Native runtime-pattern term. -/
def requestEndpoint : StagedReflectiveTm 0 0 :=
  .pattern (metta% petta "(request ticket-7 (payload datum))")

/-- A response endpoint authored in the same dialect. -/
def responseEndpoint : StagedReflectiveTm 0 0 :=
  .pattern (metta% petta "(response ticket-7 (result accepted))")

/-- The endpoint interpretation sees precisely the parsed request pattern. -/
theorem requestEndpoint_lowers :
    rhoInterpretation.lower? requestEndpoint =
      some (metta% petta "(request ticket-7 (payload datum))") :=
  rfl

/-- The endpoint interpretation sees precisely the parsed response pattern. -/
theorem responseEndpoint_lowers :
    rhoInterpretation.lower? responseEndpoint =
      some (metta% petta "(response ticket-7 (result accepted))") :=
  rfl

/-- Positive endpoint admission built from actual MeTTa syntax. -/
def requestAdmission : rhoInterpretation.Endpoint requestEndpoint :=
  ⟨metta% petta "(request ticket-7 (payload datum))", rfl⟩

/-- Negative: an intrinsic dependent function is still outside the rho
endpoint interpretation; adding source quotations does not collapse Prime's
type-theoretic constructors into runtime patterns. -/
example (domain : StagedReflectiveTm 0 0) (body : StagedReflectiveTm 0 1) :
    rhoInterpretation.lower? (.pi domain body) = none :=
  rfl

end Mettapedia.Languages.MeTTa.Prime.NativeInteractionSyntax
