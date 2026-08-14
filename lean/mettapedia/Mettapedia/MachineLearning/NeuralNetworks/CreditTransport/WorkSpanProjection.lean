import Mettapedia.Algebra.WorkSpan
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ResourceSemantics

/-!
# Work/span projection of credit-transport resources

The general credit-transport resource vector already tracks work and span as
two of ten coordinates.  This module proves that projecting those coordinates
preserves both sequential and parallel composition, so the reusable algebra is
factored out rather than reimplemented.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

open Mettapedia.Algebra

namespace ResourceVector

/-- Forget every resource coordinate except total work and critical-path span. -/
def workSpan (resource : ResourceVector) : WorkSpan :=
  ⟨resource.scalarWork, resource.criticalPathSpan⟩

@[simp] theorem workSpan_zero : workSpan 0 = 0 := rfl

/-- Projection preserves sequential composition exactly. -/
theorem workSpan_sequential (first second : ResourceVector) :
    workSpan (sequential first second) =
      WorkSpan.sequential (workSpan first) (workSpan second) :=
  rfl

/-- Projection preserves independent parallel composition exactly. -/
theorem workSpan_parallel (left right : ResourceVector) :
    workSpan (parallel left right) =
      WorkSpan.parallel (workSpan left) (workSpan right) :=
  rfl

/-- Positive example: the pre-existing ten-coordinate model really exposes
the generic work/span algebra by projection. -/
example (left right : ResourceVector) :
    (parallel left right).criticalPathSpan =
      (WorkSpan.parallel (workSpan left) (workSpan right)).span :=
  rfl

/-- Negative control: the projection intentionally forgets coordinates, so it
is not injective on full resource vectors. -/
example :
    workSpan ({ persistentMemory := 1 } : ResourceVector) =
      workSpan ({ persistentMemory := 2 } : ResourceVector) :=
  rfl

end ResourceVector

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
