import Mettapedia.Languages.MeTTa.TypeTheory.StagedReflective.Presentation
import Mettapedia.Languages.MeTTa.Prime.UniversalName

/-!
# Prime/rho structural non-collapse

Prime should internalize rho-style interaction without identifying its whole
native language with the rho calculus.  This module makes that boundary
precise at the raw-syntax level.

`DirectRhoFragment` is a deliberately generous rho-bearing fragment of
MeTTa Native syntax.  It contains arbitrary rho `Pattern` values and is closed
under native empty collections, superposition, and staged quotation.  Thus the
separation below does not depend on choosing only the one-node `pattern`
embedding.

The dependent Pure core is disjoint from this fragment.  In particular, a
native dependent function type is not a direct rho term, so the rho-bearing
fragment does not span Prime's native syntax.  This is a structural theorem
about the native constructors and the project's direct Prime-to-rho bridge.
It does not rule out an interpreter, a compiler, or another computational
encoding of Prime syntax as rho data.
-/

namespace Mettapedia.Languages.MeTTa.Prime.RhoNonCollapse

open Mettapedia.Languages.MeTTa.StagedReflective
open Mettapedia.Languages.MeTTa.Prime.UniversalName
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The direct rho-bearing fragment of MeTTa Native syntax.

The `pattern` case contains the complete rho syntax represented by `Pattern`.
The remaining cases close that image under the native collection and staging
constructors that are natural for interaction.  Dependent type formers are
intentionally absent: adding them would be an interpretation of dependent
type theory, rather than a direct rho embedding. -/
inductive DirectRhoFragment :
    {stage binders : Nat} → StagedReflectiveTm stage binders → Prop where
  | pattern {stage binders : Nat} (value : Pattern) :
      DirectRhoFragment (.pattern value : StagedReflectiveTm stage binders)
  | empty {stage binders : Nat} :
      DirectRhoFragment (.empty : StagedReflectiveTm stage binders)
  | superpose {stage binders : Nat}
      {left right : StagedReflectiveTm stage binders} :
      DirectRhoFragment left → DirectRhoFragment right →
      DirectRhoFragment (.superpose left right)
  | quote {high low binders : Nat} (route : StageHom high low)
      {term : StagedReflectiveTm high binders} :
      DirectRhoFragment term → DirectRhoFragment (.quote route term)

namespace DirectRhoFragment

/-- Every direct rho-bearing term is outside the partial projection to the
dependent Pure syntax. -/
@[simp] theorem pureProjection_eq_none
    {stage binders : Nat} {term : StagedReflectiveTm stage binders}
    (direct : DirectRhoFragment term) :
    term.pureProjection = none := by
  cases direct <;> rfl

/-- The direct rho-bearing fragment is closed under native superposition. -/
theorem superpose_closed {stage binders : Nat}
    {left right : StagedReflectiveTm stage binders}
    (leftDirect : DirectRhoFragment left)
    (rightDirect : DirectRhoFragment right) :
    DirectRhoFragment (.superpose left right) :=
  .superpose leftDirect rightDirect

/-- The direct rho-bearing fragment is closed under native quotation. -/
theorem quote_closed {high low binders : Nat} (route : StageHom high low)
    {term : StagedReflectiveTm high binders}
    (direct : DirectRhoFragment term) :
    DirectRhoFragment (.quote route term) :=
  .quote route direct

end DirectRhoFragment

/-- The current structural Prime-name translation lands in the direct
rho-bearing fragment when reified as a native runtime pattern. -/
def translatedPrimeName (name : PrimeName) : StagedReflectiveTm 0 0 :=
  .pattern (primeNameToRho name)

theorem translatedPrimeName_mem (name : PrimeName) :
    DirectRhoFragment (translatedPrimeName name) :=
  .pattern _

/-- No intrinsically Pure term is a direct rho-bearing native term.  The
separation holds for the entire conservative dependent core, not merely for
one selected constructor. -/
theorem pureImage_disjoint_directRho
    {stage binders : Nat} (term : PureTm binders) :
    ¬ DirectRhoFragment (embedPure stage term) := by
  intro direct
  have rejected := direct.pureProjection_eq_none
  rw [pureProjection_embedPure] at rejected
  cases rejected

/-- A closed dependent function type in the native core. -/
def nativeDependentFunctionType : StagedReflectiveTm 0 0 :=
  embedPure 0 (.pi .u0 .u0 : PureTm 0)

/-- The dependent function type is a concrete negative witness for the direct
rho-bearing fragment. -/
theorem nativeDependentFunctionType_not_directRho :
    ¬ DirectRhoFragment nativeDependentFunctionType := by
  exact pureImage_disjoint_directRho (.pi .u0 .u0 : PureTm 0)

/-- Structural rho spanning at an index means that every native term at that
index already belongs to the direct rho-bearing fragment. -/
def RhoSpansNativeAt (stage binders : Nat) : Prop :=
  ∀ term : StagedReflectiveTm stage binders, DirectRhoFragment term

/-- **Prime does not structurally collapse to rho.**  Even at the closed base
stage, the direct rho-bearing fragment fails to span native syntax. -/
theorem rho_does_not_span_closed_native_core :
    ¬ RhoSpansNativeAt 0 0 := by
  intro spans
  exact nativeDependentFunctionType_not_directRho
    (spans nativeDependentFunctionType)

/-! ## Positive and negative controls -/

example : DirectRhoFragment
    (.pattern (primeNameToRho UniversalName.mmPh) : StagedReflectiveTm 0 0) :=
  .pattern _

example : ¬ DirectRhoFragment nativeDependentFunctionType :=
  nativeDependentFunctionType_not_directRho

#print axioms translatedPrimeName_mem
#print axioms pureImage_disjoint_directRho
#print axioms nativeDependentFunctionType_not_directRho
#print axioms rho_does_not_span_closed_native_core

end Mettapedia.Languages.MeTTa.Prime.RhoNonCollapse
