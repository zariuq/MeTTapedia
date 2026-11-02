import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedContainerGuardedMethodContexts

/-!
# Equations for a generated method telescope

Normalize the complete dependent pair of size and source context before
transporting its context component. This retains the original generator and
does not require unfolding its size proofs inside a dependent cast.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedContainerAnnotated

open Mettapedia.Logic
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.IndexedPositiveContainer
open Presentation TypedEquality.Annotated
universe u v
variable {I : Interface.{u}} {registry : Registry I} {Head : Type} {Base : Type v}

private theorem transport_pair {F : Nat → Type} (pair : Σ size, F size) {size : Nat}
    (sameSize : pair.1 = size) (value : F size) (same : pair = ⟨size, value⟩) :
    sameSize ▸ pair.2 = value := by
  cases same
  rfl

theorem generatedMethodSource_eq (carriers : MethodCarriers I registry Base) (indexing : Indexing I Head)
    (containers : RegistrySyntax I registry Head) {parameters : Nat} {context : List I.SortCode}
    (code : Code I registry parameters context) {Γ : HOL.Ctx Base} (ambient : CCtx Head Γ.length)
    (types : TypeSyntax I Head Γ.length) (environment : TermEnvironment I Head Γ.length context)
    (motive constructor : CTm Head Γ.length) (pending : List (CTm Head Γ.length))
    (pendingCarriers : HOL.Ctx Base) (sameLength : pending.length = pendingCarriers.length)
    (explicit : CCtx Head (carriers.context code Γ pendingCarriers).length)
    (same : methodContext indexing containers code ambient types environment motive constructor pending =
      ⟨(carriers.context code Γ pendingCarriers).length, explicit⟩) :
    generatedMethodSource carriers indexing containers code ambient types environment motive constructor
      pending pendingCarriers sameLength = explicit :=
  transport_pair _ _ _ same

#print axioms generatedMethodSource_eq

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedContainerAnnotated
