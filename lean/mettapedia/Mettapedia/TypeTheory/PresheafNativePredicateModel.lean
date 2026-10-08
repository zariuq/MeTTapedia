import Mettapedia.TypeTheory.PresheafNativePredicateCapabilities
import Mettapedia.TypeTheory.ContextualPredicateModel
import Mettapedia.TypeTheory.NativeLocalPiEta
import Mettapedia.TypeTheory.NativeLocalSumElimination

/-!
# The native local model with ordinary propositions and refinements

Dependent products and full-motive sums are combined with the actual
subfunctor doctrine, guarded assumption contexts and stable retained
refinements. The product qualification is supplied by the earned chosen
native operations. This construction is an instance of local model
capabilities, independently of a syntax interpreter or classifying theorem.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafNativePredicateModel

open _root_.CategoryTheory
open ContextualPredicateModel NativeLocalTheoryTransformation

universe u

noncomputable def model (C : Type u) [Category.{u} C] :
    LocalModel (nativeLocalModel C) where
  products := NativeLocalTypeOperations.products C
  sums := NativeLocalSumElimination.stableSums C
  doctrine := PresheafNativePredicateCapabilities.doctrine C
  propositions := PresheafNativePredicateCapabilities.propositions C
  assumptions := PresheafNativePredicateCapabilities.assumptions C
  refinements := PresheafNativePredicateCapabilities.refinements C

theorem qualification (C : Type u) [Category.{u} C] : Qualification (model C) where
  stableProducts := NativeLocalTypeOperations.products_substitution C
  productBeta := NativeLocalTypeOperations.products_beta C
  productEta := NativeLocalPiEta.products_eta C

end Mettapedia.TypeTheory.PresheafNativePredicateModel
