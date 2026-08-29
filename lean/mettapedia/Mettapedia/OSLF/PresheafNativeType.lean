import Mettapedia.OSLF.PresheafNativeType.PresheafSemantics
import Mettapedia.OSLF.PresheafNativeType.InternalLanguage

/-!
# Presheaf Native Type Theory

Williams--Stay Native Type Theory has two inseparable presentations:

* `PresheafSemantics` constructs context-indexed sets, predicates, and their
  Grothendieck organization over a language; and
* `InternalLanguage` exposes the corresponding extensional higher-order
  dependent language, including indexed products and sums, comprehension,
  and the cosmic and codomain fibrations.

The umbrella deliberately names both sides.  Neither the external presheaf
semantics nor the internal dependent language is an implementation detail of
the other.
-/
