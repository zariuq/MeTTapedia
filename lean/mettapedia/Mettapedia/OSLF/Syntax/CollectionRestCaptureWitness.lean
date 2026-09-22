import Mettapedia.OSLF.MeTTaIL.Match

/-!
# The rest variable of a collection is a scope, and firing must respect it

A collection pattern has two ways to carry a matched value: an element
metavariable, and the rest variable that stands for everything the elements did
not take.  Bag matching is *nondeterministic* -- it may send a given element to
an element metavariable in one solution and into the rest in another -- so the
two carriers must transport a value the same way, or the choice becomes
observable in the result.

That is the sharpest form the scope-correctness requirement takes here, and it
is stated below as an equality between the two solutions of one match.

The rule used is the smallest one that can see the difference: it matches a bag
*under* a binder and re-emits it under one more, so a value carrying a de Bruijn
index into the emitted term must be shifted by one to keep naming the binder it
was matched against.
-/

namespace Mettapedia.OSLF.Syntax.CollectionRestCapture

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

set_option autoImplicit false

/-- Matches a bag under a binder: one element is named, the rest is carried. -/
def restLhs : Pattern :=
  .lambda (some "z") (.collection .hashBag [.fvar "S"] (some "rest"))

/-- Re-emits the same bag one binder deeper. -/
def restRhs : Pattern :=
  .lambda (some "z") (.lambda (some "w") (.collection .hashBag [.fvar "S"] (some "rest")))

/-- A closed redex: under the binder, a bag holding a constant and the bound
variable itself. -/
def restSource : Pattern :=
  .lambda (some "z") (.collection .hashBag [.apply "A" [], .bvar 0] none)

/-- Bag matching really is nondeterministic here: there are two solutions, and
they disagree about which carrier takes the bound variable. -/
theorem two_solutions :
    matchPattern restLhs restSource =
      [[("rest", .collection .hashBag [.bvar 0] none), ("S", .apply "A" [])],
       [("rest", .collection .hashBag [.apply "A" []] none), ("S", .bvar 0)]] := by
  decide +kernel

/-- The element carrier transports the bound variable correctly: matched one
binder deep and delivered two deep, the index moves from `0` to `1` and still
names `z`. -/
theorem element_carrier_is_correct :
    applyBindingsScoped restLhs
        [("rest", .collection .hashBag [.apply "A" []] none), ("S", .bvar 0)] 0 restRhs
      = .lambda (some "z") (.lambda (some "w")
          (.collection .hashBag [.bvar 1, .apply "A" []] none)) := by
  decide +kernel

/-- **The rest carrier does too.**  The spliced elements are shifted by the same
difference of depths as an element metavariable's value, so the index still
names `z` rather than the binder the rule introduced. -/
theorem rest_carrier_is_correct :
    applyBindingsScoped restLhs
        [("rest", .collection .hashBag [.bvar 0] none), ("S", .apply "A" [])] 0 restRhs
      = .lambda (some "z") (.lambda (some "w")
          (.collection .hashBag [.apply "A" [], .bvar 1] none)) := by
  decide +kernel

/-- The reading that would capture: the spliced index left where it was, now
naming `w`. -/
def capturedByRest : Pattern :=
  .lambda (some "z") (.lambda (some "w")
    (.collection .hashBag [.apply "A" [], .bvar 0] none))

/-- **And the engine does not produce it.**  Stated against the applier rather
than between two literals, so the guard is about the operation under test. -/
theorem rest_carrier_not_captured :
    applyBindingsScoped restLhs
        [("rest", .collection .hashBag [.bvar 0] none), ("S", .apply "A" [])] 0 restRhs
      ≠ capturedByRest := by
  rw [rest_carrier_is_correct]
  decide

/-- **The choice the matcher makes is not observable.**  Both solutions of the
same match deliver the same bag, up to the order bag elements are listed in --
which is what a bag means.  This is the property the rest variable's shift
exists to buy: without it the two solutions disagree, and a nondeterministic
matcher would make the scope of a bound variable depend on which element the
search happened to take first. -/
theorem carriers_agree :
    (matchPattern restLhs restSource).map
        (fun bindings => applyBindingsScoped restLhs bindings 0 restRhs)
      = [.lambda (some "z") (.lambda (some "w")
            (.collection .hashBag [.apply "A" [], .bvar 1] none)),
         .lambda (some "z") (.lambda (some "w")
            (.collection .hashBag [.bvar 1, .apply "A" []] none))] := by
  decide +kernel

/-- **Both deliveries are the same bag**, and this says so about the matcher's
own output rather than about two literals standing beside it: same binders, and
element lists that are permutations of one another -- which is what a bag means,
and is the property the rest variable's shift exists to buy. -/
theorem carriers_agree_as_bags :
    ∃ left right : List Pattern,
      (matchPattern restLhs restSource).map
          (fun bindings => applyBindingsScoped restLhs bindings 0 restRhs)
        = [.lambda (some "z") (.lambda (some "w") (.collection .hashBag left none)),
           .lambda (some "z") (.lambda (some "w") (.collection .hashBag right none))]
        ∧ left.Perm right :=
  ⟨[.apply "A" [], .bvar 1], [.bvar 1, .apply "A" []],
    carriers_agree, List.Perm.swap _ _ _⟩

/-- The rest variable is a metavariable of the left-hand side, so it has a
capture depth like any other.  Reading it off is what makes the shift above
computable: `rest` is captured one binder deep, exactly where `S` is. -/
theorem rest_captureDepth :
    captureDepth "rest" 0 restLhs = some 1 := rfl

/-- Both carriers report the same depth, which is why they transport alike. -/
theorem element_captureDepth :
    captureDepth "S" 0 restLhs = some 1 := rfl

end Mettapedia.OSLF.Syntax.CollectionRestCapture
