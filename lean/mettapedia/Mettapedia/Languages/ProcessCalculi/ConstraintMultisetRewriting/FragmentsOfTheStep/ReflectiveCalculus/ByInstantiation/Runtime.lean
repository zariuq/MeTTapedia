import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation.ReactComparison

/-!
# The programs run on the engine, read through the program's step

For each program the engine was run on, the made rows of its communications as the program computes
them (by instantiation, `rfl`), the channel matches as the knowledge decides them, and the process
the run ends at. `Q` is `@0!(0)` (`outputZero`), `R` the same process.

* `separating`: `for(y <- @0){*y} | @0!(Q)` ends at `Q` (`separating_contractum_exact`).
* `separating_then_receiver`: `for(y <- @0){*y} | @0!(b!(0)) | for(z <- b){0}`, `b = @Q`, ends at `0`.
* `bound_bare_control`: `for(y <- @0){ y!(0) } | @0!(R) | for(z <- @R){0}` ends at `0`.
* `bound_quote_drop`: `for(y <- @0){ @(*y)!(0) } | @0!(R) | for(z <- @R){0}` ends at `0` (outside
  the sealed carrier; the instantiation agrees with the paper).
* the channel matches: `@(*@0)` and `@(0 | 0)` meet `@0`, `@(@0!(0))` does not; a free drop is no
  output.
* the three programs with a continuation that uses the received name and its drop:
  `name_and_drop_payload`, `name_and_drop_parallel`, `name_and_drop_nested`, each ending at `Q`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation.Runtime

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (canonicalize)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReaction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReactionControls

/-! ## The earlier programs -/

/-- `b = @Q`. -/
def nameQ : G [] .nm := quoteT outputZero

/-- `for(y <- @0){*y} | @0!(b!(0)) | for(z <- b){0}`: the first made row is the received `b!(0)`,
on the receiver's channel as written; the receiver's continuation `0` makes `0`. -/
theorem separating_then_receiver :
    bind (received (outputT nameQ zeroT)) twinVar = outputT nameQ zeroT ∧
      bind (received zeroT) (zeroT (D := noUnknowns) (Γ := [.nm, .pr])) = zeroT ∧
      Similar nameQ nameQ :=
  ⟨rfl, rfl, similar_refl _⟩

/-- `for(y <- @0){ y!(0) } | @0!(R) | for(z <- @R){0}`: the first made row is `@R!(0)`, on the
receiver's channel; then `0`. -/
theorem bound_bare_control :
    bind (received outputZero) (outputT nameVar zeroT) = outputT nameQ zeroT ∧
      bind (received zeroT) (zeroT (D := noUnknowns) (Γ := [.nm, .pr])) = zeroT :=
  ⟨rfl, rfl⟩

/-- `for(y <- @0){ @(*y)!(0) } | @0!(R) | for(z <- @R){0}`: the continuation is outside the sealed
carrier; its instantiation makes `@R!(0)`, on the receiver's channel, as the paper's name equivalence
`@(*y) = y` requires. -/
theorem bound_quote_drop :
    bind (received outputZero) quotedTwin = outputT nameQ zeroT := rfl

/-- **Channels**: `@(*@0)` and `@(0 | 0)` are similar to `@0`; `@(@0!(0))` is not. -/
theorem channels :
    Similar nameDropZero nameZero ∧
      Similar (quoteT (bagT (pconsT zeroT (pconsT zeroT pnilT)))) nameZero ∧
      ¬ Similar nameQ nameZero := by
  refine ⟨received_name_needs_name_equivalence.2.2.1, .name (by decide) (by decide) ?_, ?_⟩
  · show StructuralCongruence (.apply "NQuote" [.collection .hashBag
        [.apply "PZero" [], .apply "PZero" []] none]) (.apply "NQuote" [.apply "PZero" []])
    exact sc_apply_one _ (StructuralCongruence.par_nil_right _)
  · intro similar
    exact Source.names_not_equivalent (similar_canonical similar)

/-- **A free drop is no output**: `*@(@0!(0))` beside a receiver is stuck. -/
theorem free_drop_no_output (c : G [] .nm) (p : G [] .pr) : ¬ Similar (outputT c p) (dropqT outputZero) := by
  intro similar
  cases similar

/-! ## Continuations that use the received name and its drop -/

/-- `for(y <- @0){ y!(*y) } | @0!(Q) | for(z <- @Q){ *z }`: the first made row is `@Q!(Q)`, on the
receiver's channel; the receiver's `*z` makes `Q`. -/
theorem name_and_drop_payload :
    bind (received outputZero) (outputT nameVar twinVar) = outputT nameQ outputZero ∧
      bind (received outputZero) twinVar = outputZero ∧ read outputZero = payload :=
  ⟨rfl, rfl, rfl⟩

/-- `*y | y!(0)`. -/
def parallelBody : G [.nm, .pr] .pr := bagT (pconsT twinVar (pconsT (outputT nameVar zeroT) pnilT))

/-- The primes of `Q | 0` are those of `Q`. -/
theorem primes_payload_zero :
    primes (read (bagT (pconsT outputZero (pconsT zeroT (pnilT (D := noUnknowns)))))) = {payload} := by
  show primes (.collection .hashBag [payload, zeroPattern] none) = _
  rw [primes_cons_bag, primes_cons_bag, primes_empty_bag, primes_zero,
    primes_of_isPrime Source.payload_prime]
  rfl

/-- `for(y <- @0){ *y | y!(0) } | @0!(Q) | for(z <- @Q){0}`: the made row is the bag `Q | @Q!(0)`;
its output meets the receiver, whose continuation makes `0`; `Q` remains. -/
theorem name_and_drop_parallel :
    bind (received outputZero) parallelBody =
        bagT (pconsT outputZero (pconsT (outputT nameQ zeroT) pnilT)) ∧
      primes (read (bagT (pconsT outputZero (pconsT zeroT (pnilT (D := noUnknowns)))))) =
        {payload} :=
  ⟨rfl, primes_payload_zero⟩

/-- The outer twin, seen from the body of a nested input. -/
def outerTwin : G [.nm, .pr, .nm, .pr] .pr := .var (.succ (.succ (.succ .zero)))

/-- `for(w <- y){ *y | *w }`. -/
def nestedBody : G [.nm, .pr] .pr :=
  inputT nameVar (bagT (pconsT outerTwin (pconsT twinVar pnilT)))

/-- The nested continuation after the first communication: `*@Q`'s twin is `Q`, weakened. -/
def nestedAfter : G [.nm, .pr] .pr :=
  bagT (pconsT (weaken (weaken outputZero)) (pconsT twinVar pnilT))

/-- `for(y <- @0){ for(w <- y){ *y | *w } } | @0!(Q) | @Q!(0)`: the first made row is the input on
`@Q` whose continuation has `Q` for the outer drop; it meets `@Q!(0)` and makes `Q | 0`. -/
theorem name_and_drop_nested :
    bind (received outputZero) nestedBody = inputT nameQ nestedAfter ∧
      bind (received zeroT) nestedAfter = bagT (pconsT outputZero (pconsT zeroT pnilT)) ∧
      primes (read (bagT (pconsT outputZero (pconsT zeroT (pnilT (D := noUnknowns)))))) =
        {payload} :=
  ⟨rfl, rfl, primes_payload_zero⟩

/-- The nested continuation reads back as `*@(@0!(0))`'s process twin `Q` beside the inner drop. -/
theorem nestedAfter_read :
    read nestedAfter = .collection .hashBag [payload, .apply "PDrop" [.bvar 0]] none := rfl

#print axioms channels
#print axioms name_and_drop_payload
#print axioms name_and_drop_parallel
#print axioms name_and_drop_nested

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation.Runtime
