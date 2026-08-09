import Mettapedia.GSLT.Core.Ultrainfinite
import Mettapedia.Languages.MeTTa.CollapseSuperposeRoundTrip

/-!
# The observational retraction, instantiated and justified

`Ultrainfinite.ObservationalRetraction` states its law on the *observation*
rather than on the ambient object: compiling and decompiling must preserve
what is observed, not what was compiled.  `Syntactic` is offered as a
strictly stronger optional property.

This module supplies two things that were missing on either side of that
definition.

**Why the weaker law is the right one, in general.**
`not_syntactic_of_compile_fiber` — the syntactic property fails exactly when
compilation has a non-trivial fibre.  That is the criterion of
`Core.NonFactorization` applied to the ambient/shadow pair, so the two
doctrines meet at a single lemma rather than by analogy.

**A real instance, from the emptiness work rather than a fixture.**
`outcomeRetraction` is the collapse/superpose pair over outcomes: compile by
reifying the values, decompile by superposing them back, observe the values.
Its observational law is exactly `decode_encode`, and its syntactic property
is **refutable** — two outcomes with the same answers and different coverage
compile to the same datum, so no decompilation restores both.

So the doctrine's choice to state the law observationally is not caution.
It is forced, and here is the witness.

The instance is also *half* syntactic, which is worth recording precisely:
compiling a superposed collection returns it exactly
(`collapse_superpose`), while superposing a compiled outcome does not.  The
retraction is exact in one direction and observational in the other, and the
asymmetry is the same one the round-trip module measures.
-/

namespace Mettapedia.Languages.MeTTa.UltrainfiniteInstance

open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.Languages.MeTTa.Emptiness
open Mettapedia.Languages.MeTTa.RoundTrip
open Mettapedia.GSLT.Core.NonFactorization

/-! ## The general justification -/

/-- **The syntactic property fails exactly on a non-trivial compilation
fibre.**  If two ambient objects compile to the same code, decompilation can
return at most one of them, so exact return is impossible — whatever the
decompiler does.

This is the non-factorization criterion stated for the doctrine's own
structure: `compile` is the shadow, the ambient object is the invariant, and
a shared code with distinct sources is the fibre. -/
theorem not_syntactic_of_compile_fiber {Ambient Code Observation : Type _}
    (retraction : ObservationalRetraction Ambient Code Observation)
    {left right : Ambient}
    (sameCode : retraction.compile left = retraction.compile right)
    (different : left ≠ right) : ¬ retraction.Syntactic := by
  intro syntactic
  refine different ?_
  calc left = retraction.decompile (retraction.compile left) := (syntactic left).symm
    _ = retraction.decompile (retraction.compile right) := by rw [sameCode]
    _ = right := syntactic right

/-- Equivalently: exact return forces compilation to be injective. -/
theorem compile_injective_of_syntactic {Ambient Code Observation : Type _}
    (retraction : ObservationalRetraction Ambient Code Observation)
    (syntactic : retraction.Syntactic) :
    Function.Injective retraction.compile := by
  intro left right sameCode
  by_contra different
  exact not_syntactic_of_compile_fiber retraction sameCode different syntactic

/-! ## The instance -/

/-- **Collapse and superpose as an observational retraction.**  Compile an
outcome by reifying its values; decompile by superposing them back; observe
the values.  The doctrine's law holds, and its proof is exactly the
round-trip lemma. -/
def outcomeRetraction : ObservationalRetraction Outcome Datum (List Datum) where
  compile := collapseValues
  decompile := superpose
  observe := Outcome.values
  roundTrip_observation := by
    intro outcome
    simp [collapseValues, superpose, decode_encode]

/-- Two outcomes with the same answers and different coverage compile to the
same datum. -/
theorem coverage_shares_code :
    outcomeRetraction.compile ⟨[.unit], .complete, []⟩ =
      outcomeRetraction.compile ⟨[.unit], .incomplete "budget", []⟩ := rfl

/-- **The syntactic property is refutable on this instance.**  So the
doctrine's weaker law is necessary rather than merely convenient: the strong
version is false of a retraction we actually have. -/
theorem outcomeRetraction_not_syntactic : ¬ outcomeRetraction.Syntactic :=
  not_syntactic_of_compile_fiber outcomeRetraction coverage_shares_code (by decide)

/-- And compilation is therefore not injective, which is the same fact in the
form the criterion uses. -/
theorem outcomeRetraction_compile_not_injective :
    ¬ Function.Injective outcomeRetraction.compile := by
  intro injective
  exact outcomeRetraction_not_syntactic (fun _ => by
    exact absurd (injective coverage_shares_code) (by decide))

/-! ## Exact in one direction

The asymmetry is worth stating explicitly: the failure is on the ambient
side, not the code side. -/

/-- Compiling a decompiled *collection* returns it exactly.  So the pair is
syntactic when read from the code side, and only observational when read from
the ambient side — which is precisely the direction in which coverage and
faults live. -/
theorem exact_on_collections {datum : Datum} (collection : IsCollection datum) :
    outcomeRetraction.compile (outcomeRetraction.decompile datum) = datum :=
  collapse_superpose collection

/-- The two halves together, as the doctrine would state them. -/
theorem retraction_is_exact_one_way_only :
    (∀ datum, IsCollection datum →
        outcomeRetraction.compile (outcomeRetraction.decompile datum) = datum) ∧
      ¬ outcomeRetraction.Syntactic :=
  ⟨fun _ collection => exact_on_collections collection,
    outcomeRetraction_not_syntactic⟩

end Mettapedia.Languages.MeTTa.UltrainfiniteInstance
