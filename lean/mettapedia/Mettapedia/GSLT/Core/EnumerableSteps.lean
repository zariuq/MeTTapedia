import Mettapedia.GSLT.Core.ComputabilityClasses
import Mettapedia.OSLF.MeTTaIL.EngineCoded.ReferenceSteps

/-!
# The steps of a language are recursively enumerable

A GSLT has enumerable steps when a function computable on codes lists, for a
fuel bound and a term, finitely many successors, every successor at some fuel,
and distinct terms have distinct codes (`enumerable_of_fuelFrontier`).

The reference relation of a language is such a GSLT (`referenceTheory`): its
executor lists the steps whose derivations fit in a fuel, and is computable on
the codes of patterns when the relation environment is
(`stepsAt_computable`). So **the steps of every language are recursively
enumerable on codes when its relation environment is computable on codes**
(`referenceSteps_enumerable`), and unconditionally for a language with no
relation environment (`referenceSteps_enumerable_closed`). Conversely every
recursively enumerable relation on numbers is the step relation on numerals of
a language with no relation environment
(`RewritingUniversality.re_iff_steps`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.EnumerableSteps

open Mettapedia.Computability
open ComputabilityClasses

/-- The steps of the theory are given by a fuel-indexed frontier computable on codes. -/
def FuelFrontier (G : GSLT.{0}) [Coded G.Term] : Prop :=
  ∃ frontier : ℕ → G.Term → List G.Term, CodeComputable₂ frontier ∧
    ∀ s t, G.Step s t ↔ ∃ fuel, t ∈ frontier fuel s

/-- A fuel-indexed frontier makes the steps enumerable: search for a fuel at
which the target is listed. -/
theorem enumerable_of_fuelFrontier {G : GSLT.{0}} [Coded G.Term]
    (injective : Function.Injective (code : G.Term → ℕ)) (listed : FuelFrontier G) : EnumerableSteps G := by
  obtain ⟨frontier, computable, exact⟩ := listed
  exact enumerableOnCodes_of_bounded injective computable exact

/-! ## Languages -/

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.PatternCode

/-- The reference relation of a language, with equality as equations. -/
def referenceTheory (relEnv : RelationEnv) (language : LanguageDef) : GSLT.{0} where
  Term := Pattern
  equations := equality Pattern
  rewrites := Mettapedia.OSLF.MeTTaIL.ReferenceStep.Step relEnv language
  rewrites_resp_left := fun {_ _ u} same moved => by
    cases same
    exact ⟨u, moved, rfl⟩
  rewrites_resp_right := fun moved same => by
    cases same
    exact moved

instance (relEnv : RelationEnv) (language : LanguageDef) : Coded (referenceTheory relEnv language).Term :=
  inferInstanceAs (Coded Pattern)

/-- **The steps of a language are recursively enumerable on codes** when its relation environment is
computable on codes. -/
theorem referenceSteps_enumerable (relEnv : RelationEnv) (relations : CodeComputable₂ relEnv.tuples)
    (language : LanguageDef) : EnumerableSteps (referenceTheory relEnv language) :=
  Mettapedia.OSLF.MeTTaIL.EngineCoded.referenceStep_enumerable relEnv language relations

/-- **The steps of a language without a relation environment are recursively enumerable on codes.** -/
theorem referenceSteps_enumerable_closed (language : LanguageDef) :
    EnumerableSteps (referenceTheory RelationEnv.empty language) :=
  referenceSteps_enumerable RelationEnv.empty ((CodeComputable.const []).of_eq fun _ => rfl) language

end Mettapedia.GSLT.EnumerableSteps

#print axioms Mettapedia.GSLT.EnumerableSteps.referenceSteps_enumerable
#print axioms Mettapedia.GSLT.EnumerableSteps.referenceSteps_enumerable_closed
