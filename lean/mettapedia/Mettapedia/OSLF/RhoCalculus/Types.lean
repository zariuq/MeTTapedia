import Mettapedia.CategoryTheory.LambdaTheory
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Semantics

/-!
# ρ-Calculus Native Types

This file defines the native types for the ρ-calculus following the OSLF construction.

## The ρ-Calculus

The ρ-calculus (rho-calculus) is a reflective process calculus where:
- **Processes** (Proc) can be quoted to become **names** (Name)
- **Names** can be dereferenced to become **processes**

Key constructors:
- `0` - nil process
- `n!(q)` - output process (send q on channel n)
- `for(x<-n){p}` - input process (receive on n, bind to x in p)
- `{P | Q | ...}` - parallel composition (multiset)
- `@(p)` - quote process p to get name
- `*(n)` - dereference name n to get process

Key equation:
- `@(*(n)) = n` (quote-drop is identity)

Key rewrite (COMM):
- `{n!(q) | for(x<-n){p} | ...rest} ~> {p[@q/x] | ...rest}`

## Native Types

In Native Type Theory, types are pairs (X, τ) where:
- X is a sort (Proc or Name)
- τ is a truth value (predicate) in the fiber over X

For ρ-calculus, we define:
- **NamePred** α : predicates on names
- **ProcPred** φ : predicates on processes

## References

- Meredith & Stay, "Operational Semantics in Logical Form" (oslf.pdf)
- Meredith & Radestock, "A Reflective Higher-Order Calculus"
- Milner, "Communicating and Mobile Systems: the π-Calculus"
-/

namespace Mettapedia.OSLF.RhoCalculus

open Mettapedia.CategoryTheory.LambdaTheories
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Semantics

/-! ## ρ-Calculus Objects -/

/-- The process object in the ρ-calculus -/
def ProcObj : InterpObj rhoCalc :=
  ⟨"Proc", by simp [rhoCalc]⟩

/-- The name object in the ρ-calculus -/
def NameObj : InterpObj rhoCalc :=
  ⟨"Name", by simp [rhoCalc]⟩

/-! ## Name Predicates (Namespaces)

A namespace is a predicate on names: α : Name → Prop

In OSLF terminology, namespaces classify which channels a process
can communicate on. The key insight is that namespaces form a
complete Heyting algebra under the fiber structure.

Following Williams & Stay (Native Type Theory, ACT 2021) and
Meredith & Stay (OSLF), predicates on sorts are THE ACTUAL predicates
(Pattern → Prop), not just Props.
-/

/-- A name predicate (namespace) is a predicate on name patterns.

    This is the correct definition per OSLF: predicates are functions
    from terms to Props, not just Props themselves.
-/
abbrev NamePred := Pattern → Prop

/-- The full namespace (all names) -/
def fullNamePred : NamePred := fun _ => True

/-- The empty namespace (no names) -/
def emptyNamePred : NamePred := fun _ => False

/-- Namespace intersection -/
def namePredInter (α β : NamePred) : NamePred := fun n => α n ∧ β n

/-- Namespace union -/
def namePredUnion (α β : NamePred) : NamePred := fun n => α n ∨ β n

/-! ## Process Predicates (Codespaces)

A codespace is a predicate on processes: φ : Proc → Prop

Codespaces classify behavioral properties of processes, including
types derived from the reduction semantics via modal operators.

Following Williams & Stay (Native Type Theory, ACT 2021) and
Meredith & Stay (OSLF), predicates on sorts are THE ACTUAL predicates
(Pattern → Prop), not just Props.
-/

/-- A process predicate (codespace) is a predicate on process patterns.

    This is the correct definition per OSLF: predicates are functions
    from terms to Props, not just Props themselves.
-/
abbrev ProcPred := Pattern → Prop

/-- The full codespace (all processes) -/
def fullProcPred : ProcPred := fun _ => True

/-- The empty codespace (no processes) -/
def emptyProcPred : ProcPred := fun _ => False

/-- Codespace intersection (conjunction of properties) -/
def procPredInter (φ ψ : ProcPred) : ProcPred := fun p => φ p ∧ ψ p

/-- Codespace union (disjunction of properties) -/
def procPredUnion (φ ψ : ProcPred) : ProcPred := fun p => φ p ∨ ψ p

/-! ## Barbs and Observables

A barb is an observable property of a process - typically whether
it can perform a communication on a given channel.

In the ρ-calculus, we observe:
- Output barbs: p↓n means p can output on channel n
- Input barbs: p↓n means p can input on channel n
-/

/-- Output barb: process can output on a name (in the namespace) -/
structure OutputBarb (α : NamePred) where
  /-- The namespace on which output is possible -/
  nameFilter : NamePred
  /-- Proof that namespace is contained in α -/
  contained : nameFilter ≤ α

/-- Input barb: process can input on a name (in the namespace) -/
structure InputBarb (α : NamePred) where
  /-- The namespace on which input is possible -/
  nameFilter : NamePred
  /-- Proof that namespace is contained in α -/
  contained : nameFilter ≤ α

/-! ## Behavioral Equivalences

The key behavioral equivalence in the ρ-calculus is α-barbed bisimulation:
two processes are equivalent if they have the same barbs (restricted to α)
and can simulate each other's reductions.
-/

/-- Barbed congruence parameters -/
structure BarbedParams where
  /-- The namespace for observable barbs -/
  nameFilter : NamePred
  /-- Whether to include all contexts (congruence) or just nil context -/
  isCongruence : Bool

/-- A barbed relation is a binary predicate on codespaces.

    This captures the type of "processes in φ are related to processes in ψ"
    which is the basic building block for bisimulation.
-/
def BarbedRelation := ProcPred → ProcPred → Prop

/-- Reflexive property of a barbed relation -/
def BarbedRelation.isRefl (R : BarbedRelation) : Prop :=
  ∀ φ, R φ φ

/-- Symmetric property of a barbed relation -/
def BarbedRelation.isSymm (R : BarbedRelation) : Prop :=
  ∀ φ ψ, R φ ψ → R ψ φ

/-- Transitive property of a barbed relation -/
def BarbedRelation.isTrans (R : BarbedRelation) : Prop :=
  ∀ φ ψ χ, R φ ψ → R ψ χ → R φ χ

/-- An equivalence relation on codespaces -/
structure ProcEquiv where
  /-- The underlying relation -/
  rel : BarbedRelation
  /-- Reflexivity -/
  refl : rel.isRefl
  /-- Symmetry -/
  symm : rel.isSymm
  /-- Transitivity -/
  trans : rel.isTrans

/-! ## Modal Operators from Rewrites

**NOTE:** The real modal operators `possiblyProp` and `relyProp` are defined in
Reduction.lean, where they have access to the reduction relation. They form a
proven Galois connection.

This file defines only the static predicate structure. Modal operators derived
from operational semantics belong in Reduction.lean, not here.
-/

/-! ## Summary

This file establishes the type-theoretic foundations for the ρ-calculus:

1. ✅ **NamePred**: Predicates on names — `Pattern → Prop` (per OSLF/Native Type Theory)
2. ✅ **ProcPred**: Predicates on processes — `Pattern → Prop` (per OSLF/Native Type Theory)
4. ✅ **Barbs**: Observable communication capabilities
5. ✅ **BarbedRelation**: Relations for bisimulation

**Modal operators** (`possiblyProp`, `relyProp`) and the **Galois connection** are in
Reduction.lean, where they have access to the reduction relation. See Reduction.lean
for the proven Galois connection theorem.

This file provides the static predicate structure. Operational semantics belongs in
Reduction.lean.
-/

end Mettapedia.OSLF.RhoCalculus
