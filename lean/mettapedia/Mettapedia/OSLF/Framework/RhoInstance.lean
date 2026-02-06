import Mettapedia.OSLF.Framework.RewriteSystem
import Mettapedia.OSLF.RhoCalculus.Reduction
import Mathlib.Order.GaloisConnection.Defs

/-!
# rho-Calculus as an OSLF Instance

This file instantiates the abstract OSLF framework for the rho-calculus,
connecting the concrete formalization (Reduction.lean, Types.lean, Soundness.lean)
to the general OSLF construction (Framework/RewriteSystem.lean).

## Key Results

- `rhoRewriteSystem`: The rho-calculus as a `RewriteSystem`
- `rhoOSLF`: The rho-calculus OSLF type system with PROVEN Galois connection
- `rho_mathlib_galois`: Mathlib `GaloisConnection` instance

## 0 sorries, 0 axioms

The Galois connection is proven by lifting the existing `galois_connection`
theorem from Reduction.lean. All specs (`diamond_spec`, `box_spec`) are
proven by definitional equality.

## References

- Meredith & Stay, "Operational Semantics in Logical Form" section 8 (rho-calculus instance)
- Meredith & Radestock, "A Reflective Higher-Order Calculus"
-/

namespace Mettapedia.OSLF.Framework.RhoInstance

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.RhoCalculus.Reduction
open Mettapedia.OSLF.Framework

/-! ## rho-Calculus Sorts -/

/-- The sorts of the rho-calculus: processes and names.

    Processes (Proc) are the computational entities.
    Names (Name) are channels for communication.

    The key reflective structure: names are quoted processes (@p),
    and processes can dereference names (*n).
-/
inductive RhoSort where
  | Proc : RhoSort
  | Name : RhoSort
deriving DecidableEq

/-! ## The Rewrite System -/

/-- The rho-calculus as a rewrite system.

    - Sort: {Proc, Name}
    - Pr: Proc (processes carry the reduction relation)
    - Term: both sorts use Pattern (the shared syntax)
    - Reduces: wraps the Type-valued `Reduces` from Reduction.lean into Prop via Nonempty

    The reduction relation includes:
    - COMM: {n!(q) | for(x<-n){p}} reduces {p[@q/x]}
    - DROP: *(@p) reduces p
    - PAR: congruence under parallel composition
    - EQUIV: reduction modulo structural congruence
-/
def rhoRewriteSystem : RewriteSystem where
  Sorts := RhoSort
  procSort := .Proc
  Term := fun _ => Pattern
  Reduces := fun p q => Nonempty (p ⇝ q)

/-! ## The OSLF Type System -/

/-- The rho-calculus OSLF type system.

    This instantiates the abstract OSLF framework with the concrete
    rho-calculus definitions:

    - **Pred**: Predicates at each sort are `Pattern -> Prop` (per OSLF/Native Type Theory,
      predicates are functions from terms to Props, matching Types.lean: `ProcPred = Pattern -> Prop`)
    - **Frame**: `Pattern -> Prop` is a Frame via Mathlib's `Pi.instFrame`
    - **satisfies**: Function application (t satisfies phi iff phi t)
    - **diamond**: `possiblyProp` from Reduction.lean
    - **box**: `relyProp` from Reduction.lean
    - **galois**: PROVEN from the existing `galois_connection` theorem

    All fields are either definitional equalities or direct applications
    of existing proven theorems. **0 sorries.**
-/
def rhoOSLF : OSLFTypeSystem rhoRewriteSystem where
  Pred := fun _ => Pattern → Prop
  frame := fun _ => inferInstance
  satisfies := fun t φ => φ t
  diamond := possiblyProp
  diamond_spec := fun _ _ => Iff.rfl
  box := relyProp
  box_spec := fun _ _ => Iff.rfl
  galois := fun φ ψ => galois_connection φ ψ

/-! ## Mathlib GaloisConnection

The Galois connection from Mathlib requires `Preorder` on `Pattern -> Prop`,
which is provided by the `Order.Frame` instance (via `Pi.instFrame`).

The order on `Pattern -> Prop` is pointwise: `phi le psi iff forall p, phi p -> psi p`.
This means `GaloisConnection possiblyProp relyProp` states:
  `forall phi psi, (forall p, possiblyProp phi p -> psi p) <-> (forall p, phi p -> relyProp psi p)`
which is exactly the `galois_connection` theorem from Reduction.lean.
-/

/-- The Galois connection diamond -| box as a Mathlib `GaloisConnection`.

    This witnesses the adjunction `possiblyProp -| relyProp` in the
    lattice-theoretic sense: `possiblyProp phi le psi <-> phi le relyProp psi`
    where `le` is pointwise implication on `Pattern -> Prop`.
-/
theorem rho_mathlib_galois : GaloisConnection possiblyProp relyProp :=
  fun φ ψ => galois_connection φ ψ

/-! ## Connecting to Concrete Formalization

The concrete rho-calculus formalization in `RhoCalculus/` uses:
- `ProcPred = Pattern -> Prop` (Types.lean) -- matches `rhoOSLF.Pred .Proc`
- `possiblyProp` / `relyProp` (Reduction.lean) -- matches `rhoOSLF.diamond` / `rhoOSLF.box`
- `NativeType` (Soundness.lean) -- a concrete version of `NativeTypeOf rhoOSLF`
- `substitutability` (Soundness.lean) -- a concrete version of `Substitutability rhoOSLF`

The abstract framework adds:
1. The OSLF type system structure, showing this IS an instance of the general algorithm
2. The Galois connection as a first-class property (not just a standalone theorem)
3. Connection points to categorical semantics via GSLT (see CategoryBridge.lean)
-/

end Mettapedia.OSLF.Framework.RhoInstance
