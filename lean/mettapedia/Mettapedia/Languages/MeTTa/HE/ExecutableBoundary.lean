import Mettapedia.Languages.MeTTa.HE.Eval

/-!
# HE MeTTa Executable Boundary

Additive implementation-facing refinement boundary for the canonical declarative HE spec.

## Design

- `EvalSpec.lean` stays the broad, language-level declarative semantics.
- This file adds the smallest top-level predicates needed to describe what the
  current executable evaluator supports stably.
- `Correctness.lean` proves the correspondence theorems for these predicates.

This keeps the canonical semantics honest while still giving the evaluator a
precise specification boundary for each of its six entry points. The top-level
public facade can still stay focused on `EvalAtomCertified`.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-- `EvalAtomStablyReaches` is the minimal top-level executable stability
    witness. It says that from some cutoff fuel onward, the evaluator keeps
    returning the same result pair. -/
def EvalAtomStablyReaches
    (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) : Prop :=
  ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
    r ∈ evalAtom space dispatch atom type_ b fuel

/-- `EvalAtomCertified` is the additive implementation-refined HE spec for the
    top-level evaluator. It packages both:
    - the canonical declarative `EvalAtom` meaning
    - stable executable support from some fuel onward -/
def EvalAtomCertified
    (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) : Prop :=
  EvalAtom space dispatch atom type_ b r ∧
  EvalAtomStablyReaches space dispatch atom type_ b r

/-! ## Internal support predicates for the lower 5 evaluator entry points

These are proof-support definitions used by `Correctness.lean`. They are not
part of the public certification boundary. -/

namespace Internal

def InterpretExpressionStablyReaches
    (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) : Prop :=
  ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
    r ∈ interpretExpression space dispatch atom type_ b fuel

/-- Implementation-refined spec boundary for `interpretExpression`. -/
def InterpretExpressionCertified
    (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) : Prop :=
  InterpretExpression space dispatch atom type_ b r ∧
  InterpretExpressionStablyReaches space dispatch atom type_ b r

/-- Stable executable witness for `interpretFunction`.
    This boundary follows the evaluator entry point, so it intentionally does
    not quantify over `retType` as an input. -/
def InterpretFunctionStablyReaches
    (space : Space) (dispatch : GroundedDispatch)
    (atom opType : Atom) (b : Bindings) (r : ResultPair) : Prop :=
  ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
    r ∈ interpretFunction space dispatch atom opType b fuel

/-- Implementation-refined spec boundary for `interpretFunction`.
    The declarative side is uniform across all return-type instantiations. -/
def InterpretFunctionCertified
    (space : Space) (dispatch : GroundedDispatch)
    (atom opType : Atom) (b : Bindings) (r : ResultPair) : Prop :=
  (∀ retType, InterpretFunction space dispatch atom opType retType b r) ∧
  InterpretFunctionStablyReaches space dispatch atom opType b r

/-- Stable executable witness for `interpretArgs`. -/
def InterpretArgsStablyReaches
    (space : Space) (dispatch : GroundedDispatch)
    (args types : List Atom) (b : Bindings) (r : ResultPair) : Prop :=
  ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
    r ∈ interpretArgs space dispatch args types b fuel

/-- Implementation-refined spec boundary for `interpretArgs`. -/
def InterpretArgsCertified
    (space : Space) (dispatch : GroundedDispatch)
    (args types : List Atom) (b : Bindings) (r : ResultPair) : Prop :=
  InterpretArgs space dispatch args types b r ∧
  InterpretArgsStablyReaches space dispatch args types b r

/-- Stable executable witness for `interpretTuple`. -/
def InterpretTupleStablyReaches
    (space : Space) (dispatch : GroundedDispatch)
    (atom : Atom) (b : Bindings) (r : ResultPair) : Prop :=
  ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
    r ∈ interpretTuple space dispatch atom b fuel

/-- Implementation-refined spec boundary for `interpretTuple`. -/
def InterpretTupleCertified
    (space : Space) (dispatch : GroundedDispatch)
    (atom : Atom) (b : Bindings) (r : ResultPair) : Prop :=
  InterpretTuple space dispatch atom b r ∧
  InterpretTupleStablyReaches space dispatch atom b r

/-- Stable executable witness for `mettaCall`. -/
def MettaCallStablyReaches
    (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) : Prop :=
  ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
    r ∈ mettaCall space dispatch atom type_ b fuel

/-- Implementation-refined spec boundary for `mettaCall`. -/
def MettaCallCertified
    (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) : Prop :=
  MettaCall space dispatch atom type_ b r ∧
  MettaCallStablyReaches space dispatch atom type_ b r

end Internal

end Mettapedia.Languages.MeTTa.HE
