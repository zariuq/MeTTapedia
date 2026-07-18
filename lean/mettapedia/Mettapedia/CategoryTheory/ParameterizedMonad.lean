/-!
# Parameterized monads

An Atkey-style parameterized monad indexes computations by a pre-state and a
post-state.  Unit leaves the index unchanged, and bind is defined only when
the post-state of the first computation matches the pre-state of the second.

This interface records the three parameterized monad laws without imposing an
ordinary endofunctor or collapsing the two state indices.
-/

namespace Mettapedia.Effects

universe u v

/-- An Atkey-style parameterized monad over a type of state indices. -/
structure ParameterizedMonad (Index : Type u)
    (Carrier : Index → Index → Type v → Type (max u v)) where
  pure : {Result : Type v} →
    (state : Index) → Result → Carrier state state Result
  bind : {Result NextResult : Type v} →
    {source middle target : Index} →
    Carrier source middle Result →
    (Result → Carrier middle target NextResult) →
    Carrier source target NextResult
  pure_bind : ∀ {Result NextResult : Type v}
    {source target : Index} (result : Result)
    (next : Result → Carrier source target NextResult),
    bind (pure source result) next = next result
  bind_pure : ∀ {Result : Type v} {source target : Index}
    (execution : Carrier source target Result),
    bind execution (pure target) = execution
  bind_assoc : ∀ {Result NextResult FinalResult : Type v}
    {firstState secondState thirdState fourthState : Index}
    (first : Carrier firstState secondState Result)
    (second : Result → Carrier secondState thirdState NextResult)
    (third : NextResult → Carrier thirdState fourthState FinalResult),
    bind (bind first second) third =
      bind first (fun result => bind (second result) third)

end Mettapedia.Effects
