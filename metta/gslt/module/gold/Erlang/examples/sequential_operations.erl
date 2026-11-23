-module(sequential_operations).
-export([run_case/1]).

captured() ->
    X = 10,
    F = fun (Y) -> X + Y end,
    shadow(F, 99).

shadow(F, _) -> F(5).

fallback(Outer, Value) ->
    case Value of
        N when N < 0 -> N;
        _ -> Outer
    end.

faulty_guard(Outer, Value, Divisor) ->
    case Value of
        N when N div Divisor > 0 -> N;
        _ -> Outer
    end.

nonboolean_guard(Outer, Value) ->
    case Value of
        N when N -> N;
        _ -> Outer
    end.

body_fault(Value, Divisor) ->
    case Value of
        N when is_integer(N) -> N div Divisor;
        _ -> 42
    end.

priority(Value) ->
    case Value of
        {tag, N} -> N;
        _ -> 99
    end.

pinned(Expected, Value) ->
    case Value of
        Expected -> equal;
        _ -> different
    end.

alias_case(Whole = [Head | Tail]) -> {Whole, Head, Tail}.
call_zero(Fun) -> Fun().

run_case('standard-sequential') -> core_sequential:run();
run_case('lexical-capture') -> captured();
run_case('failed-guard-no-binding-leak') -> fallback(7, 9);
run_case('faulty-guard-falls-through') -> faulty_guard(7, 9, 0);
run_case('nonboolean-guard-falls-through') -> nonboolean_guard(7, 9);
run_case('body-fault-does-not-fall-through') -> body_fault(9, 0);
run_case('pattern-priority') -> priority({tag, 3});
run_case('pinned-positive') -> pinned(2, 2);
run_case('pinned-negative') -> pinned(2, 3);
run_case('alias-pattern') -> alias_case([4, 5]);
run_case('multiple-return-values') -> core_multiple_values:run();
run_case('unbounded-integers') ->
    A = 1267650600228229401496703205376,
    {A + 5, A * 3};
run_case('signed-quotient-remainder') -> {-7 div 3, -7 rem 3};
run_case('erlang-data-order') -> {1 < a, {} < {-100}, [] < [0], a < b};
run_case('uncurried-function-arity') ->
    F = fun (_, B) -> B end,
    {is_function(F, 2), is_function(F, 1)};
run_case('nonfunction-fault') -> call_zero(3).
