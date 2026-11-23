-module(core_sequential).
-export([run/0, factorial/1]).

factorial(0) -> 1;
factorial(N) when is_integer(N), N > 0 -> N * factorial(N - 1).

reverse([], Acc) -> Acc;
reverse([Head | Tail], Acc) -> reverse(Tail, [Head | Acc]).

append([], Right) -> Right;
append([Head | Tail], Right) -> [Head | append(Tail, Right)].

map(_, []) -> [];
map(Fun, [Head | Tail]) -> [Fun(Head) | map(Fun, Tail)].

run() ->
    Pair = {factorial(5), reverse([1, 2, 3], [])},
    case Pair of
        {N, Reversed} when is_integer(N) ->
            {N, Reversed, append([1, 2], [3]), map(fun (X) -> X + 1 end, [1, 2])}
    end.
