-module(core_sender_order).
-export([run/0]).

second(Parent) -> receive go -> Parent ! b end.
first(Parent, Other) -> Parent ! a1, Parent ! a2, Other ! go.
run() ->
    Parent = self(),
    Other = spawn(fun () -> second(Parent) end),
    spawn(fun () -> first(Parent, Other) end),
    receive X -> receive Y -> receive Z -> [X, Y, Z] end end end.
