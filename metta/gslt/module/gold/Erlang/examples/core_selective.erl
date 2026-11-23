-module(core_selective).
-export([run/0]).

run() ->
    self() ! b,
    self() ! a,
    First = receive a -> a end,
    Second = receive b -> b end,
    {First, Second}.
