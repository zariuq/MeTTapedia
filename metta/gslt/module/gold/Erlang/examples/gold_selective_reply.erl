-module(gold_selective_reply).
-export([start/1, request/3, collect/1, server/1]).

start(Factor) -> spawn(fun() -> server(Factor) end).

request(Server, Correlation, Value) ->
    Server ! {request, self(), Correlation, Value},
    collect(Correlation).

collect(Correlation) ->
    receive {reply, Correlation, Value} -> Value end.

server(Factor) ->
    receive
        {request, From, Correlation, Value} when is_integer(Value) ->
            From ! {reply, Correlation, Value * Factor},
            server(Factor);
        {barrier, From, Correlation} ->
            From ! {barrier_reached, Correlation},
            server(Factor);
        stop -> done
    end.
