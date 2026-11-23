-module(actor_operations).
-export([run/1, selective/1, ping_pong/1]).

run(spawn_send) ->
    Parent = self(),
    spawn(fun() -> Parent ! 42 end),
    receive 42 -> 42 end;
run(self_selective) -> selective(false);
run(ping_pong) -> ping_pong(2);
run(parallel_map) -> parallel_map([2, 3]);
run(parallel_map_duplicates) -> parallel_map([2, 2]);
run(two_senders) ->
    Parent = self(),
    Second = spawn(fun() -> receive go -> Parent ! b end end),
    spawn(fun() -> Parent ! a, Second ! go end),
    FirstMessage = receive X -> X end,
    SecondMessage = receive Y -> Y end,
    {FirstMessage, SecondMessage};
run(counter) ->
    Server = spawn(fun() -> counter(0) end),
    Server ! {inc},
    Server ! {inc},
    Server ! {get, self()},
    receive
        {value, Count} when is_integer(Count) -> Server ! stop, Count
    end.

selective(Flag) ->
    self() ! b,
    self() ! a,
    self() ! b,
    First = receive a -> a; b when Flag -> wrong end,
    Second = receive b -> b end,
    {First, Second}.

ping_pong(Rounds) ->
    Server = spawn(fun pong/0),
    ping(Server, Rounds).

ping(Server, 0) -> Server ! stop, done;
ping(Server, Rounds) ->
    Server ! {ping, self()},
    receive {pong, From} when From =:= Server -> ping(Server, Rounds - 1) end.

pong() ->
    receive
        {ping, From} -> From ! {pong, self()}, pong();
        stop -> done
    end.

counter(Count) ->
    receive
        {inc} -> counter(Count + 1);
        {get, From} -> From ! {value, Count}, counter(Count);
        stop -> done
    end.

parallel_map(Jobs) -> collect(spawn_workers(Jobs, self())).

spawn_workers([], _) -> [];
spawn_workers([Job | Rest], Parent) ->
    [spawn(fun() -> Parent ! {self(), Job * 2} end) | spawn_workers(Rest, Parent)].

collect([]) -> [];
collect([Pid | Rest]) ->
    Result = receive {From, Value} when From =:= Pid -> Value end,
    [Result | collect(Rest)].
