-module(core_parallel_map).
-export([run/0]).

start([], _) -> [];
start([X | Xs], Parent) ->
    Pid = spawn(fun () -> Parent ! {self(), X * X} end),
    [Pid | start(Xs, Parent)].
collect([]) -> [];
collect([Pid | Pids]) -> receive {Pid, Value} -> [Value | collect(Pids)] end.
run() -> collect(start([3, 1, 2], self())).
