-module(channel_operations).
-export([run/0]).

send_all(_, []) -> ok;
send_all(Pid, [Head | Tail]) -> Pid ! Head, send_all(Pid, Tail).

read_like([]) -> [];
read_like([_ | Tail]) -> receive Head -> [Head | read_like(Tail)] end.

queue(Values) -> send_all(self(), Values), read_like(Values).

head_and_tail([_ | Tail] = Values) ->
    send_all(self(), Values),
    receive Head -> {Head, read_like(Tail)} end.

retained_prefix() ->
    send_all(self(), [first, second, old, earlier, new]),
    receive new -> {new, read_like([1, 2, 3, 4])} end.

run() ->
    {queue([a]), queue([a, b, c]), queue([a, a, a]),
     head_and_tail([a, b]), head_and_tail([a, a]), retained_prefix()}.
