-module(core_counter).
-export([run/0]).

server(N) ->
    receive
        {inc} -> server(N + 1);
        {get, From} -> From ! {count, N}, server(N)
    end.
run() ->
    Pid = spawn(fun () -> server(0) end),
    Pid ! {inc}, Pid ! {inc}, Pid ! {get, self()},
    receive {count, N} -> N end.
