-module(core_pingpong).
-export([run/0]).

worker() -> receive {ping, From} -> From ! pong, worker() end.
exchange(0, _) -> done;
exchange(N, Pid) -> Pid ! {ping, self()}, receive pong -> exchange(N - 1, Pid) end.
run() -> Worker = spawn(fun () -> worker() end), exchange(3, Worker).
