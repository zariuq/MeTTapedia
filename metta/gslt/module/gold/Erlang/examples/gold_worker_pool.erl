-module(gold_worker_pool).
-export([run/3, start/3, worker/2]).

run(Count, Factor, Tasks) when Count > 0 ->
    Workers = start(Count, Factor, self()),
    dispatch(Tasks, Workers, Workers, 0),
    Results = collect(length_of(Tasks), []),
    stop(Workers),
    await_stops(Count),
    Results.

start(0, _, _) -> [];
start(Count, Factor, Owner) when Count > 0 ->
    Worker = spawn(fun() -> worker(Factor, Owner) end),
    [Worker | start(Count - 1, Factor, Owner)].

worker(Factor, Owner) ->
    receive
        {run, Index, Task, Value} when is_integer(Value) ->
            Owner ! {done, Index, Task, Value * Factor},
            worker(Factor, Owner);
        stop ->
            Owner ! {stopped, self()}
    end.

dispatch([], _, _, _) -> done;
dispatch(Tasks, [], All, Index) -> dispatch(Tasks, All, All, Index);
dispatch([{Task, Value} | Tasks], [Worker | Rest], All, Index) ->
    Worker ! {run, Index, Task, Value},
    dispatch(Tasks, Rest, All, Index + 1).

collect(0, Results) -> Results;
collect(Count, Results) ->
    receive
        {done, Index, Task, Value} ->
            collect(Count - 1, insert({Index, Task, Value}, Results))
    end.

insert(Result, []) -> [Result];
insert({Index, Task, Value}, [{Next, _, _} = Head | Tail]) when Index < Next ->
    [{Index, Task, Value}, Head | Tail];
insert(Result, [Head | Tail]) -> [Head | insert(Result, Tail)].

length_of([]) -> 0;
length_of([_ | Rest]) -> 1 + length_of(Rest).

stop([]) -> done;
stop([Worker | Rest]) -> Worker ! stop, stop(Rest).

await_stops(0) -> done;
await_stops(Count) ->
    receive {stopped, _} -> await_stops(Count - 1) end.
