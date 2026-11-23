-module(core_function_message).
-export([run/0]).

run() ->
    Self = self(),
    Self ! fun(X) -> {Self, X + 1} end,
    receive
        F ->
            {Pid, Value} = F(41),
            Self = Pid,
            Value
    end.
