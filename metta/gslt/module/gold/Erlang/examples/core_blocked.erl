-module(core_blocked).
-export([run/0]).

run() -> receive missing -> done end.
