-module(mailbox_operations).
-export([run/0]).

take() -> receive Message -> Message end.

first() ->
    self() ! a, self() ! b,
    {take(), take()}.

prefix() ->
    self() ! a, self() ! b, self() ! c,
    Selected = receive b -> b end,
    {Selected, [take(), take()]}.

duplicates() ->
    self() ! a, self() ! a,
    Selected = receive a -> a end,
    {Selected, take()}.

guard() ->
    self() ! {n, 0}, self() ! {n, 2}, self() ! noise,
    Selected = receive {n, N} when N > 0 -> N end,
    {Selected, [take(), take()]}.

wake() ->
    Parent = self(),
    spawn(fun () -> Parent ! b, Parent ! a end),
    First = receive a -> a end,
    {First, take()}.

run() -> {first(), prefix(), duplicates(), guard(), wake()}.
