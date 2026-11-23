:- module(gold_resource_scheduler, [ready/2, request/1, token/1, receipt/2, reported/2]).
:- use_module(library(chr)).
:- chr_constraint ready/2, request/1, token/1, receipt/2, reported/2.

% Prefer the primary resource when an active request can use either pool.
primary @ ready(Job, Flag) \ request(Job), token(worker)
    <=> Flag == yes | receipt(Job, primary).
backup @ ready(Job, Flag) \ request(Job), token(backup)
    <=> Flag == yes | receipt(Job, backup).

% Each receipt occurrence publishes once, including equal new receipts.
publish @ receipt(Job, Pool) ==> reported(Job, Pool).
