:- module(gold_chr_ground_core, [main/0]).
:- use_module(library(chr)).
:- use_module(library(http/json)).
:- chr_constraint gcd/1, candidate/1, prime/1, minimum/1, upto/1, fib/2,
                  path/2, signal/1, published/1, tag/2, removed/2, token/1, taken/1,
                  enabled/1, request/1, worker/0, receipt/1, source/1, pair/2, blocked/1, released/1,
                  gate/0, item/1, chosen/1, pair_gate/0, pair_item/1, chosen_pair/2,
                  guard_gate/0, guard_item/1, guard_chosen/1.
:- chr_option(optimize,off).

gcd_zero @ gcd(0) <=> true.
gcd_reduce @ gcd(N) \ gcd(M) <=> N =< M | L is M mod N, gcd(L).

sieve_end @ candidate(1) <=> true.
sieve_next @ candidate(N) <=> prime(N), M is N-1, candidate(M).
sieve_remove @ prime(Y) \ prime(X) <=> 0 =:= X mod Y | true.

minimum_remove @ minimum(X) \ minimum(Y) <=> X =< Y | true.

fib_duplicate @ fib(N,V) \ fib(N,V) <=> true.
fib_next @ upto(Max), fib(N,A), fib(N1,B)
    ==> N1 =:= N+1, N1 < Max | N2 is N1+1, C is A+B, fib(N2,C).

path_duplicate @ path(X,Y) \ path(X,Y) <=> true.
path_transitive @ path(X,Y), path(Y,Z) ==> path(X,Z).

publish @ signal(X) ==> published(X).
publish_pair @ source(X), source(Y) ==> pair(X,Y).
duplicate_order @ tag(X,K) \ tag(X,R) <=> removed(K,R).
take_pair @ token(X), token(X) <=> taken(X).
allocate @ enabled(yes) \ request(Job), worker <=> receipt(Job).
release @ blocked(X) <=> X < 0 | released(X).
pick @ gate, item(X) <=> chosen(X).
pick_pair @ pair_gate, pair_item(X), pair_item(Y) <=> chosen_pair(X,Y).
guarded_pick @ guard_gate, guard_item(X) <=> X > 1 | guard_chosen(X).

control(gcd, (gcd(84),gcd(30),gcd(18)), [gcd(6)]).
control(sieve, candidate(10), [prime(2),prime(3),prime(5),prime(7)]).
control(minimum_duplicates, (minimum(4),minimum(2),minimum(2),minimum(9)), [minimum(2)]).
control(fibonacci, (upto(6),fib(0,0),fib(1,1)),
        [upto(6),fib(0,0),fib(1,1),fib(2,1),fib(3,2),fib(4,3),fib(5,5),fib(6,8)]).
control(cyclic_paths, (path(a,b),path(b,c),path(c,a)),
        [path(a,a),path(a,b),path(a,c),path(b,a),path(b,b),path(b,c),path(c,a),path(c,b),path(c,c)]).
control(empty, true, []).
control(propagation_occurrences, (signal(7),signal(7)), [signal(7),signal(7),published(7),published(7)]).
control(ordered_propagation_heads, (source(7),source(7)), [source(7),source(7),pair(7,7),pair(7,7)]).
control(propagation_needs_two, source(7), [source(7)]).
control(removed_head_first, (tag(1,old),tag(1,new)), [tag(1,old),removed(old,new)]).
control(two_resources, (token(worker),token(worker)), [taken(worker)]).
control(one_resource, token(worker), [token(worker)]).
control(disabled_head, (enabled(no),request(job),worker), [enabled(no),request(job),worker]).
control(allocation, (enabled(yes),request(job),worker), [enabled(yes),receipt(job)]).
control(guard_false, blocked(0), [blocked(0)]).
control(guard_true, blocked(-1), [released(-1)]).
control(partner_choice, (item(2),item(1),gate), [item(2),chosen(1)]).
control(partner_choice_wide, (numlist(0,19,Numbers),maplist(item,Numbers),gate), Expected) :-
    findall(item(N),between(0,18,N),Items),append(Items,[chosen(19)],Expected).
control(partner_pair, (pair_item(1),pair_item(2),pair_item(3),pair_gate), [pair_item(1),chosen_pair(3,2)]).
control(guarded_partner, (guard_item(3),guard_item(1),guard_gate), [guard_item(1),guard_chosen(3)]).

main :-
    current_prolog_flag(argv, [Label]),
    control(Label, Goal, Expected),
    call(Goal),
    findall(Constraint, find_chr_constraint(Constraint), Raw),
    msort(Raw, Actual),
    msort(Expected, SortedExpected),
    ( Actual == SortedExpected -> Passed = true ; Passed = false ),
    with_output_to(string(Store), write_canonical(Actual)),
    json_write_dict(current_output, _{control:Label, passed:Passed, store:Store}), nl,
    ( Passed == true -> halt(0) ; halt(1) ).

:- initialization(main, main).
