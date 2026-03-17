:- module(swi_fixture_runner, [main/0]).

:- use_module(library(json)).
:- use_module(library(lists)).
:- use_module(library(aggregate)).
:- use_module(swi_fixture_cases).

term_text(Term, Text) :-
    with_output_to(string(Text),
        write_term(Term, [quoted(true), numbervars(true)])).

run_goal_collect(Template, Goal, Actual) :-
    catch(findall(Template, Goal, Solutions),
        Error,
        Actual = error(Error)),
    ( var(Actual) -> Actual = solutions(Solutions) ; true ).

actual_matches_expected(solutions(Expected), solutions(Actual)) :-
    Expected == Actual.
actual_matches_expected(error(ExpectedPattern), error(ActualError)) :-
    subsumes_term(ExpectedPattern, ActualError).
actual_matches_expected(_, _) :-
    fail.

case_result(Suite, Id, Template, Goal, Expected, Dict) :-
    run_goal_collect(Template, Goal, Actual),
    ( actual_matches_expected(Expected, Actual) -> Status = pass ; Status = fail ),
    term_text(Goal, GoalText),
    term_text(Expected, ExpectedText),
    term_text(Actual, ActualText),
    Dict = _{
        suite: Suite,
        id: Id,
        status: Status,
        goal: GoalText,
        expected: ExpectedText,
        actual: ActualText
    }.

write_jsonl(Stream, Dict) :-
    json_write_dict(Stream, Dict, [width(0)]),
    nl(Stream).

collect_case_result(Dict) :-
    fixture_case(Suite, Id, Template, Goal, Expected),
    case_result(Suite, Id, Template, Goal, Expected, Dict).

run_all(OutputPath) :-
    findall(Dict, collect_case_result(Dict), Dicts),
    setup_call_cleanup(
        open(OutputPath, write, Stream),
        forall(member(D, Dicts), write_jsonl(Stream, D)),
        close(Stream)
    ),
    length(Dicts, Total),
    aggregate_all(count, (member(D, Dicts), D.status == pass), PassCount),
    FailCount is Total - PassCount,
    format("SWI fixture run complete.~n"),
    format("  output: ~w~n", [OutputPath]),
    format("  total:  ~d~n", [Total]),
    format("  pass:   ~d~n", [PassCount]),
    format("  fail:   ~d~n", [FailCount]),
    ( FailCount =:= 0 -> true ; fail ).

default_output_path(Path) :-
    get_time(Now),
    format_time(string(Stamp), "%Y%m%d_%H%M%S", Now),
    format(string(Path), "artifacts/prolog/swi_fixture_results_~w.jsonl", [Stamp]).

strip_dash_dash(['--'|Rest], Rest) :- !.
strip_dash_dash(Args, Args).

main :-
    current_prolog_flag(argv, RawArgv),
    strip_dash_dash(RawArgv, Argv),
    ( Argv = [OutPath|_] -> true ; default_output_path(OutPath) ),
    run_all(OutPath).

:- initialization(main, main).
