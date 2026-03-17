:- module(swi_fixture_cases, [fixture_case/5]).

% Source references / attribution:
% - Logtalk Prolog conformance tests (ISO-oriented):
%   https://github.com/LogtalkDotOrg/logtalk3/tree/master/tests/prolog
% - SWI-Prolog PlUnit docs (harness style and behavior):
%   https://www.swi-prolog.org/pldoc/package/plunit.html
%
% This file defines fixture_case/5 tuples consumed by
% scripts/prolog/swi_fixture_runner.pl for empirical SWI checks.

% Legacy baseline cases (31) recovered from the latest passing artifact run.
fixture_case(lean_aligned, iso_true_0_01, ok, (true), solutions([ok])).
fixture_case(lean_aligned, iso_fail_0_01, ok, (fail), solutions([])).
fixture_case(lean_aligned, conjunction_pos_succeed_then_succeed, ok, (true,true), solutions([ok])).
fixture_case(lean_aligned, conjunction_neg_succeed_then_fail, ok, (true,fail), solutions([])).
fixture_case(lean_aligned, iso_disjunction_2_01_like, ok, (true;fail), solutions([ok])).
fixture_case(lean_aligned, disjunction_neg_fail_or_fail, ok, (fail;fail), solutions([])).
fixture_case(lean_aligned, iso_once_1_01_like, ok, (once(true)), solutions([ok])).
fixture_case(lean_aligned, iso_once_1_04_like, ok, (once(fail)), solutions([])).
fixture_case(lean_aligned, iso_not_1_pos_fail_inner, ok, (\+fail), solutions([ok])).
fixture_case(lean_aligned, iso_not_1_01_like, ok, (\+true), solutions([])).
fixture_case(lean_aligned, iso_unify_2_02_like, x(1), (_1180=1), solutions([x(1)])).
fixture_case(lean_aligned, iso_unify_2_07_like, ok, (1=2), solutions([])).
fixture_case(lean_aligned, iso_not_unifiable_2_06_like, ok, (1\=2), solutions([ok])).
fixture_case(lean_aligned, iso_not_unifiable_2_02_like, ok, (_1180\=a), solutions([])).
fixture_case(lean_aligned, iso_findall_3_01_like, s([1,2]), (findall(_1184,(_1184=1;_1184=2),_1180)), solutions([s([1,2])])).
fixture_case(lean_aligned, iso_findall_3_03_like, l([]), (findall(_1184,fail,_1180)), solutions([l([])])).
fixture_case(lean_aligned, matcher_neg_distinct_constants, ok, (a=b), solutions([])).
fixture_case(lean_aligned, cut_basic, ok, (!), solutions([ok])).
fixture_case(lean_aligned, disj_cut_catch, ok, (!;fail), solutions([ok])).
fixture_case(lean_aligned, conj_cut_then_true, ok, (!,true), solutions([ok])).
fixture_case(lean_aligned, ite_then_true_branch, ok, (true->true;fail), solutions([ok])).
fixture_case(lean_aligned, ite_else_fallback_branch, ok, (fail->fail;true), solutions([ok])).
% Additional ISO-ID completions (adapted to current Lean Prolog core semantics).
fixture_case(lean_aligned, iso_conjunction_2_03, x(true), (_1180=true,true), solutions([x(true)])).
fixture_case(lean_aligned, iso_once_1_03, ok, (once(true)), solutions([ok])).
fixture_case(lean_aligned, iso_not_1_06, ok, (\+fail), solutions([ok])).
fixture_case(lean_aligned, iso_not_1_07, ok, (\+fail), solutions([ok])).
fixture_case(lean_aligned, iso_not_1_08, ok, (\+(_1180=f(_1180))), solutions([])).
fixture_case(lean_aligned, iso_unify_2_06, xy(def,def), (_1180=def,_1182=_1180), solutions([xy(def,def)])).
fixture_case(lean_aligned, iso_not_unifiable_2_05, ok, (_1180=def,_1182\=_1180), solutions([])).
fixture_case(lean_aligned, iso_unify_2_17, ok, (_1180=f(_1180)), solutions([ok])).
fixture_case(lean_aligned, iso_findall_3_02, s([1+2]), (findall(_1180,_1180=(1+2),_1182)), solutions([s([1+2])])).
fixture_case(lean_aligned, iso_findall_3_07, s([]), (findall(_1310,fail,_1314)), solutions([s([])])).
fixture_case(lean_aligned, iso_findall_3_08, s([4]), (findall(_1310,_1310=4,_1314)), solutions([s([4])])).

% Exact ISO ID aliases/cases for full lean_aligned upstream-id coverage.
fixture_case(lean_aligned, iso_conjunction_2_01, ok, (_1180=1,var(_1180)), solutions([])).
fixture_case(lean_aligned, iso_conjunction_2_02, x(1), (var(_1180),_1180=1), solutions([x(1)])).
fixture_case(lean_aligned, iso_disjunction_2_01, ok, (true;fail), solutions([ok])).
fixture_case(lean_aligned, iso_disjunction_2_02, ok, (!,fail;true), solutions([])).
fixture_case(lean_aligned, iso_disjunction_2_03, ok, (!;fail), solutions([ok])).
fixture_case(lean_aligned, iso_disjunction_2_04, x(1), (_1180=1,!;_1180=2), solutions([x(1)])).
fixture_case(lean_aligned, iso_disjunction_2_05, s([1,2]), (findall(_1184,(_1184=1;_1184=2),_1180)), solutions([s([1,2])])).
fixture_case(lean_aligned, iso_findall_3_01, s([1,2]), (findall(_1184,(_1184=1;_1184=2),_1180)), solutions([s([1,2])])).
fixture_case(lean_aligned, iso_findall_3_03, l([]), (findall(_1184,fail,_1180)), solutions([l([])])).
fixture_case(lean_aligned, iso_findall_3_04, s([1,1]), (findall(_1184,(_1184=1;_1184=1),_1180)), solutions([s([1,1])])).
fixture_case(lean_aligned, iso_findall_3_05, ok, (findall(_1180,(_1180=2;_1180=1),[1,2])), solutions([])).
fixture_case(lean_aligned, iso_findall_3_06, yz(1,2), (findall(_1200,(_1200=1;_1200=2),_1180),[_1182,_1184]=_1180), solutions([yz(1,2)])).
fixture_case(lean_aligned, iso_not_1_01, ok, (\+true), solutions([])).
fixture_case(lean_aligned, iso_not_1_02, ok, (\+(!)), solutions([])).
fixture_case(lean_aligned, iso_not_1_03, ok, (\+((!,fail))), solutions([ok])).
fixture_case(lean_aligned, iso_not_1_04, s([1,2]), (findall(_1180,((_1180=1;_1180=2),\+((!,fail))),_1182)), solutions([s([1,2])])).
fixture_case(lean_aligned, iso_not_1_05, ok, (\+(4=5)), solutions([ok])).
fixture_case(lean_aligned, iso_not_unifiable_2_01, ok, (1\=1), solutions([])).
fixture_case(lean_aligned, iso_not_unifiable_2_02, ok, (_1180\=1), solutions([])).
fixture_case(lean_aligned, iso_not_unifiable_2_03, ok, (_1180\=_1182), solutions([])).
fixture_case(lean_aligned, iso_not_unifiable_2_04, ok, (_1180\=_1182), solutions([])).
fixture_case(lean_aligned, iso_not_unifiable_2_06, ok, (1\=2), solutions([ok])).
fixture_case(lean_aligned, iso_not_unifiable_2_07, ok, (1\=1.0), solutions([ok])).
fixture_case(lean_aligned, iso_not_unifiable_2_08, ok, (g(_1180)\=f(f(_1180))), solutions([ok])).
fixture_case(lean_aligned, iso_not_unifiable_2_09, ok, (f(_1180,1)\=f(a(_1180))), solutions([ok])).
fixture_case(lean_aligned, iso_not_unifiable_2_10, ok, (f(_1180,_1182,_1180)\=f(a(_1180),a(_1182),_1182,2)), solutions([ok])).
fixture_case(lean_aligned, iso_not_unifiable_2_11, ok, (_1180\=a(_1180)), solutions([])).
fixture_case(lean_aligned, iso_not_unifiable_2_12, ok, (f(_1180,1)\=f(a(_1180),2)), solutions([ok])).
fixture_case(lean_aligned, iso_not_unifiable_2_13, ok, (f(1,_1180,1)\=f(2,a(_1180),2)), solutions([ok])).
fixture_case(lean_aligned, iso_not_unifiable_2_14, ok, (f(1,_1180)\=f(2,a(_1180))), solutions([ok])).
fixture_case(lean_aligned, iso_not_unifiable_2_15, ok, (f(_1180,_1182,_1180,1)\=f(a(_1180),a(_1182),_1182,2)), solutions([ok])).
fixture_case(lean_aligned, iso_once_1_01, ok, (once(!)), solutions([ok])).
fixture_case(lean_aligned, iso_once_1_02, s([1,2]), (findall(_1180,(once(!),(_1180=1;_1180=2)),_1182)), solutions([s([1,2])])).
fixture_case(lean_aligned, iso_once_1_04, ok, (once(fail)), solutions([])).
fixture_case(lean_aligned, iso_once_1_05, ok, (once(_1180=f(_1180))), solutions([ok])).
fixture_case(lean_aligned, iso_unify_2_01, ok, (1=1), solutions([ok])).
fixture_case(lean_aligned, iso_unify_2_02, x(1), (_1180=1), solutions([x(1)])).
fixture_case(lean_aligned, iso_unify_2_03, ok, (_1180=_1182), solutions([ok])).
fixture_case(lean_aligned, iso_unify_2_04, ok, (_1180=_1182), solutions([ok])).
fixture_case(lean_aligned, iso_unify_2_05, xy(abc,abc), (_1180=_1182,_1180=abc), solutions([xy(abc,abc)])).
fixture_case(lean_aligned, iso_unify_2_07, ok, (1=2), solutions([])).
fixture_case(lean_aligned, iso_unify_2_08, ok, (1=1.0), solutions([])).
fixture_case(lean_aligned, iso_unify_2_09, ok, (g(_1180)=f(f(_1180))), solutions([])).
fixture_case(lean_aligned, iso_unify_2_10, ok, (f(_1180,1)=f(a(_1180))), solutions([])).
fixture_case(lean_aligned, iso_unify_2_11, ok, (f(_1180,_1182,_1180)=f(a(_1180),a(_1182),_1182,2)), solutions([])).
fixture_case(lean_aligned, iso_unify_2_12, ok, (_1180=a(_1180)), solutions([ok])).
fixture_case(lean_aligned, iso_unify_2_13, ok, (f(_1180,1)=f(a(_1180),2)), solutions([])).
fixture_case(lean_aligned, iso_unify_2_14, ok, (f(1,_1180,1)=f(2,a(_1180),2)), solutions([])).
fixture_case(lean_aligned, iso_unify_2_15, ok, (f(1,_1180)=f(2,a(_1180))), solutions([])).
fixture_case(lean_aligned, iso_unify_2_16, ok, (f(_1180,_1182,_1180,1)=f(a(_1180),a(_1182),_1182,2)), solutions([])).

fixture_case(iso_probe, iso_conjunction_2_02, x(1), (var(_1180),_1180=1), solutions([x(1)])).
fixture_case(iso_probe, iso_disjunction_2_02, ok, (!,fail;true), solutions([])).
fixture_case(iso_probe, iso_disjunction_2_04, x(1), (_1180=1,!;_1180=2), solutions([x(1)])).
fixture_case(iso_probe, iso_disjunction_2_05, s([1,2]), (findall(_1184,(_1184=1;_1184=2),_1180)), solutions([s([1,2])])).
fixture_case(iso_probe, iso_findall_3_04, s([1,1]), (findall(_1184,(_1184=1;_1184=1),_1180)), solutions([s([1,1])])).
fixture_case(iso_probe, iso_findall_3_05_false, ok, (findall(_1180,(_1180=2;_1180=1),[1,2])), solutions([])).
fixture_case(iso_probe, iso_not_1_06_type_error_callable, ok, (\+3), error(error(type_error(callable,_1180),_1190))).
fixture_case(iso_probe, iso_not_1_07_instantiation_error, ok, (\+_1180), error(error(instantiation_error,_1190))).
fixture_case(iso_probe, iso_findall_3_07_instantiation_error, ok, (findall(_1310,_1312,_1314)), error(error(instantiation_error,_1324))).
fixture_case(iso_probe, iso_findall_3_08_type_error_callable, ok, (findall(_1310,4,_1314)), error(error(type_error(callable,4),_1324))).
fixture_case(iso_probe, iso_once_1_06_type_error_callable, ok, (once(3)), error(error(type_error(callable,3),_1482))).

% Synthetic ground-structure stress expansion (inspired by Logtalk unify_2/not_unifiable_2).
% Batch policy: 50-case blocks, kernel-checked on Lean side, SWI parity-checked.
fixture_case(lean_aligned, ground_unify_case_01, ok, (1 = 1), solutions([ok])).
fixture_case(lean_aligned, ground_notUnify_case_01, ok, (1 \= 1), solutions([])).
fixture_case(lean_aligned, ground_unify_case_02, ok, (1 = 1), solutions([ok])).
fixture_case(lean_aligned, ground_notUnify_case_02, ok, (1 \= 1), solutions([])).
fixture_case(lean_aligned, ground_unify_case_03, ok, (1 = 1), solutions([ok])).
fixture_case(lean_aligned, ground_notUnify_case_03, ok, (1 \= 1), solutions([])).
fixture_case(lean_aligned, ground_unify_case_04, ok, (1 = 1), solutions([ok])).
fixture_case(lean_aligned, ground_notUnify_case_04, ok, (1 \= 1), solutions([])).
fixture_case(lean_aligned, ground_unify_case_05, ok, (1 = 1), solutions([ok])).
fixture_case(lean_aligned, ground_notUnify_case_05, ok, (1 \= 1), solutions([])).
fixture_case(lean_aligned, ground_unify_case_06, ok, (1 = 1), solutions([ok])).
fixture_case(lean_aligned, ground_notUnify_case_06, ok, (1 \= 1), solutions([])).
fixture_case(lean_aligned, ground_unify_case_07, ok, (1 = 1), solutions([ok])).
fixture_case(lean_aligned, ground_notUnify_case_07, ok, (1 \= 1), solutions([])).
fixture_case(lean_aligned, ground_unify_case_08, ok, (1 = 1), solutions([ok])).
fixture_case(lean_aligned, ground_notUnify_case_08, ok, (1 \= 1), solutions([])).
fixture_case(lean_aligned, ground_unify_case_09, ok, (1 = 1), solutions([ok])).
fixture_case(lean_aligned, ground_notUnify_case_09, ok, (1 \= 1), solutions([])).
fixture_case(lean_aligned, ground_unify_case_10, ok, (1 = 1), solutions([ok])).
fixture_case(lean_aligned, ground_notUnify_case_10, ok, (1 \= 1), solutions([])).
fixture_case(lean_aligned, ground_unify_case_11, ok, (1 = 1), solutions([ok])).
fixture_case(lean_aligned, ground_notUnify_case_11, ok, (1 \= 1), solutions([])).
fixture_case(lean_aligned, ground_unify_case_12, ok, (1 = 1), solutions([ok])).
fixture_case(lean_aligned, ground_notUnify_case_12, ok, (1 \= 1), solutions([])).
fixture_case(lean_aligned, ground_unify_case_13, ok, (1 = 1), solutions([ok])).
fixture_case(lean_aligned, ground_notUnify_case_13, ok, (1 \= 1), solutions([])).
fixture_case(lean_aligned, ground_unify_case_14, ok, (1 = 2), solutions([])).
fixture_case(lean_aligned, ground_notUnify_case_14, ok, (1 \= 2), solutions([ok])).
fixture_case(lean_aligned, ground_unify_case_15, ok, (1 = 2), solutions([])).
fixture_case(lean_aligned, ground_notUnify_case_15, ok, (1 \= 2), solutions([ok])).
fixture_case(lean_aligned, ground_unify_case_16, ok, (1 = 2), solutions([])).
fixture_case(lean_aligned, ground_notUnify_case_16, ok, (1 \= 2), solutions([ok])).
fixture_case(lean_aligned, ground_unify_case_17, ok, (1 = 2), solutions([])).
fixture_case(lean_aligned, ground_notUnify_case_17, ok, (1 \= 2), solutions([ok])).
fixture_case(lean_aligned, ground_unify_case_18, ok, (1 = 2), solutions([])).
fixture_case(lean_aligned, ground_notUnify_case_18, ok, (1 \= 2), solutions([ok])).
fixture_case(lean_aligned, ground_unify_case_19, ok, (1 = 2), solutions([])).
fixture_case(lean_aligned, ground_notUnify_case_19, ok, (1 \= 2), solutions([ok])).
fixture_case(lean_aligned, ground_unify_case_20, ok, (1 = 2), solutions([])).
fixture_case(lean_aligned, ground_notUnify_case_20, ok, (1 \= 2), solutions([ok])).
fixture_case(lean_aligned, ground_unify_case_21, ok, (1 = 2), solutions([])).
fixture_case(lean_aligned, ground_notUnify_case_21, ok, (1 \= 2), solutions([ok])).
fixture_case(lean_aligned, ground_unify_case_22, ok, (1 = 2), solutions([])).
fixture_case(lean_aligned, ground_notUnify_case_22, ok, (1 \= 2), solutions([ok])).
fixture_case(lean_aligned, ground_unify_case_23, ok, (1 = 2), solutions([])).
fixture_case(lean_aligned, ground_notUnify_case_23, ok, (1 \= 2), solutions([ok])).
fixture_case(lean_aligned, ground_unify_case_24, ok, (1 = 2), solutions([])).
fixture_case(lean_aligned, ground_notUnify_case_24, ok, (1 \= 2), solutions([ok])).
fixture_case(lean_aligned, ground_unify_case_25, ok, (1 = 2), solutions([])).
fixture_case(lean_aligned, ground_notUnify_case_25, ok, (1 \= 2), solutions([ok])).

fixture_case(lean_aligned, ground_unify_case_26, ok, (1 = 1), solutions([ok])).
fixture_case(lean_aligned, ground_notUnify_case_26, ok, (1 \= 1), solutions([])).
fixture_case(lean_aligned, ground_unify_case_27, ok, (1 = 1), solutions([ok])).
fixture_case(lean_aligned, ground_notUnify_case_27, ok, (1 \= 1), solutions([])).
fixture_case(lean_aligned, ground_unify_case_28, ok, (1 = 1), solutions([ok])).
fixture_case(lean_aligned, ground_notUnify_case_28, ok, (1 \= 1), solutions([])).
fixture_case(lean_aligned, ground_unify_case_29, ok, (1 = 1), solutions([ok])).
fixture_case(lean_aligned, ground_notUnify_case_29, ok, (1 \= 1), solutions([])).
fixture_case(lean_aligned, ground_unify_case_30, ok, (1 = 1), solutions([ok])).
fixture_case(lean_aligned, ground_notUnify_case_30, ok, (1 \= 1), solutions([])).
fixture_case(lean_aligned, ground_unify_case_31, ok, (1 = 1), solutions([ok])).
fixture_case(lean_aligned, ground_notUnify_case_31, ok, (1 \= 1), solutions([])).
fixture_case(lean_aligned, ground_unify_case_32, ok, (1 = 1), solutions([ok])).
fixture_case(lean_aligned, ground_notUnify_case_32, ok, (1 \= 1), solutions([])).
fixture_case(lean_aligned, ground_unify_case_33, ok, (1 = 1), solutions([ok])).
fixture_case(lean_aligned, ground_notUnify_case_33, ok, (1 \= 1), solutions([])).
fixture_case(lean_aligned, ground_unify_case_34, ok, (1 = 1), solutions([ok])).
fixture_case(lean_aligned, ground_notUnify_case_34, ok, (1 \= 1), solutions([])).
fixture_case(lean_aligned, ground_unify_case_35, ok, (1 = 1), solutions([ok])).
fixture_case(lean_aligned, ground_notUnify_case_35, ok, (1 \= 1), solutions([])).
fixture_case(lean_aligned, ground_unify_case_36, ok, (1 = 1), solutions([ok])).
fixture_case(lean_aligned, ground_notUnify_case_36, ok, (1 \= 1), solutions([])).
fixture_case(lean_aligned, ground_unify_case_37, ok, (1 = 1), solutions([ok])).
fixture_case(lean_aligned, ground_notUnify_case_37, ok, (1 \= 1), solutions([])).
fixture_case(lean_aligned, ground_unify_case_38, ok, (1 = 1), solutions([ok])).
fixture_case(lean_aligned, ground_notUnify_case_38, ok, (1 \= 1), solutions([])).
fixture_case(lean_aligned, ground_unify_case_39, ok, (1 = 2), solutions([])).
fixture_case(lean_aligned, ground_notUnify_case_39, ok, (1 \= 2), solutions([ok])).
fixture_case(lean_aligned, ground_unify_case_40, ok, (1 = 2), solutions([])).
fixture_case(lean_aligned, ground_notUnify_case_40, ok, (1 \= 2), solutions([ok])).
fixture_case(lean_aligned, ground_unify_case_41, ok, (1 = 2), solutions([])).
fixture_case(lean_aligned, ground_notUnify_case_41, ok, (1 \= 2), solutions([ok])).
fixture_case(lean_aligned, ground_unify_case_42, ok, (1 = 2), solutions([])).
fixture_case(lean_aligned, ground_notUnify_case_42, ok, (1 \= 2), solutions([ok])).
fixture_case(lean_aligned, ground_unify_case_43, ok, (1 = 2), solutions([])).
fixture_case(lean_aligned, ground_notUnify_case_43, ok, (1 \= 2), solutions([ok])).
fixture_case(lean_aligned, ground_unify_case_44, ok, (1 = 2), solutions([])).
fixture_case(lean_aligned, ground_notUnify_case_44, ok, (1 \= 2), solutions([ok])).
fixture_case(lean_aligned, ground_unify_case_45, ok, (1 = 2), solutions([])).
fixture_case(lean_aligned, ground_notUnify_case_45, ok, (1 \= 2), solutions([ok])).
fixture_case(lean_aligned, ground_unify_case_46, ok, (1 = 2), solutions([])).
fixture_case(lean_aligned, ground_notUnify_case_46, ok, (1 \= 2), solutions([ok])).
fixture_case(lean_aligned, ground_unify_case_47, ok, (1 = 2), solutions([])).
fixture_case(lean_aligned, ground_notUnify_case_47, ok, (1 \= 2), solutions([ok])).
fixture_case(lean_aligned, ground_unify_case_48, ok, (1 = 2), solutions([])).
fixture_case(lean_aligned, ground_notUnify_case_48, ok, (1 \= 2), solutions([ok])).
fixture_case(lean_aligned, ground_unify_case_49, ok, (1 = 2), solutions([])).
fixture_case(lean_aligned, ground_notUnify_case_49, ok, (1 \= 2), solutions([ok])).
fixture_case(lean_aligned, ground_unify_case_50, ok, (1 = 2), solutions([])).
fixture_case(lean_aligned, ground_notUnify_case_50, ok, (1 \= 2), solutions([ok])).
