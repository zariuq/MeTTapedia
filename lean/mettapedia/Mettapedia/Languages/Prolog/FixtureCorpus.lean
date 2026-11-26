import Mettapedia.Languages.Prolog.FixtureTransport
import Mettapedia.Logic.Prolog.FixtureCorpus

/-!
# Prolog fixtures checked in the language interpreter

The Logic corpus supplies the declared test cases. Each named theorem
replays through the transport of evaluation derivations into this
interpreter, preserving the ordered answers and the cut status.
-/

namespace Mettapedia.Languages.Prolog
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match

namespace FixtureCorpus

def one : Pattern := .apply "1" []

def two : Pattern := .apply "2" []

def oneFloat : Pattern := .apply "1.0" []

def three : Pattern := .apply "3" []

def four : Pattern := .apply "4" []

def five : Pattern := .apply "5" []

def aConst : Pattern := .apply "a" []

def bConst : Pattern := .apply "b" []

def abcConst : Pattern := .apply "abc" []

def defConst : Pattern := .apply "def" []

def oracleSpaceConst (outs : List Pattern) : EvalOracle where
  space := { matchFacts := fun _ => [] }
  call := fun _ _ => False
  matchEval := fun _ _ outs' => outs' = outs

def oracleCallConst (expectedArgs outs : List Pattern) : EvalOracle where
  space := { matchFacts := fun _ => [] }
  call := fun args outs' => args = expectedArgs ∧ outs' = outs
  matchEval := fun _ _ _ => False

transport_prolog_fixtures [
  iso_true_0_01, iso_fail_0_01, conjunction_pos_succeed_then_succeed,
  conjunction_neg_succeed_then_fail, iso_conjunction_2_01, iso_disjunction_2_01_like,
  iso_disjunction_2_01, disjunction_neg_fail_or_fail, iso_once_1_01_like, iso_once_1_04_like,
  iso_once_1_04, iso_once_1_05, iso_not_1_pos_fail_inner, iso_not_1_01_like, iso_not_1_01,
  iso_not_1_02, iso_not_1_03, iso_conjunction_2_02, iso_unify_2_02_like, iso_unify_2_02,
  iso_unify_2_07_like, iso_unify_2_07, iso_unify_2_01_like, iso_unify_2_01, iso_unify_2_03,
  iso_unify_2_04, iso_unify_2_05, iso_unify_2_08, iso_unify_2_09, iso_unify_2_10, iso_unify_2_11,
  iso_unify_2_12, iso_unify_2_13, iso_unify_2_14, iso_unify_2_15, iso_unify_2_16,
  iso_not_unifiable_2_06_like, iso_not_unifiable_2_06, iso_not_unifiable_2_02_like,
  iso_not_unifiable_2_02, iso_not_unifiable_2_01, iso_not_unifiable_2_03, iso_not_unifiable_2_04,
  iso_not_unifiable_2_07, iso_not_unifiable_2_08, iso_not_unifiable_2_09, iso_not_unifiable_2_10,
  iso_not_unifiable_2_11, iso_not_unifiable_2_12, iso_not_unifiable_2_13, iso_not_unifiable_2_14,
  iso_not_unifiable_2_15, unify_prebound_conflict_fail, unify_prebound_consistent_succeed,
  unify_prebound_chain_consistent_three, unify_prebound_chain_conflict_late,
  unify_prebound_crossvar_consistent, unify_prebound_crossvar_conflict,
  notUnify_prebound_conflict_succeeds, notUnify_prebound_consistent_fails,
  unify_prebound_disj_then_filter_success, unify_prebound_disj_then_filter_fail,
  unify_prebound_xyz_bind_all, unify_prebound_xyz_consistent_final,
  unify_prebound_xyz_conflict_final, notUnify_prebound_xyz_success, notUnify_prebound_xyz_fail,
  unify_prebound_xyz_after_disj_filter_success, iso_findall_3_01_like, iso_findall_3_01,
  iso_findall_3_03_like, iso_findall_3_03, iso_findall_3_04_like, iso_disjunction_2_05_like,
  iso_disjunction_2_05, iso_findall_3_04, iso_findall_3_05_order_like, iso_once_1_01_cut_like,
  iso_once_1_01, iso_not_1_05_like, iso_not_1_05, matcher_neg_distinct_constants, cut_basic,
  disj_cut_catch, disj_g2_cut_simple, disj_g2_cut_with_prefix, conj_cut_then_true,
  ite_then_true_branch, ite_else_fallback_branch, spaceMatch_two_outs, spaceMatch_empty,
  reduceCall_two_outs, reduceCall_empty, iso_disjunction_2_02_like, iso_disjunction_2_02,
  iso_disjunction_2_04_like, iso_disjunction_2_04, conj_g2_cut_simple, conj_g2_cut_prunes_suffix,
  conj_g1_cut_g2_cut_simple, boundary_disj_cut_then_conj_true, boundary_disjunction_order_1_then_2,
  boundary_disjunction_fail_then_2, boundary_nested_disj_cut_prunes_third_in_findall,
  once_disj_first_answer, once_disj_first_fail_second_answer, neg_disj_fail_fail_succeeds,
  neg_disj_fail_true_fails, findall_once_disj_single, findall_cut_fail_empty,
  findall_cut_commit_single, ite_disj_cond_then_first, ite_cond_fail_else_unify, iso_not_1_04,
  boundary_disj_cut_then_conj_fail, iso_findall_3_05_false, iso_disjunction_2_03, iso_findall_3_05,
  iso_findall_3_06, iso_once_1_02, findall_disj_three_order_1_2_3, findall_disj_three_order_3_2_1,
  findall_disj_fail_prefix_single, findall_disj_fail_suffix_single, once_nested_disj_cut_commit,
  once_nested_disj_cut_prunes_all, findall_once_cut_commit_single, findall_once_cut_prunes_empty,
  findall_disj_once_mix_1_3, findall_disj_once_mix_3_1, once_findall_disj_order,
  iso_conjunction_2_03, iso_once_1_03, iso_not_1_06, iso_not_1_07, iso_not_1_08, iso_unify_2_06,
  iso_not_unifiable_2_05, iso_unify_2_17, iso_findall_3_02, iso_findall_3_07, iso_findall_3_08, ground_unify_case_02, ground_notUnify_case_02,
  ground_unify_case_03, ground_notUnify_case_03, ground_unify_case_04, ground_notUnify_case_04,
  ground_unify_case_05, ground_notUnify_case_05, ground_unify_case_06, ground_notUnify_case_06,
  ground_unify_case_07, ground_notUnify_case_07, ground_unify_case_08, ground_notUnify_case_08,
  ground_unify_case_09, ground_notUnify_case_09, ground_unify_case_10, ground_notUnify_case_10,
  ground_unify_case_11, ground_notUnify_case_11, ground_unify_case_12, ground_notUnify_case_12,
  ground_unify_case_13, ground_notUnify_case_13, ground_unify_case_14, ground_notUnify_case_14,
  ground_unify_case_15, ground_notUnify_case_15, ground_unify_case_16, ground_notUnify_case_16,
  ground_unify_case_17, ground_notUnify_case_17, ground_unify_case_18, ground_notUnify_case_18,
  ground_unify_case_19, ground_notUnify_case_19, ground_unify_case_20, ground_notUnify_case_20,
  ground_unify_case_21, ground_notUnify_case_21, ground_unify_case_22, ground_notUnify_case_22,
  ground_unify_case_23, ground_notUnify_case_23, ground_unify_case_24, ground_notUnify_case_24,
  ground_unify_case_25, ground_notUnify_case_25, ground_unify_case_26, ground_notUnify_case_26,
  ground_unify_case_27, ground_notUnify_case_27, ground_unify_case_28, ground_notUnify_case_28,
  ground_unify_case_29, ground_notUnify_case_29, ground_unify_case_30, ground_notUnify_case_30,
  ground_unify_case_31, ground_notUnify_case_31, ground_unify_case_32, ground_notUnify_case_32,
  ground_unify_case_33, ground_notUnify_case_33, ground_unify_case_34, ground_notUnify_case_34,
  ground_unify_case_35, ground_notUnify_case_35, ground_unify_case_36, ground_notUnify_case_36,
  ground_unify_case_37, ground_notUnify_case_37, ground_unify_case_38, ground_notUnify_case_38,
  ground_unify_case_39, ground_notUnify_case_39, ground_unify_case_40, ground_notUnify_case_40,
  ground_unify_case_41, ground_notUnify_case_41, ground_unify_case_42, ground_notUnify_case_42,
  ground_unify_case_43, ground_notUnify_case_43, ground_unify_case_44, ground_notUnify_case_44,
  ground_unify_case_45, ground_notUnify_case_45, ground_unify_case_46, ground_notUnify_case_46,
  ground_unify_case_47, ground_notUnify_case_47, ground_unify_case_48, ground_notUnify_case_48,
  ground_unify_case_49, ground_notUnify_case_49
]

private theorem ground_unify_eq {oracle : EvalOracle} :
    PrologEval oracle (.unify one one) [] (.normal [[]]) := by
  simpa using (iso_unify_2_01 (oracle := oracle) (env := []))

private theorem ground_notUnify_eq {oracle : EvalOracle} :
    PrologEval oracle (.notUnify one one) [] (.normal []) := by
  simpa using (iso_not_unifiable_2_01 (oracle := oracle) (env := []))

private theorem ground_unify_neq {oracle : EvalOracle} :
    PrologEval oracle (.unify one two) [] (.normal []) := by
  simpa using (iso_unify_2_07 (oracle := oracle) (env := []))

private theorem ground_notUnify_neq {oracle : EvalOracle} :
    PrologEval oracle (.notUnify one two) [] (.normal [[]]) := by
  simpa using (iso_not_unifiable_2_06 (oracle := oracle) (env := []))

theorem ground_unify_case_01 {oracle : EvalOracle} : PrologEval oracle (.unify one one) [] (.normal [[]]) := ground_unify_eq (oracle := oracle)
theorem ground_notUnify_case_01 {oracle : EvalOracle} : PrologEval oracle (.notUnify one one) [] (.normal []) := ground_notUnify_eq (oracle := oracle)
theorem ground_unify_case_50 {oracle : EvalOracle} : PrologEval oracle (.unify one two) [] (.normal []) := ground_unify_neq (oracle := oracle)
theorem ground_notUnify_case_50 {oracle : EvalOracle} : PrologEval oracle (.notUnify one two) [] (.normal [[]]) := ground_notUnify_neq (oracle := oracle)

end FixtureCorpus
end Mettapedia.Languages.Prolog
