(** The functional correspondence on one term, for a reader.

    Lean's development Mettapedia.Machines.FunctionalCorrespondence defines a
    call-by-value evaluator, evalV, which runs with fuel, and the CEK machine's
    step function.  Its theorem CEK.eval_to_machine says: when the evaluator
    returns a value, the machine started on the term, under any continuation,
    reaches that value under the same continuation.  The theorem's statement
    is generated from Lean's and proved in Egal (Lean_CEK_eval_to_machine),
    through the library of runs of a step function (Library/Machines.mg).

    Below, the theorem is used on the term (fun x => x) 7, which Lean names
    FunctionalCorrespondenceRuns.identityApplied.  The evaluator's answer at
    fuel 32 is 7: Lean_test_19 is that equation, proved by replaying Lean's
    equations and matched with the answer CeTTa computed.  The correspondence
    turns it into a run of the machine, and the machine's determinism makes
    that run's end its only final state. **)

(** 32 is a natural number. **)
Theorem Ex_fuel : LeanNum 32 :e Lean_Nat.
exact LeanNum_In 32
  (nat_ordsucc 31 (nat_ordsucc 30 (nat_ordsucc 29 (nat_ordsucc 28 (nat_ordsucc 27 (nat_ordsucc 26
  (nat_ordsucc 25 (nat_ordsucc 24 (nat_ordsucc 23 (nat_ordsucc 22 (nat_ordsucc 21 (nat_ordsucc 20
  (nat_ordsucc 19 (nat_ordsucc 18 (nat_ordsucc 17 (nat_ordsucc 16 (nat_ordsucc 15 (nat_ordsucc 14
  (nat_ordsucc 13 (nat_ordsucc 12 (nat_ordsucc 11 (nat_ordsucc 10 (nat_ordsucc 9 (nat_ordsucc 8
  (nat_ordsucc 7 (nat_ordsucc 6 (nat_ordsucc 5 (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2
  (nat_ordsucc 1 (nat_ordsucc 0 nat_0)))))))))))))))))))))))))))))))).
Qed.

(** The machine, started on (fun x => x) 7 with the empty environment and the
    empty continuation, reaches the value 7 with the empty continuation. **)
Theorem Ex_machine_run : 0 :e Lean_Relation_ReflTransGen_Prop Lean_CEK_St (Lean_StepRel Lean_CEK_St Lean_CEK_step)
  (Lean_CEK_St_mk_node (Lean_CEK_Ctl_ev_node Lean_FunctionalCorrespondenceRuns_identityApplied
    (Lean_List_nil_node Lean_CEK_Val)) (Lean_List_nil_node Lean_CEK_Frame))
  (Lean_CEK_St_mk_node (Lean_CEK_Ctl_ret_node (Lean_CEK_Val_lit_node (LeanNum 7))) (Lean_List_nil_node Lean_CEK_Frame)).
exact Lean_CEK_eval_to_machine (LeanNum 32) Ex_fuel
  (Lean_List_nil_node Lean_CEK_Val) (Lean_List_nil_typed Lean_CEK_Val)
  Lean_FunctionalCorrespondenceRuns_identityApplied Lean_FunctionalCorrespondenceRuns_identityApplied_In
  (Lean_CEK_Val_lit_node (LeanNum 7)) (Lean_CEK_Val_lit_typed (LeanNum 7) (LeanNum_In 7
  (nat_ordsucc 6 (nat_ordsucc 5 (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 (nat_ordsucc 1 (nat_ordsucc 0 nat_0)))))))))
  Lean_test_19 (Lean_List_nil_node Lean_CEK_Frame) (Lean_List_nil_typed Lean_CEK_Frame).
Qed.

(** That end is the machine's only final state: any run from the same start
    to a state where the machine stops ends there. **)
Theorem Ex_machine_answer_unique : forall f :e Lean_CEK_St,
  0 :e Lean_Relation_ReflTransGen_Prop Lean_CEK_St (Lean_StepRel Lean_CEK_St Lean_CEK_step)
    (Lean_CEK_St_mk_node (Lean_CEK_Ctl_ev_node Lean_FunctionalCorrespondenceRuns_identityApplied
      (Lean_List_nil_node Lean_CEK_Val)) (Lean_List_nil_node Lean_CEK_Frame)) f ->
  0 :e Lean_CEK_Final f ->
  f = Lean_CEK_St_mk_node (Lean_CEK_Ctl_ret_node (Lean_CEK_Val_lit_node (LeanNum 7))) (Lean_List_nil_node Lean_CEK_Frame).
let f. assume Hf: f :e Lean_CEK_St. assume Hrun. assume Hfinal.
claim Hlit: Lean_CEK_Val_lit_node (LeanNum 7) :e Lean_CEK_Val.
{ exact Lean_CEK_Val_lit_typed (LeanNum 7) (LeanNum_In 7
    (nat_ordsucc 6 (nat_ordsucc 5 (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 (nat_ordsucc 1 (nat_ordsucc 0 nat_0)))))))). }
exact Lean_CEK_steps_final_unique
  (Lean_CEK_St_mk_node (Lean_CEK_Ctl_ev_node Lean_FunctionalCorrespondenceRuns_identityApplied
    (Lean_List_nil_node Lean_CEK_Val)) (Lean_List_nil_node Lean_CEK_Frame))
  (Lean_CEK_St_mk_typed (Lean_CEK_Ctl_ev_node Lean_FunctionalCorrespondenceRuns_identityApplied
    (Lean_List_nil_node Lean_CEK_Val)) (Lean_CEK_Ctl_ev_typed Lean_FunctionalCorrespondenceRuns_identityApplied
    Lean_FunctionalCorrespondenceRuns_identityApplied_In (Lean_List_nil_node Lean_CEK_Val) (Lean_List_nil_typed Lean_CEK_Val))
    (Lean_List_nil_node Lean_CEK_Frame) (Lean_List_nil_typed Lean_CEK_Frame))
  f Hf
  (Lean_CEK_St_mk_node (Lean_CEK_Ctl_ret_node (Lean_CEK_Val_lit_node (LeanNum 7))) (Lean_List_nil_node Lean_CEK_Frame))
  (Lean_CEK_St_mk_typed (Lean_CEK_Ctl_ret_node (Lean_CEK_Val_lit_node (LeanNum 7)))
    (Lean_CEK_Ctl_ret_typed (Lean_CEK_Val_lit_node (LeanNum 7)) Hlit)
    (Lean_List_nil_node Lean_CEK_Frame) (Lean_List_nil_typed Lean_CEK_Frame))
  Hrun Ex_machine_run Hfinal (Lean_CEK_final_ret_nil (Lean_CEK_Val_lit_node (LeanNum 7)) Hlit).
Qed.
