theory Test_Automation
  imports "Disk/Disk_KCSD"
begin

(* ========================================================================= *)
(* TESTING AUTOMATED PROOF TOOLS                                            *)
(* ========================================================================= *)
(*
  Goal: Test sledgehammer, tactictoe, and other automation tools on our lemmas.

  Reference: Isabelle sledgehammer documentation
  - sledgehammer: invokes external ATPs (automated theorem provers)
  - Can be used interactively or in batch mode
*)

(* Test 1: Simple Boolean algebra lemma *)
lemma bool_test_1: "(a::bool) = (~(~a))"
  by simp

(* Test 2: XOR commutativity (the one we need!) *)
lemma xor2_comm_test:
  fixes u v :: "bool \<times> bool"
  shows "case u of (a1,b1) \<Rightarrow> case v of (a2,b2) \<Rightarrow> (a1 \<noteq> a2, b1 \<noteq> b2) =
         case v of (a2,b2) \<Rightarrow> case u of (a1,b1) \<Rightarrow> (a2 \<noteq> a1, b2 \<noteq> b1)"
  (* Try sledgehammer on this goal *)
  by (cases u; cases v) auto

(* Test 3: Can we invoke sledgehammer programmatically? *)
(* In interactive mode: sledgehammer [provers = e cvc4 vampire z3] *)

end
