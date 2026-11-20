import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RuntimeShift

/-!
# Capture-avoiding zero substitution by finite source equation runs

The comparison walks indices until it finds the variable being replaced.
Only that branch invokes the already proved shift program. Constructor
traversal retains the current depth and increments it at actual binders.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RuntimeSubstitution

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open SourceLanguage.Elaboration

theorem zero_index_runs (replacement : NativeSyntax.Raw Tower.Head) (depth index offset : Nat)
    (continuation : MClosed) :
    Runs (zeroIndexC replacement depth index (offset + depth) (offset + index) continuation)
      (returnC (quoteRaw (NativeSyntax.zeroSub replacement (offset + depth) (offset + index))) continuation) := by
  induction depth generalizing index offset with
  | zero =>
      cases index with
      | zero =>
          simpa [NativeSyntax.zeroSub] using
            (Relation.ReflTransGen.single (zero_index_equal replacement offset offset continuation)).trans
              (map_shift_runs offset 0 replacement continuation)
      | succ index =>
          have less : ¬ offset + (index + 1) < offset := by omega
          have different : offset + (index + 1) ≠ offset := by omega
          simpa [NativeSyntax.zeroSub, less, different, Nat.add_assoc] using
            Relation.ReflTransGen.single
              (zero_index_above replacement index offset (offset + index) continuation)
  | succ depth ih =>
      cases index with
      | zero =>
          have below : offset < offset + (depth + 1) := by omega
          simpa [NativeSyntax.zeroSub, below] using
            Relation.ReflTransGen.single
              (zero_index_below replacement depth (offset + (depth + 1)) offset continuation)
      | succ index =>
          exact (Relation.ReflTransGen.single
            (zero_index_next replacement depth index (offset + (depth + 1)) (offset + (index + 1)) continuation)).trans
              (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih index (offset + 1))

theorem visit_zero_runs (binds : Bool) (replacement : NativeSyntax.Raw Tower.Head) (depth : Nat)
    (term result continuation : MClosed)
    (mapped : Runs (mapC (zeroOp replacement (if binds then depth + 1 else depth)) term continuation)
      (returnC result continuation)) :
    Runs (visitC binds (zeroOp replacement depth) term continuation) (returnC result continuation) := by
  cases binds with
  | false => exact visit_free_runs _ _ _ _ mapped
  | true =>
      exact visit_bound_runs _ _ _ _ _
        (Relation.ReflTransGen.single (lift_zero replacement depth (nodeC "hd-helper-after-lift" [term, continuation]))) mapped

theorem map_zero_runs (replacement : NativeSyntax.Raw Tower.Head) (depth : Nat) (term : NativeSyntax.Raw Tower.Head) (continuation : MClosed) :
    Runs (mapC (zeroOp replacement depth) (quoteRaw term) continuation)
      (returnC (quoteRaw (NativeSyntax.substituteZero replacement depth term)) continuation) := by
  induction term generalizing depth continuation with
  | var index =>
      exact (Relation.ReflTransGen.single (map_variable _ index continuation)).trans
        ((Relation.ReflTransGen.single (zero_variable replacement depth index continuation)).trans
          (by simpa only [Nat.zero_add, NativeSyntax.substituteZero, NativeSyntax.zeroSub] using
            zero_index_runs replacement depth index 0 continuation))
  | const name => exact Relation.ReflTransGen.single (map_constant _ name continuation)
  | head head => exact Relation.ReflTransGen.single (map_head _ head continuation)
  | pi domain body domainIH bodyIH =>
      simpa only [NativeSyntax.substituteZero, quoteRaw] using
        binary_runs (tag := "prime-tm-pi") (firstBinds := false) (secondBinds := true)
          (by simp [rules]) (zeroOp replacement depth) (quoteRaw domain) (quoteRaw body)
          (quoteRaw (NativeSyntax.substituteZero replacement depth domain))
          (quoteRaw (NativeSyntax.substituteZero replacement (depth + 1) body)) continuation
          (visit_zero_runs false replacement depth _ _ _ (domainIH depth _))
          (visit_zero_runs true replacement depth _ _ _ (bodyIH (depth + 1) _))
  | sigma domain body domainIH bodyIH =>
      simpa only [NativeSyntax.substituteZero, quoteRaw] using
        binary_runs (tag := "prime-tm-sigma") (firstBinds := false) (secondBinds := true)
          (by simp [rules]) (zeroOp replacement depth) (quoteRaw domain) (quoteRaw body)
          (quoteRaw (NativeSyntax.substituteZero replacement depth domain))
          (quoteRaw (NativeSyntax.substituteZero replacement (depth + 1) body)) continuation
          (visit_zero_runs false replacement depth _ _ _ (domainIH depth _))
          (visit_zero_runs true replacement depth _ _ _ (bodyIH (depth + 1) _))
  | id carrier left right carrierIH leftIH rightIH =>
      simpa only [NativeSyntax.substituteZero, quoteRaw] using
        ternary_runs (tag := "prime-tm-id") (firstBinds := false) (secondBinds := false) (thirdBinds := false)
          (by simp [rules]) (zeroOp replacement depth) (quoteRaw carrier) (quoteRaw left) (quoteRaw right)
          (quoteRaw (NativeSyntax.substituteZero replacement depth carrier)) (quoteRaw (NativeSyntax.substituteZero replacement depth left))
          (quoteRaw (NativeSyntax.substituteZero replacement depth right)) continuation
          (visit_zero_runs false replacement depth _ _ _ (carrierIH depth _))
          (visit_zero_runs false replacement depth _ _ _ (leftIH depth _))
          (visit_zero_runs false replacement depth _ _ _ (rightIH depth _))
  | lamBare body ih =>
      simpa only [NativeSyntax.substituteZero, quoteRaw] using
        unary_runs (tag := "prime-tm-lam") (binds := true) (by simp [rules])
          (zeroOp replacement depth) (quoteRaw body) (quoteRaw (NativeSyntax.substituteZero replacement (depth + 1) body)) continuation
          (visit_zero_runs true replacement depth _ _ _ (ih (depth + 1) _))
  | lamTyped domain body domainIH bodyIH =>
      simpa only [NativeSyntax.substituteZero, quoteRaw] using
        binary_runs (tag := "prime-tm-lam-typed") (firstBinds := false) (secondBinds := true)
          (by simp [rules]) (zeroOp replacement depth) (quoteRaw domain) (quoteRaw body)
          (quoteRaw (NativeSyntax.substituteZero replacement depth domain))
          (quoteRaw (NativeSyntax.substituteZero replacement (depth + 1) body)) continuation
          (visit_zero_runs false replacement depth _ _ _ (domainIH depth _))
          (visit_zero_runs true replacement depth _ _ _ (bodyIH (depth + 1) _))
  | app function argument functionIH argumentIH =>
      simpa only [NativeSyntax.substituteZero, quoteRaw] using
        binary_runs (tag := "prime-tm-app") (firstBinds := false) (secondBinds := false)
          (by simp [rules]) (zeroOp replacement depth) (quoteRaw function) (quoteRaw argument)
          (quoteRaw (NativeSyntax.substituteZero replacement depth function))
          (quoteRaw (NativeSyntax.substituteZero replacement depth argument)) continuation
          (visit_zero_runs false replacement depth _ _ _ (functionIH depth _))
          (visit_zero_runs false replacement depth _ _ _ (argumentIH depth _))
  | pair first second firstIH secondIH =>
      simpa only [NativeSyntax.substituteZero, quoteRaw] using
        binary_runs (tag := "prime-tm-pair") (firstBinds := false) (secondBinds := false)
          (by simp [rules]) (zeroOp replacement depth) (quoteRaw first) (quoteRaw second)
          (quoteRaw (NativeSyntax.substituteZero replacement depth first))
          (quoteRaw (NativeSyntax.substituteZero replacement depth second)) continuation
          (visit_zero_runs false replacement depth _ _ _ (firstIH depth _))
          (visit_zero_runs false replacement depth _ _ _ (secondIH depth _))
  | fst pair ih =>
      simpa only [NativeSyntax.substituteZero, quoteRaw] using
        unary_runs (tag := "prime-tm-fst") (binds := false) (by simp [rules])
          (zeroOp replacement depth) (quoteRaw pair) (quoteRaw (NativeSyntax.substituteZero replacement depth pair)) continuation
          (visit_zero_runs false replacement depth _ _ _ (ih depth _))
  | snd pair ih =>
      simpa only [NativeSyntax.substituteZero, quoteRaw] using
        unary_runs (tag := "prime-tm-snd") (binds := false) (by simp [rules])
          (zeroOp replacement depth) (quoteRaw pair) (quoteRaw (NativeSyntax.substituteZero replacement depth pair)) continuation
          (visit_zero_runs false replacement depth _ _ _ (ih depth _))
  | refl subject ih =>
      simpa only [NativeSyntax.substituteZero, quoteRaw] using
        unary_runs (tag := "prime-tm-refl") (binds := false) (by simp [rules])
          (zeroOp replacement depth) (quoteRaw subject) (quoteRaw (NativeSyntax.substituteZero replacement depth subject)) continuation
          (visit_zero_runs false replacement depth _ _ _ (ih depth _))

theorem zero_runs (replacement : NativeSyntax.Raw Tower.Head) (depth : Nat)
    (body : NativeSyntax.Raw Tower.Head) (continuation : MClosed) :
    Runs (substituteZeroC (quoteRaw replacement) depth (quoteRaw body) continuation)
      (resumeC (quoteRaw (NativeSyntax.substituteZero replacement depth body)) continuation) :=
  (Relation.ReflTransGen.single (enter_zero replacement body depth continuation)).trans
    ((map_zero_runs replacement depth body (bottom continuation)).trans
      (Relation.ReflTransGen.single (leave_bottom _ continuation)))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RuntimeSubstitution
