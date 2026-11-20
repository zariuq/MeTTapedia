import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RuntimeSubstitutionSteps

/-!
# Shifting computed by finite source equation runs

The reference operation is `NativeSyntax.shift`. The target runs consist only
of instances of the finite helper program's ordinary equations. The proof
follows the numeric comparisons and the raw constructor tree, retaining the
actual continuation at every subcall.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RuntimeSubstitution

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open SourceLanguage.Elaboration

theorem add_index_runs (amount index : Nat) (continuation : MClosed) :
    Runs (addIndexC amount index continuation) (returnC (quoteRaw (.var (index + amount))) continuation) := by
  induction amount generalizing index with
  | zero => simpa using Relation.ReflTransGen.single (add_index_zero index continuation)
  | succ amount ih =>
      exact (Relation.ReflTransGen.single (add_index_next amount index continuation)).trans
        (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (index + 1))

theorem shift_index_runs (amount cutoff index original : Nat) (continuation : MClosed) :
    Runs (shiftIndexC amount cutoff index original continuation)
      (returnC (quoteRaw (.var (if index < cutoff then original else original + amount))) continuation) := by
  induction cutoff generalizing index with
  | zero =>
      simpa using (Relation.ReflTransGen.single (shift_index_cutoff amount index original continuation)).trans
        (add_index_runs amount original continuation)
  | succ cutoff ih =>
      cases index with
      | zero => simpa using Relation.ReflTransGen.single (shift_index_below amount cutoff original continuation)
      | succ index =>
          simpa using (Relation.ReflTransGen.single (shift_index_next amount cutoff index original continuation)).trans
            (ih index)

theorem visit_free_runs (operation term result continuation : MClosed)
    (mapped : Runs (mapC operation term continuation) (returnC result continuation)) :
    Runs (visitC false operation term continuation) (returnC result continuation) :=
  (Relation.ReflTransGen.single (visit_free operation term continuation)).trans mapped

theorem visit_bound_runs (operation lifted term result continuation : MClosed)
    (liftedRun : Runs (liftC operation (nodeC "hd-helper-after-lift" [term, continuation]))
      (returnC lifted (nodeC "hd-helper-after-lift" [term, continuation])))
    (mapped : Runs (mapC lifted term continuation) (returnC result continuation)) :
    Runs (visitC true operation term continuation) (returnC result continuation) :=
  (Relation.ReflTransGen.single (visit_bound operation term continuation)).trans
    (liftedRun.trans ((Relation.ReflTransGen.single (after_lift lifted term continuation)).trans mapped))

theorem visit_shift_runs (binds : Bool) (amount cutoff : Nat) (term result continuation : MClosed)
    (mapped : Runs (mapC (shiftOp amount (if binds then cutoff + 1 else cutoff)) term continuation)
      (returnC result continuation)) :
    Runs (visitC binds (shiftOp amount cutoff) term continuation) (returnC result continuation) := by
  cases binds with
  | false => exact visit_free_runs _ _ _ _ mapped
  | true =>
      exact visit_bound_runs _ _ _ _ _
        (Relation.ReflTransGen.single (lift_shift amount cutoff (nodeC "hd-helper-after-lift" [term, continuation]))) mapped

theorem unary_runs {tag : String} {binds : Bool} (inside : mapUnary tag binds ∈ rules)
    (operation child result continuation : MClosed)
    (childRun : Runs (visitC binds operation child (oneFrame tag continuation))
      (returnC result (oneFrame tag continuation))) :
    Runs (mapC operation (nodeC tag [child]) continuation) (returnC (nodeC tag [result]) continuation) :=
  (Relation.ReflTransGen.single (map_unary inside operation child continuation)).trans
    (childRun.trans (Relation.ReflTransGen.single (return_one result tag continuation)))

theorem binary_runs {tag : String} {firstBinds secondBinds : Bool}
    (inside : mapBinary tag firstBinds secondBinds ∈ rules)
    (operation first second firstResult secondResult continuation : MClosed)
    (firstRun : Runs (visitC firstBinds operation first
      (twoFirstFrame tag operation secondBinds second continuation))
      (returnC firstResult (twoFirstFrame tag operation secondBinds second continuation)))
    (secondRun : Runs (visitC secondBinds operation second (twoLastFrame tag firstResult continuation))
      (returnC secondResult (twoLastFrame tag firstResult continuation))) :
    Runs (mapC operation (nodeC tag [first, second]) continuation)
      (returnC (nodeC tag [firstResult, secondResult]) continuation) :=
  (Relation.ReflTransGen.single (map_binary inside operation first second continuation)).trans
    (firstRun.trans ((Relation.ReflTransGen.single (return_two_first firstResult tag operation secondBinds second continuation)).trans
      (secondRun.trans (Relation.ReflTransGen.single (return_two_last secondResult tag firstResult continuation)))))

theorem ternary_runs {tag : String} {firstBinds secondBinds thirdBinds : Bool}
    (inside : mapTernary tag firstBinds secondBinds thirdBinds ∈ rules)
    (operation first second third firstResult secondResult thirdResult continuation : MClosed)
    (firstRun : Runs (visitC firstBinds operation first
      (threeFirstFrame tag operation secondBinds second thirdBinds third continuation))
      (returnC firstResult (threeFirstFrame tag operation secondBinds second thirdBinds third continuation)))
    (secondRun : Runs (visitC secondBinds operation second
      (threeSecondFrame tag firstResult operation thirdBinds third continuation))
      (returnC secondResult (threeSecondFrame tag firstResult operation thirdBinds third continuation)))
    (thirdRun : Runs (visitC thirdBinds operation third (threeLastFrame tag firstResult secondResult continuation))
      (returnC thirdResult (threeLastFrame tag firstResult secondResult continuation))) :
    Runs (mapC operation (nodeC tag [first, second, third]) continuation)
      (returnC (nodeC tag [firstResult, secondResult, thirdResult]) continuation) :=
  (Relation.ReflTransGen.single (map_ternary inside operation first second third continuation)).trans
    (firstRun.trans ((Relation.ReflTransGen.single (return_three_first firstResult tag operation secondBinds second thirdBinds third continuation)).trans
      (secondRun.trans ((Relation.ReflTransGen.single (return_three_second secondResult tag firstResult operation thirdBinds third continuation)).trans
        (thirdRun.trans (Relation.ReflTransGen.single (return_three_last thirdResult tag firstResult secondResult continuation)))))))

theorem map_shift_runs (amount cutoff : Nat) (term : NativeSyntax.Raw Tower.Head) (continuation : MClosed) :
    Runs (mapC (shiftOp amount cutoff) (quoteRaw term) continuation)
      (returnC (quoteRaw (NativeSyntax.shift amount cutoff term)) continuation) := by
  induction term generalizing cutoff continuation with
  | var index =>
      exact (Relation.ReflTransGen.single (map_variable _ index continuation)).trans
        ((Relation.ReflTransGen.single (shift_variable amount cutoff index continuation)).trans
          (by simpa [NativeSyntax.shift, NativeSyntax.shiftIndex] using
            shift_index_runs amount cutoff index index continuation))
  | const name => exact Relation.ReflTransGen.single (map_constant _ name continuation)
  | head head => exact Relation.ReflTransGen.single (map_head _ head continuation)
  | pi domain body domainIH bodyIH =>
      simpa only [NativeSyntax.shift, quoteRaw] using
        binary_runs (tag := "prime-tm-pi") (firstBinds := false) (secondBinds := true)
          (by simp [rules]) (shiftOp amount cutoff) (quoteRaw domain) (quoteRaw body)
          (quoteRaw (NativeSyntax.shift amount cutoff domain))
          (quoteRaw (NativeSyntax.shift amount (cutoff + 1) body)) continuation
          (visit_shift_runs false amount cutoff _ _ _ (domainIH cutoff _))
          (visit_shift_runs true amount cutoff _ _ _ (bodyIH (cutoff + 1) _))
  | sigma domain body domainIH bodyIH =>
      simpa only [NativeSyntax.shift, quoteRaw] using
        binary_runs (tag := "prime-tm-sigma") (firstBinds := false) (secondBinds := true)
          (by simp [rules]) (shiftOp amount cutoff) (quoteRaw domain) (quoteRaw body)
          (quoteRaw (NativeSyntax.shift amount cutoff domain))
          (quoteRaw (NativeSyntax.shift amount (cutoff + 1) body)) continuation
          (visit_shift_runs false amount cutoff _ _ _ (domainIH cutoff _))
          (visit_shift_runs true amount cutoff _ _ _ (bodyIH (cutoff + 1) _))
  | id carrier left right carrierIH leftIH rightIH =>
      simpa only [NativeSyntax.shift, quoteRaw] using
        ternary_runs (tag := "prime-tm-id") (firstBinds := false) (secondBinds := false) (thirdBinds := false)
          (by simp [rules]) (shiftOp amount cutoff) (quoteRaw carrier) (quoteRaw left) (quoteRaw right)
          (quoteRaw (NativeSyntax.shift amount cutoff carrier)) (quoteRaw (NativeSyntax.shift amount cutoff left))
          (quoteRaw (NativeSyntax.shift amount cutoff right)) continuation
          (visit_shift_runs false amount cutoff _ _ _ (carrierIH cutoff _))
          (visit_shift_runs false amount cutoff _ _ _ (leftIH cutoff _))
          (visit_shift_runs false amount cutoff _ _ _ (rightIH cutoff _))
  | lamBare body ih =>
      simpa only [NativeSyntax.shift, quoteRaw] using
        unary_runs (tag := "prime-tm-lam") (binds := true) (by simp [rules])
          (shiftOp amount cutoff) (quoteRaw body) (quoteRaw (NativeSyntax.shift amount (cutoff + 1) body)) continuation
          (visit_shift_runs true amount cutoff _ _ _ (ih (cutoff + 1) _))
  | lamTyped domain body domainIH bodyIH =>
      simpa only [NativeSyntax.shift, quoteRaw] using
        binary_runs (tag := "prime-tm-lam-typed") (firstBinds := false) (secondBinds := true)
          (by simp [rules]) (shiftOp amount cutoff) (quoteRaw domain) (quoteRaw body)
          (quoteRaw (NativeSyntax.shift amount cutoff domain))
          (quoteRaw (NativeSyntax.shift amount (cutoff + 1) body)) continuation
          (visit_shift_runs false amount cutoff _ _ _ (domainIH cutoff _))
          (visit_shift_runs true amount cutoff _ _ _ (bodyIH (cutoff + 1) _))
  | app function argument functionIH argumentIH =>
      simpa only [NativeSyntax.shift, quoteRaw] using
        binary_runs (tag := "prime-tm-app") (firstBinds := false) (secondBinds := false)
          (by simp [rules]) (shiftOp amount cutoff) (quoteRaw function) (quoteRaw argument)
          (quoteRaw (NativeSyntax.shift amount cutoff function))
          (quoteRaw (NativeSyntax.shift amount cutoff argument)) continuation
          (visit_shift_runs false amount cutoff _ _ _ (functionIH cutoff _))
          (visit_shift_runs false amount cutoff _ _ _ (argumentIH cutoff _))
  | pair first second firstIH secondIH =>
      simpa only [NativeSyntax.shift, quoteRaw] using
        binary_runs (tag := "prime-tm-pair") (firstBinds := false) (secondBinds := false)
          (by simp [rules]) (shiftOp amount cutoff) (quoteRaw first) (quoteRaw second)
          (quoteRaw (NativeSyntax.shift amount cutoff first))
          (quoteRaw (NativeSyntax.shift amount cutoff second)) continuation
          (visit_shift_runs false amount cutoff _ _ _ (firstIH cutoff _))
          (visit_shift_runs false amount cutoff _ _ _ (secondIH cutoff _))
  | fst pair ih =>
      simpa only [NativeSyntax.shift, quoteRaw] using
        unary_runs (tag := "prime-tm-fst") (binds := false) (by simp [rules])
          (shiftOp amount cutoff) (quoteRaw pair) (quoteRaw (NativeSyntax.shift amount cutoff pair)) continuation
          (visit_shift_runs false amount cutoff _ _ _ (ih cutoff _))
  | snd pair ih =>
      simpa only [NativeSyntax.shift, quoteRaw] using
        unary_runs (tag := "prime-tm-snd") (binds := false) (by simp [rules])
          (shiftOp amount cutoff) (quoteRaw pair) (quoteRaw (NativeSyntax.shift amount cutoff pair)) continuation
          (visit_shift_runs false amount cutoff _ _ _ (ih cutoff _))
  | refl subject ih =>
      simpa only [NativeSyntax.shift, quoteRaw] using
        unary_runs (tag := "prime-tm-refl") (binds := false) (by simp [rules])
          (shiftOp amount cutoff) (quoteRaw subject) (quoteRaw (NativeSyntax.shift amount cutoff subject)) continuation
          (visit_shift_runs false amount cutoff _ _ _ (ih cutoff _))

theorem shift_runs (amount cutoff : Nat) (term : NativeSyntax.Raw Tower.Head) (continuation : MClosed) :
    Runs (shiftC amount cutoff (quoteRaw term) continuation)
      (resumeC (quoteRaw (NativeSyntax.shift amount cutoff term)) continuation) :=
  (Relation.ReflTransGen.single (enter_shift amount cutoff (quoteRaw term) continuation)).trans
    ((map_shift_runs amount cutoff term (bottom continuation)).trans
      (Relation.ReflTransGen.single (leave_bottom _ continuation)))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RuntimeSubstitution
