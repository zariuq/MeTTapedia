import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RuntimeShift

/-!
# Finite substitution environments executed by the helper program

Environment entries are literal raw terms. Entering a binder prepends the
newest variable and shifts every old entry. The lookup comparison includes the
explicit out-of-array default, so the raw algorithm agrees at every index.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RuntimeSubstitution

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open SourceLanguage.Elaboration

 def liftedEnvironment (environment : List (NativeSyntax.Raw Tower.Head)) : List (NativeSyntax.Raw Tower.Head) :=
  .var 0 :: environment.map (NativeSyntax.shift 1 0)

theorem lookup_lifted_environment (environment : List (NativeSyntax.Raw Tower.Head)) :
    DataEmbedding.rawLookup (liftedEnvironment environment) =
      NativeSyntax.liftSubRaw (DataEmbedding.rawLookup environment) := by
  funext index
  cases index with
  | zero => rfl
  | succ index =>
      cases found : environment[index]? with
      | none =>
          simp [liftedEnvironment, DataEmbedding.rawLookup, NativeSyntax.liftSubRaw,
            found, NativeSyntax.renameRaw]
      | some value =>
          simp [liftedEnvironment, DataEmbedding.rawLookup, NativeSyntax.liftSubRaw,
            found, NativeSyntax.renameRaw_succ]

theorem lookup_runs (environment : List (NativeSyntax.Raw Tower.Head)) (index : Nat) (continuation : MClosed) :
    Runs (lookupC environment index continuation)
      (returnC (quoteRaw (DataEmbedding.rawLookup environment index)) continuation) := by
  induction environment generalizing index with
  | nil => exact Relation.ReflTransGen.single (lookup_empty index continuation)
  | cons first rest ih =>
      cases index with
      | zero => exact Relation.ReflTransGen.single (lookup_zero first rest continuation)
      | succ index => exact (Relation.ReflTransGen.single (lookup_next first rest index continuation)).trans (ih index)

theorem lift_environment_runs (environment : List (NativeSyntax.Raw Tower.Head)) (continuation : MClosed) :
    Runs (liftEnvironmentC environment continuation)
      (returnC (encodeRawEnv (environment.map (NativeSyntax.shift 1 0))) continuation) := by
  induction environment generalizing continuation with
  | nil => exact Relation.ReflTransGen.single (lift_environment_empty continuation)
  | cons first rest ih =>
      exact (Relation.ReflTransGen.single (lift_environment_next first rest continuation)).trans
        ((map_shift_runs 1 0 first (nodeC "hd-helper-env-head" [encodeRawEnv rest, continuation])).trans
          ((Relation.ReflTransGen.single (lift_environment_head (NativeSyntax.shift 1 0 first) rest continuation)).trans
            ((ih (nodeC "hd-helper-env-tail" [quoteRaw (NativeSyntax.shift 1 0 first), continuation])).trans
              (Relation.ReflTransGen.single (lift_environment_tail (rest.map (NativeSyntax.shift 1 0))
                (NativeSyntax.shift 1 0 first) continuation)))))

theorem lift_environment_operation_runs (environment : List (NativeSyntax.Raw Tower.Head)) (continuation : MClosed) :
    Runs (liftC (environmentOp environment) continuation)
      (returnC (environmentOp (liftedEnvironment environment)) continuation) :=
  (Relation.ReflTransGen.single (lift_environment environment continuation)).trans
    ((lift_environment_runs environment (nodeC "hd-helper-env-op-frame" [continuation])).trans
      (Relation.ReflTransGen.single (environment_operation (environment.map (NativeSyntax.shift 1 0)) continuation)))

theorem visit_environment_runs (binds : Bool) (environment : List (NativeSyntax.Raw Tower.Head))
    (term result continuation : MClosed)
    (mapped : Runs (mapC (environmentOp (if binds then liftedEnvironment environment else environment)) term continuation)
      (returnC result continuation)) :
    Runs (visitC binds (environmentOp environment) term continuation) (returnC result continuation) := by
  cases binds with
  | false => exact visit_free_runs _ _ _ _ mapped
  | true =>
      exact visit_bound_runs _ _ _ _ _
        (lift_environment_operation_runs environment (nodeC "hd-helper-after-lift" [term, continuation])) mapped

theorem map_environment_runs (environment : List (NativeSyntax.Raw Tower.Head)) (term : NativeSyntax.Raw Tower.Head) (continuation : MClosed) :
    Runs (mapC (environmentOp environment) (quoteRaw term) continuation)
      (returnC (quoteRaw (NativeSyntax.substRaw (DataEmbedding.rawLookup environment) term)) continuation) := by
  induction term generalizing environment continuation with
  | var index =>
      exact (Relation.ReflTransGen.single (map_variable _ index continuation)).trans
        ((Relation.ReflTransGen.single (environment_variable environment index continuation)).trans
          (lookup_runs environment index continuation))
  | const name => exact Relation.ReflTransGen.single (map_constant _ name continuation)
  | head head => exact Relation.ReflTransGen.single (map_head _ head continuation)
  | pi domain body domainIH bodyIH =>
      simpa only [NativeSyntax.substRaw, quoteRaw, lookup_lifted_environment] using
        binary_runs (tag := "prime-tm-pi") (firstBinds := false) (secondBinds := true)
          (by simp [rules]) (environmentOp environment) (quoteRaw domain) (quoteRaw body)
          (quoteRaw (NativeSyntax.substRaw (DataEmbedding.rawLookup environment) domain))
          (quoteRaw (NativeSyntax.substRaw (DataEmbedding.rawLookup (liftedEnvironment environment)) body)) continuation
          (visit_environment_runs false environment _ _ _ (domainIH environment _))
          (visit_environment_runs true environment _ _ _ (bodyIH (liftedEnvironment environment) _))
  | sigma domain body domainIH bodyIH =>
      simpa only [NativeSyntax.substRaw, quoteRaw, lookup_lifted_environment] using
        binary_runs (tag := "prime-tm-sigma") (firstBinds := false) (secondBinds := true)
          (by simp [rules]) (environmentOp environment) (quoteRaw domain) (quoteRaw body)
          (quoteRaw (NativeSyntax.substRaw (DataEmbedding.rawLookup environment) domain))
          (quoteRaw (NativeSyntax.substRaw (DataEmbedding.rawLookup (liftedEnvironment environment)) body)) continuation
          (visit_environment_runs false environment _ _ _ (domainIH environment _))
          (visit_environment_runs true environment _ _ _ (bodyIH (liftedEnvironment environment) _))
  | id carrier left right carrierIH leftIH rightIH =>
      simpa only [NativeSyntax.substRaw, quoteRaw] using
        ternary_runs (tag := "prime-tm-id") (firstBinds := false) (secondBinds := false) (thirdBinds := false)
          (by simp [rules]) (environmentOp environment) (quoteRaw carrier) (quoteRaw left) (quoteRaw right)
          (quoteRaw (NativeSyntax.substRaw (DataEmbedding.rawLookup environment) carrier)) (quoteRaw (NativeSyntax.substRaw (DataEmbedding.rawLookup environment) left))
          (quoteRaw (NativeSyntax.substRaw (DataEmbedding.rawLookup environment) right)) continuation
          (visit_environment_runs false environment _ _ _ (carrierIH environment _))
          (visit_environment_runs false environment _ _ _ (leftIH environment _))
          (visit_environment_runs false environment _ _ _ (rightIH environment _))
  | lamBare body ih =>
      simpa only [NativeSyntax.substRaw, quoteRaw, lookup_lifted_environment] using
        unary_runs (tag := "prime-tm-lam") (binds := true) (by simp [rules])
          (environmentOp environment) (quoteRaw body) (quoteRaw (NativeSyntax.substRaw (DataEmbedding.rawLookup (liftedEnvironment environment)) body)) continuation
          (visit_environment_runs true environment _ _ _ (ih (liftedEnvironment environment) _))
  | lamTyped domain body domainIH bodyIH =>
      simpa only [NativeSyntax.substRaw, quoteRaw, lookup_lifted_environment] using
        binary_runs (tag := "prime-tm-lam-typed") (firstBinds := false) (secondBinds := true)
          (by simp [rules]) (environmentOp environment) (quoteRaw domain) (quoteRaw body)
          (quoteRaw (NativeSyntax.substRaw (DataEmbedding.rawLookup environment) domain))
          (quoteRaw (NativeSyntax.substRaw (DataEmbedding.rawLookup (liftedEnvironment environment)) body)) continuation
          (visit_environment_runs false environment _ _ _ (domainIH environment _))
          (visit_environment_runs true environment _ _ _ (bodyIH (liftedEnvironment environment) _))
  | app function argument functionIH argumentIH =>
      simpa only [NativeSyntax.substRaw, quoteRaw] using
        binary_runs (tag := "prime-tm-app") (firstBinds := false) (secondBinds := false)
          (by simp [rules]) (environmentOp environment) (quoteRaw function) (quoteRaw argument)
          (quoteRaw (NativeSyntax.substRaw (DataEmbedding.rawLookup environment) function))
          (quoteRaw (NativeSyntax.substRaw (DataEmbedding.rawLookup environment) argument)) continuation
          (visit_environment_runs false environment _ _ _ (functionIH environment _))
          (visit_environment_runs false environment _ _ _ (argumentIH environment _))
  | pair first second firstIH secondIH =>
      simpa only [NativeSyntax.substRaw, quoteRaw] using
        binary_runs (tag := "prime-tm-pair") (firstBinds := false) (secondBinds := false)
          (by simp [rules]) (environmentOp environment) (quoteRaw first) (quoteRaw second)
          (quoteRaw (NativeSyntax.substRaw (DataEmbedding.rawLookup environment) first))
          (quoteRaw (NativeSyntax.substRaw (DataEmbedding.rawLookup environment) second)) continuation
          (visit_environment_runs false environment _ _ _ (firstIH environment _))
          (visit_environment_runs false environment _ _ _ (secondIH environment _))
  | fst pair ih =>
      simpa only [NativeSyntax.substRaw, quoteRaw] using
        unary_runs (tag := "prime-tm-fst") (binds := false) (by simp [rules])
          (environmentOp environment) (quoteRaw pair) (quoteRaw (NativeSyntax.substRaw (DataEmbedding.rawLookup environment) pair)) continuation
          (visit_environment_runs false environment _ _ _ (ih environment _))
  | snd pair ih =>
      simpa only [NativeSyntax.substRaw, quoteRaw] using
        unary_runs (tag := "prime-tm-snd") (binds := false) (by simp [rules])
          (environmentOp environment) (quoteRaw pair) (quoteRaw (NativeSyntax.substRaw (DataEmbedding.rawLookup environment) pair)) continuation
          (visit_environment_runs false environment _ _ _ (ih environment _))
  | refl subject ih =>
      simpa only [NativeSyntax.substRaw, quoteRaw] using
        unary_runs (tag := "prime-tm-refl") (binds := false) (by simp [rules])
          (environmentOp environment) (quoteRaw subject) (quoteRaw (NativeSyntax.substRaw (DataEmbedding.rawLookup environment) subject)) continuation
          (visit_environment_runs false environment _ _ _ (ih environment _))

theorem environment_runs (environment : List (NativeSyntax.Raw Tower.Head))
    (body : NativeSyntax.Raw Tower.Head) (continuation : MClosed) :
    Runs (substituteEnvironmentC (encodeRawEnv environment) (quoteRaw body) continuation)
      (resumeC (quoteRaw (NativeSyntax.substRaw (DataEmbedding.rawLookup environment) body)) continuation) :=
  (Relation.ReflTransGen.single (enter_environment environment (quoteRaw body) continuation)).trans
    ((map_environment_runs environment body (bottom continuation)).trans
      (Relation.ReflTransGen.single (leave_bottom _ continuation)))

theorem scoped_environment_runs {n m : Nat} (substitution : Sub Tower.Head n m)
    (body : Tower.Tm n) (continuation : MClosed) :
    Runs (substituteEnvironmentC (encodeRawEnv (DataEmbedding.rawEnvironment substitution)) (encodeTm body) continuation)
      (resumeC (encodeTm (subst substitution body)) continuation) := by
  simpa only [quoteRaw_rawTm, DataEmbedding.finite_substitution] using
    environment_runs (DataEmbedding.rawEnvironment substitution) (rawTm body) continuation

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RuntimeSubstitution
