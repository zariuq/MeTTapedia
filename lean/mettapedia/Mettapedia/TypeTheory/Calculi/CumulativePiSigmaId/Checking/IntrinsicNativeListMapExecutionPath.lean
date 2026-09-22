import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.IntrinsicNativeListMapComputation
import Mettapedia.GSLT.Core.OperationalRealizationOSLF
import Mettapedia.GSLT.Dynamics.ExecutionPathObservation

/-!
# Proof-relevant execution paths for the intrinsic List map

The original native List computation theorems establish proposition-valued
reachability.  That is sufficient for an OSLF possibility judgment, but it
cannot be inspected by an observation discipline: eliminating a proposition
cannot recover the ordered step occurrences that produced it.

This module states the same beta/iota execution directly in the free execution
category.  Every primitive step is retained in an `ExecutionPath`; erasing the
path recovers the existing multi-step relation.  The two sides of map fusion
therefore have independently observable histories even though they converge
to the same constructor spine.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.IntrinsicNativeListMapExecutionPath

open Presentation NativeIndexedFamilies IntrinsicMaps
open IntrinsicNativeListMapComputation
open Mettapedia.GSLT.IndexedOperational

variable {n m : Nat}

/-- A finite, proof-relevant beta/iota execution in the native List GSLT. -/
abbrev PathReduces (level : LevelExpr) (left right : Tower.Tm n) :=
  ExecutionPath (reduction level n) left right

namespace PathReduces

/-- Forgetting occurrence identity recovers ordinary finite reachability. -/
theorem erase {level : LevelExpr} {left right : Tower.Tm n}
    (path : PathReduces level left right) : Reduces level left right :=
  executionPathToMultiStep path

def trans {level : LevelExpr} {first middle last : Tower.Tm n}
    (earlier : PathReduces level first middle)
    (later : PathReduces level middle last) :
    PathReduces level first last :=
  earlier.append later

def appFun {level : LevelExpr} :
    {left right : Tower.Tm n} → PathReduces level left right →
      (argument : Tower.Tm n) →
        PathReduces level (.app left argument) (.app right argument)
  | _, _, .refl _, _ => .refl _
  | _, _, .cons step rest, argument =>
      .cons ⟨.congAppFun step.down⟩ (appFun rest argument)

def appArg {level : LevelExpr} :
    {left right : Tower.Tm n} → PathReduces level left right →
      (function : Tower.Tm n) →
        PathReduces level (.app function left) (.app function right)
  | _, _, .refl _, _ => .refl _
  | _, _, .cons step rest, function =>
      .cons ⟨.congAppArg step.down⟩ (appArg rest function)

def substitute {level : LevelExpr} :
    {left right : Tower.Tm n} → PathReduces level left right →
      (sigma : Sub Tower.Head n m) →
        PathReduces level (subst sigma left) (subst sigma right)
  | _, _, .refl _, _ => .refl _
  | _, _, .cons step rest, sigma =>
      .cons ⟨step.down.substitute sigma⟩ (substitute rest sigma)

def beta (level : LevelExpr) (body : Tower.Tm (n + 1))
    (argument : Tower.Tm n) :
    PathReduces level (.app (.lam body) argument) (inst0 argument body) :=
  .cons ⟨.betaPi body argument⟩ (.refl _)

/-- Reindex only the endpoints of a retained path.  The path and all of its
step occurrences are unchanged. -/
def castEndpoints {level : LevelExpr}
    {left right left' right' : Tower.Tm n}
    (path : PathReduces level left right)
    (leftEqual : left = left') (rightEqual : right = right') :
    PathReduces level left' right' := by
  subst left'
  subst right'
  exact path

@[simp] theorem castEndpoints_length {level : LevelExpr}
    {left right left' right' : Tower.Tm n}
    (path : PathReduces level left right)
    (leftEqual : left = left') (rightEqual : right = right') :
    (castEndpoints path leftEqual rightEqual).length = path.length := by
  subst left'
  subst right'
  rfl

@[simp] theorem erase_trans {level : LevelExpr}
    {first middle last : Tower.Tm n}
    (earlier : PathReduces level first middle)
    (later : PathReduces level middle last) :
    erase (earlier.trans later) = (earlier.erase).trans later.erase := by
  apply Subsingleton.elim

@[simp] theorem trans_length {level : LevelExpr}
    {first middle last : Tower.Tm n}
    (earlier : PathReduces level first middle)
    (later : PathReduces level middle last) :
    (earlier.trans later).length = earlier.length + later.length := by
  exact Mettapedia.GSLT.Ultrainfinite.Route.length_append earlier later

@[simp] theorem appFun_length {level : LevelExpr}
    {left right : Tower.Tm n} (path : PathReduces level left right)
    (argument : Tower.Tm n) :
    (path.appFun argument).length = path.length := by
  induction path with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      simp only [appFun, Mettapedia.GSLT.Ultrainfinite.Route.length,
        inductionHypothesis]

@[simp] theorem appArg_length {level : LevelExpr}
    {left right : Tower.Tm n} (path : PathReduces level left right)
    (function : Tower.Tm n) :
    (path.appArg function).length = path.length := by
  induction path with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      simp only [appArg, Mettapedia.GSLT.Ultrainfinite.Route.length,
        inductionHypothesis]

@[simp] theorem beta_length (level : LevelExpr)
    (body : Tower.Tm (n + 1)) (argument : Tower.Tm n) :
    (beta level body argument).length = 1 := by
  rfl

/-- A retained execution path together with its exact primitive-step count.
Keeping this evidence beside the path prevents endpoint transports from
obscuring costs in later dependent constructions. -/
structure Measured (level : LevelExpr) (left right : Tower.Tm n)
    (steps : Nat) where
  path : PathReduces level left right
  length_eq : path.length = steps

namespace Measured

def trans {level : LevelExpr} {first middle last : Tower.Tm n}
    {earlierSteps laterSteps : Nat}
    (earlier : Measured level first middle earlierSteps)
    (later : Measured level middle last laterSteps) :
    Measured level first last (earlierSteps + laterSteps) where
  path := earlier.path.trans later.path
  length_eq := by
    rw [PathReduces.trans_length, earlier.length_eq, later.length_eq]

def appFun {level : LevelExpr} {left right : Tower.Tm n} {steps : Nat}
    (path : Measured level left right steps) (argument : Tower.Tm n) :
    Measured level (.app left argument) (.app right argument) steps where
  path := path.path.appFun argument
  length_eq := by
    rw [PathReduces.appFun_length, path.length_eq]

def appArg {level : LevelExpr} {left right : Tower.Tm n} {steps : Nat}
    (path : Measured level left right steps) (function : Tower.Tm n) :
    Measured level (.app function left) (.app function right) steps where
  path := path.path.appArg function
  length_eq := by
    rw [PathReduces.appArg_length, path.length_eq]

def castEndpoints {level : LevelExpr}
    {left right left' right' : Tower.Tm n} {steps : Nat}
    (path : Measured level left right steps)
    (leftEqual : left = left') (rightEqual : right = right') :
    Measured level left' right' steps where
  path := PathReduces.castEndpoints path.path leftEqual rightEqual
  length_eq := by
    rw [PathReduces.castEndpoints_length, path.length_eq]

/-- Reindex the arithmetic presentation of an already measured path. -/
def castSteps {level : LevelExpr} {left right : Tower.Tm n}
    {steps steps' : Nat} (path : Measured level left right steps)
    (equal : steps = steps') : Measured level left right steps' := by
  subst steps'
  exact path

def beta (level : LevelExpr) (body : Tower.Tm (n + 1))
    (argument : Tower.Tm n) :
    Measured level (.app (.lam body) argument) (inst0 argument body) 1 where
  path := PathReduces.beta level body argument
  length_eq := PathReduces.beta_length level body argument

end Measured

end PathReduces

@[simp] private theorem subst_vars (term : Tower.Tm n) :
    subst (fun i => .var i) term = term := subst_ids term

private theorem fin_two (n : Nat) : (2 : Fin (n + 3)) =
    (0 : Fin (n + 1)).succ.succ := by
  apply Fin.ext
  change 2 % (n + 3) = 0 + 1 + 1
  exact Nat.mod_eq_of_lt (by omega)

private theorem fin_three (n : Nat) : (3 : Fin (n + 4)) =
    (0 : Fin (n + 1)).succ.succ.succ := by
  apply Fin.ext
  change 3 % (n + 4) = 0 + 1 + 1 + 1
  exact Nat.mod_eq_of_lt (by omega)

private theorem fin_four (n : Nat) : (4 : Fin (n + 5)) =
    (0 : Fin (n + 1)).succ.succ.succ.succ := by
  apply Fin.ext
  change 4 % (n + 5) = 0 + 1 + 1 + 1 + 1
  exact Nat.mod_eq_of_lt (by omega)

private theorem fin_five (n : Nat) : (5 : Fin (n + 6)) =
    (0 : Fin (n + 1)).succ.succ.succ.succ.succ := by
  apply Fin.ext
  change 5 % (n + 6) = 0 + 1 + 1 + 1 + 1 + 1
  exact Nat.mod_eq_of_lt (by omega)

private def branch_beta_measured (level : LevelExpr)
    (target function head tail result : Tower.Tm n) :
    PathReduces.Measured level
      (.app (.app (.app (branch target function) head) tail) result)
      (Intrinsic.consApp target (.app function head) result) 3 := by
  unfold branch
  refine PathReduces.Measured.trans (laterSteps := 2)
    (((PathReduces.Measured.beta level _ head).appFun tail).appFun result) ?_
  dsimp [inst0, subst, subst0, liftSub]
  refine PathReduces.Measured.trans (laterSteps := 1)
    ((PathReduces.Measured.beta level _ tail).appFun result) ?_
  dsimp [inst0, subst, subst0, liftSub]
  let finalBody :=
    subst (liftSub (subst0 tail))
      (subst (liftSub (liftSub (subst0 head)))
        (Intrinsic.consApp (rename (fun i => i.succ.succ.succ) target)
          (.app (rename (fun i => i.succ.succ.succ) function) (.var 2))
          (.var 0)))
  refine PathReduces.Measured.castEndpoints
    (PathReduces.Measured.beta level finalBody result) rfl ?_
  dsimp only [finalBody]
  simp only [Intrinsic.consApp, inst0, subst, subst_rename]
  simp [subst0, liftSub, wk, subst, rename, fin_two,
      -Fin.succ_zero_eq_one, -Fin.succ_one_eq_two,
      -Fin.succ_zero_eq_one', -Fin.succ_one_eq_two']
  simp [subst_rename, subst0, rename]

def branch_beta_path (level : LevelExpr)
    (target function head tail result : Tower.Tm n) :
    PathReduces level
      (.app (.app (.app (branch target function) head) tail) result)
      (Intrinsic.consApp target (.app function head) result) :=
  (branch_beta_measured level target function head tail result).path

@[simp] theorem branch_beta_path_length (level : LevelExpr)
    (target function head tail result : Tower.Tm n) :
    (branch_beta_path level target function head tail result).length = 3 := by
  exact (branch_beta_measured level target function head tail result).length_eq

private def applyMap_beta_measured (level : LevelExpr)
    (source target function xs : Tower.Tm n) :
    PathReduces.Measured level (applyMap source target function xs)
      (mapped source target function xs) 4 := by
  unfold applyMap nativeMapTerm liftClosed
  dsimp [rename]
  refine PathReduces.Measured.trans (laterSteps := 3)
    ((((PathReduces.Measured.beta level _ source).appFun target).appFun function
      ).appFun xs) ?_
  dsimp [inst0, subst, subst0, liftSub]
  refine PathReduces.Measured.trans (laterSteps := 2)
    (((PathReduces.Measured.beta level _ target).appFun function).appFun xs) ?_
  dsimp [inst0, subst, subst0, liftSub]
  refine PathReduces.Measured.trans (laterSteps := 1)
    ((PathReduces.Measured.beta level _ function).appFun xs) ?_
  dsimp [inst0, subst, subst0, liftSub]
  let finalBody :=
    subst (liftSub (subst0 function))
      (subst (liftSub (liftSub (subst0 target)))
        (subst (liftSub (liftSub (liftSub (subst0 source))))
          (rename (liftRen (liftRen (liftRen (liftRen Fin.elim0))))
            nativeMapBody)))
  refine PathReduces.Measured.castEndpoints
    (PathReduces.Measured.beta level finalBody xs) rfl ?_
  dsimp only [finalBody]
  change
    subst (subst0 xs)
      (subst (liftSub (subst0 function))
        (subst (liftSub (liftSub (subst0 target)))
          (subst (liftSub (liftSub (liftSub (subst0 source))))
            (rename (liftRen (liftRen (liftRen (liftRen Fin.elim0))))
              nativeMapBody)))) = mapped source target function xs
  rw [Intrinsic.instantiateFour_eq_subst]
  simp [mapped, nativeMapBody, nativeMapMotive, nativeMapNilCase,
    nativeMapConsCase, motive, branch, Intrinsic.eliminateApp,
    Intrinsic.nilApp, Intrinsic.consApp, Intrinsic.listApp,
    Intrinsic.nilSchemaSubstitution, Intrinsic.nilCaseSchemaSubstitution,
    Intrinsic.motiveSchemaSubstitution, consSub, Fin.cases, subst, liftSub, wk,
    fin_two, fin_three, fin_four, fin_five,
    -Fin.succ_zero_eq_one, -Fin.succ_one_eq_two,
    -Fin.succ_zero_eq_one', -Fin.succ_one_eq_two']
  dsimp [Fin.induction, Intrinsic.elementSchemaSubstitution, consSub, Fin.cases]
  simp [Fin.induction.go, rename_comp, rename]

def applyMap_beta_path (level : LevelExpr)
    (source target function xs : Tower.Tm n) :
    PathReduces level (applyMap source target function xs)
      (mapped source target function xs) :=
  (applyMap_beta_measured level source target function xs).path

@[simp] theorem applyMap_beta_path_length (level : LevelExpr)
    (source target function xs : Tower.Tm n) :
    (applyMap_beta_path level source target function xs).length = 4 := by
  exact (applyMap_beta_measured level source target function xs).length_eq

private def mapped_nil_measured (level : LevelExpr)
    (source target function : Tower.Tm n) :
    PathReduces.Measured level
      (mapped source target function (Intrinsic.nilApp source))
      (Intrinsic.nilApp target) 1 where
  path := .cons ⟨.root (.declared ⟨.nil _ _ _ _⟩)⟩ (.refl _)
  length_eq := rfl

private def mapped_cons_measured (level : LevelExpr)
    (source target function head tail : Tower.Tm n) :
    PathReduces.Measured level
      (mapped source target function (Intrinsic.consApp source head tail))
      (Intrinsic.consApp target (.app function head)
        (mapped source target function tail)) 4 where
  path := .cons ⟨.root (.declared ⟨.cons _ _ _ _ _ _⟩)⟩
    (branch_beta_measured level target function head tail
      (mapped source target function tail)).path
  length_eq := by
    change (branch_beta_measured level target function head tail
      (mapped source target function tail)).path.length + 1 = 4
    rw [(branch_beta_measured level target function head tail
      (mapped source target function tail)).length_eq]

def mapped_nil_path (level : LevelExpr)
    (source target function : Tower.Tm n) :
    PathReduces level
      (mapped source target function (Intrinsic.nilApp source))
      (Intrinsic.nilApp target) :=
  (mapped_nil_measured level source target function).path

def mapped_cons_path (level : LevelExpr)
    (source target function head tail : Tower.Tm n) :
    PathReduces level
      (mapped source target function (Intrinsic.consApp source head tail))
      (Intrinsic.consApp target (.app function head)
        (mapped source target function tail)) :=
  (mapped_cons_measured level source target function head tail).path

@[simp] theorem mapped_nil_path_length (level : LevelExpr)
    (source target function : Tower.Tm n) :
    (mapped_nil_path level source target function).length = 1 := by
  exact (mapped_nil_measured level source target function).length_eq

@[simp] theorem mapped_cons_path_length (level : LevelExpr)
    (source target function head tail : Tower.Tm n) :
    (mapped_cons_path level source target function head tail).length = 4 := by
  exact (mapped_cons_measured level source target function head tail).length_eq

/-- The recursive native map path retains every declared iota and beta step. -/
private def mapped_encode_measured (level : LevelExpr)
    (source target function : Tower.Tm n) :
    (xs : List (Tower.Tm n)) →
      PathReduces.Measured level
        (mapped source target function (encode source xs))
        (encode target (xs.map (fun x => .app function x)))
        (4 * xs.length + 1)
  | [] => mapped_nil_measured level source target function
  | head :: tail =>
      PathReduces.Measured.castSteps
        ((mapped_cons_measured level source target function head
          (encode source tail)).trans
            ((mapped_encode_measured level source target function tail).appArg
              (.app (.app (.const Intrinsic.consName) target)
                (.app function head)))) (by simp; omega)

def mapped_encode_path (level : LevelExpr)
    (source target function : Tower.Tm n) (xs : List (Tower.Tm n)) :
    PathReduces level (mapped source target function (encode source xs))
      (encode target (xs.map (fun x => .app function x))) :=
  (mapped_encode_measured level source target function xs).path

@[simp] theorem mapped_encode_path_length (level : LevelExpr)
    (source target function : Tower.Tm n) (xs : List (Tower.Tm n)) :
    (mapped_encode_path level source target function xs).length =
      4 * xs.length + 1 := by
  exact (mapped_encode_measured level source target function xs).length_eq

private def applyMap_encode_measured (level : LevelExpr)
    (source target function : Tower.Tm n) (xs : List (Tower.Tm n)) :
    PathReduces.Measured level
      (applyMap source target function (encode source xs))
      (encode target (xs.map (fun x => .app function x)))
      (4 * xs.length + 5) :=
  PathReduces.Measured.castSteps
    ((applyMap_beta_measured level source target function
      (encode source xs)).trans
        (mapped_encode_measured level source target function xs)) (by omega)

def applyMap_encode_path (level : LevelExpr)
    (source target function : Tower.Tm n) (xs : List (Tower.Tm n)) :
    PathReduces level (applyMap source target function (encode source xs))
      (encode target (xs.map (fun x => .app function x))) :=
  (applyMap_encode_measured level source target function xs).path

@[simp] theorem applyMap_encode_path_length (level : LevelExpr)
    (source target function : Tower.Tm n) (xs : List (Tower.Tm n)) :
    (applyMap_encode_path level source target function xs).length =
      4 * xs.length + 5 := by
  exact (applyMap_encode_measured level source target function xs).length_eq

def encode_pointwise_path (level : LevelExpr) (element : Tower.Tm n)
    (f g : Tower.Tm n → Tower.Tm n) :
    (xs : List (Tower.Tm n)) →
    (∀ x ∈ xs, PathReduces level (f x) (g x)) →
      PathReduces level (encode element (xs.map f)) (encode element (xs.map g))
  | [], _ => .refl _
  | head :: tail, pointwise =>
      (((pointwise head List.mem_cons_self).appArg
          (.app (.const Intrinsic.consName) element)).appFun _).trans
        ((encode_pointwise_path level element f g tail
          (fun x member => pointwise x (List.mem_cons_of_mem _ member))).appArg _)

private def compose_beta_measured (level : LevelExpr) (f g x : Tower.Tm n) :
    PathReduces.Measured level (.app (compose f g) x)
      (.app f (.app g x)) 1 :=
  PathReduces.Measured.castEndpoints
    (PathReduces.Measured.beta level
      (.app (rename wk f) (.app (rename wk g) (.var 0))) x)
    (by simp [compose])
    (by simp only [inst0, subst, subst_rename, subst0_succ,
        subst0_zero, wk, subst_vars])

def compose_beta_path (level : LevelExpr) (f g x : Tower.Tm n) :
    PathReduces level (.app (compose f g) x) (.app f (.app g x)) :=
  (compose_beta_measured level f g x).path

@[simp] theorem compose_beta_path_length (level : LevelExpr)
    (f g x : Tower.Tm n) :
    (compose_beta_path level f g x).length = 1 := by
  exact (compose_beta_measured level f g x).length_eq

private def encode_pointwise_measured (level : LevelExpr)
    (element : Tower.Tm n) (f g : Tower.Tm n → Tower.Tm n) :
    (xs : List (Tower.Tm n)) →
    (∀ x ∈ xs, PathReduces.Measured level (f x) (g x) 1) →
      PathReduces.Measured level
        (encode element (xs.map f)) (encode element (xs.map g)) xs.length
  | [], _ =>
      { path := .refl _
        length_eq := rfl }
  | head :: tail, pointwise =>
      PathReduces.Measured.castSteps
        ((((pointwise head List.mem_cons_self).appArg
            (.app (.const Intrinsic.consName) element)).appFun _).trans
          ((encode_pointwise_measured level element f g tail
            (fun x member =>
              pointwise x (List.mem_cons_of_mem _ member))).appArg _))
        (by simp; omega)

/-- The two map programs, their common constructor spine, and the exact cost
of both retained executions. -/
private def fusion_common_output_measured (level : LevelExpr)
    (a b c f g : Tower.Tm n) (xs : List (Tower.Tm n)) :
    PathReduces.Measured level
        (applyMap b c f (applyMap a b g (encode a xs)))
        (encode c (xs.map (fun x => .app f (.app g x))))
        (8 * xs.length + 10) ×
      PathReduces.Measured level
        (applyMap a c (compose f g) (encode a xs))
        (encode c (xs.map (fun x => .app f (.app g x))))
        (5 * xs.length + 5) := by
  constructor
  · let inner := (applyMap_encode_measured level a b g xs).appArg
      (.app (.app (.app (liftClosed nativeMapTerm) b) c) f)
    let outer := applyMap_encode_measured level b c f
      (xs.map (fun x => .app g x))
    let aligned : PathReduces.Measured level
        (applyMap b c f (encode b (xs.map (fun x => Tm.app g x))))
        (encode c (xs.map (fun x => Tm.app f (Tm.app g x))))
        (4 * (xs.map (fun x => Tm.app g x)).length + 5) :=
      PathReduces.Measured.castEndpoints outer rfl (by
        simp only [List.map_map, Function.comp_def])
    exact PathReduces.Measured.castSteps (inner.trans aligned) (by
      simp only [List.length_map]
      omega)
  · let mapped := applyMap_encode_measured level a c (compose f g) xs
    let pointwise := encode_pointwise_measured level c _ _ xs
      (fun x _ => compose_beta_measured level f g x)
    exact PathReduces.Measured.castSteps (mapped.trans pointwise) (by omega)

/-- Both actual map programs converge while retaining their distinct ordered
primitive-step histories. -/
def fusion_common_output_paths (level : LevelExpr)
    (a b c f g : Tower.Tm n) (xs : List (Tower.Tm n)) :
    PathReduces level
        (applyMap b c f (applyMap a b g (encode a xs)))
        (encode c (xs.map (fun x => .app f (.app g x)))) ×
      PathReduces level
        (applyMap a c (compose f g) (encode a xs))
        (encode c (xs.map (fun x => .app f (.app g x)))) :=
  ((fusion_common_output_measured level a b c f g xs).1.path,
    (fusion_common_output_measured level a b c f g xs).2.path)

/-- Erasing the proof-relevant fusion paths gives the prior
proposition-valued reachability pair. -/
theorem fusion_paths_erase (level : LevelExpr)
    (a b c f g : Tower.Tm n) (xs : List (Tower.Tm n)) :
    Reduces level
        (applyMap b c f (applyMap a b g (encode a xs)))
        (encode c (xs.map (fun x => .app f (.app g x)))) ∧
      Reduces level
        (applyMap a c (compose f g) (encode a xs))
        (encode c (xs.map (fun x => .app f (.app g x)))) := by
  exact ⟨(fusion_common_output_paths level a b c f g xs).1.erase,
    (fusion_common_output_paths level a b c f g xs).2.erase⟩

/-- The exact work of both retained executions, for every finite input. -/
theorem fusion_common_output_path_lengths (level : LevelExpr)
    (a b c f g : Tower.Tm n) (xs : List (Tower.Tm n)) :
    (fusion_common_output_paths level a b c f g xs).1.length =
        8 * xs.length + 10 ∧
      (fusion_common_output_paths level a b c f g xs).2.length =
        5 * xs.length + 5 := by
  exact ⟨(fusion_common_output_measured level a b c f g xs).1.length_eq,
    (fusion_common_output_measured level a b c f g xs).2.length_eq⟩

/-- On the smallest nonempty workload, the unfused program retains eighteen
primitive beta/iota occurrences while the fused program retains ten.  Equal
endpoints therefore do not erase the cost distinction. -/
theorem singleton_fusion_path_lengths (level : LevelExpr)
    (a b c f g x : Tower.Tm n) :
    (fusion_common_output_paths level a b c f g [x]).1.length = 18 ∧
      (fusion_common_output_paths level a b c f g [x]).2.length = 10 := by
  exact fusion_common_output_path_lengths level a b c f g [x]

#print axioms PathReduces.erase_trans
#print axioms branch_beta_path
#print axioms applyMap_beta_path
#print axioms mapped_encode_path
#print axioms fusion_common_output_paths
#print axioms fusion_paths_erase
#print axioms fusion_common_output_path_lengths
#print axioms singleton_fusion_path_lengths

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.IntrinsicNativeListMapExecutionPath
