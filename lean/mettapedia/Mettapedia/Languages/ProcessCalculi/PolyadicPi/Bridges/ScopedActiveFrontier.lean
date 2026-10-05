import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Basic
import Mathlib.Data.List.Perm.Basic

/-!
# Finite active frontiers under private pi scopes

The frontier is a normal form for the existing intrinsic process syntax and
its existing structural equations. Only parallel composition and restriction
are exposed; inputs and replicated servers remain opaque active atoms. A
name-only telescope records exactly how each operand reaches the shared scope.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedActiveFrontier

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi

/-- A finite sequence of the existing name restrictions, with its exact
source and destination contexts retained in the indices. -/
inductive Scope : Ctx sig → Ctx sig → Type where
  | nil {Γ : Ctx sig} : Scope Γ Γ
  | bind {Γ Δ : Ctx sig} : Scope (.nm :: Γ) Δ → Scope Γ Δ

namespace Scope

def inclusion : {Γ Δ : Ctx sig} → Scope Γ Δ → Ren sig Γ Δ
  | _, _, .nil => fun _ name => name
  | _, _, .bind rest => fun sort name => rest.inclusion sort (.succ name)

def close : {Γ Δ : Ctx sig} → Scope Γ Δ → Proc Δ → Proc Γ
  | _, _, .nil, body => body
  | _, _, .bind rest, body => nu (rest.close body)

def append : {Γ Δ Θ : Ctx sig} → Scope Γ Δ → Scope Δ Θ → Scope Γ Θ
  | _, _, _, .nil, later => later
  | _, _, _, .bind rest, later => .bind (rest.append later)

@[simp] theorem close_append : ∀ {Γ Δ Θ : Ctx sig} (first : Scope Γ Δ)
    (second : Scope Δ Θ) (body : Proc Θ),
    (first.append second).close body = first.close (second.close body)
  | _, _, _, .nil, _, _ => rfl
  | _, _, _, .bind rest, later, body => by
      change nu ((rest.append later).close body) = nu (rest.close (later.close body))
      rw [close_append]

/-- The same private telescope over a different ambient context. -/
def rebase : {Γ Δ : Ctx sig} → Scope Γ Δ → (base : Ctx sig) →
    Σ world : Ctx sig, Scope base world
  | _, _, .nil, base => ⟨base, .nil⟩
  | _, _, .bind rest, base =>
      ⟨(rest.rebase (.nm :: base)).1, .bind (rest.rebase (.nm :: base)).2⟩

/-- Reindex an operand's private names identically and its ambient names
along the supplied map into the common world. -/
def rebaseRen : {Γ Δ Θ : Ctx sig} → (scope : Scope Γ Δ) → Ren sig Γ Θ →
    Ren sig Δ (scope.rebase Θ).1
  | _, _, _, .nil, environment => environment
  | _, _, _, .bind rest, environment => rest.rebaseRen (liftRen environment [.nm])

/-- A shared ambient name reaches the same place whether it is first
included into the private telescope or first moved into the new base. -/
theorem rebaseRen_inclusion : ∀ {Γ Δ Θ : Ctx sig} (scope : Scope Γ Δ)
    (environment : Ren sig Γ Θ) (sort : Srt) (name : Var Γ sort),
    scope.rebaseRen environment sort (scope.inclusion sort name) =
      (scope.rebase Θ).2.inclusion sort (environment sort name)
  | _, _, _, .nil, _, _, _ => rfl
  | _, _, _, .bind rest, environment, sort, name =>
      rest.rebaseRen_inclusion (liftRen environment [.nm]) sort (.succ name)

theorem close_rebase : ∀ {Γ Δ Θ : Ctx sig} (scope : Scope Γ Δ)
    (environment : Ren sig Γ Θ) (body : Proc Δ),
    rename environment (scope.close body) =
      (scope.rebase Θ).2.close (rename (scope.rebaseRen environment) body)
  | _, _, _, .nil, _, _ => rfl
  | _, _, _, .bind rest, environment, body => by
      change rename environment (nu (rest.close body)) =
        nu ((rest.rebase (.nm :: _)).2.close
          (rename (rest.rebaseRen (liftRen environment [.nm])) body))
      rw [rename_nu, close_rebase]

theorem congr : ∀ {Γ Δ : Ctx sig} (scope : Scope Γ Δ) {first second : Proc Δ},
    StructuralEq first second → StructuralEq (scope.close first) (scope.close second)
  | _, _, .nil, _, _, equal => equal
  | _, _, .bind rest, _, _, equal => .nu (rest.congr equal)

/-- Closing a selected real firing retains all enclosing restrictions. -/
theorem step : ∀ {Γ Δ : Ctx sig} (scope : Scope Γ Δ) {first second : Proc Δ},
    Step first second → Step (scope.close first) (scope.close second)
  | _, _, .nil, _, _, firing => firing
  | _, _, .bind rest, _, _, firing => .nu (rest.step firing)

/-- Extrude one operand's complete telescope over an untouched parallel
frame. The frame sees only the old ambient names. -/
theorem par_left : ∀ {Γ Δ : Ctx sig} (scope : Scope Γ Δ) (body : Proc Δ)
    (frame : Proc Γ),
    StructuralEq (par (scope.close body) frame)
      (scope.close (par body (rename scope.inclusion frame)))
  | _, _, .nil, body, frame => by
      simp only [close, inclusion, rename_id]
      exact .refl _
  | _, _, .bind rest, body, frame => by
      change StructuralEq (par (nu (rest.close body)) frame)
        (nu (rest.close (par body (rename (fun sort name => rest.inclusion sort (.succ name)) frame))))
      refine .trans (.nuPar _ _) (.nu ?_)
      have extrusion := rest.par_left body (weaken frame)
      have shifted : rename rest.inclusion (weaken frame) =
          rename (fun sort name => rest.inclusion sort (.succ name)) frame := by
        rw [weaken, rename_comp]
      rw [shifted] at extrusion
      exact extrusion

theorem par_right {Γ Δ : Ctx sig} (scope : Scope Γ Δ) (body : Proc Δ)
    (frame : Proc Γ) :
    StructuralEq (par frame (scope.close body))
      (scope.close (par (rename scope.inclusion frame) body)) :=
  .trans (.parComm _ _) (.trans (scope.par_left body frame)
    (scope.congr (.parComm _ _)))

end Scope

/-- Parallel assembly keeps list occurrences, including equal atoms. -/
def parallel {Γ : Ctx sig} : List (Proc Γ) → Proc Γ
  | [] => nil
  | first :: rest => par first (parallel rest)

private theorem nil_par {Γ : Ctx sig} (process : Proc Γ) :
    StructuralEq (par nil process) process :=
  .trans (.parComm _ _) (.parUnit _)

theorem parallel_append {Γ : Ctx sig} (first second : List (Proc Γ)) :
    StructuralEq (par (parallel first) (parallel second)) (parallel (first ++ second)) := by
  induction first with
  | nil => exact nil_par _
  | cons head rest ih =>
      exact .trans (.parAssoc _ _ _) (.par (.refl _) ih)

theorem parallel_rename {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (atoms : List (Proc Γ)) :
    rename environment (parallel atoms) = parallel (atoms.map (rename environment)) := by
  induction atoms with
  | nil => rfl
  | cons first rest ih =>
      change rename environment (par first (parallel rest)) =
        par (rename environment first) (parallel (rest.map (rename environment)))
      rw [rename_par, ih]

/-- A finite active layer and the telescope that closes its exact world. -/
structure Frontier (Γ : Ctx sig) where
  world : Ctx sig
  scope : Scope Γ world
  atoms : List (Proc world)

def Frontier.term {Γ : Ctx sig} (frontier : Frontier Γ) : Proc Γ :=
  frontier.scope.close (parallel frontier.atoms)

def singleton {Γ : Ctx sig} (atom : Proc Γ) : Frontier Γ :=
  ⟨Γ, .nil, [atom]⟩

def restrict {Γ : Ctx sig} (body : Frontier (.nm :: Γ)) : Frontier Γ :=
  ⟨body.world, .bind body.scope, body.atoms⟩

/-- Exact common-world merge. The second operand keeps its private binders;
its ambient variables are reindexed through the first operand's telescope. -/
def merge {Γ : Ctx sig} (first second : Frontier Γ) : Frontier Γ :=
  let later := second.scope.rebase first.world
  ⟨later.1, first.scope.append later.2,
    first.atoms.map (rename later.2.inclusion) ++
      second.atoms.map (rename (second.scope.rebaseRen first.scope.inclusion))⟩

theorem singleton_term {Γ : Ctx sig} (process : Proc Γ) :
    StructuralEq process (singleton process).term := .symm (.parUnit _)

theorem merge_term {Γ : Ctx sig} (first second : Frontier Γ) :
    StructuralEq (par first.term second.term) (merge first second).term := by
  let later := second.scope.rebase first.world
  have outside := first.scope.par_left (parallel first.atoms) second.term
  have secondReading : rename first.scope.inclusion second.term =
      later.2.close (parallel
        (second.atoms.map (rename (second.scope.rebaseRen first.scope.inclusion)))) := by
    rw [Frontier.term, Scope.close_rebase, parallel_rename]
  rw [secondReading] at outside
  have inside := later.2.par_right
    (parallel (second.atoms.map (rename (second.scope.rebaseRen first.scope.inclusion))))
    (parallel first.atoms)
  rw [parallel_rename] at inside
  refine .trans outside (.trans (first.scope.congr inside) ?_)
  change StructuralEq
    (first.scope.close (later.2.close
      (par (parallel (first.atoms.map (rename later.2.inclusion)))
        (parallel (second.atoms.map (rename (second.scope.rebaseRen first.scope.inclusion)))))))
    ((first.scope.append later.2).close
      (parallel (first.atoms.map (rename later.2.inclusion) ++
        second.atoms.map (rename (second.scope.rebaseRen first.scope.inclusion)))))
  rw [Scope.close_append]
  exact first.scope.congr (later.2.congr (parallel_append _ _))

/-- Neither private scope extension nor common-world merge identifies old
variables. Equal source names, however, remain equal. -/
theorem Scope.inclusion_injective : ∀ {Γ Δ : Ctx sig} (scope : Scope Γ Δ)
    (sort : Srt), Function.Injective (scope.inclusion sort)
  | _, _, .nil, _ => fun _ _ equal => equal
  | _, _, .bind rest, sort => by
      intro first second equal
      have lifted := rest.inclusion_injective sort equal
      exact Var.succ.inj lifted

theorem Scope.rebaseRen_injective : ∀ {Γ Δ Θ : Ctx sig} (scope : Scope Γ Δ)
    (environment : Ren sig Γ Θ)
    (_faithful : ∀ sort, Function.Injective (environment sort))
    (sort : Srt), Function.Injective (scope.rebaseRen environment sort)
  | _, _, _, .nil, _, faithful, sort => faithful sort
  | _, _, _, .bind rest, environment, faithful, sort => by
      apply rest.rebaseRen_injective
      intro sort first second equal
      cases first with
      | zero =>
          cases second with
          | zero => rfl
          | succ second => cases equal
      | succ first =>
          cases second with
          | zero => cases equal
          | succ second => exact congrArg Var.succ (faithful sort (Var.succ.inj equal))

/-- Left and right operand occurrences enter the very same sorted world. -/
def mergeLeft {Γ : Ctx sig} (first second : Frontier Γ) :
    Ren sig first.world (merge first second).world :=
  (second.scope.rebase first.world).2.inclusion

def mergeRight {Γ : Ctx sig} (first second : Frontier Γ) :
    Ren sig second.world (merge first second).world :=
  second.scope.rebaseRen first.scope.inclusion

/-- Both operands retain exactly the same interpretation of each name
that was shared before private-scope extrusion. -/
theorem merge_ambient_name {Γ : Ctx sig} (first second : Frontier Γ)
    (sort : Srt) (name : Var Γ sort) :
    mergeLeft first second sort (first.scope.inclusion sort name) =
      mergeRight first second sort (second.scope.inclusion sort name) :=
  (second.scope.rebaseRen_inclusion first.scope.inclusion sort name).symm

theorem merge_occurrence_count {Γ : Ctx sig} (first second : Frontier Γ) :
    (merge first second).atoms.length = first.atoms.length + second.atoms.length := by
  simp only [merge, List.length_append, List.length_map]

theorem merge_left_member {Γ : Ctx sig} (first second : Frontier Γ)
    (atom : Proc first.world) (member : atom ∈ first.atoms) :
    rename (mergeLeft first second) atom ∈ (merge first second).atoms := by
  change rename (mergeLeft first second) atom ∈
    first.atoms.map (rename (mergeLeft first second)) ++
      second.atoms.map (rename (mergeRight first second))
  exact List.mem_append_left _ (List.mem_map.mpr ⟨atom, member, rfl⟩)

theorem merge_right_member {Γ : Ctx sig} (first second : Frontier Γ)
    (atom : Proc second.world) (member : atom ∈ second.atoms) :
    rename (mergeRight first second) atom ∈ (merge first second).atoms := by
  change rename (mergeRight first second) atom ∈
    first.atoms.map (rename (mergeLeft first second)) ++
      second.atoms.map (rename (mergeRight first second))
  exact List.mem_append_right _ (List.mem_map.mpr ⟨atom, member, rfl⟩)

/-- Flatten exactly the active parallel/restriction spine. An input body or
replicated server body is not traversed until execution activates it. -/
def normalize : {Γ : Ctx sig} → Proc Γ → Frontier Γ
  | Γ, .op .nil .nil => ⟨Γ, .nil, []⟩
  | _, .op .par (.cons first (.cons second .nil)) =>
      merge (normalize first) (normalize second)
  | _, .op .nu (.cons body .nil) => restrict (normalize body)
  | _, .var name => singleton (.var name)
  | _, .op .inp1 (.cons channel (.cons body .nil)) => singleton (inp1 channel body)
  | _, .op .inp2 (.cons channel (.cons body .nil)) => singleton (inp2 channel body)
  | _, .op .out1 (.cons channel (.cons datum .nil)) => singleton (out1 channel datum)
  | _, .op .out2 (.cons channel (.cons first (.cons second .nil))) =>
      singleton (out2 channel first second)
  | _, .op .rep (.cons body .nil) => singleton (rep body)
termination_by _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

@[simp] theorem normalize_par {Γ : Ctx sig} (first second : Proc Γ) :
    normalize (par first second) = merge (normalize first) (normalize second) := by
  rw [par, normalize]

@[simp] theorem normalize_nu {Γ : Ctx sig} (body : Proc (.nm :: Γ)) :
    normalize (nu body) = restrict (normalize body) := by rw [nu, normalize]

@[simp] theorem normalize_inp1 {Γ : Ctx sig} (channel : Name Γ)
    (body : Proc (.nm :: Γ)) :
    normalize (inp1 channel body) = singleton (inp1 channel body) := by rw [inp1, normalize]; rfl

@[simp] theorem normalize_inp2 {Γ : Ctx sig} (channel : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) :
    normalize (inp2 channel body) = singleton (inp2 channel body) := by rw [inp2, normalize]; rfl

@[simp] theorem normalize_rep {Γ : Ctx sig} (body : Proc Γ) :
    normalize (rep body) = singleton (rep body) := by rw [rep, normalize]; rfl

@[simp] theorem normalize_out1 {Γ : Ctx sig} (channel datum : Name Γ) :
    normalize (out1 channel datum) = singleton (out1 channel datum) := by
  rw [out1, normalize]
  rfl

@[simp] theorem normalize_out2 {Γ : Ctx sig} (channel first second : Name Γ) :
    normalize (out2 channel first second) = singleton (out2 channel first second) := by
  rw [out2, normalize]
  rfl

@[simp] theorem normalize_nil {Γ : Ctx sig} :
    normalize (nil : Proc Γ) = ⟨Γ, .nil, []⟩ := by rw [nil, normalize]

/-- Every normal form is proved from the original process's actual scope
and parallel equations, without a change of operational authority. -/
theorem normalization : ∀ {Γ : Ctx sig} (process : Proc Γ),
    StructuralEq process (normalize process).term
  | _, .var name => by
      rw [normalize]
      exact singleton_term _
  | _, .op .nil .nil => by
      rw [normalize]
      exact .refl _
  | _, .op .par (.cons first (.cons second .nil)) => by
      rw [normalize]
      exact .trans (.par (normalization first) (normalization second))
        (merge_term _ _)
  | _, .op .nu (.cons body .nil) => by
      rw [normalize]
      change StructuralEq (nu body) (nu (normalize body).term)
      exact .nu (normalization body)
  | _, .op .inp1 (.cons channel (.cons body .nil)) => by
      rw [normalize]
      exact singleton_term _
  | _, .op .inp2 (.cons channel (.cons body .nil)) => by
      rw [normalize]
      exact singleton_term _
  | _, .op .out1 (.cons channel (.cons datum .nil)) => by
      rw [normalize]
      exact singleton_term _
  | _, .op .out2 (.cons channel (.cons first (.cons second .nil))) => by
      rw [normalize]
      exact singleton_term _
  | _, .op .rep (.cons body .nil) => by
      rw [normalize]
      exact singleton_term _
termination_by _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

/-- Reordering active occurrences does not identify duplicate processes. -/
theorem parallel_perm {Γ : Ctx sig} {first second : List (Proc Γ)}
    (permutation : first.Perm second) : StructuralEq (parallel first) (parallel second) := by
  induction permutation with
  | nil => exact .refl _
  | cons first _ ih => exact .par (.refl first) ih
  | swap first second rest =>
      exact .trans (.symm (.parAssoc _ _ _))
        (.trans (.par (.parComm _ _) (.refl _)) (.parAssoc _ _ _))
  | trans _ _ firstIH secondIH => exact .trans firstIH secondIH

/-- Select two unary occurrences in the normalized common world. Every
remaining occurrence and every private scope is retained in the endpoint. -/
theorem Frontier.unary_pair {Γ : Ctx sig} (frontier : Frontier Γ)
    (channel datum : Name frontier.world) (body : Proc (.nm :: frontier.world))
    (remaining : List (Proc frontier.world))
    (selected : frontier.atoms.Perm (out1 channel datum :: inp1 channel body :: remaining)) :
    StepModulo frontier.term
      (frontier.scope.close (par (inst body datum) (parallel remaining))) := by
  refine ⟨frontier.scope.close (par (par (out1 channel datum) (inp1 channel body))
    (parallel remaining)), _, ?_, frontier.scope.step (.parL _ (.comm1 _ _ _)), .refl _⟩
  exact frontier.scope.congr (.trans (parallel_perm selected) (.symm (.parAssoc _ _ _)))

theorem Frontier.binary_pair {Γ : Ctx sig} (frontier : Frontier Γ)
    (channel first second : Name frontier.world)
    (body : Proc (.nm :: .nm :: frontier.world)) (remaining : List (Proc frontier.world))
    (selected : frontier.atoms.Perm
      (out2 channel first second :: inp2 channel body :: remaining)) :
    StepModulo frontier.term
      (frontier.scope.close (par (openPair body first second) (parallel remaining))) := by
  refine ⟨frontier.scope.close (par (par (out2 channel first second) (inp2 channel body))
    (parallel remaining)), _, ?_, frontier.scope.step (.parL _ (.comm2 _ _ _ _)), .refl _⟩
  exact frontier.scope.congr (.trans (parallel_perm selected) (.symm (.parAssoc _ _ _)))

/-- A persistent receiver is unfolded only for the selected request. The
original listener survives outside its received-name binder. -/
theorem Frontier.unary_server {Γ : Ctx sig} (frontier : Frontier Γ)
    (channel datum : Name frontier.world) (body : Proc (.nm :: frontier.world))
    (remaining : List (Proc frontier.world))
    (selected : frontier.atoms.Perm
      (out1 channel datum :: rep (inp1 channel body) :: remaining)) :
    StepModulo frontier.term
      (frontier.scope.close (par (inst body datum)
        (par (rep (inp1 channel body)) (parallel remaining)))) := by
  refine ⟨frontier.scope.close (par (par (out1 channel datum) (inp1 channel body))
    (par (rep (inp1 channel body)) (parallel remaining))), _, ?_,
    frontier.scope.step (.parL _ (.comm1 _ _ _)), .refl _⟩
  apply frontier.scope.congr
  refine .trans (parallel_perm selected) ?_
  refine .trans (.par (.refl _) (.par (.repUnfold _) (.refl _))) ?_
  exact .trans (.par (.refl _) (.parAssoc _ _ _)) (.symm (.parAssoc _ _ _))

/-- The unary pair theorem starts at the original process, not only at its
normal form. Its result is the exact scoped assembly above. -/
theorem unary_pair {Γ : Ctx sig} (process : Proc Γ)
    (channel datum : Name (normalize process).world)
    (body : Proc (.nm :: (normalize process).world))
    (remaining : List (Proc (normalize process).world))
    (selected : (normalize process).atoms.Perm
      (out1 channel datum :: inp1 channel body :: remaining)) :
    StepModulo process ((normalize process).scope.close
      (par (inst body datum) (parallel remaining))) := by
  obtain ⟨redex, endpoint, before, firing, after⟩ :=
    (normalize process).unary_pair channel datum body remaining selected
  exact ⟨redex, endpoint, .trans (normalization process) before, firing, after⟩

theorem binary_pair {Γ : Ctx sig} (process : Proc Γ)
    (channel first second : Name (normalize process).world)
    (body : Proc (.nm :: .nm :: (normalize process).world))
    (remaining : List (Proc (normalize process).world))
    (selected : (normalize process).atoms.Perm
      (out2 channel first second :: inp2 channel body :: remaining)) :
    StepModulo process ((normalize process).scope.close
      (par (openPair body first second) (parallel remaining))) := by
  obtain ⟨redex, endpoint, before, firing, after⟩ :=
    (normalize process).binary_pair channel first second body remaining selected
  exact ⟨redex, endpoint, .trans (normalization process) before, firing, after⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedActiveFrontier
