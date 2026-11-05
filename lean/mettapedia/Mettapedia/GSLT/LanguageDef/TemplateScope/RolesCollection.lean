import Mettapedia.GSLT.LanguageDef.TemplateScope.RolesBoundary

/-!
# Binding by role: collection is an observation

A relation refines the store; refinements commute (`solveConj_perm`).  A
collection (`collapse`) does not refine: it reports the bag of answers of a
completed search, read against the store at the moment it is taken.  It is an
observation, and an observation of a store that is still being refined depends
on when it is taken.

* `stratified_stable` — an observation that reads only the shared names `Ns`
  does not change under any refinement once those names are determined.
* `schedules_agree` — so, for a frame with constraints and one collection,
  collecting first and constraining first give the same result when the
  collection's shared names are determined at the start.
* `unstratified_differs` — **the condition is needed**: for every undetermined
  shared name there is an observation reading only `Ns` on which the two
  schedules differ.
* `stratified_meaning` — **the stratification rule removes the order
  dependence**: when the collection is taken after the frame's constraints (the
  rule: a collection waits for the relations that bind its shared names), every
  order of those constraints gives the declarative meaning: the observation of
  the conjunction's solution.
* `measured_order_effect` — the measurement on PeTTa in this model: collecting
  `(p $x)` before constraining `$x` to 2 gives `(1 2)`; constraining first gives
  `(2)`.
* `collect_in_evaluator` — the same effect with the evaluator of
  `TemplateScope.Evaluation`, which also keeps multiplicity: a space with
  `(p 1)` twice collects `(1 1 2)`.

What escapes a collection: only its bag.  The collected search is reusable code
run once more, so its own names are private to the run (`private_inside`),
and the store outside is the store it was taken against (`collectFirst`,
`constrainFirst` return it unchanged by the observation).
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.Roles.Collection

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

variable {N V R : Type*}

/-- An observation that reads only the names `Ns` of a store. -/
def ReadsOnly (Ns : List N) (obs : Store N V → R) : Prop :=
  ∀ s s' : Store N V, (∀ n ∈ Ns, s n = s' n) → obs s = obs s'

/-- The names `Ns` are determined in a store. -/
def Determined (Ns : List N) (s : Store N V) : Prop :=
  ∀ n ∈ Ns, (s n).isSome

/-- A refinement keeps every determined value. -/
theorem determined_stable {Ns : List N} {s s' : Store N V} (hd : Determined Ns s) (h : s ⊑ s') :
    ∀ n ∈ Ns, s' n = s n := by
  intro n hn
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hd n hn)
  rw [hv, h n v hv]

/-- **A stratified observation is stable**: once its shared names are
determined, no refinement changes it. -/
theorem stratified_stable {Ns : List N} {obs : Store N V → R} {s s' : Store N V}
    (hobs : ReadsOnly Ns obs) (hd : Determined Ns s) (h : s ⊑ s') : obs s' = obs s :=
  hobs s' s (determined_stable hd h)

variable [DecidableEq N] [DecidableEq V]

/-- Collect first, then run the constraints. -/
def collectFirst (obs : Store N V → R) (s : Store N V) (cs : Steps N V) :
    Option (R × Store N V) :=
  (refineRun s cs).map fun s' => (obs s, s')

/-- Run the constraints, then collect. -/
def constrainFirst (obs : Store N V → R) (s : Store N V) (cs : Steps N V) :
    Option (R × Store N V) :=
  (refineRun s cs).map fun s' => (obs s', s')

/-- **The schedules agree on a stratified collection.** -/
theorem schedules_agree {Ns : List N} {obs : Store N V → R} {s : Store N V}
    (hobs : ReadsOnly Ns obs) (hd : Determined Ns s) (cs : Steps N V) :
    collectFirst obs s cs = constrainFirst obs s cs := by
  unfold collectFirst constrainFirst
  cases h : refineRun s cs with
  | none => rfl
  | some s' =>
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
      exact (stratified_stable hobs hd (refineRun_mono h)).symm

/-- **The condition is needed.**  If a shared name is undetermined, the
observation of that name separates the schedules for any value it may take. -/
theorem unstratified_differs {Ns : List N} {s : Store N V} {n : N} (hn : n ∈ Ns)
    (hs : s n = none) (v : V) :
    ∃ obs : Store N V → Option V, ReadsOnly Ns obs ∧
      collectFirst obs s [(n, v)] ≠ constrainFirst obs s [(n, v)] := by
  refine ⟨fun t => t n, fun t t' h => h n hn, ?_⟩
  simp [collectFirst, constrainFirst, refineRun, refineStep, hs]

/-- **The stratification rule.**  A collection taken after the constraints of
its frame observes the conjunction's solution, in every order of the
constraints. -/
theorem stratified_meaning (obs : Store N V → R) {cs cs' : Steps N V} (hp : cs.Perm cs') :
    constrainFirst obs Store.empty cs' = (solveConj cs).map fun s => (obs s, s) := by
  unfold constrainFirst
  rw [refineRun_empty_eq_solveConj, solveConj_perm hp.symm]

/-- And the collection is order-independent across those orders. -/
theorem stratified_perm (obs : Store N V → R) {cs cs' : Steps N V} (hp : cs.Perm cs') :
    constrainFirst obs Store.empty cs = constrainFirst obs Store.empty cs' := by
  rw [stratified_meaning obs (List.Perm.refl cs), stratified_meaning obs hp]

/-! ## The measured order effect -/

/-- The space `(p 1) (p 2)` collected through `(p $x)`, with `$x` the one
shared name. -/
def collectP (s : Store Unit ℕ) : List ℕ :=
  match s () with
  | none => [1, 2]
  | some v => [1, 2].filter fun w => w = v

theorem collectP_reads : ReadsOnly [()] collectP := by
  intro s s' h
  simp only [collectP, h () (List.mem_singleton_self _)]

/-- **The PeTTa measurement in the model**: collecting before constraining `$x`
to 2 gives `(1 2)`; constraining first gives `(2)`.  The collection is not
stratified: `$x` is undetermined when it is taken first. -/
theorem measured_order_effect :
    (collectFirst collectP Store.empty [((), 2)]).map Prod.fst = some [1, 2] ∧
      (constrainFirst collectP Store.empty [((), 2)]).map Prod.fst = some [2] ∧
      ¬ Determined [()] (Store.empty : Store Unit ℕ) := by
  refine ⟨rfl, rfl, ?_⟩
  intro h
  simpa [Store.empty] using h () (List.mem_singleton_self _)

/-! ## The same effect in the evaluator -/

section Evaluator

open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.QueryCorpus

/-- The space `(p 1) (p 1) (p 2)`. -/
def psDup : A := .alt (ap (k .p) (k .n1)) (.alt (ap (k .p) (k .n1)) (ap (k .p) (k .n2)))

/-- `(match psDup (p $x) $x)` elaborated under clause units: its `$x` is the
form's slot `([], x)`. -/
def queryX : T := elabCfg cfgLF [] (QSrc.toSrc ruleCU [] (qry (ap (k .p) (sv .x)) psDup (sv .x)))

/-- The bag the evaluator collects for `queryX` from a store. -/
def collectEval (s : GStore QSy (Slot QSp)) : Option (List T) :=
  (run cfgLF.disc (QueryCorpus.progOf ruleCU) 80 [] s queryX).map
    (List.map fun r => act r.2 r.1)

/-- The constraint `$x = 2` on the form's slot. -/
def constrainX : Steps (Nm (Slot QSp)) (GVal QSy (Slot QSp)) := [(.src ([], .x), .sym .n2)]

/-- **The order effect in the evaluator, with multiplicity kept**: collected
first, the bag is `(1 1 2)`; after the constraint, `(2)`. -/
theorem collect_in_evaluator :
    (collectFirst collectEval Store.empty constrainX).map Prod.fst =
        some (some [kT .n1, kT .n1, kT .n2]) ∧
      (constrainFirst collectEval Store.empty constrainX).map Prod.fst = some (some [kT .n2]) := by
  constructor <;> decide +kernel

end Evaluator

end Mettapedia.GSLT.LanguageDef.TemplateScope.Roles.Collection
