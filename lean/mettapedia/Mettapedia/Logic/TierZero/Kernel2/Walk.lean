import Mettapedia.Logic.TierZero.Kernel2.Claims

/-!
# The kernel's step at a node, and the walk in order

What kernel-v2 does at a node `(N RULE CHILDREN)`: read the children's theorems, match the rule's
premises against them in order (binding its formals), and build the conclusion
(`nodeStep`). `ChildBound.runCB` does more at a node: it also rebuilds the instance's premises and
discharges them against the children. For the presentations of rule tables the extra work never
changes the outcome, because side conditions consume no child and the matcher's instance has
exactly the children's judgments as premises:

* `runT_eq_runCB`: the walk by `nodeStep` is `ChildBound.runCB` with the kernel's matcher; so the
  verdict of a claim computed by this walk (`Claim.verdictT`) is `Claim.verdict`
  (`verdictT_eq_verdict`), and its soundness and completeness are those of `Claims`.

Example: at `ax-mp` with children proving `wff ph`, `wff ps`, `|- ph`, `|- (ph → ps)`, the step
binds `ph, ps` and builds `|- ps`; it never rebuilds the four premises.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Kernel2

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Mettapedia.Logic.TierZero

variable {R : Type}

/-- The conclusion of a rule from its children's judgments: match, then build. -/
def ruleStep (fr : Frame) (ru : Rule) (js : List Tm) : Option Tm :=
  match solveKinds fr ru.kinds emptySubst js with
  | some τ =>
      match (List.range ru.nformals).mapM τ with
      | some a => ru.concl.inst (substOf a)
      | none => none
  | none => none

/-- **The kernel's step at a node**: read the children's judgments, match the rule, build the
conclusion. -/
def nodeStep (env : Env R) (fr : Frame) (look : Kid → Option Tm) (r : R) (kids : List Kid) :
    Option Tm :=
  match kids.mapM look, env r with
  | some js, some ru => ruleStep fr ru js
  | _, _ => none

/-- The judgment a child names, on trees (`Kernel.lookup` at a presentation of trees). -/
def lookupT (hyps done : List Tm) : Kid → Option Tm
  | .hyp i => hyps[i]?
  | .node n => done[n]?

theorem lookupT_eq (env : Env R) (fr : Frame) (hyps done : List Tm) :
    lookupT hyps done = lookup (P := presOf env fr) hyps done := by
  funext k; cases k <;> rfl

/-- **The walk in order**, node by node. -/
def runT (env : Env R) (fr : Frame) (hyps : List Tm) : List Tm → List (R × List Kid) → Option (List Tm)
  | done, [] => some done
  | done, (r, kids) :: rest =>
      match nodeStep env fr (lookupT hyps done) r kids with
      | some c => runT env fr hyps (done ++ [c]) rest
      | none => none

/-- With no side-condition judgments, discharging is reading the children. -/
theorem discharge_of_mapM {P : Presentation.{0}} [DecidableEq P.J] (noSide : ∀ p, P.side p = false)
    (look : Kid → Option P.J) :
    ∀ (ps : List P.J) (kids : List Kid), kids.mapM look = some ps → discharge look ps kids = true
  | [], [], _ => rfl
  | _ :: _, [], h => by simp at h
  | ps, k :: ks, h => by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
      cases hk : look k with
      | none => simp [hk] at h
      | some j =>
          cases hks : ks.mapM look with
          | none => simp [hk, hks] at h
          | some js =>
              simp only [hk, hks, Option.bind_some, Option.some.injEq] at h
              subst h
              simp [discharge, noSide, hk, discharge_of_mapM noSide look js ks hks]

/-- The conclusion of a rule instance is the instantiated conclusion pattern. -/
theorem instance_concl {fr : Frame} {ru : Rule} {a ps : List Tm} {c : Tm}
    (h : ru.instance fr a = some (ps, c)) : ru.concl.inst (substOf a) = some c := by
  unfold Rule.instance at h
  split at h
  · cases hi : instKinds fr (substOf a) ru.kinds with
    | none => rw [hi] at h; simp at h
    | some ps' =>
        cases hc : ru.concl.inst (substOf a) with
        | none => rw [hi, hc] at h; simp at h
        | some c' =>
            rw [hi, hc] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            rw [h.2]
  · cases h

theorem solveEnv_eq (env : Env R) (fr : Frame) (r : R) (js : List Tm) :
    solveEnv env fr r js = match env r with
      | some ru => ru.solve fr js
      | none => none := rfl

theorem matcherOf_solve (env : Env R) (fr : Frame) (wf : EnvDetermined env) :
    (matcherOf env fr wf).solve = solveEnv env fr := rfl

theorem ruleStep_of_solve {fr : Frame} {ru : Rule} {js a : List Tm} (h : ru.solve fr js = some a) :
    ruleStep fr ru js = ru.concl.inst (substOf a) := by
  unfold Rule.solve at h
  unfold ruleStep
  cases hτ : solveKinds fr ru.kinds emptySubst js with
  | none => rw [hτ] at h; cases h
  | some τ => rw [hτ] at h; simp only [h]

theorem ruleStep_of_solve_none {fr : Frame} {ru : Rule} {js : List Tm} (h : ru.solve fr js = none) :
    ruleStep fr ru js = none := by
  unfold Rule.solve at h
  unfold ruleStep
  cases hτ : solveKinds fr ru.kinds emptySubst js with
  | none => rfl
  | some τ => rw [hτ] at h; simp only [h]

/-- **The walk by the kernel's step is the children-bound walk.** -/
theorem runT_eq_runCB (env : Env R) (fr : Frame) (wf : EnvDetermined env) (hyps : List Tm) :
    ∀ (done : List Tm) (proof : List (R × List Kid)),
      runT env fr hyps done proof = ChildBound.runCB (matcherOf env fr wf) hyps done proof
  | done, [] => by simp only [runT, ChildBound.runCB]
  | done, (r, kids) :: rest => by
      simp only [runT, ChildBound.runCB, nodeStep, lookupT_eq env fr, matcherOf_solve]
      cases hk : kids.mapM (lookup (P := presOf env fr) hyps done) with
      | none => rfl
      | some js =>
          simp only [solveEnv]
          cases he : env r with
          | none => rfl
          | some ru =>
              simp only
              cases hs : ru.solve fr js with
              | none => simp [ruleStep_of_solve_none hs]
              | some a =>
                  obtain ⟨c, hc⟩ := solve_sound fr (wf r ru he) hs
                  have dis := discharge_of_mapM (P := presOf env fr) (fun _ => rfl)
                    (lookup (P := presOf env fr) hyps done) js kids hk
                  simp only [ruleStep_of_solve hs, instance_concl hc, hc, dis, ↓reduceIte]
                  exact runT_eq_runCB env fr wf hyps (done ++ [c]) rest

namespace Claim

/-- The verdict computed by the walk in order. -/
def verdictT (env : Env R) (c : Claim R) : Bool :=
  c.wellFormed &&
    match c.cbHyps, c.goal, c.translate with
    | some hs, some g, some (pf, rt) =>
        match runT env c.frame hs [] pf with
        | some done => decide (lookupT hs done rt = some g)
        | none => false
    | _, _, _ => false

theorem checkCB_eq_runT (env : Env R) (fr : Frame) (wf : EnvDetermined env) (hs : List Tm)
    (pf : List (R × List Kid)) (rt : Kid) (g : Tm) :
    ChildBound.checkCB (matcherOf env fr wf) hs pf rt g =
      match runT env fr hs [] pf with
      | some done => decide (lookupT hs done rt = some g)
      | none => false := by
  unfold ChildBound.checkCB
  rw [← runT_eq_runCB env fr wf hs [] pf]
  cases runT env fr hs [] pf with
  | none => rfl
  | some done => simp only [lookupT_eq env fr]

/-- **The walk in order computes the verdict.** -/
theorem verdictT_eq_verdict (env : Env R) (wf : EnvDetermined env) (c : Claim R) :
    c.verdictT env = c.verdict env wf := by
  unfold verdictT verdict
  rcases c.cbHyps with _ | hs <;> rcases c.goal with _ | g <;> rcases c.translate with _ | ⟨pf, rt⟩ <;>
    simp only [checkCB_eq_runT env c.frame wf]

end Claim

end Mettapedia.Logic.TierZero.Kernel2
