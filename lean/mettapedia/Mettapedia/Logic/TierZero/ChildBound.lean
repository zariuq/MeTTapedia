import Mettapedia.Logic.TierZero.Kernel

/-!
# Kernel version 2: a proof node is a rule and its children

In version 1 a node names its rule *and its arguments*, `(r, a, kids)`. In version 2 a node names
only its rule and its children, `(r, kids)`; the kernel finds the arguments by matching the rule's
premises against the judgments the children already prove. A formal that no premise determines is
introduced by a premise that a cited term of the claim's term store discharges, so it is an
ordinary judgment premise here.

A **matcher** is what the kernel's matching computes: from a rule and the children's judgments,
the arguments (`Matcher.solve`). It is sound (its arguments give an instance whose judgment
premises are exactly the children's judgments), complete (it answers whenever some instance has
those judgment premises), and the rule's judgment premises determine its instance (`determined`).
Example: Metamath's `ax-mp` has the premises `wff ph`, `wff ps`, `|- ph`, `|- (ph -> ps)`; the
children's judgments fix `ph` and `ps`, so they fix the conclusion `|- ps`. Negative example: a rule
`|- (a -> b)` from `wff a` alone does not determine `b`; such a rule is refused at admission.

Results:
* `runCB_sound`, `runCB_complete`: the version-2 walk accepts a proof exactly when the version-1
  walk accepts the same proof with the matcher's arguments written in, with the same conclusions;
* `checkCB_iff_check`: version 2 accepts a proof exactly when some argument annotation is accepted
  by version 1;
* `checkCB_iff_derivable`: version-2 accepted proofs exist exactly for derivable judgments, so
  `check_sound` and `check_complete` of `TierZero.Kernel` carry over.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.ChildBound

open Mettapedia.Logic.TierZero

universe u

variable {P : Presentation.{u}}

/-- The premises a child discharges: those that are no side condition. -/
def judgmentPremises (P : Presentation.{u}) (ps : List P.J) : List P.J :=
  ps.filter (fun p => !P.side p)

/-- The kernel's matching, abstractly. -/
structure Matcher (P : Presentation.{u}) where
  solve : P.R → List P.J → Option P.A
  sound : ∀ r js a, solve r js = some a →
    ∃ ps c, P.inst r a = some (ps, c) ∧ judgmentPremises P ps = js
  complete : ∀ r a ps c, P.inst r a = some (ps, c) → (solve r (judgmentPremises P ps)).isSome
  determined : ∀ r a a' ps c ps' c', P.inst r a = some (ps, c) → P.inst r a' = some (ps', c') →
    judgmentPremises P ps = judgmentPremises P ps' → ps = ps' ∧ c = c'

/-- A version-2 node: a rule and its children. -/
abbrev CNode (P : Presentation.{u}) := P.R × List Kid

variable [DecidableEq P.J]

/-- The version-2 walk: each node's arguments come from matching its children's judgments. -/
def runCB (M : Matcher P) (hyps : List P.J) : List P.J → List (CNode P) → Option (List P.J)
  | done, [] => some done
  | done, (r, kids) :: rest =>
      match kids.mapM (lookup hyps done) with
      | none => none
      | some js =>
          match M.solve r js with
          | none => none
          | some a =>
              match P.inst r a with
              | none => none
              | some (ps, c) =>
                  if discharge (lookup hyps done) ps kids then runCB M hyps (done ++ [c]) rest
                  else none

def checkCB (M : Matcher P) (hyps : List P.J) (proof : List (CNode P)) (root : Kid)
    (goal : P.J) : Bool :=
  match runCB M hyps [] proof with
  | none => false
  | some done => decide (lookup hyps done root = some goal)

/-- Forget the arguments of a version-1 proof. -/
def erase (proof : List (Node P)) : List (CNode P) := proof.map fun (r, _, kids) => (r, kids)

/-- A successful discharge reads exactly the judgment premises from the children, in order. -/
theorem discharge_reads (look : Kid → Option P.J) :
    ∀ (ps : List P.J) (kids : List Kid), discharge look ps kids = true →
      kids.mapM look = some (judgmentPremises P ps)
  | [], [], _ => by simp [judgmentPremises]
  | [], _ :: _, h => by simp [discharge] at h
  | p :: ps, kids, h => by
      by_cases sp : P.side p = true
      · have rest : discharge look ps kids = true := by simpa [discharge, sp] using h
        have := discharge_reads look ps kids rest
        simpa [judgmentPremises, sp] using this
      · have sp' : P.side p = false := by simpa using sp
        cases kids with
        | nil => simp [discharge, sp'] at h
        | cons k ks =>
            simp only [discharge, sp', Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
              decide_eq_true_eq] at h
            have := discharge_reads look ps ks h.2
            simp only [List.mapM_cons, h.1, this, judgmentPremises, List.filter_cons, sp',
              Bool.not_false, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

/-- **Soundness of version 2**: an accepted version-2 walk is the version-1 walk of the same proof
with the matcher's arguments written in. -/
theorem runCB_sound (M : Matcher P) (hyps : List P.J) :
    ∀ (done : List P.J) (proof : List (CNode P)) (out : List P.J),
      runCB M hyps done proof = some out →
        ∃ full : List (Node P), erase full = proof ∧ run hyps done full = some out
  | done, [], out, h => by
      simp only [runCB, Option.some.injEq] at h
      exact ⟨[], rfl, by simp [run, h]⟩
  | done, (r, kids) :: rest, out, h => by
      simp only [runCB] at h
      cases hk : kids.mapM (lookup hyps done) with
      | none => simp [hk] at h
      | some js =>
          simp only [hk] at h
          cases hs : M.solve r js with
          | none => simp [hs] at h
          | some a =>
              simp only [hs] at h
              cases hi : P.inst r a with
              | none => simp [hi] at h
              | some pc =>
                  obtain ⟨ps, c⟩ := pc
                  simp only [hi] at h
                  by_cases hd : discharge (lookup hyps done) ps kids = true
                  · simp only [hd, ↓reduceIte] at h
                    obtain ⟨full, he, hr⟩ := runCB_sound M hyps (done ++ [c]) rest out h
                    refine ⟨(r, a, kids) :: full, by simp [erase, ← he], ?_⟩
                    simp [run, hi, hd, hr]
                  · simp [hd] at h

/-- **Completeness of version 2**: whatever version 1 accepts, version 2 accepts with the
arguments erased, with the same conclusions. -/
theorem runCB_complete (M : Matcher P) (hyps : List P.J) :
    ∀ (done : List P.J) (full : List (Node P)) (out : List P.J),
      run hyps done full = some out → runCB M hyps done (erase full) = some out
  | done, [], out, h => by simpa [run, runCB, erase] using h
  | done, (r, a, kids) :: rest, out, h => by
      simp only [run] at h
      cases hi : P.inst r a with
      | none => simp [hi] at h
      | some pc =>
          obtain ⟨ps, c⟩ := pc
          simp only [hi] at h
          by_cases hd : discharge (lookup hyps done) ps kids = true
          · simp only [hd, ↓reduceIte] at h
            have hk := discharge_reads (lookup hyps done) ps kids hd
            obtain ⟨a', hs⟩ := Option.isSome_iff_exists.mp (M.complete r a ps c hi)
            obtain ⟨ps', c', hi', hjp⟩ := M.sound r _ a' hs
            obtain ⟨rfl, rfl⟩ := M.determined r a a' ps c ps' c' hi hi' hjp.symm
            have hr := runCB_complete M hyps (done ++ [c]) rest out h
            simp only [erase, List.map_cons] at hr ⊢
            simp [runCB, hk, hs, hi', hd, hr]
          · simp [hd] at h

/-- Version 2 accepts a proof exactly when some argument annotation of it is accepted by version 1. -/
theorem checkCB_iff_check (M : Matcher P) (hyps : List P.J) (proof : List (CNode P)) (root : Kid)
    (goal : P.J) :
    checkCB M hyps proof root goal = true ↔
      ∃ full : List (Node P), erase full = proof ∧ check hyps full root goal = true := by
  constructor
  · intro h
    unfold checkCB at h
    cases hr : runCB M hyps [] proof with
    | none => simp [hr] at h
    | some done =>
        simp only [hr, decide_eq_true_eq] at h
        obtain ⟨full, he, hrun⟩ := runCB_sound M hyps [] proof done hr
        exact ⟨full, he, by simp [check, hrun, h]⟩
  · rintro ⟨full, rfl, h⟩
    unfold check at h
    cases hr : run hyps [] full with
    | none => simp [hr] at h
    | some done =>
        simp only [hr, decide_eq_true_eq] at h
        simp [checkCB, runCB_complete M hyps [] full done hr, h]

/-- **Version 2 accepts exactly the derivable judgments**, as version 1 does. -/
theorem checkCB_iff_derivable (M : Matcher P) (hyps : List P.J) (goal : P.J) :
    (∃ proof root, checkCB M hyps proof root goal = true) ↔ Derivable P hyps goal := by
  rw [← check_iff_derivable]
  constructor
  · rintro ⟨proof, root, h⟩
    obtain ⟨full, _, hc⟩ := (checkCB_iff_check M hyps proof root goal).mp h
    exact ⟨full, root, hc⟩
  · rintro ⟨full, root, h⟩
    exact ⟨erase full, root, (checkCB_iff_check M hyps (erase full) root goal).mpr ⟨full, rfl, h⟩⟩

theorem checkCB_sound (M : Matcher P) {hyps : List P.J} {proof : List (CNode P)} {root : Kid}
    {goal : P.J} (h : checkCB M hyps proof root goal = true) : Derivable P hyps goal :=
  (checkCB_iff_derivable M hyps goal).mp ⟨proof, root, h⟩

/-! ## Controls

A presentation with two judgments `w n` (a well-formed term `n`) and `t n` (a theorem `t n`) over
natural numbers: `w0 : w 0`; `wsucc : w n ⊢ w (n+1)`; `t0 : w n ⊢ t n` (one rule per argument);
`bad` concludes `t 7` from `w 0` whatever its argument, so its judgment premises do not determine
its conclusion. -/

namespace Controls

inductive J where
  | w (n : ℕ)
  | t (n : ℕ)
  deriving DecidableEq, Repr

inductive R where
  | w0 | wsucc | t0
  deriving DecidableEq, Repr

def inst : R → ℕ → Option (List J × J)
  | .w0, 0 => some ([], .w 0)
  | .w0, _ => none
  | .wsucc, n => some ([.w n], .w (n + 1))
  | .t0, n => some ([.w n], .t n)

abbrev pres : Presentation := { J := J, R := R, A := ℕ, inst := inst, side := fun _ => false }

def solve : R → List J → Option ℕ
  | .w0, [] => some 0
  | .wsucc, [.w n] => some n
  | .t0, [.w n] => some n
  | _, _ => none

theorem jp_eq (ps : List J) : judgmentPremises pres ps = ps := by
  simp [judgmentPremises, pres]

def matcher : Matcher pres where
  solve := solve
  sound := by
    intro r js a h
    cases r with
    | w0 =>
        cases js with
        | nil =>
            simp only [solve, Option.some.injEq] at h
            subst h
            exact ⟨[], .w 0, rfl, jp_eq []⟩
        | cons j js => cases j <;> simp [solve] at h
    | wsucc =>
        cases js with
        | nil => simp [solve] at h
        | cons j js =>
            cases j with
            | w n =>
                cases js with
                | nil =>
                    simp only [solve, Option.some.injEq] at h
                    subst h
                    exact ⟨[.w n], .w (n + 1), rfl, jp_eq _⟩
                | cons _ _ => simp [solve] at h
            | t n => simp [solve] at h
    | t0 =>
        cases js with
        | nil => simp [solve] at h
        | cons j js =>
            cases j with
            | w n =>
                cases js with
                | nil =>
                    simp only [solve, Option.some.injEq] at h
                    subst h
                    exact ⟨[.w n], .t n, rfl, jp_eq _⟩
                | cons _ _ => simp [solve] at h
            | t n => simp [solve] at h
  complete := by
    intro r a ps c h
    rw [jp_eq]
    cases r with
    | w0 =>
        cases a with
        | zero =>
            simp only [pres, inst, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rfl
        | succ n => simp [pres, inst] at h
    | wsucc =>
        simp only [pres, inst, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
    | t0 =>
        simp only [pres, inst, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
  determined := by
    intro r a a' ps c ps' c' h h' hjp
    rw [jp_eq, jp_eq] at hjp
    subst hjp
    cases r with
    | w0 =>
        cases a <;> cases a' <;> simp_all [pres, inst]
    | wsucc =>
        simp only [pres, inst, Option.some.injEq, Prod.mk.injEq] at h h'
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, rfl⟩ := h'
        simp only [List.cons.injEq, J.w.injEq, and_true] at h1
        subst h1
        exact ⟨rfl, rfl⟩
    | t0 =>
        simp only [pres, inst, Option.some.injEq, Prod.mk.injEq] at h h'
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, rfl⟩ := h'
        simp only [List.cons.injEq, J.w.injEq, and_true] at h1
        subst h1
        exact ⟨rfl, rfl⟩

/-- Positive control: `t 2` from the children alone (no arguments written). -/
theorem control_accepts :
    checkCB matcher [] [(.w0, []), (.wsucc, [.node 0]), (.wsucc, [.node 1]), (.t0, [.node 2])]
      (.node 3) (J.t 2) = true := by decide

/-- Negative control: the same children cannot prove another theorem. -/
theorem control_wrong_goal :
    checkCB matcher [] [(.w0, []), (.wsucc, [.node 0]), (.t0, [.node 1])]
      (.node 2) (J.t 2) = false := by decide

/-- Negative control: a child whose judgment does not fit the rule's premise. -/
theorem control_wrong_child :
    checkCB matcher [] [(.w0, []), (.t0, [.node 0]), (.t0, [.node 1])]
      (.node 2) (J.t 0) = false := by decide

end Controls

end Mettapedia.Logic.TierZero.ChildBound
