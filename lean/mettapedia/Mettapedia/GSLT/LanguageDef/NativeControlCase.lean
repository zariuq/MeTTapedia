import Mettapedia.GSLT.LanguageDef.HostGoalDelimiters

/-!
# Committed case selection as a resumable control frame

The input key and patterns have already passed the dialect's preparation
phase. In PeTTa that phase includes `constrain_args` for every pattern; it
must not be dropped or moved by this lowering. The `Empty` default's second
key evaluation is outside this module.

`selectArm` is the recursive first-unifying-arm specification. `pullCase`
instead tests one pattern per pull, then permanently enters that arm's
answer cursor. `collect_scan` and `delivered_scan` compare the two after the
exact number of administrative tests. The selected body's failures never
enable a later arm, and its answer-local stores are retained in the answer
type. Unsuccessful tests restart from the case entry store.

The unifier and branch evaluator are parameters, not implementations of
MeTTa matching. The theorems establish control lowering for any such
operations. Their realization, pattern preparation, effects, and admissible
early output constraints require separate dialect-level correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeControlCase

open HostCalls (Pull collect)
open HostGoals (delivered)

variable {Store Key Pattern Body HState Answer : Type}

/-- Matching returns a refined store; failure contributes no bindings. -/
abbrev Match (Store Key Pattern : Type) := Store → Key → Pattern → Option Store

/-- Source first-match selection, independent of whether the body succeeds. -/
def selectArm (unify : Match Store Key Pattern) (entry : Store) (key : Key) :
    List (Pattern × Body) → Option (Store × Body)
  | [] => none
  | (pattern, body) :: rest =>
      match unify entry key pattern with
      | none => selectArm unify entry key rest
      | some refined => some (refined, body)

/-- Number of matching pulls, including the exhaustion test if no arm matches. -/
def scanCost (unify : Match Store Key Pattern) (entry : Store) (key : Key) :
    List (Pattern × Body) → Nat
  | [] => 1
  | (pattern, _) :: rest =>
      match unify entry key pattern with
      | none => 1 + scanCost unify entry key rest
      | some _ => 1

/-- Once committed, the frame retains no alternative case arms. -/
inductive Frame (Store Key Pattern Body HState : Type) where
  | scan (entry : Store) (key : Key) (remaining : List (Pattern × Body))
  | running (cursor : HState)

/-- One administrative test or one body pull. No body is restarted. -/
def pullCase (unify : Match Store Key Pattern) (start : Store → Body → HState)
    (pull : HState → Pull HState Answer) :
    Frame Store Key Pattern Body HState → Pull (Frame Store Key Pattern Body HState) Answer
  | .scan _ _ [] => .done
  | .scan entry key ((pattern, body) :: rest) =>
      match unify entry key pattern with
      | none => .suspend (.scan entry key rest)
      | some refined => .suspend (.running (start refined body))
  | .running cursor =>
      match pull cursor with
      | .done => .done
      | .yield answer residual => .yield answer (.running residual)
      | .suspend residual => .suspend (.running residual)

theorem collect_running (unify : Match Store Key Pattern) (start : Store → Body → HState)
    (pull : HState → Pull HState Answer) (fuel : Nat) (cursor : HState) :
    collect (pullCase unify start pull) fuel (.running cursor) = collect pull fuel cursor := by
  induction fuel generalizing cursor with
  | zero => rfl
  | succ fuel ih =>
      cases h : pull cursor <;> simp [collect, pullCase, h, ih]

theorem delivered_running (unify : Match Store Key Pattern) (start : Store → Body → HState)
    (pull : HState → Pull HState Answer) (fuel : Nat) (cursor : HState) :
    delivered (pullCase unify start pull) fuel (.running cursor) = delivered pull fuel cursor := by
  induction fuel generalizing cursor with
  | zero => rfl
  | succ fuel ih =>
      cases h : pull cursor <;> simp [delivered, pullCase, h, ih]

/-- Exact completed observation, with the administrative matching cost exposed. -/
theorem collect_scan (unify : Match Store Key Pattern) (start : Store → Body → HState)
    (pull : HState → Pull HState Answer) (entry : Store) (key : Key)
    (arms : List (Pattern × Body)) (fuel : Nat) :
    collect (pullCase unify start pull) (scanCost unify entry key arms + fuel)
        (.scan entry key arms) =
      match selectArm unify entry key arms with
      | none => some []
      | some (refined, body) => collect pull fuel (start refined body) := by
  induction arms with
  | nil => simp [scanCost, selectArm, Nat.add_comm 1 fuel, collect, pullCase]
  | cons arm rest ih =>
      rcases arm with ⟨pattern, body⟩
      cases h : unify entry key pattern with
      | none =>
          simpa [scanCost, selectArm, h, Nat.add_assoc, Nat.add_comm 1,
            collect, pullCase] using ih
      | some refined =>
          simp [scanCost, selectArm, h, Nat.add_comm 1 fuel, collect, pullCase,
            collect_running]

/-- The same lowering preserves every finite prefix, even for divergent bodies. -/
theorem delivered_scan (unify : Match Store Key Pattern) (start : Store → Body → HState)
    (pull : HState → Pull HState Answer) (entry : Store) (key : Key)
    (arms : List (Pattern × Body)) (fuel : Nat) :
    delivered (pullCase unify start pull) (scanCost unify entry key arms + fuel)
        (.scan entry key arms) =
      match selectArm unify entry key arms with
      | none => []
      | some (refined, body) => delivered pull fuel (start refined body) := by
  induction arms with
  | nil => simp [scanCost, selectArm, Nat.add_comm 1 fuel, delivered, pullCase]
  | cons arm rest ih =>
      rcases arm with ⟨pattern, body⟩
      cases h : unify entry key pattern with
      | none =>
          simpa [scanCost, selectArm, h, Nat.add_assoc, Nat.add_comm 1,
            delivered, pullCase] using ih
      | some refined =>
          simp [scanCost, selectArm, h, Nat.add_comm 1 fuel, delivered, pullCase,
            delivered_running]

/-- The number of matching operations is bounded by the prepared arm count. -/
theorem scanCost_bounds (unify : Match Store Key Pattern) (entry : Store) (key : Key)
    (arms : List (Pattern × Body)) :
    1 ≤ scanCost unify entry key arms ∧ scanCost unify entry key arms ≤ arms.length + 1 := by
  induction arms with
  | nil => simp [scanCost]
  | cons arm rest ih =>
      rcases arm with ⟨pattern, body⟩
      cases h : unify entry key pattern with
      | none => simp only [scanCost, h, List.length_cons]; omega
      | some refined => simp [scanCost, h]

/-- A partly completed scan cannot invent an answer. -/
theorem delivered_scan_early (unify : Match Store Key Pattern)
    (start : Store → Body → HState) (pull : HState → Pull HState Answer)
    (entry : Store) (key : Key) (arms : List (Pattern × Body)) (fuel : Nat)
    (early : fuel ≤ scanCost unify entry key arms) :
    delivered (pullCase unify start pull) fuel (.scan entry key arms) = [] := by
  induction arms generalizing fuel with
  | nil => cases fuel <;> simp [delivered, pullCase]
  | cons arm rest ih =>
      rcases arm with ⟨pattern, body⟩
      cases fuel with
      | zero => rfl
      | succ fuel =>
          cases h : unify entry key pattern with
          | none =>
              have bound : fuel ≤ scanCost unify entry key rest := by
                simp only [scanCost, h] at early
                omega
              simpa [delivered, pullCase, h] using ih fuel bound
          | some refined =>
              have zero : fuel = 0 := by simp only [scanCost, h] at early; omega
              simp [zero, delivered, pullCase, h]

/-- Reflection for arbitrary target fuel, including interruptions mid-scan. -/
theorem delivered_scan_reflect (unify : Match Store Key Pattern)
    (start : Store → Body → HState) (pull : HState → Pull HState Answer)
    (entry : Store) (key : Key) (arms : List (Pattern × Body)) (fuel : Nat) :
    ∃ bodyFuel ≤ fuel,
      delivered (pullCase unify start pull) fuel (.scan entry key arms) =
        match selectArm unify entry key arms with
        | none => []
        | some (refined, body) => delivered pull bodyFuel (start refined body) := by
  by_cases early : fuel ≤ scanCost unify entry key arms
  · refine ⟨0, Nat.zero_le _, ?_⟩
    rw [delivered_scan_early unify start pull entry key arms fuel early]
    cases selectArm unify entry key arms <;> rfl
  · refine ⟨fuel - scanCost unify entry key arms, Nat.sub_le _ _, ?_⟩
    conv_lhs => rw [show fuel = scanCost unify entry key arms +
      (fuel - scanCost unify entry key arms) by omega]
    exact delivered_scan unify start pull entry key arms _

/-- A successful selection identifies the earliest matching occurrence, with
all failed trials made in the same entry store. -/
theorem selectArm_some_iff (unify : Match Store Key Pattern) (entry : Store) (key : Key)
    (arms : List (Pattern × Body)) (refined : Store) (body : Body) :
    selectArm unify entry key arms = some (refined, body) ↔
      ∃ before pattern after,
        arms = before ++ (pattern, body) :: after ∧
        (∀ arm ∈ before, unify entry key arm.1 = none) ∧
        unify entry key pattern = some refined := by
  induction arms with
  | nil =>
      constructor
      · simp [selectArm]
      · rintro ⟨before, pattern, after, eq, _, _⟩
        have := congrArg List.length eq
        simp at this
  | cons arm rest ih =>
      rcases arm with ⟨p, b⟩
      cases h : unify entry key p with
      | none =>
          constructor
          · intro found
            have found' : selectArm unify entry key rest = some (refined, body) := by
              simpa [selectArm, h] using found
            obtain ⟨before, pattern, after, eq, failed, matched⟩ := ih.mp found'
            refine ⟨(p,b) :: before, pattern, after, by simp [eq], ?_, matched⟩
            intro arm member
            rcases List.mem_cons.mp member with rfl | member
            · exact h
            · exact failed arm member
          · rintro ⟨before, pattern, after, eq, failed, matched⟩
            cases before with
            | nil =>
                simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at eq
                have bad := matched
                rw [← eq.1.1, h] at bad
                cases bad
            | cons head before =>
                simp only [List.cons_append, List.cons.injEq] at eq
                have tailFound := ih.mpr ⟨before, pattern, after, eq.2,
                  fun a member => failed a (List.mem_cons_of_mem head member), matched⟩
                simpa [selectArm, h] using tailFound
      | some s =>
          constructor
          · intro found
            have eq : s = refined ∧ b = body := by simpa [selectArm, h] using found
            rcases eq with ⟨rfl, rfl⟩
            exact ⟨[], p, rest, rfl, by simp, h⟩
          · rintro ⟨before, pattern, after, eq, failed, matched⟩
            cases before with
            | nil =>
                simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at eq
                rcases eq with ⟨⟨rfl, rfl⟩, rfl⟩
                simp [selectArm, matched]
            | cons head before =>
                simp only [List.cons_append, List.cons.injEq] at eq
                have bad := failed head (List.mem_cons_self)
                rw [← eq.1, h] at bad
                cases bad

namespace Controls

/-- A tiny matcher that binds a previously open capture. -/
def bindKey : Match (Option Nat) Nat (Option Nat)
  | entry, key, some pattern => if key = pattern then some entry else none
  | _, key, none => some (some key)

def start (s : Option Nat) (body : List Nat) : List (Option Nat × Nat) :=
  body.map (s, ·)

def pull : List (Option Nat × Nat) → Pull (List (Option Nat × Nat)) (Option Nat × Nat)
  | [] => .done
  | a :: rest => .yield a rest

/-- A failed pattern is rolled back; the wildcard binds the original open capture. -/
theorem binding_and_duplicates :
    collect (pullCase bindKey start pull) 6
      (.scan none 7 [(some 4, [0]), (none, [2, 2]), (some 7, [9])]) =
        some [(some 7, 2), (some 7, 2)] := by decide

/-- Once the first pattern matches, an empty body does not try the next pattern. -/
theorem matching_failure_commits :
    collect (pullCase bindKey start pull) 6
      (.scan none 7 [(some 7, []), (none, [9])]) = some [] := by decide

/-- Negative control: enumerating every matching arm invents an answer. -/
theorem all_matches_is_wrong :
    ([(some 7, []), (none, [9])] : List (Option Nat × List Nat)).flatMap
      (fun arm => match bindKey none 7 arm.1 with
        | none => []
        | some s => start s arm.2) = [(some 7, 9)] ∧
    collect (pullCase bindKey start pull) 6
      (.scan none 7 [(some 7, []), (none, [9])]) ≠ some [(some 7, 9)] := by decide

/-- Pending scan is not exhaustion. -/
theorem matching_budget_is_not_empty :
    collect (pullCase bindKey start pull) 1
      (.scan none 7 [(some 4, [0]), (none, [2])]) = none := by decide

/-- Filtering out a failing body before committing changes the selected arm.
This also rules out pushing a failing destination test into arm selection. -/
theorem body_filter_before_match_is_wrong :
    selectArm bindKey none 7
      ([(some 7, []), (none, [9])] : List (Option Nat × List Nat)) =
        some (none, []) ∧
    selectArm bindKey none 7
      (([(some 7, []), (none, [9])] : List (Option Nat × List Nat)).filter
        (fun arm => !arm.2.isEmpty)) = some (some 7, [9]) := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.NativeControlCase
