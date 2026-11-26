import Mettapedia.Machines.TIsa.Derivation.Evaluator

/-!
# What the evaluator's matches are

`solve` over a rule's goals is characterized without the list monad: a match is a word of store
occurrences for the take premises, one for the read premises, each premise accepted in turn
(`attemptAll`), followed by the determinate goals (`applyAll`). The shapes of a match follow:
lengths, distinct takes, reads apart from takes, and occurrences drawn from the store.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

universe u v w

variable {T : Type u} {V : Type v} {B : Type w} [DecidableEq V] (M : Matcher T V B)

/-- Premises of one role, accepted one after another at a word of occurrences. -/
def attemptAll (role : Role) : List T → Match V B → List (ℕ × V) → Option (Match V B)
  | [], m, [] => some m
  | p :: ps, m, x :: xs => (attempt M role p m x).bind fun m' => attemptAll role ps m' xs
  | _, _, _ => none

/-- Determinate goals, applied one after another. -/
def applyAll (s : Store V) : List (Determinate T) → Match V B → Option (Match V B)
  | [], m => some m
  | d :: ds, m => (d.apply M s m).bind (applyAll s ds)

/-- The determinate goals of a rule. -/
def determinates (r : Rule T) : List (Determinate T) :=
  r.body.tell.map (fun e => .tell e.1 e.2) ++ r.body.checks.map .check ++
    r.collect.map .collect ++ r.body.produce.map .produce

omit [DecidableEq V] in
theorem goals_eq (r : Rule T) :
    goals r = r.body.take.map (Goal.premise .take) ++ r.body.read.map (Goal.premise .read) ++
      (determinates r).map Goal.determinate := by
  simp [goals, determinates, List.map_append, Function.comp_def, List.append_assoc]

variable {M}

theorem solve_append (s : Store V) (first second : List (Goal T)) (m : Match V B) :
    solve M s (first ++ second) m = (solve M s first m).flatMap (solve M s second) := by
  induction first generalizing m with
  | nil => simp [solve]
  | cons g gs ih =>
      cases g with
      | premise role pattern =>
          simp only [List.cons_append, solve, List.flatMap_assoc]
          apply List.flatMap_congr
          intro x _
          cases attempt M role pattern m x with
          | none => rfl
          | some m' => exact ih m'
      | determinate d =>
          simp only [List.cons_append, solve]
          cases d.apply M s m with
          | none => rfl
          | some m' => exact ih m'

theorem mem_solve_premises (s : Store V) (role : Role) (patterns : List T) (m m' : Match V B) :
    m' ∈ solve M s (patterns.map (Goal.premise role)) m ↔
      ∃ xs : List (ℕ × V), (∀ x ∈ xs, x ∈ s.occurrences) ∧ attemptAll M role patterns m xs = some m' := by
  induction patterns generalizing m with
  | nil =>
      simp only [List.map_nil, solve, List.mem_singleton]
      constructor
      · rintro rfl
        exact ⟨[], by simp, rfl⟩
      · rintro ⟨xs, _, accepted⟩
        cases xs with
        | nil => simpa [attemptAll] using accepted.symm
        | cons _ _ => simp [attemptAll] at accepted
  | cons p ps ih =>
      simp only [List.map_cons, solve, List.mem_flatMap]
      constructor
      · rintro ⟨x, inside, found⟩
        cases tried : attempt M role p m x with
        | none => simp [tried] at found
        | some m₁ =>
            rw [tried] at found
            obtain ⟨xs, within, accepted⟩ := (ih m₁).mp found
            refine ⟨x :: xs, ?_, ?_⟩
            · intro y member
              rcases List.mem_cons.mp member with rfl | later
              · exact inside
              · exact within y later
            · simp [attemptAll, tried, accepted]
      · rintro ⟨xs, within, accepted⟩
        cases xs with
        | nil => simp [attemptAll] at accepted
        | cons x xs =>
            simp only [attemptAll] at accepted
            cases tried : attempt M role p m x with
            | none => simp [tried] at accepted
            | some m₁ =>
                rw [tried, Option.bind_some] at accepted
                refine ⟨x, within x (by simp), ?_⟩
                rw [tried]
                exact (ih m₁).mpr ⟨xs, fun y member => within y (by simp [member]), accepted⟩

theorem solve_determinates (s : Store V) (ds : List (Determinate T)) (m : Match V B) :
    solve M s (ds.map Goal.determinate) m = (applyAll M s ds m).toList := by
  induction ds generalizing m with
  | nil => simp [solve, applyAll]
  | cons d ds ih =>
      simp only [List.map_cons, solve, applyAll]
      cases d.apply M s m with
      | none => rfl
      | some m' => simpa using ih m'

/-- **The matches of a rule**: occurrences for its takes, occurrences for its reads, then its
determinate goals. -/
theorem mem_solve_goals (s : Store V) (r : Rule T) (m : Match V B) :
    m ∈ solve M s (goals r) (Match.start M) ↔
      ∃ (xs ys : List (ℕ × V)) (m₁ m₂ : Match V B),
        (∀ x ∈ xs, x ∈ s.occurrences) ∧ (∀ y ∈ ys, y ∈ s.occurrences) ∧
        attemptAll M .take r.body.take (Match.start M) xs = some m₁ ∧
        attemptAll M .read r.body.read m₁ ys = some m₂ ∧
        applyAll M s (determinates r) m₂ = some m := by
  rw [goals_eq, solve_append, solve_append]
  simp only [List.mem_flatMap, solve_determinates, Option.mem_toList]
  constructor
  · rintro ⟨m₂, ⟨m₁, inTake, inRead⟩, applied⟩
    obtain ⟨xs, xsInside, xsAccepted⟩ := (mem_solve_premises s .take _ _ _).mp inTake
    obtain ⟨ys, ysInside, ysAccepted⟩ := (mem_solve_premises s .read _ _ _).mp inRead
    exact ⟨xs, ys, m₁, m₂, xsInside, ysInside, xsAccepted, ysAccepted, applied⟩
  · rintro ⟨xs, ys, m₁, m₂, xsInside, ysInside, xsAccepted, ysAccepted, applied⟩
    exact ⟨m₂, ⟨m₁, (mem_solve_premises s .take _ _ _).mpr ⟨xs, xsInside, xsAccepted⟩,
      (mem_solve_premises s .read _ _ _).mpr ⟨ys, ysInside, ysAccepted⟩⟩, applied⟩

theorem mem_firings (P : List (Rule T)) (s : Store V) (r : Rule T) (m : Match V B) :
    (r, m) ∈ firings M P s ↔ r ∈ P ∧ m ∈ solve M s (goals r) (Match.start M) := by
  simp only [firings, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨r', member, m', found, rfl, rfl⟩
    exact ⟨member, found⟩
  · rintro ⟨member, found⟩
    exact ⟨r, member, m, found, rfl, rfl⟩

/-! ## Shapes of accepted premises -/

omit [DecidableEq V] in
theorem attemptAll_length (role : Role) (patterns : List T) (m m' : Match V B) (xs : List (ℕ × V))
    (accepted : attemptAll M role patterns m xs = some m') : patterns.length = xs.length := by
  induction patterns generalizing m xs with
  | nil => cases xs <;> simp_all [attemptAll]
  | cons p ps ih =>
      cases xs with
      | nil => simp [attemptAll] at accepted
      | cons x xs =>
          simp only [attemptAll] at accepted
          cases tried : attempt M role p m x with
          | none => simp [tried] at accepted
          | some m₁ =>
              rw [tried, Option.bind_some] at accepted
              simpa using ih m₁ xs accepted

omit [DecidableEq V] in
theorem attempt_some_iff (role : Role) (pattern : T) (m m' : Match V B) (x : ℕ × V) :
    attempt M role pattern m x = some m' ↔
      role.allows m x.1 = true ∧ ∃ θ, M.extend m.bindings pattern x.2 = some θ ∧ m' = m.select role x.1 θ := by
  unfold attempt
  by_cases allowed : role.allows m x.1 = true
  · simp only [allowed, if_true, true_and, Option.map_eq_some_iff]
    constructor
    · rintro ⟨θ, extended, rfl⟩
      exact ⟨θ, extended, rfl⟩
    · rintro ⟨θ, extended, rfl⟩
      exact ⟨θ, extended, rfl⟩
  · simp [allowed]

omit [DecidableEq V] in
/-- Takes extend the taken occurrences by their word, which is new, distinct and apart from the
reads. -/
theorem attemptAll_take (patterns : List T) (m m' : Match V B) (xs : List (ℕ × V))
    (accepted : attemptAll M .take patterns m xs = some m') :
    m'.taken = m.taken ++ xs.map Prod.fst ∧ m'.read = m.read ∧ m'.seen = m.seen ∧ m'.made = m.made ∧
      (m.taken.Nodup → m'.taken.Nodup) ∧ ∀ o ∈ xs.map Prod.fst, o ∉ m.read := by
  induction patterns generalizing m xs with
  | nil =>
      cases xs with
      | nil =>
          simp only [attemptAll, Option.some.injEq] at accepted
          subst accepted
          simp
      | cons _ _ => simp [attemptAll] at accepted
  | cons p ps ih =>
      cases xs with
      | nil => simp [attemptAll] at accepted
      | cons x xs =>
          simp only [attemptAll] at accepted
          cases tried : attempt M .take p m x with
          | none => simp [tried] at accepted
          | some m₁ =>
              rw [tried, Option.bind_some] at accepted
              obtain ⟨allowed, θ, _, rfl⟩ := (attempt_some_iff .take p m m₁ x).mp tried
              obtain ⟨taken, read, seen, made, nodup, apart⟩ := ih _ xs accepted
              simp only [Match.select] at taken read seen made nodup apart
              simp only [Role.allows, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
                List.contains_iff_mem] at allowed
              refine ⟨by simp [taken], read, seen, made, ?_, ?_⟩
              · intro first
                apply nodup
                exact List.nodup_append.mpr ⟨first, List.nodup_singleton _,
                  fun a inside b same equal => by
                    rw [List.mem_singleton] at same
                    subst same equal
                    exact allowed.1 inside⟩
              · intro o member
                rcases List.mem_cons.mp member with rfl | later
                · exact allowed.2
                · exact read ▸ apart o later

omit [DecidableEq V] in
/-- Reads extend the read occurrences by their word, each apart from the takes. -/
theorem attemptAll_read (patterns : List T) (m m' : Match V B) (ys : List (ℕ × V))
    (accepted : attemptAll M .read patterns m ys = some m') :
    m'.read = m.read ++ ys.map Prod.fst ∧ m'.taken = m.taken ∧ m'.seen = m.seen ∧ m'.made = m.made ∧
      ∀ o ∈ ys.map Prod.fst, o ∉ m.taken := by
  induction patterns generalizing m ys with
  | nil =>
      cases ys with
      | nil =>
          simp only [attemptAll, Option.some.injEq] at accepted
          subst accepted
          simp
      | cons _ _ => simp [attemptAll] at accepted
  | cons p ps ih =>
      cases ys with
      | nil => simp [attemptAll] at accepted
      | cons y ys =>
          simp only [attemptAll] at accepted
          cases tried : attempt M .read p m y with
          | none => simp [tried] at accepted
          | some m₁ =>
              rw [tried, Option.bind_some] at accepted
              obtain ⟨allowed, θ, _, rfl⟩ := (attempt_some_iff .read p m m₁ y).mp tried
              obtain ⟨read, taken, seen, made, apart⟩ := ih _ ys accepted
              simp only [Match.select] at taken read seen made apart
              simp only [Role.allows, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
                List.contains_iff_mem] at allowed
              refine ⟨by simp [read], taken, seen, made, ?_⟩
              intro o member
              rcases List.mem_cons.mp member with rfl | later
              · exact allowed
              · exact taken ▸ apart o later

/-! ## Determinate goals keep the selection and the bindings -/

theorem apply_fields (s : Store V) (d : Determinate T) (m m' : Match V B)
    (applied : d.apply M s m = some m') :
    m'.bindings = m.bindings ∧ m'.taken = m.taken ∧ m'.read = m.read := by
  cases d with
  | tell l r =>
      simp only [Determinate.apply] at applied
      split at applied <;> simp_all
  | check c =>
      simp only [Determinate.apply] at applied
      split at applied <;> simp_all
  | collect p =>
      simp only [Determinate.apply, Option.map_eq_some_iff] at applied
      obtain ⟨_, _, rfl⟩ := applied
      exact ⟨rfl, rfl, rfl⟩
  | produce t =>
      simp only [Determinate.apply, Option.map_eq_some_iff] at applied
      obtain ⟨_, _, rfl⟩ := applied
      exact ⟨rfl, rfl, rfl⟩

theorem applyAll_fields (s : Store V) (ds : List (Determinate T)) (m m' : Match V B)
    (applied : applyAll M s ds m = some m') :
    m'.bindings = m.bindings ∧ m'.taken = m.taken ∧ m'.read = m.read := by
  induction ds generalizing m with
  | nil =>
      simp only [applyAll, Option.some.injEq] at applied
      subst applied
      exact ⟨rfl, rfl, rfl⟩
  | cons d ds ih =>
      simp only [applyAll] at applied
      cases first : d.apply M s m with
      | none => simp [first] at applied
      | some m₁ =>
          rw [first, Option.bind_some] at applied
          obtain ⟨b, t, r⟩ := ih m₁ applied
          obtain ⟨b', t', r'⟩ := apply_fields s d m m₁ first
          exact ⟨b.trans b', t.trans t', r.trans r'⟩

end Mettapedia.Machines.TIsa.Derivation
