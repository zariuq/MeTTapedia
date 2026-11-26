import Mettapedia.Machines.TIsa.Derivation.Solutions

/-!
# The meaning of matching, over a substitution action

A `Matcher` is read in the step theory's terms through `Semantics`: ground values embed into the
terms and every substitution fixes them; bindings denote a set of substitutions; extending bindings
by a pattern and a value keeps exactly the substitutions that send the pattern to the value; and an
instantiated term has its value at every denoted substitution. Equality of terms is the action's
own equivalence, so terms modulo equations are covered.

From these laws alone: the bindings of a word of accepted premises denote exactly the
substitutions solving its pattern equations (`attemptAll_denotes`), a word whose equations have a
solution and whose occurrences are allowed is accepted (`attemptAll_take_complete`,
`attemptAll_read_complete`), and the determinate goals pass exactly when the tells agree, the
checks pass and every collected or produced term instantiates (`applyAll_determinates_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

universe u s v w

variable {T : Type u} {S : Type s} {V : Type v} {B : Type w}

/-- **The laws of a matcher over a substitution action.** -/
structure Semantics (A : SubstitutionAction T S) (M : Matcher T V B) where
  embed : V → T
  reflects : ∀ a b, A.E (embed a) (embed b) ↔ a = b
  fixed : ∀ σ a, A.E (A.apply σ (embed a)) (embed a)
  Denotes : B → S → Prop
  denotes_empty : ∀ σ, Denotes M.empty σ
  extend_iff : ∀ θ p a σ, (∃ θ', M.extend θ p a = some θ' ∧ Denotes θ' σ) ↔
    Denotes θ σ ∧ A.E (A.apply σ p) (embed a)
  extend_inhabited : ∀ θ p a θ', M.extend θ p a = some θ' → ∃ σ, Denotes θ' σ
  instantiate_sound : ∀ θ t a σ, M.instantiate θ t = some a → Denotes θ σ →
    A.E (A.apply σ t) (embed a)

namespace Semantics

variable {A : SubstitutionAction T S} {M : Matcher T V B} (Sem : Semantics A M)

theorem E_trans {x y z : T} (first : A.E x y) (second : A.E y z) : A.E x z :=
  A.equivalence.trans first second

theorem E_symm {x y : T} (same : A.E x y) : A.E y x := A.equivalence.symm same

/-- A term equivalent to the image of a value is equivalent to the value. -/
theorem to_embed_iff (σ : S) (y : T) (a : V) :
    A.E y (A.apply σ (Sem.embed a)) ↔ A.E y (Sem.embed a) := by
  constructor
  · intro same
    exact E_trans same (Sem.fixed σ a)
  · intro same
    exact E_trans same (E_symm (Sem.fixed σ a))

/-- Two instantiated terms agree at every denoted substitution exactly when their values are
equal. -/
theorem values_iff {σ : S} {t t' : T} {a a' : V} (first : A.E (A.apply σ t) (Sem.embed a))
    (second : A.E (A.apply σ t') (Sem.embed a')) :
    A.E (A.apply σ t) (A.apply σ t') ↔ a = a' := by
  rw [← Sem.reflects]
  constructor
  · intro same
    exact E_trans (E_symm first) (E_trans same second)
  · intro same
    exact E_trans first (E_trans same (E_symm second))

/-- A value-equivalent term is equivalent to another value exactly when the values are equal. -/
theorem value_iff {σ : S} {t : T} {a b : V} (first : A.E (A.apply σ t) (Sem.embed a)) :
    A.E (A.apply σ t) (Sem.embed b) ↔ a = b := by
  rw [← Sem.reflects]
  constructor
  · intro same
    exact E_trans (E_symm first) same
  · intro same
    exact E_trans first same

/-- The bindings of an accepted premise denote the substitutions of its own bindings that send the
pattern to the value. -/
theorem attempt_denotes {role : Role} {pattern : T} {m m' : Match V B} {x : ℕ × V}
    (accepted : attempt M role pattern m x = some m') (σ : S) :
    Sem.Denotes m'.bindings σ ↔
      Sem.Denotes m.bindings σ ∧ A.E (A.apply σ pattern) (Sem.embed x.2) := by
  obtain ⟨_, θ, extended, rfl⟩ := (attempt_some_iff role pattern m m' x).mp accepted
  have bound : (m.select role x.1 θ).bindings = θ := by cases role <;> rfl
  rw [bound, ← Sem.extend_iff]
  constructor
  · intro denoted
    exact ⟨θ, extended, denoted⟩
  · rintro ⟨θ', again, denoted⟩
    rw [extended] at again
    cases again
    exact denoted

/-- **Accepted premises denote exactly the solutions of their equations.** -/
theorem attemptAll_denotes (role : Role) (patterns : List T) (m m' : Match V B) (xs : List (ℕ × V))
    (accepted : attemptAll M role patterns m xs = some m') (σ : S) :
    Sem.Denotes m'.bindings σ ↔ Sem.Denotes m.bindings σ ∧
      List.Forall₂ (fun p x => A.E (A.apply σ p) (Sem.embed x.2)) patterns xs := by
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
          cases tried : attempt M role p m x with
          | none => simp [tried] at accepted
          | some m₁ =>
              rw [tried, Option.bind_some] at accepted
              rw [ih m₁ xs accepted, Sem.attempt_denotes tried σ, List.forall₂_cons]
              tauto

/-- Accepted premises have a denoted substitution. -/
theorem attemptAll_inhabited (role : Role) (patterns : List T) (m m' : Match V B) (xs : List (ℕ × V))
    (accepted : attemptAll M role patterns m xs = some m') (start : ∃ σ, Sem.Denotes m.bindings σ) :
    ∃ σ, Sem.Denotes m'.bindings σ := by
  induction patterns generalizing m xs with
  | nil =>
      cases xs with
      | nil =>
          simp only [attemptAll, Option.some.injEq] at accepted
          subst accepted
          exact start
      | cons _ _ => simp [attemptAll] at accepted
  | cons p ps ih =>
      cases xs with
      | nil => simp [attemptAll] at accepted
      | cons x xs =>
          simp only [attemptAll] at accepted
          cases tried : attempt M role p m x with
          | none => simp [tried] at accepted
          | some m₁ =>
              rw [tried, Option.bind_some] at accepted
              apply ih m₁ xs accepted
              obtain ⟨_, θ, extended, rfl⟩ := (attempt_some_iff role p m m₁ x).mp tried
              have bound : (m.select role x.1 θ).bindings = θ := by cases role <;> rfl
              rw [bound]
              exact Sem.extend_inhabited _ _ _ _ extended

/-- A premise whose occurrence is allowed and whose equation a denoted substitution solves is
accepted. -/
theorem attempt_complete (role : Role) (pattern : T) (m : Match V B) (x : ℕ × V) (σ : S)
    (allowed : role.allows m x.1 = true) (denoted : Sem.Denotes m.bindings σ)
    (solves : A.E (A.apply σ pattern) (Sem.embed x.2)) :
    ∃ m', attempt M role pattern m x = some m' ∧ Sem.Denotes m'.bindings σ ∧
      m' = m.select role x.1 m'.bindings := by
  obtain ⟨θ, extended, denotes⟩ := (Sem.extend_iff m.bindings pattern x.2 σ).mpr ⟨denoted, solves⟩
  have bound : (m.select role x.1 θ).bindings = θ := by cases role <;> rfl
  refine ⟨m.select role x.1 θ, ?_, by rw [bound]; exact denotes, by rw [bound]⟩
  simp [attempt, allowed, extended]

/-- **Takes at distinct occurrences, apart from the reads, with solved equations, are accepted.** -/
theorem attemptAll_take_complete (patterns : List T) (m : Match V B) (xs : List (ℕ × V)) (σ : S)
    (distinct : (m.taken ++ xs.map Prod.fst).Nodup) (apart : ∀ o ∈ xs.map Prod.fst, o ∉ m.read)
    (denoted : Sem.Denotes m.bindings σ)
    (solves : List.Forall₂ (fun p x => A.E (A.apply σ p) (Sem.embed x.2)) patterns xs) :
    ∃ m', attemptAll M .take patterns m xs = some m' := by
  induction patterns generalizing m xs with
  | nil =>
      cases xs with
      | nil => exact ⟨m, rfl⟩
      | cons _ _ => simp at solves
  | cons p ps ih =>
      cases xs with
      | nil => simp at solves
      | cons x xs =>
          obtain ⟨first, rest⟩ := List.forall₂_cons.mp solves
          have allowed : Role.allows .take m x.1 = true := by
            have notTaken : x.1 ∉ m.taken := by
              intro inside
              exact (List.nodup_append.mp distinct).2.2 x.1 inside x.1 (by simp) rfl
            have notRead : x.1 ∉ m.read := apart x.1 (by simp)
            simp [Role.allows, notTaken, notRead]
          obtain ⟨m₁, tried, denotes, shape⟩ := Sem.attempt_complete .take p m x σ allowed denoted first
          have shapeTaken : m₁.taken = m.taken ++ [x.1] := by rw [shape]; rfl
          have shapeRead : m₁.read = m.read := by rw [shape]; rfl
          obtain ⟨m', accepted⟩ := ih m₁ xs
            (by rw [shapeTaken]; simpa [List.append_assoc] using distinct)
            (fun o inside => by rw [shapeRead]; exact apart o (by simp [inside]))
            denotes rest
          exact ⟨m', by simp [attemptAll, tried, accepted]⟩

/-- **Reads apart from the takes, with solved equations, are accepted.** -/
theorem attemptAll_read_complete (patterns : List T) (m : Match V B) (ys : List (ℕ × V)) (σ : S)
    (apart : ∀ o ∈ ys.map Prod.fst, o ∉ m.taken) (denoted : Sem.Denotes m.bindings σ)
    (solves : List.Forall₂ (fun p x => A.E (A.apply σ p) (Sem.embed x.2)) patterns ys) :
    ∃ m', attemptAll M .read patterns m ys = some m' := by
  induction patterns generalizing m ys with
  | nil =>
      cases ys with
      | nil => exact ⟨m, rfl⟩
      | cons _ _ => simp at solves
  | cons p ps ih =>
      cases ys with
      | nil => simp at solves
      | cons y ys =>
          obtain ⟨first, rest⟩ := List.forall₂_cons.mp solves
          have allowed : Role.allows .read m y.1 = true := by
            have notTaken : y.1 ∉ m.taken := apart y.1 (by simp)
            simp [Role.allows, notTaken]
          obtain ⟨m₁, tried, denotes, shape⟩ := Sem.attempt_complete .read p m y σ allowed denoted first
          have shapeTaken : m₁.taken = m.taken := by rw [shape]; rfl
          obtain ⟨m', accepted⟩ := ih m₁ ys
            (fun o inside => by rw [shapeTaken]; exact apart o (by simp [inside])) denotes rest
          exact ⟨m', by simp [attemptAll, tried, accepted]⟩

end Semantics

/-! ## Determinate goals -/

section Determinate

variable [DecidableEq V] {M : Matcher T V B}

omit [DecidableEq V] in
theorem applyAll_append (s : Store V) (first second : List (Determinate T)) (m : Match V B)
    [DecidableEq V] :
    applyAll M s (first ++ second) m = (applyAll M s first m).bind (applyAll M s second) := by
  induction first generalizing m with
  | nil => simp [applyAll]
  | cons d ds ih =>
      simp only [List.cons_append, applyAll]
      cases d.apply M s m with
      | none => rfl
      | some m' => simpa using ih m'

theorem applyAll_tells (s : Store V) (tells : EquationStore T) (m : Match V B) :
    applyAll M s (tells.map fun e => .tell e.1 e.2) m =
      if ∀ e ∈ tells, agree M m.bindings e.1 e.2 = true then some m else none := by
  induction tells with
  | nil => simp [applyAll]
  | cons e es ih =>
      simp only [List.map_cons, applyAll, Determinate.apply, List.forall_mem_cons]
      by_cases here : agree M m.bindings e.1 e.2 = true
      · simp only [here, if_true, Option.bind_some, ih, true_and]
      · simp [here]

theorem applyAll_checks (s : Store V) (checks : List (Check T)) (m : Match V B) :
    applyAll M s (checks.map .check) m =
      if ∀ c ∈ checks, passes M s m.bindings c = true then some m else none := by
  induction checks with
  | nil => simp [applyAll]
  | cons c cs ih =>
      simp only [List.map_cons, applyAll, Determinate.apply, List.forall_mem_cons]
      by_cases here : passes M s m.bindings c = true
      · simp only [here, if_true, Option.bind_some, ih, true_and]
      · simp [here]

/-- The collect patterns record the occurrences carrying each instantiated value. -/
theorem applyAll_collects (s : Store V) (patterns : List T) (m m' : Match V B) :
    applyAll M s (patterns.map .collect) m = some m' ↔
      ∃ ws : List V, List.Forall₂ (fun p w => M.instantiate m.bindings p = some w) patterns ws ∧
        m' = {m with seen := m.seen ++ ws.map fun w => (s.carrying w).toFinset} := by
  induction patterns generalizing m with
  | nil =>
      simp only [List.map_nil, applyAll, Option.some.injEq, List.forall₂_nil_left_iff,
        exists_eq_left, List.map_nil, List.append_nil]
      constructor
      · rintro rfl
        rfl
      · rintro rfl
        rfl
  | cons p ps ih =>
      simp only [List.map_cons, applyAll, Determinate.apply]
      cases inst : M.instantiate m.bindings p with
      | none =>
          simp only [Option.map_none, Option.bind_none, reduceCtorEq, false_iff, not_exists, not_and]
          intro ws related
          cases ws with
          | nil => simp at related
          | cons w _ => simp [inst] at related
      | some w =>
          simp only [Option.map_some, Option.bind_some]
          rw [ih]
          constructor
          · rintro ⟨ws, related, rfl⟩
            exact ⟨w :: ws, List.Forall₂.cons inst related, by simp [List.append_assoc]⟩
          · rintro ⟨ws, related, rfl⟩
            cases ws with
            | nil => simp at related
            | cons w' ws =>
                obtain ⟨head, tail⟩ := List.forall₂_cons.mp related
                rw [inst] at head
                cases head
                exact ⟨ws, tail, by simp [List.append_assoc]⟩

/-- The produced terms record their instantiated values. -/
theorem applyAll_produces (s : Store V) (templates : List T) (m m' : Match V B) :
    applyAll M s (templates.map .produce) m = some m' ↔
      ∃ ws : List V, List.Forall₂ (fun t w => M.instantiate m.bindings t = some w) templates ws ∧
        m' = {m with made := m.made ++ ws} := by
  induction templates generalizing m with
  | nil =>
      simp only [List.map_nil, applyAll, Option.some.injEq, List.forall₂_nil_left_iff,
        exists_eq_left, List.append_nil]
      constructor
      · rintro rfl
        rfl
      · rintro rfl
        rfl
  | cons t ts ih =>
      simp only [List.map_cons, applyAll, Determinate.apply]
      cases inst : M.instantiate m.bindings t with
      | none =>
          simp only [Option.map_none, Option.bind_none, reduceCtorEq, false_iff, not_exists, not_and]
          intro ws related
          cases ws with
          | nil => simp at related
          | cons w _ => simp [inst] at related
      | some w =>
          simp only [Option.map_some, Option.bind_some]
          rw [ih]
          constructor
          · rintro ⟨ws, related, rfl⟩
            exact ⟨w :: ws, List.Forall₂.cons inst related, by simp [List.append_assoc]⟩
          · rintro ⟨ws, related, rfl⟩
            cases ws with
            | nil => simp at related
            | cons w' ws =>
                obtain ⟨head, tail⟩ := List.forall₂_cons.mp related
                rw [inst] at head
                cases head
                exact ⟨ws, tail, by simp [List.append_assoc]⟩

/-- Record collected sets and made values. -/
def Match.record (m : Match V B) (seen : List (Finset ℕ)) (made : List V) : Match V B :=
  ⟨m.bindings, m.taken, m.read, m.seen ++ seen, m.made ++ made⟩

/-- **The determinate goals of a rule pass** exactly when its tells agree, its checks pass, and its
collected and produced terms instantiate; the match then records the collected occurrences and the
produced values. -/
theorem applyAll_determinates_iff (s : Store V) (r : Rule T) (m m' : Match V B) :
    applyAll M s (determinates r) m = some m' ↔
      (∀ e ∈ r.body.tell, agree M m.bindings e.1 e.2 = true) ∧
      (∀ c ∈ r.body.checks, passes M s m.bindings c = true) ∧
      ∃ cs ws : List V,
        List.Forall₂ (fun p w => M.instantiate m.bindings p = some w) r.collect cs ∧
        List.Forall₂ (fun t w => M.instantiate m.bindings t = some w) r.body.produce ws ∧
        m' = Match.record m (cs.map (fun w => (s.carrying w).toFinset)) ws := by
  unfold determinates
  rw [applyAll_append, applyAll_append, applyAll_append, applyAll_tells]
  by_cases tells : ∀ e ∈ r.body.tell, agree M m.bindings e.1 e.2 = true
  · rw [if_pos tells, Option.bind_some, applyAll_checks]
    by_cases checks : ∀ c ∈ r.body.checks, passes M s m.bindings c = true
    · rw [if_pos checks, Option.bind_some]
      constructor
      · intro applied
        cases collected : applyAll M s (r.collect.map .collect) m with
        | none => simp [collected] at applied
        | some m₁ =>
            rw [collected, Option.bind_some] at applied
            obtain ⟨cs, csRelated, rfl⟩ := (applyAll_collects s r.collect m m₁).mp collected
            obtain ⟨ws, wsRelated, rfl⟩ := (applyAll_produces s r.body.produce _ m').mp applied
            exact ⟨tells, checks, cs, ws, csRelated, wsRelated, rfl⟩
      · rintro ⟨_, _, cs, ws, csRelated, wsRelated, rfl⟩
        rw [(applyAll_collects s r.collect m _).mpr ⟨cs, csRelated, rfl⟩, Option.bind_some]
        exact (applyAll_produces s r.body.produce _ _).mpr ⟨ws, wsRelated, rfl⟩
    · rw [if_neg checks]
      simp only [Option.bind_none, reduceCtorEq, false_iff, not_and]
      exact fun _ passing => absurd passing checks
  · rw [if_neg tells]
    simp only [Option.bind_none, reduceCtorEq, false_iff, not_and]
    exact fun agreeing => absurd agreeing tells

end Determinate

end Mettapedia.Machines.TIsa.Derivation
