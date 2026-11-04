import Mettapedia.Languages.MeTTa.PeTTa.Legacy.ContractTyping.Rules

/-!
# Runs with checks, retained obligations, and erasure

A run is a pipeline of steps over branches. A branch holds its bindings and the obligations
retained on its open values; the world (the effect trace) is threaded through backtracking.
A body step answers with binding extensions; a check step tests a condition on the bindings
and raises a type error when it fails.

With retention (`retain = true`) a passed check stays attached to the branch, as SWI's
`when(nonvar(V), check(V, T))` on the open parts of `V`: every later binding extension re-tests
it, and a binding that breaks it raises at that moment. A body step is one binding extension;
a body that binds and then acts is two steps.

Removing pure checks preserves the answers and effects of every run without a type error
(`erasure_preserves_observations`); purity is needed (`effectful_check_breaks_erasure`). A check
holding under every binding (`inst_check_redundant`), or one an earlier check retained
(`retained_check_redundant`), is removable from every run; without retention, erasing a later
check on compat evidence turns a type error into an answer (`open_alias_needs_retention`).

`when(ground(V), ...)`, which the checker uses for unions, re-tests only once `V` is ground. The
retained condition is then weaker than the immediate one, and `retained_check_redundant` covers
such a check only on runs without type errors, through `erasure_preserves_observations`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Legacy.ContractTyping

/-- The bindings of a branch. -/
abbrev Bindings := Nat → Term

/-- The condition a check tests on the bindings. -/
abbrev Cond := Bindings → Bool

universe u

inductive Step (W : Type u) where
  /-- A body or builtin: its answers, each the bindings of a branch, and the world it leaves. -/
  | run (f : Bindings → W → List Bindings × W)
  /-- A check performs `effect` and tests `c`. A generated check is pure: `effect = id`. -/
  | check (c : Cond) (effect : W → W)

/-- A branch: its bindings and its retained obligations. -/
structure Local where
  θ : Bindings
  obs : List Cond

/-- Every obligation of the branch holds at its bindings. -/
def Local.Live (l : Local) : Prop := l.obs.all (· l.θ) = true

/-- Answers in order, with duplicates, and the final world; or a type error and the world at
that point. -/
abbrev Obs (W : Type u) := Except W (List Bindings × W)

variable {W : Type u}

/-- Run the branches in order, threading the world; the first error ends the run. -/
def thread (k : Bindings → W → Obs W) : List Bindings → W → Obs W
  | [], w => .ok ([], w)
  | θ :: θs, w => match k θ w with
    | .error w' => .error w'
    | .ok (as, w') => match thread k θs w' with
      | .error w'' => .error w''
      | .ok (bs, w'') => .ok (as ++ bs, w'')

def exec (retain : Bool) : List (Step W) → Local → W → Obs W
  | [], l, w => .ok ([l.θ], w)
  | .check c e :: ps, l, w =>
      if c l.θ then exec retain ps ⟨l.θ, if retain then c :: l.obs else l.obs⟩ (e w)
      else .error (e w)
  | .run f :: ps, l, w =>
      thread (fun θ w' => if l.obs.all (· θ) then exec retain ps ⟨θ, l.obs⟩ w' else .error w')
        (f l.θ w).1 (f l.θ w).2

theorem thread_congr {k k' : Bindings → W → Obs W} (h : ∀ θ w, k θ w = k' θ w) :
    ∀ (θs : List Bindings) (w : W), thread k θs w = thread k' θs w
  | [], _ => rfl
  | θ :: θs, w => by simp only [thread, h θ w, thread_congr h θs]

theorem thread_ok {k k' : Bindings → W → Obs W} (h : ∀ θ w r, k θ w = .ok r → k' θ w = .ok r) :
    ∀ (θs : List Bindings) (w : W) (r : List Bindings × W),
      thread k θs w = .ok r → thread k' θs w = .ok r
  | [], _, _, hr => hr
  | θ :: θs, w, r, hr => by
      simp only [thread] at hr ⊢
      cases hk : k θ w with
      | error e => simp [hk] at hr
      | ok p =>
          obtain ⟨as, w'⟩ := p
          simp only [hk] at hr
          simp only [h θ w _ hk]
          cases ht : thread k θs w' with
          | error e => simp [ht] at hr
          | ok q => simpa [ht, thread_ok h θs w' q ht] using hr

/-- A run sees its obligations only through whether they all hold. -/
theorem exec_congr (retain : Bool) :
    ∀ (ps : List (Step W)) {l₁ l₂ : Local} (w : W), l₁.θ = l₂.θ →
      (∀ θ, l₁.obs.all (· θ) = l₂.obs.all (· θ)) → exec retain ps l₁ w = exec retain ps l₂ w
  | [], l₁, l₂, w, hθ, _ => by simp [exec, hθ]
  | .check c e :: ps, l₁, l₂, w, hθ, h => by
      simp only [exec, hθ]
      split
      · exact exec_congr retain ps _ rfl fun θ => by cases retain <;> simp [h θ]
      · rfl
  | .run f :: ps, l₁, l₂, w, hθ, h => by
      simp only [exec, hθ]
      refine thread_congr (fun θ w' => ?_) _ _
      rw [h θ]
      split
      · exact exec_congr retain ps (l₁ := ⟨θ, l₁.obs⟩) (l₂ := ⟨θ, l₂.obs⟩) w' rfl h
      · rfl

theorem retained_mono (retain : Bool) (c : Cond) {o₁ o₂ : List Cond} (h : ∀ d ∈ o₁, d ∈ o₂) :
    ∀ d ∈ (if retain then c :: o₁ else o₁), d ∈ (if retain then c :: o₂ else o₂) := by
  cases retain
  · exact h
  · intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (h d hd)

/-! ## Erasure -/

/-- `ps'` is `ps` with some pure checks removed. -/
inductive Erases : List (Step W) → List (Step W) → Prop
  | nil : Erases [] []
  | keep (s : Step W) {ps' ps : List (Step W)} : Erases ps' ps → Erases (s :: ps') (s :: ps)
  | drop (c : Cond) {ps' ps : List (Step W)} : Erases ps' ps → Erases ps' (.check c id :: ps)

theorem Erases.ok {ps' ps : List (Step W)} (h : Erases ps' ps) (retain : Bool) :
    ∀ {l l' : Local} {w : W} {r : List Bindings × W}, l'.θ = l.θ → (∀ c ∈ l'.obs, c ∈ l.obs) →
      exec retain ps l w = .ok r → exec retain ps' l' w = .ok r := by
  induction h with
  | nil => intro l l' w r hθ _ hr; simpa [exec, hθ] using hr
  | keep s _ ih =>
      intro l l' w r hθ hobs hr
      cases s with
      | check c e =>
          simp only [exec, hθ] at hr ⊢
          by_cases hc : c l.θ = true
          · rw [if_pos hc] at hr ⊢
            exact ih (l := ⟨l.θ, if retain then c :: l.obs else l.obs⟩)
              (l' := ⟨l.θ, if retain then c :: l'.obs else l'.obs⟩) rfl (retained_mono retain c hobs) hr
          · rw [if_neg hc] at hr; cases hr
      | run f =>
          simp only [exec, hθ] at hr ⊢
          refine thread_ok (fun θ w r' hk => ?_) _ _ _ hr
          by_cases hg : (l.obs.all fun x => x θ) = true
          · rw [if_pos hg] at hk
            rw [if_pos (List.all_eq_true.2 fun d hd => List.all_eq_true.1 hg d (hobs d hd))]
            exact ih (l := ⟨θ, l.obs⟩) (l' := ⟨θ, l'.obs⟩) rfl hobs hk
          · rw [if_neg hg] at hk; cases hk
  | drop c _ ih =>
      intro l l' w r hθ hobs hr
      simp only [exec, id] at hr
      by_cases hc : c l.θ = true
      · rw [if_pos hc] at hr
        refine ih (l := ⟨l.θ, if retain then c :: l.obs else l.obs⟩) hθ (fun d hd => ?_) hr
        cases retain
        · exact hobs d hd
        · exact List.mem_cons_of_mem _ (hobs d hd)
      · rw [if_neg hc] at hr; cases hr

/-- Removing pure checks preserves the answers and the effects of every run that raises no
type error. -/
theorem erasure_preserves_observations {ps' ps : List (Step W)} (h : Erases ps' ps)
    (retain : Bool) (l : Local) (w : W) {r : List Bindings × W} (hr : exec retain ps l w = .ok r) :
    exec retain ps' l w = .ok r :=
  h.ok retain rfl (fun _ hc => hc) hr

/-- A check that passes and performs an effect (a `get-type` rule that logs, say) cannot be
erased: the run's effects change. -/
theorem effectful_check_breaks_erasure :
    ∃ (c : Cond) (e : Nat → Nat), (∀ θ, c θ = true) ∧ ∀ (retain : Bool) (l : Local),
      (exec retain [.check c e] l 0).map Prod.snd = .ok 1 ∧
        (exec retain ([] : List (Step Nat)) l 0).map Prod.snd = .ok 0 :=
  ⟨fun _ => true, (· + 1), fun _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩

/-! ## Retained obligations -/

/-- A check whose condition holds under every binding is removable from every run. -/
theorem inst_check_redundant {c : Cond} (hc : ∀ θ, c θ = true) (retain : Bool)
    (ps : List (Step W)) (l : Local) (w : W) :
    exec retain (.check c id :: ps) l w = exec retain ps l w := by
  simp only [exec, hc, if_true, id]
  exact exec_congr retain ps w rfl fun θ => by cases retain <;> simp [hc]

/-- With retention, a check whose condition an earlier check retained is removable from every
run: the obligation was re-tested at every binding since. -/
theorem retained_check_redundant (c : Cond) (ps₂ : List (Step W)) :
    ∀ (ps₁ : List (Step W)) (l : Local) (w : W), l.Live → (c ∈ l.obs ∨ ∃ e, .check c e ∈ ps₁) →
      exec true (ps₁ ++ .check c id :: ps₂) l w = exec true (ps₁ ++ ps₂) l w
  | [], l, w, hl, hc => by
      have hc : c ∈ l.obs := hc.resolve_right (by simp)
      simp only [List.nil_append, exec, List.all_eq_true.1 hl c hc, if_true, id]
      exact exec_congr true ps₂ w rfl fun θ => by
        simp only [List.all_cons, Bool.and_eq_right_iff_imp]
        exact fun h => List.all_eq_true.1 h c hc
  | .check c' e' :: ps₁, l, w, hl, hc => by
      simp only [List.cons_append, exec, if_true]
      split
      · refine retained_check_redundant c ps₂ ps₁ _ _ (by simp_all [Local.Live]) ?_
        rcases hc with hc | ⟨e, he⟩
        · exact .inl (List.mem_cons_of_mem _ hc)
        · rcases List.mem_cons.1 he with he | he
          · cases he; exact .inl List.mem_cons_self
          · exact .inr ⟨e, he⟩
      · rfl
  | .run f :: ps₁, l, w, hl, hc => by
      simp only [List.cons_append, exec]
      refine thread_congr (fun θ w' => ?_) _ _
      split
      · refine retained_check_redundant c ps₂ ps₁ _ _ ‹_› ?_
        rcases hc with hc | ⟨e, he⟩
        · exact .inl hc
        · exact .inr ⟨e, by simpa using he⟩
      · rfl

/-! ## The open alias -/

namespace OpenAlias

/-- `x : Number`, tested on the current value of the logic variable `x` (variable `0`). -/
def xIsNumber : Cond := fun θ => primTest .number ((Term.var 0).subst θ)

/-- The test is the value relation at `Number`. -/
theorem xIsNumber_iff (sig : Sig) (θ : Bindings) :
    xIsNumber θ = true ↔ Fits sig ((Term.var 0).subst θ) (.prim .number) :=
  primTest_iff sig _ _

/-- A body that binds `x` to a string. -/
def bindString : Step Unit := .run fun θ w => ([fun x => if x = 0 then .lit (.str "s") else θ x], w)

/-- Check `x : Number` while `x` is unbound, bind it, and check again. -/
def reference : List (Step Unit) := [.check xIsNumber id, bindString, .check xIsNumber id]

/-- The second check erased on the evidence of the first. -/
def erased : List (Step Unit) := [.check xIsNumber id, bindString]

def start : Local := ⟨.var, []⟩

/-- Without retention, erasing the second check turns the type error into an answer; with
retention, the binding itself raises and erasure changes nothing. -/
theorem open_alias_needs_retention :
    exec false reference start () = .error () ∧ (∃ r, exec false erased start () = .ok r) ∧
      exec true reference start () = .error () ∧ exec true erased start () = .error () :=
  ⟨rfl, ⟨_, rfl⟩, rfl, rfl⟩

end OpenAlias

end Mettapedia.Languages.MeTTa.PeTTa.Legacy.ContractTyping
