import Mathlib.Tactic

/-!
# A root's program token covers its imported modules

A space reads its imported modules through a composed view: its own rows,
then the own rows of each module it links. Imports flatten, so a root links
every module it reads directly. A change to a module's equations or
declarations advances that projection's revision in the module and in every
space that links it; linking a module advances both revisions of the
importer. The program token is the pair of revisions.

Proved here: a step that leaves a space's token unchanged leaves its composed
equations and declarations unchanged, and so does any run of steps, because
revisions never decrease. Cached analyses keyed by the token are therefore
current whenever the token is.

Counterexample: if a view read a linked module's own links too (a recursive
view), a module that gains an import after the root linked it would change
the root's view while the root's token stays put. The flat view is what the
notification to direct importers relies on.

This is an abstract contract, not a refinement proof of `space.c`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ComposedViewProgramToken

variable {S E D : Type} [DecidableEq S]

structure State (S E D : Type) where
  eqs : S → List E
  decls : S → List D
  links : S → List S
  rev : S → ℕ × ℕ

def viewEqs (st : State S E D) (r : S) : List E :=
  st.eqs r ++ (st.links r).flatMap st.eqs

def viewDecls (st : State S E D) (r : S) : List D :=
  st.decls r ++ (st.links r).flatMap st.decls

inductive Step (S E D : Type) where
  | editEqs (m : S) (es : List E)
  | editDecls (m : S) (ds : List D)
  | link (r m : S)

/-- One step: the edited space and every space that links it advance the
edited projection; a link advances both revisions of the importer. -/
def step (st : State S E D) : Step S E D → State S E D
  | .editEqs m es =>
    { st with
      eqs := fun s => if s = m then es else st.eqs s
      rev := fun s => if s = m ∨ m ∈ st.links s then ((st.rev s).1 + 1, (st.rev s).2) else st.rev s }
  | .editDecls m ds =>
    { st with
      decls := fun s => if s = m then ds else st.decls s
      rev := fun s => if s = m ∨ m ∈ st.links s then ((st.rev s).1, (st.rev s).2 + 1) else st.rev s }
  | .link r m =>
    { st with
      links := fun s => if s = r then m :: st.links s else st.links s
      rev := fun s => if s = r then ((st.rev s).1 + 1, (st.rev s).2 + 1) else st.rev s }

omit [DecidableEq S] in
theorem flatMap_congr_of_ne {l : List S} {f g : S → List E} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

/-- A step that leaves a space's token unchanged leaves its composed view unchanged. -/
theorem view_unchanged_of_token_unchanged (st : State S E D) (s : Step S E D) (r : S)
    (h : (step st s).rev r = st.rev r) :
    viewEqs (step st s) r = viewEqs st r ∧ viewDecls (step st s) r = viewDecls st r := by
  cases s with
  | editEqs m es =>
    by_cases hr : r = m ∨ m ∈ st.links r
    · simp only [step, hr, if_true] at h
      have := congrArg Prod.fst h; simp at this
    · simp only [not_or] at hr
      refine ⟨?_, rfl⟩
      simp only [viewEqs, step, hr.1, if_false]
      congr 1
      exact flatMap_congr_of_ne (fun x hx => by
        have : x ≠ m := fun e => hr.2 (e ▸ hx)
        simp [this])
  | editDecls m ds =>
    by_cases hr : r = m ∨ m ∈ st.links r
    · simp only [step, hr, if_true] at h
      have := congrArg Prod.snd h; simp at this
    · simp only [not_or] at hr
      refine ⟨rfl, ?_⟩
      simp only [viewDecls, step, hr.1, if_false]
      congr 1
      exact flatMap_congr_of_ne (fun x hx => by
        have : x ≠ m := fun e => hr.2 (e ▸ hx)
        simp [this])
  | link r' m =>
    by_cases hr : r = r'
    · subst hr
      simp only [step, if_true] at h
      have := congrArg Prod.fst h; simp at this
    · simp [viewEqs, viewDecls, step, hr]

/-- Revisions never decrease. -/
theorem rev_mono (st : State S E D) (s : Step S E D) (r : S) :
    (st.rev r).1 ≤ ((step st s).rev r).1 ∧ (st.rev r).2 ≤ ((step st s).rev r).2 := by
  cases s <;> simp only [step] <;> split_ifs <;> simp

def run (st : State S E D) : List (Step S E D) → State S E D
  | [] => st
  | s :: rest => run (step st s) rest

theorem run_rev_mono (st : State S E D) (steps : List (Step S E D)) (r : S) :
    (st.rev r).1 ≤ ((run st steps).rev r).1 ∧ (st.rev r).2 ≤ ((run st steps).rev r).2 := by
  induction steps generalizing st with
  | nil => simp [run]
  | cons s rest ih =>
    obtain ⟨a, b⟩ := rev_mono st s r
    obtain ⟨c, d⟩ := ih (step st s)
    exact ⟨le_trans a c, le_trans b d⟩

/-- Over any run, an unchanged token means an unchanged composed view. -/
theorem view_unchanged_of_token_unchanged_run (st : State S E D) (steps : List (Step S E D)) (r : S)
    (h : (run st steps).rev r = st.rev r) :
    viewEqs (run st steps) r = viewEqs st r ∧ viewDecls (run st steps) r = viewDecls st r := by
  induction steps generalizing st with
  | nil => simp [run]
  | cons s rest ih =>
    have h' : (run (step st s) rest).rev r = st.rev r := h
    have hmono := run_rev_mono (step st s) rest r
    have h1 := rev_mono st s r
    have hfst := congrArg Prod.fst h'
    have hsnd := congrArg Prod.snd h'
    have hs : (step st s).rev r = st.rev r := by
      apply Prod.ext
      · omega
      · omega
    have hrest : (run (step st s) rest).rev r = (step st s).rev r := by rw [h', hs]
    obtain ⟨e1, d1⟩ := ih (step st s) hrest
    obtain ⟨e2, d2⟩ := view_unchanged_of_token_unchanged st s r hs
    exact ⟨e1.trans e2, d1.trans d2⟩

/-! ## Counterexample: a recursive view needs a cascade the notification does not make -/

def recursiveViewEqs (st : State Nat Nat Nat) (r : Nat) : List Nat :=
  st.eqs r ++ (st.links r).flatMap (fun m => st.eqs m ++ (st.links m).flatMap st.eqs)

/-- Root 0 links module 1; then module 1 links module 2, which has an equation.
The root's token is unchanged, but a recursive view of the root changed. -/
theorem recursive_view_breaks_token :
    let st : State Nat Nat Nat :=
      { eqs := fun s => if s = 2 then [7] else []
        decls := fun _ => []
        links := fun s => if s = 0 then [1] else []
        rev := fun _ => (0, 0) }
    let st' := step st (.link 1 2)
    st'.rev 0 = st.rev 0 ∧ recursiveViewEqs st' 0 ≠ recursiveViewEqs st 0 := by
  decide

end Mettapedia.Languages.MeTTa.ComposedViewProgramToken
