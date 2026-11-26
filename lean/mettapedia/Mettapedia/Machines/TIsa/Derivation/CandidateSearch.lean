import Mettapedia.Machines.TIsa.Derivation.ContinuationPassing

/-!
# Candidate access as a refinement of Transform search

The index selects occurrences, not values. It may omit a failed
comparison; it cannot discard another occurrence of an equal value.
The successful continuation receives the same matches in the same
order, so even a scheduler that commits to the first firing is exact.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation

universe u v w z

variable {T : Type u} {V : Type v} {B : Type w}

/-- A finite scan which lists real occurrences in source order, and
cannot lose a successful comparison with the bindings at entry. -/
structure CandidateAccess (M : Matcher T V B) where
  read : Store V → B → T → List (ℕ × V)
  selects : ∀ s bindings pattern, ∃ keep : V → Bool,
    read s bindings pattern = s.occurrences.filter (keep ∘ Prod.snd) ∧
    ∀ value next, M.extend bindings pattern value = some next → keep value = true

namespace CandidateAccess

variable {M : Matcher T V B}

def full : CandidateAccess M where
  read s _ _ := s.occurrences
  selects _ _ _ := ⟨fun _ => true, by simp, fun _ _ _ => rfl⟩

theorem sublist (access : CandidateAccess M) (s : Store V) (bindings : B) (pattern : T) :
    (access.read s bindings pattern).Sublist s.occurrences := by
  obtain ⟨_, filtered, _⟩ := access.selects s bindings pattern
  rw [filtered]
  exact List.filter_sublist

private theorem filterMap_compatible {α β : Type*} (f : α → Option β) (keep : α → Bool)
    (s : List α) (necessary : ∀ a b, f a = some b → keep a = true) :
    (s.filter keep).filterMap f = s.filterMap f := by
  induction s with
  | nil => rfl
  | cons a rest ih =>
    cases kept : keep a with
    | false =>
      have none : f a = none := by
        cases tried : f a with
        | none => rfl
        | some b => exact Bool.noConfusion (kept.symm.trans (necessary a b tried))
      simp [kept, none, ih]
    | true =>
      cases tried : f a <;> simp [kept, tried, ih]

/-- This formulation does not even require unique occurrence IDs:
the data structure must retain each comparison that can succeed. -/
def Exact (access : CandidateAccess M) : Prop :=
  ∀ (s : Store V) (role : Role) (pattern : T) (m : Match V B),
    (access.read s m.bindings pattern).filterMap (attempt M role pattern m) =
      s.occurrences.filterMap (attempt M role pattern m)

theorem exact (access : CandidateAccess M) : access.Exact := by
  intro s role pattern m
  obtain ⟨keep, filtered, necessary⟩ := access.selects s m.bindings pattern
  rw [filtered]
  apply filterMap_compatible
  intro occurrence result found
  unfold attempt at found
  split at found
  · cases extended : M.extend m.bindings pattern occurrence.2 with
    | none => simp [extended] at found
    | some new => exact necessary occurrence.2 new extended
  · cases found

end CandidateAccess

variable [DecidableEq V] (M : Matcher T V B)

/-- Binding search determines which candidates are consulted at each
premise, including keys bound by an earlier premise. -/
def solveUsing (access : CandidateAccess M) (s : Store V) :
    List (Goal T) → Match V B → List (Match V B)
  | [], m => [m]
  | .premise role pattern :: rest, m =>
    ((access.read s m.bindings pattern).filterMap (attempt M role pattern m)).flatMap
      (solveUsing access s rest)
  | .determinate goal :: rest, m =>
    match goal.apply M s m with
    | some next => solveUsing access s rest next
    | none => []

private theorem flatMap_filterMap_apply {α β γ : Type*} (test : α → Option β) (next : β → List γ)
    (occurrences : List α) :
    (occurrences.filterMap test).flatMap next =
      occurrences.flatMap (fun x => match test x with | some b => next b | none => []) := by
  induction occurrences with
  | nil => rfl
  | cons first rest ih =>
    cases tested : test first <;> simp [tested, ih]

theorem solveUsing_exact (access : CandidateAccess M) (s : Store V)
    (goals : List (Goal T)) (m : Match V B) :
    solveUsing M access s goals m = solve M s goals m := by
  induction goals generalizing m with
  | nil => rfl
  | cons first rest ih =>
    cases first with
    | premise role pattern =>
      rw [solveUsing, solve, access.exact s role pattern m, flatMap_filterMap_apply]
      apply List.flatMap_congr
      intro occurrence _
      cases attempt M role pattern m occurrence with
      | none => rfl
      | some next => exact ih next
    | determinate goal =>
      rw [solveUsing, solve]
      cases goal.apply M s m with
      | none => rfl
      | some next => exact ih next

def firingsUsing (access : CandidateAccess M) (program : List (Rule T)) (s : Store V) :
    List (Rule T × Match V B) :=
  program.flatMap fun rule =>
    (solveUsing M access s (goals rule) (Match.start M)).map fun matched => (rule, matched)

theorem firingsUsing_exact (access : CandidateAccess M) (program : List (Rule T)) (s : Store V) :
    firingsUsing M access program s = firings M program s := by
  unfold firingsUsing firings
  apply List.flatMap_congr
  intro rule _
  rw [solveUsing_exact M access s]

def solveKUsing {R : Type z} (access : CandidateAccess M) (s : Store V) :
    List (Goal T) → Match V B → (Match V B → (Unit → R) → R) → (Unit → R) → R
  | [], m, win, lose => win m lose
  | .premise role pattern :: rest, m, win, lose =>
    scanK M role pattern (fun next retry => solveKUsing access s rest next win retry)
      (access.read s m.bindings pattern) m lose
  | .determinate goal :: rest, m, win, lose =>
    match goal.apply M s m with
    | some next => solveKUsing access s rest next win lose
    | none => lose ()

theorem solveKUsing_eq {R : Type z} (access : CandidateAccess M) (s : Store V)
    (goals : List (Goal T)) (m : Match V B)
    (win : Match V B → (Unit → R) → R) (lose : Unit → R) :
    solveKUsing M access s goals m win lose = chain win lose (solveUsing M access s goals m) := by
  induction goals generalizing m lose with
  | nil => rfl
  | cons first rest ih =>
    cases first with
    | premise role pattern =>
      rw [solveKUsing, solveUsing, flatMap_filterMap_apply]
      refine (scanK_eq M role pattern
        (fun next retry => solveKUsing M access s rest next win retry) (solveUsing M access s rest)
        (fun next retry => ih next retry) (access.read s m.bindings pattern) m lose).trans ?_
      apply congrArg (chain win lose)
      apply List.flatMap_congr
      intro occurrence _
      cases found : attempt M role pattern m occurrence <;> rfl
    | determinate goal =>
      rw [solveKUsing, solveUsing]
      cases goal.apply M s m with
      | none => rfl
      | some next => exact ih next lose

end Mettapedia.Machines.TIsa.Derivation
