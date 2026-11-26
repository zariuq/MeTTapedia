import Mettapedia.Machines.TIsa.Derivation.Evaluator

/-!
# The evaluator in continuation-passing style

The second stage of the derivation. The evaluator is CPS-transformed with two continuations, the
standard rendering of backtracking (Biernacki and Danvy, *From interpreter to logic engine by
defunctionalization*, 2003): a success continuation receives a match together with the failure
continuation to resume, and a failure continuation resumes the newest alternative.

* `scanK` tries the occurrences of the store for one premise; each accepted occurrence passes its
  match on, with the scan of the remaining occurrences as its failure continuation.
* `solveK` solves goals; a determinate goal that fails calls the failure continuation.
* `rulesK` tries the rules in order; each rule's failure continuation tries the next rules.
* `takeAllK` and `makeAllK` publish, passing the store on.
* `runK` is the run: its success continuation pays for the firing, publishes and runs on, ignoring
  the failure continuation it receives; its failure continuation ends quiescent.

Each is proved equal to the direct-style evaluator: `solveK_eq` and `rulesK_eq` against the list of
matches folded through the continuations (`chain`), and `runK_eq` against `run`. Equality of the
outcomes gives both directions of the correspondence at once.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation

universe u v w r

variable {T : Type u} {V : Type v} {B : Type w} [DecidableEq V] (M : Matcher T V B) {R : Type r}

/-- Feed answers to a success continuation, in order, then call the failure continuation. -/
def chain (sk : Match V B → (Unit → R) → R) (fk : Unit → R) : List (Match V B) → R
  | [] => fk ()
  | m :: ms => sk m (fun _ => chain sk fk ms)

omit [DecidableEq V] in
theorem chain_append (sk : Match V B → (Unit → R) → R) (fk : Unit → R) :
    ∀ first second : List (Match V B),
      chain sk fk (first ++ second) = chain sk (fun _ => chain sk fk second) first
  | [], _ => rfl
  | m :: ms, second => by
      simp only [List.cons_append, chain]
      congr 1
      funext _
      exact chain_append sk fk ms second

/-- **A premise's scan of the store, in continuation-passing style.** -/
def scanK (role : Role) (pattern : T) (next : Match V B → (Unit → R) → R) :
    List (ℕ × V) → Match V B → (Unit → R) → R
  | [], _, fk => fk ()
  | x :: rest, m, fk =>
      match attempt M role pattern m x with
      | some m' => next m' (fun _ => scanK role pattern next rest m fk)
      | none => scanK role pattern next rest m fk

/-- **Goals in continuation-passing style.** -/
def solveK (s : Store V) : List (Goal T) → Match V B → (Match V B → (Unit → R) → R) → (Unit → R) → R
  | [], m, sk, fk => sk m fk
  | .premise role pattern :: gs, m, sk, fk =>
      scanK M role pattern (fun m' fk' => solveK s gs m' sk fk') s.occurrences m fk
  | .determinate d :: gs, m, sk, fk =>
      match d.apply M s m with
      | some m' => solveK s gs m' sk fk
      | none => fk ()

omit [DecidableEq V] in
theorem scanK_eq (role : Role) (pattern : T) (next : Match V B → (Unit → R) → R)
    (gsSolve : Match V B → List (Match V B)) {sk : Match V B → (Unit → R) → R}
    (nextChain : ∀ m' fk', next m' fk' = chain sk fk' (gsSolve m')) :
    ∀ (cands : List (ℕ × V)) (m : Match V B) (fk : Unit → R),
      scanK M role pattern next cands m fk =
        chain sk fk (cands.flatMap fun x =>
          match attempt M role pattern m x with
          | some m' => gsSolve m'
          | none => [])
  | [], _, _ => rfl
  | x :: rest, m, fk => by
      simp only [scanK, List.flatMap_cons]
      cases attempt M role pattern m x with
      | none =>
          simp only [List.nil_append]
          exact scanK_eq role pattern next gsSolve nextChain rest m fk
      | some m' =>
          simp only
          rw [nextChain, chain_append]
          congr 1
          funext _
          exact scanK_eq role pattern next gsSolve nextChain rest m fk

/-- **The CPS goals compute the direct-style matches**, fed to the continuations in order. -/
theorem solveK_eq (s : Store V) :
    ∀ (gs : List (Goal T)) (m : Match V B) (sk : Match V B → (Unit → R) → R) (fk : Unit → R),
      solveK M s gs m sk fk = chain sk fk (solve M s gs m)
  | [], m, sk, fk => rfl
  | .premise role pattern :: gs, m, sk, fk => by
      simp only [solveK, solve]
      exact scanK_eq M role pattern _ (solve M s gs) (fun m' fk' => solveK_eq s gs m' sk fk')
        s.occurrences m fk
  | .determinate d :: gs, m, sk, fk => by
      simp only [solveK, solve]
      cases d.apply M s m with
      | none => rfl
      | some m' => exact solveK_eq s gs m' sk fk

/-- **The rules in order, in continuation-passing style**, each started from the empty match. -/
def rulesK (s : Store V) (sk : Match V B → (Unit → R) → R) : List (Rule T) → (Unit → R) → R
  | [], fk => fk ()
  | r :: rs, fk => solveK M s (goals r) (Match.start M) sk (fun _ => rulesK s sk rs fk)

theorem rulesK_eq (s : Store V) (sk : Match V B → (Unit → R) → R) :
    ∀ (P : List (Rule T)) (fk : Unit → R),
      rulesK M s sk P fk = chain sk fk ((firings M P s).map Prod.snd)
  | [], _ => rfl
  | r :: rs, fk => by
      simp only [rulesK, firings, List.flatMap_cons, List.map_append, List.map_map]
      rw [solveK_eq, chain_append]
      have rest := rulesK_eq s sk rs fk
      simp only [firings, List.map_flatMap] at rest
      simp only [Function.comp_def, List.map_id']
      congr 1
      funext _
      rw [rest]
      simp [List.map_flatMap, Function.comp_def]

/-- Removing occurrences, passing the store on. -/
def takeAllK (s : Store V) : List ℕ → (Store V → R) → R
  | [], k => k s
  | o :: os, k => takeAllK (s.remove o) os k

/-- Adding values, passing the store on. -/
def makeAllK (s : Store V) : List V → (Store V → R) → R
  | [], k => k s
  | w :: ws, k => makeAllK (s.add w) ws k

omit [DecidableEq V] in
theorem takeAllK_eq (k : Store V → R) : ∀ (s : Store V) (os : List ℕ), takeAllK s os k = k (s.takeAll os)
  | _, [] => rfl
  | s, o :: os => takeAllK_eq k (s.remove o) os

omit [DecidableEq V] in
theorem makeAllK_eq (k : Store V → R) : ∀ (s : Store V) (ws : List V), makeAllK s ws k = k (s.makeAll ws)
  | _, [] => rfl
  | s, w :: ws => makeAllK_eq k (s.add w) ws

/-- **The run in continuation-passing style.** The success continuation pays for the firing,
publishes and runs on; with no allowance left it ends exhausted. The failure continuation ends
quiescent. -/
def runK (P : List (Rule T)) : ℕ → Store V → Outcome V
  | 0, s => rulesK M s (fun _ _ => .exhausted s) P (fun _ => .quiescent s)
  | a + 1, s =>
      rulesK M s (fun m _ => takeAllK s m.taken fun s' => makeAllK s' m.made fun s'' => runK P a s'') P
        (fun _ => .quiescent s)

omit [DecidableEq V] in
theorem chain_committed (k : Match V B → Outcome V) (fk : Unit → Outcome V) (ms : List (Match V B)) :
    chain (fun m _ => k m) fk ms = match ms with
      | [] => fk ()
      | m :: _ => k m := by
  cases ms <;> rfl

/-- **The CPS run is the run.** -/
theorem runK_eq (P : List (Rule T)) : ∀ (a : ℕ) (s : Store V), runK M P a s = run M P a s
  | 0, s => by
      rw [runK, rulesK_eq, chain_committed]
      cases first : firings M P s with
      | nil => simp [run, first]
      | cons f rest => simp [run, first]
  | a + 1, s => by
      rw [runK, rulesK_eq, chain_committed]
      cases first : firings M P s with
      | nil => simp [run, first]
      | cons f rest =>
          simp only [List.map_cons, run, first]
          rw [takeAllK_eq, makeAllK_eq, runK_eq P a]
          rfl

end Mettapedia.Machines.TIsa.Derivation
