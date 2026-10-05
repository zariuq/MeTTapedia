import Mathlib.Data.List.Basic
import Mathlib.Data.List.Infix

/-!
# An equation's cut on a frame stack

PeTTa's `(cut)` is Prolog's `!`: it commits a call to the equation the cut
occurs in, dropping the call's untried equations and the alternatives the
goals before the cut left, and nothing older.  A machine that keeps every
alternative on one stack of frames implements it by recording, as a call's
equation starts, the stack's height beneath the call's own frame, and
truncating the stack to that height at the cut.

`den` is the continuation semantics of such equations: a success
continuation, the answers on failure, and the answers on failure when the
enclosing call entered, which a cut makes the answers on failure.  Its cut
drops the later equations (`equations_cut`) and keeps only the first answer
of the goals before it (`den_prim_cut`).

`step` is the frame machine.  A call pushes a frame of its equations;
resuming that frame starts its next equation with the barrier at the frame's
own index, whether or not equations remain after it; a cut truncates the
stack to the barrier.  Every step keeps a configuration's denotation, less the answer it
emits (`step_denote`), so the answers of any run are a prefix of the query's
denotation (`run_prefix`), and a run that ends has emitted all of it
(`run_answers`).  Termination is not claimed.

Controls: a barrier one frame higher keeps the call's untried equations alive
(`Controls.barrier_above_own_frame`), and a barrier at the bottom drops the
alternatives of the caller (`Controls.barrier_at_bottom`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.EquationCut

universe u

variable {S : Type u}

/-- An equation's body: goals in sequence, with branching on the state. -/
inductive Body (S : Type u) where
  | done
  | prim (f : S → List S) (k : Body S)
  | call (r : ℕ) (k : Body S)
  | cut (k : Body S)
  | branch (t : S → Bool) (yes no : Body S)

/-- Each relation's equations, in order. -/
abbrev Program (S : Type u) := ℕ → List (Body S)

/-- The answers of a body from state `s`, with at most `n` calls nested below
it (a call past them fails): `κ` continues each answer given the answers after
it, `φ` are the answers on failure, and `ψ` the answers on failure when the
enclosing call entered, which a cut restores. -/
def den (P : Program S) : ℕ → Body S → S → (S → List S → List S) → List S → List S →
    List S
  | _, .done, s, κ, φ, _ => κ s φ
  | n, .prim f k, s, κ, φ, ψ => (f s).foldr (fun t rest => den P n k t κ rest ψ) φ
  | n, .cut k, s, κ, _, ψ => den P n k s κ ψ ψ
  | n, .branch t yes no, s, κ, φ, ψ =>
      if t s then den P n yes s κ φ ψ else den P n no s κ φ ψ
  | 0, .call _ _, _, _, φ, _ => φ
  | n + 1, .call r k, s, κ, φ, ψ =>
      (P r).foldr
        (fun c rest => den P n c s (fun t φ' => den P (n + 1) k t κ φ' ψ) rest φ) φ
termination_by n body _ _ _ _ => (n, sizeOf body)

/-- A call's equations in order: each runs with the answers of the later ones
as its answers on failure, and with the call's own answers on failure as the
ones its cut restores. -/
def equations (P : Program S) (n : ℕ) (cs : List (Body S)) (s : S)
    (κ : S → List S → List S) (φ : List S) : List S :=
  cs.foldr (fun c rest => den P n c s κ rest φ) φ

theorem den_call (P : Program S) (n r : ℕ) (k : Body S) (s : S)
    (κ : S → List S → List S) (φ ψ : List S) :
    den P (n + 1) (.call r k) s κ φ ψ =
      equations P n (P r) s (fun t φ' => den P (n + 1) k t κ φ' ψ) φ := by
  rw [den]
  rfl

/-- An equation whose first goal is the cut drops the equations after it. -/
theorem equations_cut (P : Program S) (n : ℕ) (k : Body S) (cs : List (Body S)) (s : S)
    (κ : S → List S → List S) (φ : List S) :
    equations P n (.cut k :: cs) s κ φ = den P n k s κ φ φ := by
  simp only [equations, List.foldr_cons]
  rw [den]

/-- The goals before a cut contribute their first answer only. -/
theorem den_prim_cut (P : Program S) (n : ℕ) (f : S → List S) (k : Body S) (s : S)
    (κ : S → List S → List S) (φ ψ : List S) :
    den P n (.prim f (.cut k)) s κ φ ψ =
      match f s with
      | [] => φ
      | t :: _ => den P n k t κ ψ ψ := by
  rw [den]
  cases f s with
  | nil => rfl
  | cons t ts =>
      simp only [List.foldr_cons]
      rw [den]

/-! ## The frame machine -/

/-- Where a returning call continues: the caller's bound on nested calls, the
rest of its body, and its barrier. -/
structure Ret (S : Type u) where
  fuel : ℕ
  k : Body S
  barrier : ℕ

/-- A frame: a call's untried equations, or a goal's untried answers, which
continue the activation that left them. -/
inductive Frame (S : Type u) where
  | equations (fuel : ℕ) (cs : List (Body S)) (s : S) (rets : List (Ret S))
  | answers (fuel : ℕ) (ts : List S) (k : Body S) (barrier : ℕ) (rets : List (Ret S))

/-- A running activation: its bound on nested calls, the rest of its body, its
state, the height its cut truncates the stack to, and where its answers
return. -/
structure Act (S : Type u) where
  fuel : ℕ
  body : Body S
  s : S
  barrier : ℕ
  rets : List (Ret S)

/-- The running activation, if any, and the frames, newest first. -/
structure Config (S : Type u) where
  act : Option (Act S)
  frames : List (Frame S)

/-- A stack cut to height `b`: its `b` oldest entries. -/
def trunc {α : Type*} (b : ℕ) (fs : List α) : List α := fs.drop (fs.length - b)

theorem length_trunc {α : Type*} {b : ℕ} {fs : List α} (h : b ≤ fs.length) :
    (trunc b fs).length = b := by
  simp only [trunc, List.length_drop]
  omega

theorem trunc_cons {α : Type*} {b : ℕ} (x : α) {fs : List α} (h : b ≤ fs.length) :
    trunc b (x :: fs) = trunc b fs := by
  simp only [trunc, List.length_cons]
  rw [show fs.length + 1 - b = (fs.length - b) + 1 by omega, List.drop_succ_cons]

theorem trunc_trunc {α : Type*} {c b : ℕ} {fs : List α} (hcb : c ≤ b) (hb : b ≤ fs.length) :
    trunc c (trunc b fs) = trunc c fs := by
  simp only [trunc, List.length_drop, List.drop_drop]
  congr 1
  omega

theorem trunc_length {α : Type*} (fs : List α) : trunc fs.length fs = fs := by
  simp [trunc]

/-! A representation change may replace one frame by several target frames,
or remove a marker that has no target frame. A cut must retain the image of
its old stack prefix, rather than retain its old numerical height. These
laws concern ordered stack boundaries; translating each frame's computation,
bindings and ownership is a separate obligation. -/

/-- The target height of a barrier after replacing each source frame by an
ordered block of target frames. Stacks here have their newest frame first. -/
def expandedBarrier {α β : Type*} (blocks : α → List β) (b : ℕ) (fs : List α) : ℕ :=
  ((trunc b fs).flatMap blocks).length

theorem trunc_append_length {α : Type*} (newer older : List α) :
    trunc older.length (newer ++ older) = older := by
  simp [trunc]

/-- Expanding the stack and rebasing its barrier commutes with commitment.
The result preserves every retained occurrence, including duplicates. -/
theorem trunc_expanded {α β : Type*} (blocks : α → List β) (b : ℕ) (fs : List α) :
    trunc (expandedBarrier blocks b fs) (fs.flatMap blocks) =
      (trunc b fs).flatMap blocks := by
  have split : fs.flatMap blocks =
      (fs.take (fs.length - b)).flatMap blocks ++ (trunc b fs).flatMap blocks := by
    rw [← List.flatMap_append]
    simp [trunc]
  unfold expandedBarrier
  rw [split]
  exact trunc_append_length _ _

/-- The rebased barrier remains inside the translated stack. -/
theorem expandedBarrier_le_length {α β : Type*} (blocks : α → List β)
    (b : ℕ) (fs : List α) : expandedBarrier blocks b fs ≤ (fs.flatMap blocks).length := by
  have split : fs.flatMap blocks =
      (fs.take (fs.length - b)).flatMap blocks ++ (trunc b fs).flatMap blocks := by
    rw [← List.flatMap_append]
    simp [trunc]
  rw [split, List.length_append]
  exact Nat.le_add_left _ _

/-- Translating a stack in two stages rebases the barrier in two stages too. -/
theorem expandedBarrier_compose {α β γ : Type*} (first : α → List β)
    (second : β → List γ) (b : ℕ) (fs : List α) :
    expandedBarrier second (expandedBarrier first b fs) (fs.flatMap first) =
      expandedBarrier (fun frame => (first frame).flatMap second) b fs := by
  change ((trunc (expandedBarrier first b fs) (fs.flatMap first)).flatMap second).length =
    ((trunc b fs).flatMap fun frame => (first frame).flatMap second).length
  rw [trunc_expanded]
  simp only [List.flatMap_assoc]

/-- The frame machine, its equation frames resumed with the barrier `lift` of
the frame's index (the index itself in `step`). -/
def stepWith (P : Program S) (lift : ℕ → ℕ) : Config S → Option S × Config S
  | ⟨some ⟨_, .done, s, _, []⟩, fs⟩ => (some s, ⟨none, fs⟩)
  | ⟨some ⟨_, .done, s, _, r :: rets⟩, fs⟩ =>
      (none, ⟨some ⟨r.fuel, r.k, s, r.barrier, rets⟩, fs⟩)
  | ⟨some ⟨n, .prim f k, s, b, rets⟩, fs⟩ => (none, ⟨none, .answers n (f s) k b rets :: fs⟩)
  | ⟨some ⟨n, .cut k, s, b, rets⟩, fs⟩ => (none, ⟨some ⟨n, k, s, b, rets⟩, trunc b fs⟩)
  | ⟨some ⟨n, .branch t yes no, s, b, rets⟩, fs⟩ =>
      (none, ⟨some ⟨n, if t s then yes else no, s, b, rets⟩, fs⟩)
  | ⟨some ⟨0, .call _ _, _, _, _⟩, fs⟩ => (none, ⟨none, fs⟩)
  | ⟨some ⟨n + 1, .call r k, s, b, rets⟩, fs⟩ =>
      (none, ⟨none, .equations n (P r) s (⟨n + 1, k, b⟩ :: rets) :: fs⟩)
  | ⟨none, []⟩ => (none, ⟨none, []⟩)
  | ⟨none, .equations _ [] _ _ :: fs⟩ => (none, ⟨none, fs⟩)
  | ⟨none, .equations n (c :: cs) s rets :: fs⟩ =>
      (none, ⟨some ⟨n, c, s, lift fs.length, rets⟩, .equations n cs s rets :: fs⟩)
  | ⟨none, .answers _ [] _ _ _ :: fs⟩ => (none, ⟨none, fs⟩)
  | ⟨none, .answers n (t :: ts) k b rets :: fs⟩ =>
      (none, ⟨some ⟨n, k, t, b, rets⟩, .answers n ts k b rets :: fs⟩)

/-- One step: an answer it emits, if any, and the configuration it reaches. -/
def step (P : Program S) : Config S → Option S × Config S := stepWith P id

/-- The answers of `k` steps and the configuration they reach. -/
def runWith (P : Program S) (lift : ℕ → ℕ) : ℕ → Config S → List S × Config S
  | 0, cfg => ([], cfg)
  | k + 1, cfg =>
      ((stepWith P lift cfg).1.toList ++ (runWith P lift k (stepWith P lift cfg).2).1,
        (runWith P lift k (stepWith P lift cfg).2).2)

/-- The machine's run for `k` steps. -/
def run (P : Program S) : ℕ → Config S → List S × Config S := runWith P id

/-! ## What a configuration denotes -/

/-- The continuation of the answers returned through `rets`, with the answers
on failure beneath each caller's barrier read from `D`. -/
def kontWith (P : Program S) (D : ℕ → List S) : List (Ret S) → S → List S → List S
  | [] => fun t φ => t :: φ
  | r :: rets => fun t φ => den P r.fuel r.k t (kontWith P D rets) φ (D r.barrier)

/-- The answers of backtracking into a stack of frames. -/
def decode (P : Program S) : List (Frame S) → List S
  | [] => []
  | .equations n cs s rets :: fs =>
      equations P n cs s (kontWith P (fun b => decode P (trunc b fs)) rets) (decode P fs)
  | .answers n ts k b rets :: fs =>
      ts.foldr
        (fun t rest =>
          den P n k t (kontWith P (fun c => decode P (trunc c fs)) rets) rest
            (decode P (trunc b fs)))
        (decode P fs)
termination_by fs => fs.length
decreasing_by
  all_goals simp only [trunc, List.length_drop, List.length_cons]
  all_goals omega

/-- The continuation of returns `rets` over the stack `fs` beneath them. -/
def kont (P : Program S) (rets : List (Ret S)) (fs : List (Frame S)) :
    S → List S → List S :=
  kontWith P (fun b => decode P (trunc b fs)) rets

theorem decode_equations (P : Program S) (n : ℕ) (cs : List (Body S)) (s : S)
    (rets : List (Ret S)) (fs : List (Frame S)) :
    decode P (.equations n cs s rets :: fs) = equations P n cs s (kont P rets fs) (decode P fs) := by
  rw [decode]
  rfl

theorem decode_answers (P : Program S) (n : ℕ) (ts : List S) (k : Body S) (b : ℕ)
    (rets : List (Ret S)) (fs : List (Frame S)) :
    decode P (.answers n ts k b rets :: fs) =
      ts.foldr (fun t rest => den P n k t (kont P rets fs) rest (decode P (trunc b fs)))
        (decode P fs) := by
  rw [decode]
  rfl

/-- What a configuration denotes: the running activation's answers, then the
frames'. -/
def denote (P : Program S) : Config S → List S
  | ⟨none, fs⟩ => decode P fs
  | ⟨some a, fs⟩ =>
      den P a.fuel a.body a.s (kont P a.rets fs) (decode P fs) (decode P (trunc a.barrier fs))

/-! ## Well-formed configurations -/

/-- Each return's barrier lies at or below the one inside it, the innermost at
or below `b`. -/
def RetsOk : ℕ → List (Ret S) → Prop
  | _, [] => True
  | b, r :: rets => r.barrier ≤ b ∧ RetsOk r.barrier rets

/-- Each frame's barriers lie at or below its own index. -/
def FramesOk : List (Frame S) → Prop
  | [] => True
  | .equations _ _ _ rets :: fs => RetsOk fs.length rets ∧ FramesOk fs
  | .answers _ _ _ b rets :: fs => b ≤ fs.length ∧ RetsOk b rets ∧ FramesOk fs

/-- A configuration whose activation's barrier lies within the stack. -/
def Ok : Config S → Prop
  | ⟨none, fs⟩ => FramesOk fs
  | ⟨some a, fs⟩ => a.barrier ≤ fs.length ∧ RetsOk a.barrier a.rets ∧ FramesOk fs

theorem FramesOk.tail {fr : Frame S} {fs : List (Frame S)} (ok : FramesOk (fr :: fs)) :
    FramesOk fs := by
  cases fr with
  | equations => exact ok.2
  | answers => exact ok.2.2

theorem FramesOk.drop : ∀ (k : ℕ) {fs : List (Frame S)}, FramesOk fs → FramesOk (fs.drop k)
  | 0, _, ok => ok
  | _ + 1, [], _ => trivial
  | k + 1, _ :: _, ok => FramesOk.drop k ok.tail

theorem kontWith_congr (P : Program S) {D D' : ℕ → List S} :
    ∀ {b : ℕ} {rets : List (Ret S)}, RetsOk b rets → (∀ c ≤ b, D c = D' c) →
      kontWith P D rets = kontWith P D' rets
  | _, [], _, _ => rfl
  | _, r :: _, ⟨below, rest⟩, agree => by
      have inner := kontWith_congr P rest fun c hc => agree c (le_trans hc below)
      funext t φ
      simp only [kontWith, inner, agree r.barrier below]

/-- A frame pushed above the returns' barriers leaves their continuation. -/
theorem kont_cons (P : Program S) {b : ℕ} {rets : List (Ret S)} (fr : Frame S)
    {fs : List (Frame S)} (ok : RetsOk b rets) (hb : b ≤ fs.length) :
    kont P rets (fr :: fs) = kont P rets fs :=
  kontWith_congr P ok fun c hc => by rw [trunc_cons fr (le_trans hc hb)]

/-- A truncation at or above the returns' barriers leaves their continuation. -/
theorem kont_trunc (P : Program S) {b : ℕ} {rets : List (Ret S)} {fs : List (Frame S)}
    (ok : RetsOk b rets) (hb : b ≤ fs.length) :
    kont P rets (trunc b fs) = kont P rets fs :=
  kontWith_congr P ok fun c hc => by rw [trunc_trunc hc hb]

/-- A return whose rest of body is empty continues as the returns beneath it:
a call in a tail position may hand its caller's returns to its callee, and
each answer then returns once instead of once per level of such calls. -/
theorem kont_tail (P : Program S) (m b : ℕ) (rets : List (Ret S)) (fs : List (Frame S)) :
    kont P (⟨m, .done, b⟩ :: rets) fs = kont P rets fs := by
  funext t φ
  simp only [kont, kontWith]
  rw [den]

/-- A call in a tail position, entered with its caller's returns, pushes the
frame of its equations and no return; what the configuration denotes is the
same as with the return (`kont_tail`). -/
theorem tail_call_denote (P : Program S) (n r b : ℕ) (s : S) (rets : List (Ret S))
    (fs : List (Frame S)) :
    denote P ⟨some ⟨n + 1, .call r .done, s, b, rets⟩, fs⟩ =
      denote P ⟨none, .equations n (P r) s rets :: fs⟩ := by
  simp only [denote, decode_equations, den_call]
  congr 1
  funext t φ'
  rw [den]

/-! ## Every step keeps the denotation -/

theorem step_denote (P : Program S) (cfg : Config S) (ok : Ok cfg) :
    denote P cfg = (step P cfg).1.toList ++ denote P (step P cfg).2 ∧
      Ok (step P cfg).2 := by
  rcases cfg with ⟨_ | ⟨n, body, s, b, rets⟩, fs⟩
  · -- Backtracking into the newest frame.
    rcases fs with _ | ⟨_ | _, fs⟩
    · exact ⟨rfl, trivial⟩
    · rename_i n cs s rets
      rcases cs with _ | ⟨c, cs⟩
      · exact ⟨by simp [step, stepWith, denote, decode_equations, equations], ok.tail⟩
      · have hr : RetsOk fs.length rets := ok.1
        refine ⟨?_, Nat.le_succ _, hr, hr, ok.2⟩
        simp only [step, stepWith, denote, id, Option.toList_none, List.nil_append,
          decode_equations, kont_cons P (.equations n cs s rets) hr le_rfl]
        rw [trunc_cons _ le_rfl, trunc_length]
        simp [equations]
    · rename_i n ts k b' rets
      rcases ts with _ | ⟨t, ts⟩
      · exact ⟨by simp [step, stepWith, denote, decode_answers], ok.tail⟩
      · obtain ⟨hb, hr, hfs⟩ := ok
        refine ⟨?_, le_trans hb (Nat.le_succ _), hr, hb, hr, hfs⟩
        simp only [step, stepWith, denote, Option.toList_none, List.nil_append,
          decode_answers, kont_cons P (.answers n ts k b' rets) hr hb, trunc_cons _ hb,
          List.foldr_cons]
  · obtain ⟨hb, hr, hfs⟩ := ok
    cases body with
    | done =>
        rcases rets with _ | ⟨r, rets⟩
        · refine ⟨?_, hfs⟩
          simp only [step, stepWith, denote, Option.toList_some, List.singleton_append]
          rw [den]
          rfl
        · refine ⟨?_, le_trans hr.1 hb, hr.2, hfs⟩
          simp only [step, stepWith, denote, Option.toList_none, List.nil_append]
          rw [den]
          rfl
    | prim f k =>
        refine ⟨?_, hb, hr, hfs⟩
        simp only [step, stepWith, denote, Option.toList_none, List.nil_append,
          decode_answers]
        rw [den]
    | call r k =>
        rcases n with _ | n
        · refine ⟨?_, hfs⟩
          simp only [step, stepWith, denote, Option.toList_none, List.nil_append]
          rw [den]
        · refine ⟨?_, ⟨hb, hr⟩, hfs⟩
          simp only [step, stepWith, denote, Option.toList_none, List.nil_append,
            decode_equations, den_call]
          rfl
    | cut k =>
        refine ⟨?_, (length_trunc hb).ge, hr, FramesOk.drop _ hfs⟩
        simp only [step, stepWith, denote, Option.toList_none, List.nil_append,
          kont_trunc P hr hb, trunc_trunc le_rfl hb]
        rw [den]
    | branch t yes no =>
        refine ⟨?_, hb, hr, hfs⟩
        simp only [step, stepWith, denote, Option.toList_none, List.nil_append]
        rw [den]
        cases t s <;> rfl

/-- The answers of any `k` steps, then what the configuration they reach
denotes, are what the first configuration denotes. -/
theorem run_denote (P : Program S) :
    ∀ (k : ℕ) (cfg : Config S), Ok cfg →
      denote P cfg = (run P k cfg).1 ++ denote P (run P k cfg).2
  | 0, _, _ => rfl
  | k + 1, cfg, ok => by
      obtain ⟨now, next⟩ := step_denote P cfg ok
      have rest := run_denote P k _ next
      simp only [run, runWith] at rest ⊢
      rw [now, rest, List.append_assoc]
      rfl

/-- A query: its body from `s`, beneath nothing. -/
def start (n : ℕ) (body : Body S) (s : S) : Config S := ⟨some ⟨n, body, s, 0, []⟩, []⟩

theorem ok_start (n : ℕ) (body : Body S) (s : S) : Ok (start n body s) := by
  simp [Ok, start, RetsOk, FramesOk]

theorem denote_start (P : Program S) (n : ℕ) (body : Body S) (s : S) :
    denote P (start n body s) = den P n body s (fun t φ => t :: φ) [] [] := by
  simp only [denote, start, trunc, List.length_nil, List.drop_nil, decode]
  rfl

/-- Every answer a run emits is the query's, in order. -/
theorem run_prefix (P : Program S) (k n : ℕ) (body : Body S) (s : S) :
    (run P k (start n body s)).1 <+: den P n body s (fun t φ => t :: φ) [] [] := by
  rw [← denote_start, run_denote P k _ (ok_start n body s)]
  exact List.prefix_append _ _

/-- A run that ends has emitted exactly the query's answers. -/
theorem run_answers (P : Program S) (k n : ℕ) (body : Body S) (s : S)
    (ends : (run P k (start n body s)).2.act = none)
    (empty : (run P k (start n body s)).2.frames = []) :
    (run P k (start n body s)).1 = den P n body s (fun t φ => t :: φ) [] [] := by
  rw [← denote_start, run_denote P k _ (ok_start n body s)]
  rcases h : (run P k (start n body s)).2 with ⟨act, frames⟩
  rw [h] at ends empty
  simp only at ends empty
  subst ends empty
  simp [denote, decode]

/-! ## Controls -/

namespace Controls

/-- Keeping the old height after expanding an older frame drops one of its
retained occurrences. The rebased height keeps both. -/
theorem expansion_needs_rebased_barrier :
    trunc 1 ([2, 1].flatMap fun n : Nat => [n, n]) = [1] ∧
      trunc (expandedBarrier (fun n : Nat => [n, n]) 1 [2, 1])
        ([2, 1].flatMap fun n : Nat => [n, n]) = [1, 1] := by
  decide

/-- Removing the older marker has the opposite hazard: an unchanged height
keeps an alternative which the original cut discarded. -/
theorem contraction_needs_rebased_barrier :
    let blocks := fun n : Nat => if n = 1 then [] else [n]
    trunc 1 ([2, 1].flatMap blocks) = [2] ∧
      trunc (expandedBarrier blocks 1 [2, 1]) ([2, 1].flatMap blocks) = [] := by
  decide

/-- Relation 0 has an equation that cuts and one that does not; the query calls
it once. -/
def cutFirst : Program Unit := fun _ => [.cut .done, .done]

theorem cutFirst_answers :
    (run cutFirst 12 (start 1 (.call 0 .done) ())).1 = [()] ∧
      (run cutFirst 12 (start 1 (.call 0 .done) ())).2.act.isNone ∧
      (run cutFirst 12 (start 1 (.call 0 .done) ())).2.frames.isEmpty := by
  decide

/-- The call's answers are its first equation's alone. -/
theorem cutFirst_den : den cutFirst 1 (.call 0 .done) () (fun t φ => t :: φ) [] [] = [()] := by
  have h := cutFirst_answers
  rw [← run_answers cutFirst 12 1 (.call 0 .done) () (Option.isNone_iff_eq_none.mp h.2.1)
    (List.isEmpty_iff.mp h.2.2)]
  exact h.1

/-- A barrier one frame higher, above the call's own frame, keeps the untried
equation alive after the cut. -/
theorem barrier_above_own_frame :
    (runWith cutFirst (· + 1) 12 (start 1 (.call 0 .done) ())).1 = [(), ()] ∧
      (runWith cutFirst (· + 1) 12 (start 1 (.call 0 .done) ())).1 ≠
        den cutFirst 1 (.call 0 .done) () (fun t φ => t :: φ) [] [] := by
  rw [cutFirst_den]
  decide

/-- Relation 0 only cuts; the query calls it after a goal with two answers. -/
def cutOnly : Program Unit := fun _ => [.cut .done]

def twice : Body Unit := .prim (fun _ => [(), ()]) (.call 0 .done)

theorem cutOnly_answers :
    (run cutOnly 20 (start 1 twice ())).1 = [(), ()] ∧
      (run cutOnly 20 (start 1 twice ())).2.act.isNone ∧
      (run cutOnly 20 (start 1 twice ())).2.frames.isEmpty := by
  decide

/-- A cut inside the call leaves the caller's alternatives. -/
theorem cutOnly_den : den cutOnly 1 twice () (fun t φ => t :: φ) [] [] = [(), ()] := by
  have h := cutOnly_answers
  rw [← run_answers cutOnly 20 1 twice () (Option.isNone_iff_eq_none.mp h.2.1)
    (List.isEmpty_iff.mp h.2.2)]
  exact h.1

/-- A barrier at the bottom of the stack drops the caller's second answer. -/
theorem barrier_at_bottom :
    (runWith cutOnly (fun _ => 0) 12 (start 1 twice ())).1 = [()] ∧
      (runWith cutOnly (fun _ => 0) 12 (start 1 twice ())).1 ≠
        den cutOnly 1 twice () (fun t φ => t :: φ) [] [] := by
  rw [cutOnly_den]
  decide

end Controls

end Mettapedia.Machines.EquationCut
