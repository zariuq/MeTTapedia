import Mettapedia.GSLT.LanguageDef.DefunctionalizedEquationBodies

/-!
# Executable controls for defunctionalized equation bodies

`DefunctionalizedEquationBodies` compiles first-order equation bodies to the
generic shared-continuation machine, parametrically in a template language and a
store algebra.  This file fixes one concrete instance and runs `compiled` on
small programs.  Every run below is a kernel evaluation (`decide +kernel` or
`rfl`) of the Lean definitions of `compiled`, `step`, `checkedStep` and the
instance: these are kernel-checked executions of the generic compiled machine,
not runs of native code.  `native_decide` is not used.

## The instance

* `Tm`: logical variables, atoms, integers and pairs.  `Tp k`: the same shapes
  over `k` activation slots, with no variables of their own.  An uncaptured slot
  reads as `default = atom "?"`, which is not a variable.
* `St`: variable bindings, newest first, and the next fresh variable; `fresh`
  allocates consecutive variables.
* `unify`: syntactic unification with occurs check, dereferencing through the
  bindings.  Its recursion is bounded by explicit fuel.  Dereferencing
  (`St.walk`, `St.resolve`) follows at most as many bindings as the store holds,
  which suffices when the bindings are acyclic; binding only unbound variables,
  after an occurs check, is meant to keep them so, but that is not proved here.
  Unification descends at most `unifyDepth = 1000` pair levels and fails beyond
  that; the terms below are far shallower.
* `prim`: `+` and `-` on integers; `test`: `<` on integers.  Arguments are read
  through the store; anything else fails.

## Controls

* Ordered non-tail choice (`pickProgram`): `two` binds two successive `pick`s.
  The machine delivers `(a, a), (a, b), (b, a), (b, b)` in that order, a prefix
  of them at every step, and exhausts its frontier after 13 steps.  The resume
  table is exactly the two call sites, and the shared arena stores one frame per
  executed call.  By `compiled_completed`, every denotation of the source
  machine gives the query exactly these answers (no denotation is constructed
  here).
* A captured branch-store reference (`probeProgram`): `probe` passes an unbound
  slot to `choose`, whose two equations bind it by head unification.  Both
  alternatives resume one return frame, a single arena node, which captured the
  variable itself; they deliver the same term, which reads as `(a, ok)` and
  `(b, ok)` in their two branch stores.
* Captures are necessary: at every step of the runs of `two` and `last`, every
  return frame captures exactly its site's support, and a slot that is dead after
  a call is not captured.  Dropping one captured slot from a frame that two alternatives
  share makes the same machine deliver `(?, a)` and `(?, b)`, which the
  undamaged machine never delivers.
* A deterministic region (`arithProgram`): primitives, pattern bindings and a
  test run within one control boundary.  The program has no resume site, so no
  return frame is ever built, for any query.
* Sized proof search (`obcProgram`): the size-bounded backward chainer
  `obc`/`obc-gtz` over three Hilbert axioms and modus ponens.  With budget 5 it
  proves `p -> p` exactly by `mp (mp ax2 ax1) ax1`; with budget 3 it proves
  `p -> ?Y` by `ax1`, `mp ax1 ax1`, `mp ax1 ax2`, `mp ax1 ax3`, in authored order.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Examples.DefunctionalizedEquationBodies

open Mettapedia.GSLT.LanguageDef.DefunctionalizedEquationBodies
open Mettapedia.GSLT.LanguageDef.CompiledContinuationAnswerProducer (Denotation)
open Mettapedia.Machines.SharedContinuation
open Mettapedia.GSLT.Dynamics.ContextIndexedSwitching (repeats repeats_add)

/-! ## Terms and templates -/

/-- Terms: logical variables, atoms, integers and pairs. -/
inductive Tm where
  | var (n : Nat)
  | atom (s : String)
  | num (z : Int)
  | pair (a b : Tm)
  deriving DecidableEq, Repr

/-- An uncaptured slot reads as this atom.  It is deliberately not a variable:
the derived default would be `var 0`, the first fresh variable, and a dropped
capture could then read as a live variable of the branch store. -/
instance : Inhabited Tm := ⟨.atom "?"⟩

namespace Tm

/-- Replace every variable. -/
def subst (f : Nat → Tm) : Tm → Tm
  | var n => f n
  | pair a b => .pair (a.subst f) (b.subst f)
  | t => t

/-- Whether the variable `n` occurs. -/
def mentions (n : Nat) : Tm → Bool
  | var m => m == n
  | pair a b => a.mentions n || b.mentions n
  | _ => false

end Tm

/-- Templates over `k` activation slots: the shapes of `Tm`, with slots in place
of logical variables. -/
inductive Tp (k : Nat) where
  | slot (i : Fin k)
  | atom (s : String)
  | num (z : Int)
  | pair (a b : Tp k)
  deriving DecidableEq, Repr

namespace Tp

def inst {k : Nat} : Tp k → (Fin k → Tm) → Tm
  | slot i, frame => frame i
  | atom s, _ => .atom s
  | num z, _ => .num z
  | pair a b, frame => .pair (a.inst frame) (b.inst frame)

/-- The slots a template reads. -/
def support {k : Nat} : Tp k → Finset (Fin k)
  | slot i => {i}
  | atom _ => ∅
  | num _ => ∅
  | pair a b => a.support ∪ b.support

theorem inst_congr {k : Nat} (t : Tp k) (frame frame' : Fin k → Tm)
    (agree : ∀ i ∈ t.support, frame i = frame' i) : t.inst frame = t.inst frame' := by
  induction t with
  | slot i => exact agree i (Finset.mem_singleton_self i)
  | atom => rfl
  | num => rfl
  | pair a b iha ihb =>
      rw [inst, inst, iha fun i hi => agree i (Finset.mem_union_left _ hi),
        ihb fun i hi => agree i (Finset.mem_union_right _ hi)]

end Tp

abbrev templates : TemplateLanguage Tm where
  Tmpl := Tp
  inst := Tp.inst
  support := Tp.support
  inst_congr := Tp.inst_congr

/-! ## The branch store -/

/-- A branch store: variable bindings, newest first, and the next fresh
variable. -/
structure St where
  bindings : List (Nat × Tm)
  next : Nat
  deriving DecidableEq, Repr

namespace St

def empty : St := ⟨[], 0⟩

def bind (σ : St) (n : Nat) (t : Tm) : St := { σ with bindings := (n, t) :: σ.bindings }

/-- Dereference the head of a term, following at most `fuel` bindings. -/
def walkN (σ : St) : Nat → Tm → Tm
  | fuel + 1, .var n =>
      match List.lookup n σ.bindings with
      | some t => σ.walkN fuel t
      | none => .var n
  | _, t => t

/-- Dereference the head of a term, following at most as many bindings as the
store holds. -/
def walk (σ : St) (t : Tm) : Tm := σ.walkN σ.bindings.length t

/-- Substitute bindings throughout a term, along chains of at most `fuel`
bindings. -/
def resolveN (σ : St) : Nat → Tm → Tm
  | 0, t => t
  | fuel + 1, t => t.subst fun n =>
      match List.lookup n σ.bindings with
      | some u => σ.resolveN fuel u
      | none => .var n

/-- Read a term through the store, along chains of at most as many bindings as
the store holds. -/
def resolve (σ : St) (t : Tm) : Tm := σ.resolveN (σ.bindings.length + 1) t

end St

/-- Syntactic unification with occurs check, descending at most `fuel` pair
levels; it fails beyond that. -/
def unifyN : Nat → Tm → Tm → St → Option St
  | 0, _, _, _ => none
  | fuel + 1, s, t, σ =>
      match σ.walk s, σ.walk t with
      | .var m, .var n => if m = n then some σ else some (σ.bind m (.var n))
      | .var m, u => if (σ.resolve u).mentions m then none else some (σ.bind m u)
      | u, .var n => if (σ.resolve u).mentions n then none else some (σ.bind n u)
      | .atom a, .atom b => if a = b then some σ else none
      | .num a, .num b => if a = b then some σ else none
      | .pair a b, .pair c d => (unifyN fuel a c σ).bind (unifyN fuel b d)
      | _, _ => none

/-- The depth bound of `unify`. -/
def unifyDepth : Nat := 1000

inductive Op where
  | add | sub | lt
  deriving DecidableEq, Repr

/-- `+` and `-` on integers, read through the store; anything else fails. -/
def prim : Op → List Tm → St → Option Tm
  | .add, [a, b], σ =>
      match σ.resolve a, σ.resolve b with
      | .num x, .num y => some (.num (x + y))
      | _, _ => none
  | .sub, [a, b], σ =>
      match σ.resolve a, σ.resolve b with
      | .num x, .num y => some (.num (x - y))
      | _, _ => none
  | _, _, _ => none

/-- `<` on integers, read through the store; anything else fails. -/
def test : Op → List Tm → St → Option Bool
  | .lt, [a, b], σ =>
      match σ.resolve a, σ.resolve b with
      | .num x, .num y => some (decide (x < y))
      | _, _ => none
  | _, _, _ => none

def store : StoreAlgebra Tm St Op where
  unify s t σ := unifyN unifyDepth s t σ
  fresh σ k := (fun i => .var (σ.next + i.val), { σ with next := σ.next + k })
  prim := prim
  test := test

/-! ## Running the compiled machine -/

inductive Rel where
  | pick | two | last | choose | probe | arith | obc | obcGtz
  deriving DecidableEq, Repr

abbrev MachineState :=
  State Unit (Control templates Rel Op St) (ReturnFrame templates Rel Op) (Answer Tm St)

/-- The compiled machine of `P`, `count` steps into the query `q`. -/
def run (P : EqProgram templates Rel Op) (q : Call Tm St Rel) (count : Nat) : MachineState :=
  repeats (step (compiled templates store P)) count (initial templates store P q)

/-- The same run in the shared-arena realization: every return frame is stored
once, and the frontier holds roots. -/
def arenaRun (P : EqProgram templates Rel Op) (q : Call Tm St Rel) (count : Nat) :
    ArenaState Unit (Control templates Rel Op St) (ReturnFrame templates Rel Op) (Answer Tm St) :=
  (repeats (checkedStep (compiled templates store P)) count (encode (initial templates store P q))).1

/-- The delivered answers, each read through its own branch store. -/
def answers (s : MachineState) : List Tm := s.emitted.map fun e => e.2.2.resolve e.2.1

/-- A control's slot `i` (`none` beyond its slots). -/
def slotAt (c : Control templates Rel Op St) (i : Nat) : Option Tm :=
  if h : i < c.slots then some (c.frame ⟨i, h⟩) else none

/-- A return frame's capture of slot `i` (`none` beyond its slots). -/
def capturedAt (f : ReturnFrame templates Rel Op) (i : Nat) : Option Tm :=
  if h : i < f.slots then f.captured ⟨i, h⟩ else none

/-- Every pending return frame captures exactly the support of its site. -/
def CapturesSupport (s : MachineState) : Prop :=
  ∀ t ∈ s.frontier, ∀ f ∈ t.returns,
    ∀ i : Fin f.slots, (f.captured i).isSome ↔ i ∈ frameSupport templates f.pattern f.body

instance (s : MachineState) : Decidable (CapturesSupport s) :=
  inferInstanceAs (Decidable (∀ t ∈ s.frontier, ∀ f ∈ t.returns,
    ∀ i : Fin f.slots, (f.captured i).isSome ↔ i ∈ frameSupport templates f.pattern f.body))

/-- An exhausted run stays where it is. -/
theorem run_stable (P : EqProgram templates Rel Op) (q : Call Tm St Rel) {n : Nat}
    (exhausted : (run P q n).frontier = []) (k : Nat) : run P q (n + k) = run P q n := by
  unfold run at *
  rw [repeats_add]
  generalize repeats (step (compiled templates store P)) n (initial templates store P q) = s
    at exhausted ⊢
  have fixed : step (compiled templates store P) s = s := by simp [step, exhausted]
  induction k with
  | zero => rfl
  | succ k ih => rw [repeats, fixed, ih]

/-! ## Ordered non-tail choice -/

/-- `pick` answers `a`, then `b`; `two = let x := pick in let y := pick in (x, y)`. -/
def pickProgram : EqProgram templates Rel Op :=
  [(.pick, ⟨0, [], .ret (.atom "a")⟩),
   (.pick, ⟨0, [], .ret (.atom "b")⟩),
   (.two, ⟨2, [], .letCall (.slot 0) .pick [] (.letCall (.slot 1) .pick []
      (.ret (.pair (.slot 0) (.slot 1))))⟩)]

def twoQuery : Call Tm St Rel := (.two, [], .empty)

def twoAnswers : List Tm :=
  [.pair (.atom "a") (.atom "a"), .pair (.atom "a") (.atom "b"),
   .pair (.atom "b") (.atom "a"), .pair (.atom "b") (.atom "b")]

theorem two_answers : answers (run pickProgram twoQuery 13) = twoAnswers := by
  decide +kernel

theorem two_exhausted : (run pickProgram twoQuery 13).frontier = [] :=
  List.eq_nil_of_length_eq_zero (by decide +kernel)

/-- Answers stream: after seven steps both continuations of the first pick's `a`
have delivered, and only its alternative `b` is pending. -/
theorem two_streams :
    answers (run pickProgram twoQuery 7) = twoAnswers.take 2 ∧
      (run pickProgram twoQuery 7).frontier.length = 1 := by
  decide +kernel

/-- At every step the delivered answers are a prefix of the final ones. -/
theorem two_prefix (n : Nat) : answers (run pickProgram twoQuery n) <+: twoAnswers := by
  rcases Nat.lt_or_ge n 13 with early | late
  · exact (show ∀ n < 13, answers (run pickProgram twoQuery n) <+: twoAnswers by
      decide +kernel) n early
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le late
    rw [run_stable pickProgram twoQuery two_exhausted, two_answers]

/-- The resume table is exactly the two call sites of `two`. -/
theorem two_resume_table :
    resumeTable pickProgram =
      [⟨2, .slot 0, .letCall (.slot 1) .pick [] (.ret (.pair (.slot 0) (.slot 1)))⟩,
       ⟨2, .slot 1, .ret (.pair (.slot 0) (.slot 1))⟩] := rfl

theorem two_resume_table_length : (resumeTable pickProgram).length = 2 := rfl

/-- The shared arena delivers the same answers and allocates one node per
executed call: after three steps the inner pick's two alternatives both hold
root `2` and the outer alternative root `1`; three calls, three nodes. -/
theorem two_arena :
    answers (arenaRun pickProgram twoQuery 13).decode = twoAnswers ∧
      (arenaRun pickProgram twoQuery 13).frontier.length = 0 ∧
      (arenaRun pickProgram twoQuery 3).frontier.map (·.root) = [2, 2, 1] ∧
      (arenaRun pickProgram twoQuery 13).arena.length = 3 := by
  decide +kernel

/-- Every denotation of the source machine gives `two` exactly these answers,
read through their branch stores (`compiled_completed` at the exhausted
frontier).  This file does not construct a denotation. -/
theorem two_denotation (denotation : Denotation (sourceMachine templates store pickProgram)) :
    (denotation.value twoQuery).map (fun a => a.2.resolve a.1) = twoAnswers := by
  rw [← compiled_completed templates store pickProgram denotation twoQuery 13 two_exhausted,
    List.map_map]
  exact two_answers

/-! ## A captured branch-store reference -/

/-- `choose a` and `choose b` answer `ok`; `probe` passes its slot `z` to
`choose` unbound: `probe = let r := choose z in (z, r)`. -/
def probeProgram : EqProgram templates Rel Op :=
  [(.choose, ⟨0, [.atom "a"], .ret (.atom "ok")⟩),
   (.choose, ⟨0, [.atom "b"], .ret (.atom "ok")⟩),
   (.probe, ⟨2, [], .letCall (.slot 1) .choose [.slot 0] (.ret (.pair (.slot 0) (.slot 1)))⟩)]

def probeQuery : Call Tm St Rel := (.probe, [], .empty)

/-- When `probe` calls `choose`, its slot `z` holds `var 0`, unbound in the store
of the call. -/
theorem probe_unbound_at_call :
    (run probeProgram probeQuery 0).frontier.map
        (fun t => (slotAt t.control 0, t.control.store.resolve (.var 0))) =
      [(some (.var 0), .var 0)] := by
  decide +kernel

/-- Both alternatives of `choose` resume one and the same return frame. -/
theorem probe_one_frame :
    ∃ f, (run probeProgram probeQuery 1).frontier.map (·.returns) = [[f], [f]] :=
  ⟨_, rfl⟩

/-- That frame captured `z` as the variable itself; the branch stores of the two
alternatives bind it by head unification, to `a` and to `b`. -/
theorem probe_branch_stores :
    (run probeProgram probeQuery 1).frontier.map
        (fun t => (t.returns.map (capturedAt · 0), t.control.store.resolve (.var 0))) =
      [([some (.var 0)], .atom "a"), ([some (.var 0)], .atom "b")] := by
  decide +kernel

/-- Both alternatives deliver the same term `(var 0, var 1)`; read through their
branch stores it is `(a, ok)` and `(b, ok)`. -/
theorem probe_answers :
    (run probeProgram probeQuery 5).emitted.map (fun e => (e.2.1, e.2.2.resolve e.2.1)) =
      [(.pair (.var 0) (.var 1), .pair (.atom "a") (.atom "ok")),
       (.pair (.var 0) (.var 1), .pair (.atom "b") (.atom "ok"))] := by
  decide +kernel

theorem probe_exhausted : (run probeProgram probeQuery 5).frontier = [] :=
  List.eq_nil_of_length_eq_zero (by decide +kernel)

/-- In the shared arena the frame is a single node, the root of both
alternatives. -/
theorem probe_arena_shared :
    (arenaRun probeProgram probeQuery 1).frontier.map (·.root) = [1, 1] ∧
      (arenaRun probeProgram probeQuery 1).arena.length = 1 := by
  decide +kernel

/-! ## Captures are necessary -/

/-- `last = let x := pick in let y := pick in y`: `x` is dead after the second
call. -/
def lastProgram : EqProgram templates Rel Op :=
  [(.pick, ⟨0, [], .ret (.atom "a")⟩),
   (.pick, ⟨0, [], .ret (.atom "b")⟩),
   (.last, ⟨2, [], .letCall (.slot 0) .pick [] (.letCall (.slot 1) .pick [] (.ret (.slot 1)))⟩)]

def lastQuery : Call Tm St Rel := (.last, [], .empty)

theorem last_answers :
    answers (run lastProgram lastQuery 13) = [.atom "a", .atom "b", .atom "a", .atom "b"] ∧
      (run lastProgram lastQuery 13).frontier.length = 0 := by
  decide +kernel

/-- After `last`'s second call, the frame of that site keeps only `y`; the frame
of the first site keeps both slots. -/
theorem last_frames :
    (run lastProgram lastQuery 3).frontier.map
        (fun t => t.returns.map fun f => (capturedAt f 0, capturedAt f 1)) =
      [[(none, some (.var 1))], [(none, some (.var 1))], [(some (.var 0), some (.var 1))]] := by
  decide +kernel

/-- At every step of `two` and of `last`, every return frame captures exactly its
site's support. -/
theorem captures_support :
    (∀ n ≤ 13, CapturesSupport (run pickProgram twoQuery n)) ∧
      ∀ n ≤ 13, CapturesSupport (run lastProgram lastQuery n) := by
  decide +kernel

/-- `two` after three steps: the inner pick's two alternatives share the frame of
the second call site; the outer alternative `b` holds the frame of the first. -/
theorem two_after_second_call :
    ∃ f g : ReturnFrame templates Rel Op,
      (run pickProgram twoQuery 3).frontier.map (·.returns) = [[f], [f], [g]] ∧
      f.site = ⟨2, .slot 1, .ret (.pair (.slot 0) (.slot 1))⟩ ∧
      g.site = ⟨2, .slot 0, .letCall (.slot 1) .pick [] (.ret (.pair (.slot 0) (.slot 1)))⟩ :=
  ⟨_, _, rfl, rfl, rfl⟩

/-- Drop a return frame's capture of slot `i`. -/
def forgetSlot (f : ReturnFrame templates Rel Op) (i : Nat) : ReturnFrame templates Rel Op :=
  { f with captured := fun j => if j.val = i then none else f.captured j }

/-- The state of `two_after_second_call` with slot `x`, which the continuation
reads, dropped from the shared frame of the second call site. -/
def damaged : MachineState :=
  let s := run pickProgram twoQuery 3
  ⟨(s.frontier.take 2).map (fun t => { t with returns := t.returns.map (forgetSlot · 0) }) ++
    s.frontier.drop 2, s.emitted⟩

theorem damaged_breaks_support : ¬ CapturesSupport damaged := by
  decide +kernel

/-- Undamaged, the machine continues from that state to `two`'s answers. -/
theorem undamaged_continues :
    repeats (step (compiled templates store pickProgram)) 10 (run pickProgram twoQuery 3) =
      run pickProgram twoQuery 13 :=
  (repeats_add _ 3 10 _).symm

/-- Damaged, the same machine resumes the same answers into `(?, a)` and `(?, b)`:
answers of neither the undamaged run nor, by `two_denotation`, any denotation of
the source. -/
theorem damaged_invents :
    answers (repeats (step (compiled templates store pickProgram)) 10 damaged) =
        [.pair default (.atom "a"), .pair default (.atom "b"),
         .pair (.atom "b") (.atom "a"), .pair (.atom "b") (.atom "b")] ∧
      (repeats (step (compiled templates store pickProgram)) 10 damaged).frontier.length = 0 ∧
      .pair default (.atom "a") ∉ twoAnswers ∧ .pair default (.atom "b") ∉ twoAnswers := by
  decide +kernel

/-! ## A deterministic region -/

/-- `arith x = let y := x + 4 in if y < 10 then (let r := (small, y) in r)
else (big, y - 10)`: a primitive, a test and pattern bindings, and no call. -/
def arithProgram : EqProgram templates Rel Op :=
  [(.arith, ⟨3, [.slot 0],
    .letPrim (.slot 1) .add [.slot 0, .num 4]
      (.ite .lt [.slot 1, .num 10]
        (.bind (.slot 2) (.pair (.atom "small") (.slot 1)) (.ret (.slot 2)))
        (.letPrim (.slot 2) .sub [.slot 1, .num 10] (.ret (.pair (.atom "big") (.slot 2)))))⟩)]

def arithQuery (x : Tm) : Call Tm St Rel := (.arith, [x], .empty)

/-- Each query completes in one step, the whole body within one control
boundary; a primitive on a non-number fails. -/
theorem arith_answers :
    [.num 3, .num 8, .num (-9), .atom "a"].map
        (fun x => (answers (run arithProgram (arithQuery x) 1),
          (run arithProgram (arithQuery x) 1).frontier.length)) =
      [([.pair (.atom "small") (.num 7)], 0), ([.pair (.atom "big") (.num 2)], 0),
       ([.pair (.atom "small") (.num (-5))], 0), ([], 0)] := by
  decide +kernel

theorem arith_no_sites : resumeTable arithProgram = [] := rfl

/-- For every query and every step count, no task of `arith` holds a return
frame: each would be a site of the resume table (`reachable_frames_in_table`),
which is empty. -/
theorem arith_no_frames (q : Call Tm St Rel) (n : Nat) :
    ∀ t ∈ (run arithProgram q n).frontier, t.returns = [] := by
  intro t member
  refine List.eq_nil_iff_forall_not_mem.mpr fun f framed => ?_
  simpa [arith_no_sites] using
    (reachable_frames_in_table templates store arithProgram q n t member).2 f framed

/-! ## Sized proof search -/

namespace Tp

def imp {k : Nat} (a b : Tp k) : Tp k := .pair (.atom "->") (.pair a b)
def neg {k : Nat} (a : Tp k) : Tp k := .pair (.atom "not") a
def mp {k : Nat} (f x : Tp k) : Tp k := .pair (.atom "mp") (.pair f x)
def typed {k : Nat} (x a : Tp k) : Tp k := .pair (.atom ":") (.pair x a)
def sized {k : Nat} (n t : Tp k) : Tp k := .pair (.atom "MkSized") (.pair n t)

end Tp

namespace Tm

def imp (a b : Tm) : Tm := .pair (.atom "->") (.pair a b)
def mp (f x : Tm) : Tm := .pair (.atom "mp") (.pair f x)
def typed (x a : Tm) : Tm := .pair (.atom ":") (.pair x a)
def sized (n t : Tm) : Tm := .pair (.atom "MkSized") (.pair n t)

end Tm

/-- The size-bounded backward chainer, equation for equation:

* `obcGtz s (x : A)` for the axioms `ax1 : P -> Q -> P`,
  `ax2 : (P -> Q -> R) -> (P -> Q) -> P -> R` and
  `ax3 : (not P -> not Q) -> Q -> P` answers `MkSized 1 (x : A)`;
* `obcGtz s (mp f x : B)`, if `2 < s`, binds `MkSized fs (f : A -> B)` from
  `obc (s - 2)`, then `MkSized xs (x : A)` from `obc (s - 1 - fs)`, and answers
  `MkSized (fs + xs + 1) (mp f x : B)`; its slots are `s f x B A fs xs` and five
  single-assignment temporaries for the size arithmetic;
* `obc s (x : A)` is `obcGtz s (x : A)` if `0 < s`, and fails otherwise. -/
def obcProgram : EqProgram templates Rel Op :=
  [(.obcGtz, ⟨3, [.slot 0, .typed (.atom "ax1") (.imp (.slot 1) (.imp (.slot 2) (.slot 1)))],
      .ret (.sized (.num 1) (.typed (.atom "ax1") (.imp (.slot 1) (.imp (.slot 2) (.slot 1)))))⟩),
   (.obcGtz, ⟨4, [.slot 0, .typed (.atom "ax2")
        (.imp (.imp (.slot 1) (.imp (.slot 2) (.slot 3)))
          (.imp (.imp (.slot 1) (.slot 2)) (.imp (.slot 1) (.slot 3))))],
      .ret (.sized (.num 1) (.typed (.atom "ax2")
        (.imp (.imp (.slot 1) (.imp (.slot 2) (.slot 3)))
          (.imp (.imp (.slot 1) (.slot 2)) (.imp (.slot 1) (.slot 3))))))⟩),
   (.obcGtz, ⟨3, [.slot 0, .typed (.atom "ax3")
        (.imp (.imp (.neg (.slot 1)) (.neg (.slot 2))) (.imp (.slot 2) (.slot 1)))],
      .ret (.sized (.num 1) (.typed (.atom "ax3")
        (.imp (.imp (.neg (.slot 1)) (.neg (.slot 2))) (.imp (.slot 2) (.slot 1)))))⟩),
   (.obcGtz, ⟨12, [.slot 0, .typed (.mp (.slot 1) (.slot 2)) (.slot 3)],
      .ite .lt [.num 2, .slot 0]
        (.letPrim (.slot 7) .sub [.slot 0, .num 2]
          (.letCall (.sized (.slot 5) (.typed (.slot 1) (.imp (.slot 4) (.slot 3)))) .obc
              [.slot 7, .typed (.slot 1) (.imp (.slot 4) (.slot 3))]
            (.letPrim (.slot 8) .sub [.slot 0, .num 1]
              (.letPrim (.slot 9) .sub [.slot 8, .slot 5]
                (.letCall (.sized (.slot 6) (.typed (.slot 2) (.slot 4))) .obc
                    [.slot 9, .typed (.slot 2) (.slot 4)]
                  (.letPrim (.slot 10) .add [.slot 5, .slot 6]
                    (.letPrim (.slot 11) .add [.slot 10, .num 1]
                      (.ret (.sized (.slot 11) (.typed (.mp (.slot 1) (.slot 2)) (.slot 3)))))))))))
        .fail⟩),
   (.obc, ⟨3, [.slot 0, .typed (.slot 1) (.slot 2)],
      .ite .lt [.num 0, .slot 0] (.tail .obcGtz [.slot 0, .typed (.slot 1) (.slot 2)]) .fail⟩)]

/-- `obc size (var 0 : goal)`; the goal may use `var 1`. -/
def obcQuery (size : Int) (goal : Tm) : Call Tm St Rel :=
  (.obc, [.num size, .typed (.var 0) goal], ⟨[], 2⟩)

/-- The size and proof term of each delivered `MkSized n (x : A)`. -/
def proofs (s : MachineState) : List (Tm × Tm) :=
  (answers s).filterMap fun
    | .pair (.atom "MkSized") (.pair size (.pair (.atom ":") (.pair proof _))) => some (size, proof)
    | _ => none

/-- With budget 5, `p -> p` has exactly one proof. -/
theorem obc_identity :
    answers (run obcProgram (obcQuery 5 (.imp (.atom "p") (.atom "p"))) 45) =
        [.sized (.num 5) (.typed (.mp (.mp (.atom "ax2") (.atom "ax1")) (.atom "ax1"))
          (.imp (.atom "p") (.atom "p")))] ∧
      (run obcProgram (obcQuery 5 (.imp (.atom "p") (.atom "p"))) 45).frontier.length = 0 := by
  decide +kernel

/-- With budget 3, the proofs of `p -> ?Y` arrive in authored order: the axiom
before modus ponens, and within modus ponens the axioms for the minor premise in
order. -/
theorem obc_authored_order :
    proofs (run obcProgram (obcQuery 3 (.imp (.atom "p") (.var 1))) 19) =
        [(.num 1, .atom "ax1"), (.num 3, .mp (.atom "ax1") (.atom "ax1")),
         (.num 3, .mp (.atom "ax1") (.atom "ax2")), (.num 3, .mp (.atom "ax1") (.atom "ax3"))] ∧
      (run obcProgram (obcQuery 3 (.imp (.atom "p") (.var 1))) 19).frontier.length = 0 := by
  decide +kernel

/-- Two resume sites, the two premises of modus ponens. -/
theorem obc_resume_table_length : (resumeTable obcProgram).length = 2 := rfl

end Mettapedia.GSLT.Examples.DefunctionalizedEquationBodies
