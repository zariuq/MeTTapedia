/-
# Gauthier E1 scalar-triple language family: one evaluator, many tables

This file factors the `exec.sml` scalar substrate into one table-parameterized evaluator.  A
`Signature` is a first-class operator table: each entry records an operator name, first-order arity,
higher-order arity, and primitive semantics tag.  Programs store table indices, mirroring QSynt's
`Ins (id,args)` and `execv` swap architecture.

Grounding:
  * `repos/oeis-synthesis/src/kernel.sml` lines 293-315: `org_operl`, `pow_operl`, `minimal_operl`,
    `array_operl`, and `turing_operl`.
  * `repos/oeis-synthesis/src/kernel.sml` lines 484-514: higher-order arities.
  * `repos/oeis-synthesis/src/exec.sml` lines 126-146: constants/registers/arithmetic.
  * `repos/oeis-synthesis/src/exec.sml` lines 160-172 and 192-201: array and turing primitives.
  * `repos/oeis-synthesis/src/exec.sml` lines 207-220 and 271-277: scalar loops/comprehension.
  * `repos/oeis-synthesis/src/exec.sml` lines 290-304: `array_execv`, `minimal_execv`,
    `turing_execv`, and the table switch.

Important source wart, kept explicit: `kernel.sml` lines 309-311 list `array_operl` with `loop` at
index 9, but `exec.sml` lines 290-292 place `loop_f` last in `array_execv`.  The `arraySignature`
below follows the evaluator order, because executable semantics are the ground truth for `Ins` ids.
-/

namespace Mettapedia.GSLT.LanguageDef.GauthierE1

universe u

/-- Primitive semantics available on the scalar-triple `exec.sml` substrate. -/
inductive Prim where
  | zero | one | two
  | suc | pred
  | addi | diff | mult | divi | modu
  | cond | loop | loop2 | compr | loope
  | x | y | z
  | array | assign
  | next | prev | write | read
  deriving DecidableEq, Repr

/-- One operator table entry.  `hoArity` counts leading higher-order children.
    The semantics tag is parametric so all Gauthier substrates share one parser. -/
structure Entry (σ : Type u) where
  name : String
  arity : Nat
  hoArity : Nat
  prim : σ
  deriving Repr

abbrev Signature (σ : Type u) := List (Entry σ)

def entry {σ : Type u} (name : String) (arity hoArity : Nat) (prim : σ) : Entry σ :=
  { name := name, arity := arity, hoArity := hoArity, prim := prim }

/-- Local list lookup, keeping this file import-free across core-library churn. -/
def listGet? {α : Type u} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

/-- Table lookup: program operator ids are indices into the active `Signature`. -/
def entryAt {σ : Type u} (sig : Signature σ) (id : Nat) : Option (Entry σ) := listGet? sig id

/-- The term grammar `T`: QSynt-style `Ins (id,args)` trees over table indices. -/
inductive Prog where
  | node : Nat → List Prog → Prog
  deriving Repr

/-- Structural well-formedness: every operator id exists and has the table-prescribed arity. -/
inductive WellFormed {σ : Type u} (sig : Signature σ) : Prog → Prop where
  | node {id : Nat} {ch : List Prog} {e : Entry σ} :
      entryAt sig id = some e →
      ch.length = e.arity →
      (∀ c ∈ ch, WellFormed sig c) →
      WellFormed sig (.node id ch)

/-- RPN source tokens are table indices, matching `Ins` ids. -/
abbrev Tok := Nat

/-- Pop `n` stack items, preserving top-first order in the returned prefix. -/
def popN {α : Type u} : Nat → List α → Option (List α × List α)
  | 0, st => some ([], st)
  | _ + 1, [] => none
  | n + 1, x :: st =>
      match popN n st with
      | none => none
      | some (xs, rest) => some (x :: xs, rest)

theorem popN_length {α : Type u} {n : Nat} {st args rest : List α}
    (h : popN n st = some (args, rest)) : args.length = n := by
  induction n generalizing st args rest with
  | zero =>
      simp [popN] at h
      rw [h.1]
      rfl
  | succ n ih =>
      cases st with
      | nil =>
          simp [popN] at h
      | cons x xs =>
          simp [popN] at h
          cases hpop : popN n xs with
          | none =>
              simp [hpop] at h
          | some r =>
              cases r with
              | mk xs' rest' =>
                  simp [hpop] at h
                  have hlen := ih hpop
                  rw [← h.1]
                  simp [hlen]

abbrev WProg {σ : Type u} (sig : Signature σ) := {p : Prog // WellFormed sig p}

/-- One certified RPN parser step.  Arguments are popped from the stack and reversed into child order. -/
def recognizeStep {σ : Type u} (sig : Signature σ) (id : Tok)
    (stack : List (WProg sig)) : Option (List (WProg sig)) :=
  match hentry : entryAt sig id with
  | none => none
  | some e =>
      match hpop : popN e.arity stack with
      | none => none
      | some (args, rest) =>
          let children := (args.map (fun p => p.val)).reverse
          have hpopLen : args.length = e.arity := popN_length hpop
          have hlen : children.length = e.arity := by
            simp [children, hpopLen]
          have hall : ∀ c ∈ children, WellFormed sig c := by
            intro c hc
            have hc' : c ∈ args.map (fun p => p.val) := by
              simpa [children] using List.mem_reverse.mp hc
            rcases List.mem_map.mp hc' with ⟨wp, hwp, hval⟩
            cases hval
            exact wp.property
          let p : Prog := .node id children
          have hwf : WellFormed sig p :=
            WellFormed.node (sig := sig) (id := id) (ch := children) (e := e) hentry hlen hall
          some (⟨p, hwf⟩ :: rest)

/-- Table-driven RPN stack fold, certified by carrying well-formed programs on the stack. -/
def recognizeStack {σ : Type u} (sig : Signature σ) :
    List Tok → List (WProg sig) → Option (List (WProg sig))
  | [], st => some st
  | id :: toks, st =>
      match recognizeStep sig id st with
      | none => none
      | some st' => recognizeStack sig toks st'

/-- Certified recognizer: success means exactly one well-formed program remains on the stack. -/
def recognizeCertified {σ : Type u} (sig : Signature σ) (toks : List Tok) : Option (WProg sig) :=
  match recognizeStack sig toks [] with
  | some [p] => some p
  | _ => none

/-- Raw RPN parser step.  It has the same stack behavior as `recognizeStep`, without proof payloads. -/
def recognizeRawStep {σ : Type u} (sig : Signature σ) (id : Tok)
    (stack : List Prog) : Option (List Prog) :=
  match entryAt sig id with
  | none => none
  | some e =>
      match popN e.arity stack with
      | none => none
      | some (args, rest) => some (.node id args.reverse :: rest)

/-- Table-driven RPN stack fold over raw programs. -/
def recognizeRawStack {σ : Type u} (sig : Signature σ) :
    List Tok → List Prog → Option (List Prog)
  | [], st => some st
  | id :: toks, st =>
      match recognizeRawStep sig id st with
      | none => none
      | some st' => recognizeRawStack sig toks st'

/-- Raw recognizer: success means exactly one raw program remains on the stack. -/
def recognizeRaw {σ : Type u} (sig : Signature σ) (toks : List Tok) : Option Prog :=
  match recognizeRawStack sig toks [] with
  | some [p] => some p
  | _ => none

/-- Public parser: table-driven RPN tokens to `Prog`. -/
def recognize {σ : Type u} (sig : Signature σ) (toks : List Tok) : Option Prog :=
  recognizeRaw sig toks

/-- The prefix popped by `popN` followed by the remaining suffix reconstructs the original stack. -/
theorem popN_append {α : Type u} {n : Nat} {st args rest : List α}
    (h : popN n st = some (args, rest)) : args ++ rest = st := by
  induction n generalizing st args rest with
  | zero =>
      simp [popN] at h
      rw [h.1, h.2]
      rfl
  | succ n ih =>
      cases st with
      | nil =>
          simp [popN] at h
      | cons x xs =>
          simp [popN] at h
          cases hpop : popN n xs with
          | none =>
              simp [hpop] at h
          | some r =>
              cases r with
              | mk args' rest' =>
                  simp [hpop] at h
                  have htail := ih hpop
                  rw [← h.1, ← h.2]
                  simp [htail]

theorem recognizeRawStep_sound {σ : Type u} {sig : Signature σ} {id : Tok}
    {stack stack' : List Prog}
    (hstack : ∀ p ∈ stack, WellFormed sig p)
    (hstep : recognizeRawStep sig id stack = some stack') :
    ∀ p ∈ stack', WellFormed sig p := by
  unfold recognizeRawStep at hstep
  cases hentry : entryAt sig id with
  | none =>
      simp [hentry] at hstep
  | some e =>
      simp [hentry] at hstep
      cases hpop : popN e.arity stack with
      | none =>
          simp [hpop] at hstep
      | some r =>
          cases r with
          | mk args rest =>
              simp [hpop] at hstep
              rw [← hstep]
              intro p hp
              rcases List.mem_cons.mp hp with hpHead | hpTail
              · cases hpHead
                apply WellFormed.node (sig := sig) (id := id) (ch := args.reverse) (e := e)
                · exact hentry
                · simp [popN_length hpop]
                · intro c hc
                  apply hstack
                  have hcArgs : c ∈ args := by
                    simpa using List.mem_reverse.mp hc
                  have happ := popN_append hpop
                  rw [← happ]
                  exact List.mem_append_left rest hcArgs
              · apply hstack
                have happ := popN_append hpop
                rw [← happ]
                exact List.mem_append_right args hpTail

theorem recognizeRawStack_sound {σ : Type u} {sig : Signature σ} :
    ∀ {toks stack stack' : List _},
      (∀ p ∈ stack, WellFormed sig p) →
      recognizeRawStack sig toks stack = some stack' →
      ∀ p ∈ stack', WellFormed sig p
  | [], stack, stack', hstack, hrun => by
      simp [recognizeRawStack] at hrun
      rw [← hrun]
      exact hstack
  | id :: toks, stack, stack', hstack, hrun => by
      simp [recognizeRawStack] at hrun
      cases hstep : recognizeRawStep sig id stack with
      | none =>
          simp [hstep] at hrun
      | some mid =>
          simp [hstep] at hrun
          exact recognizeRawStack_sound
            (recognizeRawStep_sound hstack hstep)
            hrun

theorem recognizeRaw_sound {σ : Type u} {sig : Signature σ} {toks : List Tok} {p : Prog}
    (h : recognizeRaw sig toks = some p) : WellFormed sig p := by
  unfold recognizeRaw at h
  cases hstack : recognizeRawStack sig toks [] with
  | none =>
      simp [hstack] at h
  | some stack =>
      cases stack with
      | nil =>
          simp [hstack] at h
      | cons q rest =>
          cases rest with
          | nil =>
              simp [hstack] at h
              rw [← h]
              exact recognizeRawStack_sound (sig := sig)
                (by intro p hp; cases hp)
                hstack q (by simp)
          | cons r rest =>
              simp [hstack] at h

/-- One generic parser theorem: every accepted RPN stream is well-formed for its table. -/
theorem recognize_sound {σ : Type u} {sig : Signature σ} {toks : List Tok} {p : Prog}
    (h : recognize sig toks = some p) : WellFormed sig p := by
  exact recognizeRaw_sound h

/-! ## Verified mask automaton for constrained RPN decoding -/

/-- One stack-depth mask step, represented by a stack of units. -/
def maskStep? {σ : Type u} (sig : Signature σ) (id : Tok) (stack : List Unit) :
    Option (List Unit) :=
  match entryAt sig id with
  | none => none
  | some e =>
      match popN e.arity stack with
      | none => none
      | some (_, rest) => some (() :: rest)

/-- The postfix stack-depth mask machine. -/
def maskStack? {σ : Type u} (sig : Signature σ) :
    List Tok → List Unit → Option (List Unit)
  | [], st => some st
  | id :: toks, st =>
      match maskStep? sig id st with
      | none => none
      | some st' => maskStack? sig toks st'

/-- Legal constrained-decoding masks are precisely streams that leave one item on the depth stack. -/
def maskLegal {σ : Type u} (sig : Signature σ) (toks : List Tok) : Prop :=
  maskStack? sig toks [] = some [()]

theorem popN_lockstep {α β : Type u} :
    ∀ (n : Nat) (xs : List α) (ys : List β), xs.length = ys.length →
      match popN n xs, popN n ys with
      | some (_, xr), some (_, yr) => xr.length = yr.length
      | none, none => True
      | _, _ => False
  | 0, xs, ys, hlen => by
      simp [popN, hlen]
  | n + 1, [], [], hlen => by
      simp [popN]
  | n + 1, [], _ :: _, hlen => by
      cases hlen
  | n + 1, _ :: _, [], hlen => by
      cases hlen
  | n + 1, _ :: xs, _ :: ys, hlen => by
      have htail := popN_lockstep n xs ys (Nat.succ.inj hlen)
      cases hx : popN n xs <;> cases hy : popN n ys <;>
        simp [popN, hx, hy] at htail ⊢
      exact htail

theorem rawStep_maskStep_correct {σ : Type u} (sig : Signature σ) (id : Tok)
    (pst : List Prog) (mst : List Unit) (hlen : pst.length = mst.length) :
    match recognizeRawStep sig id pst, maskStep? sig id mst with
    | some pst', some mst' => pst'.length = mst'.length
    | none, none => True
    | _, _ => False := by
  unfold recognizeRawStep maskStep?
  cases hentry : entryAt sig id with
  | none =>
      simp
  | some e =>
      simp
      have hpop := popN_lockstep e.arity pst mst hlen
      cases hp : popN e.arity pst <;> cases hm : popN e.arity mst <;>
        simp [hp, hm] at hpop ⊢
      exact hpop

theorem rawStack_maskStack_correct {σ : Type u} (sig : Signature σ) :
    ∀ (toks : List Tok) (pst : List Prog) (mst : List Unit),
      pst.length = mst.length →
        match recognizeRawStack sig toks pst, maskStack? sig toks mst with
        | some pout, some mout => pout.length = mout.length
        | none, none => True
        | _, _ => False
  | [], pst, mst, hlen => by
      simp [recognizeRawStack, maskStack?, hlen]
  | id :: toks, pst, mst, hlen => by
      simp [recognizeRawStack, maskStack?]
      have hstep := rawStep_maskStep_correct sig id pst mst hlen
      cases hp : recognizeRawStep sig id pst <;> cases hm : maskStep? sig id mst <;>
        simp [hp, hm] at hstep ⊢
      exact rawStack_maskStack_correct sig toks _ _ hstep

theorem recognizeRaw_iff_maskLegal {σ : Type u} (sig : Signature σ) (toks : List Tok) :
    maskLegal sig toks ↔ (recognizeRaw sig toks).isSome := by
  unfold maskLegal recognizeRaw
  have hrun := rawStack_maskStack_correct sig toks [] [] rfl
  cases hp : recognizeRawStack sig toks [] with
  | none =>
      cases hm : maskStack? sig toks [] with
      | none => simp
      | some mst => simp [hp, hm] at hrun
  | some pst =>
      cases hm : maskStack? sig toks [] with
      | none => simp [hp, hm] at hrun
      | some mst =>
          simp [hp, hm] at hrun ⊢
          cases pst with
          | nil =>
              cases mst with
              | nil => simp
              | cons u mstTail => cases hrun
          | cons p ptail =>
              cases ptail with
              | nil =>
                  cases mst with
                  | nil => cases hrun
                  | cons u mstTail =>
                      cases mstTail with
                      | nil => simp
                      | cons v mstTail => cases hrun
              | cons p2 ptail =>
                  cases mst with
                  | nil => cases hrun
                  | cons u mstTail =>
                      cases mstTail with
                      | nil => cases hrun
                      | cons v mstTail =>
                          simp

/-- The stack-depth mask accepts exactly the token streams accepted by `recognize`. -/
theorem recognize_iff_maskLegal {σ : Type u} (sig : Signature σ) (toks : List Tok) :
    maskLegal sig toks ↔ (recognize sig toks).isSome := by
  exact recognizeRaw_iff_maskLegal sig toks

/-- Canonical postfix emission for a table-indexed program tree. -/
def rpnTokens : Prog → List Tok
  | .node id ch => (ch.map rpnTokens).flatten ++ [id]

theorem recognizeRawStack_append {σ : Type u} (sig : Signature σ) :
    ∀ (toks more : List Tok) (stack : List Prog),
      recognizeRawStack sig (toks ++ more) stack =
        match recognizeRawStack sig toks stack with
        | none => none
        | some stack' => recognizeRawStack sig more stack'
  | [], more, stack => by simp [recognizeRawStack]
  | id :: toks, more, stack => by
      simp [recognizeRawStack]
      cases hstep : recognizeRawStep sig id stack with
      | none => simp
      | some stack' =>
          simp [recognizeRawStack_append sig toks more stack']

theorem popN_append_exact {α : Type u} :
    ∀ (xs rest : List α), popN xs.length (xs ++ rest) = some (xs, rest)
  | [], rest => by simp [popN]
  | x :: xs, rest => by
      simp [popN, popN_append_exact xs rest]

theorem recognizeRawStack_rpnTokens_complete {σ : Type u} {sig : Signature σ}
    {p : Prog} (h : WellFormed sig p) :
    ∀ stack, recognizeRawStack sig (rpnTokens p) stack = some (p :: stack) := by
  induction h with
  | node hentry hlen hall ih =>
      rename_i id ch e
      intro stack
      simp [rpnTokens]
      have hchildrenAll :
          ∀ (xs : List Prog),
            (∀ c ∈ xs, WellFormed sig c) →
            (∀ c ∈ xs, ∀ stack,
              recognizeRawStack sig (rpnTokens c) stack = some (c :: stack)) →
            ∀ stack, recognizeRawStack sig (List.flatten (List.map rpnTokens xs)) stack =
              some (xs.reverse ++ stack) := by
        intro xs
        induction xs with
        | nil =>
            intro hxs ihxs stack
            simp [recognizeRawStack]
        | cons c cs ihcs =>
            intro hxs ihxs stack
            simp [List.map_cons, List.flatten_cons]
            rw [recognizeRawStack_append]
            have hcRun := ihxs c (by simp) stack
            simp [hcRun]
            have htail :
                recognizeRawStack sig (List.flatten (List.map rpnTokens cs)) (c :: stack) =
                  some (cs.reverse ++ c :: stack) := by
              exact ihcs
                (by
                  intro a ha
                  exact hxs a (by simp [ha]))
                (by
                  intro a ha
                  exact ihxs a (by simp [ha]))
                (c :: stack)
            simpa [List.reverse_cons, List.append_assoc] using htail
      have hchildren := hchildrenAll ch hall ih stack
      rw [recognizeRawStack_append]
      rw [hchildren]
      simp [recognizeRawStack, recognizeRawStep, hentry]
      have harity : e.arity = (ch.reverse).length := by
        rw [← hlen]
        simp
      rw [harity]
      have hpop : popN ch.reverse.length (ch.reverse ++ stack) = some (ch.reverse, stack) := by
        exact popN_append_exact (ch.reverse) stack
      rw [hpop]
      simp

theorem recognizeRaw_complete {σ : Type u} {sig : Signature σ} {p : Prog}
    (h : WellFormed sig p) : ∃ toks, recognizeRaw sig toks = some p := by
  refine ⟨rpnTokens p, ?_⟩
  unfold recognizeRaw
  simp [recognizeRawStack_rpnTokens_complete h []]

/-- Every well-formed program has a postfix token stream accepted by `recognize`. -/
theorem recognize_complete {σ : Type u} {sig : Signature σ} {p : Prog}
    (h : WellFormed sig p) : ∃ toks, recognize sig toks = some p := by
  exact recognizeRaw_complete h

/-- Replace the element at index `n`; out-of-bounds writes leave the list unchanged. -/
def setAt {α : Type u} : List α → Nat → α → List α
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | x :: xs, n + 1, v => x :: setAt xs n v

/-- Pure model of the scalar executor's global array/tape state. -/
structure Store where
  tape : List Int
  ptr : Nat
  deriving Repr

namespace Store

def size : Nat := 500

def zero : Store := { tape := List.replicate size 0, ptr := 0 }

def index? (s : Store) (i : Int) : Option Nat :=
  if i < 0 then none
  else
    let n := i.toNat
    if n < s.tape.length then some n else none

def readAt (s : Store) (i : Int) : Int :=
  match s.index? i with
  | none => 0
  | some n =>
      match listGet? s.tape n with
      | some v => v
      | none => 0

def writeAt (s : Store) (i v : Int) : Store :=
  match s.index? i with
  | none => s
  | some n => { s with tape := setAt s.tape n v }

def readPtr? (s : Store) : Option Int := listGet? s.tape s.ptr

def next? (s : Store) : Option Store :=
  if s.ptr + 1 < s.tape.length then some { s with ptr := s.ptr + 1 } else none

def prev (s : Store) : Store :=
  if s.ptr = 0 then s else { s with ptr := s.ptr - 1 }

/-- `exec.sml` line 201 calls `Array.sub`, not `Array.update`; this models that no-op write exactly. -/
def writePtrNoop? (s : Store) (_v : Int) : Option Store :=
  match s.readPtr? with
  | some _ => some s
  | none => none

def withInputAtZero (s : Store) (x : Int) : Store := s.writeAt 0 x

end Store

/-- Scalar-register environment `(x,y,z)`. -/
structure Config where
  x : Int
  y : Int
  z : Int
  deriving Repr

def seed (x : Int) : Config := { x := x, y := 0, z := 0 }

/-- Floor division / floor modulo, guarded against a zero divisor. -/
def sdiv (a b : Int) : Option Int := if b = 0 then none else some (Int.fdiv a b)
def smod (a b : Int) : Option Int := if b = 0 then none else some (Int.fmod a b)

mutual

/--
Table-driven scalar evaluator.  `none` means fuel exhaustion, unknown operator id, arity/primitive
mismatch, or an explicit partial operation (division by zero, out-of-tape `next`, empty pointer read).
-/
def eval : Nat → Signature Prim → Prog → Config → Store → Option (Int × Store)
  | 0, _, _, _, _ => none
  | fuel + 1, sig, .node id ch, cfg, st =>
      match entryAt sig id with
      | none => none
      | some e =>
          match e.prim, ch with
          | .zero, [] => some (0, st)
          | .one,  [] => some (1, st)
          | .two,  [] => some (2, st)
          | .x,    [] => some (cfg.x, st)
          | .y,    [] => some (cfg.y, st)
          | .z,    [] => some (cfg.z, st)
          | .suc,  [a] => do
              let ra ← eval fuel sig a cfg st
              some (ra.1 + 1, ra.2)
          | .pred, [a] => do
              let ra ← eval fuel sig a cfg st
              some (ra.1 - 1, ra.2)
          | .addi, [a, b] => do
              let ra ← eval fuel sig a cfg st
              let rb ← eval fuel sig b cfg ra.2
              some (ra.1 + rb.1, rb.2)
          | .diff, [a, b] => do
              let ra ← eval fuel sig a cfg st
              let rb ← eval fuel sig b cfg ra.2
              some (ra.1 - rb.1, rb.2)
          | .mult, [a, b] => do
              let ra ← eval fuel sig a cfg st
              let rb ← eval fuel sig b cfg ra.2
              some (ra.1 * rb.1, rb.2)
          | .divi, [a, b] => do
              let ra ← eval fuel sig a cfg st
              let rb ← eval fuel sig b cfg ra.2
              let q ← sdiv ra.1 rb.1
              some (q, rb.2)
          | .modu, [a, b] => do
              let ra ← eval fuel sig a cfg st
              let rb ← eval fuel sig b cfg ra.2
              let r ← smod ra.1 rb.1
              some (r, rb.2)
          | .cond, [c, t, e'] => do
              let rc ← eval fuel sig c cfg st
              if rc.1 ≤ 0 then eval fuel sig t cfg rc.2 else eval fuel sig e' cfg rc.2
          | .loop, [f, n, x0] => do
              let rn ← eval fuel sig n cfg st
              let rx0 ← eval fuel sig x0 cfg rn.2
              loopIter fuel sig f rn.1.toNat rx0.1 1 rx0.1 rx0.2
          | .loop2, [f, g, n, a, b] => do
              let rn ← eval fuel sig n cfg st
              let ra ← eval fuel sig a cfg rn.2
              let rb ← eval fuel sig b cfg ra.2
              loop2Iter fuel sig f g rn.1.toNat ra.1 rb.1 1 rb.2
          | .compr, [f, n] => do
              let rn ← eval fuel sig n cfg st
              comprSearch fuel sig f rn.1.toNat 0 0 rn.2
          | .loope, [f, n] => do
              let rn ← eval fuel sig n cfg st
              loopeIter fuel sig f rn.1.toNat rn.2
          | .array, [a] => do
              let ra ← eval fuel sig a cfg st
              some (ra.2.readAt ra.1, ra.2)
          | .assign, [a, b] => do
              let ra ← eval fuel sig a cfg st
              let rb ← eval fuel sig b cfg ra.2
              some (0, rb.2.writeAt ra.1 rb.1)
          | .next, [] =>
              match st.next? with
              | some st' => some (0, st')
              | none => none
          | .prev, [] => some (0, st.prev)
          | .read, [] =>
              match st.readPtr? with
              | some v => some (v, st)
              | none => none
          | .write, [a] => do
              let ra ← eval fuel sig a cfg st
              let st' ← ra.2.writePtrNoop? ra.1
              some (0, st')
          | _, _ => none

/-- `loop_f`: iterate `k` times, updating `x1 := f(x1,counter,input)`, counter starting at `1`. -/
def loopIter :
    Nat → Signature Prim → Prog → Nat → Int → Int → Int → Store → Option (Int × Store)
  | 0, _, _, _, _, _, _, _ => none
  | _, _, _, 0, x1, _, _, st => some (x1, st)
  | fuel + 1, sig, f, k + 1, x1, x2, x3, st => do
      let rf ← eval fuel sig f { x := x1, y := x2, z := x3 } st
      loopIter fuel sig f k rf.1 (x2 + 1) x3 rf.2

/-- `loop2_f`: update `(x1,x2) := (f(old), g(old))`, incrementing hidden `z` from `1`. -/
def loop2Iter :
    Nat → Signature Prim → Prog → Prog → Nat → Int → Int → Int → Store → Option (Int × Store)
  | 0, _, _, _, _, _, _, _, _ => none
  | _, _, _, _, 0, x1, _, _, st => some (x1, st)
  | fuel + 1, sig, f, g, k + 1, x1, x2, x3, st => do
      let cfg := { x := x1, y := x2, z := x3 }
      let rf ← eval fuel sig f cfg st
      let rg ← eval fuel sig g cfg rf.2
      loop2Iter fuel sig f g k rf.1 rg.1 (x3 + 1) rg.2

/-- `loope_f`: execute the body at `(0,0,0)` `k` times for effects, returning `0`. -/
def loopeIter : Nat → Signature Prim → Prog → Nat → Store → Option (Int × Store)
  | 0, _, _, _, _ => none
  | _, _, _, 0, st => some (0, st)
  | fuel + 1, sig, f, k + 1, st => do
      let r ← eval fuel sig f { x := 0, y := 0, z := 0 } st
      loopeIter fuel sig f k r.2

/-- Non-cached scalar comprehension: find the `target`-th candidate `c >= 0` with `f(c,0,0) <= 0`. -/
def comprSearch :
    Nat → Signature Prim → Prog → Nat → Nat → Int → Store → Option (Int × Store)
  | 0, _, _, _, _, _, _ => none
  | fuel + 1, sig, f, target, seen, cand, st => do
      let r ← eval fuel sig f { x := cand, y := 0, z := 0 } st
      if r.1 ≤ 0 then
        if seen ≥ target then some (cand, r.2)
        else comprSearch fuel sig f target (seen + 1) (cand + 1) r.2
      else
        comprSearch fuel sig f target seen (cand + 1) r.2

end

/-- Run a program at scalar OEIS seed `(k,0,0)` with an explicit initial store. -/
def termWithStore (fuel : Nat) (sig : Signature Prim) (p : Prog) (k : Int) (st : Store) : Option Int := do
  let r ← eval fuel sig p (seed k) st
  some r.1

/-- Run a program at scalar OEIS seed `(k,0,0)` with a zeroed store. -/
def term (fuel : Nat) (sig : Signature Prim) (p : Prog) (k : Int) : Option Int :=
  termWithStore fuel sig p k Store.zero

def seqPrefix (fuel : Nat) (sig : Signature Prim) (p : Prog) (len : Nat) : List (Option Int) :=
  (List.range len).map (fun k => term fuel sig p (Int.ofNat k))

/-! ## Extensional equivalence — the parametric E1 equations `E` -/

/-- `p ≈ q` for a fixed table: `eval` agrees for all fuel, scalar registers, and store states. -/
def Extensional (sig : Signature Prim) (p q : Prog) : Prop :=
  ∀ fuel cfg st, eval fuel sig p cfg st = eval fuel sig q cfg st

theorem Extensional.refl (sig : Signature Prim) (p : Prog) : Extensional sig p p :=
  fun _ _ _ => rfl

theorem Extensional.symm {sig : Signature Prim} {p q : Prog}
    (h : Extensional sig p q) : Extensional sig q p :=
  fun fuel cfg st => (h fuel cfg st).symm

theorem Extensional.trans {sig : Signature Prim} {p q r : Prog}
    (h₁ : Extensional sig p q) (h₂ : Extensional sig q r) : Extensional sig p r :=
  fun fuel cfg st => (h₁ fuel cfg st).trans (h₂ fuel cfg st)

/-- The GSLT equations `E` as a `Setoid`, parameterized by the active operator table. -/
def extSetoid (sig : Signature Prim) : Setoid Prog where
  r := Extensional sig
  iseqv :=
    ⟨ Extensional.refl sig
    , fun h => Extensional.symm h
    , fun h₁ h₂ => Extensional.trans h₁ h₂
    ⟩

/-! ## Certified commutative canonicalization -/

mutual
def progSize : Prog → Nat
  | .node _ ch => 1 + progListSize ch

def progListSize : List Prog → Nat
  | [] => 0
  | p :: ps => progSize p + progListSize ps
end

mutual
/-- Fuel-bounded strict lexicographic order matching the executable canonicalizer's structural key. -/
def progStructuralLtBound : Nat → Prog → Prog → Bool
  | 0, _, _ => false
  | fuel + 1, .node id₁ ch₁, .node id₂ ch₂ =>
      if id₁ < id₂ then true
      else if id₂ < id₁ then false
      else progListStructuralLtBound fuel ch₁ ch₂

/-- Fuel-bounded lexicographic list order for structural program keys. -/
def progListStructuralLtBound : Nat → List Prog → List Prog → Bool
  | 0, _, _ => false
  | _ + 1, [], [] => false
  | _ + 1, [], _ :: _ => true
  | _ + 1, _ :: _, [] => false
  | fuel + 1, p :: ps, q :: qs =>
      if progStructuralLtBound fuel p q then true
      else if progStructuralLtBound fuel q p then false
      else progListStructuralLtBound fuel ps qs
end

/-- Strict structural order used for commutative canonicalization. -/
def progStructuralLt (p q : Prog) : Bool :=
  progStructuralLtBound (progSize p + progSize q + 1) p q

def canonicalPair (p q : Prog) : Prog × Prog :=
  if progStructuralLt q p then (q, p) else (p, q)

/--
Canonicalization flags.  The current executable canonicalizer consumes the commutativity flag; assoc
and identity flags are represented as proof obligations before any future canonicalizer uses them.
-/
structure CanonicalPolicy (sig : Signature Prim) where
  comm : Nat → Bool
  assoc : Nat → Bool
  identityOf : Nat → Option Nat

def noCanonicalPolicy (sig : Signature Prim) : CanonicalPolicy sig where
  comm := fun _ => false
  assoc := fun _ => false
  identityOf := fun _ => none

mutual
def canonicalize (policy : CanonicalPolicy sig) : Prog → Prog
  | .node id ch =>
      let ch' := canonicalizeList policy ch
      match ch' with
      | [a, b] =>
          if policy.comm id then
            let ab := canonicalPair a b
            .node id [ab.1, ab.2]
          else
            .node id ch'
      | _ => .node id ch'

def canonicalizeList (policy : CanonicalPolicy sig) : List Prog → List Prog
  | [] => []
  | p :: ps => canonicalize policy p :: canonicalizeList policy ps
end

def commutativeEvalLaw (sig : Signature Prim) (id : Nat) : Prop :=
  ∀ fuel a b cfg st,
    eval fuel sig (.node id [a, b]) cfg st =
      eval fuel sig (.node id [b, a]) cfg st

def associativeEvalLaw (sig : Signature Prim) (id : Nat) : Prop :=
  ∀ fuel a b c cfg st,
    eval fuel sig (.node id [.node id [a, b], c]) cfg st =
      eval fuel sig (.node id [a, .node id [b, c]]) cfg st

def identityEvalLaw (sig : Signature Prim) (id ident : Nat) : Prop :=
  ∀ fuel a cfg st,
    eval fuel sig (.node id [.node ident [], a]) cfg st = eval fuel sig a cfg st ∧
      eval fuel sig (.node id [a, .node ident []]) cfg st = eval fuel sig a cfg st

def CanonicalPolicy.Sound (policy : CanonicalPolicy sig) : Prop :=
  ∀ id, policy.comm id = true → commutativeEvalLaw sig id

def CanonicalPolicy.AllFlagLawsSound (policy : CanonicalPolicy sig) : Prop :=
  policy.Sound ∧
    (∀ id, policy.assoc id = true → associativeEvalLaw sig id) ∧
    (∀ id ident, policy.identityOf id = some ident → identityEvalLaw sig id ident)

namespace Prim

/-- A primitive is store-neutral when it never mutates the global store by itself. -/
def storeNeutral : Prim → Prop
  | .assign => False
  | .next => False
  | .prev => False
  | _ => True

end Prim

theorem writePtrNoop?_store_eq {s s' : Store} {v : Int}
    (h : s.writePtrNoop? v = some s') : s' = s := by
  unfold Store.writePtrNoop? at h
  cases hread : s.readPtr? with
  | none =>
      simp [hread] at h
  | some value =>
      simp [hread] at h
      exact h.symm

theorem eval_store_preserving_all {sig : Signature Prim}
    (hSig : ∀ id e, entryAt sig id = some e → e.prim.storeNeutral) :
    ∀ fuel,
      (∀ (p : Prog) (cfg : Config) (st : Store) (r : Int × Store),
        eval fuel sig p cfg st = some r → r.2 = st) ∧
      (∀ (f g : Prog) (k : Nat) (x1 x2 x3 : Int) (st : Store) (r : Int × Store),
        loop2Iter fuel sig f g k x1 x2 x3 st = some r → r.2 = st) ∧
      (∀ (f : Prog) (k : Nat) (x1 x2 x3 : Int) (st : Store) (r : Int × Store),
        loopIter fuel sig f k x1 x2 x3 st = some r → r.2 = st) ∧
      (∀ (f : Prog) (k : Nat) (st : Store) (r : Int × Store),
        loopeIter fuel sig f k st = some r → r.2 = st) ∧
      (∀ (f : Prog) (target seen : Nat) (cand : Int) (st : Store) (r : Int × Store),
        comprSearch fuel sig f target seen cand st = some r → r.2 = st) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro p cfg st r h
        cases p
        simp [eval] at h
      constructor
      · intro f g k x1 x2 x3 st r h
        simp [loop2Iter] at h
      constructor
      · intro f k x1 x2 x3 st r h
        simp [loopIter] at h
      constructor
      · intro f k st r h
        simp [loopeIter] at h
      · intro f target seen cand st r h
        simp [comprSearch] at h
  | succ fuel ih =>
      rcases ih with ⟨ihEval, ihLoop2, ihLoop, ihLoope, ihCompr⟩
      constructor
      · intro p cfg st r h
        cases p with
        | node id ch =>
            cases hentry : entryAt sig id with
            | none =>
                simp [eval, hentry] at h
            | some e =>
                cases e with
                | mk name arity ho prim =>
                    have hneutral :
                        Prim.storeNeutral prim := by
                      exact hSig id
                        ({ name := name, arity := arity, hoArity := ho, prim := prim } :
                          Entry Prim)
                        hentry
                    cases ch with
                    | nil =>
                        cases prim <;> simp [eval, hentry, Prim.storeNeutral] at hneutral h ⊢
                        · rw [← h]
                        · rw [← h]
                        · rw [← h]
                        · rw [← h]
                        · rw [← h]
                        · rw [← h]
                        · cases hread : st.readPtr? with
                          | none =>
                              simp [hread] at h
                          | some value =>
                              simp [hread] at h
                              rw [← h]
                    | cons a ch1 =>
                        cases ch1 with
                        | nil =>
                            cases prim <;> simp [eval, hentry, Prim.storeNeutral] at hneutral h ⊢
                            · cases ha : eval fuel sig a cfg st with
                              | none =>
                                  simp [ha] at h
                              | some ra =>
                                  simp [ha] at h
                                  rw [← h]
                                  exact ihEval a cfg st ra ha
                            · cases ha : eval fuel sig a cfg st with
                              | none =>
                                  simp [ha] at h
                              | some ra =>
                                  simp [ha] at h
                                  rw [← h]
                                  exact ihEval a cfg st ra ha
                            · cases ha : eval fuel sig a cfg st with
                              | none =>
                                  simp [ha] at h
                              | some ra =>
                                  simp [ha] at h
                                  rw [← h]
                                  exact ihEval a cfg st ra ha
                            · cases ha : eval fuel sig a cfg st with
                              | none =>
                                  simp [ha] at h
                              | some ra =>
                                  simp [ha] at h
                                  cases hw : ra.2.writePtrNoop? ra.1 with
                                  | none =>
                                      simp [hw] at h
                                  | some st' =>
                                      simp [hw] at h
                                      have hst' : st' = ra.2 := writePtrNoop?_store_eq hw
                                      have hra : ra.2 = st := ihEval a cfg st ra ha
                                      rw [← h]
                                      simp [hst', hra]
                        | cons b ch2 =>
                            cases ch2 with
                            | nil =>
                                cases prim <;> simp [eval, hentry, Prim.storeNeutral] at hneutral h ⊢
                                · cases ha : eval fuel sig a cfg st with
                                  | none =>
                                      simp [ha] at h
                                  | some ra =>
                                      have hra : ra.2 = st := ihEval a cfg st ra ha
                                      cases hb : eval fuel sig b cfg ra.2 with
                                      | none =>
                                          simp [ha, hb] at h
                                      | some rb =>
                                          simp [ha, hb] at h
                                          have hrb : rb.2 = ra.2 := ihEval b cfg ra.2 rb hb
                                          rw [← h, hrb, hra]
                                · cases ha : eval fuel sig a cfg st with
                                  | none =>
                                      simp [ha] at h
                                  | some ra =>
                                      have hra : ra.2 = st := ihEval a cfg st ra ha
                                      cases hb : eval fuel sig b cfg ra.2 with
                                      | none =>
                                          simp [ha, hb] at h
                                      | some rb =>
                                          simp [ha, hb] at h
                                          have hrb : rb.2 = ra.2 := ihEval b cfg ra.2 rb hb
                                          rw [← h, hrb, hra]
                                · cases ha : eval fuel sig a cfg st with
                                  | none =>
                                      simp [ha] at h
                                  | some ra =>
                                      have hra : ra.2 = st := ihEval a cfg st ra ha
                                      cases hb : eval fuel sig b cfg ra.2 with
                                      | none =>
                                          simp [ha, hb] at h
                                      | some rb =>
                                          simp [ha, hb] at h
                                          have hrb : rb.2 = ra.2 := ihEval b cfg ra.2 rb hb
                                          rw [← h, hrb, hra]
                                · cases ha : eval fuel sig a cfg st with
                                  | none =>
                                      simp [ha] at h
                                  | some ra =>
                                      have hra : ra.2 = st := ihEval a cfg st ra ha
                                      cases hb : eval fuel sig b cfg ra.2 with
                                      | none =>
                                          simp [ha, hb] at h
                                      | some rb =>
                                          simp [ha, hb] at h
                                          cases hdiv : sdiv ra.1 rb.1 with
                                          | none =>
                                              simp [hdiv] at h
                                          | some q =>
                                              simp [hdiv] at h
                                              have hrb : rb.2 = ra.2 := ihEval b cfg ra.2 rb hb
                                              rw [← h, hrb, hra]
                                · cases ha : eval fuel sig a cfg st with
                                  | none =>
                                      simp [ha] at h
                                  | some ra =>
                                      have hra : ra.2 = st := ihEval a cfg st ra ha
                                      cases hb : eval fuel sig b cfg ra.2 with
                                      | none =>
                                          simp [ha, hb] at h
                                      | some rb =>
                                          simp [ha, hb] at h
                                          cases hmod : smod ra.1 rb.1 with
                                          | none =>
                                              simp [hmod] at h
                                          | some q =>
                                              simp [hmod] at h
                                              have hrb : rb.2 = ra.2 := ihEval b cfg ra.2 rb hb
                                              rw [← h, hrb, hra]
                                · cases hn : eval fuel sig b cfg st with
                                  | none =>
                                      simp [hn] at h
                                  | some rn =>
                                      have hrn : rn.2 = st := ihEval b cfg st rn hn
                                      simp [hn] at h
                                      have hloop := ihCompr a rn.1.toNat 0 0 rn.2 r h
                                      rw [hloop, hrn]
                                · cases hn : eval fuel sig b cfg st with
                                  | none =>
                                      simp [hn] at h
                                  | some rn =>
                                      have hrn : rn.2 = st := ihEval b cfg st rn hn
                                      simp [hn] at h
                                      have hloop := ihLoope a rn.1.toNat rn.2 r h
                                      rw [hloop, hrn]
                            | cons c ch3 =>
                                cases ch3 with
                                | nil =>
                                    cases prim <;> simp [eval, hentry, Prim.storeNeutral] at hneutral h ⊢
                                    · cases hc : eval fuel sig a cfg st with
                                      | none =>
                                          simp [hc] at h
                                      | some rc =>
                                          have hrc : rc.2 = st := ihEval a cfg st rc hc
                                          by_cases hle : rc.1 ≤ 0
                                          · simp [hc, hle] at h
                                            have ht : r.2 = rc.2 := ihEval b cfg rc.2 r h
                                            rw [ht, hrc]
                                          · simp [hc, hle] at h
                                            have he : r.2 = rc.2 := ihEval c cfg rc.2 r h
                                            rw [he, hrc]
                                    · cases hn : eval fuel sig b cfg st with
                                      | none =>
                                          simp [hn] at h
                                      | some rn =>
                                          have hrn : rn.2 = st := ihEval b cfg st rn hn
                                          cases hx0 : eval fuel sig c cfg rn.2 with
                                          | none =>
                                              simp [hn, hx0] at h
                                          | some rx0 =>
                                              simp [hn, hx0] at h
                                              have hx0s : rx0.2 = rn.2 := ihEval c cfg rn.2 rx0 hx0
                                              have hloop := ihLoop a rn.1.toNat rx0.1 1 rx0.1 rx0.2 r h
                                              rw [hloop, hx0s, hrn]
                                | cons d ch4 =>
                                    cases ch4 with
                                    | nil =>
                                        cases prim <;> simp [eval, hentry, Prim.storeNeutral] at hneutral h ⊢
                                    | cons e ch5 =>
                                        cases ch5 with
                                        | nil =>
                                            cases prim <;> simp [eval, hentry, Prim.storeNeutral] at hneutral h ⊢
                                            cases hn : eval fuel sig c cfg st with
                                            | none =>
                                                simp [hn] at h
                                            | some rn =>
                                                have hrn : rn.2 = st := ihEval c cfg st rn hn
                                                cases ha : eval fuel sig d cfg rn.2 with
                                                | none =>
                                                    simp [hn, ha] at h
                                                | some ra =>
                                                    have hra : ra.2 = rn.2 := ihEval d cfg rn.2 ra ha
                                                    cases hb : eval fuel sig e cfg ra.2 with
                                                    | none =>
                                                        simp [hn, ha, hb] at h
                                                    | some rb =>
                                                        simp [hn, ha, hb] at h
                                                        have hrb : rb.2 = ra.2 := ihEval e cfg ra.2 rb hb
                                                        have hloop :=
                                                          ihLoop2 a b rn.1.toNat ra.1 rb.1 1 rb.2 r h
                                                        rw [hloop, hrb, hra, hrn]
                                        | cons f ch6 =>
                                            cases prim <;> simp [eval, hentry, Prim.storeNeutral] at hneutral h ⊢
      constructor
      · intro f g k x1 x2 x3 st r h
        cases k with
        | zero =>
            simp [loop2Iter] at h
            rw [← h]
        | succ k =>
            simp [loop2Iter] at h
            cases hf : eval fuel sig f { x := x1, y := x2, z := x3 } st with
            | none =>
                simp [hf] at h
            | some rf =>
                have hrf : rf.2 = st := ihEval f { x := x1, y := x2, z := x3 } st rf hf
                cases hg : eval fuel sig g { x := x1, y := x2, z := x3 } rf.2 with
                | none =>
                    simp [hf, hg] at h
                | some rg =>
                    simp [hf, hg] at h
                    have hrg : rg.2 = rf.2 := ihEval g { x := x1, y := x2, z := x3 } rf.2 rg hg
                    have hloop := ihLoop2 f g k rf.1 rg.1 (x3 + 1) rg.2 r h
                    rw [hloop, hrg, hrf]
      constructor
      · intro f k x1 x2 x3 st r h
        cases k with
        | zero =>
            simp [loopIter] at h
            rw [← h]
        | succ k =>
            simp [loopIter] at h
            cases hf : eval fuel sig f { x := x1, y := x2, z := x3 } st with
            | none =>
                simp [hf] at h
            | some rf =>
                simp [hf] at h
                have hrf : rf.2 = st := ihEval f { x := x1, y := x2, z := x3 } st rf hf
                have hloop := ihLoop f k rf.1 (x2 + 1) x3 rf.2 r h
                rw [hloop, hrf]
      constructor
      · intro f k st r h
        cases k with
        | zero =>
            simp [loopeIter] at h
            rw [← h]
        | succ k =>
            simp [loopeIter] at h
            cases hf : eval fuel sig f { x := 0, y := 0, z := 0 } st with
            | none =>
                simp [hf] at h
            | some rf =>
                simp [hf] at h
                have hrf : rf.2 = st := ihEval f { x := 0, y := 0, z := 0 } st rf hf
                have hloop := ihLoope f k rf.2 r h
                rw [hloop, hrf]
      · intro f target seen cand st r h
        simp [comprSearch] at h
        cases hf : eval fuel sig f { x := cand, y := 0, z := 0 } st with
        | none =>
            simp [hf] at h
        | some rf =>
            have hrf : rf.2 = st := ihEval f { x := cand, y := 0, z := 0 } st rf hf
            by_cases hle : rf.1 ≤ 0
            · by_cases hseen : seen ≥ target
              · simp [hf, hle, hseen] at h
                rw [← h, hrf]
              · simp [hf, hle, hseen] at h
                have hrec := ihCompr f target (seen + 1) (cand + 1) rf.2 r h
                rw [hrec, hrf]
            · simp [hf, hle] at h
              have hrec := ihCompr f target seen (cand + 1) rf.2 r h
              rw [hrec, hrf]

theorem addi_commutativeEvalLaw_of_entry {sig : Signature Prim}
    (hSig : ∀ id e, entryAt sig id = some e → e.prim.storeNeutral)
    {id : Nat} {name : String} {arity ho : Nat}
    (hentry :
      entryAt sig id =
        some ({ name := name, arity := arity, hoArity := ho, prim := .addi } : Entry Prim)) :
    commutativeEvalLaw sig id := by
  intro fuel a b cfg st
  cases fuel with
  | zero =>
      simp [eval]
  | succ fuel =>
      have hstore := eval_store_preserving_all (sig := sig) hSig fuel
      simp [eval, hentry]
      cases ha : eval fuel sig a cfg st with
      | none =>
          cases hb : eval fuel sig b cfg st with
          | none =>
              simp
          | some rb =>
              have hbStore : rb.2 = st := hstore.1 b cfg st rb hb
              simp [ha, hbStore]
      | some ra =>
          have haStore : ra.2 = st := hstore.1 a cfg st ra ha
          cases hb : eval fuel sig b cfg st with
          | none =>
              simp [hb, haStore]
          | some rb =>
              have hbStore : rb.2 = st := hstore.1 b cfg st rb hb
              simp [ha, hb, haStore, hbStore, Int.add_comm]

theorem mult_commutativeEvalLaw_of_entry {sig : Signature Prim}
    (hSig : ∀ id e, entryAt sig id = some e → e.prim.storeNeutral)
    {id : Nat} {name : String} {arity ho : Nat}
    (hentry :
      entryAt sig id =
        some ({ name := name, arity := arity, hoArity := ho, prim := .mult } : Entry Prim)) :
    commutativeEvalLaw sig id := by
  intro fuel a b cfg st
  cases fuel with
  | zero =>
      simp [eval]
  | succ fuel =>
      have hstore := eval_store_preserving_all (sig := sig) hSig fuel
      simp [eval, hentry]
      cases ha : eval fuel sig a cfg st with
      | none =>
          cases hb : eval fuel sig b cfg st with
          | none =>
              simp
          | some rb =>
              have hbStore : rb.2 = st := hstore.1 b cfg st rb hb
              simp [ha, hbStore]
      | some ra =>
          have haStore : ra.2 = st := hstore.1 a cfg st ra ha
          cases hb : eval fuel sig b cfg st with
          | none =>
              simp [hb, haStore]
          | some rb =>
              have hbStore : rb.2 = st := hstore.1 b cfg st rb hb
              simp [ha, hb, haStore, hbStore, Int.mul_comm]

theorem canonicalize_sound_all {sig : Signature Prim} (policy : CanonicalPolicy sig)
    (hpolicy : policy.Sound) :
    ∀ fuel,
      (∀ (p : Prog) (cfg : Config) (st : Store),
        eval fuel sig (canonicalize policy p) cfg st = eval fuel sig p cfg st) ∧
      (∀ (f g : Prog) (k : Nat) (x1 x2 x3 : Int) (st : Store),
        loop2Iter fuel sig (canonicalize policy f) (canonicalize policy g) k x1 x2 x3 st =
          loop2Iter fuel sig f g k x1 x2 x3 st) ∧
      (∀ (f : Prog) (k : Nat) (x1 x2 x3 : Int) (st : Store),
        loopIter fuel sig (canonicalize policy f) k x1 x2 x3 st =
          loopIter fuel sig f k x1 x2 x3 st) ∧
      (∀ (f : Prog) (k : Nat) (st : Store),
        loopeIter fuel sig (canonicalize policy f) k st = loopeIter fuel sig f k st) ∧
      (∀ (f : Prog) (target seen : Nat) (cand : Int) (st : Store),
        comprSearch fuel sig (canonicalize policy f) target seen cand st =
          comprSearch fuel sig f target seen cand st) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro p cfg st
        cases p
        simp [canonicalize, eval]
      constructor
      · intro f g k x1 x2 x3 st
        simp [loop2Iter]
      constructor
      · intro f k x1 x2 x3 st
        simp [loopIter]
      constructor
      · intro f k st
        simp [loopeIter]
      · intro f target seen cand st
        simp [comprSearch]
  | succ fuel ih =>
      rcases ih with ⟨ihEval, ihLoop2, ihLoop, ihLoope, ihCompr⟩
      constructor
      · intro p cfg st
        cases p with
        | node id ch =>
            cases ch with
            | nil =>
                simp [canonicalize, canonicalizeList, eval]
            | cons a ch1 =>
                cases ch1 with
                | nil =>
                    cases hentry : entryAt sig id with
                    | none =>
                        simp [canonicalize, canonicalizeList, eval, hentry]
                    | some e =>
                        cases e with
                        | mk name arity ho prim =>
                            cases prim <;>
                              simp [canonicalize, canonicalizeList, eval, hentry, ihEval]
                | cons b ch2 =>
                    cases ch2 with
                    | nil =>
                        cases hcomm : policy.comm id with
                        | false =>
                            cases hentry : entryAt sig id with
                            | none =>
                                simp [canonicalize, canonicalizeList, eval, hentry, hcomm]
                            | some e =>
                                cases e with
                                | mk name arity ho prim =>
                                    cases prim <;>
                                      simp [canonicalize, canonicalizeList, eval, hentry,
                                        hcomm, ihEval, ihCompr, ihLoope]
                        | true =>
                            cases hlt :
                                progStructuralLt (canonicalize policy b) (canonicalize policy a) with
                            | true =>
                              have hcommLaw :
                                  eval (fuel + 1) sig
                                    (.node id [canonicalize policy a, canonicalize policy b]) cfg st =
                                  eval (fuel + 1) sig
                                    (.node id [canonicalize policy b, canonicalize policy a]) cfg st :=
                                hpolicy id hcomm (fuel + 1)
                                  (canonicalize policy a) (canonicalize policy b) cfg st
                              simp [canonicalize, canonicalizeList, canonicalPair, hcomm, hlt]
                              rw [← hcommLaw]
                              cases hentry : entryAt sig id with
                              | none =>
                                  simp [eval, hentry]
                              | some e =>
                                  cases e with
                                  | mk name arity ho prim =>
                                      cases prim <;>
                                        simp [eval, hentry, ihEval, ihCompr, ihLoope]
                            | false =>
                                cases hentry : entryAt sig id with
                                | none =>
                                    simp [canonicalize, canonicalizeList, canonicalPair, eval, hentry,
                                      hcomm, hlt]
                                | some e =>
                                    cases e with
                                    | mk name arity ho prim =>
                                        cases prim <;>
                                          simp [canonicalize, canonicalizeList, canonicalPair, eval, hentry,
                                            hcomm, hlt, ihEval, ihCompr, ihLoope]
                    | cons c ch3 =>
                        cases ch3 with
                        | nil =>
                            cases hentry : entryAt sig id with
                            | none =>
                                simp [canonicalize, canonicalizeList, eval, hentry]
                            | some e =>
                                cases e with
                                | mk name arity ho prim =>
                                    cases prim <;>
                                      simp [canonicalize, canonicalizeList, eval, hentry, ihEval, ihLoop]
                        | cons d ch4 =>
                            cases ch4 with
                            | nil =>
                                cases hentry : entryAt sig id with
                                | none =>
                                    simp [canonicalize, canonicalizeList, eval, hentry]
                                | some e =>
                                    cases e with
                                    | mk name arity ho prim =>
                                        cases prim <;>
                                          simp [canonicalize, canonicalizeList, eval, hentry]
                            | cons e ch5 =>
                                cases ch5 with
                                | nil =>
                                    cases hentry : entryAt sig id with
                                    | none =>
                                        simp [canonicalize, canonicalizeList, eval, hentry]
                                    | some ent =>
                                        cases ent with
                                        | mk name arity ho prim =>
                                            cases prim <;>
                                              simp [canonicalize, canonicalizeList, eval, hentry, ihEval,
                                                ihLoop2]
                                | cons f ch6 =>
                                    cases hentry : entryAt sig id with
                                    | none =>
                                        simp [canonicalize, canonicalizeList, eval, hentry]
                                    | some ent =>
                                        cases ent with
                                        | mk name arity ho prim =>
                                            cases prim <;>
                                              simp [canonicalize, canonicalizeList, eval, hentry]
      constructor
      · intro f g k x1 x2 x3 st
        cases k with
        | zero =>
            simp [loop2Iter]
        | succ k =>
            simp [loop2Iter]
            rw [ihEval f { x := x1, y := x2, z := x3 } st]
            cases hf : eval fuel sig f { x := x1, y := x2, z := x3 } st with
            | none =>
                simp
            | some rf =>
                simp
                rw [ihEval g { x := x1, y := x2, z := x3 } rf.2]
                cases hg : eval fuel sig g { x := x1, y := x2, z := x3 } rf.2 with
                | none =>
                    simp
                | some rg =>
                    simp [ihLoop2 f g k rf.1 rg.1 (x3 + 1) rg.2]
      constructor
      · intro f k x1 x2 x3 st
        cases k with
        | zero =>
            simp [loopIter]
        | succ k =>
            simp [loopIter]
            rw [ihEval f { x := x1, y := x2, z := x3 } st]
            cases hf : eval fuel sig f { x := x1, y := x2, z := x3 } st with
            | none =>
                simp
            | some rf =>
                simp [ihLoop f k rf.1 (x2 + 1) x3 rf.2]
      constructor
      · intro f k st
        cases k with
        | zero =>
            simp [loopeIter]
        | succ k =>
            simp [loopeIter]
            rw [ihEval f { x := 0, y := 0, z := 0 } st]
            cases hf : eval fuel sig f { x := 0, y := 0, z := 0 } st with
            | none =>
                simp
            | some rf =>
                simp [ihLoope f k rf.2]
      · intro f target seen cand st
        simp [comprSearch]
        rw [ihEval f { x := cand, y := 0, z := 0 } st]
        cases hf : eval fuel sig f { x := cand, y := 0, z := 0 } st with
        | none =>
            simp
        | some rf =>
            by_cases hle : rf.1 ≤ 0
            · by_cases hseen : seen ≥ target
              · simp [hle, hseen]
              · simp [hle, hseen, ihCompr f target (seen + 1) (cand + 1) rf.2]
            · simp [hle, ihCompr f target seen (cand + 1) rf.2]

theorem canonicalize_sound {sig : Signature Prim} (policy : CanonicalPolicy sig)
    (hpolicy : policy.Sound) :
    ∀ p, Extensional sig (canonicalize policy p) p := by
  intro p fuel cfg st
  exact (canonicalize_sound_all policy hpolicy fuel).1 p cfg st

/-! ## Signature relabeling invariance -/

/-- The executable shape of a table entry, excluding its source name. -/
def EntryShapeEq (e₁ e₂ : Entry Prim) : Prop :=
  e₂.arity = e₁.arity ∧ e₂.hoArity = e₁.hoArity ∧ e₂.prim = e₁.prim

/-- A bijection between table indices that preserves arity, higher-order arity, and semantics. -/
structure SignatureIso (sig₁ sig₂ : Signature Prim) where
  toFun : Nat → Nat
  invFun : Nat → Nat
  left_inv : ∀ id, invFun (toFun id) = id
  right_inv : ∀ id, toFun (invFun id) = id
  entry_shape : ∀ id,
    match entryAt sig₁ id, entryAt sig₂ (toFun id) with
    | some e₁, some e₂ => EntryShapeEq e₁ e₂
    | none, none => True
    | _, _ => False

/-- Relabel every operator id in a program through a signature isomorphism. -/
def relabel (φ : SignatureIso sig₁ sig₂) : Prog → Prog
  | .node id ch => .node (φ.toFun id) (ch.map (relabel φ))

namespace SignatureIso

/-- Method form of `relabel`. -/
def map (φ : SignatureIso sig₁ sig₂) (p : Prog) : Prog := relabel φ p

end SignatureIso

theorem relabel_signature_iso_all {sig₁ sig₂ : Signature Prim} (φ : SignatureIso sig₁ sig₂) :
    ∀ fuel,
      (∀ (p : Prog) (cfg : Config) (st : Store),
        eval fuel sig₂ (relabel φ p) cfg st = eval fuel sig₁ p cfg st) ∧
      (∀ (f g : Prog) (k : Nat) (x1 x2 x3 : Int) (st : Store),
        loop2Iter fuel sig₂ (relabel φ f) (relabel φ g) k x1 x2 x3 st =
          loop2Iter fuel sig₁ f g k x1 x2 x3 st) ∧
      (∀ (f : Prog) (k : Nat) (x1 x2 x3 : Int) (st : Store),
        loopIter fuel sig₂ (relabel φ f) k x1 x2 x3 st =
          loopIter fuel sig₁ f k x1 x2 x3 st) ∧
      (∀ (f : Prog) (k : Nat) (st : Store),
        loopeIter fuel sig₂ (relabel φ f) k st = loopeIter fuel sig₁ f k st) ∧
      (∀ (f : Prog) (target seen : Nat) (cand : Int) (st : Store),
        comprSearch fuel sig₂ (relabel φ f) target seen cand st =
          comprSearch fuel sig₁ f target seen cand st) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro p cfg st
        simp [eval]
      constructor
      · intro f g k x1 x2 x3 st
        simp [loop2Iter]
      constructor
      · intro f k x1 x2 x3 st
        simp [loopIter]
      constructor
      · intro f k st
        simp [loopeIter]
      · intro f target seen cand st
        simp [comprSearch]
  | succ fuel ih =>
      rcases ih with ⟨ihEval, ihLoop2, ihLoop, ihLoope, ihCompr⟩
      constructor
      · intro p cfg st
        cases p with
        | node id ch =>
            simp [relabel]
            cases h₁ : entryAt sig₁ id with
            | none =>
                have hshape := φ.entry_shape id
                cases h₂ : entryAt sig₂ (φ.toFun id) with
                | none => simp [eval, h₁, h₂]
                | some e₂ => simp [h₁, h₂] at hshape
            | some e₁ =>
                have hshape := φ.entry_shape id
                cases h₂ : entryAt sig₂ (φ.toFun id) with
                | none => simp [h₁, h₂] at hshape
                | some e₂ =>
                    cases e₁ with
                    | mk name₁ arity₁ ho₁ prim₁ =>
                        cases e₂ with
                        | mk name₂ arity₂ ho₂ prim₂ =>
                            have hshape' :
                                EntryShapeEq
                                  ({ name := name₁, arity := arity₁, hoArity := ho₁, prim := prim₁ } :
                                    Entry Prim)
                                  ({ name := name₂, arity := arity₂, hoArity := ho₂, prim := prim₂ } :
                                    Entry Prim) := by
                              simpa [h₁, h₂] using hshape
                            have hprim : prim₂ = prim₁ := hshape'.2.2
                            cases hprim
                            cases ch with
                            | nil =>
                                cases prim₁ <;>
                                  simp [eval, h₁, h₂]
                            | cons a ch1 =>
                                cases ch1 with
                                | nil =>
                                    cases prim₁ <;>
                                      simp [eval, h₁, h₂, ihEval]
                                | cons b ch2 =>
                                    cases ch2 with
                                    | nil =>
                                        cases prim₁ <;>
                                          simp [eval, h₁, h₂, ihEval, ihCompr, ihLoope]
                                    | cons c ch3 =>
                                        cases ch3 with
                                        | nil =>
                                            cases prim₁ <;>
                                              simp [eval, h₁, h₂, ihEval, ihLoop]
                                        | cons d ch4 =>
                                            cases ch4 with
                                            | nil =>
                                                cases prim₁ <;>
                                                  simp [eval, h₁, h₂]
                                            | cons e ch5 =>
                                                cases ch5 with
                                                | nil =>
                                                    cases prim₁ <;>
                                                      simp [eval, h₁, h₂, ihEval, ihLoop2]
                                                | cons f ch6 =>
                                                    cases prim₁ <;>
                                                      simp [eval, h₁, h₂]
      constructor
      · intro f g k x1 x2 x3 st
        cases k with
        | zero => simp [loop2Iter]
        | succ k =>
            simp [loop2Iter]
            rw [ihEval f { x := x1, y := x2, z := x3 } st]
            cases hf : eval fuel sig₁ f { x := x1, y := x2, z := x3 } st with
            | none => simp
            | some rf =>
                simp
                rw [ihEval g { x := x1, y := x2, z := x3 } rf.2]
                cases hg : eval fuel sig₁ g { x := x1, y := x2, z := x3 } rf.2 with
                | none => simp
                | some rg =>
                    simp [ihLoop2 f g k rf.1 rg.1 (x3 + 1) rg.2]
      constructor
      · intro f k x1 x2 x3 st
        cases k with
        | zero => simp [loopIter]
        | succ k =>
            simp [loopIter]
            rw [ihEval f { x := x1, y := x2, z := x3 } st]
            cases hf : eval fuel sig₁ f { x := x1, y := x2, z := x3 } st with
            | none => simp
            | some rf =>
                simp [ihLoop f k rf.1 (x2 + 1) x3 rf.2]
      constructor
      · intro f k st
        cases k with
        | zero => simp [loopeIter]
        | succ k =>
            simp [loopeIter]
            rw [ihEval f { x := 0, y := 0, z := 0 } st]
            cases h : eval fuel sig₁ f { x := 0, y := 0, z := 0 } st with
            | none => simp
            | some r =>
                simp [ihLoope f k r.2]
      · intro f target seen cand st
        simp [comprSearch]
        rw [ihEval f { x := cand, y := 0, z := 0 } st]
        cases h : eval fuel sig₁ f { x := cand, y := 0, z := 0 } st with
        | none => simp
        | some r =>
            by_cases hr : r.1 ≤ 0
            · by_cases hs : seen ≥ target
              · simp [hr, hs]
              · simp [hr, hs, ihCompr f target (seen + 1) (cand + 1) r.2]
            · simp [hr, ihCompr f target seen (cand + 1) r.2]

/-- Evaluation is invariant under signature isomorphisms that preserve executable entry shape. -/
theorem eval_relabel_signature_iso {sig₁ sig₂ : Signature Prim} (φ : SignatureIso sig₁ sig₂)
    (fuel : Nat) (p : Prog) (cfg : Config) (st : Store) :
    eval fuel sig₂ (relabel φ p) cfg st = eval fuel sig₁ p cfg st :=
  (relabel_signature_iso_all φ fuel).1 p cfg st

def swap01 : Nat → Nat
  | 0 => 1
  | 1 => 0
  | n + 2 => n + 2

theorem swap01_involutive : ∀ id, swap01 (swap01 id) = id
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

def tinySigA : Signature Prim :=
  [ entry "zeroA" 0 0 .zero
  , entry "xA" 0 0 .x
  ]

def tinySigB : Signature Prim :=
  [ entry "xB" 0 0 .x
  , entry "zeroB" 0 0 .zero
  ]

def tinySwapIso : SignatureIso tinySigA tinySigB where
  toFun := swap01
  invFun := swap01
  left_inv := swap01_involutive
  right_inv := swap01_involutive
  entry_shape := by
    intro id
    cases id with
    | zero =>
        simp [entryAt, listGet?, tinySigA, tinySigB, swap01, EntryShapeEq, entry]
    | succ id =>
        cases id with
        | zero =>
            simp [entryAt, listGet?, tinySigA, tinySigB, swap01, EntryShapeEq, entry]
        | succ id =>
            simp [entryAt, listGet?, tinySigA, tinySigB, swap01, entry]

example (fuel : Nat) (cfg : Config) (st : Store) :
    eval fuel tinySigB (tinySwapIso.map (.node 1 [])) cfg st =
      eval fuel tinySigA (.node 1 []) cfg st :=
  eval_relabel_signature_iso tinySwapIso fuel (.node 1 []) cfg st

example :
    ¬ EntryShapeEq (entry "zeroA" 0 0 .zero) (entry "xA" 0 0 .x) := by
  intro h
  cases h.2.2

example (fuel : Nat) (cfg : Config) (st : Store) :
    eval fuel tinySigB (tinySwapIso.map (.node 1 [])) cfg st =
      eval fuel tinySigA (.node 1 []) cfg st := by
  fail_if_success
    rfl
  exact eval_relabel_signature_iso tinySwapIso fuel (.node 1 []) cfg st

/-! ## Table instances, in evaluator order -/

/-- `exec.sml` lines 294-295: `[zero,x,y,suc,pred,loop]`. -/
def minimalSignature : Signature Prim :=
  [ entry "zero" 0 0 .zero
  , entry "x"    0 0 .x
  , entry "y"    0 0 .y
  , entry "suc"  1 0 .suc
  , entry "pred" 1 0 .pred
  , entry "loop" 3 1 .loop
  ]

/-- `exec.sml` lines 284-288: the scalar, non-memo `org` table. -/
def orgE1Signature : Signature Prim :=
  [ entry "zero"  0 0 .zero
  , entry "one"   0 0 .one
  , entry "two"   0 0 .two
  , entry "addi"  2 0 .addi
  , entry "diff"  2 0 .diff
  , entry "mult"  2 0 .mult
  , entry "divi"  2 0 .divi
  , entry "modu"  2 0 .modu
  , entry "cond"  3 0 .cond
  , entry "loop"  3 1 .loop
  , entry "x"     0 0 .x
  , entry "y"     0 0 .y
  , entry "compr" 2 1 .compr
  , entry "loop2" 5 2 .loop2
  ]

def SignatureStoreNeutral (sig : Signature Prim) : Prop :=
  ∀ id e, entryAt sig id = some e → e.prim.storeNeutral

theorem SignatureStoreNeutral.nil : SignatureStoreNeutral [] := by
  intro id e h
  cases id <;> simp [entryAt, listGet?] at h

theorem SignatureStoreNeutral.cons {e : Entry Prim} {sig : Signature Prim}
    (he : e.prim.storeNeutral) (hsig : SignatureStoreNeutral sig) :
    SignatureStoreNeutral (e :: sig) := by
  intro id e' h
  cases id with
  | zero =>
      simp [entryAt, listGet?] at h
      rw [← h]
      exact he
  | succ id =>
      exact hsig id e' (by simpa [entryAt, listGet?] using h)

theorem orgE1Signature_storeNeutral : SignatureStoreNeutral orgE1Signature := by
  unfold orgE1Signature
  apply SignatureStoreNeutral.cons
  · simp [Prim.storeNeutral, entry]
  apply SignatureStoreNeutral.cons
  · simp [Prim.storeNeutral, entry]
  apply SignatureStoreNeutral.cons
  · simp [Prim.storeNeutral, entry]
  apply SignatureStoreNeutral.cons
  · simp [Prim.storeNeutral, entry]
  apply SignatureStoreNeutral.cons
  · simp [Prim.storeNeutral, entry]
  apply SignatureStoreNeutral.cons
  · simp [Prim.storeNeutral, entry]
  apply SignatureStoreNeutral.cons
  · simp [Prim.storeNeutral, entry]
  apply SignatureStoreNeutral.cons
  · simp [Prim.storeNeutral, entry]
  apply SignatureStoreNeutral.cons
  · simp [Prim.storeNeutral, entry]
  apply SignatureStoreNeutral.cons
  · simp [Prim.storeNeutral, entry]
  apply SignatureStoreNeutral.cons
  · simp [Prim.storeNeutral, entry]
  apply SignatureStoreNeutral.cons
  · simp [Prim.storeNeutral, entry]
  apply SignatureStoreNeutral.cons
  · simp [Prim.storeNeutral, entry]
  apply SignatureStoreNeutral.cons
  · simp [Prim.storeNeutral, entry]
  exact SignatureStoreNeutral.nil

def orgExportedCommFlag : Nat → Bool
  | 3 => true
  | 5 => true
  | _ => false

def orgExportedAssocFlag : Nat → Bool := fun _ => false

def orgExportedIdentityOf : Nat → Option Nat := fun _ => none

def orgExportedCanonicalPolicy : CanonicalPolicy orgE1Signature where
  comm := orgExportedCommFlag
  assoc := orgExportedAssocFlag
  identityOf := orgExportedIdentityOf

def orgCommPolicy : CanonicalPolicy orgE1Signature :=
  orgExportedCanonicalPolicy

theorem orgCommPolicy_matches_exported_table (id : Nat) :
    orgCommPolicy.comm id = orgExportedCommFlag id ∧
      orgCommPolicy.assoc id = orgExportedAssocFlag id ∧
      orgCommPolicy.identityOf id = orgExportedIdentityOf id := by
  simp [orgCommPolicy, orgExportedCanonicalPolicy]

theorem orgCommPolicy_sound : orgCommPolicy.Sound := by
  intro id hcomm
  cases id with
  | zero =>
      simp [orgCommPolicy, orgExportedCanonicalPolicy, orgExportedCommFlag] at hcomm
  | succ id =>
      cases id with
      | zero =>
          simp [orgCommPolicy, orgExportedCanonicalPolicy, orgExportedCommFlag] at hcomm
      | succ id =>
          cases id with
          | zero =>
              simp [orgCommPolicy, orgExportedCanonicalPolicy, orgExportedCommFlag] at hcomm
          | succ id =>
              cases id with
              | zero =>
                  exact addi_commutativeEvalLaw_of_entry
                    (sig := orgE1Signature) orgE1Signature_storeNeutral
                    (id := 3) (name := "addi") (arity := 2) (ho := 0) rfl
              | succ id =>
                  cases id with
                  | zero =>
                      simp [orgCommPolicy, orgExportedCanonicalPolicy, orgExportedCommFlag] at hcomm
                  | succ id =>
                      cases id with
                      | zero =>
                          exact mult_commutativeEvalLaw_of_entry
                            (sig := orgE1Signature) orgE1Signature_storeNeutral
                            (id := 5) (name := "mult") (arity := 2) (ho := 0) rfl
                      | succ id =>
                          simp [orgCommPolicy, orgExportedCanonicalPolicy, orgExportedCommFlag] at hcomm

theorem orgCommPolicy_allFlagLawsSound : orgCommPolicy.AllFlagLawsSound := by
  constructor
  · exact orgCommPolicy_sound
  constructor
  · intro id h
    simp [orgCommPolicy, orgExportedCanonicalPolicy, orgExportedAssocFlag] at h
  · intro id ident h
    simp [orgCommPolicy, orgExportedCanonicalPolicy, orgExportedIdentityOf] at h

theorem orgCanonicalize_sound (p : Prog) :
    Extensional orgE1Signature (canonicalize orgCommPolicy p) p :=
  canonicalize_sound orgCommPolicy orgCommPolicy_sound p

def orgX : Prog := .node 10 []
def orgZero : Prog := .node 0 []
def orgNestedAdd : Prog := .node 3 [.node 3 [orgX, orgZero], orgZero]
def orgDiffWithNestedAdd : Prog := .node 4 [.node 3 [orgX, orgZero], orgZero]

example : Prim.storeNeutral .addi := trivial

example : ¬ Prim.storeNeutral .assign := by
  intro h
  cases h

example :
    canonicalize orgCommPolicy orgNestedAdd =
      .node 3 [orgZero, .node 3 [orgZero, orgX]] := rfl

example :
    canonicalize orgCommPolicy orgDiffWithNestedAdd =
      .node 4 [.node 3 [orgZero, orgX], orgZero] := rfl

example (p : Prog) :
    Extensional orgE1Signature (canonicalize orgCommPolicy p) p := by
  fail_if_success
    rfl
  exact orgCanonicalize_sound p

/--
`array` follows `array_execv`, not `array_operl`: indices 9-13 are `x,y,array,assign,loop`.
See the file header for the upstream order mismatch.
-/
def arraySignature : Signature Prim :=
  [ entry "zero"   0 0 .zero
  , entry "one"    0 0 .one
  , entry "two"    0 0 .two
  , entry "addi"   2 0 .addi
  , entry "diff"   2 0 .diff
  , entry "mult"   2 0 .mult
  , entry "divi"   2 0 .divi
  , entry "modu"   2 0 .modu
  , entry "cond"   3 0 .cond
  , entry "x"      0 0 .x
  , entry "y"      0 0 .y
  , entry "array"  1 0 .array
  , entry "assign" 2 0 .assign
  , entry "loop"   3 1 .loop
  ]

/-- `exec.sml` lines 297-299: turing table in evaluator order.
    `kernel.sml` lines 498-499 record all turing `ho_ariv` entries as `0`, so `loope` keeps
    source-table metadata `0` even though its first child is executed as a function by `loope_f`. -/
def turingSignature : Signature Prim :=
  [ entry "zero"  0 0 .zero
  , entry "one"   0 0 .one
  , entry "two"   0 0 .two
  , entry "addi"  2 0 .addi
  , entry "diff"  2 0 .diff
  , entry "mult"  2 0 .mult
  , entry "divi"  2 0 .divi
  , entry "modu"  2 0 .modu
  , entry "cond"  3 0 .cond
  , entry "loope" 2 0 .loope
  , entry "next"  0 0 .next
  , entry "prev"  0 0 .prev
  , entry "write" 1 0 .write
  , entry "read"  0 0 .read
  ]

def turingTerm (fuel : Nat) (p : Prog) (k : Int) : Option Int :=
  termWithStore fuel turingSignature p k (Store.zero.withInputAtZero k)

def turingSeqPrefix (fuel : Nat) (p : Prog) (len : Nat) : List (Option Int) :=
  (List.range len).map (fun k => turingTerm fuel p (Int.ofNat k))

namespace Minimal
def z : Prog := .node 0 []
def X : Prog := .node 1 []
def Y : Prog := .node 2 []
def suc (a : Prog) : Prog := .node 3 [a]
def pred (a : Prog) : Prog := .node 4 [a]
def loop (f n x0 : Prog) : Prog := .node 5 [f, n, x0]
end Minimal

namespace Org
def z : Prog := .node 0 []
def o : Prog := .node 1 []
def tw : Prog := .node 2 []
def addi (a b : Prog) : Prog := .node 3 [a, b]
def diff (a b : Prog) : Prog := .node 4 [a, b]
def mult (a b : Prog) : Prog := .node 5 [a, b]
def divi (a b : Prog) : Prog := .node 6 [a, b]
def modu (a b : Prog) : Prog := .node 7 [a, b]
def cond (c t e : Prog) : Prog := .node 8 [c, t, e]
def loop (f n x0 : Prog) : Prog := .node 9 [f, n, x0]
def X : Prog := .node 10 []
def Y : Prog := .node 11 []
def compr (f n : Prog) : Prog := .node 12 [f, n]
def loop2 (f g n a b : Prog) : Prog := .node 13 [f, g, n, a, b]
end Org

namespace Array
def z : Prog := .node 0 []
def o : Prog := .node 1 []
def tw : Prog := .node 2 []
def addi (a b : Prog) : Prog := .node 3 [a, b]
def diff (a b : Prog) : Prog := .node 4 [a, b]
def mult (a b : Prog) : Prog := .node 5 [a, b]
def divi (a b : Prog) : Prog := .node 6 [a, b]
def modu (a b : Prog) : Prog := .node 7 [a, b]
def cond (c t e : Prog) : Prog := .node 8 [c, t, e]
def X : Prog := .node 9 []
def Y : Prog := .node 10 []
def array (a : Prog) : Prog := .node 11 [a]
def assign (a b : Prog) : Prog := .node 12 [a, b]
def loop (f n x0 : Prog) : Prog := .node 13 [f, n, x0]
end Array

namespace Turing
def z : Prog := .node 0 []
def o : Prog := .node 1 []
def tw : Prog := .node 2 []
def addi (a b : Prog) : Prog := .node 3 [a, b]
def diff (a b : Prog) : Prog := .node 4 [a, b]
def mult (a b : Prog) : Prog := .node 5 [a, b]
def divi (a b : Prog) : Prog := .node 6 [a, b]
def modu (a b : Prog) : Prog := .node 7 [a, b]
def cond (c t e : Prog) : Prog := .node 8 [c, t, e]
def loope (f n : Prog) : Prog := .node 9 [f, n]
def next : Prog := .node 10 []
def prev : Prog := .node 11 []
def write (a : Prog) : Prog := .node 12 [a]
def read : Prog := .node 13 []
end Turing

/-! ## Non-vacuity examples for `WellFormed` -/

example : WellFormed minimalSignature Minimal.X :=
  .node (e := entry "x" 0 0 .x) rfl rfl (by intro c hc; cases hc)

example : ¬ WellFormed minimalSignature (.node 3 []) := by
  intro h
  cases h with
  | node hentry hlen _ =>
      simp [entryAt, listGet?, minimalSignature] at hentry
      cases hentry
      simp [entry] at hlen

example : WellFormed orgE1Signature (Org.mult Org.X Org.X) :=
  recognize_sound (sig := orgE1Signature) (toks := [10, 10, 5]) (p := Org.mult Org.X Org.X) rfl

example : ¬ WellFormed orgE1Signature (.node 5 [Org.X]) := by
  intro h
  cases h with
  | node hentry hlen _ =>
      simp [entryAt, listGet?, orgE1Signature] at hentry
      cases hentry
      simp [entry] at hlen

example : WellFormed arraySignature (Array.loop (Array.addi Array.X Array.o) Array.X Array.X) :=
  .node (e := entry "loop" 3 1 .loop) rfl rfl (by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact .node (e := entry "addi" 2 0 .addi) rfl rfl (by
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact .node (e := entry "x" 0 0 .x) rfl rfl (by intro c hc; cases hc)
        · rcases List.mem_cons.mp hc' with rfl | hc''
          · exact .node (e := entry "one" 0 0 .one) rfl rfl (by intro c hc; cases hc)
          · cases hc'')
    · rcases List.mem_cons.mp hc' with rfl | hc''
      · exact .node (e := entry "x" 0 0 .x) rfl rfl (by intro c hc; cases hc)
      · rcases List.mem_cons.mp hc'' with rfl | hc'''
        · exact .node (e := entry "x" 0 0 .x) rfl rfl (by intro c hc; cases hc)
        · cases hc''')

example : ¬ WellFormed arraySignature (.node 13 [Array.X]) := by
  intro h
  cases h with
  | node hentry hlen _ =>
      simp [entryAt, listGet?, arraySignature] at hentry
      cases hentry
      simp [entry] at hlen

example : WellFormed turingSignature Turing.read :=
  recognize_sound (sig := turingSignature) (toks := [13]) (p := Turing.read) rfl

example : ¬ WellFormed turingSignature (.node 12 []) := by
  intro h
  cases h with
  | node hentry hlen _ =>
      simp [entryAt, listGet?, turingSignature] at hentry
      cases hentry
      simp [entry] at hlen

/-! ## Non-vacuity examples for the mask automaton and recognizer completeness -/

example : maskLegal minimalSignature [1, 3] := rfl

example : ¬ maskLegal minimalSignature [3] := by
  intro h
  cases h

example (toks : List Tok) :
    maskLegal minimalSignature toks ↔ (recognize minimalSignature toks).isSome := by
  fail_if_success
    rfl
  exact recognize_iff_maskLegal minimalSignature toks

example (p : Prog) (h : WellFormed minimalSignature p) :
    ∃ toks, recognize minimalSignature toks = some p := by
  fail_if_success
    exact ⟨[], rfl⟩
  exact recognize_complete h

/-! ## Validation: known scalar programs through the parametric evaluator. -/

-- minimal identity: [0,1,2,3,4,5,6,7]
#eval seqPrefix 400 minimalSignature Minimal.X 8
-- minimal doubling: [0,2,4,6,8,10,12,14]
#eval seqPrefix 400 minimalSignature (Minimal.loop (Minimal.suc Minimal.X) Minimal.X Minimal.X) 8
-- pure `org` factorial: [1,1,2,6,24,120,720]
#eval seqPrefix 600 orgE1Signature (Org.loop (Org.mult Org.X Org.Y) Org.X Org.o) 7
-- `array`: assign cell 0 from x, then read it back through the same table-driven evaluator.
#eval seqPrefix 300 arraySignature (Array.addi (Array.assign Array.z Array.X) (Array.array Array.z)) 8
-- `array` loop is at evaluator index 13: [0,2,4,6,8,10,12,14]
#eval seqPrefix 400 arraySignature (Array.loop (Array.addi Array.X Array.o) Array.X Array.X) 8
-- `turing`: the OEIS seed is placed in tape cell 0 before execution.
#eval turingSeqPrefix 100 Turing.read 8
-- `turing` line-201 write is a no-op in the source: writing 2 then reading still returns the seed.
#eval turingSeqPrefix 100 (Turing.addi (Turing.write Turing.tw) Turing.read) 5
-- Partial-operation validation: division/modulo by zero and invalid tape access return `none`.
#eval eval 20 orgE1Signature (Org.divi Org.X Org.z) (seed 5) Store.zero
#eval eval 20 orgE1Signature (Org.modu Org.X Org.z) (seed 5) Store.zero
#eval eval 5 turingSignature Turing.next (seed 0) { Store.zero with ptr := Store.size - 1 }
#eval eval 5 turingSignature Turing.read (seed 0) { tape := [], ptr := 0 }
-- Generic RPN recognizer: `x suc x x loop` parses as minimal doubling.
#eval recognize minimalSignature [1, 3, 1, 1, 5]
-- Generic RPN recognizer rejects arity underflow (`suc` without an argument).
#eval recognize minimalSignature [3]
-- Array RPN uses evaluator order: token 13 is `loop`, while token 9 is `x`.
#eval recognize arraySignature [9, 1, 3, 9, 9, 13]
#eval recognize arraySignature [13]

end Mettapedia.GSLT.LanguageDef.GauthierE1
