import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.Checker.All

/-!
# A definition by rows, compiled to the recursor of the numbers

A definition in the checker's source form (`Vectors.Checker.Definition`) is compiled to **one term of
the package**: an application of the recursor of the numbers `num-rec` to a motive and two methods.
No rule, constant or axiom is added to the package.

**The call index** (`scrutinee`): every row has the same single call index `j`, read off the
patterns by the checker's own `callIndices`. It is a number parameter matched by `zero` and
`succ k` (`Kind.number`), or the length of a vector parameter matched by `nil` and `cons a v`
(`Kind.vector`, the length a variable pattern). Recursion on a vector is recursion on its length,
the vector taken apart by the family's computation `vec A (succ k) ≡ Σ A (vec A k)`.

**The compiled function** (`compileRec`), for a telescope `x₀ … x_{j-1} (n : num) y₁ … y_q` and
result `C`:

`λ x₀ … x_{j-1} n. num-rec P z s n`, `P = λ n. Π y₁ … y_q. C`,
`z = λ y₁ … y_q. body₀`, `s = λ k ih. λ y₁ … y_q. body₁`.

Every later parameter `yᵢ` is abstracted in the motive, so a recursive call may pass any later
arguments (accumulators). The method bodies are the row bodies with:
* the pattern variables replaced by the method's variables (`cons a v` by `fst y`, `snd y` of the
  vector parameter `y`; the call index by `zero` or `succ k`);
* **the recursive call prefix** `f x₀ … x_{j-1} k` replaced by the induction hypothesis `ih`
  (`translate`): the prefix uniform, the index the predecessor. Any other occurrence of the
  function has no image, and the row is outside the class.

**Uncovered cases** (`filler`): a case without a row is filled by the function's own name applied to
the case's arguments. The compiled term then lives over one base variable, the function's name, and
an uncovered call computes to itself, stuck, as an unmatched call stays unevaluated. When the rows
cover, the compiled term is closed (`covers`, `baseOf`).

**Without a call index** (`compilePlain`): one row with variable patterns and no recursion is the
abstraction of its body.

**Exported** (`exported`): a closed compiled function is annotated with its declared type as the
recursor at zero, `num-rec (λ _. F) c (λ k x. x) zero`, which the tree's synthesis types and which
steps to `c`. A later definition uses it in its types and rows.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Definitions

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open TowerVectorsModel (numC zeroC succC ttC)
open Vectors (numRecAt)
open Vectors.Checker (Pattern Row Definition entries callIndices)

/-! ## The call index -/

/-- **The kind of the call index**: a number matched by `zero`/`succ`, or the length of the vector at
a position, matched by `nil`/`cons`. -/
inductive Kind where
  | number
  | vector (position : Nat)
  deriving DecidableEq, Repr

/-- **What a pattern variable of a row stands for** in the methods: a declared parameter, the call
index (matched by a variable), the predecessor, or the head or tail of the vector at a position. -/
inductive Slot where
  | param (i : Nat)
  | index
  | pred
  | head (i : Nat)
  | tail (i : Nat)
  deriving DecidableEq, Repr

/-- One parameter of a row: its case (`some false` for `zero`/`nil`, `some true` for `succ`/`cons`)
and its slots. -/
def slotStep (j : Nat) (kind : Kind) (acc : Option Bool × List Slot) (ip : Nat × Pattern) :
    Option (Option Bool × List Slot) :=
  if ip.1 = j then
    match kind, ip.2 with
    | .number, .zero => if acc.1.isNone then some (some false, acc.2) else none
    | .number, .succ .var => if acc.1.isNone then some (some true, acc.2 ++ [.pred]) else none
    | .vector _, .var => some (acc.1, acc.2 ++ [.index])
    | _, _ => none
  else
    match kind with
    | .vector v =>
        if ip.1 = v then
          match ip.2 with
          | .nil => if acc.1.isNone then some (some false, acc.2) else none
          | .cons .var .var =>
              if acc.1.isNone then some (some true, acc.2 ++ [.pred, .head ip.1, .tail ip.1]) else none
          | _ => none
        else
          match ip.2 with
          | .var => some (acc.1, acc.2 ++ [.param ip.1])
          | _ => none
    | .number =>
        match ip.2 with
        | .var => some (acc.1, acc.2 ++ [.param ip.1])
        | _ => none

/-- **The shape of a row**: its case and the slots of its pattern variables, left to right. -/
def rowShape (j : Nat) (kind : Kind) (r : Row) : Option (Bool × List Slot) :=
  match ((List.range r.patterns.length).zip r.patterns).foldlM (slotStep j kind) (none, []) with
  | some (some case, slots) => if slots.length = r.vars then some (case, slots) else none
  | _ => none

/-- The kind of a row's call index at `j`. -/
def rowKind (j : Nat) (r : Row) : Option Kind :=
  match r.patterns[j]? with
  | some .zero | some (.succ _) => some .number
  | some .var =>
      match r.patterns.findIdx? (fun p => match p with | .nil | .cons _ _ => true | _ => false) with
      | some v => some (.vector v)
      | none => none
  | _ => none

/-- **The call index of a definition**: every row has the same single call index and kind. -/
def scrutinee (d : Definition) : Option (Nat × Kind) :=
  match d.rows with
  | [] => none
  | r :: _ =>
      match callIndices (entries d.telescope) r.patterns with
      | [j] =>
          (rowKind j r).bind fun kind =>
            if d.rows.all (fun r' => callIndices (entries d.telescope) r'.patterns == [j] &&
                rowKind j r' == some kind) then some (j, kind) else none
      | _ => none

/-! ## Terms of the method contexts -/

/-- A variable of a context of arity `M`, by its index. -/
def varAt (M idx : Nat) : Option (Tower.Tm M) :=
  if h : idx < M then some (.var ⟨idx, h⟩) else none

/-- Apply a term to arguments, left to right. -/
def spine {n : Nat} (g : Tower.Tm n) : List (Tower.Tm n) → Tower.Tm n
  | [] => g
  | a :: as => spine (.app g a) as

/-- Abstract the newest `k` variables. -/
def lams : (k : Nat) → {n : Nat} → Tower.Tm (n + k) → Tower.Tm n
  | 0, _, t => t
  | k + 1, _, t => lams k (.lam t)

/-- Close the newest `q` entries of a telescope over a type. -/
def closeNewest : (q : Nat) → {n : Nat} → Ctx Tower.Head (n + q) → Tower.Tm (n + q) → Tower.Tm n
  | 0, _, _, T => T
  | q + 1, _, .snoc Γ A, T => closeNewest q Γ (.pi A T)

/-- Rename a term of a context of arity `n` into one with `b` older variables below it. -/
def raise (b : Nat) {n : Nat} : Ren n (b + n) := fun x => ⟨x.val, by omega⟩

/-! ## Call abstraction -/

/-- Lift an image function under a binder. -/
def liftImg {n M : Nat} (img : Fin n → Option (Tower.Tm M)) : Fin (n + 1) → Option (Tower.Tm (M + 1)) :=
  Fin.cases (some (.var 0)) (fun i => (img i).map (rename wk))

/-- **Translate a row body into a method body**: variables by their images; the recursive call prefix
`f p₀ … p_{j-1} k` by the induction hypothesis; any other occurrence of the function has no image. -/
def translate : {n M : Nat} → (Fin n → Option (Tower.Tm M)) → Option (Tower.Tm n × Tower.Tm M) →
    Tower.Tm n → Option (Tower.Tm M)
  | _, _, img, _, .var i => img i
  | _, _, _, _, .const c => some (.const c)
  | _, _, _, _, .head h => some (.head h)
  | _, _, img, call, .pi A B => do
      let A' ← translate img call A
      let B' ← translate (liftImg img) (call.map fun p => (rename wk p.1, rename wk p.2)) B
      pure (.pi A' B')
  | _, _, img, call, .sigma A B => do
      let A' ← translate img call A
      let B' ← translate (liftImg img) (call.map fun p => (rename wk p.1, rename wk p.2)) B
      pure (.sigma A' B')
  | _, _, img, call, .id A a b => do
      let A' ← translate img call A
      let a' ← translate img call a
      let b' ← translate img call b
      pure (.id A' a' b')
  | _, _, img, call, .lam body => do
      let body' ← translate (liftImg img) (call.map fun p => (rename wk p.1, rename wk p.2)) body
      pure (.lam body')
  | _, _, img, call, .app g a =>
      match call with
      | some (pre, ih) =>
          if (.app g a : Tower.Tm _) = pre then some ih
          else do
            let g' ← translate img call g
            let a' ← translate img call a
            pure (.app g' a')
      | none => do
          let g' ← translate img call g
          let a' ← translate img call a
          pure (.app g' a')
  | _, _, img, call, .pair a b => do
      let a' ← translate img call a
      let b' ← translate img call b
      pure (.pair a' b')
  | _, _, img, call, .fst p => (translate img call p).map .fst
  | _, _, img, call, .snd p => (translate img call p).map .snd
  | _, _, img, call, .refl a => (translate img call a).map .refl

/-! ## The compiled function -/

/-- **A compilation plan**: the base arity `b` (the function's own name, or nothing), the prefix
length `j`, the number `q` of later parameters, the kind of the call index. -/
structure Plan where
  b : Nat
  j : Nat
  q : Nat
  kind : Kind
  deriving DecidableEq, Repr

/-- The row variable of the slot at left-to-right position `ℓ`. -/
def slotVar (vars ℓ : Nat) : Option (Fin (vars + 1)) :=
  if h : vars - 1 - ℓ < vars + 1 then if ℓ < vars then some ⟨vars - 1 - ℓ, h⟩ else none else none

/-- The image of a slot in a method context: for `case = false` the context is the base, the prefix
and the later parameters; for `case = true` the base, the prefix, `k`, `ih` and the later parameters. -/
def slotImage (p : Plan) (case : Bool) (M : Nat) : Slot → Option (Tower.Tm M)
  | .param i =>
      if i < p.j then varAt M (p.q + (if case then 2 else 0) + (p.j - 1 - i))
      else if p.j < i ∧ i ≤ p.j + p.q then varAt M (p.j + p.q - i)
      else none
  | .index => if case then (varAt M (p.q + 1)).map succC else some zeroC
  | .pred => if case then varAt M (p.q + 1) else none
  | .head i => if p.j < i ∧ i ≤ p.j + p.q then (varAt M (p.j + p.q - i)).map .fst else none
  | .tail i => if p.j < i ∧ i ≤ p.j + p.q then (varAt M (p.j + p.q - i)).map .snd else none

/-- The images of a row's variables; the function, oldest, has none. -/
def rowImages (p : Plan) (case : Bool) (M : Nat) (r : Row) (slots : List Slot) :
    Fin (r.vars + 1) → Option (Tower.Tm M) := fun x =>
  if x.val < r.vars then (slots[r.vars - 1 - x.val]?).bind (slotImage p case M) else none

/-- **The recursive call prefix** `f p₀ … p_{j-1} k` of a successor row, in the row's variables. -/
def callPrefix (p : Plan) (r : Row) (slots : List Slot) : Option (Tower.Tm (r.vars + 1)) := do
  let fVar ← varAt (r.vars + 1) r.vars
  let prefixVars ← (List.range p.j).mapM fun i => do
    let ℓ ← slots.idxOf? (.param i)
    let x ← slotVar r.vars ℓ
    pure (.var x : Tower.Tm (r.vars + 1))
  let ℓk ← slots.idxOf? .pred
  let k ← slotVar r.vars ℓk
  pure (spine fVar (prefixVars ++ [.var k]))

/-- **The method of a row**: its body translated. A `zero`/`nil` row may not recur. -/
def method (p : Plan) (case : Bool) (r : Row) (slots : List Slot) :
    Option (Tower.Tm (if case then p.b + p.j + 2 + p.q else p.b + p.j + p.q)) :=
  match case with
  | false => translate (rowImages p false _ r slots) none r.body
  | true => do
      let pre ← callPrefix p r slots
      let ih ← varAt (p.b + p.j + 2 + p.q) p.q
      translate (rowImages p true _ r slots) (some (pre, ih)) r.body

/-- The prefix, the call index and the later parameters of a method context, as arguments. -/
def stuckArgs (p : Plan) (case : Bool) (M : Nat) : Option (List (Tower.Tm M)) := do
  let pre ← (List.range p.j).mapM fun i => varAt M (p.q + (if case then 2 else 0) + (p.j - 1 - i))
  let idx ← if case then (varAt M (p.q + 1)).map succC else some zeroC
  let suf ← (List.range p.q).mapM fun t => varAt M (p.q - 1 - t)
  pure (pre ++ [idx] ++ suf)

/-- **The filler of an uncovered case**: the function's own name (the oldest base variable) applied to
the case's arguments, stuck. Without a base there is no filler. -/
def filler (p : Plan) (case : Bool) :
    Option (Tower.Tm (if case then p.b + p.j + 2 + p.q else p.b + p.j + p.q)) :=
  match case with
  | false =>
      if 0 < p.b then do
        let f ← varAt (p.b + p.j + p.q) (p.b + p.j + p.q - 1)
        let as ← stuckArgs p false _
        pure (spine f as)
      else none
  | true =>
      if 0 < p.b then do
        let f ← varAt (p.b + p.j + 2 + p.q) (p.b + p.j + 2 + p.q - 1)
        let as ← stuckArgs p true _
        pure (spine f as)
      else none

/-- The method of a case: the row of that case, or the filler when no row has it; two rows of one
case are outside the class. -/
def caseMethod (p : Plan) (shapes : List (Row × Bool × List Slot)) (case : Bool) :
    Option (Tower.Tm (if case then p.b + p.j + 2 + p.q else p.b + p.j + p.q)) :=
  match shapes.filter (fun s => s.2.1 == case) with
  | [] => filler p case
  | [(r, _, slots)] => method p case r slots
  | _ => none

/-- **The motive** `λ n. Π y₁ … y_q. C`, over the base and the prefix. -/
def motive (p : Plan) (telescope : Ctx Tower.Head (p.j + 1 + p.q)) (result : Tower.Tm (p.j + 1 + p.q)) :
    Tower.Tm (p.b + p.j) :=
  rename (raise p.b) (.lam (closeNewest p.q telescope result))

/-- **The compiled function** `λ x₀ … x_{j-1} n. num-rec P z s n`, over the base. -/
def assemble (p : Plan) (P z s : Tower.Tm (p.b + p.j)) : Tower.Tm p.b :=
  lams p.j (.lam (numRecAt (rename wk P) (rename wk z) (rename wk s) (.var 0)))

/-- The definition's telescope and result, at arity `j + 1 + q`. -/
def splitAt (d : Definition) (j q : Nat) : Option (Ctx Tower.Head (j + 1 + q) × Tower.Tm (j + 1 + q)) :=
  if h : d.arity = j + 1 + q then some (h ▸ d.telescope, h ▸ d.result) else none

/-- **Compile a recursive definition** over a base of `b` variables. -/
def compileRec (b : Nat) (d : Definition) (j : Nat) (kind : Kind) : Option (Tower.Tm b) := do
  let q := d.arity - 1 - j
  let p : Plan := ⟨b, j, q, kind⟩
  let (telescope, result) ← splitAt d j q
  let shapes ← d.rows.mapM fun r => (rowShape j kind r).map fun s => (r, s.1, s.2)
  let z ← caseMethod p shapes false
  let s ← caseMethod p shapes true
  let z' : Tower.Tm (p.b + p.j) := lams p.q z
  let s' : Tower.Tm (p.b + p.j) := .lam (.lam (lams p.q s))
  pure (assemble p (motive p telescope result) z' s')

/-- **Compile a definition without a call index**: one row, every pattern a variable, no recursion. -/
def compilePlain (b : Nat) (d : Definition) : Option (Tower.Tm b) :=
  match d.rows with
  | [r] =>
      if r.patterns.all (· == .var) ∧ r.patterns.length = d.arity ∧ r.vars = d.arity then
        (translate (fun x : Fin (r.vars + 1) => if x.val < r.vars then varAt (b + d.arity) x.val else none)
          none r.body).map (lams d.arity)
      else none
  | _ => none

/-- **Compile a definition.** -/
def compile (b : Nat) (d : Definition) : Option (Tower.Tm b) :=
  match scrutinee d with
  | some (j, kind) => compileRec b d j kind
  | none => compilePlain b d

/-- **The row shapes**: case and slots of every row; a row without a call index has one parameter
slot per pattern. -/
def shapesOf (d : Definition) : Option (List (Row × Bool × List Slot)) :=
  match scrutinee d with
  | some (j, kind) => d.rows.mapM fun r => (rowShape j kind r).map fun s => (r, s.1, s.2)
  | none => d.rows.mapM fun r => some (r, false, (List.range r.patterns.length).map .param)

/-- **The rows cover**: both cases have a row; always, without a call index. -/
def covers (d : Definition) : Bool :=
  match scrutinee d with
  | none => true
  | some _ =>
      match shapesOf d with
      | some shapes => shapes.any (fun s => s.2.1 == false) && shapes.any (fun s => s.2.1 == true)
      | none => false

/-- **The base of the compiled function**: nothing when the rows cover, the function's own name
otherwise. -/
def baseOf (d : Definition) : Nat := if covers d then 0 else 1

/-- **The class**, a decidable predicate on the source form: the definition compiles over its base. -/
def InClass (d : Definition) : Bool := (compile (baseOf d) d).isSome

/-- **The exported definition**: the compiled function annotated with its declared type, as the
recursor of the numbers at zero. -/
def exported (F c : Tower.Tm 0) : Tower.Tm 0 :=
  numRecAt (.lam (rename wk F)) c (.lam (.lam (.var 0))) zeroC

/-- Shapes are found row by row, in order. -/
theorem mapM_shapes {f : Row → Option (Row × Bool × List Slot)} (keeps : ∀ r s, f r = some s → s.1 = r) :
    ∀ {rows : List Row} {shapes : List (Row × Bool × List Slot)}, rows.mapM f = some shapes →
      shapes.map (·.1) = rows ∧ ∀ s ∈ shapes, f s.1 = some s
  | [], shapes, h => by
      simp only [List.mapM_nil, pure, Option.some.injEq] at h
      subst h
      exact ⟨rfl, fun _ member => absurd member List.not_mem_nil⟩
  | r :: rows, shapes, h => by
      rw [List.mapM_cons] at h
      obtain ⟨s, hs, rest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨tail, htail, done⟩ := Option.bind_eq_some_iff.mp rest
      simp only [pure, Option.some.injEq] at done
      subst done
      obtain ⟨same, each⟩ := mapM_shapes keeps htail
      refine ⟨?_, ?_⟩
      · simp only [List.map_cons, same, keeps r s hs]
      · intro s' member
        rcases List.mem_cons.mp member with rfl | later
        · rw [keeps r s' hs]
          exact hs
        · exact each s' later

/-- **Every row has its shape**: the shapes list the rows, in order. -/
theorem shapesOf_rows {d : Definition} {shapes : List (Row × Bool × List Slot)}
    (found : shapesOf d = some shapes) : shapes.map (·.1) = d.rows := by
  unfold shapesOf at found
  split at found
  · exact (mapM_shapes (fun r s h => by
      obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp h
      rfl) found).1
  · exact (mapM_shapes (fun r s h => by
      cases h
      rfl) found).1

end NativeTypesOnTheStep.Computing.Definitions

#print axioms NativeTypesOnTheStep.Computing.Definitions.compile
#print axioms NativeTypesOnTheStep.Computing.Definitions.mapM_shapes
#print axioms NativeTypesOnTheStep.Computing.Definitions.shapesOf_rows

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
