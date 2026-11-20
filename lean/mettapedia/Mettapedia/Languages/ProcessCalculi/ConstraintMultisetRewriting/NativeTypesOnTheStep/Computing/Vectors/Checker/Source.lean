import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.ValueTypeRow
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCheckingBudget

/-!
# A source form for definitions over the vectors package, elaborated into rows of the step

**The source form** (`Definition`): a function name, its declared telescope (a raw context of the
package, `Ctx`, the tree's telescopes) and result type, and rows (`Row`). A row has one pattern per
parameter (`Pattern`: a variable, or a declared constructor applied to patterns: `zero`, `succ p` of
the numbers; `nil` and `cons a v` of the recursive family of vectors, `vec A zero ≡ unit` and
`vec A (succ k) ≡ Σ A (vec A k)`, the length `k` of `cons` an implicit pattern variable) and a body,
a term over the function itself (oldest) and the pattern variables, left to right. The function is
in scope at its declared type (`Definition.type`), so a recursive call is a call of a variable.

**Elaboration** (`elaborate`) is computable. A raw pass (`rawPass`, no budget) reads each parameter's
declared type and each constructor's declaration and produces:

* **the frame**: the function, then the pattern variables at their types, then, newest, **the call's
  index**: a number argument matched by a constructor, or the length of a vector argument matched
  by `nil` or `cons`;
* **what the patterns teach**: the index equals the constructor's index (`zero`, `succ k`, or the
  number pattern), told as the definition of the newest variable (`Elimination.definition`);
* **the made row**: the body, renamed into the frame, at the declared result type with the
  parameters replaced by their images in the frame (`Elaborated.args`).

The frame's formation, the made type's universe and the index's type are then certified by the
tree's executable checker within a budget (`formed?`, `level?`, `typedNum?`); failure is "not
elaborated within the budget". Each elaborated row is a firing of the step (`Elaborated.firing`):
no takes, the made row, the information told. The nil row of `append`, head's row and the literal
row come out as the rows written by hand for the audit, with the function added as the oldest
variable (`Controls`); the cons row binds its implicit length after `m`, the hand-written one before.

**The class elaborated** (`rawPass` returns `none` outside it): at most one call index per row;
`cons` with variable sub-patterns; vector parameters whose length is a parameter matched by a
variable; no frame variable's type mentions the call index.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Vectors.Checker

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull (Make State Firing)
open TowerVectorsModel (numC zeroC succC ttC vecC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1 pkg D numType)

/-! ## The source form -/

/-- **A pattern**: a variable, or a declared constructor applied to patterns. -/
inductive Pattern where
  | var
  | zero
  | succ (inner : Pattern)
  | nil
  | cons (head tail : Pattern)
  deriving DecidableEq, Repr

/-- The number of pattern variables a pattern binds; `cons` binds its implicit length too. -/
def Pattern.vars : Pattern → Nat
  | .var => 1
  | .zero => 0
  | .succ inner => inner.vars
  | .nil => 0
  | .cons head tail => 1 + head.vars + tail.vars

/-- **A row**: one pattern per parameter, and a body over the function (variable `vars`) and the
pattern variables, left to right (the last one is variable `0`). -/
structure Row where
  patterns : List Pattern
  vars : Nat
  body : Tower.Tm (vars + 1)

/-- **A definition**: a name, the declared telescope and result type, and the rows. -/
structure Definition where
  name : String
  arity : Nat
  telescope : Ctx Tower.Head arity
  result : Tower.Tm arity
  rows : List Row

/-- The dependent function type of a telescope and a result type. -/
def closePi : {n : Nat} → Ctx Tower.Head n → Tower.Tm n → Tower.Tm 0
  | _, .nil, result => result
  | _, .snoc Γ A, result => closePi Γ (.pi A result)

/-- **The declared type of the function.** -/
def Definition.type (d : Definition) : Tower.Tm 0 := closePi d.telescope d.result

/-- The entries of a telescope, oldest first, each at its position. -/
def entries : {n : Nat} → Ctx Tower.Head n → List (Σ i : Nat, Tower.Tm i)
  | _, .nil => []
  | _, .snoc Γ A => entries Γ ++ [⟨_, A⟩]

/-! ## The raw pass -/

/-- **The raw state of elaboration**: the frame so far, the images of the parameters read so far
(newest first; the call index has none), the frame variables of the pattern variables so far (newest
first; the call index's variable has none), and the call index's value once a pattern teaches it. -/
structure Acc where
  arity : Nat
  frame : Ctx Tower.Head arity
  images : List (Option (Tower.Tm arity))
  sources : List (Option (Fin arity))
  value : Option (Tower.Tm arity)
  deriving DecidableEq

/-- The state before the first parameter: the function at its declared type. -/
def start (d : Definition) : Acc := ⟨1, .snoc .nil d.type, [], [], none⟩

/-- Bind a pattern variable of a type. -/
abbrev Acc.bind (acc : Acc) (type : Tower.Tm acc.arity) : Acc where
  arity := acc.arity + 1
  frame := .snoc acc.frame type
  images := acc.images.map (Option.map (rename wk))
  sources := some ⟨0, Nat.zero_lt_succ _⟩ :: acc.sources.map (Option.map Fin.succ)
  value := acc.value.map (rename wk)

/-- Bind a parameter matched by a variable: a pattern variable, and the parameter's image. -/
abbrev Acc.bindParam (acc : Acc) (type : Tower.Tm acc.arity) : Acc where
  arity := acc.arity + 1
  frame := .snoc acc.frame type
  images := some (.var ⟨0, Nat.zero_lt_succ _⟩) :: acc.images.map (Option.map (rename wk))
  sources := some ⟨0, Nat.zero_lt_succ _⟩ :: acc.sources.map (Option.map Fin.succ)
  value := acc.value.map (rename wk)

/-- Whether a term mentions a variable the predicate marks. -/
def mentions : {k : Nat} → (Fin k → Bool) → Tower.Tm k → Bool
  | _, p, .var i => p i
  | _, _, .const _ => false
  | _, _, .head _ => false
  | _, p, .pi A B => mentions p A || mentions (Fin.cases (motive := fun _ => Bool) false p) B
  | _, p, .sigma A B => mentions p A || mentions (Fin.cases (motive := fun _ => Bool) false p) B
  | _, p, .id A a b => mentions p A || mentions p a || mentions p b
  | _, p, .lam body => mentions (Fin.cases (motive := fun _ => Bool) false p) body
  | _, p, .app f a => mentions p f || mentions p a
  | _, p, .pair a b => mentions p a || mentions p b
  | _, p, .fst t => mentions p t
  | _, p, .snd t => mentions p t
  | _, p, .refl t => mentions p t

/-- A declared type, read in the frame so far: its parameters replaced by their images. It fails when
the type mentions the call index, whose variable comes last. -/
def instantiate? (acc : Acc) {i : Nat} (t : Tower.Tm i) : Option (Tower.Tm acc.arity) :=
  if acc.images.length = i ∧ mentions (fun x => (acc.images.getD x.val none).isNone) t = false then
    some (subst (fun x => (acc.images.getD x.val none).getD zeroC) t)
  else none

/-- A vector type whose length is a variable: `vec A x`. -/
def vecIndexVar? {i : Nat} : Tower.Tm i → Option (Tower.Tm i × Fin i)
  | .app (.app (.const c) A) (.var x) => if c = TowerVectorsModel.vec then some (A, x) else none
  | _ => none

/-- The positions of the parameters a row's patterns make call indices. -/
def callIndices : List (Σ i : Nat, Tower.Tm i) → List Pattern → List Nat
  | entry :: rest, p :: ps =>
      (match p with
        | .zero | .succ _ => [entry.1]
        | .nil | .cons _ _ =>
            (match vecIndexVar? entry.2 with
              | some (_, x) => [entry.1 - 1 - x.val]
              | none => [])
        | .var => []) ++ callIndices rest ps
  | _, _ => []

/-- Bind the implicit length `k`, the head `a : A` and the tail `v : vec A k` of a `cons` pattern; the
vector parameter's image is `pair a v`, and the match teaches `succ k`. -/
def consBind (acc : Acc) (A : Tower.Tm acc.arity) : Acc where
  arity := acc.arity + 3
  frame := .snoc (.snoc (.snoc acc.frame numC) (rename wk A))
    (vecC (rename wk (rename wk A)) (.var ⟨1, by omega⟩))
  images := some (.pair (.var ⟨1, by omega⟩) (.var ⟨0, by omega⟩)) ::
    acc.images.map (Option.map fun t => rename wk (rename wk (rename wk t)))
  sources := some ⟨0, by omega⟩ :: some ⟨1, by omega⟩ :: some ⟨2, by omega⟩ ::
    acc.sources.map (Option.map fun j => j.succ.succ.succ)
  value := some (succC (.var ⟨2, by omega⟩))

/-- A number pattern: its variables bound at `num`, and its value. -/
def numPattern : (acc : Acc) → Pattern → Option ((acc' : Acc) × Tower.Tm acc'.arity)
  | acc, .zero => some ⟨acc, zeroC⟩
  | acc, .var => some ⟨acc.bind numC, .var ⟨0, Nat.zero_lt_succ _⟩⟩
  | acc, .succ inner => (numPattern acc inner).map fun r => ⟨r.1, succC r.2⟩
  | _, _ => none

/-- **One parameter and its pattern.** -/
def step (index : Option Nat) (acc : Acc) (entry : Σ i : Nat, Tower.Tm i) (p : Pattern) : Option Acc :=
  match p with
  | .var =>
      if index = some entry.1 then
        if instantiate? acc entry.2 = some numC then
          some { acc with images := none :: acc.images, sources := none :: acc.sources }
        else none
      else (instantiate? acc entry.2).map acc.bindParam
  | .zero | .succ _ =>
      if index = some entry.1 ∧ instantiate? acc entry.2 = some numC ∧ acc.value = none then
        (numPattern acc p).map fun r => { r.1 with images := none :: r.1.images, value := some r.2 }
      else none
  | .nil =>
      match vecIndexVar? entry.2 with
      | some (_, x) =>
          if index = some (entry.1 - 1 - x.val) ∧ acc.value = none then
            some { acc with images := some ttC :: acc.images, value := some zeroC }
          else none
      | none => none
  | .cons .var .var =>
      match vecIndexVar? entry.2 with
      | some (A, x) =>
          if index = some (entry.1 - 1 - x.val) ∧ acc.value = none then
            (instantiate? acc A).map (consBind acc)
          else none
      | none => none
  | .cons _ _ => none

/-- **The raw pass** over the parameters, with the call index read off the patterns. -/
def rawPass (d : Definition) (r : Row) : Option Acc :=
  let es := entries d.telescope
  let pass (index : Option Nat) : Option Acc :=
    ((es.zip r.patterns).foldlM (fun acc e => step index acc e.1 e.2) (start d)).bind fun acc =>
      if acc.images.length = d.arity ∧ acc.sources.length = r.vars ∧ index.isSome = acc.value.isSome then
        some acc
      else none
  if es.length = r.patterns.length then
    match callIndices es r.patterns with
    | [] => pass none
    | [i] => pass (some i)
    | _ => none
  else none

/-! ## Certification by the executable checker -/

/-- The frame's formation, certified within a budget. -/
def formed? (fuel : Nat) {a : Nat} (Γ : Ctx Tower.Head a) : Option (PLift (CtxFormed pkg Γ)) :=
  (ExecutableChecking.formContext vecS.R vecChoices (vecReducer level1) fuel Γ).bind fun c =>
    some ⟨ExecutableChecking.ContextAlgorithm.sound (S := vecS) (TowerVectorsModel.facts level1)
      (TowerVectorsModel.roots level1) (TowerVectorsModel.heads level1) (TowerVectorsModel.algebra level1)
      (vecDeclared level1) c.down⟩

/-- A type's universe, certified within a budget: the type is formed at it. -/
def level? (fuel : Nat) (Γ : Context pkg) (T : Tower.Tm Γ.arity) :
    Option {level : Tower.Head // pkg.isUniverse level ∧ Typed pkg Γ.raw T (.head level)} :=
  (ExecutableChecking.synth vecS.R vecChoices (vecReducer level1) fuel Γ.raw T).bind fun s =>
    (ExecutableChecking.asUniverse vecS.R (vecReducer level1) fuel s.1).bind fun l =>
      have typed : Typed pkg Γ.raw T s.1 :=
        CheckingAlgorithm.sound (S := vecS) (TowerVectorsModel.facts level1) (TowerVectorsModel.roots level1)
          (TowerVectorsModel.heads level1) (TowerVectorsModel.algebra level1) (vecDeclared level1) s.2.down
          Γ.formed
      some ⟨l.val, l.property.1, Typed.convType typed
        (Reduces.typeEq (S := vecS) (TowerVectorsModel.facts level1) (TowerVectorsModel.roots level1)
          (TowerVectorsModel.heads level1) Γ.formed l.property.2 (Typed.isType (S := vecS) typed Γ.formed))⟩

/-- A number, certified within a budget. -/
def typedNum? (fuel : Nat) (Γ : Context pkg) (t : Tower.Tm Γ.arity) :
    Option (PLift (Typed pkg Γ.raw t numC)) :=
  (ExecutableChecking.check vecS.R vecChoices (vecReducer level1) fuel Γ.raw t numC).bind fun c =>
    some ⟨CheckingAlgorithm.sound (S := vecS) (TowerVectorsModel.facts level1) (TowerVectorsModel.roots level1)
      (TowerVectorsModel.heads level1) (TowerVectorsModel.algebra level1) (vecDeclared level1) c.down
      Γ.formed (numType Γ).isType⟩

/-! ## Elaborated rows -/

/-- **An elaborated row**: its frame, what its patterns teach, its made row, and the images of the
declared parameters in the frame. -/
structure Elaborated (n : Nat) where
  frame : Context pkg
  tells : EquationStore (TotalTerm frame)
  made : Make frame
  args : Sub Tower.Head n frame.arity

/-- The made row at the declared result type read through the images. -/
def madeAt {n : Nat} {Γ : Context pkg} (args : Sub Tower.Head n Γ.arity) (result : Tower.Tm n)
    (code : Tower.Tm Γ.arity)
    (level : {level : Tower.Head // pkg.isUniverse level ∧ Typed pkg Γ.raw (subst args result) (.head level)}) :
    Make Γ :=
  ⟨⟨subst args result, level.val, level.property.1, level.property.2⟩, code⟩

/-- The frame before the call index: the function and the pattern variables. -/
abbrev prefixOf (acc : Acc) (formed : CtxFormed pkg acc.frame) : Context pkg := ⟨acc.arity, acc.frame, formed⟩

/-- Without a call index: the parameters' images in the frame. -/
def plainArgs (d : Definition) (acc : Acc) : Sub Tower.Head d.arity acc.arity :=
  fun x => (acc.images.getD x.val none).getD zeroC

/-- Without a call index: the body's variables in the frame (the function is the oldest). -/
def plainRen (r : Row) (acc : Acc) (pos : 0 < acc.arity) : Ren (r.vars + 1) acc.arity := fun x =>
  if x.val < r.vars then (acc.sources.getD x.val none).getD ⟨acc.arity - 1, Nat.sub_lt pos Nat.one_pos⟩
  else ⟨acc.arity - 1, Nat.sub_lt pos Nat.one_pos⟩

/-- With a call index, newest: the parameters' images in the frame. -/
def indexArgs (d : Definition) (acc : Acc) : Sub Tower.Head d.arity (acc.arity + 1) := fun x =>
  match acc.images.getD x.val none with
  | some t => rename wk t
  | none => .var ⟨0, Nat.zero_lt_succ _⟩

/-- With a call index, newest: the body's variables in the frame. -/
def indexRen (r : Row) (acc : Acc) : Ren (r.vars + 1) (acc.arity + 1) := fun x =>
  if x.val < r.vars then
    match acc.sources.getD x.val none with
    | some j => j.succ
    | none => ⟨0, Nat.zero_lt_succ _⟩
  else ⟨acc.arity, Nat.lt_succ_self _⟩

/-- **Elaboration of a row**, within a budget for the certificates. -/
def elaborate (fuel : Nat) (d : Definition) (r : Row) : Option (Elaborated d.arity) :=
  (rawPass d r).bind fun acc =>
    if pos : 0 < acc.arity then
      (formed? fuel acc.frame).bind fun formed =>
        match acc.value with
        | none =>
            (level? fuel (prefixOf acc formed.down) (subst (plainArgs d acc) d.result)).bind fun l =>
              some ⟨prefixOf acc formed.down, [],
                madeAt (Γ := prefixOf acc formed.down) (plainArgs d acc) d.result
                  (rename (plainRen r acc pos) r.body) l, plainArgs d acc⟩
        | some v =>
            (typedNum? fuel (prefixOf acc formed.down) v).bind fun tv =>
              (level? fuel (extend (prefixOf acc formed.down) (numType _)) (subst (indexArgs d acc) d.result)).bind
                fun l =>
                  some ⟨extend (prefixOf acc formed.down) (numType _),
                    [Elimination.definition (prefixOf acc formed.down) ⟨v, tv.down⟩],
                    madeAt (Γ := extend (prefixOf acc formed.down) (numType _)) (indexArgs d acc) d.result
                      (rename (indexRen r acc) r.body) l, indexArgs d acc⟩
    else none

/-! ## The firing of an elaborated row -/

namespace Elaborated

variable {n : Nat} (e : Elaborated n)

/-- The state of the call: the frame, no knowledge, no present rows. -/
def state : State pkg Nat := ⟨e.frame, [], ∅, fun _ => ⟨numType _, ⟨zeroC, D.zero_typed⟩⟩⟩

/-- **The row as a firing of the step**: told what its patterns teach, it makes the body at the
call's declared type. -/
def firing : Firing vecS.levels e.state where
  helpers := .nil _
  taken := []
  read := []
  takes := []
  reads := []
  makes := [(0, e.made)]
  tells := e.tells
  guards := []
  queries := []

/-- The information of the firing is what the patterns teach. -/
theorem firing_information : e.firing.information = e.tells := rfl

end Elaborated

/-- **Inversion, without a call index**: the frame is the raw pass's, nothing is told, and the made
row is the renamed body at the declared result type. -/
theorem elaborate_plain {fuel : Nat} {d : Definition} {r : Row} {e : Elaborated d.arity} {acc : Acc}
    (elaborated : elaborate fuel d r = some e) (raw : rawPass d r = some acc) (value : acc.value = none) :
    ∃ (pos : 0 < acc.arity) (formed : CtxFormed pkg acc.frame)
      (l : {level : Tower.Head // pkg.isUniverse level ∧
        Typed pkg acc.frame (subst (plainArgs d acc) d.result) (.head level)}),
      e = ⟨prefixOf acc formed, [], madeAt (Γ := prefixOf acc formed) (plainArgs d acc) d.result
        (rename (plainRen r acc pos) r.body) l, plainArgs d acc⟩ := by
  unfold elaborate at elaborated
  rw [raw, Option.bind_some] at elaborated
  split at elaborated
  · rename_i pos
    obtain ⟨formed, -, rest⟩ := Option.bind_eq_some_iff.mp elaborated
    split at rest
    · obtain ⟨l, -, rest⟩ := Option.bind_eq_some_iff.mp rest
      cases rest
      exact ⟨pos, formed.down, l, rfl⟩
    · rename_i v hv
      rw [value] at hv
      cases hv
  · cases elaborated

/-- **Inversion, with a call index**: the frame is the raw pass's with the index newest, the match
teaches the index's value, and the made row is the renamed body at the declared result type. -/
theorem elaborate_index {fuel : Nat} {d : Definition} {r : Row} {e : Elaborated d.arity} {acc : Acc}
    {v : Tower.Tm acc.arity} (elaborated : elaborate fuel d r = some e) (raw : rawPass d r = some acc)
    (value : acc.value = some v) :
    ∃ (formed : CtxFormed pkg acc.frame) (tv : Typed pkg acc.frame v TowerVectorsModel.numC)
      (l : {level : Tower.Head // pkg.isUniverse level ∧
        Typed pkg (extend (prefixOf acc formed) (numType _)).raw (subst (indexArgs d acc) d.result) (.head level)}),
      e = ⟨extend (prefixOf acc formed) (numType _), [Elimination.definition (prefixOf acc formed) ⟨v, tv⟩],
        madeAt (Γ := extend (prefixOf acc formed) (numType _)) (indexArgs d acc) d.result
          (rename (indexRen r acc) r.body) l, indexArgs d acc⟩ := by
  unfold elaborate at elaborated
  rw [raw, Option.bind_some] at elaborated
  split at elaborated
  · obtain ⟨formed, -, rest⟩ := Option.bind_eq_some_iff.mp elaborated
    split at rest
    · rename_i hv
      rw [value] at hv
      cases hv
    · rename_i v' hv
      rw [value] at hv
      obtain rfl := Option.some.inj hv
      obtain ⟨tv, -, rest⟩ := Option.bind_eq_some_iff.mp rest
      obtain ⟨l, -, rest⟩ := Option.bind_eq_some_iff.mp rest
      cases rest
      exact ⟨formed.down, tv.down, l, rfl⟩
  · cases elaborated

/-- **The made row is at the declared result type read through the images.** -/
theorem made_type_code {d : Definition} {r : Row} {fuel : Nat} {e : Elaborated d.arity}
    (elaborated : elaborate fuel d r = some e) : e.made.type.code = subst e.args d.result := by
  unfold elaborate at elaborated
  obtain ⟨acc, -, rest⟩ := Option.bind_eq_some_iff.mp elaborated
  split at rest
  · obtain ⟨formed, -, rest⟩ := Option.bind_eq_some_iff.mp rest
    split at rest
    · obtain ⟨l, -, rest⟩ := Option.bind_eq_some_iff.mp rest
      cases rest
      rfl
    · obtain ⟨tv, -, rest⟩ := Option.bind_eq_some_iff.mp rest
      obtain ⟨l, -, rest⟩ := Option.bind_eq_some_iff.mp rest
      cases rest
      rfl
  · cases rest

end NativeTypesOnTheStep.Computing.Vectors.Checker

#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.rawPass
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.formed?
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.level?
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.typedNum?
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.elaborate
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.Elaborated.firing
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.Elaborated.firing_information
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.elaborate_plain
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.elaborate_index
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.made_type_code

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
