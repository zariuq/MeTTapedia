import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeViewsControls

/-!
# Shape keys of the type-stamp store

The store answers a node's typing from a table of transitions keyed by the
node's head, the question and one key per child (`type_stamps_shape`). The
C keys a symbol child by the symbol itself, a literal child by its grounded
kind's typing, and an expression child by its typing state. This module
states when such a table answers as inference does, in the
question-qualified model of `NativeTypeViews`, and refutes the literal
rule.

**When a key is enough** (`Adequate`): equal keys give equal child
observations (kind, inferred types and tuple-part types), and the head's
classification and the node's own annotations read the children only
through their keys. Then equal keys give equal descriptors, hence the same
source answers (`key_factor`). A table each of whose entries was computed by
the source traversal on some node with its key (`Valid`, kept by `record`
whatever the order of recording) answers every node of an adequate head as
the source traversal does (`read_eq_source`): the store's answers are
inference, independent of the order in which nodes were typed.

**The literal rule is refuted.** HE's native-handle classification reads a
string kind itself: `(NativeHandle "mork-space" 0)` is a `MorkSpace`, while
`(NativeHandle "other" 0)` types `(H String Number)` under
`(: NativeHandle H)` (`string_handle_answers`). Both have the C's key, a
`String` literal and a `Number` literal (`string_handle_same_key`), so no
computation from that key gives both answers
(`string_handle_no_key_factorization`), and the table that recorded the
first answers `MorkSpace` for the second (`string_handle_table_wrong`). The
executable probe: with `CETTA_TYPE_STAMPS=0`,
`(change-state! (new-state (NativeHandle "mork-space" 0)) (NativeHandle "other" 0))`
raises `BadArgType 2 MorkSpace (H String Number)`; with stamps on it is
accepted.

**The corrected rule is adequate.** For every head other than
`NativeHandle`, in a space whose annotations have symbol subjects, the key
(a symbol by identity, a literal by its grounded type) determines every
observation (`fixed_key_adequate`), so its table is exact
(`fixed_table_exact`); a native handle must key its literal kind by value or
read no shape.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.StampKeys

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE
open NativeTypeViews

/-! ## Adequate keys -/

section Generic

variable {Value TypeAtom Bind Kind K : Type}

/-- **A child key is adequate for a head** when equal keys give equal child
observations and the head's classification and annotations read the
children only through their keys. -/
structure Adequate (reads : Reads Value TypeAtom Kind) (key : Value → K) (head : Value) : Prop where
  view : ∀ v w, key v = key w → childView reads v = childView reads w
  classify : ∀ vs ws, vs.map key = ws.map key → reads.classify head vs = reads.classify head ws
  annotations : ∀ vs ws, vs.map key = ws.map key → reads.annotations head vs = reads.annotations head ws

theorem map_congr_of_key {α β γ : Type} (key : α → γ) (g : α → β)
    (h : ∀ v w, key v = key w → g v = g w) :
    ∀ vs ws : List α, vs.map key = ws.map key → vs.map g = ws.map g
  | [], [], _ => rfl
  | [], _ :: _, hk => by simp at hk
  | _ :: _, [], hk => by simp at hk
  | v :: vs, w :: ws, hk => by
      simp only [List.map_cons, List.cons.injEq] at hk ⊢
      exact ⟨h v w hk.1, map_congr_of_key key g h vs ws hk.2⟩

/-- **Equal keys give equal descriptors.** -/
theorem descriptor_of_keys (reads : Reads Value TypeAtom Kind) (key : Value → K) (head : Value)
    (adequate : Adequate reads key head) (question : Bool) {vs ws : List Value}
    (same : vs.map key = ws.map key) :
    descriptor reads question head vs = descriptor reads question head ws := by
  simp only [descriptor, adequate.classify vs ws same, adequate.annotations vs ws same,
    map_congr_of_key key (childView reads) adequate.view vs ws same]

/-- **Equal keys give the same source answers.** -/
theorem key_factor (ops : Ops TypeAtom Bind Kind) (reads : Reads Value TypeAtom Kind) (key : Value → K)
    (head : Value) (adequate : Adequate reads key head) (question : Bool) {vs ws : List Value}
    (same : vs.map key = ws.map key) :
    sourceNode ops reads question head vs = sourceNode ops reads question head ws :=
  equal_descriptors_equal_results ops reads (descriptor_of_keys reads key head adequate question same)

/-- A transition table: answers keyed by the question, the head and the
children's keys. -/
abbrev Table (Value TypeAtom K : Type) := List ((Bool × Value × List K) × List TypeAtom)

/-- The first entry under a key. -/
def lookup [DecidableEq Value] [DecidableEq K] (k : Bool × Value × List K) :
    Table Value TypeAtom K → Option (List TypeAtom)
  | [] => none
  | (k', answer) :: rest => if k = k' then some answer else lookup k rest

/-- Every entry was computed by the source traversal on some node with its
key. -/
def Valid (ops : Ops TypeAtom Bind Kind) (reads : Reads Value TypeAtom Kind) (key : Value → K)
    (table : Table Value TypeAtom K) : Prop :=
  ∀ q head ks answer, ((q, head, ks), answer) ∈ table →
    ∃ vs, vs.map key = ks ∧ answer = sourceNode ops reads q head vs

/-- Record the source answer of a node under its key. -/
def record (ops : Ops TypeAtom Bind Kind) (reads : Reads Value TypeAtom Kind) (key : Value → K)
    (q : Bool) (head : Value) (vs : List Value) (table : Table Value TypeAtom K) :
    Table Value TypeAtom K :=
  ((q, head, vs.map key), sourceNode ops reads q head vs) :: table

/-- The store's answer for a node: the table's entry under its key, or the
source traversal on a miss. -/
def read [DecidableEq Value] [DecidableEq K] (ops : Ops TypeAtom Bind Kind)
    (reads : Reads Value TypeAtom Kind) (key : Value → K) (q : Bool) (head : Value) (vs : List Value)
    (table : Table Value TypeAtom K) : List TypeAtom :=
  (lookup (q, head, vs.map key) table).getD (sourceNode ops reads q head vs)

theorem valid_nil (ops : Ops TypeAtom Bind Kind) (reads : Reads Value TypeAtom Kind) (key : Value → K) :
    Valid ops reads key ([] : Table Value TypeAtom K) := by
  intro _ _ _ _ h
  cases h

/-- **Recording keeps the table valid**, in any order. -/
theorem valid_record (ops : Ops TypeAtom Bind Kind) (reads : Reads Value TypeAtom Kind) (key : Value → K)
    (q : Bool) (head : Value) (vs : List Value) {table : Table Value TypeAtom K}
    (valid : Valid ops reads key table) : Valid ops reads key (record ops reads key q head vs table) := by
  intro q' head' ks answer h
  rcases List.mem_cons.mp h with h | h
  · simp only [Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
    exact ⟨vs, rfl, rfl⟩
  · exact valid q' head' ks answer h

theorem lookup_mem [DecidableEq Value] [DecidableEq K] {k : Bool × Value × List K} :
    ∀ {table : Table Value TypeAtom K} {answer : List TypeAtom},
      lookup k table = some answer → (k, answer) ∈ table
  | [], _, h => by cases h
  | (k', a) :: rest, answer, h => by
      unfold lookup at h
      split_ifs at h with hk
      · cases h
        subst hk
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (lookup_mem h)

/-- **A valid table answers as inference** at every node of a head whose
key is adequate, whatever nodes were recorded and in whatever order. -/
theorem read_eq_source [DecidableEq Value] [DecidableEq K] (ops : Ops TypeAtom Bind Kind)
    (reads : Reads Value TypeAtom Kind) (key : Value → K) (head : Value)
    (adequate : Adequate reads key head) (q : Bool) (vs : List Value)
    {table : Table Value TypeAtom K} (valid : Valid ops reads key table) :
    read ops reads key q head vs table = sourceNode ops reads q head vs := by
  unfold read
  cases hit : lookup (q, head, vs.map key) table with
  | none => rfl
  | some answer =>
      obtain ⟨ws, hws, rfl⟩ := valid q head _ answer (lookup_mem hit)
      exact key_factor ops reads key head adequate q hws

end Generic

/-! ## The C's key on HE's observations -/

/-- A child's part of the C's shape key: a symbol itself, a literal's
grounded typing, an expression's typing state, nothing for a variable. -/
inductive CChild where
  | symbol (s : String)
  | literal (type_ : Atom)
  | typed (types : List Atom)
  | unkeyed
  deriving DecidableEq

/-- The C's key of a child, an expression read through a typing state. -/
def cKey (state : Atom → List Atom) : Atom → CChild
  | .symbol s => .symbol s
  | .grounded g => .literal (getGroundedType g)
  | .expression xs => .typed (state (.expression xs))
  | .var _ => .unkeyed

open NativeTypeViewsControls (annotation zero ops reads classify)

/-- `(: NativeHandle H)`. -/
def handleSpace : Space := Space.ofList [annotation "NativeHandle" (Atom.symbol "H")]

/-- The typing states of the native fixture: HE's inferred view. -/
def state (value : Atom) : List Atom := (reads handleSpace).inferred value

/-- A string literal. -/
def text (s : String) : Atom := .grounded (.string s)

/-- **Both handles have the C's key.** -/
theorem string_handle_same_key :
    [text "mork-space", zero].map (cKey state) = [text "other", zero].map (cKey state) := rfl

/-- **Their typings differ**: a `MorkSpace`, and the tuple `(H String Number)`. -/
theorem string_handle_answers :
    sourceNode (ops handleSpace) (reads handleSpace) true (Atom.symbol "NativeHandle") [text "mork-space", zero] =
      [Atom.symbol "MorkSpace"] ∧
    sourceNode (ops handleSpace) (reads handleSpace) true (Atom.symbol "NativeHandle") [text "other", zero] =
      [Atom.expression [Atom.symbol "H", Atom.symbol "String", Atom.symbol "Number"]] := by
  cbv

/-- **No computation from the C's key answers both handles.** -/
theorem string_handle_no_key_factorization :
    ¬ ∃ compute : List CChild → List Atom, ∀ kind,
      compute ([kind, zero].map (cKey state)) =
        sourceNode (ops handleSpace) (reads handleSpace) true (Atom.symbol "NativeHandle") [kind, zero] := by
  rintro ⟨compute, correct⟩
  have left := correct (text "mork-space")
  have right := correct (text "other")
  rw [string_handle_same_key, string_handle_answers.1] at left
  rw [string_handle_answers.2] at right
  rw [left] at right
  cases right

/-- **The table that recorded the first handle answers the second wrongly**:
`MorkSpace`, where inference gives `(H String Number)`. -/
theorem string_handle_table_wrong :
    read (ops handleSpace) (reads handleSpace) (cKey state) true (Atom.symbol "NativeHandle") [text "other", zero]
        (record (ops handleSpace) (reads handleSpace) (cKey state) true (Atom.symbol "NativeHandle")
          [text "mork-space", zero] []) = [Atom.symbol "MorkSpace"] ∧
      [Atom.symbol "MorkSpace"] ≠
        sourceNode (ops handleSpace) (reads handleSpace) true (Atom.symbol "NativeHandle") [text "other", zero] := by
  constructor
  · unfold read record
    rw [show [text "other", zero].map (cKey state) = [text "mork-space", zero].map (cKey state) from rfl]
    simp only [lookup, if_pos, Option.getD_some, string_handle_answers.1]
  · rw [string_handle_answers.2]
    decide

/-- The record is valid: the refutation is not a corrupted table. -/
theorem string_handle_table_valid :
    Valid (ops handleSpace) (reads handleSpace) (cKey state)
      (record (ops handleSpace) (reads handleSpace) (cKey state) true (Atom.symbol "NativeHandle")
        [text "mork-space", zero] []) :=
  valid_record _ _ _ _ _ _ (valid_nil _ _ _)

/-! ## The corrected key -/

/-- Annotations with symbol subjects only. -/
def SymbolSubjects (space : Space) : Prop :=
  ∀ a ∈ space.atoms, ∀ subject type_, a = .expression [.symbol ":", subject, type_] →
    ∃ s, subject = .symbol s

theorem annotations_expression {space : Space} (h : SymbolSubjects space) (xs : List Atom) :
    getAnnotatedTypes space (.expression xs) = [] := by
  unfold getAnnotatedTypes
  rw [List.filterMap_eq_nil_iff]
  intro a ha
  split
  · next subject type_ =>
      obtain ⟨s, rfl⟩ := h _ ha subject type_ rfl
      rfl
  · rfl

/-- **The corrected key is adequate** for every head other than
`NativeHandle`, in a space whose annotations have symbol subjects, on
expression children whose typing state determines their observations. -/
theorem fixed_key_adequate (space : Space) (hs : SymbolSubjects space) (st : Atom → List Atom)
    (hexpr : ∀ xs ys, st (.expression xs) = st (.expression ys) →
      childView (reads space) (.expression xs) = childView (reads space) (.expression ys))
    (head : Atom) (hh : head ≠ Atom.symbol "NativeHandle") :
    Adequate (reads space) (cKey st) head where
  view v w hk := by
    cases v <;> cases w <;> simp only [cKey, reduceCtorEq] at hk
    · cases hk
      rfl
    · rfl
    · rename_i g g'
      simp only [CChild.literal.injEq] at hk
      simp only [childView, reads, NativeTypeViews.Ops.close, ops, getMetaType, getAtomTypes, hk]
    · rename_i xs ys
      simp only [CChild.typed.injEq] at hk
      exact hexpr xs ys hk
  classify vs ws _ := by
    have hh' : head ≠ NativeTypeViewsControls.sym "NativeHandle" := hh
    simp [reads, classify, hh']
  annotations vs ws _ := by
    change getAnnotatedTypes space (Atom.expression (head :: vs)) =
      getAnnotatedTypes space (Atom.expression (head :: ws))
    rw [annotations_expression hs, annotations_expression hs]

/-- **The corrected table is exact**: every valid table answers every node
of a head other than `NativeHandle` as inference does. -/
theorem fixed_table_exact (space : Space) (hs : SymbolSubjects space) (st : Atom → List Atom)
    (hexpr : ∀ xs ys, st (.expression xs) = st (.expression ys) →
      childView (reads space) (.expression xs) = childView (reads space) (.expression ys))
    (head : Atom) (hh : head ≠ Atom.symbol "NativeHandle") (q : Bool) (vs : List Atom)
    {table : Table Atom Atom CChild} (valid : Valid (ops space) (reads space) (cKey st) table) :
    read (ops space) (reads space) (cKey st) q head vs table =
      sourceNode (ops space) (reads space) q head vs :=
  read_eq_source _ _ _ head (fixed_key_adequate space hs st hexpr head hh) q vs valid

theorem handleSpace_symbolSubjects : SymbolSubjects handleSpace := by
  intro a ha subject type_ h
  simp only [handleSpace, Space.ofList, List.mem_singleton] at ha
  subst ha
  simp only [NativeTypeViewsControls.annotation, NativeTypeViewsControls.expr,
    NativeTypeViewsControls.sym, Atom.expression.injEq, List.cons.injEq] at h
  exact ⟨_, h.2.1.symm⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.StampKeys
