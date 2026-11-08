import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ShapeTyping

/-!
# Ordered first-match inference and its stamp cache

The inferred-type service used by a type stamp is not the full HE typing
relation. Within each function row it commits to the first successful typing
of each argument. A later failure does not reconsider an earlier choice.
Every function row is still tried, in order. If any arrow row was tried,
failure does not fall back to a tuple typing.

This module models that ordered driver on the existing `Atom` and `Ty`
syntax. Matching, binding application and result normalization are explicit
services: the driver does not equate the C matcher with HE's all-candidate
matcher. The closed equality service and a one-variable service instantiate
the driver in the controls. Full native matcher correspondence is separate.

The compositional profile has symbol-headed expressions, symbol-subject
declarations, no subtype closure, no identity-bearing native values and no
inference budget. List values with a distinct metatype are outside this
profile. Stamps retain ordered typing lists, including repeats. An executable
transition table is keyed by declaration revision, question, head and child
stamps; recording and validated lookup preserve the inference. The existing
arena/epoch theorem applies to this judgment as well.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.StampInference

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-- One argument's public shape: metatype and ordered typing answers. -/
structure Stamp where
  kind : String
  types : List (Ty String)
  deriving DecidableEq

/-- The operations used by the ordered inference driver. -/
structure Matcher (State : Type) where
  initial : State
  apply : State → Ty String → Ty String
  unify : State → Ty String → Ty String → Option State
  normalize : Ty String → Ty String

variable {State : Type}

/-- Scan in occurrence order, retaining the first successful result. -/
def firstResult {α β : Type} (f : α → Option β) : List α → Option β
  | [] => none
  | a :: as => match f a with
      | some b => some b
      | none => firstResult f as

theorem firstResult_none_iff {α β : Type} (f : α → Option β) (as : List α) :
    firstResult f as = none ↔ ∀ a ∈ as, f a = none := by
  induction as with
  | nil => simp [firstResult]
  | cons a as ih =>
      cases h : f a with
      | none => simp [firstResult, h, ih]
      | some b => simp [firstResult, h]

/-- A successful answer comes after a prefix of failures, not merely from
some successful candidate in the list. -/
theorem firstResult_some_iff {α β : Type} (f : α → Option β) (as : List α) (b : β) :
    firstResult f as = some b ↔
      ∃ pre a post, as = pre ++ a :: post ∧
        (∀ x ∈ pre, f x = none) ∧ f a = some b := by
  induction as with
  | nil =>
      constructor
      · intro h; cases h
      · rintro ⟨pre, a, post, h, _, _⟩
        have := congrArg List.length h
        simp at this
  | cons a as ih =>
      constructor
      · cases h : f a with
        | some c =>
            intro result
            have hc : c = b := by simpa [firstResult, h] using result
            exact ⟨[], a, as, rfl, by simp, hc ▸ h⟩
        | none =>
            intro result
            have tail : firstResult f as = some b := by simpa [firstResult, h] using result
            obtain ⟨pre, x, post, eq, fails, yes⟩ := ih.mp tail
            refine ⟨a :: pre, x, post, by simp [eq], ?_, yes⟩
            intro y hy
            rcases List.mem_cons.mp hy with rfl | hy
            · exact h
            · exact fails y hy
      · rintro ⟨pre, x, post, eq, fails, yes⟩
        cases pre with
        | nil =>
            cases eq
            simp [firstResult, yes]
        | cons y pre =>
            have parts := List.cons.inj eq
            have ha : f a = none := by
              rw [parts.1]
              exact fails y (by simp)
            rw [firstResult, ha]
            exact ih.mpr ⟨pre, x, post, parts.2,
              fun z hz => fails z (by simp [hz]), yes⟩

/-- Ordinary atom metatypes are checked from the child's kind, not from its
declared types. `none` means this is an ordinary type request. -/
def metaCheck (formal : Ty String) (kind : String) : Option Bool :=
  match formal with
  | .sym "Atom" => some true
  | .sym "Symbol" => some (kind == "Symbol")
  | .sym "Variable" => some (kind == "Variable")
  | .sym "Grounded" => some (kind == "Grounded")
  | .sym "Expression" => some (kind == "Expression")
  | _ => none

/-- The left-to-right argument loop. A selected candidate is committed before
the rest of the arguments are checked. -/
def checkArgs (M : Matcher State) : List (Ty String) → List Stamp → State → Option State
  | [], [], s => some s
  | p :: ps, a :: args, s =>
      match metaCheck (M.apply s p) a.kind with
      | some true => checkArgs M ps args s
      | some false => none
      | none =>
          (firstResult (fun t => M.unify s t (M.apply s p)) a.types).bind
            (checkArgs M ps args)
  | [], _ :: _, _ => none
  | _ :: _, [], _ => none

/-- An operational derivation of the argument loop. A type-choice step must
exhibit the failed prefix preceding the selected candidate. This rules out
backtracking into that prefix after a later argument fails. -/
inductive Checks (M : Matcher State) :
    List (Ty String) → List Stamp → State → State → Prop where
  | done (s : State) : Checks M [] [] s s
  | kindPass {p ps a args s result}
      (accepts : metaCheck (M.apply s p) a.kind = some true)
      (rest : Checks M ps args s result) : Checks M (p :: ps) (a :: args) s result
  | choice {p ps a args s next result}
      (ordinary : metaCheck (M.apply s p) a.kind = none)
      (pre : List (Ty String)) (candidate : Ty String) (post : List (Ty String))
      (shape : a.types = pre ++ candidate :: post)
      (skipped : ∀ t ∈ pre, M.unify s t (M.apply s p) = none)
      (selected : M.unify s candidate (M.apply s p) = some next)
      (rest : Checks M ps args next result) : Checks M (p :: ps) (a :: args) s result

theorem Checks.sound (M : Matcher State) {ps args s result}
    (run : Checks M ps args s result) : checkArgs M ps args s = some result := by
  induction run with
  | done => rfl
  | kindPass accepts rest ih => simp [checkArgs, accepts, ih]
  | @choice p ps a args s next result ordinary pre candidate post shape skipped selected rest ih =>
      have first := (firstResult_some_iff
        (fun t => M.unify s t (M.apply s p)) a.types next).mpr
          ⟨pre, candidate, post, shape, skipped, selected⟩
      simp [checkArgs, ordinary, first, ih]

theorem Checks.complete (M : Matcher State) (ps : List (Ty String)) :
    ∀ (args : List Stamp) (s result : State),
      checkArgs M ps args s = some result → Checks M ps args s result := by
  induction ps with
  | nil =>
      intro args s result h
      cases args with
      | nil =>
          have eq : s = result := by simpa [checkArgs] using h
          subst result
          exact .done s
      | cons a args => cases h
  | cons p ps ih =>
      intro args s result h
      cases args with
      | nil => cases h
      | cons a args =>
          cases kind : metaCheck (M.apply s p) a.kind with
          | some accepted =>
              cases accepted with
              | false => simp [checkArgs, kind] at h
              | true =>
                  exact .kindPass kind (ih args s result (by simpa [checkArgs, kind] using h))
          | none =>
              cases first : firstResult (fun t => M.unify s t (M.apply s p)) a.types with
              | none => simp [checkArgs, kind, first] at h
              | some next =>
                  have tail : checkArgs M ps args next = some result := by
                    simpa [checkArgs, kind, first] using h
                  obtain ⟨pre, candidate, post, shape, skipped, selected⟩ :=
                    (firstResult_some_iff _ _ _).mp first
                  exact .choice kind pre candidate post shape skipped selected (ih args next result tail)

/-- Exact correspondence with the operational first-match driver. -/
theorem checkArgs_iff_checks (M : Matcher State) (ps : List (Ty String))
    (args : List Stamp) (s result : State) :
    checkArgs M ps args s = some result ↔ Checks M ps args s result :=
  ⟨Checks.complete M ps args s result, Checks.sound M⟩

/-- The first-match driver admits at most one final substitution, even when
an argument has several successful typings. -/
theorem Checks.deterministic (M : Matcher State) {ps args s r₁ r₂}
    (left : Checks M ps args s r₁) (right : Checks M ps args s r₂) : r₁ = r₂ := by
  exact Option.some.inj ((Checks.sound M left).symm.trans (Checks.sound M right))

/-- One row contributes zero or one inferred type. -/
def rowResult (M : Matcher State) (args : List Stamp) (row : Ty String) : Option (Ty String) :=
  match arrowSplit row with
  | none => none
  | some (parameters, result) =>
      (checkArgs M parameters args M.initial).map fun s => M.normalize (M.apply s result)

/-- Tuple alternatives in occurrence order, last position varying fastest. -/
def product {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | xs :: xss => xs.flatMap fun x => (product xss).map (x :: ·)

/-- Undefined types do not participate in tuple formation, and function
types do not participate at the head position. -/
def tuplePart (head : Bool) (types : List (Ty String)) : List (Ty String) :=
  types.filter fun t => t != undefinedTy && (!head || !ShapeTyping.IsFun t)

def defaultTypes (types : List (Ty String)) : List (Ty String) :=
  if types.isEmpty then [undefinedTy] else types

/-- One symbol-headed inference from its rows and child stamps. Arrow rows
suppress tuple fallback even when every attempted arrow fails. -/
def inferRows (M : Matcher State) (rows : List (Ty String)) (args : List Stamp) : Stamp :=
  ⟨"Expression",
    if rows.any ShapeTyping.IsFun then rows.filterMap (rowResult M args)
    else defaultTypes ((product (tuplePart true rows ::
      args.map fun a => tuplePart false a.types)).map Ty.app)⟩

/-- The compositional judgment also retains symbol declarations at leaves,
so a parent can distinguish declared operator rows from inferred child types. -/
structure Info where
  stamp : Stamp
  rows : Option (List (Ty String))
  deriving DecidableEq

def leaf (Γ : Decls) : Atom → Info
  | .symbol s => ⟨⟨"Symbol", defaultTypes (Γ s)⟩, some (Γ s)⟩
  | .var _ => ⟨⟨"Variable", [undefinedTy]⟩, none⟩
  | .grounded g => ⟨⟨"Grounded", match valueClass g with
      | some c => [.sym c]
      | none => [undefinedTy]⟩, none⟩
  | .expression _ => ⟨⟨"Expression", [undefinedTy]⟩, none⟩

/-- Non-symbol heads lie outside this constructor profile. -/
def node (M : Matcher State) : List Info → Info
  | h :: args => match h.rows with
      | some rows => ⟨inferRows M rows (args.map Info.stamp), none⟩
      | none => ⟨⟨"Expression", [undefinedTy]⟩, none⟩
  | [] => ⟨⟨"Expression", [undefinedTy]⟩, none⟩

def judgment (M : Matcher State) : TypedCertificates.Judgment Decls Info :=
  ⟨leaf, node M⟩

def infer (M : Matcher State) (Γ : Decls) (v : Atom) : Stamp :=
  (TypedCertificates.Judgment.full (judgment M) Γ v).stamp

theorem infer_node (M : Matcher State) (Γ : Decls) (head : String) (args : List Atom) :
    infer M Γ (.expression (.symbol head :: args)) =
      inferRows M (Γ head) (args.map (infer M Γ)) := by
  unfold infer
  rw [TypedCertificates.Judgment.full_expression]
  simp only [List.map_cons, judgment, TypedCertificates.Judgment.full, leaf, node,
    List.map_map]
  rfl

/-- Replacing any child by one with the same ordered stamp preserves the
parent's complete ordered inference, not just its set of possible types. -/
theorem infer_congr_children (M : Matcher State) (Γ : Decls) (head : String)
    (xs ys : List Atom) (same : xs.map (infer M Γ) = ys.map (infer M Γ)) :
    infer M Γ (.expression (.symbol head :: xs)) =
      infer M Γ (.expression (.symbol head :: ys)) := by
  rw [infer_node, infer_node, same]

theorem infer_congr_declarations (M : Matcher State) {Γ Γ' : Decls} (v : Atom)
    (same : ∀ s, Atom.symbol s ∈ TypedCertificates.Judgment.leaves v → Γ s = Γ' s) :
    infer M Γ v = infer M Γ' v := by
  unfold infer
  congr 1
  apply TypedCertificates.Judgment.full_congr (judgment M) v
  intro atom ha
  cases atom with
  | symbol s => simp only [judgment, leaf, same s ha]
  | var _ => rfl
  | grounded _ => rfl
  | expression _ => rfl

/-- The declaration environment is named by the complete bound store token,
not by a declaration counter shared by unrelated spaces. -/
structure Scope where
  space : Nat
  revision : Nat
  dependencyEpoch : Nat
  evaluatorScope : Nat
  deriving DecidableEq

/-- Question and scope are not discarded from a transition key. The ordered
list of child stamps also records arity. -/
structure Key where
  scope : Scope
  question : Nat
  head : String
  args : List Stamp
  deriving DecidableEq

abbrev Table := List (Key × Stamp)

def Key.result (M : Matcher State) (decls : Scope → Decls) (key : Key) : Stamp :=
  inferRows M (decls key.scope key.head) key.args

/-- An entry was produced by the ordered inference under its own key. -/
def Valid (M : Matcher State) (decls : Scope → Decls) (table : Table) : Prop :=
  ∀ key answer, (key, answer) ∈ table → answer = key.result M decls

/-- Record a transition by prepending an entry. Repeated equal entries are
allowed: lookup remains deterministic and the invariant covers every entry. -/
def record (M : Matcher State) (decls : Scope → Decls) (key : Key) (table : Table) : Table :=
  (key, key.result M decls) :: table

def lookup (key : Key) : Table → Option Stamp
  | [] => none
  | (k, answer) :: rest => if key = k then some answer else lookup key rest

def read (M : Matcher State) (decls : Scope → Decls) (key : Key) (table : Table) : Stamp :=
  (lookup key table).getD (key.result M decls)

theorem valid_empty (M : Matcher State) (decls : Scope → Decls) : Valid M decls [] := by
  intro key answer h
  cases h

theorem valid_record (M : Matcher State) (decls : Scope → Decls) (key : Key) (table : Table)
    (valid : Valid M decls table) : Valid M decls (record M decls key table) := by
  intro k answer h
  rcases List.mem_cons.mp h with h | h
  · cases h
    rfl
  · exact valid k answer h

theorem lookup_sound (M : Matcher State) (decls : Scope → Decls) (key : Key) (table : Table)
    (valid : Valid M decls table) {answer : Stamp} (hit : lookup key table = some answer) :
    answer = key.result M decls := by
  induction table with
  | nil => cases hit
  | cons entry rest ih =>
      obtain ⟨k, stored⟩ := entry
      by_cases same : key = k
      · subst k
        have eq : stored = answer := by simpa [lookup] using hit
        subst answer
        exact valid key stored (by simp)
      · have tail : lookup key rest = some answer := by simpa [lookup, same] using hit
        exact ih (fun k a ha => valid k a (by simp [ha])) tail

theorem read_eq (M : Matcher State) (decls : Scope → Decls) (key : Key) (table : Table)
    (valid : Valid M decls table) : read M decls key table = key.result M decls := by
  unfold read
  cases hit : lookup key table with
  | none => rfl
  | some answer => exact lookup_sound M decls key table valid hit

/-- The cache answers the full inference of every constructor whose child
stamps equal the key, including all duplicate occurrences. -/
theorem transition_eq_inference (M : Matcher State) (decls : Scope → Decls)
    (scope : Scope) (question : Nat) (head : String) (args : List Atom) (table : Table)
    (valid : Valid M decls table) :
    read M decls ⟨scope, question, head, args.map (infer M (decls scope))⟩ table =
      infer M (decls scope) (.expression (.symbol head :: args)) := by
  rw [read_eq M decls _ table valid, infer_node]
  rfl

/-- Whole-subtree memoization uses the same ordered judgment. -/
theorem recorded_inference (M : Matcher State) (Γ : Decls)
    (memo : TypedCertificates.Judgment.Memo Info)
    (valid : TypedCertificates.Judgment.Valid (judgment M) Γ memo) (v : Atom) :
    (TypedCertificates.Judgment.check (judgment M) Γ memo v).stamp = infer M Γ v := by
  rw [TypedCertificates.Judgment.check_eq (judgment M) Γ memo valid v]
  rfl

/-- Address hits retain this inference only after validating arena and epoch. -/
theorem validated_address_hit {Addr : Type} (M : Matcher State) (Γ : Decls)
    {heap : ShapeTyping.Heap Addr} {memo : ShapeTyping.AddrMemo Addr Stamp}
    (valid : ShapeTyping.Sound heap (infer M Γ) memo) {p : Addr} {answer : Stamp}
    (hit : ShapeTyping.lookupAt heap memo p = some answer) :
    ∃ v arena, heap.cell p = some (v, arena) ∧ answer = infer M Γ v :=
  ShapeTyping.validated_hit valid hit

namespace Controls

/-- Exact closed-type matching, without wildcard or subtype extensions. -/
def closed : Matcher Unit where
  initial := ()
  apply := fun _ t => t
  unify := fun _ actual expected => if actual = expected then some () else none
  normalize := id

def number : Ty String := .sym "Number"
def string : Ty String := .sym "String"
def arrowRow (parameters : List (Ty String)) (result : Ty String) : Ty String :=
  .app (.sym "->" :: parameters ++ [result])

def numeric : Stamp := ⟨"Grounded", [number]⟩
def textual : Stamp := ⟨"Grounded", [string]⟩

/-- Distinct applicable function rows may yield the same type twice. -/
theorem row_multiplicity :
    (inferRows closed [arrowRow [number] number, arrowRow [.sym "Atom"] number] [numeric]).types =
      [number, number] := by decide +kernel

/-- A failed arrow is not rescued by the tuple fallback. -/
theorem no_tuple_after_failed_arrow :
    (inferRows closed [arrowRow [number] number] [textual]).types = [] := by decide +kernel

/-- Without any arrow row, ordinary tuple formation is retained. -/
theorem tuple_without_arrow :
    (inferRows closed [.sym "Tag"] [numeric, textual]).types =
      [.app [.sym "Tag", number, string]] := by decide +kernel

/-- Metatype checks read the atom's kind, not its list of declared types. -/
theorem kind_is_required :
    checkArgs closed [.sym "Symbol"] [⟨"Symbol", [number]⟩] () = some () ∧
      checkArgs closed [.sym "Symbol"] [numeric] () = none := by decide +kernel

def natDecls : Decls := fun head =>
  if head = "Z" then [.sym "Nat"]
  else if head = "S" then [arrowRow [.sym "Nat"] (.sym "Nat")]
  else []

def numeral : Nat → Atom
  | 0 => .symbol "Z"
  | n + 1 => .expression [.symbol "S", numeral n]

/-- The ordered inference types arbitrarily deep constructor values. -/
theorem numeral_types (n : Nat) : (infer closed natDecls (numeral n)).types = [.sym "Nat"] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [numeral, infer_node]
      simp only [closed] at ih
      simp [inferRows, natDecls, arrowRow, ShapeTyping.IsFun, rowResult,
        arrowSplit, checkArgs, closed, metaCheck, firstResult, ih]

theorem wrong_constructor_argument :
    (infer closed natDecls (.expression [.symbol "S", .grounded (.int 1)])).types = [] := by
  decide +kernel

/-- A single shared formal variable; sufficient to expose the greedy
argument policy independently of the native unification implementation. -/
def oneVariable : Matcher (Option (Ty String)) where
  initial := none
  apply := fun env t => t.bind fun x => if x = "a" then env.getD (.var x) else .var x
  unify := fun env actual formal =>
    if formal = .var "a" then some (some actual)
    else if actual = formal then some env else none
  normalize := id

def both : Stamp := ⟨"Symbol", [number, string]⟩
def reversed : Stamp := ⟨"Symbol", [string, number]⟩

/-- Permuting a child's answers can change the inferred result. Sets and
bags therefore cannot replace the ordered stamp. -/
theorem order_matters :
    rowResult oneVariable [both] (arrowRow [.var "a"] (.var "a")) = some number ∧
      rowResult oneVariable [reversed] (arrowRow [.var "a"] (.var "a")) = some string := by
  decide +kernel

/-- An early commitment can make a later argument fail, although taking the
other early candidate would have produced a complete solution. -/
theorem first_local_not_first_complete :
    rowResult oneVariable [both, textual]
      (arrowRow [.var "a", .var "a"] (.var "a")) = none ∧
    rowResult oneVariable [reversed, textual]
      (arrowRow [.var "a", .var "a"] (.var "a")) = some string := by
  decide +kernel

def changed : Scope → Decls := fun scope head =>
  if head = "f" then
    [arrowRow [number] (if scope.revision = 0 then number else string)]
  else []

def oldKey : Key := ⟨⟨0, 0, 0, 0⟩, 0, "f", [numeric]⟩
def newKey : Key := ⟨⟨0, 1, 0, 0⟩, 0, "f", [numeric]⟩
def oldTable : Table := record closed changed oldKey []

theorem recorded_hit : lookup oldKey oldTable = some ⟨"Expression", [number]⟩ := by
  decide +kernel

/-- The same shape at a different declaration revision must miss. -/
theorem revision_miss : lookup newKey oldTable = none ∧
    read closed changed newKey oldTable = ⟨"Expression", [string]⟩ := by decide +kernel

/-- Reusing the old transition while discarding revision returns the wrong
inference, even though the head and children are unchanged. -/
theorem stale_transition_wrong :
    oldKey.result closed changed ≠ newKey.result closed changed := by decide +kernel

theorem different_question_misses :
    lookup { oldKey with question := 1 } oldTable = none := by decide +kernel

theorem different_space_misses :
    lookup { oldKey with scope := { oldKey.scope with space := 1 } } oldTable = none := by
  decide +kernel

theorem different_dependency_epoch_misses :
    lookup { oldKey with scope := { oldKey.scope with dependencyEpoch := 1 } } oldTable = none := by
  decide +kernel

def oldHeap : ShapeTyping.Heap Nat :=
  ⟨fun p => if p = 0 then some (.grounded (.int 1), 0) else none, fun _ => 0⟩

def oldMemo : ShapeTyping.AddrMemo Nat Stamp :=
  fun p => if p = 0 then some (0, 0, numeric) else none

def reusedHeap : ShapeTyping.Heap Nat :=
  (oldHeap.step (.reset 0)).step (.alloc 0 (.grounded (.string "x")) 0)

theorem stale_epoch_misses : ShapeTyping.lookupAt reusedHeap oldMemo 0 = none := by
  decide +kernel

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.StampInference
