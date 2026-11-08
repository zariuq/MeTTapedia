import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ValueRows
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.CertifiedSpines
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypingTransfer
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.StampKeys
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.StaticEvidence

/-!
# The type stamp store's invariant, its leaves-up typing, the noted build, and PeTTa's let-form guards

**A kept typing vouches its subtree has no expression-row node.** The store keeps a
node's typing only in these ways (`Records`):
* inference or a shape hit (`get_atom_types_mode`, `type_stamps_type_children`,
  `type_stamps_state_of`) on a node it admits (`type_stamps_admit`: a symbol head no
  row types an expression by) whose expression children all keep a typing (a shape
  key reads each child's kept state, so a shape hit implies it);
* the run's answer (`space_type_stamps_record_type`) on an admitted node whose
  children keep typings, or that the hereditary walk passes;
* a copy of a kept node (`space_type_stamps_transfer`);
* the hereditary walk's own marks (`space_type_rows_free_below`).
Each keeps the invariant that every kept node is row-free below (`records_vouch`,
`keep_vouches`). The store is cleared when the declarations change, which the
invariant needs (`Controls.declarations_change`). So the machine's check, which reads
the store first and walks the rows only where nothing is kept, judges a row-free
value either way, where `ValueRows.check_iff` makes it HE's (`store_check_exact`).

**Leaves-up typing in any order** (`type_stamps_type_children`): every state it keeps
is read from a valid transition table or computed by inference, and a valid table
answers as inference does (`StampKeys.read_eq_source`), so the states kept are
inference's whatever the order, the recursion's included (`typeAll_source`,
`typeAll_order`); a node met before a shared child it waits for misses the table and
is inferred. The scope bound once for the walk is the scope each step binds:
binding is idempotent under one declaration token (`bind_idem`).

**The noted build through a collection** (`prepared_pure_gc_collect`): a build kept
by the strong roots moves to a structural copy, which has its source's typing
(`TypingTransfer.stamp_rename`), so the typing recorded at the copy's address is the
build's (`answer_typing_relocated`); a build the roots do not keep is forgotten.

**PeTTa's let-form guards.** A callee whose trusted version proves its closed range
answers, on arguments meeting the version's entry facts, values its result guard
passes exactly once, so the guard may go (`result_guard_discharged`); a let-bound
answer passed on at the identical formal meets the next callee's guard exactly once
(`let_form_discharged`, from `StaticEvidence.proven_range_discharged`). The facts are
the condition: the argument guards check types, and a type passed by a value with
variables is not kept under the bindings the callee makes, where a ground value's is
(`ground_subst`, `Controls.binding_breaks_type`): with
`(: f (-> (List Number) (List Number)))` and `(= (f $l) (let (Cons "s" $t) $l $l))`,
which has a version with a proven range, `(f (Cons $e Nil))` passes the argument guard,
binds `$e` to `"s"`, and its result guard rejects `(Cons "s" Nil)`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.StampStoreInvariant

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open ValueRows (rowsFree rowsFreeAll Reading heCheck Accepts TySet ScopedStore admitted_check_iff)

/-! ## A kept typing vouches its subtree -/

section Vouch

variable (typesExpr : String → Bool)

/-- A node the store admits (`type_stamps_admit`): an expression whose head is a
symbol that no type row types an expression by. -/
def Admitted : Atom → Prop
  | .expression (.symbol h :: _) => typesExpr h = false
  | _ => False

/-- An expression. -/
def IsExpr : Atom → Prop
  | .expression _ => True
  | _ => False

/-- Every expression element after the head keeps a typing
(`type_stamps_children_kept`). -/
def ChildrenKept (kept : Atom → Prop) : Atom → Prop
  | .expression (_ :: rest) => ∀ x ∈ rest, IsExpr x → kept x
  | _ => True

/-- **The store's invariant**: every kept node is row-free below. -/
def Vouches (kept : Atom → Prop) : Prop := ∀ t, kept t → rowsFree typesExpr t = true

/-- **The ways the store comes to keep a node's typing.** -/
inductive Records (kept : Atom → Prop) : Atom → Prop
  /-- Inference or a shape hit on an admitted node whose children keep typings. -/
  | inferred {t : Atom} : Admitted typesExpr t → ChildrenKept kept t → Records kept t
  /-- The run's answer: an admitted node whose children keep typings, or that the
  hereditary walk passes. -/
  | runAnswer {t : Atom} : Admitted typesExpr t →
      (ChildrenKept kept t ∨ rowsFree typesExpr t = true) → Records kept t
  /-- A copy of a kept node. -/
  | transfer {t s : Atom} : kept s → t = s → Records kept t
  /-- The hereditary walk's mark after it passed. -/
  | walked {t : Atom} : rowsFree typesExpr t = true → Records kept t

theorem rowsFree_of_not_expr {t : Atom} (h : ¬ IsExpr t) : rowsFree typesExpr t = true := by
  cases t with
  | symbol _ => rfl
  | var _ => rfl
  | grounded _ => rfl
  | expression _ => exact absurd trivial h

theorem rowsFreeAll_of_each : ∀ {xs : List Atom}, (∀ x ∈ xs, rowsFree typesExpr x = true) →
    rowsFreeAll typesExpr xs = true
  | [], _ => rfl
  | x :: xs, h => by
      simp only [rowsFreeAll, Bool.and_eq_true]
      exact ⟨h x (by simp), rowsFreeAll_of_each fun y hy => h y (by simp [hy])⟩

/-- An admitted node whose children keep typings, under the invariant, is
row-free below. -/
theorem rowsFree_of_children {kept : Atom → Prop} (inv : Vouches typesExpr kept) {t : Atom}
    (ha : Admitted typesExpr t) (hc : ChildrenKept kept t) : rowsFree typesExpr t = true := by
  match t, ha, hc with
  | .expression (.symbol h :: rest), ha, hc =>
      simp only [Admitted] at ha
      simp only [rowsFree, ha, Bool.not_false, Bool.true_and]
      apply rowsFreeAll_of_each
      intro x hx
      by_cases e : IsExpr x
      · exact inv x (hc x hx e)
      · exact rowsFree_of_not_expr typesExpr e

/-- **Every way of keeping keeps the invariant.** -/
theorem records_vouch {kept : Atom → Prop} (inv : Vouches typesExpr kept) {t : Atom}
    (hr : Records typesExpr kept t) : rowsFree typesExpr t = true := by
  cases hr with
  | inferred ha hc => exact rowsFree_of_children typesExpr inv ha hc
  | runAnswer ha h =>
      rcases h with hc | hw
      · exact rowsFree_of_children typesExpr inv ha hc
      · exact hw
  | transfer hs heq =>
      subst heq
      exact inv _ hs
  | walked hw => exact hw

/-- **A kept typing vouches its subtree**: keeping a node by any of the store's ways
keeps the invariant. -/
theorem keep_vouches {kept : Atom → Prop} (inv : Vouches typesExpr kept) {t : Atom}
    (hr : Records typesExpr kept t) : Vouches typesExpr fun u => kept u ∨ u = t := by
  rintro u (hu | rfl)
  · exact inv u hu
  · exact records_vouch typesExpr inv hr

/-- The empty store, after a clear, vouches for nothing it does not keep. -/
theorem cleared_vouches : Vouches typesExpr fun _ => False := fun _ h => h.elim

/-- **The machine's check is HE's on every value it judges**: it reads the store's
typing where one is kept, and otherwise walks the rows; either way the value is
row-free below, and its reading's check is HE's (`ValueRows.check_iff`). -/
theorem store_check_exact (ρ : Reading) (rows : ∀ h, typesExpr h = false → ρ.rowsOf h = [])
    {kept : Atom → Prop} (inv : Vouches typesExpr kept) (t : Atom)
    (judged : kept t ∨ rowsFree typesExpr t = true) (E : TySet) :
    (heCheck (ρ.read t) E).isSome ↔ Accepts (ρ.read t) E := by
  apply admitted_check_iff ρ typesExpr rows t
  rcases judged with hk | hw
  · exact inv t hk
  · exact hw

end Vouch

/-! ## Leaves-up typing in any order -/

section Iterative

open NativeTypeViews StampKeys

variable {Value TypeAtom Bind Kind K : Type} [DecidableEq Value] [DecidableEq K]
variable (ops : Ops TypeAtom Bind Kind) (reads : Reads Value TypeAtom Kind) (key : Value → K)
  (q : Bool)

/-- **Typing nodes one by one** (`type_stamps_type_children`): each node's state is
read from the table (a hit) or computed by inference (a miss), and recorded. -/
def typeAll : Table Value TypeAtom K → List (Value × List Value) → Table Value TypeAtom K × List (List TypeAtom)
  | table, [] => (table, [])
  | table, (head, vs) :: rest =>
      let answer := read ops reads key q head vs table
      let next := typeAll (record ops reads key q head vs table) rest
      (next.1, answer :: next.2)

/-- **Every kept state is inference's**, whatever the order of the nodes, from any
valid table, at heads whose key is adequate. -/
theorem typeAll_source (adequate : ∀ head : Value, Adequate reads key head) :
    ∀ (table : Table Value TypeAtom K) (nodes : List (Value × List Value)),
      Valid ops reads key table →
        (typeAll ops reads key q table nodes).2 = nodes.map (fun n => sourceNode ops reads q n.1 n.2) ∧
          Valid ops reads key (typeAll ops reads key q table nodes).1
  | table, [], valid => ⟨rfl, valid⟩
  | table, (head, vs) :: rest, valid => by
      obtain ⟨answers, valid'⟩ := typeAll_source adequate (record ops reads key q head vs table) rest
        (valid_record ops reads key q head vs valid)
      refine ⟨?_, valid'⟩
      simp only [typeAll, List.map_cons, answers]
      rw [read_eq_source ops reads key head (adequate head) q vs valid]

/-- **The order does not matter**: two orders of nodes keep, at a node met in both,
the same state. -/
theorem typeAll_order (adequate : ∀ head : Value, Adequate reads key head)
    (table table' : Table Value TypeAtom K) (valid : Valid ops reads key table)
    (valid' : Valid ops reads key table') (nodes nodes' : List (Value × List Value))
    {n : Value × List Value} {i j : ℕ} (hi : nodes[i]? = some n) (hj : nodes'[j]? = some n) :
    (typeAll ops reads key q table nodes).2[i]? = (typeAll ops reads key q table' nodes').2[j]? := by
  rw [(typeAll_source ops reads key q adequate table nodes valid).1,
    (typeAll_source ops reads key q adequate table' nodes' valid').1, List.getElem?_map,
    List.getElem?_map, hi, hj]

end Iterative

/-- **The scope bound once is the scope each step binds**: under one declaration
token, binding again changes nothing. -/
theorem bind_idem {Addr : Type} (st : ScopedStore Addr) (r : ℕ) : (st.bind r).bind r = st.bind r := by
  unfold ScopedStore.bind
  split_ifs with h1 h2 <;> simp_all

/-! ## The noted build through a collection -/

section Relocation

open ShapeTyping ExactStaticTypes TypingTransfer

variable {Addr : Type} [DecidableEq Addr]

/-- **The recorded typing follows the build to its copy**: where the strong roots
moved the build's value `t` to a structural copy `t'` at `q'`, recording the build's
exact typing `S` there is sound, a later validated hit at `q'` is HE's typing of the
atom then there, and while the arena's epoch is unchanged that atom is the copy,
typed exactly at `S`. -/
theorem answer_typing_relocated {Γ : Decls} {H : Heap Addr} {m : AddrMemo Addr Stamp}
    (hm : Sound H (stamp Γ) m) {q' : Addr} {t t' : Atom} {b' : ℕ} (hq' : H.cell q' = some (t', b'))
    (copy : ∃ g, t' = renameA g t) {S : Set (Ty Empty)} (hS : ExactAt S (stamp Γ t))
    (ops : List (HeapOp Addr)) {j : Stamp}
    (hit : lookupAt (H.run ops)
        (Function.update m q' (some (b', H.epoch b', ⟨metaName t', [Sem.ok S]⟩))) q' = some j) :
    (∃ t'' a, (H.run ops).cell q' = some (t'', a) ∧ j = stamp Γ t'') ∧
      ((H.run ops).epoch b' = H.epoch b' → j = stamp Γ t' ∧ (answers Γ t').map sols = [S]) := by
  obtain ⟨g, rfl⟩ := copy
  have hS' : ExactAt S (stamp Γ (renameA g t)) := by
    rw [stamp_rename]
    exact hS
  exact answer_typing hm hq' hS' ops hit

end Relocation

/-! ## PeTTa's let-form guards -/

section LetForm

open StaticEvidence

variable {Γ : Decls} {grounded : String → Bool}

/-- **The result guard may go on a call meeting the version's entry facts**: the
version proves its closed range, so its result guard passes each answer exactly
once, and the protocol's answers are the unguarded ones. -/
theorem result_guard_discharged {bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    {As : List (Ty Empty)} {R : Ty Empty}
    (hV : VersionHyps (Γ := Γ) (grounded := grounded) bodyP bodyV As R) (n : ℕ) (ws : List Atom)
    (hws : EntryFacts Γ grounded As ws) :
    chainCall Γ (metatype grounded) (versionRun bodyV n) (arrow (As.map Ty.lift) R.lift) ws =
      argCount Γ (metatype grounded) As ws • versionRun bodyV n ws := by
  rw [chainCall_closed]
  congr 1
  calc (versionRun bodyV n ws).bind (fun r =>
          if ResultGuarded R.lift then guardCount (info Γ r) R (metatype grounded r) • {r} else {r})
        = (versionRun bodyV n ws).bind fun r => {r} := Multiset.bind_congr fun r hr => by
          have one := (version_results hV n ws hws r hr).guardCount
          split_ifs <;> simp [one]
      _ = versionRun bodyV n ws := by rw [Multiset.bind_singleton, Multiset.map_id']

/-- **The let-form with both guards gone**: the answers of `(let $l (build ..) (sum
$l))`, `build`'s result guarded and `sum`'s argument guarded at `build`'s range, are
those with neither guard, multiplicity included. -/
theorem let_form_discharged (hΓ : Functional Γ)
    {bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    {As : List (Ty Empty)} {R : Ty Empty}
    (hV : VersionHyps (Γ := Γ) (grounded := grounded) bodyP bodyV As R) (n : ℕ) (ws : List Atom)
    (hws : EntryFacts Γ grounded As ws) (sumBody : List Atom → Multiset Atom) (S : Ty Empty) :
    (chainCall Γ (metatype grounded) (versionRun bodyV n) (arrow (As.map Ty.lift) R.lift) ws).bind
        (fun r => chainCall Γ (metatype grounded) sumBody (arrow ([R].map Ty.lift) S.lift) [r]) =
      (argCount Γ (metatype grounded) As ws • versionRun bodyV n ws).bind
        (fun r => chainCall Γ (metatype grounded) sumBody (arrow ([uncheckedTy].map Ty.lift) S.lift) [r]) := by
  rw [result_guard_discharged hV n ws hws]
  refine Multiset.bind_congr fun r hr => ?_
  have held := proven_range_holds hV n ws hws (Multiset.mem_of_mem_nsmul hr)
  have := identical_formal_discharged hΓ sumBody [] [] R S [] [] rfl held
  simpa using this

/-! ### Why the entry facts ask for ground arguments -/

mutual
/-- An atom with values substituted for its variables. -/
def substA (σ : String → Option Atom) : Atom → Atom
  | .var x => (σ x).getD (.var x)
  | .symbol s => .symbol s
  | .grounded g => .grounded g
  | .expression xs => .expression (substL σ xs)
/-- A list of atoms with values substituted for their variables. -/
def substL (σ : String → Option Atom) : List Atom → List Atom
  | [] => []
  | x :: xs => substA σ x :: substL σ xs
end

mutual
/-- **A ground value is kept under every binding**, and so is every fact about it. -/
theorem ground_subst (σ : String → Option Atom) : ∀ v : Atom, CertifiedSpines.Ground v → substA σ v = v
  | .var _, h => h.elim
  | .symbol _, _ => rfl
  | .grounded _, _ => rfl
  | .expression xs, h => by
      rw [substA, groundAll_subst σ xs h]
theorem groundAll_subst (σ : String → Option Atom) :
    ∀ xs : List Atom, CertifiedSpines.GroundAll xs → substL σ xs = xs
  | [], _ => rfl
  | x :: xs, h => by
      rw [substL, ground_subst σ x h.1, groundAll_subst σ xs h.2]
end

end LetForm

/-! ## Controls -/

namespace Controls

open TypedCalls.Controls (sym num app listOf consRow cons_constructor)
open ClosedSortEvidence (listDecls listDecls_cons)
open CertifiedSpines.Controls (listDecls_functional count_int count_nil_of listNum)

/-- **Clearing on a declaration change is needed**: a node row-free while no row
types an expression by its head is not once one does. -/
theorem declarations_change :
    rowsFree (fun _ => false) (app "Wrap" [num 1]) = true ∧
      rowsFree (fun h => h == "Wrap") (app "Wrap" [num 1]) = false := by
  constructor <;> rfl

/-- `(Cons $e Nil)` and its instance `(Cons "s" Nil)` under `$e := "s"`. -/
def openCell : Atom := app "Cons" [.var "e", sym "Nil"]

/-- **A type passed by a value with variables is not kept under a binding**:
`(Cons $e Nil)` is typed once at `(List Number)`, its instance under `$e := "s"` not
at all (the probe's `f` answers nothing where its result guard rejects it). -/
theorem binding_breaks_type :
    count (info listDecls openCell) listNum = 1 ∧
      substA (fun x => if x = "e" then some (.grounded (.string "s")) else none) openCell =
        app "Cons" [.grounded (.string "s"), sym "Nil"] ∧
      count (info listDecls (app "Cons" [.grounded (.string "s"), sym "Nil"])) listNum = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · have := ctor_construction listDecls_functional (C := "Cons") listDecls_cons cons_constructor
      [.var "e", sym "Nil"] rfl (fun _ => .sym "Number") (by
        intro p hp _
        simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
          or_false] at hp
        rcases hp with rfl | rfl
        · exact count_var _ _ _
        · simpa [listOf] using count_nil_of listDecls_functional
            ClosedSortEvidence.listDecls_nil (.sym "Number"))
    simpa [openCell, listOf] using this
  · simp [openCell, substA, substL]
  · have le := count_le_one listDecls_functional (app "Cons" [.grounded (.string "s"), sym "Nil"])
      listNum
    by_contra ne
    have one : count (info listDecls (app "Cons" [.grounded (.string "s"), sym "Nil"])) listNum = 1 := by
      omega
    obtain ⟨σ, hσ, fields⟩ := ctor_inversion listDecls_functional listDecls_cons _ rfl listNum
      (by simp [Named, listOf]) one
    have ha : σ "a" = .sym "Number" := by simpa [listOf] using hσ
    have field := fields (.var "a", .grounded (.string "s")) (by simp) (by simp [Unchecked])
    rw [Ty.bind_var', ha, count_class listDecls (g := .string "s") rfl] at field
    simp at field

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.StampStoreInvariant
