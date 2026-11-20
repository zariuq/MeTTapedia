import Mettapedia.Languages.HOLLight.RuleModuleInterning

/-!
# Generic components of the rule compiler: structural order, memo tables, ordered sets

The HOL Light kernel rule module is compiled to C.  Some of its judgments are answered by generic
C components instead of their compiled rules, and the rules stay the contract.  For three
components this file states a model of the C function and proves that the model computes what the
rules compute.  That each C function computes its model is trusted; each model follows its
function step by step.

* **Structural order** (`rc_order_cmp`).  A value of an interned sort is a tree whose nodes are
  constructors, byte strings or naturals (`RcLabel`), as the interning store holds it.  A
  signature (`Signature`: the tables `rc_sort_order`, `rc_ctor_rank`, `rc_ctor_asort`) gives each
  sort its kind of order, and each constructor its rank and the sorts of its arguments.
  `structuralOrder` compares two values of a sort: constructor nodes by the ranks of their
  constructors if these differ, otherwise by their children from left to right, each by the order
  of its own sort, the first difference deciding; byte strings by `memcmp` over the common length,
  then the shorter first (`bytesCmp`, which is `nativeCmp`); naturals numerically (`natCmp`).  It
  answers `eq` on equal values (`structuralOrder_refl`), so the C procedure, which tests its two
  arguments for identity at every call (`rcOrderCmp`), computes it whenever that test holds only
  of equal values (`rcOrderCmp_eq`).  For the signature of the HOL Light module (`holSig`), on the
  trees of the module's names, types and terms as the store holds them (`rcTreeOfStr`,
  `rcTreeOfTy`, `rcTreeOfTerm`), it is `"cmp-str"`, `"cmp-type"`, `"cmp-types"` and `"cmp-term"`
  (`structuralOrder_cmpStr`, `structuralOrder_cmpType`, `structuralOrder_cmpTypes`,
  `structuralOrder_cmpTerm`; with the identity test, `rcOrderCmp_cmpType`, `rcOrderCmp_cmpTerm`),
  and it answers `eq` exactly on equal types and on equal terms (`structuralOrder_eq_iff_ty`,
  `structuralOrder_eq_iff_term`).
* **Memo tables** (`rc_memo`).  A memoised judgment is a function `f : K → Option V` of its
  arguments (`none`: the judgment fails; a failure is kept too).  A table holds pairs of a key and
  a result and is consulted by equality of keys; its invariant (`MemoSound`) is that every kept
  result is `f` of its key.  A call looks its key up, and on a miss computes `f k` and keeps it
  (`memoCall`); clearing empties the table.  Every run of calls and clearings answers each call
  with `f` of its key and keeps the invariant (`memo_sound`).  The two generations of the C tables
  (`Memo2`: a hit in the older one is copied into the current one; when the current one is full,
  the older one is dropped and the current one becomes the older) answer alike (`memo2_sound`) and
  never hold more than the capacity each (`memo2_bounded`).
* **Ordered sets** (`rc_set`).  The module's rules `"term-union-*"` and `"term-remove-*"` are
  transcribed one equation per rule (`termUnion`, `termRemove`), over a comparator that stands for
  `"alphaorder"`.  The loops of `rc_set_union` and `rc_set_remove` (`setUnion`, `setRemove`: the
  kept heads collected in a buffer, then consed onto the rest of the list) compute them, for every
  comparator (`setUnion_eq_termUnion`, `setRemove_eq_termRemove`).

How the models follow the C functions, and what they leave out.

* Order.  The identity test is `a == b` on words; equal words are one value, and in an interning
  store one value is one word (`interning_eq_iff`).  The C loop runs the last child of a node
  without a recursive call; that computes what the recursion computes.  The model answers `eq` on
  two values that do not fit their sort: values whose shape does not match the sort's kind of order
  (no C behaviour is defined for them), and two different values of a sort with no order (the C
  function stops the run there).  No part of a HOL Light type or term is of either kind.  The C
  function returns `-1`, `0`, `1`, which the generated glue turns into the module's `lt`, `eq`,
  `gt`.
* Memo tables.  A key of the model is a judgment with its arguments as values; the C key is the
  judgment's id and the argument words, compared word by word after a filter on a hash computed
  from them, which equal keys always pass.  The hashing, the probing and the growth of a
  generation's array are not modelled; they do not change which entries a generation holds.  A
  miss changes neither generation (`memoGet2_miss`), so the memoised calls that the rules make
  while computing a result come first in the run, and the call whose result they compute after
  them.  The tables are cleared before every collection of the interning store, so that a word
  never outlives the value it stood for.
* Sets.  The comparator is a total function here; a comparator that fails is not modelled (the C
  function expects one of `lt`, `eq`, `gt` from it).  The lists are values: that the rest of a
  list is shared rather than copied, and that the rebuilt conses are interned, is representation
  only.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.RuleModuleComponents

open RuleModulePrimitives RuleModuleComparisonLaws RuleModuleInterning

universe u v

/-! ## The structural order -/

section Order

/-- `rc_sort_order`: how the values of a sort are ordered. -/
inductive OrderKind
  /-- `RC_ORDER_NONE`: no order. -/
  | none
  /-- `RC_ORDER_STRUCT`: constructor nodes, ordered structurally. -/
  | struct
  /-- `RC_ORDER_BYTES`: byte strings. -/
  | bytes
  /-- `RC_ORDER_NAT`: naturals. -/
  | nat
  deriving DecidableEq, Repr

/-- The label of a node of a value: a constructor, whose arguments are the node's children; a byte
string; a natural, held as an immediate.  The last two have no children. -/
inductive RcLabel (C : Type u) : Type u
  | ctor (c : C)
  | bytes (b : List UInt8)
  | nat (n : Nat)
  deriving DecidableEq, Repr

instance {C : Type u} : Inhabited (RcLabel C) := ⟨.nat 0⟩

/-- The tables the compiler generates from a module's signature. -/
structure Signature (S : Type u) (C : Type v) : Type (max u v) where
  /-- `rc_sort_order`: the kind of order of each sort. -/
  order : S → OrderKind
  /-- `rc_ctor_rank`: the position of a constructor among the constructors of its sort. -/
  rank : C → Nat
  /-- `rc_ctor_asort`: the sorts of a constructor's arguments, in order. -/
  asort : C → List S

/-- `rc_bytes_cmp`: `memcmp` over the common length decides if it finds a difference; otherwise the
shorter string comes first. -/
def bytesCmp (a b : List UInt8) : Ord :=
  let c := memcmp a b (min a.length b.length)
  if c ≠ .eq then c else ordOfCompare (compare a.length b.length)

/-- `rc_nat_cmp`. -/
def natCmp (m n : Nat) : Ord :=
  if m < n then .lt else if n < m then .gt else .eq

/-- `rc_bytes_cmp` is the unsigned lexicographic order of bytes, a proper prefix first. -/
theorem bytesCmp_eq_nativeCmp (a b : List UInt8) : bytesCmp a b = nativeCmp a b :=
  (nativeCmp_eq_memcmp a b).symm

theorem then_eq_self (o : Ord) : o.then .eq = o := by
  cases o <;> rfl

variable {S : Type u} {C : Type v} [DecidableEq C]

/-- The comparison of two nodes of sort `s` with labels `a` and `b`, where `kids c` compares their
children when both are nodes of the constructor `c`.  By the kind of order of `s`: byte strings by
`bytesCmp`; naturals by `natCmp`; constructor nodes by the ranks of their constructors if the
constructors differ, otherwise by `kids`.  A pair of labels that does not fit the sort gets
`eq`. -/
def nodeCmp (σ : Signature S C) (s : S) (a b : RcLabel C) (kids : C → Ord) : Ord :=
  match σ.order s, a, b with
  | .bytes, .bytes x, .bytes y => bytesCmp x y
  | .nat, .nat m, .nat n => natCmp m n
  | .struct, .ctor c, .ctor d =>
    if c = d then kids c else if σ.rank c < σ.rank d then .lt else .gt
  | _, _, _ => .eq

/-- A node compared with itself is `eq` when its children are. -/
theorem nodeCmp_self (σ : Signature S C) (s : S) (a : RcLabel C) {kids : C → Ord}
    (h : ∀ c, kids c = .eq) : nodeCmp σ s a a kids = .eq := by
  cases a <;> cases hs : σ.order s <;>
    simp [nodeCmp, hs, h, bytesCmp_eq_nativeCmp, natCmp, nativeCmp_eq_eq_iff]

mutual

/-- **The structural order** of the signature `σ` on two values of sort `s`: the two root nodes by
`nodeCmp`, the children of two nodes of one constructor by `structuralOrderKids`. -/
def structuralOrder (σ : Signature S C) : S → Tree (RcLabel C) → Tree (RcLabel C) → Ord
  | s, .node a as, .node b bs => nodeCmp σ s a b fun c => structuralOrderKids σ (σ.asort c) as bs
termination_by structural _ t _ => t

/-- The children of two nodes of one constructor, from left to right, each by the order of its own
sort: the first that differs decides. -/
def structuralOrderKids (σ : Signature S C) :
    List S → List (Tree (RcLabel C)) → List (Tree (RcLabel C)) → Ord
  | s :: ss, x :: xs, y :: ys => (structuralOrder σ s x y).then (structuralOrderKids σ ss xs ys)
  | _, _, _ => .eq
termination_by structural _ xs _ => xs

end

mutual

/-- **`rc_order_cmp`**: the structural order, with the two values first tested by `same` at every
call (`a == b` on words). -/
def rcOrderCmp (same : Tree (RcLabel C) → Tree (RcLabel C) → Bool) (σ : Signature S C) :
    S → Tree (RcLabel C) → Tree (RcLabel C) → Ord
  | s, .node a as, .node b bs =>
    if same (.node a as) (.node b bs) then .eq
    else nodeCmp σ s a b fun c => rcOrderKids same σ (σ.asort c) as bs
termination_by structural _ t _ => t

/-- The children as `rc_order_cmp` compares them: all but the last by a recursive call, the last by
the next turn of its loop, which is the same comparison. -/
def rcOrderKids (same : Tree (RcLabel C) → Tree (RcLabel C) → Bool) (σ : Signature S C) :
    List S → List (Tree (RcLabel C)) → List (Tree (RcLabel C)) → Ord
  | s :: ss, x :: xs, y :: ys => (rcOrderCmp same σ s x y).then (rcOrderKids same σ ss xs ys)
  | _, _, _ => .eq
termination_by structural _ xs _ => xs

end

mutual

/-- The structural order answers `eq` on equal values, of every sort. -/
theorem structuralOrder_refl (σ : Signature S C) :
    ∀ (s : S) (t : Tree (RcLabel C)), structuralOrder σ s t t = .eq
  | s, .node a as => by
    rw [structuralOrder]
    exact nodeCmp_self σ s a fun c => structuralOrderKids_refl σ (σ.asort c) as
termination_by structural _ t => t

theorem structuralOrderKids_refl (σ : Signature S C) :
    ∀ (ss : List S) (ts : List (Tree (RcLabel C))), structuralOrderKids σ ss ts ts = .eq
  | s :: ss, t :: ts => by
    rw [structuralOrderKids, structuralOrder_refl σ s t, structuralOrderKids_refl σ ss ts]
    rfl
  | [], _ => by simp [structuralOrderKids]
  | _ :: _, [] => by simp [structuralOrderKids]
termination_by structural _ ts => ts

end

mutual

/-- **The identity test at every call.**  When `same` holds only of equal values, `rc_order_cmp`
computes the structural order. -/
theorem rcOrderCmp_eq {same : Tree (RcLabel C) → Tree (RcLabel C) → Bool}
    (hsame : ∀ t u, same t u = true → t = u) (σ : Signature S C) :
    ∀ (s : S) (t u : Tree (RcLabel C)), rcOrderCmp same σ s t u = structuralOrder σ s t u
  | s, .node a as, .node b bs => by
    by_cases h : same (.node a as) (.node b bs) = true
    · rw [rcOrderCmp, if_pos h, hsame _ _ h, structuralOrder_refl]
    · rw [rcOrderCmp, if_neg h, structuralOrder]
      exact congrArg (nodeCmp σ s a b) (funext fun c => rcOrderKids_eq hsame σ (σ.asort c) as bs)
termination_by structural _ t _ => t

theorem rcOrderKids_eq {same : Tree (RcLabel C) → Tree (RcLabel C) → Bool}
    (hsame : ∀ t u, same t u = true → t = u) (σ : Signature S C) :
    ∀ (ss : List S) (ts us : List (Tree (RcLabel C))),
      rcOrderKids same σ ss ts us = structuralOrderKids σ ss ts us
  | s :: ss, t :: ts, u :: us => by
    rw [rcOrderKids, structuralOrderKids, rcOrderCmp_eq hsame σ s t u,
      rcOrderKids_eq hsame σ ss ts us]
  | [], _, _ => by simp [rcOrderKids, structuralOrderKids]
  | _ :: _, [], _ => by simp [rcOrderKids, structuralOrderKids]
  | _ :: _, _ :: _, [] => by simp [rcOrderKids, structuralOrderKids]
termination_by structural _ ts _ => ts

end

end Order

/-! ### The signature of the HOL Light module -/

section HolOrder

/-- The sorts that the HOL Light module's comparisons of types and terms meet. -/
inductive HolSort
  | str
  | type
  | tys
  | term
  | tms
  deriving DecidableEq, Repr

/-- The constructors of these sorts, as the module declares them. -/
inductive HolCtor
  | Tyvar
  | Tyapp
  | tynil
  | tycons
  | Var
  | Const
  | Comb
  | Abs
  | tmnil
  | tmcons
  deriving DecidableEq, Repr

/-- The tables of the HOL Light module for these sorts.  Names are byte strings; types, lists of
types, terms and lists of terms are interned nodes.  The rank of a constructor is its position
among the constructors of its sort in the module's declaration: `Tyvar`, `Tyapp`; `tynil`,
`tycons`; `Var`, `Const`, `Comb`, `Abs`; `tmnil`, `tmcons`. -/
def holSig : Signature HolSort HolCtor where
  order
    | .str => .bytes
    | .type | .tys | .term | .tms => .struct
  rank
    | .Tyvar => 0
    | .Tyapp => 1
    | .tynil => 0
    | .tycons => 1
    | .Var => 0
    | .Const => 1
    | .Comb => 2
    | .Abs => 3
    | .tmnil => 0
    | .tmcons => 1
  asort
    | .Tyvar => [.str]
    | .Tyapp => [.str, .tys]
    | .tynil => []
    | .tycons => [.type, .tys]
    | .Var | .Const => [.str, .type]
    | .Comb | .Abs => [.term, .term]
    | .tmnil => []
    | .tmcons => [.term, .tms]

/-- A name as the store holds it: its bytes. -/
def rcTreeOfStr (n : Str) : Tree (RcLabel HolCtor) := .node (.bytes (decodeStr n)) []

mutual

/-- A type as the store holds it: a node of its constructor over its name and its arguments. -/
def rcTreeOfTy : Ty → Tree (RcLabel HolCtor)
  | .Tyvar n => .node (.ctor .Tyvar) [rcTreeOfStr n]
  | .Tyapp n args => .node (.ctor .Tyapp) [rcTreeOfStr n, rcTreeOfTys args]
termination_by structural t => t

/-- A list of types as the store holds it: `tynil`, `tycons` nodes. -/
def rcTreeOfTys : Tys → Tree (RcLabel HolCtor)
  | .tynil => .node (.ctor .tynil) []
  | .tycons x xs => .node (.ctor .tycons) [rcTreeOfTy x, rcTreeOfTys xs]
termination_by structural l => l

end

/-- A term as the store holds it. -/
def rcTreeOfTerm : Term → Tree (RcLabel HolCtor)
  | .Var n ty => .node (.ctor .Var) [rcTreeOfStr n, rcTreeOfTy ty]
  | .Const n ty => .node (.ctor .Const) [rcTreeOfStr n, rcTreeOfTy ty]
  | .Comb f x => .node (.ctor .Comb) [rcTreeOfTerm f, rcTreeOfTerm x]
  | .Abs v b => .node (.ctor .Abs) [rcTreeOfTerm v, rcTreeOfTerm b]

/-- **Names.**  On names, the structural order is `"cmp-str"`. -/
theorem structuralOrder_cmpStr (a b : Str) :
    structuralOrder holSig .str (rcTreeOfStr a) (rcTreeOfStr b) = cmpStr a b := by
  rw [cmpStr_refines]
  exact bytesCmp_eq_nativeCmp _ _

mutual

/-- **Types.**  On types, the structural order is `"cmp-type"`. -/
theorem structuralOrder_cmpType :
    ∀ a b : Ty, structuralOrder holSig .type (rcTreeOfTy a) (rcTreeOfTy b) = cmpType a b
  | .Tyvar x, .Tyvar y => by
    show (structuralOrder holSig .str (rcTreeOfStr x) (rcTreeOfStr y)).then .eq = cmpStr x y
    rw [structuralOrder_cmpStr, then_eq_self]
  | .Tyvar _, .Tyapp _ _ => rfl
  | .Tyapp _ _, .Tyvar _ => rfl
  | .Tyapp n1 a1, .Tyapp n2 a2 => by
    show (structuralOrder holSig .str (rcTreeOfStr n1) (rcTreeOfStr n2)).then
      ((structuralOrder holSig .tys (rcTreeOfTys a1) (rcTreeOfTys a2)).then .eq) = _
    rw [structuralOrder_cmpStr, structuralOrder_cmpTypes a1 a2, then_eq_self, cmpType_Tyapp_Tyapp,
      cmpTypeK_eq_then]
termination_by structural a => a

/-- **Lists of types.**  On lists of types, the structural order is `"cmp-types"`. -/
theorem structuralOrder_cmpTypes :
    ∀ a b : Tys, structuralOrder holSig .tys (rcTreeOfTys a) (rcTreeOfTys b) = cmpTypes a b
  | .tynil, .tynil => rfl
  | .tynil, .tycons _ _ => rfl
  | .tycons _ _, .tynil => rfl
  | .tycons x xs, .tycons y ys => by
    show (structuralOrder holSig .type (rcTreeOfTy x) (rcTreeOfTy y)).then
      ((structuralOrder holSig .tys (rcTreeOfTys xs) (rcTreeOfTys ys)).then .eq) = _
    rw [structuralOrder_cmpType x y, structuralOrder_cmpTypes xs ys, then_eq_self,
      cmpTypes_tycons_tycons, cmpTypesK_eq_then]
termination_by structural a => a

end

/-- **Terms.**  On terms, the structural order is `"cmp-term"`. -/
theorem structuralOrder_cmpTerm :
    ∀ a b : Term, structuralOrder holSig .term (rcTreeOfTerm a) (rcTreeOfTerm b) = cmpTerm a b
  | .Var n1 t1, .Var n2 t2 | .Const n1 t1, .Const n2 t2 => by
    show (structuralOrder holSig .str (rcTreeOfStr n1) (rcTreeOfStr n2)).then
      ((structuralOrder holSig .type (rcTreeOfTy t1) (rcTreeOfTy t2)).then .eq) =
        cmpLeafK (cmpStr n1 n2) t1 t2
    rw [structuralOrder_cmpStr, structuralOrder_cmpType, then_eq_self, cmpLeafK_eq_then]
  | .Comb f1 x1, .Comb f2 x2 => by
    show (structuralOrder holSig .term (rcTreeOfTerm f1) (rcTreeOfTerm f2)).then
      ((structuralOrder holSig .term (rcTreeOfTerm x1) (rcTreeOfTerm x2)).then .eq) = _
    rw [structuralOrder_cmpTerm f1 f2, structuralOrder_cmpTerm x1 x2, then_eq_self,
      cmpTerm_Comb_Comb, cmpTermK_eq_then]
  | .Abs v1 b1, .Abs v2 b2 => by
    show (structuralOrder holSig .term (rcTreeOfTerm v1) (rcTreeOfTerm v2)).then
      ((structuralOrder holSig .term (rcTreeOfTerm b1) (rcTreeOfTerm b2)).then .eq) = _
    rw [structuralOrder_cmpTerm v1 v2, structuralOrder_cmpTerm b1 b2, then_eq_self,
      cmpTerm_Abs_Abs, cmpTermK_eq_then]
  | .Var _ _, .Const _ _ | .Var _ _, .Comb _ _ | .Var _ _, .Abs _ _
  | .Const _ _, .Var _ _ | .Const _ _, .Comb _ _ | .Const _ _, .Abs _ _
  | .Comb _ _, .Var _ _ | .Comb _ _, .Const _ _ | .Comb _ _, .Abs _ _
  | .Abs _ _, .Var _ _ | .Abs _ _, .Const _ _ | .Abs _ _, .Comb _ _ => rfl
termination_by structural a => a

/-- On the trees of types, the structural order answers `eq` exactly on equal types. -/
theorem structuralOrder_eq_iff_ty (a b : Ty) :
    structuralOrder holSig .type (rcTreeOfTy a) (rcTreeOfTy b) = .eq ↔ a = b := by
  rw [structuralOrder_cmpType]
  exact cmpType_eq_iff a b

/-- On the trees of terms, the structural order answers `eq` exactly on equal terms. -/
theorem structuralOrder_eq_iff_term (a b : Term) :
    structuralOrder holSig .term (rcTreeOfTerm a) (rcTreeOfTerm b) = .eq ↔ a = b := by
  rw [structuralOrder_cmpTerm]
  exact cmpTerm_eq_iff a b

/-- **`rc_order_cmp` on types** is `"cmp-type"`, for every identity test that holds only of equal
values. -/
theorem rcOrderCmp_cmpType {same : Tree (RcLabel HolCtor) → Tree (RcLabel HolCtor) → Bool}
    (hsame : ∀ t u, same t u = true → t = u) (a b : Ty) :
    rcOrderCmp same holSig .type (rcTreeOfTy a) (rcTreeOfTy b) = cmpType a b := by
  rw [rcOrderCmp_eq hsame, structuralOrder_cmpType]

/-- **`rc_order_cmp` on terms** is `"cmp-term"`, for every identity test that holds only of equal
values. -/
theorem rcOrderCmp_cmpTerm {same : Tree (RcLabel HolCtor) → Tree (RcLabel HolCtor) → Bool}
    (hsame : ∀ t u, same t u = true → t = u) (a b : Term) :
    rcOrderCmp same holSig .term (rcTreeOfTerm a) (rcTreeOfTerm b) = cmpTerm a b := by
  rw [rcOrderCmp_eq hsame, structuralOrder_cmpTerm]

end HolOrder

/-! ## Memo tables -/

section Memo

variable {K : Type u} {V : Type v} [DecidableEq K]

/-- A memo table: entries of a key and the result kept for it; a failure is kept as `none`. -/
abbrev MemoTable (K : Type u) (V : Type v) : Type (max u v) := List (K × Option V)

/-- `gen_find`: the result kept for a key, found by equality of keys; `none` on a miss. -/
def memoFind : MemoTable K V → K → Option (Option V)
  | [], _ => none
  | (k', r) :: m, k => if k' = k then some r else memoFind m k

/-- **The invariant**: every kept result is the value of `f` at its key. -/
def MemoSound (f : K → Option V) (m : MemoTable K V) : Prop :=
  ∀ e ∈ m, e.2 = f e.1

omit [DecidableEq K] in
theorem memoSound_nil (f : K → Option V) : MemoSound f ([] : MemoTable K V) :=
  fun _ h => absurd h List.not_mem_nil

omit [DecidableEq K] in
theorem MemoSound.cons {f : K → Option V} {m : MemoTable K V} (hm : MemoSound f m) (k : K) :
    MemoSound f ((k, f k) :: m) := by
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · rfl
  · exact hm e he

/-- What a sound table finds for a key is `f` of the key. -/
theorem memoFind_sound {f : K → Option V} {m : MemoTable K V} (hm : MemoSound f m) {k : K}
    {r : Option V} (h : memoFind m k = some r) : r = f k := by
  induction m with
  | nil => exact absurd h nofun
  | cons e m ih =>
    obtain ⟨k', r'⟩ := e
    simp only [memoFind] at h
    split at h
    · rename_i hk
      cases h
      subst hk
      exact hm _ List.mem_cons_self
    · exact ih (fun e he => hm e (List.mem_cons_of_mem _ he)) h

/-- One memoised call: the kept result on a hit; on a miss, the judgment's result `f k`, kept. -/
def memoCall (f : K → Option V) (m : MemoTable K V) (k : K) : Option V × MemoTable K V :=
  match memoFind m k with
  | some r => (r, m)
  | none =>
    let r := f k
    (r, (k, r) :: m)

/-- One call on a sound table answers `f k` and leaves a sound table. -/
theorem memoCall_sound {f : K → Option V} {m : MemoTable K V} (hm : MemoSound f m) (k : K) :
    (memoCall f m k).1 = f k ∧ MemoSound f (memoCall f m k).2 := by
  unfold memoCall
  cases h : memoFind m k with
  | some r => exact ⟨memoFind_sound hm h, hm⟩
  | none => exact ⟨rfl, hm.cons k⟩

/-- An operation on a memo table: a call of the memoised judgment, or `rc_memo_clear`, which runs
before every collection of the interning store. -/
inductive MemoOp (K : Type u) : Type u
  | call (k : K)
  | clear
  deriving DecidableEq, Repr

/-- The key of a call. -/
def MemoOp.key? {K : Type u} : MemoOp K → Option K
  | .call k => some k
  | .clear => none

/-- A run of operations: the answers of its calls in order, and the table at the end. -/
def memoRun (f : K → Option V) :
    MemoTable K V → List (MemoOp K) → List (Option V) × MemoTable K V
  | m, [] => ([], m)
  | m, .call k :: ops =>
    let c := memoCall f m k
    let rest := memoRun f c.2 ops
    (c.1 :: rest.1, rest.2)
  | _, .clear :: ops => memoRun f [] ops

/-- **Memoisation is sound.**  From a table that keeps the invariant, every run of calls and
clearings answers each call with `f` of its key, and leaves a table that keeps the invariant. -/
theorem memo_sound (f : K → Option V) {m : MemoTable K V} (hm : MemoSound f m)
    (ops : List (MemoOp K)) :
    (memoRun f m ops).1 = (ops.filterMap MemoOp.key?).map f ∧
      MemoSound f (memoRun f m ops).2 := by
  induction ops generalizing m with
  | nil => exact ⟨rfl, hm⟩
  | cons op ops ih =>
    cases op with
    | call k =>
      obtain ⟨h₁, h₂⟩ := memoCall_sound hm k
      obtain ⟨ih₁, ih₂⟩ := ih h₂
      refine ⟨?_, ih₂⟩
      show (memoCall f m k).1 :: (memoRun f (memoCall f m k).2 ops).1 = f k :: _
      rw [h₁, ih₁]
    | clear => exact ih (memoSound_nil f)

/-! ### Two generations -/

/-- The two generations of the C tables: new entries go into `cur`. -/
structure Memo2 (K : Type u) (V : Type v) : Type (max u v) where
  /-- The current generation. -/
  cur : MemoTable K V
  /-- The older generation. -/
  old : MemoTable K V
  deriving DecidableEq, Repr

/-- `gen_put` with capacity `cap` (`RC_MEMO_MAX`): when `cur` holds `cap` entries, `old` is
dropped, `cur` becomes `old` and `cur` begins empty; then the entry goes into `cur`. -/
def memoPut2 (cap : Nat) (g : Memo2 K V) (k : K) (r : Option V) : Memo2 K V :=
  if cap ≤ g.cur.length then ⟨[(k, r)], g.cur⟩ else ⟨(k, r) :: g.cur, g.old⟩

/-- `rc_memo_get`: a hit in `cur`; otherwise a hit in `old`, copied into `cur`; otherwise a
miss. -/
def memoGet2 (cap : Nat) (g : Memo2 K V) (k : K) : Option (Option V) × Memo2 K V :=
  match memoFind g.cur k with
  | some r => (some r, g)
  | none =>
    match memoFind g.old k with
    | some r => (some r, memoPut2 cap g k r)
    | none => (none, g)

/-- One memoised call: `rc_memo_get`; on a miss, the judgment's result `f k`, kept by
`rc_memo_put`. -/
def memoCall2 (cap : Nat) (f : K → Option V) (g : Memo2 K V) (k : K) : Option V × Memo2 K V :=
  match memoGet2 cap g k with
  | (some r, g') => (r, g')
  | (none, g') =>
    let r := f k
    (r, memoPut2 cap g' k r)

/-- A run of operations on two generations; `rc_memo_clear` drops both. -/
def memoRun2 (cap : Nat) (f : K → Option V) :
    Memo2 K V → List (MemoOp K) → List (Option V) × Memo2 K V
  | g, [] => ([], g)
  | g, .call k :: ops =>
    let c := memoCall2 cap f g k
    let rest := memoRun2 cap f c.2 ops
    (c.1 :: rest.1, rest.2)
  | _, .clear :: ops => memoRun2 cap f ⟨[], []⟩ ops

/-- The invariant on both generations. -/
def Memo2Sound (f : K → Option V) (g : Memo2 K V) : Prop :=
  MemoSound f g.cur ∧ MemoSound f g.old

omit [DecidableEq K] in
theorem memo2Sound_empty (f : K → Option V) : Memo2Sound f (⟨[], []⟩ : Memo2 K V) :=
  ⟨memoSound_nil f, memoSound_nil f⟩

omit [DecidableEq K] in
theorem memoPut2_sound {f : K → Option V} {g : Memo2 K V} (hg : Memo2Sound f g) (cap : Nat)
    (k : K) : Memo2Sound f (memoPut2 cap g k (f k)) := by
  unfold memoPut2
  split
  · exact ⟨(memoSound_nil f).cons k, hg.1⟩
  · exact ⟨hg.1.cons k, hg.2⟩

theorem memoGet2_sound {f : K → Option V} {g : Memo2 K V} (hg : Memo2Sound f g) (cap : Nat)
    (k : K) :
    (∀ r, (memoGet2 cap g k).1 = some r → r = f k) ∧ Memo2Sound f (memoGet2 cap g k).2 := by
  unfold memoGet2
  cases h : memoFind g.cur k with
  | some r =>
    exact ⟨fun r' hr' => (Option.some.inj hr') ▸ memoFind_sound hg.1 h, hg⟩
  | none =>
    cases h' : memoFind g.old k with
    | some r =>
      have hr : r = f k := memoFind_sound hg.2 h'
      subst hr
      exact ⟨fun r' hr' => (Option.some.inj hr').symm, memoPut2_sound hg cap k⟩
    | none => exact ⟨fun _ hr => absurd hr nofun, hg⟩

/-- A miss leaves both generations as they were.  So when the rules computing `f k` make memoised
calls of their own between the miss and the keeping of `f k`, the tables evolve as in the run with
those calls first and then the call of `k`. -/
theorem memoGet2_miss (cap : Nat) (g : Memo2 K V) (k : K) (h : (memoGet2 cap g k).1 = none) :
    (memoGet2 cap g k).2 = g := by
  revert h
  unfold memoGet2
  cases memoFind g.cur k with
  | some r => exact fun h => absurd h nofun
  | none =>
    cases memoFind g.old k with
    | some r => exact fun h => absurd h nofun
    | none => exact fun _ => rfl

/-- One call on two sound generations answers `f k` and leaves two sound generations. -/
theorem memoCall2_sound {f : K → Option V} {g : Memo2 K V} (hg : Memo2Sound f g) (cap : Nat)
    (k : K) : (memoCall2 cap f g k).1 = f k ∧ Memo2Sound f (memoCall2 cap f g k).2 := by
  obtain ⟨h₁, h₂⟩ := memoGet2_sound hg cap k
  unfold memoCall2
  revert h₁ h₂
  cases memoGet2 cap g k with
  | mk o g' =>
    intro h₁ h₂
    cases o with
    | some r => exact ⟨h₁ r rfl, h₂⟩
    | none => exact ⟨rfl, memoPut2_sound h₂ cap k⟩

/-- **Two generations are sound.**  From two generations that keep the invariant, every run of
calls and clearings answers each call with `f` of its key, whatever the capacity, and leaves two
generations that keep the invariant. -/
theorem memo2_sound (cap : Nat) (f : K → Option V) {g : Memo2 K V} (hg : Memo2Sound f g)
    (ops : List (MemoOp K)) :
    (memoRun2 cap f g ops).1 = (ops.filterMap MemoOp.key?).map f ∧
      Memo2Sound f (memoRun2 cap f g ops).2 := by
  induction ops generalizing g with
  | nil => exact ⟨rfl, hg⟩
  | cons op ops ih =>
    cases op with
    | call k =>
      obtain ⟨h₁, h₂⟩ := memoCall2_sound hg cap k
      obtain ⟨ih₁, ih₂⟩ := ih h₂
      refine ⟨?_, ih₂⟩
      show (memoCall2 cap f g k).1 :: (memoRun2 cap f (memoCall2 cap f g k).2 ops).1 = f k :: _
      rw [h₁, ih₁]
    | clear => exact ih (memo2Sound_empty f)

/-- Both generations hold at most `cap` entries. -/
def Memo2Bounded (cap : Nat) (g : Memo2 K V) : Prop :=
  g.cur.length ≤ cap ∧ g.old.length ≤ cap

omit [DecidableEq K] in
theorem memoPut2_bounded {cap : Nat} (hcap : 0 < cap) {g : Memo2 K V} (hg : Memo2Bounded cap g)
    (k : K) (r : Option V) : Memo2Bounded cap (memoPut2 cap g k r) := by
  unfold memoPut2
  split
  · exact ⟨by simp only [List.length_singleton]; omega, hg.1⟩
  · rename_i h
    exact ⟨by simp only [List.length_cons]; omega, hg.2⟩

theorem memoCall2_bounded {cap : Nat} (hcap : 0 < cap) (f : K → Option V) {g : Memo2 K V}
    (hg : Memo2Bounded cap g) (k : K) : Memo2Bounded cap (memoCall2 cap f g k).2 := by
  unfold memoCall2 memoGet2
  cases memoFind g.cur k with
  | some r => exact hg
  | none =>
    cases memoFind g.old k with
    | some r => exact memoPut2_bounded hcap hg k r
    | none => exact memoPut2_bounded hcap hg k (f k)

/-- **The generations stay bounded.**  With a positive capacity, every run keeps each generation
at most at the capacity. -/
theorem memo2_bounded {cap : Nat} (hcap : 0 < cap) (f : K → Option V) {g : Memo2 K V}
    (hg : Memo2Bounded cap g) (ops : List (MemoOp K)) :
    Memo2Bounded cap (memoRun2 cap f g ops).2 := by
  induction ops generalizing g with
  | nil => exact hg
  | cons op ops ih =>
    cases op with
    | call k => exact ih (memoCall2_bounded hcap f hg k)
    | clear => exact ih ⟨Nat.zero_le _, Nat.zero_le _⟩

end Memo

/-! ## Ordered sets -/

section Sets

variable {α : Type u}

/-! ### The rules

The module's rules over its lists of terms (`tmnil`, `tmcons` are `[]`, `::` here) and its order
`"alphaorder"` (the comparator `cmp` here), one Lean equation per rule.  Each premise but the last
is a `let`, named as in the rule. -/

/-- `"term-union-nil"`, `"term-union-cons-nil"`, and `"term-union-cons-cons"` with its
continuation `"term-union-k-*"` unfolded in place; `termUnion_cons_cons` restates
`"term-union-cons-cons"` as the module writes it, through `termUnionK`. -/
def termUnion (cmp : α → α → Ord) : List α → List α → List α
  | [], l2 => l2                                     -- "term-union-nil"
  | h :: t, [] => h :: t                             -- "term-union-cons-nil"
  | h1 :: t1, h2 :: t2 =>                            -- "term-union-cons-cons"
    match cmp h1 h2 with
    | .eq =>                                         -- "term-union-k-eq"
      let r := termUnion cmp t1 t2
      h1 :: r
    | .lt =>                                         -- "term-union-k-lt"
      let r := termUnion cmp t1 (h2 :: t2)
      h1 :: r
    | .gt =>                                         -- "term-union-k-gt"
      let r := termUnion cmp (h1 :: t1) t2
      h2 :: r
termination_by l1 l2 => l1.length + l2.length

/-- `"term-union-k-*"`. -/
def termUnionK (cmp : α → α → Ord) : Ord → α → List α → α → List α → List α
  | .eq, h1, t1, _, t2 =>                            -- "term-union-k-eq"
    let r := termUnion cmp t1 t2
    h1 :: r
  | .lt, h1, t1, h2, t2 =>                           -- "term-union-k-lt"
    let r := termUnion cmp t1 (h2 :: t2)
    h1 :: r
  | .gt, h1, t1, h2, t2 =>                           -- "term-union-k-gt"
    let r := termUnion cmp (h1 :: t1) t2
    h2 :: r

/-- `"term-union-cons-cons"` as the module states it. -/
theorem termUnion_cons_cons (cmp : α → α → Ord) (h1 : α) (t1 : List α) (h2 : α)
    (t2 : List α) :
    termUnion cmp (h1 :: t1) (h2 :: t2) = termUnionK cmp (cmp h1 h2) h1 t1 h2 t2 := by
  rw [termUnion]
  cases cmp h1 h2 <;> rfl

/-- `"term-remove-nil"`, and `"term-remove-cons"` with its continuation `"term-remove-k-*"`
unfolded in place; `termRemove_cons` restates `"term-remove-cons"` as the module writes it,
through `termRemoveK`. -/
def termRemove (cmp : α → α → Ord) (t : α) : List α → List α
  | [] => []                                         -- "term-remove-nil"
  | s :: ss =>                                       -- "term-remove-cons"
    match cmp t s with
    | .gt =>                                         -- "term-remove-k-gt"
      let r := termRemove cmp t ss
      s :: r
    | .eq => ss                                      -- "term-remove-k-eq"
    | .lt => s :: ss                                 -- "term-remove-k-lt"

/-- `"term-remove-k-*"`. -/
def termRemoveK (cmp : α → α → Ord) : Ord → α → α → List α → List α
  | .gt, t, s, ss =>                                 -- "term-remove-k-gt"
    let r := termRemove cmp t ss
    s :: r
  | .eq, _, _, ss => ss                              -- "term-remove-k-eq"
  | .lt, _, s, ss => s :: ss                         -- "term-remove-k-lt"

/-- `"term-remove-cons"` as the module states it. -/
theorem termRemove_cons (cmp : α → α → Ord) (t s : α) (ss : List α) :
    termRemove cmp t (s :: ss) = termRemoveK cmp (cmp t s) t s ss := by
  rw [termRemove]
  cases cmp t s <;> rfl

/-! ### The component -/

/-- `buf_onto`: the buffer's elements consed onto `tail`, from the last to the first. -/
def bufOnto (buf tail : List α) : List α :=
  buf.foldr (· :: ·) tail

theorem bufOnto_eq (buf tail : List α) : bufOnto buf tail = buf ++ tail := by
  induction buf with
  | nil => rfl
  | cons x xs ih => exact congrArg (x :: ·) ih

/-- The loop of `rc_set_union`: `out` is the buffer of kept heads, `a` and `b` are what is left of
the two lists.  While both are nonempty their heads are compared: `eq` keeps `a`'s head and
advances both, `lt` keeps `a`'s head, `gt` keeps `b`'s head.  Then the buffer goes onto the list
that is left. -/
def unionLoop (cmp : α → α → Ord) : List α → List α → List α → List α
  | out, x :: xs, y :: ys =>
    match cmp x y with
    | .eq => unionLoop cmp (out ++ [x]) xs ys
    | .lt => unionLoop cmp (out ++ [x]) xs (y :: ys)
    | .gt => unionLoop cmp (out ++ [y]) (x :: xs) ys
  | out, x :: xs, [] => bufOnto out (x :: xs)
  | out, [], b => bufOnto out b
termination_by _ a b => a.length + b.length

/-- **`rc_set_union`.** -/
def setUnion (cmp : α → α → Ord) (l1 l2 : List α) : List α :=
  unionLoop cmp [] l1 l2

/-- The loop of `rc_set_remove`: the elements `s` with `cmp t s = gt` are kept and passed; the next
element is dropped if it compares `eq`; then the buffer goes onto what is left. -/
def removeLoop (cmp : α → α → Ord) (t : α) : List α → List α → List α
  | out, [] => bufOnto out []
  | out, s :: ss =>
    match cmp t s with
    | .gt => removeLoop cmp t (out ++ [s]) ss
    | .eq => bufOnto out ss
    | .lt => bufOnto out (s :: ss)

/-- **`rc_set_remove`.** -/
def setRemove (cmp : α → α → Ord) (t : α) (l : List α) : List α :=
  removeLoop cmp t [] l

/-- The loop of `rc_set_union` puts the buffer before the rules' union of what is left. -/
theorem unionLoop_eq (cmp : α → α → Ord) (out a b : List α) :
    unionLoop cmp out a b = out ++ termUnion cmp a b := by
  fun_induction unionLoop cmp out a b with
  | case1 out x xs y ys h ih => simp [termUnion, h, ih]
  | case2 out x xs y ys h ih => simp [termUnion, h, ih]
  | case3 out x xs y ys h ih => simp [termUnion, h, ih]
  | case4 out x xs => simp [termUnion, bufOnto_eq]
  | case5 out b => simp [termUnion, bufOnto_eq]

/-- **Union.**  For every comparator, `rc_set_union` computes the rules of `"term-union"`. -/
theorem setUnion_eq_termUnion (cmp : α → α → Ord) (l1 l2 : List α) :
    setUnion cmp l1 l2 = termUnion cmp l1 l2 := by
  rw [setUnion, unionLoop_eq, List.nil_append]

/-- The loop of `rc_set_remove` puts the buffer before the rules' removal from what is left. -/
theorem removeLoop_eq (cmp : α → α → Ord) (t : α) (out l : List α) :
    removeLoop cmp t out l = out ++ termRemove cmp t l := by
  induction l generalizing out with
  | nil => simp [removeLoop, termRemove, bufOnto_eq]
  | cons s ss ih =>
    cases h : cmp t s <;> simp [removeLoop, termRemove, h, ih, bufOnto_eq]

/-- **Removal.**  For every comparator, `rc_set_remove` computes the rules of `"term-remove"`. -/
theorem setRemove_eq_termRemove (cmp : α → α → Ord) (t : α) (l : List α) :
    setRemove cmp t l = termRemove cmp t l := by
  rw [setRemove, removeLoop_eq, List.nil_append]

end Sets

/-! ## Examples -/

namespace Examples

open RuleModulePrimitives.Examples (nameBool nameFun nameX)
open RuleModuleComparisonLaws.Examples (nameA nameB tyA tyB tyBool funTy varXA varYA varXB)

/-! ### The structural order -/

-- `A -> bool` after `A`: `Tyapp` has the higher rank.
example : structuralOrder holSig .type (rcTreeOfTy (funTy tyA tyBool)) (rcTreeOfTy tyA) = .gt := by
  decide
example : cmpType (funTy tyA tyBool) tyA = .gt := by decide
-- `A -> bool` before `B -> bool`: the names are both `fun`, the first arguments decide.
example : structuralOrder holSig .type (rcTreeOfTy (funTy tyA tyBool))
    (rcTreeOfTy (funTy tyB tyBool)) = .lt := by decide
-- `bool` before `A -> bool`: the names decide, `bool` before `fun` though `bool` is longer.
example : structuralOrder holSig .type (rcTreeOfTy tyBool) (rcTreeOfTy (funTy tyA tyBool)) =
    .lt := by decide
-- Lists of types: the empty list first.
example : structuralOrder holSig .tys (rcTreeOfTys .tynil) (rcTreeOfTys (.tycons tyA .tynil)) =
    .lt := by decide
-- Terms: `x:A` before `x:B` (the names agree, the types decide); `Var` before `Const`; `Comb`
-- before `Abs`.
example : structuralOrder holSig .term (rcTreeOfTerm varXA) (rcTreeOfTerm varXB) = .lt := by decide
example : structuralOrder holSig .term (rcTreeOfTerm (.Const nameX tyA)) (rcTreeOfTerm varXA) =
    .gt := by decide
example : structuralOrder holSig .term (rcTreeOfTerm (.Comb varXA varXA))
    (rcTreeOfTerm (.Abs varXA varXA)) = .lt := by decide
-- Structural, not up to renaming: `λx. x` and `λy. y` differ.
example : structuralOrder holSig .term (rcTreeOfTerm (.Abs varXA varXA))
    (rcTreeOfTerm (.Abs varYA varYA)) = cmpTerm (.Abs varXA varXA) (.Abs varYA varYA) :=
  structuralOrder_cmpTerm _ _
example : cmpTerm (.Abs varXA varXA) (.Abs varYA varYA) = .lt := by decide

/-- The identity test that equal values pass: equality of the trees. -/
def sameValue (t u : Tree (RcLabel HolCtor)) : Bool := decide (t = u)

example : rcOrderCmp sameValue holSig .term (rcTreeOfTerm varXA) (rcTreeOfTerm varXB) =
    cmpTerm varXA varXB :=
  rcOrderCmp_cmpTerm (fun _ _ h => of_decide_eq_true h) _ _
example : rcOrderCmp sameValue holSig .term (rcTreeOfTerm varXA) (rcTreeOfTerm varXA) = .eq := by
  decide

/-- A test that compares the root labels only, and so holds of some values that differ. -/
def sameRoot : Tree (RcLabel HolCtor) → Tree (RcLabel HolCtor) → Bool
  | .node a _, .node b _ => decide (a = b)

-- `sameRoot` holds of `x:A` and `x:B`, which differ; the procedure built on it answers `eq` where
-- the structural order answers `lt`.
example : sameRoot (rcTreeOfTerm varXA) (rcTreeOfTerm varXB) = true ∧
    rcTreeOfTerm varXA ≠ rcTreeOfTerm varXB := by decide
example : rcOrderCmp sameRoot holSig .term (rcTreeOfTerm varXA) (rcTreeOfTerm varXB) = .eq ∧
    structuralOrder holSig .term (rcTreeOfTerm varXA) (rcTreeOfTerm varXB) = .lt := by decide

/-- The module's signature with `Tyapp` ranked before `Tyvar`. -/
def holSigTyappFirst : Signature HolSort HolCtor :=
  { holSig with
    rank := fun
      | .Tyvar => 1
      | .Tyapp => 0
      | c => holSig.rank c }

-- With another rank the order is another: `A` after `bool`, where `"cmp-type"` puts it before.
example : structuralOrder holSigTyappFirst .type (rcTreeOfTy tyA) (rcTreeOfTy tyBool) = .gt := by
  decide
example : cmpType tyA tyBool = .lt := by decide

-- Values that do not fit their sort: two different names compared as types get `eq`.
example : structuralOrder holSig .type (rcTreeOfStr nameA) (rcTreeOfStr nameB) = .eq := by decide
example : structuralOrder holSig .str (rcTreeOfStr nameA) (rcTreeOfStr nameB) = .lt := by decide

/-- A run of the interning store's constructors: `0` the bytes of `A`; `1` the type `A`; `2` the
bytes of `bool`; `3` the empty list of types; `4` `bool`; `5` `[bool]`; `6` `[A, bool]`; `7` the
bytes of `fun`; `8` `A -> bool`. -/
def rcOps : List (Node (RcLabel HolCtor)) :=
  [⟨.bytes (decodeStr nameA), []⟩, ⟨.ctor .Tyvar, [0]⟩,
    ⟨.bytes (decodeStr nameBool), []⟩, ⟨.ctor .tynil, []⟩, ⟨.ctor .Tyapp, [2, 3]⟩,
    ⟨.ctor .tycons, [4, 3]⟩, ⟨.ctor .tycons, [1, 5]⟩,
    ⟨.bytes (decodeStr nameFun), []⟩, ⟨.ctor .Tyapp, [7, 6]⟩]

/-- The store `rcOps` builds. -/
def rcStore : Store (RcLabel HolCtor) := run [] rcOps

example : Interning rcStore := by decide
-- Its nodes read back as the trees of the types they hold.
example : readback rcStore 8 = rcTreeOfTy (funTy tyA tyBool) := by decide
example : readback rcStore 1 = rcTreeOfTy tyA := by decide
-- The order on two of its nodes is `"cmp-type"` on their types.
example : structuralOrder holSig .type (readback rcStore 8) (readback rcStore 1) =
    cmpType (funTy tyA tyBool) tyA := by
  rw [show readback rcStore 8 = rcTreeOfTy (funTy tyA tyBool) by decide,
    show readback rcStore 1 = rcTreeOfTy tyA by decide, structuralOrder_cmpType]

/-! ### Memo tables -/

/-- A partial function: half an even number; an odd number fails. -/
def half (n : Nat) : Option Nat := if n % 2 = 0 then some (n / 2) else none

/-- Calls, a clearing, calls. -/
def memoOps : List (MemoOp Nat) := [.call 4, .call 3, .call 4, .call 3, .clear, .call 6, .call 4]

-- The answers are `half` of the keys, the failures included.
example : (memoRun half [] memoOps).1 = [some 2, none, some 2, none, some 3, some 2] := by decide
example : (memoRun half [] memoOps).1 = (memoOps.filterMap MemoOp.key?).map half :=
  (memo_sound half (memoSound_nil half) memoOps).1
-- The third and fourth calls are answered by the table: after two calls it holds both keys, the
-- failure too.
example : memoFind (memoRun half [] [.call 4, .call 3]).2 4 = some (some 2) ∧
    memoFind (memoRun half [] [.call 4, .call 3]).2 3 = some none := by decide
-- After the clearing it holds only the keys called since.
example : (memoRun half [] memoOps).2 = [(4, some 2), (6, some 3)] := by decide

-- A table that keeps a wrong result answers wrongly: the invariant is needed.
example : ¬ MemoSound half [(4, some 7)] := fun h => absurd (h _ List.mem_cons_self) (by decide)
example : (memoCall half [(4, some 7)] 4).1 = some 7 ∧ half 4 = some 2 := by decide

/-- Calls on two generations of capacity `2`. -/
def memo2Ops : List (MemoOp Nat) := [.call 2, .call 4, .call 6, .call 2, .call 8, .call 4]

-- `2`, `4`: misses, kept in `cur`.  `6`: `cur` is full, becomes `old`, and `6` begins a new `cur`.
-- `2`: a hit in `old`, copied into `cur`.  `8`: `cur` is full again, and the generation holding
-- `4` is dropped.  `4`: a miss, computed again.
example : (memoGet2 2 ⟨[(6, some 3)], [(4, some 2), (2, some 1)]⟩ 2).1 = some (some 1) := by
  decide
example : memoRun2 2 half ⟨[], []⟩ memo2Ops =
    ([some 1, some 2, some 3, some 1, some 4, some 2],
      ⟨[(4, some 2), (8, some 4)], [(2, some 1), (6, some 3)]⟩) := by decide
example : (memoRun2 2 half ⟨[], []⟩ memo2Ops).1 = (memo2Ops.filterMap MemoOp.key?).map half :=
  (memo2_sound 2 half (memo2Sound_empty half) memo2Ops).1
example : Memo2Bounded 2 (memoRun2 2 half ⟨[], []⟩ memo2Ops).2 :=
  memo2_bounded (by decide) half ⟨Nat.zero_le _, Nat.zero_le _⟩ memo2Ops
-- The bound needs a positive capacity: with capacity `0` one call already exceeds it.
example : ¬ Memo2Bounded 0 (memoRun2 0 half ⟨[], []⟩ [.call 2]).2 := by
  unfold Memo2Bounded
  decide

/-! ### Ordered sets

`termUnion` and `unionLoop` recurse on two lists at once, by well-founded recursion, so the
examples that run them are evaluated by the kernel (`decide +kernel`). -/

/-- The order of natural numbers as a comparator. -/
def natOrd (a b : Nat) : Ord := ordOfCompare (compare a b)

example : setUnion natOrd [1, 3, 5] [2, 3, 4] = [1, 2, 3, 4, 5] := by decide +kernel
example : termUnion natOrd [1, 3, 5] [2, 3, 4] = [1, 2, 3, 4, 5] := by decide +kernel
example : setRemove natOrd 3 [1, 3, 5] = [1, 5] := by decide
-- `4` is not there: the walk stops at `5`, which compares `lt`.
example : setRemove natOrd 4 [1, 3, 5] = [1, 3, 5] := by decide
-- One element that compares `eq` is dropped, not every one.
example : setRemove natOrd 2 [1, 2, 2] = [1, 2] := by decide

/-- Entries ordered by their keys alone: entries with equal keys compare `eq`. -/
def byKey (a b : Nat × Nat) : Ord := natOrd a.1 b.1

-- On heads that compare `eq` the union keeps the first list's entry ...
example : setUnion byKey [(1, 0), (2, 0)] [(1, 9), (3, 9)] = [(1, 0), (2, 0), (3, 9)] := by
  decide +kernel
-- ... so it depends on the order of its arguments.
example : setUnion byKey [(1, 9), (3, 9)] [(1, 0), (2, 0)] = [(1, 9), (2, 0), (3, 9)] := by
  decide +kernel
-- Removal drops the entry whose key compares `eq`, whatever its payload.
example : setRemove byKey (1, 7) [(0, 0), (1, 9), (2, 0)] = [(0, 0), (2, 0)] := by decide

-- No property of the comparator is used: one that answers `gt` on every pair puts the second list
-- first, in the component and in the rules alike.
example : setUnion (fun _ _ => .gt) [1, 2] [3, 4] = [3, 4, 1, 2] := by decide +kernel
example : termUnion (fun _ _ => .gt) [1, 2] [3, 4] = [3, 4, 1, 2] := by
  rw [← setUnion_eq_termUnion]
  decide +kernel

-- Removal is not filtering: on a list that is not sorted, the rules stop at the first `lt`.
example : setRemove natOrd 2 [3, 2] = [3, 2] ∧
    [3, 2].filter (fun s => decide (natOrd 2 s ≠ .eq)) = [3] := by decide

end Examples

end Mettapedia.Languages.HOLLight.RuleModuleComponents

#print axioms Mettapedia.Languages.HOLLight.RuleModuleComponents.bytesCmp_eq_nativeCmp
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComponents.nodeCmp_self
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComponents.structuralOrder_refl
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComponents.rcOrderCmp_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComponents.structuralOrder_cmpStr
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComponents.structuralOrder_cmpType
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComponents.structuralOrder_cmpTypes
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComponents.structuralOrder_cmpTerm
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComponents.structuralOrder_eq_iff_ty
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComponents.structuralOrder_eq_iff_term
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComponents.rcOrderCmp_cmpType
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComponents.rcOrderCmp_cmpTerm
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComponents.memoFind_sound
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComponents.memoCall_sound
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComponents.memo_sound
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComponents.memoGet2_miss
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComponents.memoCall2_sound
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComponents.memo2_sound
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComponents.memo2_bounded
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComponents.termUnion_cons_cons
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComponents.termRemove_cons
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComponents.unionLoop_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComponents.removeLoop_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComponents.setUnion_eq_termUnion
#print axioms Mettapedia.Languages.HOLLight.RuleModuleComponents.setRemove_eq_termRemove
