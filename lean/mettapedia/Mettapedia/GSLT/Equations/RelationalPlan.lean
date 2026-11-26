import Mettapedia.GSLT.Equations.RecipeMatching

/-! # Compile constructor matching to a conjunctive query

Each operation occurrence contributes one predicate on a result class and
its argument classes. Internal wires have private addresses. User variables
retain their identities, including repeated ones. The flat plan is exact
regardless of cyclicity of the catalogue or repeated variables of the query.
Its finite scopes can be supplied to a join planner independently of how
the plan is produced or which tuple order is indexed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Equations.RelationalPlan

open UniversalAlgebra RecipeMatching

variable {S : Signature} {C : Type*}

abbrev Wire := Nat ⊕ List Nat

def resolve (vars : Nat → C) (nodes : List Nat → C) : Wire → C
  | .inl v => vars v
  | .inr p => nodes p

def descend (i : Nat) : Wire → Wire
  | .inl v => .inl v
  | .inr p => .inr (i :: p)

@[simp] theorem resolve_descend (vars : Nat → C) (nodes : List Nat → C) (i : Nat) (w : Wire) :
    resolve vars nodes (descend i w) = resolve vars (fun path => nodes (i :: path)) w := by
  cases w <;> rfl

structure Atom (S : Signature) where
  operation : S.Operation
  output : Wire
  inputs : Fin (S.arity operation) → Wire

def Atom.atChild (atom : Atom S) (i : Nat) : Atom S :=
  ⟨atom.operation, descend i atom.output, descend i ∘ atom.inputs⟩

def Atom.holds (g : Catalogue S C) (env : Wire → C) (atom : Atom S) : Prop :=
  (env atom.output, env ∘ atom.inputs) ∈ g.rows atom.operation

def Atom.scope (atom : Atom S) : Finset Wire :=
  insert atom.output ((List.ofFn atom.inputs).toFinset)

/-- The same tuple predicate is ready for either a separator plan or a
general conjunctive join: only its own finite scope matters. -/
theorem Atom.holds_scope (g : Catalogue S C) (atom : Atom S) (one two : Wire → C)
    (agrees : ∀ w ∈ atom.scope, one w = two w) :
    atom.holds g one ↔ atom.holds g two := by
  have sameRoot := agrees atom.output (by simp [Atom.scope])
  have sameInputs : one ∘ atom.inputs = two ∘ atom.inputs := by
    funext i
    apply agrees
    exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨i, rfl⟩))
  simp only [Atom.holds, sameRoot, sameInputs]

@[simp] theorem Atom.holds_atChild (g : Catalogue S C) (vars : Nat → C)
    (nodes : List Nat → C) (atom : Atom S) (i : Nat) :
    (atom.atChild i).holds g (resolve vars nodes) ↔
      atom.holds g (resolve vars (fun path => nodes (i :: path))) := by
  cases atom
  simp only [Atom.atChild, Atom.holds, Function.comp_def, resolve_descend]
  rfl

def output : Term S → Wire
  | .var v => .inl v
  | .op _ _ => .inr []

def compile : Term S → List (Atom S)
  | .var _ => []
  | .op f args =>
    ⟨f, .inr [], fun i => descend i.val (output (args i))⟩ ::
      (List.ofFn fun i => (compile (args i)).map (fun a => a.atChild i.val)).flatten

def query (g : Catalogue S C) (vars : Nat → C) (p : Term S) (root : C) : Prop :=
  ∃ nodes : List Nat → C, resolve vars nodes (output p) = root ∧
    ∀ atom ∈ compile p, atom.holds g (resolve vars nodes)

private theorem child_mem {f : S.Operation} (ps : Fin (S.arity f) → Term S)
    (i : Fin (S.arity f)) (a : Atom S) (mem : a ∈ compile (ps i)) :
    a.atChild i.val ∈ compile (.op f ps) := by
  apply List.mem_cons_of_mem
  apply List.mem_flatten.mpr
  exact ⟨(compile (ps i)).map (fun a => a.atChild i.val), List.mem_ofFn.mpr ⟨i, rfl⟩,
    List.mem_map.mpr ⟨a, mem, rfl⟩⟩

/-- No invented solutions and no lost solutions on the represented domain.
Child-local names are glued by address; repeated pattern variables share
one class throughout, including across otherwise independent branches. -/
theorem query_iff (g : Catalogue S C) (vars : Nat → C) (p : Term S) (root : C) :
    query g vars p root ↔ g.Matches vars p root := by
  induction p generalizing root with
  | var v =>
    constructor
    · rintro ⟨_, value, _⟩
      exact value
    · intro value
      exact ⟨fun _ => root, value, by simp [compile]⟩
  | op f ps ih =>
    constructor
    · rintro ⟨nodes, rootEq, all⟩
      let args := fun i : Fin (S.arity f) =>
        resolve vars (fun path => nodes (i.val :: path)) (output (ps i))
      have top := all _ (List.mem_cons_self (a :=
        Atom.mk f (.inr []) (fun i => descend i.val (output (ps i)))) (l := _))
      have value : nodes [] = root := rootEq
      have topArgs : (nodes [], args) ∈ g.rows f := by
        change (nodes [], fun i => resolve vars nodes (descend i.val (output (ps i)))) ∈ g.rows f at top
        simpa only [resolve_descend, args] using top
      refine ⟨args, value ▸ topArgs, fun i => (ih i (args i)).1 ?_⟩
      exact ⟨fun path => nodes (i.val :: path), rfl, fun a mem =>
        (Atom.holds_atChild g vars nodes a i.val).1 (all _ (child_mem ps i a mem))⟩
    · rintro ⟨args, row, children⟩
      have witness i := (ih i (args i)).2 (children i)
      choose each facts using witness
      let nodes : List Nat → C
        | [] => root
        | i :: path => if within : i < S.arity f then each ⟨i, within⟩ path else root
      have atChild (i : Fin (S.arity f)) : (fun path => nodes (i.val :: path)) = each i := by
        funext path
        simp [nodes, i.isLt]
      refine ⟨nodes, rfl, ?_⟩
      intro a member
      simp only [compile, List.mem_cons, List.mem_flatten, List.mem_ofFn] at member
      rcases member with rfl | ⟨_, ⟨i, rfl⟩, below⟩
      · have same : (fun i : Fin (S.arity f) =>
            resolve vars nodes (descend i.val (output (ps i)))) = args := by
          funext i
          rw [resolve_descend, atChild]
          exact (facts i).1
        change (root, (fun i => resolve vars nodes (descend i.val (output (ps i))))) ∈ g.rows f
        rw [same]
        exact row
      · obtain ⟨child, belongs, rfl⟩ := List.mem_map.mp below
        apply (Atom.holds_atChild g vars nodes child i.val).2
        rw [atChild]
        exact (facts i).2 child belongs

/-- Changes outside the relations used by this pattern cannot affect the
read. An empty relation in scope is still a dependency: changing it from
empty to nonempty is not permitted by the premise. Class labels and the
supplied valuation are held fixed in this statement. -/
theorem matches_stable_on_relations (g h : Catalogue S C) (vars : Nat → C)
    (p : Term S) (root : C)
    (same : ∀ atom ∈ compile p, g.rows atom.operation = h.rows atom.operation) :
    g.Matches vars p root ↔ h.Matches vars p root := by
  rw [← query_iff g, ← query_iff h]
  constructor
  · rintro ⟨nodes, r, facts⟩
    exact ⟨nodes, r, fun a mem => by
      simpa only [Atom.holds, ← same a mem] using facts a mem⟩
  · rintro ⟨nodes, r, facts⟩
    exact ⟨nodes, r, fun a mem => by
      simpa only [Atom.holds, same a mem] using facts a mem⟩

end Mettapedia.GSLT.Equations.RelationalPlan
