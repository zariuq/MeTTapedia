import Mettapedia.Logic.ASP.Circuits
import Mathlib.Algebra.Field.Basic

/-!
# CPOG certificates: certified knowledge compilation, checked

A CPOG certificate (Bryant, Nawrocki, Avigad and Heule, *Certified knowledge
compilation with application to verified model counting*, SAT 2023) proves that
a partitioned-operation graph (POG) is equivalent to an input CNF over its data
variables. This module gives the format as data, an executable checker, and the
proof that an accepted certificate yields a decomposable, deterministic circuit
with the same models as the input, hence the same (weighted) model count.

## The format

The input (`Input`) is a CNF over a finite set of data variables; its clauses
are numbered from 1. A certificate (`Certificate`) is a list of steps (`Step`):

* `prod id v args` declares the extension variable `v` as the product of the
  literals `args`, with the defining clauses `v ∨ ¬a₁ ∨ … ∨ ¬aₖ` (identifier
  `id`) and `¬v ∨ aⱼ` (identifiers `id + j`). The arguments must have pairwise
  disjoint dependency sets.
* `sum id v a b hints` declares `v` as the sum of `a` and `b`, with the defining
  clauses `¬v ∨ a ∨ b`, `v ∨ ¬a`, `v ∨ ¬b` (identifiers `id`, `id + 1`, `id + 2`).
  The hints must be defining clauses and prove `¬a ∨ ¬b` by reverse unit
  propagation: the two arguments have no common model.
* `add id c hints` adds the clause `c`, proved by reverse unit propagation from
  the hinted clauses.
* `delete id hints` deletes the clause `id`, which must not be a defining
  clause, proved by reverse unit propagation from the hinted clauses that
  remain.
* `root r` declares the root literal, once.

A declared variable must be new, and the arguments of a node must be data
variables or earlier nodes. A negated argument, or a negated root, may point to a
data variable or to a product whose graph contains no sum (`negatable`): the
negation of a product of disjoint arguments is again a deterministic,
decomposable sum (`negChain`), while the negation of a sum is not decomposable.
This is the one restriction against the paper's format, which allows any edge to
be negated; the paper's generator negates data variables only. Identifiers of new
clauses must be unused. The certificate is accepted when, at the end, the clauses
other than the defining ones are exactly the unit clause of the root.

Reverse unit propagation reuses the propagation of `CNF` (`Clause.openLits`,
`Clause.unit_sound`, `Clause.conflict_sound`), walking the hints in order.

## Results

* **Hinted reverse unit propagation is sound** (`rup_sound`): if the walk over
  the hints refutes the negation of a clause, every assignment satisfying the
  hints satisfies the clause.
* **The checker's invariant** (`Inv`): the node table is well formed (`Table`),
  every defining clause holds under the extension of every assignment by the node
  definitions (`extend`), and the input holds under an assignment exactly when
  the current clauses hold under its extension. Every step keeps it
  (`step_inv`).
* **Soundness** (`pog_sound`, `check_sound`): if the checker accepts, the POG
  read from the root as a circuit over the data variables (`circuit`) is
  decomposable and deterministic, its variables are data variables, and it has
  the models of the input. The final clauses, read with the extension variables
  existentially quantified, are equivalent to the input (`pog_final_equiv`).
* **Counting** (`weightedCount_eq_amc`, `weightedCount_eq_scaled_amc`,
  `count_eq_amc`): with weights summing to one, the algebraic model count of the
  certified circuit is the weighted count of the input; with other nonzero weight
  sums it is scaled by their product; the model count is `2 ^ n` times the
  circuit evaluated at weight one half, `n` the number of data variables.
* **Counting on the graph** (`litValue_values`, `certifiedValue_sound`,
  `certifiedCount_sound`): the circuit is a tree, so a shared node is read once
  per parent. The executable count instead evaluates each node once, from the
  values of the older nodes (`values`), and is proved equal to the algebraic
  model count of the reading, hence to the (weighted) count of the input.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP.CPOG

open CNF Finset

universe u v

variable {V : Type u}

/-! ## Reverse unit propagation with hints -/

section RUP

variable [DecidableEq V]

/-- The hinted reverse-unit-propagation walk. `α` lists the literals assumed true. A hint with no
literal left open by `α` is falsified and ends the walk with success; a hint with exactly one open
literal is unit and assumes it; any other hint fails the walk. -/
def rupWalk : List (Literal V) → List (Clause V) → Bool
  | _, [] => false
  | α, h :: hs =>
    match h.openLits α with
    | [] => true
    | [l] => rupWalk (l :: α) hs
    | _ :: _ :: _ => false

/-- The clause `c` is a reverse-unit-propagation consequence of the hints: assuming the negation
of `c`, the walk over the hints reaches a falsified hint. -/
def rup (c : Clause V) (hints : List (Clause V)) : Bool := rupWalk (c.map Literal.neg) hints

theorem rupWalk_sound {σ : V → Bool} :
    ∀ {α : List (Literal V)} {hints : List (Clause V)}, rupWalk α hints = true →
      (∀ h ∈ hints, h.eval σ = true) → ¬ Agrees σ α
  | _, [], accepted, _, _ => by simp [rupWalk] at accepted
  | α, h :: hs, accepted, sat, agrees => by
    have hsat : h.eval σ = true := sat h List.mem_cons_self
    unfold rupWalk at accepted
    split at accepted
    · rename_i conflict
      rw [Clause.conflict_sound agrees conflict] at hsat
      cases hsat
    · rename_i l unit
      refine rupWalk_sound accepted (fun h' hh' => sat h' (List.mem_cons_of_mem _ hh')) ?_
      rintro m (_ | ⟨_, hm⟩)
      · exact Clause.unit_sound agrees unit hsat
      · exact agrees m hm
    · cases accepted

/-- **Hinted reverse unit propagation is sound**: an assignment satisfying the hints satisfies the
clause. -/
theorem rup_sound {c : Clause V} {hints : List (Clause V)} (accepted : rup c hints = true) {σ : V → Bool}
    (sat : ∀ h ∈ hints, h.eval σ = true) : c.eval σ = true := by
  cases hc : c.eval σ with
  | true => rfl
  | false =>
    refine absurd ?_ (rupWalk_sound accepted sat)
    intro l hl
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hl
    rw [Literal.eval_neg, Clause.eval_eq_false.mp hc m hm]
    rfl

end RUP

/-! ## Nodes -/

/-- A POG operation: the product of a list of literals, or the sum of two. -/
inductive Node (V : Type u)
  | prod (args : List (Literal V))
  | sum (a b : Literal V)
  deriving DecidableEq, Repr

namespace Node

/-- The arguments of a node. -/
def args : Node V → List (Literal V)
  | prod args => args
  | sum a b => [a, b]

/-- The value of a node, given the values of its arguments. -/
def eval (τ : V → Bool) : Node V → Bool
  | prod args => args.all (Literal.eval τ)
  | sum a b => a.eval τ || b.eval τ

/-- The defining clauses of the node `n` named by the variable `v`: the Tseitin encoding of
`v ↔ n`. -/
def clauses (v : V) : Node V → List (Clause V)
  | prod args => (⟨v, true⟩ :: args.map Literal.neg) :: args.map fun a => [⟨v, false⟩, a]
  | sum a b => [[⟨v, false⟩, a, b], [⟨v, true⟩, a.neg], [⟨v, true⟩, b.neg]]

/-- A node depends only on its arguments. -/
theorem eval_congr {τ τ' : V → Bool} (n : Node V) (same : ∀ a ∈ n.args, τ a.var = τ' a.var) :
    n.eval τ = n.eval τ' := by
  cases n with
  | prod args =>
    simp only [eval]
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    exact forall₂_congr fun a ha => by simp only [Literal.eval, same a ha]
  | sum a b =>
    simp only [eval, Literal.eval, same a (by simp [args]), same b (by simp [args])]

/-- **The defining clauses hold** when the variable has the value of its node. -/
theorem clauses_sound {τ : V → Bool} {v : V} {n : Node V} (hv : τ v = n.eval τ) :
    ∀ c ∈ n.clauses v, c.eval τ = true := by
  intro c hc
  apply Clause.eval_eq_true.mpr
  cases n with
  | prod args =>
    simp only [clauses, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨a, ha, rfl⟩
    · cases hτ : τ v with
      | true => exact ⟨_, List.mem_cons_self, by simp [Literal.eval, hτ]⟩
      | false =>
        rw [hτ, eval, eq_comm, List.all_eq_false] at hv
        obtain ⟨a, ha, fa⟩ := hv
        exact ⟨a.neg, List.mem_cons_of_mem _ (List.mem_map_of_mem ha), by simpa using fa⟩
    · cases hτ : τ v with
      | false => exact ⟨_, List.mem_cons_self, by simp [Literal.eval, hτ]⟩
      | true =>
        rw [hτ, eval, eq_comm, List.all_eq_true] at hv
        exact ⟨a, by simp, hv a ha⟩
  | sum a b =>
    simp only [eval] at hv
    simp only [clauses, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · cases hτ : τ v with
      | false => exact ⟨_, List.mem_cons_self, by simp [Literal.eval, hτ]⟩
      | true =>
        rw [hτ, eq_comm, Bool.or_eq_true] at hv
        rcases hv with ha | hb
        · exact ⟨a, by simp, ha⟩
        · exact ⟨b, by simp, hb⟩
    · cases ha : a.eval τ with
      | false => exact ⟨a.neg, by simp, by simp [ha]⟩
      | true => exact ⟨_, List.mem_cons_self, by rw [Literal.eval_eq_true]; exact hv.trans (by rw [ha, Bool.true_or])⟩
    · cases hb : b.eval τ with
      | false => exact ⟨b.neg, by simp, by simp [hb]⟩
      | true => exact ⟨_, List.mem_cons_self, by rw [Literal.eval_eq_true]; exact hv.trans (by rw [hb, Bool.or_true])⟩

/-- **The defining clauses determine the variable**: where they all hold, the variable has the
value of its node. -/
theorem clauses_complete {τ : V → Bool} {v : V} {n : Node V} (sat : ∀ c ∈ n.clauses v, c.eval τ = true) :
    τ v = n.eval τ := by
  cases n with
  | prod args =>
    have each : ∀ a ∈ args, τ v = true → a.eval τ = true := fun a ha hv => by
      obtain ⟨l, hl, hle⟩ := Clause.eval_eq_true.mp
        (sat [⟨v, false⟩, a] (List.mem_cons_of_mem _ (List.mem_map_of_mem (f := fun a => [⟨v, false⟩, a]) ha)))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · simp [Literal.eval, hv] at hle
      · exact hle
    simp only [eval]
    cases hv : τ v with
    | true => exact (List.all_eq_true.mpr fun a ha => each a ha hv).symm
    | false =>
      obtain ⟨l, hl, hle⟩ := Clause.eval_eq_true.mp (sat _ List.mem_cons_self)
      rcases List.mem_cons.mp hl with rfl | hl
      · simp [Literal.eval, hv] at hle
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hl
        rw [Literal.eval_neg, Bool.not_eq_true'] at hle
        exact (List.all_eq_false.mpr ⟨a, ha, by simp [hle]⟩).symm
  | sum a b =>
    have c1 := sat [⟨v, false⟩, a, b] (by simp [clauses])
    have c2 := sat [⟨v, true⟩, a.neg] (by simp [clauses])
    have c3 := sat [⟨v, true⟩, b.neg] (by simp [clauses])
    simp only [Clause.eval, List.any_cons, List.any_nil, Bool.or_false, Literal.eval_neg] at c1 c2 c3
    simp only [eval]
    cases hv : τ v <;> cases ha : a.eval τ <;> cases hb : b.eval τ <;> simp_all [Literal.eval]

/-- The literals of a defining clause are on the node's variable or on its arguments. -/
theorem var_of_mem_clauses {v : V} {n : Node V} {c : Clause V} (hc : c ∈ n.clauses v) {l : Literal V}
    (hl : l ∈ c) : l.var = v ∨ ∃ a ∈ n.args, l.var = a.var := by
  cases n with
  | prod args =>
    simp only [clauses, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨a, ha, rfl⟩
    · simp only [List.mem_cons, List.mem_map] at hl
      rcases hl with rfl | ⟨a, ha, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨a, ha, rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr ⟨l, ha, rfl⟩
  | sum a b =>
    simp only [clauses, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;>
      rcases hl with rfl | rfl | rfl <;> simp [args]

end Node

/-- A declared node: its variable, its operation, its dependency set (the data variables it
depends on) and whether it may be negated. -/
structure Decl (V : Type u) where
  var : V
  node : Node V
  deps : Finset V
  negatable : Bool

/-! ## The node table -/

section Table

variable [DecidableEq V]

/-- **The extension of an assignment by the node definitions**: every declared variable, oldest
first, takes the value of its node. The table lists the newest declaration first. -/
def extend : List (Decl V) → (V → Bool) → V → Bool
  | [], σ => σ
  | n :: ns, σ => Function.update (extend ns σ) n.var (n.node.eval (extend ns σ))

/-- A variable is known: a data variable or a declared node. -/
def known (S : Finset V) (ns : List (Decl V)) (x : V) : Bool :=
  decide (x ∈ S) || ns.any fun n => decide (n.var = x)

/-- The dependency set of a variable: itself for a data variable, the stored set for a node. -/
def depsOf : List (Decl V) → V → Finset V
  | [], x => {x}
  | n :: ns, x => if x = n.var then n.deps else depsOf ns x

/-- Whether a variable may be negated: a data variable may; a node may when it is marked so. -/
def negatableVar : List (Decl V) → V → Bool
  | [], _ => true
  | n :: ns, x => if x = n.var then n.negatable else negatableVar ns x

/-- A literal may be used as an argument or as the root: it is positive, or its variable may be
negated. -/
def admissible (ns : List (Decl V)) (l : Literal V) : Bool := l.sign || negatableVar ns l.var

/-- The union of the dependency sets of some literals. -/
def argDeps (ns : List (Decl V)) (args : List (Literal V)) : Finset V :=
  args.foldr (fun a d => depsOf ns a.var ∪ d) ∅

/-- A product may be negated when all its arguments may; a sum never. -/
def Node.negatableOver (ns : List (Decl V)) : Node V → Bool
  | .prod args => args.all fun a => negatableVar ns a.var
  | .sum _ _ => false

/-- **The partition condition** of a node: the arguments of a product have pairwise disjoint
dependency sets; the arguments of a sum have no common model, under the extension of every
assignment. -/
def Node.Partitioned (ns : List (Decl V)) : Node V → Prop
  | .prod args => args.Pairwise fun a b => Disjoint (depsOf ns a.var) (depsOf ns b.var)
  | .sum a b => ∀ σ, a.eval (extend ns σ) = true → b.eval (extend ns σ) = false

/-- The side conditions of a declaration, against the older table `ns`. -/
structure DeclOK (S : Finset V) (ns : List (Decl V)) (n : Decl V) : Prop where
  fresh : known S ns n.var = false
  known_args : ∀ a ∈ n.node.args, known S ns a.var = true
  admissible_args : ∀ a ∈ n.node.args, admissible ns a = true
  deps_eq : n.deps = argDeps ns n.node.args
  negatable_eq : n.negatable = n.node.negatableOver ns
  partitioned : n.node.Partitioned ns

/-- **A well-formed node table**: every declaration satisfies its side conditions against the
declarations before it. -/
inductive Table (S : Finset V) : List (Decl V) → Prop
  | nil : Table S []
  | cons {n : Decl V} {ns : List (Decl V)} : DeclOK S ns n → Table S ns → Table S (n :: ns)

theorem known_cons {S : Finset V} {ns : List (Decl V)} (n : Decl V) {x : V} (h : known S ns x = true) :
    known S (n :: ns) x = true := by
  simp only [known, Bool.or_eq_true, decide_eq_true_eq, List.any_cons] at h ⊢
  tauto

theorem known_cons_self (S : Finset V) (ns : List (Decl V)) (n : Decl V) : known S (n :: ns) n.var = true := by
  simp [known]

theorem ne_of_known {S : Finset V} {ns : List (Decl V)} {n : Decl V} (fresh : known S ns n.var = false) {x : V}
    (h : known S ns x = true) : x ≠ n.var := by
  rintro rfl
  rw [fresh] at h
  cases h

theorem known_of_cons {S : Finset V} {ns : List (Decl V)} {n : Decl V} {x : V} (h : known S (n :: ns) x = true)
    (ne : x ≠ n.var) : known S ns x = true := by
  simp only [known, Bool.or_eq_true, decide_eq_true_eq, List.any_cons] at h ⊢
  rcases h with h | h | h
  · exact Or.inl h
  · exact absurd h.symm ne
  · exact Or.inr h

theorem extend_cons_of_ne (n : Decl V) (ns : List (Decl V)) (σ : V → Bool) {x : V} (ne : x ≠ n.var) :
    extend (n :: ns) σ x = extend ns σ x := by
  simp [extend, Function.update_of_ne ne]

theorem extend_cons_self (n : Decl V) (ns : List (Decl V)) (σ : V → Bool) :
    extend (n :: ns) σ n.var = n.node.eval (extend ns σ) := by
  simp [extend]

theorem admissible_cons_of_ne (n : Decl V) (ns : List (Decl V)) {l : Literal V} (ne : l.var ≠ n.var) :
    admissible (n :: ns) l = admissible ns l := by
  simp [admissible, negatableVar, ne]

/-- A clause over variables other than `n.var` has the same value under both extensions. -/
theorem clause_eval_extend_cons {n : Decl V} {ns : List (Decl V)} {c : Clause V} (ne : ∀ l ∈ c, l.var ≠ n.var)
    (σ : V → Bool) : c.eval (extend (n :: ns) σ) = c.eval (extend ns σ) :=
  Clause.eval_congr fun l hl => extend_cons_of_ne n ns σ (ne l hl)

theorem foldr_subset {ns : List (Decl V)} {S : Finset V} :
    ∀ {args : List (Literal V)}, (∀ a ∈ args, depsOf ns a.var ⊆ S) → argDeps ns args ⊆ S
  | [], _ => by simp [argDeps]
  | a :: as, h => by
    simp only [argDeps, List.foldr_cons]
    exact union_subset (h a List.mem_cons_self) (foldr_subset fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- **The dependency set of a known variable consists of data variables.** -/
theorem depsOf_subset {S : Finset V} : ∀ {ns : List (Decl V)}, Table S ns → ∀ x, known S ns x = true →
    depsOf ns x ⊆ S
  | [], _, x, h => by
    simp only [known, List.any_nil, Bool.or_false, decide_eq_true_eq] at h
    simpa [depsOf] using h
  | n :: ns, .cons ok tab, x, h => by
    by_cases hx : x = n.var
    · simp only [depsOf, if_pos hx]
      rw [ok.deps_eq]
      exact foldr_subset fun a ha => depsOf_subset tab a.var (ok.known_args a ha)
    · simp only [depsOf, if_neg hx]
      exact depsOf_subset tab x (known_of_cons h hx)

end Table

/-! ## The POG read as a circuit -/

section Reading

variable [DecidableEq V]

open Circuit

/-- The product of a list of circuits. -/
def prodChain : List (Circuit V) → Circuit V
  | [] => .top
  | c :: cs => .prod c (prodChain cs)

/-- The negation of a product, given each argument with its negation: `¬a₁ + a₁ · (¬a₂ + a₂ · …)`,
a sum whose sides exclude each other. -/
def negChain : List (Circuit V × Circuit V) → Circuit V
  | [] => .bot
  | (p, q) :: cs => .sum q (.prod p (negChain cs))

/-- A node read as a circuit with the given polarity, from the readings `c` of its arguments. -/
def Node.circuit (c : Literal V → Circuit V) : Node V → Bool → Circuit V
  | .prod args, true => prodChain (args.map c)
  | .prod args, false => negChain (args.map fun a => (c a, c a.neg))
  | .sum a b, true => .sum (c a) (c b)
  | .sum a b, false => .prod (c a.neg) (c b.neg)

/-- **The POG read as a circuit over the data variables**: a literal on a node is its operation on
the readings of its arguments, with negation pushed through products; a literal on a data
variable is itself. -/
def circuit : List (Decl V) → Literal V → Circuit V
  | [], l => .lit l.var l.sign
  | n :: ns, l => if l.var = n.var then n.node.circuit (circuit ns) l.sign else circuit ns l

omit [DecidableEq V] in
theorem prodChain_eval (σ : V → Bool) : ∀ cs : List (Circuit V), (prodChain cs).eval σ = cs.all (·.eval σ)
  | [] => rfl
  | c :: cs => by simp [prodChain, Circuit.eval, prodChain_eval σ cs]

omit [DecidableEq V] in
theorem negChain_eval (σ : V → Bool) :
    ∀ cs : List (Circuit V × Circuit V), (∀ p ∈ cs, p.2.eval σ = !p.1.eval σ) →
      (negChain cs).eval σ = !cs.all (·.1.eval σ)
  | [], _ => rfl
  | (p, q) :: cs, h => by
    have hq : q.eval σ = !p.eval σ := h (p, q) List.mem_cons_self
    have rest := negChain_eval σ cs fun r hr => h r (List.mem_cons_of_mem _ hr)
    simp only [negChain, Circuit.eval, hq, rest, List.all_cons]
    cases p.eval σ <;> simp

omit [DecidableEq V] in
theorem Node.circuit_eval {c : Literal V → Circuit V} {σ τ : V → Bool} (hc : ∀ a, (c a).eval σ = a.eval τ)
    (n : Node V) (s : Bool) : (n.circuit c s).eval σ = (n.eval τ == s) := by
  cases n with
  | prod args =>
    cases s
    · rw [Node.circuit, negChain_eval σ _ (by simp [hc])]
      simp [Node.eval, List.all_map, Function.comp_def, hc]
    · simp [Node.circuit, prodChain_eval, Node.eval, List.all_map, Function.comp_def, hc]
  | sum a b =>
    cases s <;> simp [Node.circuit, Circuit.eval, Node.eval, hc]

/-- **The reading evaluates as the literal under the extension.** -/
theorem circuit_eval : ∀ (ns : List (Decl V)) (l : Literal V) (σ : V → Bool),
    (circuit ns l).eval σ = l.eval (extend ns σ)
  | [], l, σ => rfl
  | n :: ns, l, σ => by
    by_cases h : l.var = n.var
    · rw [circuit, if_pos h, Node.circuit_eval (τ := extend ns σ) (fun a => circuit_eval ns a σ)]
      simp [Literal.eval, h, extend_cons_self]
    · rw [circuit, if_neg h, circuit_eval ns l σ]
      simp only [Literal.eval, extend_cons_of_ne n ns σ h]

/-- A circuit is decomposable and deterministic, with variables in `D`. -/
def Good (C : Circuit V) (D : Finset V) : Prop := C.Decomposable ∧ C.Deterministic ∧ C.vars ⊆ D

theorem disjoint_foldr {d : Literal V → Finset V} {X : Finset V} :
    ∀ {args : List (Literal V)}, (∀ b ∈ args, Disjoint X (d b)) → Disjoint X (args.foldr (fun a D => d a ∪ D) ∅)
  | [], _ => by simp
  | a :: as, h => by
    simp only [List.foldr_cons]
    exact disjoint_union_right.mpr ⟨h a List.mem_cons_self, disjoint_foldr fun b hb => h b (List.mem_cons_of_mem _ hb)⟩

theorem prodChain_good {c : Literal V → Circuit V} {d : Literal V → Finset V} :
    ∀ {args : List (Literal V)}, args.Pairwise (fun a b => Disjoint (d a) (d b)) → (∀ a ∈ args, Good (c a) (d a)) →
      Good (prodChain (args.map c)) (args.foldr (fun a D => d a ∪ D) ∅)
  | [], _, _ => ⟨.top, .top, by simp [prodChain, vars]⟩
  | a :: as, pw, h => by
    obtain ⟨apart, pw⟩ := List.pairwise_cons.mp pw
    obtain ⟨da, ta, va⟩ := h a List.mem_cons_self
    obtain ⟨dr, tr, vr⟩ := prodChain_good pw fun b hb => h b (List.mem_cons_of_mem _ hb)
    refine ⟨.prod ?_ da dr, .prod ta tr, ?_⟩
    · exact Disjoint.mono va vr (disjoint_foldr apart)
    · simp only [List.map_cons, prodChain, vars, List.foldr_cons]
      exact union_subset_union va vr

theorem negChain_good {c : Literal V → Circuit V} {d : Literal V → Finset V} :
    ∀ {args : List (Literal V)}, args.Pairwise (fun a b => Disjoint (d a) (d b)) →
      (∀ a ∈ args, Good (c a) (d a) ∧ Good (c a.neg) (d a) ∧ ∀ σ, (c a.neg).eval σ = !(c a).eval σ) →
      Good (negChain (args.map fun a => (c a, c a.neg))) (args.foldr (fun a D => d a ∪ D) ∅)
  | [], _, _ => ⟨.bot, .bot, by simp [negChain, vars]⟩
  | a :: as, pw, h => by
    obtain ⟨apart, pw⟩ := List.pairwise_cons.mp pw
    obtain ⟨⟨da, ta, va⟩, ⟨dn, tn, vn⟩, compl⟩ := h a List.mem_cons_self
    obtain ⟨dr, tr, vr⟩ := negChain_good pw fun b hb => h b (List.mem_cons_of_mem _ hb)
    refine ⟨.sum dn (.prod ?_ da dr), .sum ?_ tn (.prod ta tr), ?_⟩
    · exact Disjoint.mono va vr (disjoint_foldr apart)
    · intro σ hn
      rw [compl σ, Bool.not_eq_true'] at hn
      simp [Circuit.eval, hn]
    · simp only [List.map_cons, negChain, vars, List.foldr_cons]
      exact union_subset (vn.trans subset_union_left) (union_subset_union va vr)

/-- **The reading of an admissible literal is decomposable and deterministic**, with variables in
the literal's dependency set. -/
theorem circuit_good {S : Finset V} : ∀ {ns : List (Decl V)}, Table S ns →
    ∀ l : Literal V, admissible ns l = true → Good (circuit ns l) (depsOf ns l.var)
  | [], _, l, _ => ⟨.lit _ _, .lit _ _, by simp [circuit, vars, depsOf]⟩
  | n :: ns, .cons ok tab, l, adm => by
    by_cases h : l.var = n.var
    · have hneg : l.sign = false → n.negatable = true := fun hs => by
        simpa [admissible, negatableVar, hs, h] using adm
      have ih := circuit_good tab
      obtain ⟨_, _, admArgs, depsEq, negEq, part⟩ := ok
      rcases l with ⟨x, s⟩
      simp only at h hneg
      subst h
      simp only [circuit, depsOf, if_true]
      rw [depsEq]
      rcases n with ⟨v, node, D, ng⟩
      simp only at admArgs depsEq negEq part hneg ⊢
      cases node with
      | prod args =>
        cases s with
        | true => exact prodChain_good part fun a ha => ih a (admArgs a ha)
        | false =>
          have all : ∀ a ∈ args, negatableVar ns a.var = true := by
            have := hneg rfl
            rw [negEq] at this
            simpa [Node.negatableOver, List.all_eq_true] using this
          refine negChain_good part fun a ha => ⟨ih a (admArgs a ha), ?_, fun σ => ?_⟩
          · exact ih a.neg (by simp [admissible, all a ha])
          · rw [circuit_eval, circuit_eval, Literal.eval_neg]
      | sum a b =>
        cases s with
        | false =>
          have := hneg rfl
          rw [negEq] at this
          cases this
        | true =>
          obtain ⟨da, ta, va⟩ := ih a (admArgs a (by simp [Node.args]))
          obtain ⟨db, tb, vb⟩ := ih b (admArgs b (by simp [Node.args]))
          refine ⟨.sum da db, .sum (fun σ ha => ?_) ta tb, ?_⟩
          · rw [circuit_eval] at ha ⊢
            exact part σ ha
          · simp only [Node.circuit, vars, Node.args, argDeps, List.foldr_cons, List.foldr_nil, union_empty]
            exact union_subset_union va vb
    · simp only [circuit, depsOf, if_neg h]
      exact circuit_good tab l (by rwa [admissible_cons_of_ne n ns h] at adm)

end Reading

/-! ## The checker -/

/-- Where a clause of the checker's store comes from. -/
inductive Kind
  | input
  | asserted
  | defining
  deriving DecidableEq, Repr

/-- A clause of the checker's store, with its origin. -/
structure Entry (V : Type u) where
  clause : Clause V
  kind : Kind
  deriving DecidableEq, Repr

/-- **The input**: a CNF over a finite set of data variables. -/
structure Input (V : Type u) where
  vars : Finset V
  cnf : Formula V

/-- **A certificate step.** -/
inductive Step (V : Type u)
  /-- Declare a product node, with the identifier of its first defining clause. -/
  | prod (id : ℕ) (v : V) (args : List (Literal V))
  /-- Declare a sum node, with the hints proving that its arguments exclude each other. -/
  | sum (id : ℕ) (v : V) (a b : Literal V) (hints : List ℕ)
  /-- Add a clause, with its reverse-unit-propagation hints. -/
  | add (id : ℕ) (c : Clause V) (hints : List ℕ)
  /-- Delete a clause, with reverse-unit-propagation hints among the remaining clauses. -/
  | delete (id : ℕ) (hints : List ℕ)
  /-- Declare the root literal. -/
  | root (r : Literal V)
  deriving Repr

/-- **A CPOG certificate**: its steps, in order. -/
abbrev Certificate (V : Type u) := List (Step V)

/-- The checker's state: the clause store with identifiers, the node table (newest first), and
the root once declared. -/
structure State (V : Type u) where
  store : List (ℕ × Entry V)
  nodes : List (Decl V)
  root : Option (Literal V)

/-- Number a list from `i`. -/
def number {α : Type v} : ℕ → List α → List (ℕ × α)
  | _, [] => []
  | i, a :: as => (i, a) :: number (i + 1) as

theorem mem_number {α : Type v} : ∀ {i : ℕ} {as : List α} {p : ℕ × α}, p ∈ number i as → p.2 ∈ as
  | _, [], _, h => by simp [number] at h
  | i, a :: as, p, h => by
    simp only [number, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_number h)

theorem exists_mem_number {α : Type v} : ∀ {i : ℕ} {as : List α} {a : α}, a ∈ as → ∃ p ∈ number i as, p.2 = a
  | _, [], _, h => by cases h
  | i, b :: as, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨(i, a), List.mem_cons_self, rfl⟩
    · obtain ⟨p, hp, hpa⟩ := exists_mem_number (i := i + 1) h
      exact ⟨p, List.mem_cons_of_mem _ hp, hpa⟩

theorem map_snd_number {α : Type v} : ∀ (i : ℕ) (as : List α), (number i as).map Prod.snd = as
  | _, [] => rfl
  | i, a :: as => by simp [number, map_snd_number (i + 1) as]

/-- The clauses of a store. -/
def clausesOf (store : List (ℕ × Entry V)) : Formula V := store.map (·.2.clause)

theorem mem_clausesOf {store : List (ℕ × Entry V)} {c : Clause V} :
    c ∈ clausesOf store ↔ ∃ p ∈ store, p.2.clause = c := by
  simp [clausesOf]

section Checker

variable [DecidableEq V]

/-- The initial state: the input clauses, numbered from 1. -/
def init (I : Input V) : State V :=
  { store := number 1 (I.cnf.map fun c => ⟨c, .input⟩), nodes := [], root := none }

/-- The identifiers are not in use. -/
def freshIds (store : List (ℕ × Entry V)) (ids : List ℕ) : Bool := ids.all fun i => store.all fun p => p.1 != i

/-- The clauses named by the hints, each required to satisfy `ok`. -/
def hintClauses (store : List (ℕ × Entry V)) (ok : Entry V → Bool) : List ℕ → Option (List (Clause V))
  | [] => some []
  | i :: is =>
    match store.find? (·.1 == i) with
    | some p => if ok p.2 then (hintClauses store ok is).map (p.2.clause :: ·) else none
    | none => none

omit [DecidableEq V] in
theorem hintClauses_mem {store : List (ℕ × Entry V)} {ok : Entry V → Bool} :
    ∀ {ids : List ℕ} {hs : List (Clause V)}, hintClauses store ok ids = some hs →
      ∀ c ∈ hs, ∃ p ∈ store, ok p.2 = true ∧ p.2.clause = c
  | [], hs, h, c, hc => by
    simp only [hintClauses, Option.some.injEq] at h
    subst h
    cases hc
  | i :: is, hs, h, c, hc => by
    simp only [hintClauses] at h
    split at h
    · rename_i p hp
      split at h
      · rename_i hok
        obtain ⟨rest, hrest, rfl⟩ := Option.map_eq_some_iff.mp h
        rcases List.mem_cons.mp hc with rfl | hc
        · exact ⟨p, List.mem_of_find?_eq_some hp, hok, rfl⟩
        · exact hintClauses_mem hrest c hc
      · cases h
    · cases h

/-- The defining clauses of the node `node` named by `v`, numbered from `id`. -/
def definingEntries (id : ℕ) (v : V) (node : Node V) : List (ℕ × Entry V) :=
  number id ((node.clauses v).map fun c => ⟨c, .defining⟩)

/-- Declare the node `node` as the variable `v`, its defining clauses numbered from `id`. The
variable must be new, the arguments known and admissible, and the identifiers unused. -/
def declare (S : Finset V) (st : State V) (id : ℕ) (v : V) (node : Node V) : Option (State V) :=
  if known S st.nodes v = false ∧ (∀ a ∈ node.args, known S st.nodes a.var = true ∧ admissible st.nodes a = true) ∧
      freshIds st.store ((definingEntries id v node).map Prod.fst) = true then
    some { store := definingEntries id v node ++ st.store
           nodes := ⟨v, node, argDeps st.nodes node.args, node.negatableOver st.nodes⟩ :: st.nodes
           root := st.root }
  else none

/-- **One step of the checker.** -/
def step (S : Finset V) (st : State V) : Step V → Option (State V)
  | .prod id v args =>
    if args.Pairwise fun a b => Disjoint (depsOf st.nodes a.var) (depsOf st.nodes b.var) then
      declare S st id v (.prod args)
    else none
  | .sum id v a b hints =>
    match hintClauses st.store (fun e => decide (e.kind = .defining)) hints with
    | some hs => if rup [a.neg, b.neg] hs = true then declare S st id v (.sum a b) else none
    | none => none
  | .add id c hints =>
    match hintClauses st.store (fun _ => true) hints with
    | some hs =>
      if freshIds st.store [id] = true ∧ (∀ l ∈ c, known S st.nodes l.var = true) ∧ rup c hs = true then
        some { st with store := (id, ⟨c, .asserted⟩) :: st.store }
      else none
    | none => none
  | .delete id hints =>
    match st.store.find? (·.1 == id) with
    | some p =>
      if p.2.kind = .defining then none
      else
        match hintClauses (st.store.erase p) (fun _ => true) hints with
        | some hs => if rup p.2.clause hs = true then some { st with store := st.store.erase p } else none
        | none => none
    | none => none
  | .root r =>
    if st.root = none ∧ known S st.nodes r.var = true ∧ admissible st.nodes r = true then
      some { st with root := some r }
    else none

/-- Run the steps in order. -/
def run (S : Finset V) : State V → Certificate V → Option (State V)
  | st, [] => some st
  | st, s :: ss => (step S st s).bind fun st' => run S st' ss

/-- The final condition: a root was declared, and the clauses other than the defining ones are
exactly its unit clause. Returns the root. -/
def finish (st : State V) : Option (Literal V) :=
  match st.root with
  | some r => if clausesOf (st.store.filter fun p => p.2.kind != .defining) = [[r]] then some r else none
  | none => none

/-- The input clauses are over the data variables. -/
def wellFormed (I : Input V) : Bool := I.cnf.all fun c => c.all fun l => decide (l.var ∈ I.vars)

/-- **The accepted POG**: the final node table and the root, if the input is well formed and the
certificate is accepted. -/
def accept (I : Input V) (cert : Certificate V) : Option (List (Decl V) × Literal V) :=
  if wellFormed I = true then
    (run I.vars (init I) cert).bind fun st => (finish st).map fun r => (st.nodes, r)
  else none

/-- **The certified POG**: the circuit read from the root, if the certificate is accepted. -/
def pog (I : Input V) (cert : Certificate V) : Option (Circuit V) :=
  (accept I cert).map fun p => circuit p.1 p.2

/-- **The CPOG checker.** -/
def check (I : Input V) (cert : Certificate V) : Bool := (pog I cert).isSome

/-! ## The invariant -/

/-- **The checker's invariant.** The node table is well formed; the clauses of the store mention
known variables only; every defining clause holds under the extension of every assignment; the
input holds under an assignment exactly when the store holds under its extension; a declared root
is known and admissible; every defining clause of every node is in the store. -/
structure Inv (I : Input V) (st : State V) : Prop where
  table : Table I.vars st.nodes
  known_store : ∀ p ∈ st.store, ∀ l ∈ p.2.clause, known I.vars st.nodes l.var = true
  defining : ∀ p ∈ st.store, p.2.kind = .defining → ∀ σ, p.2.clause.eval (extend st.nodes σ) = true
  equiv : ∀ σ, I.cnf.eval σ = (clausesOf st.store).eval (extend st.nodes σ)
  root : ∀ r, st.root = some r → known I.vars st.nodes r.var = true ∧ admissible st.nodes r = true
  complete : ∀ n ∈ st.nodes, ∀ c ∈ n.node.clauses n.var, ∃ p ∈ st.store, p.2.kind = .defining ∧ p.2.clause = c

theorem init_inv {I : Input V} (wf : wellFormed I = true) : Inv I (init I) where
  table := .nil
  known_store := by
    intro p hp l hl
    obtain ⟨c, hc, hpc⟩ := List.mem_map.mp (mem_number hp)
    rw [← hpc] at hl
    have := List.all_eq_true.mp (List.all_eq_true.mp wf c hc) l hl
    simp only [decide_eq_true_eq] at this
    simp [known, this]
  defining := by
    intro p hp hk
    obtain ⟨c, _, hpc⟩ := List.mem_map.mp (mem_number hp)
    rw [← hpc] at hk
    cases hk
  equiv := by
    intro σ
    have : clausesOf (init I).store = I.cnf := by
      rw [init, clausesOf, show (fun p : ℕ × Entry V => p.2.clause) = Entry.clause ∘ Prod.snd from rfl,
        ← List.map_map, map_snd_number, List.map_map]
      simp [Function.comp_def]
    rw [this]
    rfl
  root := by
    intro r hr
    cases hr
  complete := by
    intro n hn
    cases hn

omit [DecidableEq V] in
theorem formula_eval_cons_entry (τ : V → Bool) (p : ℕ × Entry V) (store : List (ℕ × Entry V)) :
    (clausesOf (p :: store)).eval τ = (p.2.clause.eval τ && (clausesOf store).eval τ) := rfl

omit [DecidableEq V] in
theorem formula_eval_append (τ : V → Bool) (A B : List (ℕ × Entry V)) :
    (clausesOf (A ++ B)).eval τ = ((clausesOf A).eval τ && (clausesOf B).eval τ) := by
  simp [clausesOf, Formula.eval_append]

omit [DecidableEq V] in
/-- The clauses named by hints hold wherever the store holds. -/
theorem hints_sat {store : List (ℕ × Entry V)} {ok : Entry V → Bool} {ids : List ℕ} {hs : List (Clause V)}
    (h : hintClauses store ok ids = some hs) {τ : V → Bool} (sat : (clausesOf store).eval τ = true) :
    ∀ c ∈ hs, c.eval τ = true := by
  intro c hc
  obtain ⟨p, hp, _, rfl⟩ := hintClauses_mem h c hc
  exact Formula.eval_eq_true.mp sat _ (mem_clausesOf.mpr ⟨p, hp, rfl⟩)

theorem declare_inv {I : Input V} {st st' : State V} {id : ℕ} {v : V} {node : Node V} (inv : Inv I st)
    (part : node.Partitioned st.nodes) (h : declare I.vars st id v node = some st') : Inv I st' := by
  unfold declare at h
  split at h
  · rename_i cond
    obtain ⟨fresh, args, _⟩ := cond
    cases h
    set n : Decl V := ⟨v, node, argDeps st.nodes node.args, node.negatableOver st.nodes⟩ with hn
    have freshN : known I.vars st.nodes n.var = false := fresh
    have argsNe : ∀ a ∈ node.args, a.var ≠ v := fun a ha => ne_of_known freshN (args a ha).1
    have oldNe : ∀ p ∈ st.store, ∀ l ∈ p.2.clause, l.var ≠ n.var :=
      fun p hp l hl => ne_of_known freshN (inv.known_store p hp l hl)
    have newDef : ∀ p ∈ definingEntries id v node,
        p.2.clause ∈ node.clauses v ∧ p.2.kind = .defining := by
      intro p hp
      obtain ⟨c, hc, hpc⟩ := List.mem_map.mp (mem_number hp)
      rw [← hpc]
      exact ⟨hc, rfl⟩
    have newSat : ∀ σ, ∀ c ∈ node.clauses v, c.eval (extend (n :: st.nodes) σ) = true := by
      intro σ
      apply Node.clauses_sound
      rw [show v = n.var from rfl, extend_cons_self]
      exact Node.eval_congr node fun a ha => (extend_cons_of_ne n st.nodes σ (argsNe a ha)).symm
    refine ⟨.cons ⟨freshN, fun a ha => (args a ha).1, fun a ha => (args a ha).2, rfl, rfl, part⟩ inv.table,
      ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp l hl
      rcases List.mem_append.mp hp with hp | hp
      · rcases Node.var_of_mem_clauses (newDef p hp).1 hl with hv | ⟨a, ha, hv⟩
        · rw [hv]
          exact known_cons_self _ _ n
        · rw [hv]
          exact known_cons n (args a ha).1
      · exact known_cons n (inv.known_store p hp l hl)
    · intro p hp hk σ
      rcases List.mem_append.mp hp with hp | hp
      · exact newSat σ _ (newDef p hp).1
      · rw [clause_eval_extend_cons (oldNe p hp)]
        exact inv.defining p hp hk σ
    · intro σ
      have newTrue : (clausesOf (definingEntries id v node)).eval
          (extend (n :: st.nodes) σ) = true := by
        apply Formula.eval_eq_true.mpr
        intro c hc
        obtain ⟨p, hp, rfl⟩ := mem_clausesOf.mp hc
        exact newSat σ _ (newDef p hp).1
      have oldSame : (clausesOf st.store).eval (extend (n :: st.nodes) σ) = (clausesOf st.store).eval (extend st.nodes σ) :=
        Formula.eval_congr fun c hc l hl => by
          obtain ⟨p, hp, rfl⟩ := mem_clausesOf.mp hc
          exact extend_cons_of_ne n st.nodes σ (oldNe p hp l hl)
      simp only
      rw [formula_eval_append, newTrue, oldSame, Bool.true_and]
      exact inv.equiv σ
    · intro r hr
      obtain ⟨kr, ar⟩ := inv.root r hr
      have ne := ne_of_known freshN kr
      exact ⟨known_cons n kr, by rw [admissible_cons_of_ne n st.nodes ne]; exact ar⟩
    · intro m hm c hc
      rcases List.mem_cons.mp hm with rfl | hm
      · obtain ⟨q, hq, hqc⟩ := exists_mem_number (i := id)
          (List.mem_map_of_mem (f := fun c => (⟨c, .defining⟩ : Entry V)) (show c ∈ node.clauses v from hc))
        exact ⟨q, List.mem_append_left _ hq, by rw [hqc], by rw [hqc]⟩
      · obtain ⟨q, hq, hk, hqc⟩ := inv.complete m hm c hc
        exact ⟨q, List.mem_append_right _ hq, hk, hqc⟩
  · cases h

/-- **Every step keeps the invariant.** -/
theorem step_inv {I : Input V} {st st' : State V} (inv : Inv I st) :
    ∀ {s : Step V}, step I.vars st s = some st' → Inv I st'
  | .prod id v args, h => by
    simp only [step] at h
    split at h
    · exact declare_inv inv ‹_› h
    · cases h
  | .sum id v a b hints, h => by
    simp only [step] at h
    split at h
    · rename_i hs hhs
      split at h
      · rename_i accepted
        have part : ∀ σ, a.eval (extend st.nodes σ) = true → b.eval (extend st.nodes σ) = false := by
          intro σ ha
          have sat : ∀ c ∈ hs, c.eval (extend st.nodes σ) = true := by
            intro c hc
            obtain ⟨p, hp, hk, rfl⟩ := hintClauses_mem hhs c hc
            exact inv.defining p hp (by simpa using hk) σ
          have := rup_sound accepted sat
          simp only [Clause.eval, List.any_cons, List.any_nil, Bool.or_false, Literal.eval_neg, ha,
            Bool.not_true, Bool.false_or, Bool.not_eq_true'] at this
          exact this
        exact declare_inv (node := .sum a b) inv part h
      · cases h
    · cases h
  | .add id c hints, h => by
    simp only [step] at h
    split at h
    · rename_i hs hhs
      split at h
      · rename_i cond
        obtain ⟨_, kc, accepted⟩ := cond
        cases h
        refine ⟨inv.table, ?_, ?_, ?_, inv.root, fun m hm c hc => ?_⟩
        · intro p hp l hl
          rcases List.mem_cons.mp hp with rfl | hp
          · exact kc l hl
          · exact inv.known_store p hp l hl
        · intro p hp hk σ
          rcases List.mem_cons.mp hp with rfl | hp
          · cases hk
          · exact inv.defining p hp hk σ
        · intro σ
          rw [formula_eval_cons_entry, inv.equiv σ]
          cases hF : (clausesOf st.store).eval (extend st.nodes σ) with
          | false => simp
          | true => simp [rup_sound accepted (hints_sat hhs hF)]
        · obtain ⟨q, hq, hk, hqc⟩ := inv.complete m hm c hc
          exact ⟨q, List.mem_cons_of_mem _ hq, hk, hqc⟩
      · cases h
    · cases h
  | .delete id hints, h => by
    simp only [step] at h
    split at h
    · rename_i p hp
      have mem : p ∈ st.store := List.mem_of_find?_eq_some hp
      split at h
      · cases h
      · rename_i notDef
        split at h
        · rename_i hs hhs
          split at h
          · rename_i accepted
            cases h
            refine ⟨inv.table, fun q hq => inv.known_store q (List.mem_of_mem_erase hq),
              fun q hq => inv.defining q (List.mem_of_mem_erase hq), ?_, inv.root, fun m hm c hc => ?_⟩
            swap
            · obtain ⟨q, hq, hk, hqc⟩ := inv.complete m hm c hc
              have ne : q ≠ p := by
                rintro rfl
                exact notDef hk
              exact ⟨q, (List.mem_erase_of_ne ne).mpr hq, hk, hqc⟩
            intro σ
            rw [inv.equiv σ]
            apply Bool.eq_iff_iff.mpr
            simp only [Formula.eval_eq_true, mem_clausesOf]
            constructor
            · rintro sat c ⟨q, hq, rfl⟩
              exact sat _ ⟨q, List.mem_of_mem_erase hq, rfl⟩
            · rintro sat c ⟨q, hq, rfl⟩
              by_cases same : q = p
              · subst same
                exact rup_sound accepted (hints_sat hhs (Formula.eval_eq_true.mpr fun c hc => by
                  obtain ⟨q', hq', rfl⟩ := mem_clausesOf.mp hc
                  exact sat _ ⟨q', hq', rfl⟩))
              · exact sat _ ⟨q, (List.mem_erase_of_ne same).mpr hq, rfl⟩
          · cases h
        · cases h
    · cases h
  | .root r, h => by
    simp only [step] at h
    split at h
    · rename_i cond
      obtain ⟨_, kr, ar⟩ := cond
      cases h
      refine ⟨inv.table, inv.known_store, inv.defining, inv.equiv, ?_, inv.complete⟩
      intro r' hr'
      cases hr'
      exact ⟨kr, ar⟩
    · cases h

theorem run_inv {I : Input V} : ∀ {st st' : State V} {cert : Certificate V}, Inv I st →
    run I.vars st cert = some st' → Inv I st'
  | _, _, [], inv, h => by
    cases h
    exact inv
  | st, st', s :: ss, inv, h => by
    simp only [run, Option.bind_eq_some_iff] at h
    obtain ⟨mid, hmid, rest⟩ := h
    exact run_inv (step_inv inv hmid) rest

/-- At the end, the store holds under the extension of an assignment exactly when the root does. -/
theorem finish_eval {I : Input V} {st : State V} {r : Literal V} (inv : Inv I st) (h : finish st = some r)
    (σ : V → Bool) : (clausesOf st.store).eval (extend st.nodes σ) = r.eval (extend st.nodes σ) := by
  unfold finish at h
  split at h
  · split at h
    · rename_i rest
      cases h
      have filtered : (clausesOf (st.store.filter fun p => p.2.kind != .defining)).eval (extend st.nodes σ) =
          r.eval (extend st.nodes σ) := by
        rw [rest]
        simp [Clause.eval]
      rw [← filtered]
      apply Bool.eq_iff_iff.mpr
      simp only [Formula.eval_eq_true, mem_clausesOf, List.mem_filter]
      constructor
      · rintro sat c ⟨q, ⟨hq, _⟩, rfl⟩
        exact sat _ ⟨q, hq, rfl⟩
      · rintro sat c ⟨q, hq, rfl⟩
        by_cases hk : q.2.kind = .defining
        · exact inv.defining q hq hk σ
        · exact sat _ ⟨q, ⟨hq, by simpa using hk⟩, rfl⟩
    · cases h
  · cases h

theorem finish_root {st : State V} {r : Literal V} (h : finish st = some r) : st.root = some r := by
  unfold finish at h
  split at h
  · split at h
    · cases h
      assumption
    · cases h
  · cases h

theorem finish_clauses {st : State V} {r : Literal V} (h : finish st = some r) :
    clausesOf (st.store.filter fun p => p.2.kind != .defining) = [[r]] := by
  unfold finish at h
  split at h
  · split at h
    · cases h
      assumption
    · cases h
  · cases h

/-- The accepted run: the final state, its invariant and its root. -/
theorem accept_eq_some {I : Input V} {cert : Certificate V} {ns : List (Decl V)} {r : Literal V}
    (h : accept I cert = some (ns, r)) :
    ∃ st, run I.vars (init I) cert = some st ∧ finish st = some r ∧ ns = st.nodes ∧ Inv I st ∧
      wellFormed I = true := by
  unfold accept at h
  split at h
  · rename_i wf
    obtain ⟨st, hst, hr⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r', hr', hpair⟩ := Option.map_eq_some_iff.mp hr
    cases hpair
    exact ⟨st, hst, hr', rfl, run_inv (init_inv wf) hst, wf⟩
  · cases h

theorem pog_eq_some {I : Input V} {cert : Certificate V} {C : Circuit V} (h : pog I cert = some C) :
    ∃ st r, run I.vars (init I) cert = some st ∧ finish st = some r ∧ C = circuit st.nodes r ∧ Inv I st ∧
      wellFormed I = true := by
  obtain ⟨⟨ns, r⟩, hacc, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨st, hst, hr, rfl, inv, wf⟩ := accept_eq_some hacc
  exact ⟨st, r, hst, hr, rfl, inv, wf⟩

/-- Data variables keep their values under the extension. -/
theorem extend_data {S : Finset V} : ∀ {ns : List (Decl V)}, Table S ns → ∀ σ, ∀ x ∈ S, extend ns σ x = σ x
  | [], _, _, _, _ => rfl
  | n :: ns, .cons ok tab, σ, x, hx => by
    have ne : x ≠ n.var := by
      rintro rfl
      have := ok.fresh
      simp [known, hx] at this
    rw [extend_cons_of_ne n ns σ ne]
    exact extend_data tab σ x hx

/-- **The definitions determine the extension**: an assignment satisfying the defining clauses of
every node agrees with its own extension on the known variables. -/
theorem eq_extend_of_defining {S : Finset V} {τ : V → Bool} : ∀ {ns : List (Decl V)}, Table S ns →
    (∀ n ∈ ns, ∀ c ∈ n.node.clauses n.var, c.eval τ = true) → ∀ x, known S ns x = true → τ x = extend ns τ x
  | [], _, _, _, _ => rfl
  | n :: ns, .cons ok tab, sat, x, hx => by
    have ih := eq_extend_of_defining tab fun m hm => sat m (List.mem_cons_of_mem _ hm)
    by_cases h : x = n.var
    · subst h
      rw [extend_cons_self, Node.clauses_complete (sat n List.mem_cons_self)]
      exact Node.eval_congr n.node fun a ha => ih a.var (ok.known_args a ha)
    · rw [extend_cons_of_ne n ns τ h]
      exact ih x (known_of_cons hx h)

/-! ## Soundness -/

/-- **Soundness of the CPOG checker.** If the certified POG is `C`, then `C` is decomposable and
deterministic, its variables are data variables, and it has exactly the models of the input. -/
theorem pog_sound {I : Input V} {cert : Certificate V} {C : Circuit V} (h : pog I cert = some C) :
    C.Decomposable ∧ C.Deterministic ∧ C.vars ⊆ I.vars ∧ ∀ σ : V → Bool, I.cnf.eval σ = C.eval σ := by
  obtain ⟨st, r, _, hr, rfl, inv, _⟩ := pog_eq_some h
  obtain ⟨kr, ar⟩ := inv.root r (finish_root hr)
  obtain ⟨dec, det, sub⟩ := circuit_good inv.table r ar
  refine ⟨dec, det, sub.trans (depsOf_subset inv.table r.var kr), fun σ => ?_⟩
  rw [inv.equiv σ, finish_eval inv hr σ, circuit_eval]

/-- **An accepted certificate certifies a POG**: the checker's verdict as the existence of the
certified circuit with the properties of `pog_sound`. -/
theorem check_sound {I : Input V} {cert : Certificate V} (h : check I cert = true) :
    ∃ C, pog I cert = some C ∧ C.Decomposable ∧ C.Deterministic ∧ C.vars ⊆ I.vars ∧
      ∀ σ : V → Bool, I.cnf.eval σ = C.eval σ := by
  obtain ⟨C, hC⟩ := Option.isSome_iff_exists.mp h
  exact ⟨C, hC, pog_sound hC⟩

/-- **The final clauses are equivalent to the input over the data variables**, the form in which
the CPOG paper states soundness: at the end the store holds the defining clauses and the unit
clause of the root, and an assignment of the data variables satisfies the input exactly when some
assignment of the other variables extends it to a model of the store. -/
theorem pog_final_equiv {I : Input V} {cert : Certificate V} {C : Circuit V} (h : pog I cert = some C) :
    ∃ st r, run I.vars (init I) cert = some st ∧ st.root = some r ∧
      clausesOf (st.store.filter fun p => p.2.kind != .defining) = [[r]] ∧
      ∀ σ : V → Bool, I.cnf.eval σ = true ↔
        ∃ τ : V → Bool, (∀ x ∈ I.vars, τ x = σ x) ∧ (clausesOf st.store).eval τ = true := by
  obtain ⟨st, r, hst, hr, _, inv, wf⟩ := pog_eq_some h
  refine ⟨st, r, hst, finish_root hr, finish_clauses hr, fun σ => ⟨fun hσ => ?_, ?_⟩⟩
  · exact ⟨extend st.nodes σ, extend_data inv.table σ, (inv.equiv σ).symm.trans hσ⟩
  · rintro ⟨τ, agree, sat⟩
    have defs : ∀ n ∈ st.nodes, ∀ c ∈ n.node.clauses n.var, c.eval τ = true := by
      intro n hn c hc
      obtain ⟨p, hp, _, rfl⟩ := inv.complete n hn c hc
      exact Formula.eval_eq_true.mp sat _ (mem_clausesOf.mpr ⟨p, hp, rfl⟩)
    have same := eq_extend_of_defining inv.table defs
    have atTau : I.cnf.eval τ = true := by
      rw [inv.equiv τ, ← sat]
      symm
      exact Formula.eval_congr fun c hc l hl => by
        obtain ⟨p, hp, rfl⟩ := mem_clausesOf.mp hc
        exact same l.var (inv.known_store p hp l hl)
    rw [← atTau]
    refine Formula.eval_congr fun c hc l hl => (agree l.var ?_).symm
    have := List.all_eq_true.mp (List.all_eq_true.mp wf c hc) l hl
    simpa using this

end Checker

/-! ## Counting -/

section Counting

variable [DecidableEq V]

open Circuit

/-- **The certified circuit counts the input**: with weights summing to one on every variable, its
algebraic model count is the weighted model count of the input over the data variables. -/
theorem weightedCount_eq_amc {R : Type v} [CommSemiring R] {I : Input V} {cert : Certificate V} {C : Circuit V}
    (h : pog I cert = some C) (w : V → Bool → R) (normalized : ∀ x, w x false + w x true = 1) :
    I.cnf.weightedCount w I.vars = C.amc w := by
  obtain ⟨dec, det, sub, eqv⟩ := pog_sound h
  rw [amc_eq_wmc_of_normalized w normalized C dec det, ← wmc_eval]
  have same : wmc w I.vars I.cnf.eval = wmc w I.vars (fun σ => C.eval σ) := by
    congr 1
    funext σ
    exact eqv σ
  rw [same, ← union_sdiff_of_subset sub, wmc_extend w disjoint_sdiff C.dependsOn]
  simp [normalized]

/-- Rescaling the weights of each variable by their sum rescales the weighted count by the
product of the sums. -/
theorem weightedCount_rescale {K : Type v} [Semifield K] (W : V → Bool → K) (nz : ∀ x, W x false + W x true ≠ 0)
    (S : Finset V) (F : Formula V) :
    F.weightedCount W S =
      (∏ x ∈ S, (W x false + W x true)) * F.weightedCount (fun x b => W x b / (W x false + W x true)) S := by
  unfold Formula.weightedCount
  rw [mul_sum]
  refine sum_congr rfl fun T _ => ?_
  split
  · rw [← prod_mul_distrib]
    exact prod_congr rfl fun x _ => (mul_div_cancel₀ (W x _) (nz x)).symm
  · rw [mul_zero]

/-- **The weighted count from the certified circuit, for any nonzero weight sums**: the circuit is
evaluated at the normalized weights and scaled by the product of the weight sums. -/
theorem weightedCount_eq_scaled_amc {K : Type v} [Semifield K] {I : Input V} {cert : Certificate V}
    {C : Circuit V} (h : pog I cert = some C) (W : V → Bool → K) (nz : ∀ x, W x false + W x true ≠ 0) :
    I.cnf.weightedCount W I.vars =
      (∏ x ∈ I.vars, (W x false + W x true)) * C.amc (fun x b => W x b / (W x false + W x true)) := by
  rw [weightedCount_rescale W nz, weightedCount_eq_amc h]
  intro x
  rw [← add_div, div_self (nz x)]

/-- With unit weights the weighted count is the model count. -/
theorem weightedCount_one {K : Type v} [Semifield K] (S : Finset V) (F : Formula V) :
    F.weightedCount (fun _ _ => (1 : K)) S = (F.count S : K) := by
  unfold Formula.weightedCount Formula.count
  simp only [prod_const_one]
  rw [sum_boole]

/-- **The model count from the certified circuit**: `2 ^ n` times the circuit evaluated with weight
one half on every literal, `n` the number of data variables. -/
theorem count_eq_amc {K : Type v} [Semifield K] [CharZero K] {I : Input V} {cert : Certificate V} {C : Circuit V}
    (h : pog I cert = some C) :
    (I.cnf.count I.vars : K) = 2 ^ I.vars.card * C.amc (fun _ _ => (1 / 2 : K)) := by
  have two : (1 : K) + 1 ≠ 0 := by
    rw [one_add_one_eq_two]
    exact_mod_cast (two_ne_zero : (2 : ℕ) ≠ 0)
  rw [← weightedCount_one, weightedCount_eq_scaled_amc h (fun _ _ => (1 : K)) fun _ => two, prod_const,
    one_add_one_eq_two]

/-! ## Evaluation on the graph

The circuit is a tree, so a node shared by several parents is read once per parent. The values
below are computed on the graph instead: once per node and polarity, from the values of the older
nodes, with the same shape as the reading. -/

section Values

variable {R : Type v} [CommSemiring R]

/-- A node's value with the given polarity, from the values `f` of its arguments: the algebraic
model count of its reading (`amc_nodeCircuit`). -/
def Node.value (f : Literal V → R) : Node V → Bool → R
  | .prod args, true => (args.map f).prod
  | .prod args, false => args.foldr (fun a r => f a.neg + f a * r) 0
  | .sum a b, true => f a + f b
  | .sum a b, false => f a.neg * f b.neg

/-- The value of a literal in a table of node values (newest first); a data literal weighs `w`. -/
def litValue (w : V → Bool → R) : List (V × R × R) → Literal V → R
  | [], l => w l.var l.sign
  | (x, p, q) :: vs, l => if l.var = x then (if l.sign then p else q) else litValue w vs l

/-- **The values of all nodes**, newest first: each node's positive and negative value, computed
once from the values of the older nodes. -/
def values (w : V → Bool → R) : List (Decl V) → List (V × R × R)
  | [] => []
  | n :: ns =>
    let vs := values w ns
    (n.var, n.node.value (litValue w vs) true, n.node.value (litValue w vs) false) :: vs

omit [DecidableEq V] in
theorem amc_prodChain (w : V → Bool → R) : ∀ cs : List (Circuit V), (prodChain cs).amc w = (cs.map (amc w)).prod
  | [] => rfl
  | c :: cs => by simp [prodChain, amc, amc_prodChain w cs]

omit [DecidableEq V] in
theorem amc_negChain (w : V → Bool → R) (c : Literal V → Circuit V) : ∀ args : List (Literal V),
    (negChain (args.map fun a => (c a, c a.neg))).amc w = args.foldr (fun a r => (c a.neg).amc w + (c a).amc w * r) 0
  | [] => rfl
  | a :: as => by simp [negChain, amc, amc_negChain w c as]

omit [DecidableEq V] in
theorem amc_nodeCircuit (w : V → Bool → R) (c : Literal V → Circuit V) (n : Node V) (s : Bool) :
    (n.circuit c s).amc w = n.value (fun a => (c a).amc w) s := by
  cases n with
  | prod args =>
    cases s
    · exact amc_negChain w c args
    · simp [Node.circuit, Node.value, amc_prodChain, Function.comp_def]
  | sum a b => cases s <;> rfl

/-- **The graph values are the algebraic model counts of the readings.** -/
theorem litValue_values (w : V → Bool → R) : ∀ (ns : List (Decl V)) (l : Literal V),
    litValue w (values w ns) l = (circuit ns l).amc w
  | [], _ => rfl
  | n :: ns, l => by
    have ih : litValue w (values w ns) = fun a => (circuit ns a).amc w := funext (litValue_values w ns)
    simp only [values, litValue, circuit]
    split
    · rw [ih, ← amc_nodeCircuit, ← amc_nodeCircuit]
      cases l.sign <;> rfl
    · exact litValue_values w ns l

/-- **The certified value**: the root's value on the graph, if the certificate is accepted. -/
def certifiedValue (w : V → Bool → R) (I : Input V) (cert : Certificate V) : Option R :=
  (accept I cert).map fun p => litValue w (values w p.1) p.2

theorem certifiedValue_eq {w : V → Bool → R} {I : Input V} {cert : Certificate V} :
    certifiedValue w I cert = (pog I cert).map (amc w) := by
  unfold certifiedValue pog
  cases accept I cert with
  | none => rfl
  | some p => simp [litValue_values]

/-- **The certified value is the weighted count of the input**, for weights summing to one. -/
theorem certifiedValue_sound {w : V → Bool → R} (normalized : ∀ x, w x false + w x true = 1) {I : Input V}
    {cert : Certificate V} {q : R} (h : certifiedValue w I cert = some q) : q = I.cnf.weightedCount w I.vars := by
  rw [certifiedValue_eq] at h
  obtain ⟨C, hC, rfl⟩ := Option.map_eq_some_iff.mp h
  exact (weightedCount_eq_amc hC w normalized).symm

end Values

/-- **The certified model count**: `2 ^ n` times the root's value on the graph at weight one half,
if the certificate is accepted. -/
def certifiedCount (K : Type v) [Semifield K] (I : Input V) (cert : Certificate V) : Option K :=
  (certifiedValue (fun _ _ => (1 / 2 : K)) I cert).map (2 ^ I.vars.card * ·)

/-- **The certified model count is the model count of the input.** -/
theorem certifiedCount_sound {K : Type v} [Semifield K] [CharZero K] {I : Input V} {cert : Certificate V} {q : K}
    (h : certifiedCount K I cert = some q) : q = I.cnf.count I.vars := by
  unfold certifiedCount at h
  rw [certifiedValue_eq, Option.map_map] at h
  obtain ⟨C, hC, rfl⟩ := Option.map_eq_some_iff.mp h
  exact (count_eq_amc hC).symm

end Counting

end Mettapedia.Logic.ASP.CPOG
