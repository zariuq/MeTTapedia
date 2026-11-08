import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Interface
import Mettapedia.Logic.LP.Substitution

/-!
# Rational trees: the terms of the rational-tree fibre

The finite-tree fibre of the step reads first-order terms as finite trees (`FirstOrder.action`),
where the occurs check refuses `X = f(X)`. Its sibling reads them as **rational trees**: possibly
infinite trees with finitely many distinct subtrees (Colmerauer's Prolog II; Courcelle; Maher's
complete axiomatizations of the finite, rational and infinite tree algebras), where `X = f(X)`
has the solution `f(f(f(…)))`.

**What the terms are.** A tree is read at its paths (`Raw`: the label at each path, `none` off
the tree), and it is well formed (`WF`) when it has a root and children exist exactly below each
label's arity. Equality of trees is equality of unfoldings, which is Lean's equality of these
functions; it is proved by coinduction (`eq_of_bisim`). A tree is rational when it has finitely
many distinct subtrees (`Rational`). Substitution replaces variable leaves by trees, path by path
(`subst`); it is strictly unital on well-formed trees (`subst_id`) and strictly associative
(`subst_comp`), and keeps trees well formed and rational (`wf_subst`, `rational_subst`).

**Their finite representation** (`Graph`): a finite system of equations, one per node, each
equation `x_k = label_k(x_{edge k 0}, …)` guarded by a label. Justification:
* every node of a finite graph unfolds to a well-formed rational tree (`wf_unfold`,
  `rational_unfold`), and every well-formed rational tree is such an unfolding: of its own graph
  of subtrees (`subtreeGraph_unfold`, `rational_iff_unfold`);
* two nodes unfold to the same tree exactly when a bisimulation of the graph relates them
  (`unfold_eq_iff`): equality of unfoldings is bisimilarity of presentations;
* a guarded system has exactly one solution, its unfolding (`unfold_solves`, `solves_unique`).

Substitution on graphs (grafting) is associative only up to bisimilarity, while the frame
interface asks the action laws as equalities; so the frame's terms are the trees the graphs
present, not the graphs (`RTree`), exactly as a quotient of graphs by bisimilarity would give.

**Scope: data only.** Labels are variables, constants and function symbols: the trees are pure
immutable first-order data. A graph's sharing of a node is not observable in its unfolding
(`sharing_unobservable`), and variable identities are kept (`distinct_variables_unshared`). This
profile has no choice, effect or resource construct, so it cannot identify a shared choice with two
independent ones; where computations are shared, sharing is observable
(`CallTimeChoiceInstructionControls.shared_choices_stay_correlated`) and no such identification is
made here. The profile is for object terms; it does not change dependent type syntax.

**The rational-tree frames** (`rationalAction`, `rationalFrames`): terms are well-formed rational
trees with equality, substitutions assign them to variables, and the action is substitution. The
finite terms embed (`ofTerm`, `ofTerm_subst`, `ofTerm_injective`), and a tree that becomes finite
under a substitution was finite already (`eq_ofTerm_of_subst`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Rational

open Mettapedia.Logic.LP

/-- The label of a node: a variable, a constant or a function symbol. -/
inductive Head (σ : LPSignature) where
  | var (v : σ.vars)
  | const (c : σ.constants)
  | fn (f : σ.functionSymbols)

namespace Head

variable {σ : LPSignature}

/-- The number of children below a label. -/
def arity : Head σ → ℕ
  | .var _ => 0
  | .const _ => 0
  | .fn f => σ.functionArity f

/-- A label that is not a variable. -/
def Rigid (h : Head σ) : Prop := ∀ v, h ≠ .var v

theorem rigid_or_var (h : Head σ) : h.Rigid ∨ ∃ v, h = .var v := by
  cases h with
  | var v => exact Or.inr ⟨v, rfl⟩
  | const c => exact Or.inl fun v same => by cases same
  | fn f => exact Or.inl fun v same => by cases same

end Head

/-- **A possibly infinite tree with variables, read at its paths**: the label at each path (child
positions listed from the root), and `none` off the tree. -/
abbrev Raw (σ : LPSignature) := List ℕ → Option (Head σ)

namespace Raw

variable {σ : LPSignature}

/-- The `i`-th child. -/
def child (i : ℕ) (t : Raw σ) : Raw σ := fun q => t (i :: q)

/-- The subtree at a path. -/
def sub (p : List ℕ) (t : Raw σ) : Raw σ := fun q => t (p ++ q)

/-- Nothing: the reading off a tree. -/
def bot : Raw σ := fun _ => none

/-- A node with a label and children; children beyond the label's arity are dropped. -/
def node (h : Head σ) (children : ℕ → Raw σ) : List ℕ → Option (Head σ)
  | [] => some h
  | i :: q => if i < h.arity then children i q else none

/-- A variable leaf. -/
def leaf (v : σ.vars) : Raw σ := node (.var v) fun _ => bot

@[simp] theorem node_nil (h : Head σ) (c : ℕ → Raw σ) : node h c [] = some h := rfl

@[simp] theorem bot_apply (p : List ℕ) : (bot : Raw σ) p = none := rfl

@[simp] theorem child_bot (i : ℕ) : child i (bot : Raw σ) = bot := rfl

@[simp] theorem sub_bot (p : List ℕ) : sub p (bot : Raw σ) = bot := rfl

@[simp] theorem leaf_nil (v : σ.vars) : leaf v [] = some (Head.var v : Head σ) := rfl

theorem sub_nil (t : Raw σ) : sub [] t = t := rfl

theorem sub_cons (i : ℕ) (p : List ℕ) (t : Raw σ) : sub (i :: p) t = sub p (child i t) := rfl

theorem child_sub (p : List ℕ) (i : ℕ) (t : Raw σ) : child i (sub p t) = sub (p ++ [i]) t := by
  funext q
  simp [child, sub, List.append_assoc]

theorem child_node (h : Head σ) (c : ℕ → Raw σ) (i : ℕ) :
    child i (node h c) = if i < h.arity then c i else bot := by
  funext q
  by_cases inside : i < h.arity
  · simp only [child, node, inside, if_true]
  · simp only [child, node, inside, if_false, bot]

/-- Two trees with the same root and the same children are equal. -/
theorem ext_child {s t : Raw σ} (root : s [] = t []) (children : ∀ i, child i s = child i t) :
    s = t := by
  funext p
  cases p with
  | nil => exact root
  | cons i q => exact congrFun (children i) q

/-! ## Coinduction -/

/-- **Coinduction for trees**: a relation with equal roots that is closed under taking children
relates only equal trees. -/
theorem eq_of_bisim (R : Raw σ → Raw σ → Prop) (root : ∀ s t, R s t → s [] = t [])
    (children : ∀ s t, R s t → ∀ i, R (child i s) (child i t)) {s t : Raw σ} (related : R s t) :
    s = t := by
  funext p
  induction p generalizing s t with
  | nil => exact root s t related
  | cons i q ih => exact ih (children s t related i)

/-- Coinduction up to equality: each related pair is equal outright, or has equal roots and
children that are equal or related. -/
theorem eq_of_bisim_or (R : Raw σ → Raw σ → Prop)
    (step : ∀ s t, R s t → s = t ∨ (s [] = t [] ∧ ∀ i, child i s = child i t ∨ R (child i s) (child i t)))
    {s t : Raw σ} (related : R s t) : s = t := by
  refine eq_of_bisim (fun a b => a = b ∨ R a b) ?_ ?_ (Or.inr related)
  · rintro a b (same | r)
    · exact congrFun same []
    · rcases step a b r with same | ⟨root, _⟩
      · exact congrFun same []
      · exact root
  · rintro a b (same | r) i
    · exact Or.inl (congrArg (child i) same)
    · rcases step a b r with same | ⟨_, kids⟩
      · exact Or.inl (congrArg (child i) same)
      · exact kids i

/-! ## Well-formed trees -/

/-- Children exist exactly below the arity of their parent's label. -/
def Shaped (t : Raw σ) : Prop := ∀ p i, t (p ++ [i]) ≠ none ↔ ∃ h, t p = some h ∧ i < h.arity

/-- **A well-formed tree**: a root, and children exactly below each label's arity. -/
structure WF (t : Raw σ) : Prop where
  root : t [] ≠ none
  shaped : Shaped t

/-- Below an absent node nothing is present. -/
theorem Shaped.none_append {t : Raw σ} (shaped : Shaped t) {p : List ℕ} (absent : t p = none) :
    ∀ q, t (p ++ q) = none := by
  intro q
  induction q generalizing p with
  | nil => simpa using absent
  | cons j q ih =>
    have next : t (p ++ [j]) = none := by
      by_contra present
      obtain ⟨h, found, _⟩ := (shaped p j).mp present
      rw [absent] at found
      cases found
    simpa [List.append_assoc] using ih next

theorem WF.root_some {t : Raw σ} (w : WF t) : ∃ h, t [] = some h :=
  Option.ne_none_iff_exists'.mp w.root

/-- Children beyond the root's arity are absent. -/
theorem WF.child_eq_bot {t : Raw σ} (w : WF t) {h : Head σ} (root : t [] = some h) {i : ℕ}
    (outside : h.arity ≤ i) : child i t = bot := by
  have absent : t [i] = none := by
    by_contra present
    obtain ⟨h', found, small⟩ := (w.shaped [] i).mp present
    rw [root] at found
    cases found
    omega
  funext q
  exact w.shaped.none_append (p := [i]) absent q

/-- Children below the root's arity are well formed. -/
theorem WF.child_wf {t : Raw σ} (w : WF t) {h : Head σ} (root : t [] = some h) {i : ℕ}
    (inside : i < h.arity) : WF (child i t) where
  root := (w.shaped [] i).mpr ⟨h, root, inside⟩
  shaped p j := w.shaped (i :: p) j

/-- Subtrees at present paths are well formed. -/
theorem WF.sub_wf {t : Raw σ} (w : WF t) {p : List ℕ} (present : t p ≠ none) : WF (sub p t) where
  root := by simpa [Raw.sub] using present
  shaped q j := by simpa [Raw.sub, List.append_assoc] using w.shaped (p ++ q) j

/-- A well-formed tree is the node of its root and its children. -/
theorem WF.eq_node {t : Raw σ} (w : WF t) {h : Head σ} (root : t [] = some h) :
    t = node h fun i => child i t := by
  funext p
  cases p with
  | nil => exact root
  | cons i q =>
    by_cases inside : i < h.arity
    · simp only [node, inside, if_true, Raw.child]
    · simp only [node, inside, if_false]
      exact congrFun (w.child_eq_bot root (not_lt.mp inside)) q

/-- A well-formed tree with a variable root is that variable's leaf. -/
theorem WF.eq_leaf {t : Raw σ} (w : WF t) {v : σ.vars} (root : t [] = some (.var v)) : t = leaf v := by
  rw [w.eq_node root]
  exact congrArg (node _) (funext fun i => w.child_eq_bot root (Nat.zero_le i))

/-- The node form of a well-formed tree. -/
theorem WF.node_form {t : Raw σ} (w : WF t) :
    ∃ h, t [] = some h ∧ t = (node h fun i => child i t) ∧ ∀ i < h.arity, WF (child i t) := by
  obtain ⟨h, root⟩ := w.root_some
  exact ⟨h, root, w.eq_node root, fun i inside => w.child_wf root inside⟩

/-- A shape condition at the root of every member of a family closed under children holds at
every path. -/
theorem shaped_of_family (F : Raw σ → Prop)
    (atRoot : ∀ t, F t → ∀ i, t [i] ≠ none ↔ ∃ h, t [] = some h ∧ i < h.arity)
    (closed : ∀ t, F t → ∀ i, F (child i t)) {t : Raw σ} (member : F t) : Shaped t := by
  intro p
  induction p generalizing t with
  | nil => exact atRoot t member
  | cons j q ih => exact ih (closed t member j)

/-- **Well-formedness by nodes**: every member of a family that is a node whose children below its
arity are again members is well formed. -/
theorem wf_of_nodes (F : Raw σ → Prop)
    (nodes : ∀ t, F t → ∃ h c, t = node h c ∧ ∀ i < h.arity, F (c i)) {t : Raw σ} (member : F t) :
    WF t := by
  refine ⟨?_, shaped_of_family (fun a => F a ∨ a = bot) ?_ ?_ (Or.inl member)⟩
  · obtain ⟨h, c, rfl, -⟩ := nodes t member
    simp
  · rintro a (inF | rfl) i
    · obtain ⟨h, c, rfl, kids⟩ := nodes a inF
      by_cases inside : i < h.arity
      · obtain ⟨h', c', same, -⟩ := nodes (c i) (kids i inside)
        have rootChild : c i [] = some h' := by rw [same]; rfl
        simp [node, inside, rootChild]
      · simp [node, inside]
    · simp
  · rintro a (inF | rfl) i
    · obtain ⟨h, c, rfl, kids⟩ := nodes a inF
      rw [child_node]
      split_ifs with inside
      · exact Or.inl (kids i inside)
      · exact Or.inr rfl
    · exact Or.inr rfl

theorem wf_node {h : Head σ} {c : ℕ → Raw σ} (kids : ∀ i < h.arity, WF (c i)) : WF (node h c) := by
  refine wf_of_nodes (fun a => a = node h c ∨ WF a) ?_ (Or.inl rfl)
  rintro a (rfl | w)
  · exact ⟨h, c, rfl, fun i inside => Or.inr (kids i inside)⟩
  · obtain ⟨h', -, same, kids'⟩ := w.node_form
    exact ⟨h', _, same, fun i inside => Or.inr (kids' i inside)⟩

theorem wf_leaf (v : σ.vars) : WF (leaf v : Raw σ) :=
  wf_node fun i inside => absurd inside (Nat.not_lt_zero i)

/-! ## Substitution -/

/-- Substitution read at a path: the first variable met on the way down is replaced. -/
def substAt (θ : σ.vars → Raw σ) : List ℕ → Raw σ → Option (Head σ)
  | [], t => match t [] with
    | some (.var v) => θ v []
    | r => r
  | i :: q, t => match t [] with
    | some (.var v) => θ v (i :: q)
    | _ => substAt θ q (child i t)

/-- **Substitution**: every variable leaf is replaced by its tree. -/
def subst (θ : σ.vars → Raw σ) (t : Raw σ) : Raw σ := fun p => substAt θ p t

theorem subst_of_var {θ : σ.vars → Raw σ} {t : Raw σ} {v : σ.vars} (root : t [] = some (.var v)) :
    subst θ t = θ v := by
  funext p
  cases p with
  | nil =>
    show substAt θ [] t = θ v []
    simp only [substAt, root]
  | cons i q =>
    show substAt θ (i :: q) t = θ v (i :: q)
    simp only [substAt, root]

@[simp] theorem subst_leaf (θ : σ.vars → Raw σ) (v : σ.vars) : subst θ (leaf v) = θ v :=
  subst_of_var rfl

/-- At a root that is not a variable, substitution keeps the root. -/
theorem subst_nil {θ : σ.vars → Raw σ} {t : Raw σ} (notVar : ∀ v, t [] ≠ some (.var v)) :
    subst θ t [] = t [] := by
  show substAt θ [] t = t []
  simp only [substAt]

/-- At a root that is not a variable, substitution commutes with taking children. -/
theorem child_subst {θ : σ.vars → Raw σ} {t : Raw σ} (notVar : ∀ v, t [] ≠ some (.var v)) (i : ℕ) :
    child i (subst θ t) = subst θ (child i t) := by
  funext q
  show substAt θ (i :: q) t = substAt θ q (child i t)
  simp only [substAt]

theorem notVar_of_rigid {t : Raw σ} {h : Head σ} (root : t [] = some h) (rigid : h.Rigid) :
    ∀ v, t [] ≠ some (.var v) := fun v same => rigid v (Option.some.inj (root.symm.trans same))

@[simp] theorem subst_bot (θ : σ.vars → Raw σ) : subst θ (bot : Raw σ) = bot :=
  eq_of_bisim (fun a b => a = subst θ bot ∧ b = bot)
    (fun a b ⟨ha, hb⟩ => by rw [ha, hb]; exact subst_nil (fun v same => by simp at same))
    (fun a b ⟨ha, hb⟩ i => by
      rw [ha, hb]
      exact ⟨child_subst (fun v same => by simp at same) i, rfl⟩)
    ⟨rfl, rfl⟩

theorem subst_node (θ : σ.vars → Raw σ) {h : Head σ} (rigid : h.Rigid) (c : ℕ → Raw σ) :
    subst θ (node h c) = node h fun i => subst θ (c i) := by
  have notVar := notVar_of_rigid (t := node h c) rfl rigid
  refine ext_child (subst_nil notVar) fun i => ?_
  rw [child_subst notVar, child_node, child_node]
  split_ifs
  · rfl
  · exact subst_bot θ

/-- **Substitution is unital** on well-formed trees. -/
theorem subst_id {t : Raw σ} (w : WF t) : subst leaf t = t := by
  refine eq_of_bisim_or (fun a b => WF b ∧ a = subst leaf b) ?_ ⟨w, rfl⟩
  rintro a b ⟨wb, rfl⟩
  obtain ⟨h, root⟩ := wb.root_some
  rcases h.rigid_or_var with rigid | ⟨v, rfl⟩
  · have notVar := notVar_of_rigid root rigid
    refine Or.inr ⟨subst_nil notVar, fun i => ?_⟩
    rw [child_subst notVar]
    by_cases inside : i < h.arity
    · exact Or.inr ⟨wb.child_wf root inside, rfl⟩
    · rw [wb.child_eq_bot root (not_lt.mp inside), subst_bot]
      exact Or.inl rfl
  · exact Or.inl ((subst_of_var root).trans (wb.eq_leaf root).symm)

/-- **Substitution is associative.** -/
theorem subst_comp (outer inner : σ.vars → Raw σ) (t : Raw σ) :
    subst (fun v => subst outer (inner v)) t = subst outer (subst inner t) := by
  refine eq_of_bisim_or (fun a b => ∃ t, a = subst (fun v => subst outer (inner v)) t ∧
    b = subst outer (subst inner t)) ?_ ⟨t, rfl, rfl⟩
  rintro a b ⟨t, rfl, rfl⟩
  by_cases isVar : ∃ v, t [] = some (.var v)
  · obtain ⟨v, root⟩ := isVar
    left
    rw [subst_of_var root, subst_of_var root]
  · simp only [not_exists] at isVar
    have innerRoot : subst inner t [] = t [] := subst_nil isVar
    have notVar' : ∀ v, subst inner t [] ≠ some (.var v) := by rw [innerRoot]; exact isVar
    refine Or.inr ⟨?_, fun i => Or.inr ⟨child i t, ?_, ?_⟩⟩
    · rw [subst_nil isVar, subst_nil notVar', innerRoot]
    · exact child_subst isVar i
    · rw [child_subst notVar' i, child_subst isVar i]

/-- **Substitution keeps trees well formed.** -/
theorem wf_subst {θ : σ.vars → Raw σ} (hθ : ∀ v, WF (θ v)) {t : Raw σ} (w : WF t) :
    WF (subst θ t) := by
  refine wf_of_nodes (fun a => WF a ∨ ∃ t, WF t ∧ a = subst θ t) ?_ (Or.inr ⟨t, w, rfl⟩)
  have ofWF : ∀ a, WF a → ∃ h c, a = node h c ∧
      ∀ i < h.arity, (WF (c i) ∨ ∃ t, WF t ∧ c i = subst θ t) := by
    intro a wa
    obtain ⟨h, -, same, kids⟩ := wa.node_form
    exact ⟨h, _, same, fun i inside => Or.inl (kids i inside)⟩
  rintro a (wa | ⟨t, w, rfl⟩)
  · exact ofWF a wa
  · obtain ⟨h, root⟩ := w.root_some
    rcases h.rigid_or_var with rigid | ⟨v, rfl⟩
    · refine ⟨h, fun i => subst θ (child i t), ?_, fun i inside => Or.inr ⟨child i t, w.child_wf root inside, rfl⟩⟩
      conv_lhs => rw [w.eq_node root]
      exact subst_node θ rigid _
    · rw [subst_of_var root]
      exact ofWF _ (hθ v)

/-! ## Rational trees -/

/-- **A rational tree**: finitely many distinct subtrees. -/
def IsRational (t : Raw σ) : Prop := (Set.range fun p => sub p t).Finite

theorem rational_of_subset {t : Raw σ} (S : Set (Raw σ)) (finite : S.Finite)
    (inside : ∀ p, sub p t ∈ S) : IsRational t :=
  finite.subset (by rintro _ ⟨p, rfl⟩; exact inside p)

theorem IsRational.child_rational {t : Raw σ} (r : IsRational t) (i : ℕ) : IsRational (child i t) :=
  rational_of_subset _ r fun p => ⟨i :: p, rfl⟩

/-- The variables occurring in a tree. -/
def occursVars (t : Raw σ) : Set σ.vars := {v | ∃ p, t p = some (.var v)}

/-- A rational tree has finitely many variables. -/
theorem IsRational.vars_finite {t : Raw σ} (r : IsRational t) : (occursVars t).Finite := by
  have image : ((fun u : Raw σ => u []) '' Set.range fun p => sub p t).Finite := r.image _
  refine (image.preimage (f := fun v : σ.vars => (some (Head.var v) : Option (Head σ))) ?_).subset ?_
  · intro v _ w _ same
    simpa using same
  · rintro v ⟨p, found⟩
    exact ⟨sub p t, ⟨p, rfl⟩, by simp [Raw.sub, found]⟩

/-- **Substitution keeps trees rational.** -/
theorem rational_subst {θ : σ.vars → Raw σ} (hθ : ∀ v, IsRational (θ v)) {t : Raw σ}
    (r : IsRational t) : IsRational (subst θ t) := by
  let S : Set (Raw σ) := (subst θ '' Set.range fun p => sub p t) ∪
    ⋃ v ∈ occursVars t, Set.range fun p => sub p (θ v)
  have finite : S.Finite := (r.image _).union (r.vars_finite.biUnion fun v _ => hθ v)
  have key : ∀ p r', sub p (subst θ (sub r' t)) ∈ S := by
    intro p
    induction p with
    | nil => intro r'; exact Or.inl ⟨sub r' t, ⟨r', rfl⟩, rfl⟩
    | cons i q ih =>
      intro r'
      by_cases isVar : ∃ v, sub r' t [] = some (.var v)
      · obtain ⟨v, found⟩ := isVar
        rw [subst_of_var found]
        exact Or.inr (Set.mem_biUnion (x := v) ⟨r', by simpa [Raw.sub] using found⟩ ⟨i :: q, rfl⟩)
      · simp only [not_exists] at isVar
        rw [sub_cons, child_subst isVar, child_sub]
        exact ih (r' ++ [i])
  exact rational_of_subset S finite fun p => key p []

theorem rational_node {h : Head σ} {c : ℕ → Raw σ} (kids : ∀ i < h.arity, IsRational (c i)) :
    IsRational (node h c) := by
  let S : Set (Raw σ) := insert (node h c) (insert bot
    (⋃ i ∈ {i | i < h.arity}, Set.range fun p => sub p (c i)))
  have finite : S.Finite :=
    ((Set.finite_lt_nat h.arity).biUnion fun i inside => kids i inside).insert _ |>.insert _
  refine rational_of_subset S finite fun p => ?_
  cases p with
  | nil => exact Set.mem_insert _ _
  | cons i q =>
    rw [sub_cons, child_node]
    split_ifs with inside
    · exact Or.inr (Or.inr (Set.mem_biUnion (x := i) inside ⟨q, rfl⟩))
    · exact Or.inr (Or.inl rfl)

theorem rational_leaf (v : σ.vars) : IsRational (leaf v : Raw σ) :=
  rational_node fun i inside => absurd inside (Nat.not_lt_zero i)

/-! ## Finite presentations: graphs, i.e. guarded systems of equations -/

/-- **A graph**: each node has a label and successors; it presents the guarded system of equations
`x_k = label_k(x_{edge k 0}, …, x_{edge k (n-1)})`, with `n` the label's arity. -/
structure Graph (σ : LPSignature) (N : Type*) where
  label : N → Head σ
  edge : N → ℕ → N

namespace Graph

variable {N : Type*} (G : Graph σ N)

/-- The unfolding read at a path. -/
def unfoldAt : List ℕ → N → Option (Head σ)
  | [], k => some (G.label k)
  | i :: q, k => if i < (G.label k).arity then unfoldAt q (G.edge k i) else none

/-- **The unfolding** of a node. -/
def unfold (k : N) : Raw σ := fun p => G.unfoldAt p k

theorem unfold_eq (k : N) : G.unfold k = node (G.label k) fun i => G.unfold (G.edge k i) := by
  funext p
  cases p <;> rfl

theorem child_unfold (k : N) (i : ℕ) :
    child i (G.unfold k) = if i < (G.label k).arity then G.unfold (G.edge k i) else bot := by
  rw [G.unfold_eq k, child_node]

theorem wf_unfold (k : N) : WF (G.unfold k) :=
  wf_of_nodes (fun a => ∃ k, a = G.unfold k)
    (fun _ ⟨k, same⟩ => ⟨G.label k, _, same.trans (G.unfold_eq k), fun i _ => ⟨G.edge k i, rfl⟩⟩)
    ⟨k, rfl⟩

/-- **Every node of a finite graph unfolds to a rational tree.** -/
theorem rational_unfold [Finite N] (k : N) : IsRational (G.unfold k) := by
  refine rational_of_subset (insert bot (Set.range G.unfold)) ((Set.finite_range _).insert _) ?_
  intro p
  induction p generalizing k with
  | nil => exact Or.inr ⟨k, rfl⟩
  | cons i q ih =>
    rw [sub_cons, child_unfold]
    split_ifs
    · exact ih _
    · exact Or.inl rfl

/-- A solution of the guarded system: each node's tree has the node's label and its successors'
trees as children. -/
def Solves (a : N → Raw σ) : Prop := ∀ k, a k = node (G.label k) fun i => a (G.edge k i)

/-- The unfolding solves the system. -/
theorem unfold_solves : G.Solves G.unfold := G.unfold_eq

/-- **A guarded system has exactly one solution**: its unfolding. -/
theorem solves_unique {a : N → Raw σ} (solved : G.Solves a) (k : N) : a k = G.unfold k := by
  refine eq_of_bisim_or (fun s t => ∃ k, s = a k ∧ t = G.unfold k) ?_ ⟨k, rfl, rfl⟩
  rintro s t ⟨k, rfl, rfl⟩
  refine Or.inr ⟨by rw [solved k, G.unfold_eq k]; rfl, fun i => ?_⟩
  rw [solved k, child_node, child_unfold]
  split_ifs
  · exact Or.inr ⟨_, rfl, rfl⟩
  · exact Or.inl rfl

/-- A bisimulation of a graph: related nodes have equal labels and related successors. -/
def IsBisimulation (R : N → N → Prop) : Prop :=
  ∀ k l, R k l → G.label k = G.label l ∧ ∀ i < (G.label k).arity, R (G.edge k i) (G.edge l i)

/-- **Equality of unfoldings is bisimilarity.** -/
theorem unfold_eq_iff (k l : N) :
    G.unfold k = G.unfold l ↔ ∃ R, G.IsBisimulation R ∧ R k l := by
  constructor
  · intro same
    refine ⟨fun k l => G.unfold k = G.unfold l, fun k l same => ?_, same⟩
    have labels : G.label k = G.label l := Option.some.inj (congrFun same [])
    refine ⟨labels, fun i inside => ?_⟩
    have kids := congrArg (child i) same
    rw [child_unfold, child_unfold, if_pos inside, if_pos (labels ▸ inside)] at kids
    exact kids
  · rintro ⟨R, bisim, related⟩
    refine eq_of_bisim_or (fun s t => ∃ k l, R k l ∧ s = G.unfold k ∧ t = G.unfold l) ?_
      ⟨k, l, related, rfl, rfl⟩
    rintro s t ⟨k, l, r, rfl, rfl⟩
    obtain ⟨labels, kids⟩ := bisim k l r
    refine Or.inr ⟨by rw [G.unfold_eq k, G.unfold_eq l, labels]; rfl, fun i => ?_⟩
    rw [child_unfold, child_unfold, ← labels]
    split_ifs with inside
    · exact Or.inr ⟨_, _, kids i inside, rfl, rfl⟩
    · exact Or.inl rfl

end Graph

/-- The subtrees of a tree at its present paths. -/
def Subtrees (t : Raw σ) : Set (Raw σ) := {u | ∃ p, t p ≠ none ∧ u = sub p t}

theorem Subtrees.root_ne_none {t : Raw σ} (u : Subtrees t) : u.1 [] ≠ none := by
  obtain ⟨p, present, same⟩ := u.2
  rw [same]
  simpa [Raw.sub] using present

theorem Subtrees.wf {t : Raw σ} (w : WF t) (u : Subtrees t) : WF u.1 := by
  obtain ⟨p, present, same⟩ := u.2
  rw [same]
  exact w.sub_wf present

/-- The label of a subtree's root. -/
noncomputable def Subtrees.label {t : Raw σ} (u : Subtrees t) : Head σ :=
  Classical.choose (Option.ne_none_iff_exists'.mp (Subtrees.root_ne_none u))

theorem Subtrees.label_spec {t : Raw σ} (u : Subtrees t) : u.1 [] = some (Subtrees.label u) :=
  Classical.choose_spec (Option.ne_none_iff_exists'.mp (Subtrees.root_ne_none u))

theorem Subtrees.child_mem {t : Raw σ} (w : WF t) (u : Subtrees t) {i : ℕ}
    (inside : i < (Subtrees.label u).arity) : child i u.1 ∈ Subtrees t := by
  obtain ⟨p, present, same⟩ := u.2
  have rootLabel : t p = some (Subtrees.label u) := by
    have := (Subtrees.label_spec u)
    rw [same] at this
    simpa [Raw.sub] using this
  refine ⟨p ++ [i], (w.shaped p i).mpr ⟨(Subtrees.label u), rootLabel, inside⟩, ?_⟩
  rw [same, child_sub]

/-- **The graph of subtrees** of a well-formed tree. -/
noncomputable def subtreeGraph {t : Raw σ} (w : WF t) : Graph σ (Subtrees t) where
  label u := (Subtrees.label u)
  edge u i := if inside : i < (Subtrees.label u).arity then ⟨child i u.1, (Subtrees.child_mem w u) inside⟩ else u

/-- **Every subtree is the unfolding of its node of the subtree graph.** -/
theorem subtreeGraph_unfold {t : Raw σ} (w : WF t) (u : Subtrees t) :
    (subtreeGraph w).unfold u = u.1 := by
  refine eq_of_bisim_or (fun a b => ∃ u : Subtrees t, a = (subtreeGraph w).unfold u ∧ b = u.1) ?_
    ⟨u, rfl, rfl⟩
  rintro a b ⟨u, rfl, rfl⟩
  refine Or.inr ⟨by rw [(subtreeGraph w).unfold_eq u, (Subtrees.label_spec u)]; rfl, fun i => ?_⟩
  have labelled : (subtreeGraph w).label u = Subtrees.label u := rfl
  rw [Graph.child_unfold, labelled]
  by_cases inside : i < (Subtrees.label u).arity
  · rw [if_pos inside]
    have edged : (subtreeGraph w).edge u i = ⟨child i u.1, Subtrees.child_mem w u inside⟩ :=
      dif_pos inside
    rw [edged]
    exact Or.inr ⟨_, rfl, rfl⟩
  · rw [if_neg inside, (Subtrees.wf w u).child_eq_bot (Subtrees.label_spec u) (not_lt.mp inside)]
    exact Or.inl rfl

theorem rational_subtrees_finite {t : Raw σ} (r : IsRational t) : (Subtrees t).Finite :=
  r.subset fun _ ⟨p, _, same⟩ => ⟨p, same.symm⟩

/-- **The finite representation is exact**: a well-formed tree is rational exactly when it is the
unfolding of a node of a finite graph. -/
theorem rational_iff_unfold {t : Raw σ} (w : WF t) :
    IsRational t ↔ ∃ (S : Set (Raw σ)) (_ : S.Finite) (G : Graph σ S) (k : S), G.unfold k = t := by
  constructor
  · intro r
    exact ⟨Subtrees t, rational_subtrees_finite r, subtreeGraph w,
      ⟨t, [], by simpa using w.root, rfl⟩, subtreeGraph_unfold w _⟩
  · rintro ⟨S, finite, G, k, rfl⟩
    have := finite.to_subtype
    exact G.rational_unfold k

/-! ## The finite trees -/

/-- **A finite term as a tree.** -/
def ofTerm : Term σ → Raw σ
  | .var v => leaf v
  | .const c => node (.const c) fun _ => bot
  | .app f ts => node (.fn f) fun i => if h : i < σ.functionArity f then ofTerm (ts ⟨i, h⟩) else bot

theorem ofTerm_app_child {f : σ.functionSymbols} (ts : Fin (σ.functionArity f) → Term σ)
    (i : Fin (σ.functionArity f)) : child i (ofTerm (.app f ts)) = ofTerm (ts i) := by
  simp only [ofTerm, child_node, Head.arity, i.2, if_true, dif_pos]

theorem wf_ofTerm (u : Term σ) : WF (ofTerm u) := by
  refine wf_of_nodes (fun a => ∃ u, a = ofTerm u) ?_ ⟨u, rfl⟩
  rintro _ ⟨u, rfl⟩
  cases u with
  | var v => exact ⟨_, _, rfl, fun i inside => absurd inside (Nat.not_lt_zero i)⟩
  | const c => exact ⟨_, _, rfl, fun i inside => absurd inside (Nat.not_lt_zero i)⟩
  | app f ts =>
    refine ⟨_, _, rfl, fun i inside => ⟨ts ⟨i, inside⟩, ?_⟩⟩
    exact dif_pos inside

theorem rational_ofTerm (u : Term σ) : IsRational (ofTerm u) := by
  induction u with
  | var v => exact rational_leaf v
  | const c => exact rational_node fun i inside => absurd inside (Nat.not_lt_zero i)
  | app f ts ih =>
    refine rational_node fun i inside => ?_
    show IsRational (if h : i < σ.functionArity f then ofTerm (ts ⟨i, h⟩) else bot)
    rw [dif_pos (show i < σ.functionArity f from inside)]
    exact ih _

/-- **The embedding is a homomorphism**: finite substitution is substitution of trees. -/
theorem ofTerm_subst (θ : Subst σ) (t : Term σ) :
    ofTerm (θ.applyTerm t) = subst (fun v => ofTerm (θ v)) (ofTerm t) := by
  induction t with
  | var v => exact (subst_leaf (fun v => ofTerm (θ v)) v).symm
  | const c =>
    show node (.const c) (fun _ => bot) = subst _ (node (.const c) fun _ => bot)
    rw [subst_node _ (fun v same => by cases same)]
    simp
  | app f ts ih =>
    show node (.fn f) (fun i => if h : i < σ.functionArity f then ofTerm (θ.applyTerm (ts ⟨i, h⟩))
      else bot) = subst _ (node (.fn f) fun i => if h : i < σ.functionArity f then ofTerm (ts ⟨i, h⟩)
      else bot)
    rw [subst_node _ (fun v same => by cases same)]
    congr 1
    funext i
    split_ifs with inside
    · exact ih _
    · exact (subst_bot _).symm

/-- **The embedding is injective.** -/
theorem ofTerm_injective : Function.Injective (ofTerm : Term σ → Raw σ) := by
  intro s
  induction s with
  | var v =>
    intro t same
    have roots := congrFun same []
    cases t <;> simp [ofTerm, leaf] at roots
    rw [roots]
  | const c =>
    intro t same
    have roots := congrFun same []
    cases t <;> simp [ofTerm, leaf] at roots
    rw [roots]
  | app f ts ih =>
    intro t same
    have roots := congrFun same []
    cases t with
    | var v => simp [ofTerm, leaf] at roots
    | const c => simp [ofTerm] at roots
    | app g us =>
      have fg : f = g := by simpa [ofTerm] using roots
      subst fg
      have kids : ∀ i, ts i = us i := fun i => ih i (by
        have := congrArg (child i) same
        rwa [ofTerm_app_child, ofTerm_app_child] at this)
      rw [funext kids]

/-- **A tree that a substitution makes finite was finite already.** -/
theorem eq_ofTerm_of_subst {θ : σ.vars → Raw σ} :
    ∀ (u : Term σ) {t : Raw σ}, WF t → subst θ t = ofTerm u → ∃ s, t = ofTerm s := by
  intro u
  induction u with
  | var v =>
    intro t w same
    obtain ⟨h, root⟩ := w.root_some
    rcases h.rigid_or_var with rigid | ⟨x, rfl⟩
    · have := congrFun same []
      rw [subst_nil (notVar_of_rigid root rigid), root] at this
      exact absurd (Option.some.inj this) (rigid v)
    · exact ⟨.var x, w.eq_leaf root⟩
  | const c =>
    intro t w same
    obtain ⟨h, root⟩ := w.root_some
    rcases h.rigid_or_var with rigid | ⟨x, rfl⟩
    · have heads := congrFun same []
      rw [subst_nil (notVar_of_rigid root rigid), root] at heads
      have : h = .const c := Option.some.inj heads
      subst this
      refine ⟨.const c, (w.eq_node root).trans ?_⟩
      exact congrArg (node _) (funext fun i => w.child_eq_bot root (Nat.zero_le i))
    · exact ⟨.var x, w.eq_leaf root⟩
  | app f ts ih =>
    intro t w same
    obtain ⟨h, root⟩ := w.root_some
    rcases h.rigid_or_var with rigid | ⟨x, rfl⟩
    · have notVar := notVar_of_rigid root rigid
      have heads := congrFun same []
      rw [subst_nil notVar, root] at heads
      have : h = .fn f := Option.some.inj heads
      subst this
      have kids : ∀ i : Fin (σ.functionArity f), ∃ s, child i t = ofTerm s := by
        intro i
        refine ih i (w.child_wf root i.2) ?_
        rw [← child_subst notVar, same, ofTerm_app_child]
      choose ss hss using kids
      refine ⟨.app f ss, (w.eq_node root).trans ?_⟩
      show node (.fn f) (fun i => child i t) =
        node (.fn f) fun i => if h : i < σ.functionArity f then ofTerm (ss ⟨i, h⟩) else bot
      congr 1
      funext i
      split_ifs with inside
      · exact hss ⟨i, inside⟩
      · exact w.child_eq_bot root (not_lt.mp inside)
    · exact ⟨.var x, w.eq_leaf root⟩

/-! ## Controls on sharing: data trees forget sharing and keep variable identities -/

/-- `f(a, a)` with `a` one shared node: nodes `0 ↦ f(1, 1)`, `1 ↦ leaf`. -/
def sharedGraph (f : σ.functionSymbols) (a : Head σ) : Graph σ (Fin 2) where
  label k := if k = 0 then .fn f else a
  edge _ _ := 1

/-- `f(a, a)` with two copies of `a`: nodes `0 ↦ f(1, 2)`, `1 ↦ leaf`, `2 ↦ leaf`. -/
def copiedGraph (f : σ.functionSymbols) (a : Head σ) : Graph σ (Fin 3) where
  label k := if k = 0 then .fn f else a
  edge _ i := if i = 0 then 1 else 2

theorem node_congr {h : Head σ} {c d : ℕ → Raw σ} (same : ∀ i < h.arity, c i = d i) :
    node h c = node h d := by
  funext p
  cases p with
  | nil => rfl
  | cons i q =>
    simp only [node]
    split_ifs with inside
    · exact congrFun (same i inside) q
    · rfl

theorem Graph.unfold_of_leafLabel {N : Type*} (G : Graph σ N) {k : N} {a : Head σ}
    (labelled : G.label k = a) (leafLabel : a.arity = 0) : G.unfold k = node a fun _ => bot := by
  rw [G.unfold_eq k, labelled]
  exact node_congr fun i inside => absurd inside (by omega)

/-- **Sharing is not observable in data trees**: a shared leaf and two copies of it unfold alike. -/
theorem sharing_unobservable (f : σ.functionSymbols) (a : Head σ) (leafLabel : a.arity = 0) :
    (sharedGraph f a).unfold 0 = (copiedGraph f a).unfold 0 := by
  have shared0 : (sharedGraph f a).label 0 = .fn f := by simp [sharedGraph]
  have copied0 : (copiedGraph f a).label 0 = .fn f := by simp [copiedGraph]
  have shared1 : (sharedGraph f a).label 1 = a := by simp [sharedGraph]
  have copied1 : (copiedGraph f a).label 1 = a := by simp [copiedGraph]
  have copied2 : (copiedGraph f a).label 2 = a := by simp [copiedGraph]
  rw [(sharedGraph f a).unfold_eq 0, (copiedGraph f a).unfold_eq 0, shared0, copied0]
  refine node_congr fun i _ => ?_
  show (sharedGraph f a).unfold 1 = (copiedGraph f a).unfold (if i = 0 then 1 else 2)
  rw [(sharedGraph f a).unfold_of_leafLabel shared1 leafLabel]
  split_ifs
  · exact ((copiedGraph f a).unfold_of_leafLabel copied1 leafLabel).symm
  · exact ((copiedGraph f a).unfold_of_leafLabel copied2 leafLabel).symm

/-- **Variable identities are kept**: distinct variables are distinct trees, however a presentation
shares them. -/
theorem distinct_variables_unshared {v w : σ.vars} (distinct : v ≠ w) : (leaf v : Raw σ) ≠ leaf w :=
  fun same => distinct (Head.var.inj (Option.some.inj (congrFun same [])))

end Raw

/-! ## The rational-tree frames -/

variable (σ : LPSignature)

/-- **The terms of the rational-tree fibre**: well-formed rational trees. -/
def RTree : Type _ := {t : Raw σ // Raw.WF t ∧ Raw.IsRational t}

/-- Its substitutions: rational trees for variables. -/
abbrev RSubst := σ.vars → RTree σ

variable {σ}

namespace RTree

/-- A variable as a tree. -/
def leaf (v : σ.vars) : RTree σ := ⟨Raw.leaf v, Raw.wf_leaf v, Raw.rational_leaf v⟩

/-- A finite term as a rational tree. -/
def ofTerm (u : Term σ) : RTree σ := ⟨Raw.ofTerm u, Raw.wf_ofTerm u, Raw.rational_ofTerm u⟩

/-- **Substitution of rational trees.** -/
def subst (θ : RSubst σ) (t : RTree σ) : RTree σ :=
  ⟨Raw.subst (fun v => (θ v).1) t.1, Raw.wf_subst (fun v => (θ v).2.1) t.2.1,
    Raw.rational_subst (fun v => (θ v).2.2) t.2.2⟩

theorem ext {s t : RTree σ} (same : s.1 = t.1) : s = t := Subtype.ext same

@[simp] theorem subst_leaf (θ : RSubst σ) (v : σ.vars) : subst θ (leaf v) = θ v :=
  ext (Raw.subst_leaf _ v)

theorem subst_id (t : RTree σ) : subst leaf t = t := ext (Raw.subst_id t.2.1)

theorem subst_comp (outer inner : RSubst σ) (t : RTree σ) :
    subst (fun v => subst outer (inner v)) t = subst outer (subst inner t) :=
  ext (Raw.subst_comp (fun v => (outer v).1) (fun v => (inner v).1) t.1)

theorem ofTerm_subst (θ : Subst σ) (u : Term σ) :
    ofTerm (θ.applyTerm u) = subst (fun v => ofTerm (θ v)) (ofTerm u) :=
  ext (Raw.ofTerm_subst θ u)

theorem ofTerm_injective : Function.Injective (ofTerm : Term σ → RTree σ) :=
  fun _ _ same => Raw.ofTerm_injective (congrArg Subtype.val same)

end RTree

variable (σ)

/-- **The rational-tree substitution action**: rational trees with equality (of unfoldings), acted on
by substitution. -/
def rationalAction : SubstitutionAction (RTree σ) (RSubst σ) where
  E := Eq
  equivalence := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  apply := RTree.subst
  identity := RTree.leaf
  compose outer inner := fun v => RTree.subst outer (inner v)
  apply_identity := RTree.subst_id
  apply_compose := RTree.subst_comp
  preserves := fun θ {_ _} same => congrArg (RTree.subst θ) same

/-- **The rational-tree frames**: the one-frame category of the rational-tree action. -/
abbrev rationalFrames := Interface.Frames.ofSubstitution (rationalAction σ)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Rational

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

#print axioms Rational.Raw.eq_of_bisim
#print axioms Rational.Raw.subst_id
#print axioms Rational.Raw.subst_comp
#print axioms Rational.Raw.wf_subst
#print axioms Rational.Raw.rational_subst
#print axioms Rational.Raw.Graph.rational_unfold
#print axioms Rational.Raw.Graph.solves_unique
#print axioms Rational.Raw.Graph.unfold_eq_iff
#print axioms Rational.Raw.subtreeGraph_unfold
#print axioms Rational.Raw.rational_iff_unfold
#print axioms Rational.Raw.ofTerm_subst
#print axioms Rational.Raw.ofTerm_injective
#print axioms Rational.Raw.eq_ofTerm_of_subst
#print axioms Rational.Raw.sharing_unobservable
#print axioms Rational.Raw.distinct_variables_unshared
#print axioms Rational.rationalAction

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
