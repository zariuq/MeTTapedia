import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RationalTrees

/-!
# Unification over rational trees is unitary

Over rational trees every finite store of equations has a most general solution or a refutation,
and the refutations are clashes only: there is no occurs check.

**The closure** (`Joined`): the least equivalence containing the store's equations and closed under
decomposition (equal function symbols join their children). It is a calculus: a joining is a finite
derivation. **A refutation** (`Clash`) is a joining of two different labels that are not variables,
for example `f(…)` with `g(…)` or two distinct constants.

**Soundness of refutations** (`not_unifies_of_clash`): every solution identifies what the closure
joins (`Joined.sound`), so a clash has no solution, in any algebra of trees, finite or not.

**The solved form** (`classTree`, `mguRaw`): the class of a tree under the closure unfolds to a tree:
the label of a rigid member of the class, with the classes of that member's children below it, or a
variable of the class when the class has no rigid member. A variable is sent to the unfolding of its
class. Without a clash:
* it is a solution (`mguRaw_unifies`): every well-formed tree goes to the unfolding of its class
  (`subst_mguRaw`), and joined trees have the same class;
* it is most general, with the solution itself as the residual (`mguRaw_factors`): every solution
  `δ` satisfies `δ ∘ mgu = δ` on variables, so it is idempotent (`mgu_idempotent`);
* its values are well formed (`wf_classTree`) and rational when the store is (`rational_classTree`).

**The dichotomy** (`principal_or_refuted`, `consistent_iff_not_refuted`): in the rational-tree frames
every store has the principal answer `mgu store` or a clash, and not both.

The construction here is classical (it chooses members of classes): it is the model-theoretic
unification theorem, over all well-formed trees. On finite presentations the same closure is
computed and decides unifiability (`RationalDecision`), and the solved form is a computed finite
graph (`RationalSolvedForm`). The executable comparison that remembers compound pairs
(`Logic.LP.RuntimeUnification`) is a further algorithmic side; its rational soundness is not proved
here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Rational

open Mettapedia.Logic.LP

namespace Raw

variable {σ : LPSignature}

/-- **The closure of a store**: the least equivalence containing its equations and closed under
decomposition of equal function symbols. -/
inductive Joined (store : List (Raw σ × Raw σ)) : Raw σ → Raw σ → Prop
  | base {s t : Raw σ} : (s, t) ∈ store → Joined store s t
  | refl (t : Raw σ) : Joined store t t
  | symm {s t : Raw σ} : Joined store s t → Joined store t s
  | trans {s t u : Raw σ} : Joined store s t → Joined store t u → Joined store s u
  | down {s t : Raw σ} {f : σ.functionSymbols} {i : ℕ} : Joined store s t →
      s [] = some (.fn f) → t [] = some (.fn f) → i < σ.functionArity f →
      Joined store (child i s) (child i t)

/-- **A refutation**: the closure joins two different labels that are not variables. -/
def Clash (store : List (Raw σ × Raw σ)) : Prop :=
  ∃ (s t : Raw σ) (hs ht : Head σ), Joined store s t ∧ s [] = some hs ∧ t [] = some ht ∧
    hs.Rigid ∧ ht.Rigid ∧ hs ≠ ht

/-- A substitution of trees solving every equation of a store. -/
def Unifies (θ : σ.vars → Raw σ) (store : List (Raw σ × Raw σ)) : Prop :=
  ∀ e ∈ store, subst θ e.1 = subst θ e.2

theorem rigid_fn (f : σ.functionSymbols) : (Head.fn f : Head σ).Rigid := fun _ same => by cases same

theorem fn_of_rigid {h : Head σ} (rigid : h.Rigid) {i : ℕ} (inside : i < h.arity) :
    ∃ f, h = .fn f := by
  cases h with
  | var v => exact absurd rfl (rigid v)
  | const c => exact absurd inside (Nat.not_lt_zero i)
  | fn f => exact ⟨f, rfl⟩

variable {store : List (Raw σ × Raw σ)}

/-- **Every solution identifies what the closure joins.** -/
theorem Joined.sound {θ : σ.vars → Raw σ} (unifies : Unifies θ store) {s t : Raw σ}
    (joined : Joined store s t) : subst θ s = subst θ t := by
  induction joined with
  | base member => exact unifies _ member
  | refl t => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | @down s t f i _ rs rt _ ih =>
    have kids := congrArg (child i) ih
    rwa [child_subst (notVar_of_rigid rs (rigid_fn f)), child_subst (notVar_of_rigid rt (rigid_fn f))]
      at kids

/-- **A refutation has no solution**, in any algebra of trees. -/
theorem not_unifies_of_clash (clash : Clash store) (θ : σ.vars → Raw σ) : ¬ Unifies θ store := by
  intro unifies
  obtain ⟨s, t, hs, ht, joined, rs, rt, rigidS, rigidT, distinct⟩ := clash
  have roots := congrFun (joined.sound unifies) []
  rw [subst_nil (notVar_of_rigid rs rigidS), subst_nil (notVar_of_rigid rt rigidT), rs, rt] at roots
  exact distinct (Option.some.inj roots)

/-- The closure only joins a tree with itself or members of a set that contains the store and is
closed under decomposition. -/
theorem Joined.closed (G : Set (Raw σ)) (base : ∀ e ∈ store, e.1 ∈ G ∧ e.2 ∈ G)
    (down : ∀ s ∈ G, ∀ (f : σ.functionSymbols) (i : ℕ), s [] = some (.fn f) → i < σ.functionArity f →
      child i s ∈ G)
    {s t : Raw σ} (joined : Joined store s t) : s = t ∨ (s ∈ G ∧ t ∈ G) := by
  induction joined with
  | base member => exact Or.inr (base _ member)
  | refl => exact Or.inl rfl
  | symm _ ih =>
    rcases ih with same | ⟨left, right⟩
    · exact Or.inl same.symm
    · exact Or.inr ⟨right, left⟩
  | trans _ _ ih₁ ih₂ =>
    rcases ih₁ with rfl | ⟨left, _⟩
    · exact ih₂
    · rcases ih₂ with rfl | ⟨_, right⟩
      · exact Or.inr ⟨left, by assumption⟩
      · exact Or.inr ⟨left, right⟩
  | @down s t f i _ rs rt inside ih =>
    rcases ih with rfl | ⟨left, right⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨down s left f i rs inside, down t right f i rt inside⟩

/-- Joined trees have the same class. -/
theorem Joined.class_eq {s t : Raw σ} (joined : Joined store s t) :
    Joined store s = Joined store t :=
  funext fun _ => propext ⟨fun h => joined.symm.trans h, fun h => joined.trans h⟩

/-- With well-formed equations, the closure joins well-formed trees only with well-formed trees. -/
theorem Joined.wf (hstore : ∀ e ∈ store, WF e.1 ∧ WF e.2) {s t : Raw σ} (joined : Joined store s t)
    (ws : WF s) : WF t := by
  rcases joined.closed {a | WF a} hstore
      (fun s ws f i rs inside => WF.child_wf ws rs inside) with rfl | ⟨_, wt⟩
  · exact ws
  · exact wt

/-! ## Classes and their unfolding -/

/-- A class with a member whose root is not a variable. -/
def Structured (C : Raw σ → Prop) : Prop := ∃ y, C y ∧ ∃ h : Head σ, y [] = some h ∧ h.Rigid

/-- The chosen rigid member of a structured class. -/
noncomputable def pick {C : Raw σ → Prop} (structured : Structured C) : Raw σ :=
  Classical.choose structured

theorem pick_mem {C : Raw σ → Prop} (structured : Structured C) : C (pick structured) :=
  (Classical.choose_spec structured).1

theorem pick_root {C : Raw σ → Prop} (structured : Structured C) :
    ∃ h : Head σ, pick structured [] = some h ∧ h.Rigid :=
  (Classical.choose_spec structured).2

/-- The arity of an optional label. -/
def arityOf : Option (Head σ) → ℕ
  | some h => h.arity
  | none => 0

open Classical in
/-- A variable of a class, when it has one. -/
noncomputable def classVar (C : Raw σ → Prop) : Option σ.vars :=
  if exists_var : ∃ w, C (leaf w) then some (Classical.choose exists_var) else none

theorem classVar_spec {C : Raw σ → Prop} (exists_var : ∃ w, C (leaf w)) :
    ∃ w, classVar C = some w ∧ C (leaf w) :=
  ⟨Classical.choose exists_var, dif_pos exists_var, Classical.choose_spec exists_var⟩

variable (store) in
open Classical in
/-- The unfolding of a class, read at a path. -/
noncomputable def classAt : List ℕ → (Raw σ → Prop) → Option (Head σ)
  | [], C => if structured : Structured C then pick structured [] else (classVar C).map Head.var
  | i :: q, C => if structured : Structured C then
      (if i < arityOf (pick structured []) then classAt q (Joined store (child i (pick structured)))
        else none)
      else none

variable (store) in
/-- **The unfolding of a class**: the root of its rigid member over the classes of that member's
children, or a variable of the class. -/
noncomputable def classTree (C : Raw σ → Prop) : Raw σ := fun p => classAt store p C

theorem classTree_structured {C : Raw σ → Prop} (structured : Structured C) {h : Head σ}
    (root : pick structured [] = some h) :
    classTree store C = node h fun i => classTree store (Joined store (child i (pick structured))) := by
  funext p
  cases p with
  | nil =>
    show classAt store [] C = some h
    simp only [classAt, dif_pos structured, root]
  | cons i q =>
    show classAt store (i :: q) C = node h _ (i :: q)
    simp only [classAt, dif_pos structured, root, arityOf, node]
    rfl

theorem classTree_cons_of_not {C : Raw σ → Prop} (unstructured : ¬ Structured C) (i : ℕ)
    (q : List ℕ) : classTree store C (i :: q) = none := by
  show classAt store (i :: q) C = none
  simp only [classAt, dif_neg unstructured]

theorem classTree_var {C : Raw σ → Prop} (unstructured : ¬ Structured C) {w : σ.vars}
    (found : classVar C = some w) : classTree store C = leaf w := by
  funext p
  cases p with
  | nil =>
    show classAt store [] C = some (.var w)
    simp only [classAt, dif_neg unstructured, found, Option.map_some]
  | cons i q =>
    rw [classTree_cons_of_not unstructured]
    rfl

/-- The class of a well-formed tree without a rigid member has a variable. -/
theorem classVar_of_unstructured {x : Raw σ} (wx : WF x) (unstructured : ¬ Structured (Joined store x)) :
    ∃ w, classVar (Joined store x) = some w ∧ Joined store x (leaf w) := by
  obtain ⟨h, root⟩ := wx.root_some
  rcases h.rigid_or_var with rigid | ⟨v, rfl⟩
  · exact absurd ⟨x, Joined.refl x, h, root, rigid⟩ unstructured
  · refine classVar_spec ⟨v, ?_⟩
    rw [← wx.eq_leaf root]
    exact Joined.refl x

/-- **Classes of well-formed trees unfold to well-formed trees.** -/
theorem wf_classTree (hstore : ∀ e ∈ store, WF e.1 ∧ WF e.2) {x : Raw σ} (wx : WF x) :
    WF (classTree store (Joined store x)) := by
  refine wf_of_nodes (fun a => ∃ x, WF x ∧ a = classTree store (Joined store x)) ?_ ⟨x, wx, rfl⟩
  rintro _ ⟨x, wx, rfl⟩
  by_cases structured : Structured (Joined store x)
  · obtain ⟨h, root, rigid⟩ := pick_root structured
    have wy : WF (pick structured) := (pick_mem structured).wf hstore wx
    exact ⟨h, _, classTree_structured structured root,
      fun i inside => ⟨_, wy.child_wf root inside, rfl⟩⟩
  · obtain ⟨w, found, -⟩ := classVar_of_unstructured wx structured
    exact ⟨.var w, fun _ => bot, classTree_var structured found,
      fun i inside => absurd inside (Nat.not_lt_zero i)⟩

/-! ## The solved form -/

variable (store) in
/-- **The solved form**: each variable goes to the unfolding of its class. -/
noncomputable def mguRaw (v : σ.vars) : Raw σ := classTree store (Joined store (leaf v))

/-- **Without a clash, the solved form sends a well-formed tree to the unfolding of its class.** -/
theorem subst_mguRaw (noClash : ¬ Clash store) {x : Raw σ} (wx : WF x) :
    subst (mguRaw store) x = classTree store (Joined store x) := by
  refine eq_of_bisim_or (fun a b => ∃ x, WF x ∧ a = subst (mguRaw store) x ∧
    b = classTree store (Joined store x)) ?_ ⟨x, wx, rfl, rfl⟩
  rintro _ _ ⟨x, wx, rfl, rfl⟩
  obtain ⟨h, root⟩ := wx.root_some
  rcases h.rigid_or_var with rigid | ⟨u, rfl⟩
  · have structured : Structured (Joined store x) := ⟨x, Joined.refl x, h, root, rigid⟩
    obtain ⟨h', root', rigid'⟩ := pick_root structured
    have joined := pick_mem structured
    have same : h = h' := by
      by_contra distinct
      exact noClash ⟨x, _, h, h', joined, root, root', rigid, rigid', distinct⟩
    subst same
    have notVar := notVar_of_rigid root rigid
    rw [classTree_structured structured root']
    refine Or.inr ⟨by rw [subst_nil notVar, root]; rfl, fun i => ?_⟩
    rw [child_subst notVar, child_node]
    split_ifs with inside
    · obtain ⟨f, rfl⟩ := fn_of_rigid rigid inside
      have kids : Joined store (child i x) (child i (pick structured)) :=
        Joined.down joined root root' inside
      exact Or.inr ⟨child i x, wx.child_wf root inside, rfl, by rw [kids.class_eq]⟩
    · rw [wx.child_eq_bot root (not_lt.mp inside), subst_bot]
      exact Or.inl rfl
  · left
    rw [subst_of_var root, wx.eq_leaf root]
    rfl

/-- **Without a clash, the solved form is a solution.** -/
theorem mguRaw_unifies (noClash : ¬ Clash store) (hstore : ∀ e ∈ store, WF e.1 ∧ WF e.2) :
    Unifies (mguRaw store) store := by
  intro e member
  rw [subst_mguRaw noClash (hstore e member).1, subst_mguRaw noClash (hstore e member).2,
    (Joined.base member).class_eq]

/-- **Every solution factors through the unfolding of classes, by itself.** -/
theorem subst_classTree (hstore : ∀ e ∈ store, WF e.1 ∧ WF e.2) {δ : σ.vars → Raw σ}
    (unifies : Unifies δ store) {x : Raw σ} (wx : WF x) :
    subst δ (classTree store (Joined store x)) = subst δ x := by
  refine eq_of_bisim_or (fun a b => ∃ x, WF x ∧ a = subst δ (classTree store (Joined store x)) ∧
    b = subst δ x) ?_ ⟨x, wx, rfl, rfl⟩
  rintro _ _ ⟨x, wx, rfl, rfl⟩
  by_cases structured : Structured (Joined store x)
  · obtain ⟨h, root, rigid⟩ := pick_root structured
    have joined := pick_mem structured
    have wy : WF (pick structured) := joined.wf hstore wx
    have left : subst δ (classTree store (Joined store x)) =
        node h fun i => subst δ (classTree store (Joined store (child i (pick structured)))) := by
      rw [classTree_structured structured root, subst_node δ rigid]
    have right : subst δ x = node h fun i => subst δ (child i (pick structured)) := by
      rw [joined.sound unifies]
      conv_lhs => rw [wy.eq_node root]
      exact subst_node δ rigid _
    rw [left, right]
    refine Or.inr ⟨rfl, fun i => ?_⟩
    rw [child_node, child_node]
    split_ifs with inside
    · exact Or.inr ⟨child i (pick structured), wy.child_wf root inside, rfl, rfl⟩
    · exact Or.inl rfl
  · obtain ⟨w, found, joined⟩ := classVar_of_unstructured wx structured
    left
    rw [classTree_var structured found, joined.sound unifies]

/-- **Most generality, with the solution itself as the residual**: `δ ∘ mgu = δ` on variables. -/
theorem mguRaw_factors (hstore : ∀ e ∈ store, WF e.1 ∧ WF e.2) {δ : σ.vars → Raw σ}
    (unifies : Unifies δ store) (v : σ.vars) : subst δ (mguRaw store v) = δ v := by
  have := subst_classTree hstore unifies (wf_leaf v)
  rwa [subst_leaf] at this

/-- The subtrees of a store's terms. -/
def subtreesOf (store : List (Raw σ × Raw σ)) : Set (Raw σ) :=
  ⋃ e ∈ {e | e ∈ store}, (Set.range fun p => sub p e.1) ∪ Set.range fun p => sub p e.2

theorem child_mem_subtreesOf {s : Raw σ} (member : s ∈ subtreesOf store) (i : ℕ) :
    child i s ∈ subtreesOf store := by
  obtain ⟨e, present, inside⟩ := Set.mem_iUnion₂.mp member
  refine Set.mem_biUnion present ?_
  rcases inside with ⟨p, rfl⟩ | ⟨p, rfl⟩
  · exact Or.inl ⟨p ++ [i], (child_sub p i _).symm⟩
  · exact Or.inr ⟨p ++ [i], (child_sub p i _).symm⟩

theorem subtreesOf_finite (hstore : ∀ e ∈ store, IsRational e.1 ∧ IsRational e.2) :
    (subtreesOf store).Finite :=
  (store.finite_toSet).biUnion fun e member => ((hstore e member).1).union (hstore e member).2

/-- **Over rational equations, classes of variables unfold to rational trees.** -/
theorem rational_classTree (hstore : ∀ e ∈ store, IsRational e.1 ∧ IsRational e.2) (v : σ.vars) :
    IsRational (classTree store (Joined store (leaf v))) := by
  let reach : Set (Raw σ) := insert (leaf v) (subtreesOf store)
  let S : Set (Raw σ) := insert bot ((fun z => classTree store (Joined store z)) '' reach)
  have finite : S.Finite := (((subtreesOf_finite hstore).insert _).image _).insert _
  have closedStore : ∀ s ∈ subtreesOf store, ∀ (f : σ.functionSymbols) (i : ℕ),
      s [] = some (.fn f) → i < σ.functionArity f → child i s ∈ subtreesOf store :=
    fun s member _ i _ _ => child_mem_subtreesOf member i
  have baseStore : ∀ e ∈ store, e.1 ∈ subtreesOf store ∧ e.2 ∈ subtreesOf store := fun e member =>
    ⟨Set.mem_biUnion member (Or.inl ⟨[], rfl⟩), Set.mem_biUnion member (Or.inr ⟨[], rfl⟩)⟩
  have key : ∀ p x, x ∈ reach → sub p (classTree store (Joined store x)) ∈ S := by
    intro p
    induction p with
    | nil => intro x member; exact Or.inr ⟨x, member, rfl⟩
    | cons i q ih =>
      intro x member
      by_cases structured : Structured (Joined store x)
      · obtain ⟨h, root, rigid⟩ := pick_root structured
        rw [classTree_structured structured root, sub_cons, child_node]
        split_ifs with inside
        · refine ih _ (Or.inr (child_mem_subtreesOf ?_ i))
          rcases (pick_mem structured).closed (subtreesOf store) baseStore closedStore with
            same | ⟨_, picked⟩
          · rcases member with rfl | inStore
            · rw [← same] at root
              exact absurd (Option.some.inj root).symm (rigid v)
            · rw [← same]
              exact inStore
          · exact picked
        · exact Or.inl rfl
      · have : sub (i :: q) (classTree store (Joined store x)) = bot := by
          funext r
          exact classTree_cons_of_not structured i (q ++ r)
        rw [this]
        exact Or.inl rfl
  exact rational_of_subset S finite fun p => key p (leaf v) (Set.mem_insert _ _)

end Raw

/-! ## The dichotomy in the rational-tree frames -/

variable {σ : LPSignature}

/-- The equations of a store of rational trees, as trees. -/
def rawStore (store : EquationStore (RTree σ)) : List (Raw σ × Raw σ) :=
  store.map fun e => (e.1.1, e.2.1)

theorem rawStore_wf (store : EquationStore (RTree σ)) :
    ∀ e ∈ rawStore store, Raw.WF e.1 ∧ Raw.WF e.2 := by
  intro e member
  obtain ⟨e', _, rfl⟩ := List.mem_map.mp member
  exact ⟨e'.1.2.1, e'.2.2.1⟩

theorem rawStore_rational (store : EquationStore (RTree σ)) :
    ∀ e ∈ rawStore store, Raw.IsRational e.1 ∧ Raw.IsRational e.2 := by
  intro e member
  obtain ⟨e', _, rfl⟩ := List.mem_map.mp member
  exact ⟨e'.1.2.2, e'.2.2.2⟩

/-- **A refutation of a store of rational trees**: a clash in its closure. -/
def Refuted (store : EquationStore (RTree σ)) : Prop := Raw.Clash (rawStore store)

/-- **The solved form of a store of rational trees.** -/
noncomputable def mgu (store : EquationStore (RTree σ)) : RSubst σ := fun v =>
  ⟨Raw.mguRaw (rawStore store) v, Raw.wf_classTree (rawStore_wf store) (Raw.wf_leaf v),
    Raw.rational_classTree (rawStore_rational store) v⟩

theorem models_iff_unifies (θ : RSubst σ) (store : EquationStore (RTree σ)) :
    (rationalAction σ).Models θ store ↔ Raw.Unifies (fun v => (θ v).1) (rawStore store) := by
  unfold SubstitutionAction.Models Raw.Unifies rawStore
  rw [List.forall_mem_map]
  exact forall₂_congr fun e _ => ⟨congrArg Subtype.val,
    fun same => (RTree.ext same : RTree.subst θ e.1 = RTree.subst θ e.2)⟩

/-- **A refuted store has no solution.** -/
theorem refuted_inconsistent {store : EquationStore (RTree σ)} (refuted : Refuted store) :
    ¬ (rationalAction σ).Consistent store := by
  rintro ⟨θ, solved⟩
  exact Raw.not_unifies_of_clash refuted _ ((models_iff_unifies θ store).mp solved)

/-- **Every solution factors through the solved form, by itself.** -/
theorem mgu_factors {store : EquationStore (RTree σ)} {δ : RSubst σ}
    (solved : (rationalAction σ).Models δ store) (v : σ.vars) :
    RTree.subst δ (mgu store v) = δ v :=
  RTree.ext (Raw.mguRaw_factors (rawStore_wf store) ((models_iff_unifies δ store).mp solved) v)

/-- **Without a refutation, the solved form is a principal answer.** -/
theorem mgu_principal {store : EquationStore (RTree σ)} (unrefuted : ¬ Refuted store) :
    (rationalAction σ).Principal store (mgu store) := by
  refine ⟨(models_iff_unifies _ store).mpr (Raw.mguRaw_unifies unrefuted (rawStore_wf store)), ?_⟩
  intro δ solved
  refine ⟨δ, fun t => ?_⟩
  have through : (rationalAction σ).compose δ (mgu store) = δ := funext (mgu_factors solved)
  rw [through]
  exact rfl

/-- **Unification over rational trees is unitary**: a principal answer or a refutation. -/
theorem principal_or_refuted (store : EquationStore (RTree σ)) :
    (rationalAction σ).Principal store (mgu store) ∨ Refuted store := by
  by_cases refuted : Refuted store
  · exact Or.inr refuted
  · exact Or.inl (mgu_principal refuted)

/-- **Solvability is the absence of a clash.** -/
theorem consistent_iff_not_refuted (store : EquationStore (RTree σ)) :
    (rationalAction σ).Consistent store ↔ ¬ Refuted store :=
  ⟨fun consistent refuted => refuted_inconsistent refuted consistent,
    fun unrefuted => ⟨mgu store, (mgu_principal unrefuted).sound⟩⟩

/-- **The solved form is idempotent.** -/
theorem mgu_idempotent {store : EquationStore (RTree σ)} (unrefuted : ¬ Refuted store) (v : σ.vars) :
    RTree.subst (mgu store) (mgu store v) = mgu store v :=
  mgu_factors (mgu_principal unrefuted).sound v

/-- In the rational-tree frames. -/
theorem frames_principal_or_refuted (store : EquationStore (RTree σ)) :
    (rationalFrames σ).Principal (a := PUnit.unit) (m := PUnit.unit) store (mgu store) ∨
      Refuted store :=
  (principal_or_refuted store).imp (Interface.Frames.ofSubstitution_principal_iff _ _ _).mpr id

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Rational

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

#print axioms Rational.Raw.Joined.sound
#print axioms Rational.Raw.not_unifies_of_clash
#print axioms Rational.Raw.wf_classTree
#print axioms Rational.Raw.subst_mguRaw
#print axioms Rational.Raw.mguRaw_unifies
#print axioms Rational.Raw.mguRaw_factors
#print axioms Rational.Raw.rational_classTree
#print axioms Rational.refuted_inconsistent
#print axioms Rational.mgu_factors
#print axioms Rational.mgu_principal
#print axioms Rational.principal_or_refuted
#print axioms Rational.consistent_iff_not_refuted
#print axioms Rational.mgu_idempotent
#print axioms Rational.frames_principal_or_refuted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
