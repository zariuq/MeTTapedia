import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RationalDecision

/-!
# The solved form, computed

From the computed closure on the nodes of a finite presentation, the solved form is a finite graph
on the same nodes (`solvedGraph`): each node is presented by the representative of its class, the
least rigid member when the class has one and otherwise its least member, which is then a
variable (`rep`). A variable is sent to the solved graph's unfolding at its least node, or to itself
when it does not occur (`solvedSubst`).

**Without a refutation the computed solved form is a principal answer** (`solvedSubst_principal`):
it solves the store (`subst_solved`), and every solution `δ` satisfies `δ ∘ solved = δ`
(`solved_factors`). Together with `consistent_rstore_iff_unifiable` this is rational-tree
unification as a computation: it returns a finite presentation of a most general solution, or a
refutation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Rational

open Mettapedia.Logic.LP

namespace Raw.Graph

variable {σ : LPSignature} {N : Type*} [Fintype N] [DecidableEq N] [LinearOrder N]
  [DecidableEq (Head σ)] (G : Graph σ N) (E : List (N × N))

/-- The class of a node under the computed closure. -/
def classOf (k : N) : Finset N := Finset.univ.filter fun m => (k, m) ∈ closure G E

omit [LinearOrder N] in
theorem mem_classOf {k m : N} : m ∈ G.classOf E k ↔ NodeJoined G E k m := by
  simp [classOf, mem_closure_iff]

omit [LinearOrder N] in
theorem classOf_nonempty (k : N) : (G.classOf E k).Nonempty :=
  ⟨k, (G.mem_classOf E).mpr (.same rfl)⟩

omit [LinearOrder N] in
theorem classOf_eq {k k' : N} (joined : NodeJoined G E k k') : G.classOf E k = G.classOf E k' := by
  ext m
  rw [mem_classOf, mem_classOf]
  exact ⟨fun h => joined.symm.trans h, fun h => joined.trans h⟩

/-- The rigid members of a class. -/
def rigidOf (C : Finset N) : Finset N := C.filter fun m => (G.label m).isVar = false

/-- The representative of a class: its least rigid member, else its least member. -/
def repOf (C : Finset N) (nonempty : C.Nonempty) : N :=
  if h : (G.rigidOf C).Nonempty then (G.rigidOf C).min' h else C.min' nonempty

/-- **The representative of a node's class.** -/
def rep (k : N) : N := G.repOf (G.classOf E k) (G.classOf_nonempty E k)

theorem rep_congr {k k' : N} (joined : NodeJoined G E k k') : G.rep E k = G.rep E k' := by
  unfold rep
  have same := G.classOf_eq E joined
  generalize G.classOf_nonempty E k = h
  generalize G.classOf_nonempty E k' = h'
  revert h h'
  rw [same]
  intro _ _
  rfl

theorem rep_joined (k : N) : NodeJoined G E k (G.rep E k) := by
  rw [← mem_classOf]
  unfold rep repOf
  split_ifs with h
  · exact (Finset.mem_filter.mp (Finset.min'_mem _ h)).1
  · exact Finset.min'_mem _ _

theorem rep_rigid {k m : N} (joined : NodeJoined G E k m) (rigid : (G.label m).isVar = false) :
    (G.label (G.rep E k)).isVar = false := by
  have present : (G.rigidOf (G.classOf E k)).Nonempty :=
    ⟨m, Finset.mem_filter.mpr ⟨(G.mem_classOf E).mpr joined, rigid⟩⟩
  unfold rep repOf
  rw [dif_pos present]
  exact (Finset.mem_filter.mp (Finset.min'_mem _ present)).2

/-- **The solved form, as a finite graph on the same nodes.** -/
def solvedGraph : Graph σ N where
  label k := G.label (G.rep E k)
  edge k i := G.edge (G.rep E k) i

theorem solved_unfold_congr {k k' : N} (same : G.rep E k = G.rep E k') :
    (G.solvedGraph E).unfold k = (G.solvedGraph E).unfold k' := by
  rw [(G.solvedGraph E).unfold_eq k, (G.solvedGraph E).unfold_eq k']
  show node (G.label (G.rep E k)) (fun i => (G.solvedGraph E).unfold (G.edge (G.rep E k) i)) =
    node (G.label (G.rep E k')) (fun i => (G.solvedGraph E).unfold (G.edge (G.rep E k') i))
  rw [same]

/-- The nodes labelled by a variable. -/
def varNodes (v : σ.vars) : Finset N := Finset.univ.filter fun k => G.label k = .var v

/-- **The solved form, as a substitution**: a variable goes to the solved graph's unfolding at its
least node, or to itself when it does not occur. -/
def solvedRaw (v : σ.vars) : Raw σ :=
  if h : (G.varNodes v).Nonempty then (G.solvedGraph E).unfold ((G.varNodes v).min' h) else leaf v

theorem solvedRaw_wf (v : σ.vars) : WF (G.solvedRaw E v) := by
  unfold solvedRaw
  split_ifs
  · exact (G.solvedGraph E).wf_unfold _
  · exact wf_leaf v

theorem solvedRaw_rational (v : σ.vars) : IsRational (G.solvedRaw E v) := by
  unfold solvedRaw
  split_ifs
  · exact (G.solvedGraph E).rational_unfold _
  · exact rational_leaf v

omit [Fintype N] [DecidableEq N] [LinearOrder N] [DecidableEq (Head σ)] in
theorem unfold_of_var {k : N} {v : σ.vars} (labelled : G.label k = .var v) : G.unfold k = leaf v := by
  rw [G.unfold_eq k, labelled]
  exact node_congr fun i inside => absurd inside (Nat.not_lt_zero i)

/-- At a variable node the solved form is the solved graph's unfolding there. -/
theorem solvedRaw_at_var {k : N} {v : σ.vars} (labelled : G.label k = .var v) :
    G.solvedRaw E v = (G.solvedGraph E).unfold k := by
  have present : (G.varNodes v).Nonempty := ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, labelled⟩⟩
  unfold solvedRaw
  rw [dif_pos present]
  have least := (Finset.mem_filter.mp (Finset.min'_mem _ present)).2
  refine G.solved_unfold_congr E (G.rep_congr E (.same ?_))
  rw [G.unfold_of_var least, G.unfold_of_var labelled]

/-- **Without a refutation, the solved form sends each node's tree to the solved graph's
unfolding.** -/
theorem subst_solved (noClash : ¬ G.NodeClash E) (k : N) :
    subst (G.solvedRaw E) (G.unfold k) = (G.solvedGraph E).unfold k := by
  refine eq_of_bisim_or (fun a b => ∃ k, a = subst (G.solvedRaw E) (G.unfold k) ∧
    b = (G.solvedGraph E).unfold k) ?_ ⟨k, rfl, rfl⟩
  rintro _ _ ⟨k, rfl, rfl⟩
  rcases (G.label k).rigid_or_var with rigid | ⟨v, labelled⟩
  · have joined := G.rep_joined E k
    have repRigid := G.rep_rigid E (.same rfl) ((Head.rigid_iff_isVar _).mp rigid)
    have labels : G.label k = G.label (G.rep E k) := by
      by_contra distinct
      exact noClash ⟨k, _, joined, rigid, (Head.rigid_iff_isVar _).mpr repRigid, distinct⟩
    have notVar := notVar_of_rigid (G.unfold_nil k) rigid
    refine Or.inr ⟨?_, fun i => ?_⟩
    · rw [subst_nil notVar, unfold_nil, unfold_nil]
      exact congrArg some labels
    · have solvedChild : child i ((G.solvedGraph E).unfold k) =
          if i < (G.label (G.rep E k)).arity then (G.solvedGraph E).unfold (G.edge (G.rep E k) i)
          else bot := (G.solvedGraph E).child_unfold k i
      rw [child_subst notVar, G.child_unfold, solvedChild, ← labels]
      split_ifs with inside
      · obtain ⟨f, lf⟩ := fn_of_rigid rigid inside
        have below : i < σ.functionArity f := by rw [lf] at inside; exact inside
        have kids : NodeJoined G E (G.edge k i) (G.edge (G.rep E k) i) :=
          .down joined lf (labels ▸ lf) below
        exact Or.inr ⟨G.edge k i, rfl, G.solved_unfold_congr E (G.rep_congr E kids).symm⟩
      · exact Or.inl (subst_bot _)
  · left
    rw [G.unfold_of_var labelled, subst_leaf, G.solvedRaw_at_var E labelled]

/-- **Every solution factors through the solved form, by itself.** -/
theorem solved_factors {δ : σ.vars → Raw σ} (unifies : Unifies δ (G.store E)) (k : N) :
    subst δ ((G.solvedGraph E).unfold k) = subst δ (G.unfold k) := by
  refine eq_of_bisim_or (fun a b => ∃ k, a = subst δ ((G.solvedGraph E).unfold k) ∧
    b = subst δ (G.unfold k)) ?_ ⟨k, rfl, rfl⟩
  rintro _ _ ⟨k, rfl, rfl⟩
  have joined := G.rep_joined E k
  have same : subst δ (G.unfold k) = subst δ (G.unfold (G.rep E k)) := joined.joined.sound unifies
  rw [same]
  rcases (G.label (G.rep E k)).rigid_or_var with rigid | ⟨w, labelled⟩
  · have solvedEq : (G.solvedGraph E).unfold k =
        node (G.label (G.rep E k)) fun i => (G.solvedGraph E).unfold (G.edge (G.rep E k) i) :=
      (G.solvedGraph E).unfold_eq k
    rw [solvedEq, G.unfold_eq (G.rep E k), subst_node δ rigid, subst_node δ rigid]
    refine Or.inr ⟨rfl, fun i => ?_⟩
    rw [child_node, child_node]
    split_ifs
    · exact Or.inr ⟨_, rfl, rfl⟩
    · exact Or.inl rfl
  · left
    have solvedLeaf : (G.solvedGraph E).unfold k = leaf w := by
      rw [(G.solvedGraph E).unfold_eq k]
      show node (G.label (G.rep E k)) _ = _
      rw [labelled]
      exact node_congr fun i inside => absurd inside (Nat.not_lt_zero i)
    rw [solvedLeaf, G.unfold_of_var labelled]

/-- The solved form as a rational substitution. -/
def solvedSubst : RSubst σ := fun v => ⟨G.solvedRaw E v, G.solvedRaw_wf E v, G.solvedRaw_rational E v⟩

/-- **Without a refutation, the computed solved form is a principal answer.** -/
theorem solvedSubst_principal (noClash : ¬ G.NodeClash E) :
    (rationalAction σ).Principal (G.rstore E) (G.solvedSubst E) := by
  refine ⟨?_, ?_⟩
  · refine (models_iff_unifies _ _).mpr ?_
    rw [rawStore_rstore]
    intro e member
    obtain ⟨⟨k, l⟩, present, rfl⟩ := List.mem_map.mp member
    show subst (G.solvedRaw E) (G.unfold k) = subst (G.solvedRaw E) (G.unfold l)
    rw [G.subst_solved E noClash, G.subst_solved E noClash]
    exact G.solved_unfold_congr E (G.rep_congr E (.base present))
  · intro δ solved
    have unifies : Unifies (fun v => (δ v).1) (G.store E) := by
      rw [← rawStore_rstore]
      exact (models_iff_unifies δ _).mp solved
    refine ⟨δ, fun t => ?_⟩
    have pointwise : ∀ v, RTree.subst δ (G.solvedSubst E v) = δ v := by
      intro v
      refine RTree.ext ?_
      show subst (fun w => (δ w).1) (G.solvedRaw E v) = (δ v).1
      unfold solvedRaw
      split_ifs with present
      · have least := (Finset.mem_filter.mp (Finset.min'_mem _ present)).2
        rw [G.solved_factors E unifies, G.unfold_of_var least, subst_leaf]
      · exact subst_leaf _ v
    have composed : (rationalAction σ).compose δ (G.solvedSubst E) = δ := funext pointwise
    rw [composed]
    exact rfl

end Raw.Graph

/-! ## Control: the computed solved form of `X = f(X)` -/

namespace Controls

open Raw

/-- **The computed solved form of `X = f(X)` is principal and sends `X` to `f(f(f(…)))`.** -/
theorem loopPresented_solved :
    (rationalAction ctlSig).Principal (loopPresented.rstore [(0, 1)])
        (loopPresented.solvedSubst [(0, 1)]) ∧
      loopPresented.solvedSubst [(0, 1)] 0 = loop .f := by
  have noClash : ¬ loopPresented.NodeClash [(0, 1)] :=
    (Graph.consistent_rstore_iff (G := loopPresented) (E := [(0, 1)])).mp loopPresented_consistent
  have principal := Graph.solvedSubst_principal loopPresented [(0, 1)] noClash
  refine ⟨principal, ?_⟩
  have raw := congrArg Subtype.val (principal.sound _ (List.mem_singleton_self _))
  change subst (fun v => (loopPresented.solvedSubst [(0, 1)] v).1) (loopPresented.unfold 0) =
    subst (fun v => (loopPresented.solvedSubst [(0, 1)] v).1) (loopPresented.unfold 1) at raw
  have u0 : loopPresented.unfold 0 = leaf (0 : ℕ) :=
    loopPresented.unfold_of_var (by simp [loopPresented])
  have l1 : loopPresented.label 1 = .fn Sym.f := by simp [loopPresented]
  have u1 : loopPresented.unfold 1 = node (.fn Sym.f) fun _ => leaf (0 : ℕ) := by
    rw [loopPresented.unfold_eq 1, l1]
    exact node_congr fun _ _ => u0
  rw [u0, u1, subst_leaf, subst_node _ (rigid_fn _)] at raw
  simp only [subst_leaf] at raw
  exact RTree.ext (eq_loop raw)

end Controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Rational

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

#print axioms Rational.Raw.Graph.rep_congr
#print axioms Rational.Raw.Graph.subst_solved
#print axioms Rational.Raw.Graph.solved_factors
#print axioms Rational.Raw.Graph.solvedSubst_principal
#print axioms Rational.Controls.loopPresented_solved

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
