import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Basic

/-!
# Unfolding traversals: one tree, many machines

Fix a program and a query.  The **unfolding tree** is the tree of activations
the rules generate: each node carries the answers produced at that activation
together with the sub-activations its body makes, in declaration order.  The
tree is defined by the rules alone — *no evaluation strategy occurs in its
definition*.  It is the strategy-neutral denotation of a recursive call.

Engines are then **traversals of that one tree**:

* an ordinary relational engine visits it depth-first, left-to-right, in
  declaration order — `preOrder`, the reference;
* an engine free to schedule differently visits it some other complete way —
  `postOrderRev` is a maximally different schedule, answers after subcalls and
  subcalls right-to-left;
* a demand-driven engine visits only as much as an observation requires —
  `demandTake`.

The two theorems of this module say what the differences do and do not cost.

* **Bag invariance** (`Complete` traversals, `postOrderRev_perm_preOrder`,
  `complete_perm`): every complete traversal produces the same answers with the
  same multiplicities.  Order is genuinely schedule-dependent —
  `order_is_schedule_dependent` exhibits two complete traversals whose outputs
  differ as lists — but the bag is not.  This is the precise sense in which
  engines with different schedules "agree", and the exact statement a
  cross-engine differential comparison is entitled to make.
* **Demanded-prefix agreement** (`demandTake_eq_take`): the demand-driven
  traversal computes *exactly* the demanded prefix of the complete traversal.
  Demand-driven evaluation is therefore a **traversal discipline, not a
  different semantics** — and with unbounded demand it recovers the complete
  traversal exactly (`demandTake_of_saturated`).

The operational half of the second theorem is stated without instrumenting a
counter: `demandTake_ignores_children` shows that once the demand is met at a
node, the result does not depend on that node's children *at all* — so an
implementation is free not to visit them, and no observation can detect the
difference.

Scope: trees here are finite, which is the setting in which "every complete
traversal" is meaningful.  Infinite unfoldings are the subject of the
productivity results, where finite approximants carry the observations.
-/

namespace Mettapedia.GSLT.Dynamics.UnfoldingTraversal

variable {Ans : Type}

/-! ## The unfolding tree -/

/-- An activation: the answers produced here, and the sub-activations the body
makes, in declaration order. -/
inductive Unfold (Ans : Type) where
  | node (here : List Ans) (children : List (Unfold Ans))

/-- Induction with the list hypothesis for children. -/
def Unfold.inductionOn {motive : Unfold Ans → Prop} (t : Unfold Ans)
    (hnode : ∀ here children, (∀ c ∈ children, motive c) →
      motive (.node here children)) : motive t :=
  match t with
  | .node here children =>
    hnode here children fun c _ => Unfold.inductionOn c hnode

/-! ## Traversals -/

/-- Depth-first, left-to-right, answers before subcalls: the declaration-order
schedule, taken as the reference. -/
def preOrder : Unfold Ans → List Ans
  | .node here children => here ++ children.flatMap preOrder

/-- A maximally different complete schedule: subcalls first, right-to-left,
answers last. -/
def postOrderRev : Unfold Ans → List Ans
  | .node here children => (children.reverse).flatMap postOrderRev ++ here

/-- A traversal is **complete** when it produces the reference answers up to
order — every answer, with its multiplicity, and nothing else. -/
def Complete (trav : Unfold Ans → List Ans) : Prop :=
  ∀ t, (trav t).Perm (preOrder t)

/-! ## Bag invariance -/

/-- Pointwise permuted images give permuted `flatMap`s. -/
theorem flatMap_perm_of_pointwise {α β : Type} {f g : α → List β} :
    ∀ (l : List α), (∀ a ∈ l, (f a).Perm (g a)) → (l.flatMap f).Perm (l.flatMap g)
  | [], _ => by simp
  | a :: rest, h => by
    simp only [List.flatMap_cons]
    exact (h a (by simp)).append
      (flatMap_perm_of_pointwise rest fun b hb => h b (by simp [hb]))

/-- The reference traversal is trivially complete. -/
theorem preOrder_complete : Complete (preOrder (Ans := Ans)) :=
  fun _ => List.Perm.refl _

/-- **The other schedule is complete too.**  Visiting subcalls first and
right-to-left produces the same answers with the same multiplicities. -/
theorem postOrderRev_perm_preOrder (t : Unfold Ans) :
    (postOrderRev t).Perm (preOrder t) := by
  induction t using Unfold.inductionOn with
  | hnode here children ih =>
    have hrev : ((children.reverse).flatMap postOrderRev).Perm
        (children.flatMap postOrderRev) :=
      List.Perm.flatMap_right _ (List.reverse_perm children)
    have hpt : (children.flatMap postOrderRev).Perm (children.flatMap preOrder) :=
      flatMap_perm_of_pointwise children fun c hc => ih c hc
    simp only [postOrderRev, preOrder]
    exact ((hrev.append_right here).trans
      (hpt.append_right here)).trans List.perm_append_comm

theorem postOrderRev_complete : Complete (postOrderRev (Ans := Ans)) :=
  postOrderRev_perm_preOrder

/-- **Bag invariance.**  Any two complete traversals agree on the answer bag:
same answers, same multiplicities, whatever their schedules. -/
theorem complete_perm {trav trav' : Unfold Ans → List Ans}
    (h : Complete trav) (h' : Complete trav') (t : Unfold Ans) :
    (trav t).Perm (trav' t) :=
  (h t).trans (h' t).symm

/-- **Order is genuinely schedule-dependent.**  Two complete traversals whose
outputs differ as lists: a root answering `0` with one subcall answering `1`.
The bag is shared; the sequence is not.  A cross-engine comparison may compare
bags and must not compare orders. -/
theorem order_is_schedule_dependent :
    ∃ t : Unfold Nat, postOrderRev t ≠ preOrder t := by
  refine ⟨.node [0] [.node [1] []], ?_⟩
  simp [postOrderRev, preOrder]

/-! ## Demand-driven traversal

`demandTake k` collects at most `k` answers in reference order.  When the
demand is exhausted the remaining demand is `0`, and a traversal with zero
demand produces nothing and consults nothing. -/

mutual

/-- Collect at most `k` answers from an activation, in reference order. -/
def demandTake (k : Nat) : Unfold Ans → List Ans
  | .node here children =>
    here.take k ++ demandForest (k - (here.take k).length) children

/-- Collect at most `k` answers from a sequence of sub-activations. -/
def demandForest (k : Nat) : List (Unfold Ans) → List Ans
  | [] => []
  | t :: rest =>
    demandTake k t ++ demandForest (k - (demandTake k t).length) rest

end

/-! ### Demanded-prefix agreement -/

/-- Trimming a prefix by the length actually taken is trimming by the full
length: the arithmetic both proofs below turn on. -/
private theorem sub_length_take {α : Type} (k : Nat) (l : List α) :
    k - (l.take k).length = k - l.length := by
  rw [List.length_take]; omega

/-- **Demanded-prefix agreement.**  The demand-driven traversal computes
exactly the demanded prefix of the complete traversal — not an approximation of
it, and not a reordering of it.  Demand-driven evaluation is therefore a
traversal discipline, not a weaker semantics. -/
theorem demandTake_eq_take (t : Unfold Ans) :
    ∀ k : Nat, demandTake k t = (preOrder t).take k := by
  induction t using Unfold.inductionOn with
  | hnode here children ih =>
    have hforest : ∀ (cs : List (Unfold Ans)),
        (∀ c ∈ cs, ∀ k : Nat, demandTake k c = (preOrder c).take k) →
        ∀ k : Nat, demandForest k cs = (cs.flatMap preOrder).take k := by
      intro cs
      induction cs with
      | nil => intro _ k; simp [demandForest]
      | cons c rest ihrest =>
        intro hcs k
        have hc : demandTake k c = (preOrder c).take k := hcs c (by simp) k
        simp only [demandForest, List.flatMap_cons, List.take_append, hc,
          sub_length_take, ihrest (fun d hd => hcs d (by simp [hd]))]
    intro k
    simp only [demandTake, preOrder, List.take_append, sub_length_take,
      hforest children ih]

/-- The same statement for a sequence of sub-activations. -/
theorem demandForest_eq_take (cs : List (Unfold Ans)) :
    ∀ k : Nat, demandForest k cs = (cs.flatMap preOrder).take k := by
  induction cs with
  | nil => intro k; simp [demandForest]
  | cons c rest ih =>
    intro k
    simp only [demandForest, List.flatMap_cons, List.take_append,
      demandTake_eq_take c k, sub_length_take, ih]

/-- Zero demand collects nothing. -/
theorem demandTake_zero (t : Unfold Ans) : demandTake 0 t = [] := by
  rw [demandTake_eq_take]; simp

/-- Zero demand collects nothing from a sequence of sub-activations either. -/
theorem demandForest_zero (cs : List (Unfold Ans)) : demandForest 0 cs = [] := by
  rw [demandForest_eq_take]; simp

/-- **Saturated demand recovers the complete traversal.**  Ask for everything
and the demand-driven schedule returns exactly the reference answers, in
reference order. -/
theorem demandTake_of_saturated (t : Unfold Ans) {k : Nat}
    (hk : (preOrder t).length <= k) : demandTake k t = preOrder t := by
  rw [demandTake_eq_take, List.take_of_length_le hk]

/-! ### Economy: a met demand does not consult the children

Stated as non-dependence rather than by counting a visit: once the answers at a
node meet the demand, the result is the same for *any* children whatsoever, so
an implementation that never visits them is indistinguishable by observation. -/

/-- When the answers present already meet the demand, the result is just those
answers. -/
theorem demandTake_of_met {k : Nat} {here : List Ans}
    (hk : k <= here.length) (cs : List (Unfold Ans)) :
    demandTake k (.node here cs) = here.take k := by
  rw [demandTake_eq_take]
  simp only [preOrder, List.take_append]
  have hz : k - here.length = 0 := by omega
  simp [hz]

/-- **Economy.**  If the answers present at an activation already meet the
demand, the result does not depend on that activation's sub-activations at all.
No observation can distinguish an implementation that skips them. -/
theorem demandTake_ignores_children {k : Nat} {here : List Ans}
    (hk : k <= here.length) (cs cs' : List (Unfold Ans)) :
    demandTake k (.node here cs) = demandTake k (.node here cs') := by
  rw [demandTake_of_met hk cs, demandTake_of_met hk cs']

end Mettapedia.GSLT.Dynamics.UnfoldingTraversal
