import Mettapedia.Logic.BDD.StateTransducer
import Mettapedia.Logic.BDD.Projection

/-!
# Forward symbolic images and output-safety preconditions

The transition graph uses target bits followed by source bits. Existential
projection eliminates the entire source block with one shared witness, not
independent witnesses for different output coordinates. Forward image and
universal predecessor form the expected adjunction on domain-qualified sets.

Universal predecessor is output safety, not existence or termination: a state
with no successor satisfies it vacuously. A total-result profile must separately
require a successor. These operations forget multiplicity by design.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.BDDCore.RelationalImage

open StatePredicates StateTransducer
open Mettapedia.Machines.GuardEvaluationRegimes (scalar)

def sourceBlock {n : Nat} (diagram : Diagram n) : Diagram (n + n) :=
  substitute (fun i => bit (Fin.natAdd n i)) diagram.val

theorem sourceBlock_eval {n : Nat} (diagram : Diagram n) (after before : State n) :
    (sourceBlock diagram).val.eval (Fin.addCases after before) = diagram.val.eval before := by
  simp only [sourceBlock, substitute_eval, bit, bddVar_eval, Fin.addCases_right]

def allBits {n : Nat} (predicates : List (Diagram n)) : Diagram n := predicates.foldr conj (truth n)

theorem allBits_eval {n : Nat} (predicates : List (Diagram n)) (state : State n) :
    (allBits predicates).val.eval state = true ↔ ∀ p ∈ predicates, p.val.eval state = true := by
  induction predicates <;> simp_all [allBits, conj, truth]

def coordinate {n : Nat} (rule : Rule n) (i : Fin n) : Diagram (n + n) :=
  ⟨apply (· == ·) (bit (Fin.castAdd n i)).val (sourceBlock (compileGuard (rule.assign i))).val,
    apply_ordered _ _ _ none (bit (Fin.castAdd n i)).property (sourceBlock (compileGuard (rule.assign i))).property⟩

def graph {n : Nat} (rule : Rule n) : Diagram (n + n) :=
  conj (sourceBlock (compileGuard rule.guard)) (allBits ((List.finRange n).map (coordinate rule)))

theorem graph_eval {n : Nat} (rule : Rule n) (after before : State n) :
    (graph rule).val.eval (Fin.addCases after before) = true ↔ rule.Fires before after := by
  simp only [graph, conj, apply_eval, Bool.and_eq_true_iff, sourceBlock_eval, compileGuard_eval, allBits_eval]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  simp [coordinate, apply_eval, bit, sourceBlock_eval, compileGuard_eval, Rule.Fires, Rule.nextState, funext_iff]

def graphs {n : Nat} (rules : List (Rule n)) : Diagram (n + n) :=
  rules.foldr (fun rule rest => disj (graph rule) rest) (falsity (n + n))

theorem graphs_eval {n : Nat} (rules : List (Rule n)) (after before : State n) :
    (graphs rules).val.eval (Fin.addCases after before) = true ↔ Transition rules before after := by
  induction rules with
  | nil => simp [graphs, falsity, Transition]
  | cons rule rest ih =>
    simp only [graphs, List.foldr_cons, disj, apply_eval, Bool.or_eq_true]
    change ((graph rule).val.eval (Fin.addCases after before) = true ∨
      (graphs rest).val.eval (Fin.addCases after before) = true) ↔ _
    rw [graph_eval, ih]
    simp [Transition]

def pushForward {n : Nat} (domain : Diagram n) (rules : List (Rule n)) (source : Diagram n) : Diagram n :=
  let joined := conj (graphs rules) (sourceBlock (within domain source))
  within domain ⟨Projection.projectAux joined.val, Projection.projectAux_ordered joined.val none joined.property⟩

theorem pushForward_eval {n : Nat} (domain : Diagram n) (rules : List (Rule n)) (source : Diagram n) (after : State n) :
    (pushForward domain rules source).val.eval after = true ↔
      ∃ before, Relation domain rules before after ∧ source.val.eval before = true := by
  let joined := conj (graphs rules) (sourceBlock (within domain source))
  change (apply (· && ·) domain.val (Projection.projectAux joined.val)).eval after = true ↔ _
  rw [apply_eval, Bool.and_eq_true_iff, Projection.projectAux_eval joined.val joined.property]
  have joinedEval (before : State n) : joined.val.eval (Fin.addCases after before) = true ↔
      Transition rules before after ∧ domain.val.eval before = true ∧ source.val.eval before = true := by
    change (conj (graphs rules) (sourceBlock (within domain source))).val.eval _ = true ↔ _
    rw [show (conj (graphs rules) (sourceBlock (within domain source))).val =
      apply (· && ·) (graphs rules).val (sourceBlock (within domain source)).val from rfl,
      apply_eval, Bool.and_eq_true_iff, graphs_eval, sourceBlock_eval]
    simp [within, conj]
  simp only [joinedEval, Relation]
  aesop

def mustPre {n : Nat} (domain : Diagram n) (rules : List (Rule n)) (target : Diagram n) : Diagram n :=
  complement domain (StateTransducer.pre domain rules (complement domain target))

theorem mustPre_eval {n : Nat} (domain : Diagram n) (rules : List (Rule n)) (target : Diagram n) (before : State n) :
    (mustPre domain rules target).val.eval before = true ↔
      domain.val.eval before = true ∧ ∀ after, Relation domain rules before after → target.val.eval after = true := by
  change (apply (· && ·) domain.val
    (bddNot (StateTransducer.pre domain rules (complement domain target)).val)).eval before = true ↔ _
  rw [apply_eval, bddNot_eval, Bool.and_eq_true_iff]
  constructor
  · rintro ⟨valid, noBad⟩
    refine ⟨valid, ?_⟩
    intro after edge
    cases value : target.val.eval after with
    | true => rfl
    | false =>
      have bad : (complement domain target).val.eval after = true := by
        simp [complement, conj, neg, edge.2.2, value]
      have predecessor := (pre_eval domain rules (complement domain target) before).mpr ⟨after, edge, bad⟩
      simp [predecessor] at noBad
  · rintro ⟨valid, safe⟩
    refine ⟨valid, ?_⟩
    cases bad : (StateTransducer.pre domain rules (complement domain target)).val.eval before with
    | false => rfl
    | true =>
      obtain ⟨after, edge, violates⟩ := (pre_eval domain rules (complement domain target) before).mp bad
      simp [complement, conj, neg, safe after edge] at violates

/-- This is the output-safety adjunction. Its right side is the largest
domain-qualified input set all of whose successors satisfy the postcondition. -/
theorem image_must_adjunction {n : Nat} (domain : Diagram n) (rules : List (Rule n)) (source target : Diagram n) :
    denote (pushForward domain rules source) ⊆ denote target ↔
      denote (within domain source) ⊆ denote (mustPre domain rules target) := by
  constructor
  · intro safe before admitted
    have data : domain.val.eval before = true ∧ source.val.eval before = true := by
      simpa [denote, BDD.satSet, within, conj] using admitted
    apply (mustPre_eval domain rules target before).mpr
    refine ⟨data.1, ?_⟩
    intro after edge
    exact safe ((pushForward_eval domain rules source after).mpr ⟨before, edge, data.2⟩)
  · intro admitted after produced
    obtain ⟨before, edge, member⟩ := (pushForward_eval domain rules source after).mp produced
    have valid : before ∈ denote (within domain source) := by
      simp [denote, BDD.satSet, within, conj, edge.1, member]
    exact ((mustPre_eval domain rules target before).mp (admitted valid)).2 after edge

namespace Controls

def copyBoth : Rule 2 := ⟨.constant true, fun _ => .atom 0⟩

theorem copied_outputs_share_one_source (after : State 2)
    (reachable : (pushForward (truth 2) [copyBoth] (truth 2)).val.eval after = true) : after 0 = after 1 := by
  obtain ⟨before, edge, _⟩ := (pushForward_eval _ _ _ after).mp reachable
  obtain ⟨rule, member, enabled, equal⟩ := edge.2.1
  have same : rule = copyBoth := by simpa using member
  subst rule
  rw [equal]
  rfl

theorem incompatible_outputs_are_excluded :
    (pushForward (truth 2) [copyBoth] (truth 2)).val.eval ![true, false] = false := by
  apply Bool.eq_false_iff.mpr
  intro reachable
  have incompatible := copied_outputs_share_one_source ![true, false] reachable
  cases incompatible

theorem safety_does_not_imply_a_successor (state : State 1) :
    (mustPre (truth 1) [] (falsity 1)).val.eval state = true ∧
    (StateTransducer.pre (truth 1) [] (truth 1)).val.eval state = false := by
  simp [mustPre, complement, StateTransducer.pre, rawPre, truth, falsity, conj, neg]

end Controls
end Mettapedia.Logic.BDDCore.RelationalImage
