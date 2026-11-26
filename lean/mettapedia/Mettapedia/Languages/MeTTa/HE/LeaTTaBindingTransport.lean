import Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
import Mettapedia.Languages.MeTTa.HE.DeclMergeSpec
import Mettapedia.Languages.MeTTa.HE.EqualityClosure
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Mettapedia.Languages.MeTTa.HE.BindingComposition

/-!
# Representation-independent HE/LeaTTa binding transport

This layer transports the faithful HE matcher and merge relations to LeaTTa's
binding interface through `LeaBindingRelEquiv`. Concrete binding-list order is not
part of the contract: the official binding set is order-free, while the two
implementations use opposite insertion conventions.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaBridge

open Mettapedia.Languages.MeTTa.HE.DeclMatchSpec
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge
  (AtomOccurs ClassDepends SemanticLoopFree hasLoop_eq_false_iff_semanticLoopFree)
open Mettapedia.Languages.MeTTa.HE.CanonAbsorbsFreshening
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge

@[simp] theorem renBy_id (a : Metta.Atom) : renBy id a = a := by
  induction a with
  | expr xs ih =>
      simp only [renBy]
      rw [List.map_congr_left ih]
      simp
  | _ => simp [renBy]

@[simp] theorem renBy_refl (a : Metta.Atom) :
    renBy (Equiv.refl String) a = a := by
  induction a with
  | expr xs ih =>
      simp only [renBy]
      rw [List.map_congr_left ih]
      simp
  | _ => simp

/-- A LeaTTa matcher witness for one HE matcher result, modulo the independent
relation-set equivalence. Matcher orientation is reversed because LeaTTa's
`queryOp` matches the rule pattern against the query atom. -/
def LeaMatcherTransport (query pattern : Atom) (hb : Bindings) : Prop :=
  ∃ lb,
    lb ∈ Metta.matchAtoms (encodeModelAtom pattern) (encodeModelAtom query) ∧
      LeaBindingRelEquiv hb lb

/-- Equality edges carried by a LeaTTa binding list, retaining stored order and
orientation while erasing direct value relations. -/
def leaEqualityEdges : Metta.Bindings → List (String × String)
  | [] => []
  | .val _ _ :: rest => leaEqualityEdges rest
  | .eq x y :: rest => (x, y) :: leaEqualityEdges rest

@[simp] theorem mem_leaEqualityEdges_iff {lb : Metta.Bindings} {x y : String} :
    (x, y) ∈ leaEqualityEdges lb ↔ Metta.BindingRel.eq x y ∈ lb := by
  induction lb with
  | nil => simp [leaEqualityEdges]
  | cons rel rest ih =>
      cases rel <;> simp [leaEqualityEdges, ih]

/-- Raw alias insertion retains every previously stored equality edge. -/
theorem leaEqualityEdges_addEqRaw_old
    (bindings : Metta.Bindings) (left right : String)
    {edge : String × String} (present : edge ∈ leaEqualityEdges bindings) :
    edge ∈ leaEqualityEdges (Metta.Bindings.addEqRaw bindings left right) := by
  rcases edge with ⟨x, y⟩
  rw [mem_leaEqualityEdges_iff] at present ⊢
  exact Metta.Bindings.mem_addEqRaw_of_mem bindings left right present

/-- Every non-reflexive alias is present after raw insertion, including replay. -/
theorem leaEqualityEdges_addEqRaw_new
    (bindings : Metta.Bindings) {left right : String} (different : left ≠ right) :
    (left, right) ∈
      leaEqualityEdges (Metta.Bindings.addEqRaw bindings left right) := by
  rw [mem_leaEqualityEdges_iff]
  exact Metta.Bindings.eq_mem_addEqRaw bindings left right different

/-- Equality-edge membership after a non-reflexive insertion is exactly old
membership plus the requested edge. -/
theorem mem_leaEqualityEdges_addEqRaw_iff
    (bindings : Metta.Bindings) {left right x y : String}
    (different : left ≠ right) :
    (x, y) ∈ leaEqualityEdges (Metta.Bindings.addEqRaw bindings left right) ↔
      (x = left ∧ y = right) ∨ (x, y) ∈ leaEqualityEdges bindings := by
  simpa [mem_leaEqualityEdges_iff] using
    (Metta.Bindings.mem_addEqRaw_iff bindings left right different
      (Metta.BindingRel.eq x y))

/-- A fresh non-reflexive alias is prepended to the ordered equality projection. -/
theorem leaEqualityEdges_addEqRaw_of_not_mem
    (bindings : Metta.Bindings) {left right : String}
    (different : left ≠ right)
    (absent : Metta.BindingRel.eq left right ∉ bindings) :
    leaEqualityEdges (Metta.Bindings.addEqRaw bindings left right) =
      (left, right) :: leaEqualityEdges bindings := by
  rw [Metta.Bindings.addEqRaw_of_not_mem bindings left right different absent]
  rfl

/-- LeaTTa's saturation pass is HE's pass on the explicit equality projection.
Value relations have no effect on either equality closure. -/
theorem leaEqStep_eq_heEqStep (lb : Metta.Bindings) (acc : List String) :
    Metta.Bindings.eqStep lb acc =
      Bindings.eqStep (leaEqualityEdges lb) acc := by
  induction lb generalizing acc with
  | nil => rfl
  | cons rel rest ih =>
      cases rel with
      | val x value =>
          simpa [Metta.Bindings.eqStep, Bindings.eqStep, leaEqualityEdges] using
            ih (acc := acc)
      | eq x y =>
          let acc' :=
            let acc := if acc.contains x && !acc.contains y then
              acc ++ [y] else acc
            if acc.contains y && !acc.contains x then acc ++ [x] else acc
          simpa [Metta.Bindings.eqStep, Bindings.eqStep, leaEqualityEdges,
            acc'] using ih (acc := acc')

theorem leaEqClassAux_eq_heEqClassAux (lb : Metta.Bindings)
    (fuel : Nat) (acc : List String) :
    Metta.Bindings.eqClassAux lb fuel acc =
      Bindings.eqClassAux (leaEqualityEdges lb) fuel acc := by
  induction fuel generalizing acc with
  | zero => rfl
  | succ fuel ih =>
      simp only [Metta.Bindings.eqClassAux, Bindings.eqClassAux]
      rw [leaEqStep_eq_heEqStep]
      exact ih _

theorem leaEqualityEdges_length_le (lb : Metta.Bindings) :
    (leaEqualityEdges lb).length ≤ lb.length := by
  induction lb with
  | nil => simp [leaEqualityEdges]
  | cons rel rest ih =>
      cases rel with
      | val _ _ =>
          simp only [leaEqualityEdges, List.length_cons]
          exact Nat.le_trans ih (Nat.le_succ _)
      | eq _ _ => simp [leaEqualityEdges, ih]

/-- LeaTTa's fuelled class computation has the same order-independent graph
meaning as HE's, even though LeaTTa counts value relations in its fuel bound. -/
theorem mem_leaEqClass_iff_reachable {lb : Metta.Bindings}
    {start finish : String} :
    finish ∈ Metta.Bindings.eqClass lb start ↔
      (EqualityClosure.edgeGraph (leaEqualityEdges lb)).Reachable start finish := by
  constructor
  · intro h
    unfold Metta.Bindings.eqClass at h
    rw [leaEqClassAux_eq_heEqClassAux] at h
    apply EqualityClosure.reachable_of_mem_eqClassAux (acc := [start])
      (by
        intro u hu
        simp only [List.mem_singleton] at hu
        subst u
        exact .rfl)
    exact h
  · intro h
    obtain ⟨path, hlength⟩ :=
      EqualityClosure.reachable_has_bounded_path h
    unfold Metta.Bindings.eqClass
    rw [leaEqClassAux_eq_heEqClassAux]
    apply EqualityClosure.walk_end_mem_eqClassAux_of_length_le path.val
      (Nat.le_trans hlength
        (Nat.le_trans
          (Nat.mul_le_mul_left 2 (leaEqualityEdges_length_le lb))
          (Nat.le_add_right _ 1)))
    simp

/-- Order-free equality-relation equivalence identifies the undirected graphs
presented by HE and LeaTTa. -/
theorem edgeGraph_eq_of_leaEqualityRelEquiv {b : Bindings}
    {lb : Metta.Bindings} (hequiv : LeaEqualityRelEquiv b lb) :
    EqualityClosure.edgeGraph b.equalities =
      EqualityClosure.edgeGraph (leaEqualityEdges lb) := by
  ext x y
  simp only [EqualityClosure.edgeGraph_adj_iff, mem_leaEqualityEdges_iff]
  exact and_congr Iff.rfl (hequiv x y).symm

/-- Representation-independent equality-edge agreement transfers every
equality class extensionally. -/
theorem eqClass_mem_iff_of_leaBindingRelEquiv
    {b : Bindings} {lb : Metta.Bindings}
    (hequiv : LeaBindingRelEquiv b lb) {start finish : String} :
    finish ∈ b.eqClass start ↔
      finish ∈ Metta.Bindings.eqClass lb start := by
  rw [EqualityClosure.mem_eqClass_iff_reachable,
    mem_leaEqClass_iff_reachable,
    edgeGraph_eq_of_leaEqualityRelEquiv hequiv.equalities]

/-! ### Binding equation-system semantics

Merge and unification may return sparse or redundant presentations of one
solution.  The compositional invariant is therefore not equality of returned
relations or MGUs, but equality of the valuations satisfying their equations.
The resolver-facing global-permutation invariant below is the observable layer
that will be derived from this theory for successful acyclic matcher outputs.
-/

/-- A valuation satisfies the equations presented by one repaired-LeaTTa
binding list.  Relation order and equality orientation are immaterial. -/
def LeaBindingSatisfied
    (valuation : String → Metta.Atom) (lb : Metta.Bindings) : Prop :=
  (∀ x value, Metta.BindingRel.val x value ∈ lb →
      valuation x = applyClassSolution valuation value) ∧
  (∀ x y, Metta.BindingRel.eq x y ∈ lb → valuation x = valuation y)

/-- A valuation satisfies only the equality graph presented by an HE binding
record.  Values are intentionally omitted: equality-class closure is the
meaning of this graph, independently of other equations that may happen to
entail additional equalities. -/
def HEEqualitySatisfied
    (valuation : String → Metta.Atom) (b : Bindings) : Prop :=
  ∀ x y, (x, y) ∈ b.equalities → valuation x = valuation y

/-- A valuation satisfies only the equality graph presented by a repaired
LeaTTa binding list. -/
def LeaEqualitySatisfied
    (valuation : String → Metta.Atom) (lb : Metta.Bindings) : Prop :=
  ∀ x y, Metta.BindingRel.eq x y ∈ lb → valuation x = valuation y

/-- Equality of the theories presented by the two explicit equality graphs.
This quotient-level invariant ignores edge orientation, multiplicity, list
order, and representative chronology. -/
def LeaEqualityTheoryEquiv (b : Bindings) (lb : Metta.Bindings) : Prop :=
  ∀ valuation,
    HEEqualitySatisfied valuation b ↔ LeaEqualitySatisfied valuation lb

/-- Equality of the complete binding solution theories. -/
def LeaBindingSolutionTheoryEquiv
    (b : Bindings) (lb : Metta.Bindings) : Prop :=
  ∀ valuation,
    HEBindingSatisfied valuation b ↔
      LeaBindingSatisfied valuation lb

private noncomputable def equalityComponentIndicator
    (edges : List (String × String)) (start v : String) : Metta.Atom := by
  classical
  exact if (EqualityClosure.edgeGraph edges).Reachable start v then
    .sym "reachable" else .sym "separate"

private theorem equalityComponentIndicator_satisfies
    (edges : List (String × String)) (start : String) :
    ∀ x y, (x, y) ∈ edges →
      equalityComponentIndicator edges start x =
        equalityComponentIndicator edges start y := by
  classical
  intro x y hedge
  by_cases hxy : x = y
  · subst y
    rfl
  · have hstep :
        (EqualityClosure.edgeGraph edges).Reachable x y :=
      (show (EqualityClosure.edgeGraph edges).Adj x y from
        ⟨hxy, Or.inl hedge⟩).reachable
    have hreach :
        (EqualityClosure.edgeGraph edges).Reachable start x ↔
          (EqualityClosure.edgeGraph edges).Reachable start y :=
      ⟨fun hx => hx.trans hstep, fun hy => hy.trans hstep.symm⟩
    by_cases hx :
        (EqualityClosure.edgeGraph edges).Reachable start x
    · have hy := hreach.mp hx
      simp [equalityComponentIndicator, hx, hy]
    · have hy :
          ¬ (EqualityClosure.edgeGraph edges).Reachable start y :=
        fun hy => hx (hreach.mpr hy)
      simp [equalityComponentIndicator, hx, hy]

private theorem equalitySatisfied_eq_of_reachable
    {edges : List (String × String)} {valuation : String → Metta.Atom}
    {left right : String}
    (hsatisfied : ∀ x y, (x, y) ∈ edges → valuation x = valuation y)
    (hreach : (EqualityClosure.edgeGraph edges).Reachable left right) :
    valuation left = valuation right := by
  apply hreach.elim
  intro walk
  induction walk with
  | nil => rfl
  | @cons start next finish hadj tail ih =>
      have hstep : valuation start = valuation next := by
        rcases (EqualityClosure.edgeGraph_adj_iff.mp hadj).2 with
          hedge | hedge
        · exact hsatisfied start next hedge
        · exact (hsatisfied next start hedge).symm
      exact hstep.trans (ih tail.reachable)

/-- Equality-graph theory determines equality-class closure exactly.  This is
the extensional bridge from a semantic invariant to the operational `eqClass`
observables used by both resolvers. -/
theorem eqClass_mem_iff_of_equalityTheoryEquiv
    {b : Bindings} {lb : Metta.Bindings}
    (htheory : LeaEqualityTheoryEquiv b lb) {start finish : String} :
    finish ∈ b.eqClass start ↔
      finish ∈ Metta.Bindings.eqClass lb start := by
  classical
  rw [EqualityClosure.mem_eqClass_iff_reachable,
    mem_leaEqClass_iff_reachable]
  constructor
  · intro hhe
    let valuation :=
      equalityComponentIndicator (leaEqualityEdges lb) start
    have hleaSatisfied : LeaEqualitySatisfied valuation lb := by
      intro x y hmem
      exact equalityComponentIndicator_satisfies
        (leaEqualityEdges lb) start x y
          (mem_leaEqualityEdges_iff.mpr hmem)
    have hheSatisfied : HEEqualitySatisfied valuation b :=
      (htheory valuation).mpr hleaSatisfied
    by_contra hnot
    have heq : valuation start = valuation finish :=
      equalitySatisfied_eq_of_reachable hheSatisfied hhe
    simp [valuation, equalityComponentIndicator, hnot] at heq
  · intro hlea
    let valuation := equalityComponentIndicator b.equalities start
    have hheSatisfied : HEEqualitySatisfied valuation b := by
      exact equalityComponentIndicator_satisfies b.equalities start
    have hleaSatisfied : LeaEqualitySatisfied valuation lb :=
      (htheory valuation).mp hheSatisfied
    have hleaEdgesSatisfied :
        ∀ x y, (x, y) ∈ leaEqualityEdges lb →
          valuation x = valuation y := by
      intro x y hmem
      exact hleaSatisfied x y (mem_leaEqualityEdges_iff.mp hmem)
    by_contra hnot
    have heq : valuation start = valuation finish :=
      equalitySatisfied_eq_of_reachable hleaEdgesSatisfied hlea
    simp [valuation, equalityComponentIndicator, hnot] at heq

/- Recursive float-freedom for the opaque carrier used by `collapse-bind`.
The carrier is semantically opaque, but its structural Boolean equality still
visits every stored value, so a nested host float must remain outside the
lawful-equality fragment. -/
mutual
  /-- A stored grounded payload contains no host float. -/
  def StoredGroundNoFloat : Metta.StoredGround → Prop
    | .float _ => False
    | .bindings relations => StoredBindingsNoFloat relations
    | _ => True

  /-- A stored atom contains no host float. -/
  def StoredAtomNoFloat : Metta.StoredAtom → Prop
    | .gnd value => StoredGroundNoFloat value
    | .expr atoms => StoredAtomsNoFloat atoms
    | _ => True

  /-- A stored binding relation contains no host float. -/
  def StoredBindingNoFloat : Metta.StoredBinding → Prop
    | .val _ value => StoredAtomNoFloat value
    | .eq _ _ => True

  /-- Every relation in an opaque binding payload is float-free. -/
  def StoredBindingsNoFloat : List Metta.StoredBinding → Prop
    | [] => True
    | relation :: relations =>
        StoredBindingNoFloat relation ∧ StoredBindingsNoFloat relations

  /-- Every member of a stored expression is float-free. -/
  def StoredAtomsNoFloat : List Metta.StoredAtom → Prop
    | [] => True
    | atom :: atoms => StoredAtomNoFloat atom ∧ StoredAtomsNoFloat atoms
end

/-- Host-float-free atoms form the lawful structural-equality domain needed by
the matcher and unifier.  Opaque binding payloads remain in the domain exactly
when their recursively stored atoms are float-free; rejecting every payload
would incorrectly exclude reachable `collapse-bind` evaluator results. -/
def MettaAtomNoFloat : Metta.Atom → Prop
  | .gnd (.float _) => False
  | .gnd (.bindings relations) =>
      StoredBindingsNoFloat relations
  | .expr atoms => ∀ atom ∈ atoms, MettaAtomNoFloat atom
  | _ => True

mutual

/-- Boolean equality is sound on recursively float-free stored grounds. -/
theorem storedGround_eq_of_beq_true_noFloat
    {left right : Metta.StoredGround} :
    StoredGroundNoFloat left → StoredGroundNoFloat right →
      (left == right) = true → left = right := by
  intro leftSafe rightSafe equal
  cases left <;> cases right <;>
    simp_all [StoredGroundNoFloat, BEq.beq, Metta.StoredGround.beq]
  exact storedBindings_eq_of_beq_true_noFloat leftSafe rightSafe equal

/-- Boolean equality is sound on recursively float-free stored atoms. -/
theorem storedAtom_eq_of_beq_true_noFloat
    {left right : Metta.StoredAtom} :
    StoredAtomNoFloat left → StoredAtomNoFloat right →
      (left == right) = true → left = right := by
  intro leftSafe rightSafe equal
  cases left with
  | sym name =>
      cases right <;>
        simp_all [BEq.beq, Metta.StoredAtom.beq]
  | var name =>
      cases right <;>
        simp_all [BEq.beq, Metta.StoredAtom.beq]
  | gnd ground =>
      cases right with
      | sym | var | expr =>
          simp_all [BEq.beq, Metta.StoredAtom.beq]
      | gnd other =>
          apply congrArg Metta.StoredAtom.gnd
          apply storedGround_eq_of_beq_true_noFloat leftSafe rightSafe
          simpa [BEq.beq, Metta.StoredAtom.beq] using equal
  | expr atoms =>
      cases right with
      | sym | var | gnd =>
          simp_all [BEq.beq, Metta.StoredAtom.beq]
      | expr others =>
          apply congrArg Metta.StoredAtom.expr
          apply storedAtoms_eq_of_beq_true_noFloat leftSafe rightSafe
          simpa [BEq.beq, Metta.StoredAtom.beq] using equal

/-- Boolean equality is sound on recursively float-free stored relations. -/
theorem storedBinding_eq_of_beq_true_noFloat
    {left right : Metta.StoredBinding} :
    StoredBindingNoFloat left → StoredBindingNoFloat right →
      (left == right) = true → left = right := by
  intro leftSafe rightSafe equal
  cases left with
  | val name value =>
      cases right with
      | eq => simp_all [BEq.beq, Metta.StoredBinding.beq]
      | val otherName otherValue =>
          have parts : (name == otherName) = true ∧
              (value == otherValue) = true := by
            simpa [BEq.beq, Metta.StoredBinding.beq,
              Bool.and_eq_true] using equal
          have nameEquation : name = otherName := beq_iff_eq.mp parts.1
          have valueEquation : value = otherValue :=
            storedAtom_eq_of_beq_true_noFloat leftSafe rightSafe parts.2
          simp [nameEquation, valueEquation]
  | eq leftName rightName =>
      cases right with
      | val => simp_all [BEq.beq, Metta.StoredBinding.beq]
      | eq otherLeft otherRight =>
          have parts : (leftName == otherLeft) = true ∧
              (rightName == otherRight) = true := by
            simpa [BEq.beq, Metta.StoredBinding.beq,
              Bool.and_eq_true] using equal
          simp [beq_iff_eq.mp parts.1, beq_iff_eq.mp parts.2]

/-- List Boolean equality is sound on recursively float-free stored
relations. -/
theorem storedBindings_eq_of_beq_true_noFloat :
    ∀ {left right : List Metta.StoredBinding},
      StoredBindingsNoFloat left → StoredBindingsNoFloat right →
        Metta.StoredBinding.beqList left right = true → left = right
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, equal => by
      simp [Metta.StoredBinding.beqList] at equal
  | _ :: _, [], _, _, equal => by
      simp [Metta.StoredBinding.beqList] at equal
  | left :: lefts, right :: rights, leftSafe, rightSafe, equal => by
      have parts : Metta.StoredBinding.beq left right = true ∧
          Metta.StoredBinding.beqList lefts rights = true := by
        simpa [Metta.StoredBinding.beqList, Bool.and_eq_true] using equal
      have headEquation : left = right :=
        storedBinding_eq_of_beq_true_noFloat leftSafe.1 rightSafe.1
          (by simpa [BEq.beq] using parts.1)
      have tailEquation : lefts = rights :=
        storedBindings_eq_of_beq_true_noFloat leftSafe.2 rightSafe.2 parts.2
      simp [headEquation, tailEquation]

/-- List Boolean equality is sound on recursively float-free stored atoms. -/
theorem storedAtoms_eq_of_beq_true_noFloat :
    ∀ {left right : List Metta.StoredAtom},
      StoredAtomsNoFloat left → StoredAtomsNoFloat right →
        Metta.StoredAtom.beqList left right = true → left = right
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, equal => by
      simp [Metta.StoredAtom.beqList] at equal
  | _ :: _, [], _, _, equal => by
      simp [Metta.StoredAtom.beqList] at equal
  | left :: lefts, right :: rights, leftSafe, rightSafe, equal => by
      have parts : Metta.StoredAtom.beq left right = true ∧
          Metta.StoredAtom.beqList lefts rights = true := by
        simpa [Metta.StoredAtom.beqList, Bool.and_eq_true] using equal
      have headEquation : left = right :=
        storedAtom_eq_of_beq_true_noFloat leftSafe.1 rightSafe.1
          (by simpa [BEq.beq] using parts.1)
      have tailEquation : lefts = rights :=
        storedAtoms_eq_of_beq_true_noFloat leftSafe.2 rightSafe.2 parts.2
      simp [headEquation, tailEquation]

end

mutual

/-- Boolean equality is reflexive on recursively float-free stored
grounds. -/
theorem storedGround_beq_self_noFloat :
    ∀ ground : Metta.StoredGround,
      StoredGroundNoFloat ground →
        Metta.StoredGround.beq ground ground = true
  | .float _, safe => by simp [StoredGroundNoFloat] at safe
  | .bindings relations, safe => by
      simpa [Metta.StoredGround.beq] using
        storedBindings_beq_self_noFloat relations safe
  | .int _, _ => by simp [Metta.StoredGround.beq]
  | .str _, _ => by simp [Metta.StoredGround.beq]
  | .bool _, _ => by simp [Metta.StoredGround.beq]
  | .unit, _ => by simp [Metta.StoredGround.beq]
  | .error _, _ => by simp [Metta.StoredGround.beq]
  | .external _ _, _ => by simp [Metta.StoredGround.beq]

/-- Boolean equality is reflexive on recursively float-free stored atoms. -/
theorem storedAtom_beq_self_noFloat :
    ∀ atom : Metta.StoredAtom,
      StoredAtomNoFloat atom → Metta.StoredAtom.beq atom atom = true
  | .sym _, _ => by simp [Metta.StoredAtom.beq]
  | .var _, _ => by simp [Metta.StoredAtom.beq]
  | .gnd ground, safe => by
      simpa [Metta.StoredAtom.beq] using
        storedGround_beq_self_noFloat ground safe
  | .expr atoms, safe => by
      simpa [Metta.StoredAtom.beq] using
        storedAtoms_beq_self_noFloat atoms safe

/-- Boolean equality is reflexive on recursively float-free stored binding
relations. -/
theorem storedBinding_beq_self_noFloat :
    ∀ relation : Metta.StoredBinding,
      StoredBindingNoFloat relation →
        Metta.StoredBinding.beq relation relation = true
  | .val _ value, safe => by
      simp [Metta.StoredBinding.beq,
        storedAtom_beq_self_noFloat value safe]
  | .eq _ _, _ => by simp [Metta.StoredBinding.beq]

/-- Boolean equality is reflexive on float-free stored binding lists. -/
theorem storedBindings_beq_self_noFloat :
    ∀ relations : List Metta.StoredBinding,
      StoredBindingsNoFloat relations →
        Metta.StoredBinding.beqList relations relations = true
  | [], _ => by simp [Metta.StoredBinding.beqList]
  | relation :: relations, safe => by
      simp [Metta.StoredBinding.beqList,
        storedBinding_beq_self_noFloat relation safe.1,
        storedBindings_beq_self_noFloat relations safe.2]

/-- Boolean equality is reflexive on float-free stored atom lists. -/
theorem storedAtoms_beq_self_noFloat :
    ∀ atoms : List Metta.StoredAtom,
      StoredAtomsNoFloat atoms →
        Metta.StoredAtom.beqList atoms atoms = true
  | [], _ => by simp [Metta.StoredAtom.beqList]
  | atom :: atoms, safe => by
      simp [Metta.StoredAtom.beqList,
        storedAtom_beq_self_noFloat atom safe.1,
        storedAtoms_beq_self_noFloat atoms safe.2]

end

/-- Every target stored in a unifier substitution remains in the
HE-translatable host-float-free fragment. -/
def MettaSubstNoFloat (subst : Metta.Subst) : Prop :=
  ∀ x term, (x, term) ∈ subst → MettaAtomNoFloat term

/-- A Robinson substitution never presents a reflexive variable alias as an
entry.  Trivial `$x = $x` equations are removed by decomposition, while every
eliminated variable constraint has passed the occurs check. -/
def MettaSubstNoSelfVariable (subst : Metta.Subst) : Prop :=
  ∀ key, (key, Metta.Atom.var key) ∉ subst

@[simp] theorem mettaSubstNoSelfVariable_empty :
    MettaSubstNoSelfVariable Metta.Subst.empty := by
  simp [MettaSubstNoSelfVariable, Metta.Subst.empty]

/-- Structural Boolean equality is sound on the HE-translatable fragment.
Host floats are excluded because their Boolean equality need not be
reflexive; no stronger equality law is assumed for the host interface. -/
theorem mettaAtom_eq_of_beq_true_noFloat :
    ∀ {left right : Metta.Atom},
      MettaAtomNoFloat left → MettaAtomNoFloat right →
        (left == right) = true → left = right := by
  intro left
  induction left using Metta.Atom.recAux with
  | sym symbol =>
      intro right _ _ h
      cases right with
      | sym other =>
          change (symbol == other) = true at h
          exact congrArg Metta.Atom.sym (beq_iff_eq.mp h)
      | var | gnd | expr => contradiction
  | var name =>
      intro right _ _ h
      cases right with
      | var other =>
          change (name == other) = true at h
          exact congrArg Metta.Atom.var (beq_iff_eq.mp h)
      | sym | gnd | expr => contradiction
  | gnd ground =>
      intro right hleft hright h
      cases right with
      | gnd other =>
          change Metta.Ground.beq ground other = true at h
          cases ground <;> cases other <;>
            simp [MettaAtomNoFloat] at hleft hright <;>
            simp [BEq.beq, Metta.Ground.beq] at h <;>
            simp_all
          exact storedBindings_eq_of_beq_true_noFloat hleft hright h
      | sym | var | expr => contradiction
  | expr atoms ih =>
      intro right hleft hright h
      cases right with
      | expr others =>
          change Metta.Atom.beqList atoms others = true at h
          have hleftChildren : ∀ atom ∈ atoms,
              MettaAtomNoFloat atom := by
            simpa [MettaAtomNoFloat] using hleft
          have hrightChildren : ∀ atom ∈ others,
              MettaAtomNoFloat atom := by
            simpa [MettaAtomNoFloat] using hright
          have listSound : ∀ (lefts rights : List Metta.Atom),
              (∀ atom ∈ lefts, atom ∈ atoms) →
              (∀ atom ∈ lefts, MettaAtomNoFloat atom) →
              (∀ atom ∈ rights, MettaAtomNoFloat atom) →
              Metta.Atom.beqList lefts rights = true →
              lefts = rights := by
            intro lefts
            induction lefts with
            | nil =>
                intro rights _ _ _ hbeq
                cases rights with
                | nil => rfl
                | cons head tail =>
                    simp [Metta.Atom.beqList] at hbeq
            | cons head tail ihTail =>
                intro rights hsubset hlefts hrights hbeq
                cases rights with
                | nil =>
                    simp [Metta.Atom.beqList] at hbeq
                | cons other rest =>
                    change ((head == other) &&
                      Metta.Atom.beqList tail rest) = true at hbeq
                    rw [Bool.and_eq_true] at hbeq
                    have hhead : head = other :=
                      ih head (hsubset head (by simp))
                        (hlefts head (by simp))
                        (hrights other (by simp)) hbeq.1
                    have htail : tail = rest :=
                      ihTail rest
                        (fun atom hmem => hsubset atom
                          (List.mem_cons_of_mem head hmem))
                        (fun atom hmem => hlefts atom
                          (List.mem_cons_of_mem head hmem))
                        (fun atom hmem => hrights atom
                          (List.mem_cons_of_mem other hmem))
                        hbeq.2
                    simp [hhead, htail]
          have hlists : atoms = others :=
            listSound atoms others (by simp) hleftChildren hrightChildren h
          exact congrArg Metta.Atom.expr hlists
      | sym | var | gnd => contradiction

/-- Structural Boolean equality is reflexive on the host-float-free atom
fragment.  This is the converse companion to
`mettaAtom_eq_of_beq_true_noFloat`; together they provide the lawful equality
interface used by semantic projection proofs without asserting `LawfulBEq` for
the larger runtime atom type. -/
theorem mettaAtom_beq_self_noFloat :
    ∀ atom : Metta.Atom, MettaAtomNoFloat atom → (atom == atom) = true := by
  intro atom
  induction atom using Metta.Atom.recAux with
  | sym symbol =>
      intro _
      change (symbol == symbol) = true
      simp
  | var name =>
      intro _
      change (name == name) = true
      simp
  | gnd ground =>
      intro groundNoFloat
      change Metta.Ground.beq ground ground = true
      cases ground <;>
        simp_all [MettaAtomNoFloat, BEq.beq, Metta.Ground.beq]
      exact storedBindings_beq_self_noFloat _ groundNoFloat
  | expr atoms inductionHypothesis =>
      intro atomsNoFloat
      change Metta.Atom.beqList atoms atoms = true
      have childrenNoFloat : ∀ child ∈ atoms,
          MettaAtomNoFloat child := by
        simpa [MettaAtomNoFloat] using atomsNoFloat
      have listSelf : ∀ items : List Metta.Atom,
          (∀ child ∈ items, child ∈ atoms) →
          (∀ child ∈ items, MettaAtomNoFloat child) →
          Metta.Atom.beqList items items = true := by
        intro items
        induction items with
        | nil => simp [Metta.Atom.beqList]
        | cons head tail tailHypothesis =>
            intro itemsSubset itemsNoFloat
            simp only [Metta.Atom.beqList, Bool.and_eq_true]
            exact ⟨inductionHypothesis head
                (itemsSubset head (by simp))
                (itemsNoFloat head (by simp)),
              tailHypothesis
                (fun child member =>
                  itemsSubset child (by simp [member]))
                (fun child member =>
                  itemsNoFloat child (by simp [member]))⟩
      exact listSelf atoms (fun _ member => member) childrenNoFloat

theorem MettaSubstNoFloat.extend
    {subst : Metta.Subst} {x : String} {term : Metta.Atom}
    (hsubst : MettaSubstNoFloat subst)
    (hterm : MettaAtomNoFloat term) :
    MettaSubstNoFloat (Metta.Subst.extend subst x term) := by
  intro key value hmem
  simp only [Metta.Subst.extend, List.mem_cons] at hmem
  rcases hmem with hmem | hmem
  · have hvalue : value = term := congrArg Prod.snd hmem
    rw [hvalue]
    exact hterm
  · apply hsubst key value
    exact (List.mem_filter.mp hmem).1

mutual

theorem encodeModelAtom_noFloat (atom : Atom) :
    MettaAtomNoFloat (encodeModelAtom atom) := by
  cases atom with
  | symbol => simp [encodeModelAtom, MettaAtomNoFloat]
  | var => simp [encodeModelAtom, MettaAtomNoFloat]
  | grounded ground =>
      cases ground <;> simp [encodeModelAtom, encodeModelGround, MettaAtomNoFloat]
  | expression atoms =>
      simpa [encodeModelAtom, MettaAtomNoFloat] using
        encodeModelAtoms_noFloat atoms

theorem encodeModelAtoms_noFloat (atoms : List Atom) :
    ∀ atom ∈ encodeModelAtoms atoms, MettaAtomNoFloat atom := by
  cases atoms with
  | nil => simp [encodeModelAtoms]
  | cons head tail =>
      intro atom hmem
      simp only [encodeModelAtoms, List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · exact encodeModelAtom_noFloat head
      · exact encodeModelAtoms_noFloat tail atom htail

end

private theorem ground_eq_of_equiv_of_noFloat
    {left right : Metta.Ground}
    (hleft : MettaAtomNoFloat (.gnd left))
    (hright : MettaAtomNoFloat (.gnd right))
    (hequiv : Metta.Ground.equiv left right = true) :
    left = right := by
  cases left <;> cases right <;>
    simp [MettaAtomNoFloat] at hleft hright <;>
    simp [Metta.Ground.equiv, BEq.beq, Metta.Ground.beq] at hequiv <;>
    simp_all
  exact storedBindings_eq_of_beq_true_noFloat hleft hright hequiv

/-- Satisfaction of every equation in a worklist. -/
def MettaEquationsSatisfied
    (valuation : String → Metta.Atom)
    (equations : List (Metta.Atom × Metta.Atom)) : Prop :=
  ∀ equation ∈ equations, MettaEquationSatisfied valuation equation

/-- Satisfaction of every variable constraint emitted by structural
decomposition. -/
def MettaConstraintsSatisfied
    (valuation : String → Metta.Atom)
    (constraints : List (String × Metta.Atom)) : Prop :=
  ∀ constraint ∈ constraints,
    valuation constraint.1 =
      applyClassSolution valuation constraint.2

/-- Structural decomposition preserves exactly the valuation solutions of a
host-float-free atom equation. -/
theorem decomposeEq_solution_iff
    (valuation : String → Metta.Atom) :
    ∀ (left right : Metta.Atom)
      (constraints : List (String × Metta.Atom)),
      MettaAtomNoFloat left → MettaAtomNoFloat right →
      Metta.Unify.decomposeEq left right = some constraints →
      (MettaEquationSatisfied valuation (left, right) ↔
        MettaConstraintsSatisfied valuation constraints) := by
  intro left
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_ left
  · intro symbol right constraints _hleft _hright hdecomp
    cases right with
    | sym other =>
        simp [Metta.Unify.decomposeEq] at hdecomp
        rcases hdecomp with ⟨rfl, rfl⟩
        simp [MettaEquationSatisfied, MettaConstraintsSatisfied,
          applyClassSolution]
    | var v =>
        simp [Metta.Unify.decomposeEq] at hdecomp
        subst constraints
        simp [MettaEquationSatisfied, MettaConstraintsSatisfied,
          applyClassSolution, eq_comm]
    | gnd ground => simp [Metta.Unify.decomposeEq] at hdecomp
    | expr atoms => simp [Metta.Unify.decomposeEq] at hdecomp
  · intro v right constraints _hleft _hright hdecomp
    cases right with
    | var w =>
        by_cases hvw : v = w
        · subst w
          simp [Metta.Unify.decomposeEq] at hdecomp
          subst constraints
          simp [MettaEquationSatisfied, MettaConstraintsSatisfied,
            applyClassSolution]
        · simp [Metta.Unify.decomposeEq, hvw] at hdecomp
          subst constraints
          simp [MettaEquationSatisfied, MettaConstraintsSatisfied,
            applyClassSolution]
    | sym symbol | gnd symbol | expr symbol =>
        simp [Metta.Unify.decomposeEq] at hdecomp
        subst constraints
        simp [MettaEquationSatisfied, MettaConstraintsSatisfied,
          applyClassSolution]
  · intro ground right constraints hleft hright hdecomp
    cases right with
    | sym symbol => simp [Metta.Unify.decomposeEq] at hdecomp
    | var v =>
        simp [Metta.Unify.decomposeEq] at hdecomp
        subst constraints
        simp [MettaEquationSatisfied, MettaConstraintsSatisfied,
          applyClassSolution, eq_comm]
    | gnd other =>
        simp [Metta.Unify.decomposeEq] at hdecomp
        rcases hdecomp with ⟨hequiv, rfl⟩
        rw [ground_eq_of_equiv_of_noFloat hleft hright hequiv]
        simp [MettaEquationSatisfied, MettaConstraintsSatisfied,
          applyClassSolution]
    | expr atoms => simp [Metta.Unify.decomposeEq] at hdecomp
  · intro atoms ih right constraints hleft hright hdecomp
    cases right with
    | sym symbol | gnd symbol =>
        simp [Metta.Unify.decomposeEq] at hdecomp
    | var v =>
        simp [Metta.Unify.decomposeEq] at hdecomp
        subst constraints
        simp [MettaEquationSatisfied, MettaConstraintsSatisfied,
          applyClassSolution, eq_comm]
    | expr rights =>
        have hleftChildren :
            ∀ atom ∈ atoms, MettaAtomNoFloat atom := by
          simpa [MettaAtomNoFloat] using hleft
        have hrightChildren :
            ∀ atom ∈ rights, MettaAtomNoFloat atom := by
          simpa [MettaAtomNoFloat] using hright
        have hlist : ∀ (lefts rights : List Metta.Atom) constraints,
            (∀ atom ∈ lefts, atom ∈ atoms) →
            (∀ atom ∈ lefts, MettaAtomNoFloat atom) →
            (∀ atom ∈ rights, MettaAtomNoFloat atom) →
            Metta.Unify.decomposeList lefts rights = some constraints →
            (MettaAtomListsSatisfied valuation lefts rights ↔
              MettaConstraintsSatisfied valuation constraints) := by
          intro lefts
          induction lefts with
          | nil =>
              intro rights constraints _ _ _ h
              cases rights with
              | nil =>
                  simp [Metta.Unify.decomposeList] at h
                  subst constraints
                  simp [MettaAtomListsSatisfied, MettaConstraintsSatisfied]
              | cons head tail =>
                  simp [Metta.Unify.decomposeList] at h
          | cons head tail ihTail =>
              intro rights constraints hsubset hlefts hrights h
              cases rights with
              | nil => simp [Metta.Unify.decomposeList] at h
              | cons rightHead rightTail =>
                  cases hhead : Metta.Unify.decomposeEq head rightHead with
                  | none =>
                      simp [Metta.Unify.decomposeList, hhead] at h
                  | some headConstraints =>
                      cases htail :
                          Metta.Unify.decomposeList tail rightTail with
                      | none =>
                          simp [Metta.Unify.decomposeList, hhead, htail] at h
                      | some tailConstraints =>
                          simp [Metta.Unify.decomposeList, hhead, htail] at h
                          subst constraints
                          have hheadIff :=
                            ih head (hsubset head (by simp))
                              rightHead headConstraints
                              (hlefts head (by simp))
                              (hrights rightHead (by simp)) hhead
                          have htailIff :=
                            ihTail rightTail tailConstraints
                              (fun atom hmem =>
                                hsubset atom (by simp [hmem]))
                              (fun atom hmem =>
                                hlefts atom (by simp [hmem]))
                              (fun atom hmem =>
                                hrights atom (by simp [hmem])) htail
                          have happend :
                              MettaConstraintsSatisfied valuation
                                  (headConstraints ++ tailConstraints) ↔
                                MettaConstraintsSatisfied valuation
                                    headConstraints ∧
                                  MettaConstraintsSatisfied valuation
                                    tailConstraints := by
                            constructor
                            · intro hall
                              exact
                                ⟨fun constraint hmem =>
                                    hall constraint (by simp [hmem]),
                                  fun constraint hmem =>
                                    hall constraint (by simp [hmem])⟩
                            · rintro ⟨hheadSat, htailSat⟩ constraint hmem
                              simp only [List.mem_append] at hmem
                              exact hmem.elim (hheadSat constraint)
                                (htailSat constraint)
                          rw [happend]
                          simpa [MettaAtomListsSatisfied,
                            MettaEquationSatisfied] using
                            and_congr hheadIff htailIff
        simpa [MettaEquationSatisfied, MettaAtomListsSatisfied,
          applyClassSolution] using
          hlist atoms rights constraints (fun atom hmem => hmem)
            hleftChildren hrightChildren hdecomp

/-- Decomposing a host-float-free equation worklist preserves its complete
valuation solution theory. -/
theorem decomposeAll_solution_iff
    (valuation : String → Metta.Atom) :
    ∀ (equations : List (Metta.Atom × Metta.Atom)) constraints,
      (∀ equation ∈ equations,
        MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2) →
      Metta.Unify.decomposeAll equations = some constraints →
      (MettaEquationsSatisfied valuation equations ↔
        MettaConstraintsSatisfied valuation constraints) := by
  intro equations
  induction equations with
  | nil =>
      intro constraints _ h
      simp [Metta.Unify.decomposeAll] at h
      subst constraints
      simp [MettaEquationsSatisfied, MettaConstraintsSatisfied]
  | cons equation rest ih =>
      intro constraints hnoFloat hdecomp
      cases hhead :
          Metta.Unify.decomposeEq equation.1 equation.2 with
      | none =>
          simp [Metta.Unify.decomposeAll, hhead] at hdecomp
      | some headConstraints =>
          cases htail : Metta.Unify.decomposeAll rest with
          | none =>
              simp [Metta.Unify.decomposeAll, hhead, htail] at hdecomp
          | some tailConstraints =>
              simp [Metta.Unify.decomposeAll, hhead, htail] at hdecomp
              subst constraints
              have heqNoFloat := hnoFloat equation (by simp)
              have hheadIff :=
                decomposeEq_solution_iff valuation
                  equation.1 equation.2 headConstraints
                  heqNoFloat.1 heqNoFloat.2 hhead
              have htailIff :=
                ih tailConstraints
                  (fun item hmem => hnoFloat item (by simp [hmem])) htail
              have happend :
                  MettaConstraintsSatisfied valuation
                      (headConstraints ++ tailConstraints) ↔
                    MettaConstraintsSatisfied valuation headConstraints ∧
                      MettaConstraintsSatisfied valuation tailConstraints := by
                constructor
                · intro hall
                  exact
                    ⟨fun constraint hmem =>
                        hall constraint (by simp [hmem]),
                      fun constraint hmem =>
                        hall constraint (by simp [hmem])⟩
                · rintro ⟨hheadSat, htailSat⟩ constraint hmem
                  simp only [List.mem_append] at hmem
                  exact hmem.elim (hheadSat constraint)
                    (htailSat constraint)
              rw [happend]
              simpa [MettaEquationsSatisfied] using
                and_congr hheadIff htailIff

/-- Structural decomposition of host-float-free atoms emits only
host-float-free constraint targets. -/
theorem decomposeEq_constraints_noFloat :
    ∀ (left right : Metta.Atom) constraints,
      MettaAtomNoFloat left → MettaAtomNoFloat right →
      Metta.Unify.decomposeEq left right = some constraints →
      ∀ constraint ∈ constraints,
        MettaAtomNoFloat constraint.2 := by
  intro left
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_ left
  · intro symbol right constraints hleft hright hdecompose
    cases right with
    | sym other =>
        simp [Metta.Unify.decomposeEq] at hdecompose
        rcases hdecompose with ⟨_, rfl⟩
        simp
    | var x =>
        simp [Metta.Unify.decomposeEq] at hdecompose
        subst constraints
        simpa using hleft
    | gnd ground => simp [Metta.Unify.decomposeEq] at hdecompose
    | expr atoms => simp [Metta.Unify.decomposeEq] at hdecompose
  · intro x right constraints hleft hright hdecompose
    cases right with
    | var y =>
        by_cases hxy : x = y
        · subst y
          simp [Metta.Unify.decomposeEq] at hdecompose
          subst constraints
          simp
        · simp [Metta.Unify.decomposeEq, hxy] at hdecompose
          subst constraints
          simp [MettaAtomNoFloat]
    | sym symbol | gnd symbol | expr symbol =>
        simp [Metta.Unify.decomposeEq] at hdecompose
        subst constraints
        simpa using hright
  · intro ground right constraints hleft hright hdecompose
    cases right with
    | sym symbol => simp [Metta.Unify.decomposeEq] at hdecompose
    | var x =>
        simp [Metta.Unify.decomposeEq] at hdecompose
        subst constraints
        simpa using hleft
    | gnd other =>
        simp [Metta.Unify.decomposeEq] at hdecompose
        rcases hdecompose with ⟨_, rfl⟩
        simp
    | expr atoms => simp [Metta.Unify.decomposeEq] at hdecompose
  · intro atoms ih right constraints hleft hright hdecompose
    cases right with
    | sym symbol | gnd symbol =>
        simp [Metta.Unify.decomposeEq] at hdecompose
    | var x =>
        simp [Metta.Unify.decomposeEq] at hdecompose
        subst constraints
        simpa using hleft
    | expr rights =>
        have hleftChildren :
            ∀ atom ∈ atoms, MettaAtomNoFloat atom := by
          simpa [MettaAtomNoFloat] using hleft
        have hrightChildren :
            ∀ atom ∈ rights, MettaAtomNoFloat atom := by
          simpa [MettaAtomNoFloat] using hright
        have hlist : ∀ (lefts rights : List Metta.Atom) constraints,
            (∀ atom ∈ lefts, atom ∈ atoms) →
            (∀ atom ∈ lefts, MettaAtomNoFloat atom) →
            (∀ atom ∈ rights, MettaAtomNoFloat atom) →
            Metta.Unify.decomposeList lefts rights = some constraints →
            ∀ constraint ∈ constraints,
              MettaAtomNoFloat constraint.2 := by
          intro lefts
          induction lefts with
          | nil =>
              intro rights constraints _ _ _ hdecompose
              cases rights <;>
                simp [Metta.Unify.decomposeList] at hdecompose
              subst constraints
              simp
          | cons head tail ihTail =>
              intro rights constraints hsubset hlefts hrights hdecompose
              cases rights with
              | nil =>
                  simp [Metta.Unify.decomposeList] at hdecompose
              | cons rightHead rightTail =>
                  cases hhead :
                      Metta.Unify.decomposeEq head rightHead with
                  | none =>
                      simp [Metta.Unify.decomposeList, hhead] at hdecompose
                  | some headConstraints =>
                      cases htail :
                          Metta.Unify.decomposeList tail rightTail with
                      | none =>
                          simp [Metta.Unify.decomposeList, hhead, htail]
                            at hdecompose
                      | some tailConstraints =>
                          simp [Metta.Unify.decomposeList, hhead, htail]
                            at hdecompose
                          subst constraints
                          intro constraint hconstraint
                          simp only [List.mem_append] at hconstraint
                          rcases hconstraint with hconstraint | hconstraint
                          · exact ih head (hsubset head (by simp))
                              rightHead headConstraints
                              (hlefts head (by simp))
                              (hrights rightHead (by simp)) hhead
                              constraint hconstraint
                          · exact ihTail rightTail tailConstraints
                              (fun atom hmem =>
                                hsubset atom (by simp [hmem]))
                              (fun atom hmem =>
                                hlefts atom (by simp [hmem]))
                              (fun atom hmem =>
                                hrights atom (by simp [hmem]))
                              htail constraint hconstraint
        exact hlist atoms rights constraints (fun atom hmem => hmem)
          hleftChildren hrightChildren hdecompose

/-- Decomposing a host-float-free worklist emits only host-float-free
constraint targets. -/
theorem decomposeAll_constraints_noFloat
    {equations : List (Metta.Atom × Metta.Atom)}
    {constraints : List (String × Metta.Atom)}
    (hnoFloat : ∀ equation ∈ equations,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hdecompose : Metta.Unify.decomposeAll equations = some constraints) :
    ∀ constraint ∈ constraints,
      MettaAtomNoFloat constraint.2 := by
  induction equations generalizing constraints with
  | nil =>
      simp [Metta.Unify.decomposeAll] at hdecompose
      subst constraints
      simp
  | cons equation rest ih =>
      cases hhead :
          Metta.Unify.decomposeEq equation.1 equation.2 with
      | none =>
          simp [Metta.Unify.decomposeAll, hhead] at hdecompose
      | some headConstraints =>
          cases htail : Metta.Unify.decomposeAll rest with
          | none =>
              simp [Metta.Unify.decomposeAll, hhead, htail] at hdecompose
          | some tailConstraints =>
              simp [Metta.Unify.decomposeAll, hhead, htail] at hdecompose
              subst constraints
              intro constraint hconstraint
              simp only [List.mem_append] at hconstraint
              rcases hconstraint with hconstraint | hconstraint
              · have hheadNoFloat := hnoFloat equation (by simp)
                exact decomposeEq_constraints_noFloat
                  equation.1 equation.2 headConstraints
                  hheadNoFloat.1 hheadNoFloat.2 hhead
                  constraint hconstraint
              · exact ih
                  (fun item hitem => hnoFloat item (by simp [hitem]))
                  htail constraint hconstraint

/-- Singleton substitution preserves the host-float-free fragment when its
replacement term belongs to that fragment. -/
theorem apply_singleton_noFloat
    {x : String} {term : Metta.Atom}
    (hterm : MettaAtomNoFloat term) :
    ∀ atom : Metta.Atom,
      MettaAtomNoFloat atom →
      MettaAtomNoFloat (Metta.Subst.apply [(x, term)] atom) := by
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_
  · intro symbol _
    simp [Metta.Subst.apply, MettaAtomNoFloat]
  · intro name _
    by_cases hname : name = x
    · subst name
      simpa [Metta.Subst.apply, Metta.Subst.lookup] using hterm
    · simp [Metta.Subst.apply, Metta.Subst.lookup, hname,
        MettaAtomNoFloat]
  · intro ground hground
    simpa [Metta.Subst.apply] using hground
  · intro atoms ih hatoms
    have hchildren :
        ∀ atom ∈ atoms, MettaAtomNoFloat atom := by
      simpa [MettaAtomNoFloat] using hatoms
    simp only [Metta.Subst.apply, MettaAtomNoFloat]
    intro applied hmem
    obtain ⟨atom, hatom, rfl⟩ := List.mem_map.mp hmem
    exact ih atom hatom (hchildren atom hatom)

/-- Under a valuation satisfying `x = term`, replacing `x` by `term` anywhere
in an atom preserves its denotation. -/
theorem apply_singleton_eq_of_satisfied
    (valuation : String → Metta.Atom) {x : String} {term : Metta.Atom}
    (h : valuation x = applyClassSolution valuation term) :
    ∀ atom : Metta.Atom,
      applyClassSolution valuation
          (Metta.Subst.apply [(x, term)] atom) =
        applyClassSolution valuation atom := by
  intro atom
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_ atom
  · intro symbol
    simp [Metta.Subst.apply, applyClassSolution]
  · intro v
    by_cases hv : v = x
    · subst v
      simpa [Metta.Subst.apply, Metta.Subst.lookup,
        applyClassSolution] using h.symm
    · simp [Metta.Subst.apply, Metta.Subst.lookup,
        applyClassSolution, hv]
  · intro ground
    simp [Metta.Subst.apply, applyClassSolution]
  · intro atoms ih
    simp only [Metta.Subst.apply, applyClassSolution, List.map_map]
    congr 1
    apply List.map_congr_left
    exact ih

/-- Eliminating one satisfied variable constraint from the remaining
constraint worklist preserves its complete solution theory. -/
theorem eliminatedConstraints_solution_iff
    (valuation : String → Metta.Atom) {x : String} {term : Metta.Atom}
    (h : valuation x = applyClassSolution valuation term)
    (rest : List (String × Metta.Atom)) :
    MettaEquationsSatisfied valuation
        (rest.map fun p =>
          (Metta.Subst.apply [(x, term)] (.var p.1),
            Metta.Subst.apply [(x, term)] p.2)) ↔
      MettaConstraintsSatisfied valuation rest := by
  constructor
  · intro hall constraint hmem
    have hmapped :
        (Metta.Subst.apply [(x, term)] (.var constraint.1),
          Metta.Subst.apply [(x, term)] constraint.2) ∈
          rest.map fun p =>
            (Metta.Subst.apply [(x, term)] (.var p.1),
              Metta.Subst.apply [(x, term)] p.2) :=
      List.mem_map_of_mem hmem
    have heq := hall _ hmapped
    unfold MettaEquationSatisfied at heq
    rw [apply_singleton_eq_of_satisfied valuation h,
      apply_singleton_eq_of_satisfied valuation h] at heq
    simpa [applyClassSolution] using heq
  · intro hall equation hmem
    obtain ⟨constraint, hconstraint, rfl⟩ := List.mem_map.mp hmem
    have heq := hall constraint hconstraint
    unfold MettaEquationSatisfied
    rw [apply_singleton_eq_of_satisfied valuation h,
      apply_singleton_eq_of_satisfied valuation h]
    simpa [applyClassSolution] using heq

/-- Variable keys explicitly recorded by a unifier substitution. -/
def mettaSubstKeys (subst : Metta.Subst) : List String :=
  subst.map Prod.fst

/-- Every variable mentioned by a decomposed unification constraint, including
its left-hand key. -/
def mettaConstraintVars
    (constraints : List (String × Metta.Atom)) : List String :=
  constraints.flatMap fun constraint =>
    constraint.1 :: constraint.2.vars

/-- Structural decomposition introduces no variables: every variable in a
returned constraint already occurs in one of the input atoms. -/
theorem decomposeEq_constraintVars_subset :
    ∀ (left right : Metta.Atom) constraints,
      Metta.Unify.decomposeEq left right = some constraints →
      ∀ name ∈ mettaConstraintVars constraints,
        name ∈ left.vars ++ right.vars := by
  intro left
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_ left
  · intro symbol right constraints hdecompose
    cases right with
    | sym other =>
        simp [Metta.Unify.decomposeEq] at hdecompose
        rcases hdecompose with ⟨_, rfl⟩
        simp [mettaConstraintVars, Metta.Atom.vars]
    | var x =>
        simp [Metta.Unify.decomposeEq] at hdecompose
        subst constraints
        simp [mettaConstraintVars, Metta.Atom.vars]
    | gnd ground => simp [Metta.Unify.decomposeEq] at hdecompose
    | expr atoms => simp [Metta.Unify.decomposeEq] at hdecompose
  · intro x right constraints hdecompose
    cases right with
    | var y =>
        by_cases hxy : x = y
        · subst y
          simp [Metta.Unify.decomposeEq] at hdecompose
          subst constraints
          simp [mettaConstraintVars, Metta.Atom.vars]
        · simp [Metta.Unify.decomposeEq, hxy] at hdecompose
          subst constraints
          simp [mettaConstraintVars, Metta.Atom.vars]
    | sym symbol | gnd symbol | expr symbol =>
        simp [Metta.Unify.decomposeEq] at hdecompose
        subst constraints
        simp [mettaConstraintVars, Metta.Atom.vars]
  · intro ground right constraints hdecompose
    cases right with
    | sym symbol => simp [Metta.Unify.decomposeEq] at hdecompose
    | var x =>
        simp [Metta.Unify.decomposeEq] at hdecompose
        subst constraints
        simp [mettaConstraintVars, Metta.Atom.vars]
    | gnd other =>
        simp [Metta.Unify.decomposeEq] at hdecompose
        rcases hdecompose with ⟨_, rfl⟩
        simp [mettaConstraintVars, Metta.Atom.vars]
    | expr atoms => simp [Metta.Unify.decomposeEq] at hdecompose
  · intro atoms ih right constraints hdecompose
    cases right with
    | sym symbol | gnd symbol =>
        simp [Metta.Unify.decomposeEq] at hdecompose
    | var x =>
        simp [Metta.Unify.decomposeEq] at hdecompose
        subst constraints
        simp [mettaConstraintVars, Metta.Atom.vars]
        aesop
    | expr rights =>
        have hlist : ∀ (lefts rights : List Metta.Atom) constraints,
            (∀ atom ∈ lefts, atom ∈ atoms) →
            Metta.Unify.decomposeList lefts rights = some constraints →
            ∀ name ∈ mettaConstraintVars constraints,
              name ∈
                (lefts.map Metta.Atom.vars).flatten ++
                  (rights.map Metta.Atom.vars).flatten := by
          intro lefts
          induction lefts with
          | nil =>
              intro rights constraints _ hdecompose
              cases rights <;>
                simp [Metta.Unify.decomposeList] at hdecompose
              subst constraints
              simp [mettaConstraintVars]
          | cons head tail ihTail =>
              intro rights constraints hsubset hdecompose
              cases rights with
              | nil =>
                  simp [Metta.Unify.decomposeList] at hdecompose
              | cons rightHead rightTail =>
                  cases hhead :
                      Metta.Unify.decomposeEq head rightHead with
                  | none =>
                      simp [Metta.Unify.decomposeList, hhead] at hdecompose
                  | some headConstraints =>
                      cases htail :
                          Metta.Unify.decomposeList tail rightTail with
                      | none =>
                          simp [Metta.Unify.decomposeList, hhead, htail]
                            at hdecompose
                      | some tailConstraints =>
                          simp [Metta.Unify.decomposeList, hhead, htail]
                            at hdecompose
                          subst constraints
                          intro name hvariable
                          simp only [mettaConstraintVars,
                            List.flatMap_append, List.mem_append] at hvariable
                          rcases hvariable with hvariable | hvariable
                          · have hout :=
                              ih head (hsubset head (by simp)) rightHead
                                headConstraints hhead name hvariable
                            simp only [List.map_cons, List.flatten_cons,
                              List.mem_append] at hout ⊢
                            aesop
                          · have hout :=
                              ihTail rightTail tailConstraints
                                (fun atom hmem =>
                                  hsubset atom (by simp [hmem]))
                                htail name hvariable
                            simp only [List.map_cons, List.flatten_cons,
                              List.mem_append] at hout ⊢
                            aesop
        simpa [Metta.Atom.vars] using
          hlist atoms rights constraints (fun atom hmem => hmem) hdecompose

/-- Every variable mentioned by an equation worklist. -/
def mettaEquationVars
    (equations : List (Metta.Atom × Metta.Atom)) : List String :=
  equations.flatMap fun equation =>
    equation.1.vars ++ equation.2.vars

/-- Worklist decomposition likewise introduces no variables. -/
theorem decomposeAll_constraintVars_subset
    {equations : List (Metta.Atom × Metta.Atom)}
    {constraints : List (String × Metta.Atom)}
    (hdecompose : Metta.Unify.decomposeAll equations = some constraints) :
    ∀ name ∈ mettaConstraintVars constraints,
      name ∈ mettaEquationVars equations := by
  induction equations generalizing constraints with
  | nil =>
      simp [Metta.Unify.decomposeAll] at hdecompose
      subst constraints
      simp [mettaConstraintVars, mettaEquationVars]
  | cons equation rest ih =>
      cases hhead :
          Metta.Unify.decomposeEq equation.1 equation.2 with
      | none =>
          simp [Metta.Unify.decomposeAll, hhead] at hdecompose
      | some headConstraints =>
          cases htail : Metta.Unify.decomposeAll rest with
          | none =>
              simp [Metta.Unify.decomposeAll, hhead, htail] at hdecompose
          | some tailConstraints =>
              simp [Metta.Unify.decomposeAll, hhead, htail] at hdecompose
              subst constraints
              intro name hname
              simp only [mettaConstraintVars, List.flatMap_append,
                List.mem_append] at hname
              simp only [mettaEquationVars, List.flatMap_cons,
                List.mem_append]
              rcases hname with hname | hname
              · apply Or.inl
                simpa only [List.mem_append] using
                  (decomposeEq_constraintVars_subset
                    equation.1 equation.2 headConstraints hhead name hname)
              · exact Or.inr (ih htail name hname)

/-- The executable occurs check returning `false` certifies syntactic absence
from the proof-facing variable list. -/
theorem not_mem_vars_of_occurs_eq_false (x : String) :
    ∀ atom : Metta.Atom,
      Metta.Subst.occurs x atom = false → x ∉ atom.vars := by
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_
  · intro symbol _
    simp [Metta.Atom.vars]
  · intro name hoccurs
    simp [Metta.Subst.occurs, Metta.Atom.vars] at hoccurs ⊢
    exact hoccurs
  · intro ground _
    simp [Metta.Atom.vars]
  · intro atoms ih hoccurs hmem
    simp only [Metta.Subst.occurs, List.any_eq_false] at hoccurs
    simp only [Metta.Atom.vars, List.mem_flatten] at hmem
    obtain ⟨childVars, hchildVars, hx⟩ := hmem
    obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hchildVars
    have hchildOccurs : Metta.Subst.occurs x child = false := by
      have hnotTrue := hoccurs ⟨child, hchild⟩ (by simp)
      simpa using hnotTrue
    exact ih child hchild hchildOccurs hx

/-- A singleton elimination introduces only variables from its replacement
term.  Thus a name absent from that term remains absent if it is either the
eliminated name itself or was absent from the input atom. -/
theorem not_mem_vars_apply_singleton
    {x y : String} {term : Metta.Atom} :
    ∀ atom : Metta.Atom,
      (y = x ∨ y ∉ atom.vars) →
      y ∉ term.vars →
      y ∉ (Metta.Subst.apply [(x, term)] atom).vars := by
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_
  · intro symbol _ _
    simp [Metta.Subst.apply, Metta.Atom.vars]
  · intro name hy hterm
    by_cases hname : name = x
    · subst name
      simp [Metta.Subst.apply, Metta.Subst.lookup, hterm]
    · have hyname : y ≠ name := by
        rcases hy with rfl | hy
        · exact Ne.symm hname
        · simpa [Metta.Atom.vars] using hy
      simpa [Metta.Subst.apply, Metta.Subst.lookup, hname,
        Metta.Atom.vars] using hyname
  · intro ground _ _
    simp [Metta.Subst.apply, Metta.Atom.vars]
  · intro atoms ih hy hterm hmem
    simp only [Metta.Subst.apply, Metta.Atom.vars,
      List.mem_flatten] at hmem
    obtain ⟨childVars, hchildVars, hymem⟩ := hmem
    obtain ⟨appliedChild, happliedChild, rfl⟩ :=
      List.mem_map.mp hchildVars
    obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp happliedChild
    apply ih child hchild
    · rcases hy with rfl | hy
      · exact Or.inl rfl
      · apply Or.inr
        intro hchildMem
        apply hy
        simp only [Metta.Atom.vars, List.mem_flatten]
        exact
          ⟨child.vars,
            List.mem_map.mpr ⟨child, hchild, rfl⟩,
            hchildMem⟩
    · exact hterm
    · exact hymem

private theorem substErase_eq_self_of_key_not_mem
    {subst : Metta.Subst} {x : String}
    (hfresh : x ∉ mettaSubstKeys subst) :
    Metta.Subst.erase subst x = subst := by
  unfold Metta.Subst.erase
  apply List.filter_eq_self.mpr
  intro binding hbinding
  have hne : binding.1 ≠ x := by
    intro h
    apply hfresh
    exact List.mem_map.mpr ⟨binding, hbinding, h⟩
  simp [hne]

private theorem substExtend_eq_cons_of_key_not_mem
    {subst : Metta.Subst} {x : String} {term : Metta.Atom}
    (hfresh : x ∉ mettaSubstKeys subst) :
    Metta.Subst.extend subst x term = (x, term) :: subst := by
  simp [Metta.Subst.extend, substErase_eq_self_of_key_not_mem hfresh]

/-- The accumulated substitution mentions none of the variables still present
in the unification worklist.  No ordering or uniqueness property of the
substitution presentation is required. -/
def UnifyStateFresh
    (equations : List (Metta.Atom × Metta.Atom))
    (subst : Metta.Subst) : Prop :=
  ∀ key ∈ mettaSubstKeys subst,
    key ∉ mettaEquationVars equations

/-- One occurs-checked elimination round preserves state freshness. -/
theorem unifyRound_preserves_freshness
    {equations : List (Metta.Atom × Metta.Atom)}
    {subst : Metta.Subst} {x : String} {term : Metta.Atom}
    {rest : List (String × Metta.Atom)}
    (hdecompose :
      Metta.Unify.decomposeAll equations = some ((x, term) :: rest))
    (hoccurs : Metta.Subst.occurs x term = false)
    (hfreshState : UnifyStateFresh equations subst) :
    let remaining := rest.map fun constraint =>
      (Metta.Subst.apply [(x, term)] (.var constraint.1),
        Metta.Subst.apply [(x, term)] constraint.2)
    UnifyStateFresh remaining (Metta.Subst.extend subst x term) := by
  have hxSource : x ∈ mettaEquationVars equations :=
    decomposeAll_constraintVars_subset hdecompose x (by
      simp [mettaConstraintVars])
  have hxFresh : x ∉ mettaSubstKeys subst := by
    intro hx
    exact hfreshState x hx hxSource
  have hkeys :
      mettaSubstKeys (Metta.Subst.extend subst x term) =
        x :: mettaSubstKeys subst := by
    rw [substExtend_eq_cons_of_key_not_mem hxFresh]
    rfl
  have htermSource : ∀ name ∈ term.vars,
      name ∈ mettaEquationVars equations := by
    intro name hname
    apply decomposeAll_constraintVars_subset hdecompose name
    simp [mettaConstraintVars, hname]
  have hrestSource : ∀ constraint ∈ rest,
      ∀ name ∈ constraint.1 :: constraint.2.vars,
        name ∈ mettaEquationVars equations := by
    intro constraint hconstraint name hname
    apply decomposeAll_constraintVars_subset hdecompose name
    unfold mettaConstraintVars
    apply List.mem_flatMap.mpr
    exact ⟨constraint, by simp [hconstraint], hname⟩
  dsimp only
  unfold UnifyStateFresh
  rw [hkeys]
  intro name hname
  simp only [List.mem_cons] at hname
  have htermAbsent : name ∉ term.vars := by
    rcases hname with hname | hname
    · rw [hname]
      exact not_mem_vars_of_occurs_eq_false x term hoccurs
    · intro hmem
      exact hfreshState name hname (htermSource name hmem)
  intro hremaining
  simp only [mettaEquationVars, List.mem_flatMap] at hremaining
  obtain ⟨equation, hequation, hnameVars⟩ := hremaining
  obtain ⟨constraint, hconstraint, rfl⟩ :=
    List.mem_map.mp hequation
  simp only [List.mem_append] at hnameVars
  rcases hnameVars with hnameVars | hnameVars
  · apply not_mem_vars_apply_singleton
      (atom := Metta.Atom.var constraint.1) ?_ htermAbsent hnameVars
    rcases hname with hname | hname
    · exact Or.inl hname
    · apply Or.inr
      intro hmem
      exact hfreshState name hname
        (hrestSource constraint hconstraint name
          (List.mem_cons.mpr (Or.inl (by
            simpa [Metta.Atom.vars] using hmem))))
  · apply not_mem_vars_apply_singleton
      (atom := constraint.2) ?_ htermAbsent hnameVars
    rcases hname with hname | hname
    · exact Or.inl hname
    · apply Or.inr
      intro hmem
      exact hfreshState name hname
        (hrestSource constraint hconstraint name
          (List.mem_cons.mpr (Or.inr hmem)))

/-- One elimination round also preserves the host-float-free fragment. -/
theorem unifyRound_preserves_noFloat
    {equations : List (Metta.Atom × Metta.Atom)}
    {x : String} {term : Metta.Atom}
    {rest : List (String × Metta.Atom)}
    (hnoFloat : ∀ equation ∈ equations,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hdecompose :
      Metta.Unify.decomposeAll equations = some ((x, term) :: rest)) :
    let remaining := rest.map fun constraint =>
      (Metta.Subst.apply [(x, term)] (.var constraint.1),
        Metta.Subst.apply [(x, term)] constraint.2)
    ∀ equation ∈ remaining,
      MettaAtomNoFloat equation.1 ∧
        MettaAtomNoFloat equation.2 := by
  have hconstraints :=
    decomposeAll_constraints_noFloat hnoFloat hdecompose
  have hterm : MettaAtomNoFloat term :=
    hconstraints (x, term) (by simp)
  dsimp only
  intro equation hequation
  obtain ⟨constraint, hconstraint, rfl⟩ :=
    List.mem_map.mp hequation
  constructor
  · apply apply_singleton_noFloat hterm
    simp [MettaAtomNoFloat]
  · apply apply_singleton_noFloat hterm
    exact hconstraints constraint (by simp [hconstraint])

private theorem constraintsSatisfied_cons_iff
    (valuation : String → Metta.Atom)
    (constraint : String × Metta.Atom)
    (rest : List (String × Metta.Atom)) :
    MettaConstraintsSatisfied valuation (constraint :: rest) ↔
      valuation constraint.1 =
          applyClassSolution valuation constraint.2 ∧
        MettaConstraintsSatisfied valuation rest := by
  constructor
  · intro hall
    exact
      ⟨hall constraint (by simp),
        fun item hmem => hall item (by simp [hmem])⟩
  · rintro ⟨hhead, htail⟩ item hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact hhead
    · exact htail item hmem

/-- Extending a substitution at a fresh key conjoins exactly one new equation
to its valuation theory. -/
theorem constraintsSatisfied_extend_iff
    (valuation : String → Metta.Atom)
    {subst : Metta.Subst} {x : String} {term : Metta.Atom}
    (hfresh : x ∉ mettaSubstKeys subst) :
    MettaConstraintsSatisfied valuation
        (Metta.Subst.extend subst x term) ↔
      valuation x = applyClassSolution valuation term ∧
        MettaConstraintsSatisfied valuation subst := by
  rw [substExtend_eq_cons_of_key_not_mem hfresh]
  exact constraintsSatisfied_cons_iff valuation (x, term) subst

/-- One successful Robinson elimination round preserves the complete theory
of the current equation worklist together with the accumulated substitution.
This is the semantic reconciliation kernel shared by sparse and redundant MGU
presentations. -/
theorem unifyRound_solution_iff
    (valuation : String → Metta.Atom)
    {equations : List (Metta.Atom × Metta.Atom)}
    {subst : Metta.Subst} {x : String} {term : Metta.Atom}
    {rest : List (String × Metta.Atom)}
    (hnoFloat : ∀ equation ∈ equations,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hdecomp :
      Metta.Unify.decomposeAll equations = some ((x, term) :: rest))
    (hfresh : x ∉ mettaSubstKeys subst) :
    let remaining := rest.map fun p =>
      (Metta.Subst.apply [(x, term)] (.var p.1),
        Metta.Subst.apply [(x, term)] p.2)
    (MettaEquationsSatisfied valuation remaining ∧
        MettaConstraintsSatisfied valuation
          (Metta.Subst.extend subst x term)) ↔
      (MettaEquationsSatisfied valuation equations ∧
        MettaConstraintsSatisfied valuation subst) := by
  dsimp only
  have hdecompIff :=
    decomposeAll_solution_iff valuation equations ((x, term) :: rest)
      hnoFloat hdecomp
  have hextendIff :=
    constraintsSatisfied_extend_iff valuation (term := term) hfresh
  constructor
  · rintro ⟨hremaining, hextended⟩
    obtain ⟨hxt, hsubst⟩ := hextendIff.mp hextended
    have hrest :=
      (eliminatedConstraints_solution_iff valuation hxt rest).mp hremaining
    have hconstraints :
        MettaConstraintsSatisfied valuation ((x, term) :: rest) :=
      (constraintsSatisfied_cons_iff valuation (x, term) rest).mpr
        ⟨hxt, hrest⟩
    exact ⟨hdecompIff.mpr hconstraints, hsubst⟩
  · rintro ⟨hequations, hsubst⟩
    have hconstraints := hdecompIff.mp hequations
    obtain ⟨hxt, hrest⟩ :=
      (constraintsSatisfied_cons_iff valuation (x, term) rest).mp
        hconstraints
    have hremaining :=
      (eliminatedConstraints_solution_iff valuation hxt rest).mpr hrest
    exact ⟨hremaining, hextendIff.mpr ⟨hxt, hsubst⟩⟩

/-- Every successful run of repaired LeaTTa's Robinson unifier preserves the
complete valuation theory of the original equation worklist and accumulated
substitution.  The result need not be the same ordered MGU as another engine. -/
theorem unifyRounds_solution_iff
    (valuation : String → Metta.Atom)
    {fuel : Nat} {equations : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst}
    (hnoFloat : ∀ equation ∈ equations,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hfresh : UnifyStateFresh equations subst)
    (hunify :
      Metta.Unify.unifyRounds fuel equations subst = some result) :
    MettaConstraintsSatisfied valuation result ↔
      MettaEquationsSatisfied valuation equations ∧
        MettaConstraintsSatisfied valuation subst := by
  induction fuel generalizing equations subst result with
  | zero =>
      cases hdecompose : Metta.Unify.decomposeAll equations with
      | none =>
          simp [Metta.Unify.unifyRounds, hdecompose] at hunify
      | some constraints =>
          cases constraints with
          | nil =>
              simp [Metta.Unify.unifyRounds, hdecompose] at hunify
              subst result
              have hequations :
                  MettaEquationsSatisfied valuation equations :=
                (decomposeAll_solution_iff valuation equations []
                  hnoFloat hdecompose).mpr (by
                    simp [MettaConstraintsSatisfied])
              exact
                ⟨fun hsubst => ⟨hequations, hsubst⟩,
                  fun hboth => hboth.2⟩
          | cons constraint rest =>
              simp [Metta.Unify.unifyRounds, hdecompose] at hunify
  | succ fuel ih =>
      cases hdecompose : Metta.Unify.decomposeAll equations with
      | none =>
          simp [Metta.Unify.unifyRounds, hdecompose] at hunify
      | some constraints =>
          cases constraints with
          | nil =>
              simp [Metta.Unify.unifyRounds, hdecompose] at hunify
              subst result
              have hequations :
                  MettaEquationsSatisfied valuation equations :=
                (decomposeAll_solution_iff valuation equations []
                  hnoFloat hdecompose).mpr (by
                    simp [MettaConstraintsSatisfied])
              exact
                ⟨fun hsubst => ⟨hequations, hsubst⟩,
                  fun hboth => hboth.2⟩
          | cons constraint rest =>
              obtain ⟨x, term⟩ := constraint
              cases hoccurs : Metta.Subst.occurs x term with
              | true =>
                  simp [Metta.Unify.unifyRounds, hdecompose, hoccurs]
                    at hunify
              | false =>
                  let remaining := rest.map fun item =>
                    (Metta.Subst.apply [(x, term)] (.var item.1),
                      Metta.Subst.apply [(x, term)] item.2)
                  have hunify' :
                      Metta.Unify.unifyRounds fuel remaining
                          (Metta.Subst.extend subst x term) = some result := by
                    simpa [Metta.Unify.unifyRounds, hdecompose, hoccurs,
                      remaining] using hunify
                  have hxSource : x ∈ mettaEquationVars equations :=
                    decomposeAll_constraintVars_subset hdecompose x (by
                      simp [mettaConstraintVars])
                  have hxFresh : x ∉ mettaSubstKeys subst := by
                    intro hx
                    exact hfresh x hx hxSource
                  have hnoFloat' : ∀ equation ∈ remaining,
                      MettaAtomNoFloat equation.1 ∧
                        MettaAtomNoFloat equation.2 := by
                    simpa [remaining] using
                      (unifyRound_preserves_noFloat hnoFloat hdecompose)
                  have hfresh' :
                      UnifyStateFresh remaining
                        (Metta.Subst.extend subst x term) := by
                    simpa [remaining] using
                      (unifyRound_preserves_freshness
                        hdecompose hoccurs hfresh)
                  have hinduction := ih hnoFloat' hfresh' hunify'
                  have hround :=
                    unifyRound_solution_iff valuation
                      hnoFloat hdecompose hxFresh
                  exact hinduction.trans (by
                    simpa [remaining] using hround)

/-- The sequence of variable constraints actually selected for elimination by
repaired LeaTTa's Robinson loop.  This is a proof certificate for structural
provenance, not part of the runtime result and not an ordering requirement on
another engine's MGU. -/
def unificationEliminationTrace :
    Nat → List (Metta.Atom × Metta.Atom) →
      List (String × Metta.Atom)
  | 0, _ => []
  | fuel + 1, equations =>
      match Metta.Unify.decomposeAll equations with
      | none | some [] => []
      | some ((key, term) :: rest) =>
          if Metta.Subst.occurs key term then []
          else
            let sub : Metta.Subst := [(key, term)]
            let remaining := rest.map fun constraint =>
              (Metta.Subst.apply sub (.var constraint.1),
                Metta.Subst.apply sub constraint.2)
            (key, term) :: unificationEliminationTrace fuel remaining

/-- Every constraint recorded by the successful-elimination trace is a
non-reflexive variable equation.  A reflexive variable target would make the
occurs check true at the very step that records it. -/
theorem unificationEliminationTrace_noSelfVariable
    (fuel : Nat) (equations : List (Metta.Atom × Metta.Atom)) :
    MettaSubstNoSelfVariable
      (unificationEliminationTrace fuel equations) := by
  induction fuel generalizing equations with
  | zero =>
      simp [MettaSubstNoSelfVariable, unificationEliminationTrace]
  | succ fuel ih =>
      cases hdecompose : Metta.Unify.decomposeAll equations with
      | none =>
          simp [MettaSubstNoSelfVariable, unificationEliminationTrace,
            hdecompose]
      | some constraints =>
          cases constraints with
          | nil =>
              simp [MettaSubstNoSelfVariable, unificationEliminationTrace,
                hdecompose]
          | cons constraint rest =>
              rcases constraint with ⟨key, term⟩
              cases hoccurs : Metta.Subst.occurs key term with
              | true =>
                  simp [MettaSubstNoSelfVariable,
                    unificationEliminationTrace, hdecompose, hoccurs]
              | false =>
                  let remaining := rest.map fun item =>
                    (Metta.Subst.apply [(key, term)] (.var item.1),
                      Metta.Subst.apply [(key, term)] item.2)
                  intro candidate hmem
                  simp only [unificationEliminationTrace, hdecompose,
                    hoccurs, Bool.false_eq_true, ↓reduceIte,
                    List.mem_cons] at hmem
                  rcases hmem with hhead | htail
                  · have hkey : candidate = key :=
                      congrArg Prod.fst hhead
                    have hterm : Metta.Atom.var candidate = term :=
                      congrArg Prod.snd hhead
                    subst candidate
                    subst term
                    simp [Metta.Subst.occurs] at hoccurs
                  · apply ih remaining candidate
                    simpa [remaining] using htail

/-- In a fresh unification state, the returned substitution is exactly the
reverse solve trace followed by the incoming substitution.  This is an
internal characterization of repaired LeaTTa's normalization order; it makes
no claim that HE or any other implementation selects the same MGU. -/
theorem unifyRounds_result_eq_eliminationTrace_reverse_append
    {fuel : Nat} {equations : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst}
    (hfresh : UnifyStateFresh equations subst)
    (hrun : Metta.Unify.unifyRounds fuel equations subst = some result) :
    result =
      (unificationEliminationTrace fuel equations).reverse ++ subst := by
  induction fuel generalizing equations subst result with
  | zero =>
      cases hdecompose : Metta.Unify.decomposeAll equations with
      | none => simp [Metta.Unify.unifyRounds, hdecompose] at hrun
      | some constraints =>
          cases constraints with
          | nil =>
              simp [Metta.Unify.unifyRounds, hdecompose] at hrun
              subst result
              simp [unificationEliminationTrace]
          | cons constraint rest =>
              simp [Metta.Unify.unifyRounds, hdecompose] at hrun
  | succ fuel ih =>
      cases hdecompose : Metta.Unify.decomposeAll equations with
      | none => simp [Metta.Unify.unifyRounds, hdecompose] at hrun
      | some constraints =>
          cases constraints with
          | nil =>
              simp [Metta.Unify.unifyRounds, hdecompose] at hrun
              subst result
              simp [unificationEliminationTrace, hdecompose]
          | cons constraint rest =>
              rcases constraint with ⟨key, term⟩
              cases hoccurs : Metta.Subst.occurs key term with
              | true =>
                  simp [Metta.Unify.unifyRounds, hdecompose, hoccurs] at hrun
              | false =>
                  let remaining := rest.map fun item =>
                    (Metta.Subst.apply [(key, term)] (.var item.1),
                      Metta.Subst.apply [(key, term)] item.2)
                  have hrun' :
                      Metta.Unify.unifyRounds fuel remaining
                          (Metta.Subst.extend subst key term) = some result := by
                    simpa [Metta.Unify.unifyRounds, hdecompose, hoccurs,
                      remaining] using hrun
                  have hkeySource : key ∈ mettaEquationVars equations :=
                    decomposeAll_constraintVars_subset hdecompose key (by
                      simp [mettaConstraintVars])
                  have hkeyFresh : key ∉ mettaSubstKeys subst := by
                    intro hkey
                    exact hfresh key hkey hkeySource
                  have hfresh' :
                      UnifyStateFresh remaining
                        (Metta.Subst.extend subst key term) := by
                    simpa [remaining] using
                      (unifyRound_preserves_freshness
                        hdecompose hoccurs hfresh)
                  rw [ih hfresh' hrun',
                    substExtend_eq_cons_of_key_not_mem hkeyFresh]
                  simp [unificationEliminationTrace, hdecompose, hoccurs,
                    remaining, List.append_assoc]

/-- Every entry in a successful Robinson result was either present in the
incoming substitution or was an actual eliminated constraint.  In particular,
no normalized value appears from the valuation-theory proof alone: it carries
a concrete syntactic provenance trace. -/
theorem unifyRounds_result_mem_or_mem_eliminationTrace
    {fuel : Nat} {equations : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {binding : String × Metta.Atom}
    (hrun :
      Metta.Unify.unifyRounds fuel equations subst = some result)
    (hmem : binding ∈ result) :
    binding ∈ subst ∨
      binding ∈ unificationEliminationTrace fuel equations := by
  induction fuel generalizing equations subst result binding with
  | zero =>
      cases hdecompose : Metta.Unify.decomposeAll equations with
      | none =>
          simp [Metta.Unify.unifyRounds, hdecompose] at hrun
      | some constraints =>
          cases constraints with
          | nil =>
              simp [Metta.Unify.unifyRounds, hdecompose] at hrun
              subst result
              exact Or.inl hmem
          | cons constraint rest =>
              simp [Metta.Unify.unifyRounds, hdecompose] at hrun
  | succ fuel ih =>
      cases hdecompose : Metta.Unify.decomposeAll equations with
      | none =>
          simp [Metta.Unify.unifyRounds, hdecompose] at hrun
      | some constraints =>
          cases constraints with
          | nil =>
              simp [Metta.Unify.unifyRounds, hdecompose] at hrun
              subst result
              exact Or.inl hmem
          | cons constraint rest =>
              rcases constraint with ⟨key, term⟩
              cases hoccurs : Metta.Subst.occurs key term with
              | true =>
                  simp [Metta.Unify.unifyRounds, hdecompose, hoccurs] at hrun
              | false =>
                  let remaining := rest.map fun item =>
                    (Metta.Subst.apply [(key, term)] (.var item.1),
                      Metta.Subst.apply [(key, term)] item.2)
                  have hrun' :
                      Metta.Unify.unifyRounds fuel remaining
                          (Metta.Subst.extend subst key term) = some result := by
                    simpa [Metta.Unify.unifyRounds, hdecompose, hoccurs,
                      remaining] using hrun
                  rcases ih hrun' hmem with hextended | htail
                  · simp only [Metta.Subst.extend, List.mem_cons] at hextended
                    rcases hextended with hhead | hold
                    · exact Or.inr (by
                        have hbinding : binding = (key, term) := hhead
                        subst binding
                        simp [unificationEliminationTrace, hdecompose,
                          hoccurs])
                    · exact Or.inl (List.mem_filter.mp hold).1
                  · exact Or.inr (by
                      simp [unificationEliminationTrace, hdecompose,
                        hoccurs, remaining, htail])

/-- A successful Robinson run cannot synthesize the reflexive substitution
`x ↦ $x`.  Such an entry must either have been present in the incoming
substitution or have arisen at an occurs-checked elimination step. -/
theorem unifyRounds_result_noSelfVariable
    {fuel : Nat} {equations : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst}
    (hsubst : MettaSubstNoSelfVariable subst)
    (hrun : Metta.Unify.unifyRounds fuel equations subst = some result) :
    MettaSubstNoSelfVariable result := by
  intro key hmem
  rcases unifyRounds_result_mem_or_mem_eliminationTrace hrun hmem with
    hold | htrace
  · exact hsubst key hold
  · exact unificationEliminationTrace_noSelfVariable fuel equations key htrace

/-- Successful elimination never removes an entry already accumulated in a
fresh unification state.  Every later eliminated key comes from the remaining
worklist and is therefore distinct from all accumulated keys. -/
theorem unifyRounds_preserves_subst_mem
    {fuel : Nat} {equations : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {binding : String × Metta.Atom}
    (hfresh : UnifyStateFresh equations subst)
    (hrun : Metta.Unify.unifyRounds fuel equations subst = some result)
    (hmem : binding ∈ subst) :
    binding ∈ result := by
  induction fuel generalizing equations subst result binding with
  | zero =>
      cases hdecompose : Metta.Unify.decomposeAll equations with
      | none => simp [Metta.Unify.unifyRounds, hdecompose] at hrun
      | some constraints =>
          cases constraints with
          | nil =>
              simp [Metta.Unify.unifyRounds, hdecompose] at hrun
              subst result
              exact hmem
          | cons constraint rest =>
              simp [Metta.Unify.unifyRounds, hdecompose] at hrun
  | succ fuel ih =>
      cases hdecompose : Metta.Unify.decomposeAll equations with
      | none => simp [Metta.Unify.unifyRounds, hdecompose] at hrun
      | some constraints =>
          cases constraints with
          | nil =>
              simp [Metta.Unify.unifyRounds, hdecompose] at hrun
              subst result
              exact hmem
          | cons constraint rest =>
              rcases constraint with ⟨key, term⟩
              cases hoccurs : Metta.Subst.occurs key term with
              | true =>
                  simp [Metta.Unify.unifyRounds, hdecompose, hoccurs] at hrun
              | false =>
                  let remaining := rest.map fun item =>
                    (Metta.Subst.apply [(key, term)] (.var item.1),
                      Metta.Subst.apply [(key, term)] item.2)
                  have hrun' :
                      Metta.Unify.unifyRounds fuel remaining
                          (Metta.Subst.extend subst key term) = some result := by
                    simpa [Metta.Unify.unifyRounds, hdecompose, hoccurs,
                      remaining] using hrun
                  have hkeySource : key ∈ mettaEquationVars equations :=
                    decomposeAll_constraintVars_subset hdecompose key (by
                      simp [mettaConstraintVars])
                  have hkeyFresh : key ∉ mettaSubstKeys subst := by
                    intro hkey
                    exact hfresh key hkey hkeySource
                  have hfresh' :
                      UnifyStateFresh remaining
                        (Metta.Subst.extend subst key term) := by
                    simpa [remaining] using
                      (unifyRound_preserves_freshness
                        hdecompose hoccurs hfresh)
                  have hmem' :
                      binding ∈ Metta.Subst.extend subst key term := by
                    rw [substExtend_eq_cons_of_key_not_mem hkeyFresh]
                    exact List.mem_cons_of_mem _ hmem
                  exact ih hfresh' hrun' hmem'

/-- Conversely, every eliminated constraint in a successful fresh-state run
survives in the returned substitution.  Together with
`unifyRounds_result_mem_or_mem_eliminationTrace`, this identifies the returned
substitution extensionally with the incoming entries plus the elimination
trace, without imposing a list order. -/
theorem unifyRounds_eliminationTrace_mem_result
    {fuel : Nat} {equations : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {binding : String × Metta.Atom}
    (hfresh : UnifyStateFresh equations subst)
    (hrun : Metta.Unify.unifyRounds fuel equations subst = some result)
    (htrace : binding ∈ unificationEliminationTrace fuel equations) :
    binding ∈ result := by
  induction fuel generalizing equations subst result binding with
  | zero =>
      simp [unificationEliminationTrace] at htrace
  | succ fuel ih =>
      cases hdecompose : Metta.Unify.decomposeAll equations with
      | none =>
          simp [Metta.Unify.unifyRounds, hdecompose] at hrun
      | some constraints =>
          cases constraints with
          | nil =>
              simp [unificationEliminationTrace, hdecompose] at htrace
          | cons constraint rest =>
              rcases constraint with ⟨key, term⟩
              cases hoccurs : Metta.Subst.occurs key term with
              | true =>
                  simp [Metta.Unify.unifyRounds, hdecompose, hoccurs] at hrun
              | false =>
                  let remaining := rest.map fun item =>
                    (Metta.Subst.apply [(key, term)] (.var item.1),
                      Metta.Subst.apply [(key, term)] item.2)
                  have hrun' :
                      Metta.Unify.unifyRounds fuel remaining
                          (Metta.Subst.extend subst key term) = some result := by
                    simpa [Metta.Unify.unifyRounds, hdecompose, hoccurs,
                      remaining] using hrun
                  have hkeySource : key ∈ mettaEquationVars equations :=
                    decomposeAll_constraintVars_subset hdecompose key (by
                      simp [mettaConstraintVars])
                  have hkeyFresh : key ∉ mettaSubstKeys subst := by
                    intro hkey
                    exact hfresh key hkey hkeySource
                  have hfresh' :
                      UnifyStateFresh remaining
                        (Metta.Subst.extend subst key term) := by
                    simpa [remaining] using
                      (unifyRound_preserves_freshness
                        hdecompose hoccurs hfresh)
                  simp [unificationEliminationTrace, hdecompose, hoccurs]
                    at htrace
                  rcases htrace with hhead | htail
                  · have hbinding : binding = (key, term) := hhead
                    subst binding
                    apply unifyRounds_preserves_subst_mem hfresh' hrun'
                    rw [substExtend_eq_cons_of_key_not_mem hkeyFresh]
                    simp
                  · exact ih hfresh' hrun' htail

private theorem aliasConstraints_satisfied
    (valuation : String → Metta.Atom)
    {constraints : List (String × Metta.Atom)}
    (hsatisfied : MettaConstraintsSatisfied valuation constraints)
    {edge : String × String}
    (hedge : edge ∈ Metta.Unify.aliasConstraints constraints) :
    valuation edge.1 = valuation edge.2 := by
  induction constraints with
  | nil => simp [Metta.Unify.aliasConstraints] at hedge
  | cons constraint rest ih =>
      rcases constraint with ⟨key, term⟩
      have hrest : MettaConstraintsSatisfied valuation rest := by
        intro item hitem
        exact hsatisfied item (List.mem_cons_of_mem _ hitem)
      cases term with
      | var target =>
          simp only [Metta.Unify.aliasConstraints, List.mem_cons] at hedge
          rcases hedge with rfl | hedge
          · simpa [MettaConstraintsSatisfied, applyClassSolution] using
              hsatisfied (key, .var target) (by simp)
          · exact ih hrest hedge
      | sym symbol | gnd symbol | expr symbol =>
          simp only [Metta.Unify.aliasConstraints] at hedge
          exact ih hrest hedge

/-- Every alias exposed by Robinson decomposition is a semantic consequence
of the input equation system, independently of which successful elimination
order is used to normalize that system. -/
theorem aliasTrace_satisfied_of_equations
    (valuation : String → Metta.Atom) :
    ∀ (fuel : Nat) (equations : List (Metta.Atom × Metta.Atom)),
      (∀ equation ∈ equations,
        MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2) →
      MettaEquationsSatisfied valuation equations →
      ∀ edge ∈ Metta.Unify.aliasTrace fuel equations,
        valuation edge.1 = valuation edge.2 := by
  intro fuel
  induction fuel with
  | zero =>
      intro equations hnoFloat hsatisfied edge hedge
      cases hdecompose : Metta.Unify.decomposeAll equations with
      | none =>
          simp [Metta.Unify.aliasTrace, hdecompose] at hedge
      | some constraints =>
          have hconstraints :
              MettaConstraintsSatisfied valuation constraints :=
            (decomposeAll_solution_iff valuation equations constraints
              hnoFloat hdecompose).mp hsatisfied
          exact aliasConstraints_satisfied valuation hconstraints
            (by simpa [Metta.Unify.aliasTrace, hdecompose] using hedge)
  | succ fuel ih =>
      intro equations hnoFloat hsatisfied edge hedge
      cases hdecompose : Metta.Unify.decomposeAll equations with
      | none =>
          simp [Metta.Unify.aliasTrace, hdecompose] at hedge
      | some constraints =>
          cases constraints with
          | nil =>
              simp [Metta.Unify.aliasTrace, hdecompose] at hedge
          | cons constraint rest =>
              rcases constraint with ⟨key, term⟩
              have hconstraints : MettaConstraintsSatisfied valuation
                  ((key, term) :: rest) :=
                (decomposeAll_solution_iff valuation equations
                  ((key, term) :: rest) hnoFloat hdecompose).mp hsatisfied
              cases hoccurs : Metta.Subst.occurs key term with
              | true =>
                  exact aliasConstraints_satisfied valuation hconstraints
                    (by simpa [Metta.Unify.aliasTrace, hdecompose, hoccurs]
                      using hedge)
              | false =>
                  let remaining := rest.map fun item =>
                    (Metta.Subst.apply [(key, term)] (.var item.1),
                      Metta.Subst.apply [(key, term)] item.2)
                  have hsplit :
                      edge ∈ Metta.Unify.aliasConstraints
                          ((key, term) :: rest) ∨
                        edge ∈ Metta.Unify.aliasTrace fuel remaining := by
                    simpa [Metta.Unify.aliasTrace, hdecompose, hoccurs,
                      remaining] using hedge
                  rcases hsplit with hhere | htail
                  · exact aliasConstraints_satisfied valuation
                      hconstraints hhere
                  · have hhead : valuation key =
                        applyClassSolution valuation term :=
                      hconstraints (key, term) (by simp)
                    have hrest : MettaConstraintsSatisfied valuation rest :=
                      fun item hmem => hconstraints item (by simp [hmem])
                    have hremainingSatisfied :
                        MettaEquationsSatisfied valuation remaining := by
                      simpa [remaining] using
                        (eliminatedConstraints_solution_iff valuation
                          hhead rest).mpr hrest
                    have hremainingNoFloat : ∀ equation ∈ remaining,
                        MettaAtomNoFloat equation.1 ∧
                          MettaAtomNoFloat equation.2 := by
                      simpa [remaining] using
                        (unifyRound_preserves_noFloat hnoFloat hdecompose)
                    exact ih remaining hremainingNoFloat
                      hremainingSatisfied edge htail

/-- Every alias recorded during a successful Robinson run is satisfied by
every valuation satisfying the returned substitution.  The certificate is
the successful run itself, not equality of any oriented MGU presentation. -/
theorem unifyRounds_aliasTrace_satisfied
    (valuation : String → Metta.Atom)
    {fuel : Nat} {equations : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst}
    (hnoFloat : ∀ equation ∈ equations,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hfresh : UnifyStateFresh equations subst)
    (hrun : Metta.Unify.unifyRounds fuel equations subst = some result)
    (hresult : MettaConstraintsSatisfied valuation result) :
    ∀ edge ∈ Metta.Unify.aliasTrace fuel equations,
      valuation edge.1 = valuation edge.2 := by
  induction fuel generalizing equations subst result with
  | zero =>
      cases hdecompose : Metta.Unify.decomposeAll equations with
      | none => simp [Metta.Unify.unifyRounds, hdecompose] at hrun
      | some constraints =>
          cases constraints with
          | nil =>
              have htrace : Metta.Unify.aliasTrace 0 equations = [] := by
                simp [Metta.Unify.aliasTrace, Metta.Unify.aliasConstraints,
                  hdecompose]
              rw [htrace]
              simp
          | cons constraint rest =>
              simp [Metta.Unify.unifyRounds, hdecompose] at hrun
  | succ fuel ih =>
      cases hdecompose : Metta.Unify.decomposeAll equations with
      | none => simp [Metta.Unify.unifyRounds, hdecompose] at hrun
      | some constraints =>
          cases constraints with
          | nil =>
              have htrace :
                  Metta.Unify.aliasTrace (fuel + 1) equations = [] := by
                simp [Metta.Unify.aliasTrace, hdecompose]
              rw [htrace]
              simp
          | cons constraint rest =>
              rcases constraint with ⟨key, term⟩
              cases hoccurs : Metta.Subst.occurs key term with
              | true =>
                  simp [Metta.Unify.unifyRounds, hdecompose, hoccurs] at hrun
              | false =>
                  let remaining := rest.map fun item =>
                    (Metta.Subst.apply [(key, term)] (.var item.1),
                      Metta.Subst.apply [(key, term)] item.2)
                  have hrun' :
                      Metta.Unify.unifyRounds fuel remaining
                          (Metta.Subst.extend subst key term) = some result := by
                    simpa [Metta.Unify.unifyRounds, hdecompose, hoccurs,
                      remaining] using hrun
                  have hnoFloat' : ∀ equation ∈ remaining,
                      MettaAtomNoFloat equation.1 ∧
                        MettaAtomNoFloat equation.2 := by
                    simpa [remaining] using
                      (unifyRound_preserves_noFloat hnoFloat hdecompose)
                  have hfresh' :
                      UnifyStateFresh remaining
                        (Metta.Subst.extend subst key term) := by
                    simpa [remaining] using
                      (unifyRound_preserves_freshness
                        hdecompose hoccurs hfresh)
                  have htrace :
                      Metta.Unify.aliasTrace (fuel + 1) equations =
                        Metta.Unify.aliasConstraints ((key, term) :: rest) ++
                          Metta.Unify.aliasTrace fuel remaining := by
                    simp [Metta.Unify.aliasTrace, hdecompose, hoccurs,
                      remaining]
                  intro edge hedge
                  rw [htrace, List.mem_append] at hedge
                  rcases hedge with hhere | htail
                  · have hequations :
                        MettaEquationsSatisfied valuation equations :=
                      ((unifyRounds_solution_iff valuation
                        hnoFloat hfresh hrun).mp hresult).1
                    have hconstraints :
                        MettaConstraintsSatisfied valuation
                          ((key, term) :: rest) :=
                      (decomposeAll_solution_iff valuation equations
                        ((key, term) :: rest) hnoFloat hdecompose).mp
                          hequations
                    exact aliasConstraints_satisfied valuation
                      hconstraints hhere
                  · exact ih hnoFloat' hfresh' hrun' hresult edge htail

/-- Successful elimination preserves uniqueness of accumulated substitution
keys.  This is an output-normalization fact, not part of semantic equivalence. -/
theorem unifyRounds_result_keys_nodup
    {fuel : Nat} {equations : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst}
    (hkeys : (mettaSubstKeys subst).Nodup)
    (hfresh : UnifyStateFresh equations subst)
    (hunify :
      Metta.Unify.unifyRounds fuel equations subst = some result) :
    (mettaSubstKeys result).Nodup := by
  induction fuel generalizing equations subst result with
  | zero =>
      cases hdecompose : Metta.Unify.decomposeAll equations with
      | none =>
          simp [Metta.Unify.unifyRounds, hdecompose] at hunify
      | some constraints =>
          cases constraints with
          | nil =>
              simp [Metta.Unify.unifyRounds, hdecompose] at hunify
              subst result
              exact hkeys
          | cons constraint rest =>
              simp [Metta.Unify.unifyRounds, hdecompose] at hunify
  | succ fuel ih =>
      cases hdecompose : Metta.Unify.decomposeAll equations with
      | none =>
          simp [Metta.Unify.unifyRounds, hdecompose] at hunify
      | some constraints =>
          cases constraints with
          | nil =>
              simp [Metta.Unify.unifyRounds, hdecompose] at hunify
              subst result
              exact hkeys
          | cons constraint rest =>
              obtain ⟨x, term⟩ := constraint
              cases hoccurs : Metta.Subst.occurs x term with
              | true =>
                  simp [Metta.Unify.unifyRounds, hdecompose, hoccurs]
                    at hunify
              | false =>
                  let remaining := rest.map fun item =>
                    (Metta.Subst.apply [(x, term)] (.var item.1),
                      Metta.Subst.apply [(x, term)] item.2)
                  have hunify' :
                      Metta.Unify.unifyRounds fuel remaining
                          (Metta.Subst.extend subst x term) = some result := by
                    simpa [Metta.Unify.unifyRounds, hdecompose, hoccurs,
                      remaining] using hunify
                  have hxSource : x ∈ mettaEquationVars equations :=
                    decomposeAll_constraintVars_subset hdecompose x (by
                      simp [mettaConstraintVars])
                  have hxFresh : x ∉ mettaSubstKeys subst := by
                    intro hx
                    exact hfresh x hx hxSource
                  have hkeys' :
                      (mettaSubstKeys
                        (Metta.Subst.extend subst x term)).Nodup := by
                    rw [substExtend_eq_cons_of_key_not_mem hxFresh]
                    exact List.nodup_cons.mpr ⟨hxFresh, hkeys⟩
                  have hfresh' :
                      UnifyStateFresh remaining
                        (Metta.Subst.extend subst x term) := by
                    simpa [remaining] using
                      (unifyRound_preserves_freshness
                        hdecompose hoccurs hfresh)
                  exact ih hkeys' hfresh' hunify'

/-- Successful unification cannot introduce host floats when both the current
equations and accumulated substitution are host-float-free. -/
theorem unifyRounds_result_noFloat
    {fuel : Nat} {equations : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst}
    (hequations : ∀ equation ∈ equations,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hsubst : MettaSubstNoFloat subst)
    (hunify :
      Metta.Unify.unifyRounds fuel equations subst = some result) :
    MettaSubstNoFloat result := by
  induction fuel generalizing equations subst result with
  | zero =>
      cases hdecompose : Metta.Unify.decomposeAll equations with
      | none =>
          simp [Metta.Unify.unifyRounds, hdecompose] at hunify
      | some constraints =>
          cases constraints with
          | nil =>
              simp [Metta.Unify.unifyRounds, hdecompose] at hunify
              subst result
              exact hsubst
          | cons constraint rest =>
              simp [Metta.Unify.unifyRounds, hdecompose] at hunify
  | succ fuel ih =>
      cases hdecompose : Metta.Unify.decomposeAll equations with
      | none =>
          simp [Metta.Unify.unifyRounds, hdecompose] at hunify
      | some constraints =>
          cases constraints with
          | nil =>
              simp [Metta.Unify.unifyRounds, hdecompose] at hunify
              subst result
              exact hsubst
          | cons constraint rest =>
              obtain ⟨x, term⟩ := constraint
              cases hoccurs : Metta.Subst.occurs x term with
              | true =>
                  simp [Metta.Unify.unifyRounds, hdecompose, hoccurs]
                    at hunify
              | false =>
                  let remaining := rest.map fun item =>
                    (Metta.Subst.apply [(x, term)] (.var item.1),
                      Metta.Subst.apply [(x, term)] item.2)
                  have hunify' :
                      Metta.Unify.unifyRounds fuel remaining
                          (Metta.Subst.extend subst x term) = some result := by
                    simpa [Metta.Unify.unifyRounds, hdecompose, hoccurs,
                      remaining] using hunify
                  have hconstraints :=
                    decomposeAll_constraints_noFloat hequations hdecompose
                  have hterm : MettaAtomNoFloat term :=
                    hconstraints (x, term) (by simp)
                  have hequations' : ∀ equation ∈ remaining,
                      MettaAtomNoFloat equation.1 ∧
                        MettaAtomNoFloat equation.2 := by
                    simpa [remaining] using
                      (unifyRound_preserves_noFloat
                        hequations hdecompose)
                  exact ih hequations'
                    (MettaSubstNoFloat.extend hsubst hterm) hunify'

/-- A successful top-level LeaTTa unifier presents exactly the solutions of
its input equation on the HE-translatable fragment. -/
theorem unifyTop_solution_iff
    (valuation : String → Metta.Atom)
    {left right : Metta.Atom} {result : Metta.Subst}
    (hleft : MettaAtomNoFloat left)
    (hright : MettaAtomNoFloat right)
    (hunify : Metta.Unify.unifyTop left right = some result) :
    MettaConstraintsSatisfied valuation result ↔
      MettaEquationSatisfied valuation (left, right) := by
  have hrounds :
      Metta.Unify.unifyRounds (left.size + right.size)
          [(left, right)] [] = some result := by
    simpa [Metta.Unify.unifyTop] using hunify
  have htheory := unifyRounds_solution_iff valuation
    (equations := [(left, right)]) (subst := [])
    (fun equation hequation => by
      simp only [List.mem_singleton] at hequation
      subst equation
      exact ⟨hleft, hright⟩)
    (by simp [UnifyStateFresh, mettaSubstKeys]) hrounds
  simpa [MettaEquationsSatisfied, MettaConstraintsSatisfied] using htheory

/-- The equation worklist reconciled by `unifyValues`: every later class value
is equated with the first. -/
def mettaClassValueEquations : List Metta.Atom →
    List (Metta.Atom × Metta.Atom)
  | [] => []
  | first :: rest => rest.map fun value => (first, value)

/-- Successful class-value reconciliation presents exactly the valuation
solutions of the whole class-value equation worklist. -/
theorem unifyValues_solution_iff
    (valuation : String → Metta.Atom)
    {values : List Metta.Atom} {result : Metta.Subst}
    (hnoFloat : ∀ value ∈ values, MettaAtomNoFloat value)
    (hunify : Metta.Bindings.unifyValues values = some result) :
    MettaConstraintsSatisfied valuation result ↔
      MettaEquationsSatisfied valuation
        (mettaClassValueEquations values) := by
  cases values with
  | nil =>
      simp [Metta.Bindings.unifyValues] at hunify
      subst result
      simp [mettaClassValueEquations, MettaConstraintsSatisfied,
        MettaEquationsSatisfied]
  | cons first rest =>
      cases rest with
      | nil =>
          simp [Metta.Bindings.unifyValues] at hunify
          subst result
          simp [mettaClassValueEquations, MettaConstraintsSatisfied,
            MettaEquationsSatisfied]
      | cons second tail =>
          let equations :=
            (second :: tail).map fun value => (first, value)
          have hrounds :
              Metta.Unify.unifyRounds
                  (first.size +
                    ((second :: tail).map Metta.Atom.size).sum)
                  equations [] = some result := by
            simpa [Metta.Bindings.unifyValues, equations] using hunify
          have hequationNoFloat : ∀ equation ∈ equations,
              MettaAtomNoFloat equation.1 ∧
                MettaAtomNoFloat equation.2 := by
            intro equation hequation
            obtain ⟨value, hvalue, rfl⟩ := List.mem_map.mp hequation
            exact
              ⟨hnoFloat first (by simp),
                hnoFloat value (by simp [hvalue])⟩
          have htheory := unifyRounds_solution_iff valuation
            hequationNoFloat
            (by simp [UnifyStateFresh, mettaSubstKeys]) hrounds
          simpa [mettaClassValueEquations, equations,
            MettaConstraintsSatisfied] using htheory

/-- Present one repaired-LeaTTa binding relation as an atom equation. -/
abbrev leaRelationEquation : Metta.BindingRel → Metta.Atom × Metta.Atom :=
  Metta.Bindings.relationEquation

/-- The complete equation presentation of a repaired-LeaTTa binding set. -/
abbrev leaBindingEquations
    (bindings : Metta.Bindings) : List (Metta.Atom × Metta.Atom) :=
  Metta.Bindings.equations bindings

/-- Every direct value in the binding set belongs to the HE-translatable,
host-float-free fragment. -/
def LeaBindingsNoFloat (bindings : Metta.Bindings) : Prop :=
  ∀ x value,
    Metta.BindingRel.val x value ∈ bindings →
      MettaAtomNoFloat value

/-- Repaired-LeaTTa's normalized binding representation stores every
variable/variable relationship as an explicit equality edge, never as a
bare-variable value relation. -/
def LeaAssignmentsNonVariable (bindings : Metta.Bindings) : Prop :=
  ∀ key target,
    Metta.BindingRel.val key (.var target) ∉ bindings

/-- Normalized repaired-LeaTTa bindings never store a reflexive equality
edge.  Reflexive variable equations are discarded by raw equality insertion
and by the occurs-checked unifier before substitutions are replayed. -/
def LeaEqualitiesIrreflexive (bindings : Metta.Bindings) : Prop :=
  ∀ key, Metta.BindingRel.eq key key ∉ bindings

@[simp] theorem leaAssignmentsNonVariable_empty :
    LeaAssignmentsNonVariable Metta.Bindings.empty := by
  intro key target hmem
  simp [Metta.Bindings.empty] at hmem

@[simp] theorem leaEqualitiesIrreflexive_empty :
    LeaEqualitiesIrreflexive Metta.Bindings.empty := by
  intro key hmem
  simp [Metta.Bindings.empty] at hmem

/-- Raw equality insertion preserves irreflexivity because its reflexive case
is definitionally a no-op. -/
theorem LeaEqualitiesIrreflexive.addEqRaw
    {bindings : Metta.Bindings}
    (hbindings : LeaEqualitiesIrreflexive bindings)
    (left right : String) :
    LeaEqualitiesIrreflexive
      (Metta.Bindings.addEqRaw bindings left right) := by
  intro key hmem
  by_cases heq : left = right
  · subst right
    exact hbindings key (by
      simpa [Metta.Bindings.addEqRaw] using hmem)
  · have hmem' :=
      (Metta.Bindings.mem_addEqRaw_iff bindings left right heq
        (Metta.BindingRel.eq key key)).mp hmem
    simp only [List.mem_cons] at hmem'
    rcases hmem' with hnew | hold
    · cases hnew
      exact heq rfl
    · exact hbindings key hold

/-- Replacing a value relation cannot introduce an equality edge. -/
theorem LeaEqualitiesIrreflexive.addValRaw
    {bindings : Metta.Bindings}
    (hbindings : LeaEqualitiesIrreflexive bindings)
    (key : String) (value : Metta.Atom) :
    LeaEqualitiesIrreflexive
      (Metta.Bindings.addValRaw bindings key value) := by
  intro stored hmem
  simp only [Metta.Bindings.addValRaw, List.mem_cons] at hmem
  rcases hmem with hnew | hold
  · cases hnew
  · exact hbindings stored (List.mem_of_mem_filter hold)

/-- Raw equality insertion cannot introduce a variable-valued assignment. -/
theorem LeaAssignmentsNonVariable.addEqRaw
    {bindings : Metta.Bindings}
    (hbindings : LeaAssignmentsNonVariable bindings)
    (left right : String) :
    LeaAssignmentsNonVariable
      (Metta.Bindings.addEqRaw bindings left right) := by
  intro key target hmem
  exact hbindings key target
    ((Metta.Bindings.val_mem_addEqRaw_iff bindings left right key
      (.var target)).mp hmem)

/-- Raw value insertion preserves normalization when the inserted payload is
not itself a variable. -/
theorem LeaAssignmentsNonVariable.addValRaw
    {bindings : Metta.Bindings}
    (hbindings : LeaAssignmentsNonVariable bindings)
    {key : String} {value : Metta.Atom}
    (hvalue : ∀ target, value ≠ .var target) :
    LeaAssignmentsNonVariable
      (Metta.Bindings.addValRaw bindings key value) := by
  intro storedKey target hmem
  simp only [Metta.Bindings.addValRaw, List.mem_cons,
    Metta.BindingRel.val.injEq] at hmem
  rcases hmem with ⟨rfl, heq⟩ | hmem
  · exact hvalue target heq.symm
  · exact hbindings storedKey target (List.mem_of_mem_filter hmem)

/-- The equality skeleton contains no value relations at all. -/
theorem leaEqualitySkeleton_assignmentsNonVariable
    (bindings : Metta.Bindings) :
    LeaAssignmentsNonVariable
      (Metta.Bindings.equalitySkeleton bindings) := by
  induction bindings with
  | nil => exact leaAssignmentsNonVariable_empty
  | cons relation rest ih =>
      cases relation with
      | val key value =>
          simpa [Metta.Bindings.equalitySkeleton] using ih
      | eq left right =>
          intro key target hmem
          exact ih key target (by
            simpa [Metta.Bindings.equalitySkeleton] using hmem)

/-- The equality skeleton preserves every equality edge verbatim, hence
preserves irreflexivity. -/
theorem leaEqualitySkeleton_equalitiesIrreflexive
    {bindings : Metta.Bindings}
    (hbindings : LeaEqualitiesIrreflexive bindings) :
    LeaEqualitiesIrreflexive
      (Metta.Bindings.equalitySkeleton bindings) := by
  induction bindings with
  | nil => exact leaEqualitiesIrreflexive_empty
  | cons relation rest ih =>
      have hrest : LeaEqualitiesIrreflexive rest := by
        intro stored hmem
        exact hbindings stored (List.mem_cons_of_mem relation hmem)
      have ihRest := ih hrest
      cases relation with
      | val key value =>
          simpa [Metta.Bindings.equalitySkeleton] using ihRest
      | eq left right =>
          intro stored hmem
          simp only [Metta.Bindings.equalitySkeleton, List.mem_cons] at hmem
          rcases hmem with hhead | htail
          · exact hbindings stored (List.mem_cons.mpr (Or.inl hhead))
          · exact ihRest stored htail

/-- Substitution replay normalizes every variable image to an equality edge. -/
theorem leaOfSubst_assignmentsNonVariable (subst : Metta.Subst) :
    LeaAssignmentsNonVariable (Metta.Bindings.ofSubst subst) := by
  intro key target hmem
  obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hmem
  rcases entry with ⟨source, value⟩
  cases value <;> simp at heq

/-- Replaying a substitution with no `x ↦ $x` entry produces no reflexive
equality relation. -/
theorem leaOfSubst_equalitiesIrreflexive
    {subst : Metta.Subst}
    (hsubst : MettaSubstNoSelfVariable subst) :
    LeaEqualitiesIrreflexive (Metta.Bindings.ofSubst subst) := by
  intro key hmem
  obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hmem
  rcases entry with ⟨source, value⟩
  cases value with
  | var target =>
      simp only at heq
      cases heq
      exact hsubst key hentry
  | sym symbol => cases heq
  | gnd ground => cases heq
  | expr atoms => cases heq

/-- Whole-substitution reconstruction is normalized independently of the
candidate's former direct values. -/
theorem rebuildFromSubst_assignmentsNonVariable
    (candidate : Metta.Bindings) (subst : Metta.Subst) :
    LeaAssignmentsNonVariable
      (Metta.Bindings.rebuildFromSubst candidate subst) := by
  intro key target hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact leaEqualitySkeleton_assignmentsNonVariable candidate key target hmem
  · exact leaOfSubst_assignmentsNonVariable subst key target hmem

/-- Rebuilding from an irreflexive candidate and a no-self substitution
preserves equality irreflexivity. -/
theorem rebuildFromSubst_equalitiesIrreflexive
    {candidate : Metta.Bindings} {subst : Metta.Subst}
    (hcandidate : LeaEqualitiesIrreflexive candidate)
    (hsubst : MettaSubstNoSelfVariable subst) :
    LeaEqualitiesIrreflexive
      (Metta.Bindings.rebuildFromSubst candidate subst) := by
  intro key hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact leaEqualitySkeleton_equalitiesIrreflexive hcandidate key hmem
  · exact leaOfSubst_equalitiesIrreflexive hsubst key hmem

private theorem leaAssignmentsNonVariable_restoreAlias
    {bindings : Metta.Bindings}
    (hbindings : LeaAssignmentsNonVariable bindings)
    (edge : String × String) :
    LeaAssignmentsNonVariable
      (Metta.Bindings.restoreAlias bindings edge) := by
  rcases edge with ⟨left, right⟩
  unfold Metta.Bindings.restoreAlias
  split
  · exact hbindings
  · exact hbindings.addEqRaw left right

private theorem leaEqualitiesIrreflexive_restoreAlias
    {bindings : Metta.Bindings}
    (hbindings : LeaEqualitiesIrreflexive bindings)
    (edge : String × String) :
    LeaEqualitiesIrreflexive
      (Metta.Bindings.restoreAlias bindings edge) := by
  rcases edge with ⟨left, right⟩
  unfold Metta.Bindings.restoreAlias
  split
  · exact hbindings
  · exact hbindings.addEqRaw left right

private theorem leaAssignmentsNonVariable_restoreAliases
    {bindings : Metta.Bindings}
    (hbindings : LeaAssignmentsNonVariable bindings)
    (aliases : List (String × String)) :
    LeaAssignmentsNonVariable
      (aliases.foldl Metta.Bindings.restoreAlias bindings) := by
  induction aliases generalizing bindings with
  | nil => exact hbindings
  | cons edge rest ih =>
      exact ih (leaAssignmentsNonVariable_restoreAlias hbindings edge)

private theorem leaEqualitiesIrreflexive_restoreAliases
    {bindings : Metta.Bindings}
    (hbindings : LeaEqualitiesIrreflexive bindings)
    (aliases : List (String × String)) :
    LeaEqualitiesIrreflexive
      (aliases.foldl Metta.Bindings.restoreAlias bindings) := by
  induction aliases generalizing bindings with
  | nil => exact hbindings
  | cons edge rest ih =>
      exact ih (leaEqualitiesIrreflexive_restoreAlias hbindings edge)

/-- Whole-system reconciliation starts from the empty substitution, so its
successful result cannot contain a reflexive variable image. -/
theorem reconcileAll_result_noSelfVariable
    {source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {subst : Metta.Subst}
    (hreconcile : Metta.Bindings.reconcileAll source extra = some subst) :
    MettaSubstNoSelfVariable subst := by
  apply unifyRounds_result_noSelfVariable (subst := []) (by
    simp [MettaSubstNoSelfVariable])
  simpa [Metta.Bindings.reconcileAll] using hreconcile

/-- Whole-system reconciliation always returns the normalized representation:
substitution values are replayed with `ofSubst`, then only equality aliases
are restored. -/
theorem rebuildFromReconciliation_assignmentsNonVariable
    (candidate source : Metta.Bindings)
    (extra : List (Metta.Atom × Metta.Atom)) (subst : Metta.Subst) :
    LeaAssignmentsNonVariable
      (Metta.Bindings.rebuildFromReconciliation
        candidate source extra subst) := by
  apply leaAssignmentsNonVariable_restoreAliases
  exact rebuildFromSubst_assignmentsNonVariable candidate subst

/-- Whole-system reconstruction preserves equality irreflexivity.  Existing
candidate edges are retained, the successful substitution contains no self
image, and alias restoration uses the self-discarding raw equality insert. -/
theorem rebuildFromReconciliation_equalitiesIrreflexive
    {candidate source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {subst : Metta.Subst}
    (hcandidate : LeaEqualitiesIrreflexive candidate)
    (hreconcile : Metta.Bindings.reconcileAll source extra = some subst) :
    LeaEqualitiesIrreflexive
      (Metta.Bindings.rebuildFromReconciliation
        candidate source extra subst) := by
  apply leaEqualitiesIrreflexive_restoreAliases
  exact rebuildFromSubst_equalitiesIrreflexive hcandidate
    (reconcileAll_result_noSelfVariable hreconcile)

/-- Binding satisfaction is exactly satisfaction of the complete atom-equation
presentation, including explicit aliases. -/
theorem leaBindingEquations_solution_iff
    (valuation : String → Metta.Atom) (bindings : Metta.Bindings) :
    MettaEquationsSatisfied valuation (leaBindingEquations bindings) ↔
      LeaBindingSatisfied valuation bindings := by
  constructor
  · intro hall
    refine ⟨?_, ?_⟩
    · intro x value hmem
      have hequation := hall (.var x, value)
        (List.mem_map.mpr ⟨.val x value, hmem, rfl⟩)
      simpa [MettaEquationSatisfied, applyClassSolution] using hequation
    · intro x y hmem
      have hequation := hall (.var x, .var y)
        (List.mem_map.mpr ⟨.eq x y, hmem, rfl⟩)
      simpa [MettaEquationSatisfied, applyClassSolution] using hequation
  · rintro ⟨hvalues, hequalities⟩ equation hequation
    obtain ⟨relation, hrelation, rfl⟩ := List.mem_map.mp hequation
    cases relation with
    | val x value =>
        simpa [leaRelationEquation, Metta.Bindings.relationEquation,
          MettaEquationSatisfied,
          applyClassSolution] using hvalues x value hrelation
    | eq x y =>
        simpa [leaRelationEquation, Metta.Bindings.relationEquation,
          MettaEquationSatisfied,
          applyClassSolution] using hequalities x y hrelation

/-- The equation presentation of an HE-translatable binding set remains in
the host-float-free fragment. -/
theorem leaBindingEquations_noFloat
    {bindings : Metta.Bindings}
    (hnoFloat : LeaBindingsNoFloat bindings) :
    ∀ equation ∈ leaBindingEquations bindings,
      MettaAtomNoFloat equation.1 ∧
        MettaAtomNoFloat equation.2 := by
  intro equation hequation
  obtain ⟨relation, hrelation, rfl⟩ := List.mem_map.mp hequation
  cases relation with
  | val x value =>
      exact
        ⟨by simp [Metta.Bindings.relationEquation, MettaAtomNoFloat],
          hnoFloat x value hrelation⟩
  | eq x y =>
      simp [Metta.Bindings.relationEquation, MettaAtomNoFloat]

theorem mettaEquationsSatisfied_append_iff
    (valuation : String → Metta.Atom)
    (left right : List (Metta.Atom × Metta.Atom)) :
    MettaEquationsSatisfied valuation (left ++ right) ↔
      MettaEquationsSatisfied valuation left ∧
        MettaEquationsSatisfied valuation right := by
  constructor
  · intro hall
    exact
      ⟨fun equation hmem => hall equation (by simp [hmem]),
        fun equation hmem => hall equation (by simp [hmem])⟩
  · rintro ⟨hleft, hright⟩ equation hmem
    simp only [List.mem_append] at hmem
    exact hmem.elim (hleft equation) (hright equation)

/-- Structural fuel covering every atom in an equation system. -/
abbrev mettaEquationSystemFuel
    (equations : List (Metta.Atom × Metta.Atom)) : Nat :=
  Metta.Bindings.equationFuel equations

/-- Repaired Core interface: reconcile the entire existing binding equation
system together with new constraints, never merely the selected class values. -/
abbrev wholeBindingReconciliation
    (bindings : Metta.Bindings)
    (extra : List (Metta.Atom × Metta.Atom)) : Option Metta.Subst :=
  Metta.Bindings.reconcileAll bindings extra

/-- A successful whole-system result is the reverse of its elimination trace,
because reconciliation starts from the empty substitution. -/
theorem wholeBindingReconciliation_result_eq_eliminationTrace_reverse
    {bindings : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hreconcile : wholeBindingReconciliation bindings extra = some result) :
    result =
      (unificationEliminationTrace
        (Metta.Bindings.equationFuel
          (Metta.Bindings.equations bindings ++ extra))
        (Metta.Bindings.equations bindings ++ extra)).reverse := by
  have hrun :
      Metta.Unify.unifyRounds
          (Metta.Bindings.equationFuel
            (Metta.Bindings.equations bindings ++ extra))
          (Metta.Bindings.equations bindings ++ extra) [] = some result := by
    simpa [wholeBindingReconciliation, Metta.Bindings.reconcileAll] using
      hreconcile
  simpa using
    (unifyRounds_result_eq_eliminationTrace_reverse_append
      (by simp [UnifyStateFresh, mettaSubstKeys]) hrun)

/-- Whole-system reconciliation starts from the empty substitution, so every
returned binding has an eliminated-constraint witness. -/
theorem wholeBindingReconciliation_result_mem_eliminationTrace
    {bindings : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hreconcile : wholeBindingReconciliation bindings extra = some result)
    {binding : String × Metta.Atom} (hmem : binding ∈ result) :
    binding ∈ unificationEliminationTrace
      (Metta.Bindings.equationFuel
        (Metta.Bindings.equations bindings ++ extra))
      (Metta.Bindings.equations bindings ++ extra) := by
  have hrun :
      Metta.Unify.unifyRounds
          (Metta.Bindings.equationFuel
            (Metta.Bindings.equations bindings ++ extra))
          (Metta.Bindings.equations bindings ++ extra) [] = some result := by
    simpa [wholeBindingReconciliation, Metta.Bindings.reconcileAll] using
      hreconcile
  rcases unifyRounds_result_mem_or_mem_eliminationTrace hrun hmem with
    h | h
  · simp at h
  · exact h

/-- Exact set-level characterization of a successful whole-system result:
its entries are precisely the constraints selected by Robinson elimination.
Only list order is quotiented. -/
theorem wholeBindingReconciliation_result_mem_iff_eliminationTrace
    {bindings : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hreconcile : wholeBindingReconciliation bindings extra = some result)
    {binding : String × Metta.Atom} :
    binding ∈ result ↔
      binding ∈ unificationEliminationTrace
        (Metta.Bindings.equationFuel
          (Metta.Bindings.equations bindings ++ extra))
        (Metta.Bindings.equations bindings ++ extra) := by
  constructor
  · exact wholeBindingReconciliation_result_mem_eliminationTrace hreconcile
  · intro htrace
    have hrun :
        Metta.Unify.unifyRounds
            (Metta.Bindings.equationFuel
              (Metta.Bindings.equations bindings ++ extra))
            (Metta.Bindings.equations bindings ++ extra) [] = some result := by
      simpa [wholeBindingReconciliation, Metta.Bindings.reconcileAll] using
        hreconcile
    exact unifyRounds_eliminationTrace_mem_result
      (by simp [UnifyStateFresh, mettaSubstKeys]) hrun htrace

/-- Singleton substitution can only retain variables from the source atom or
introduce variables from the replacement. -/
private theorem mem_vars_apply_singleton
    {key : String} {replacement : Metta.Atom} :
    ∀ (atom : Metta.Atom) {name : String},
      name ∈ (Metta.Subst.apply [(key, replacement)] atom).vars →
        name ∈ atom.vars ∨ name ∈ replacement.vars := by
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_
  · intro symbol name hmem
    simp [Metta.Subst.apply, Metta.Atom.vars] at hmem
  · intro sourceVar name hmem
    by_cases hvariable : sourceVar = key
    · subst sourceVar
      exact Or.inr (by
        simpa [Metta.Subst.apply, Metta.Subst.lookup] using hmem)
    · have hbeq : (sourceVar == key) = false := by simp [hvariable]
      left
      simpa [Metta.Subst.apply, Metta.Subst.lookup, hbeq,
        Metta.Atom.vars] using hmem
  · intro ground name hmem
    simp [Metta.Subst.apply, Metta.Atom.vars] at hmem
  · intro atoms ih name hmem
    simp only [Metta.Subst.apply, Metta.Atom.vars,
      List.mem_flatten] at hmem
    obtain ⟨appliedVars, happliedVars, hname⟩ := hmem
    obtain ⟨applied, happlied, rfl⟩ := List.mem_map.mp happliedVars
    obtain ⟨atom, hatom, rfl⟩ := List.mem_map.mp happlied
    rcases ih atom hatom hname with hsource | hreplacement
    · left
      simp only [Metta.Atom.vars, List.mem_flatten]
      exact ⟨atom.vars, List.mem_map.mpr ⟨atom, hatom, rfl⟩,
        hsource⟩
    · exact Or.inr hreplacement

/-- The substituted worklist of one Robinson round mentions only variables
already present in the decomposed source worklist. -/
private theorem remainingEquationVars_subset_source
    {equations : List (Metta.Atom × Metta.Atom)}
    {key : String} {term : Metta.Atom}
    {rest : List (String × Metta.Atom)}
    (hdecompose :
      Metta.Unify.decomposeAll equations = some ((key, term) :: rest)) :
    let remaining := rest.map fun constraint =>
      (Metta.Subst.apply [(key, term)] (.var constraint.1),
        Metta.Subst.apply [(key, term)] constraint.2)
    ∀ name ∈ mettaEquationVars remaining,
      name ∈ mettaEquationVars equations := by
  dsimp only
  intro name hname
  simp only [mettaEquationVars, List.mem_flatMap] at hname
  obtain ⟨equation, hequation, hname⟩ := hname
  obtain ⟨constraint, hconstraint, rfl⟩ := List.mem_map.mp hequation
  have htermSource : ∀ sourceVar ∈ term.vars,
      sourceVar ∈ mettaEquationVars equations := by
    intro sourceVar hvariable
    apply decomposeAll_constraintVars_subset hdecompose sourceVar
    simp [mettaConstraintVars, hvariable]
  have hconstraintSource :
      ∀ sourceVar ∈ constraint.1 :: constraint.2.vars,
        sourceVar ∈ mettaEquationVars equations := by
    intro sourceVar hvariable
    apply decomposeAll_constraintVars_subset hdecompose sourceVar
    unfold mettaConstraintVars
    apply List.mem_flatMap.mpr
    exact ⟨constraint, by simp [hconstraint], hvariable⟩
  simp only [List.mem_append] at hname
  rcases hname with hleft | hright
  · rcases mem_vars_apply_singleton (.var constraint.1) hleft with
      hsource | hreplacement
    · have hnameEq : name = constraint.1 := by
        simpa [Metta.Atom.vars] using hsource
      exact hconstraintSource name (by simp [hnameEq])
    · exact htermSource name hreplacement
  · rcases mem_vars_apply_singleton constraint.2 hright with
      hsource | hreplacement
    · exact hconstraintSource name (List.mem_cons.mpr (Or.inr hsource))
    · exact htermSource name hreplacement

/-- Every variable occurring in the selected solve trace came from the
worklist on which that trace started. -/
theorem unificationEliminationTrace_constraintVars_subset
    (fuel : Nat) (equations : List (Metta.Atom × Metta.Atom)) :
    ∀ name ∈ mettaConstraintVars
        (unificationEliminationTrace fuel equations),
      name ∈ mettaEquationVars equations := by
  induction fuel generalizing equations with
  | zero => simp [unificationEliminationTrace, mettaConstraintVars]
  | succ fuel ih =>
      cases hdecompose : Metta.Unify.decomposeAll equations with
      | none =>
          simp [unificationEliminationTrace, hdecompose,
            mettaConstraintVars]
      | some constraints =>
          cases constraints with
          | nil =>
              simp [unificationEliminationTrace, hdecompose,
                mettaConstraintVars]
          | cons constraint rest =>
              rcases constraint with ⟨key, term⟩
              cases hoccurs : Metta.Subst.occurs key term with
              | true =>
                  simp [unificationEliminationTrace, hdecompose, hoccurs,
                    mettaConstraintVars]
              | false =>
                  let remaining := rest.map fun constraint =>
                    (Metta.Subst.apply [(key, term)] (.var constraint.1),
                      Metta.Subst.apply [(key, term)] constraint.2)
                  simp only [unificationEliminationTrace, hdecompose,
                    hoccurs]
                  intro name hname
                  change name ∈
                    (key :: term.vars) ++
                      mettaConstraintVars
                        (unificationEliminationTrace fuel remaining) at hname
                  rw [List.mem_append] at hname
                  rcases hname with hhead | htail
                  · apply decomposeAll_constraintVars_subset hdecompose name
                    simp only [mettaConstraintVars, List.flatMap_cons,
                      List.mem_append]
                    exact Or.inl hhead
                  · apply remainingEquationVars_subset_source hdecompose name
                    exact ih remaining name htail

/-- A solve trace is triangular when each eliminated key is absent from every
later key and term.  This is an operational invariant of the successful
Robinson loop, not a representative-order convention. -/
def EliminationTraceTriangular :
    List (String × Metta.Atom) → Prop
  | [] => True
  | binding :: trace =>
      binding.1 ∉ mettaConstraintVars trace ∧
        EliminationTraceTriangular trace

/-- Triangularity is inherited by every left prefix. -/
theorem EliminationTraceTriangular.left_of_append
    {frontTrace suffix : List (String × Metta.Atom)}
    (h : EliminationTraceTriangular (frontTrace ++ suffix)) :
    EliminationTraceTriangular frontTrace := by
  induction frontTrace with
  | nil => simp [EliminationTraceTriangular]
  | cons binding frontTrace ih =>
      simp only [List.cons_append, EliminationTraceTriangular] at h ⊢
      refine ⟨?_, ih h.2⟩
      intro hmem
      apply h.1
      simpa [mettaConstraintVars] using
        (List.mem_append_left (mettaConstraintVars suffix) hmem)

/-- A triangular trace has distinct eliminated keys. -/
theorem EliminationTraceTriangular.keys_nodup
    {trace : List (String × Metta.Atom)}
    (h : EliminationTraceTriangular trace) :
    (trace.map Prod.fst).Nodup := by
  induction trace with
  | nil => simp
  | cons binding trace ih =>
      simp only [EliminationTraceTriangular] at h
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih h.2⟩
      intro hkey
      obtain ⟨tailBinding, htail, heq⟩ := List.mem_map.mp hkey
      apply h.1
      unfold mettaConstraintVars
      apply List.mem_flatMap.mpr
      exact ⟨tailBinding, htail, by simp [heq]⟩

/-- Every successful fresh-state Robinson run produces a triangular solve
trace.  In particular, replaying the trace from tail to head always introduces
an isolated key. -/
theorem unificationEliminationTrace_triangular_of_success
    {fuel : Nat} {equations : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst}
    (hfresh : UnifyStateFresh equations subst)
    (hrun : Metta.Unify.unifyRounds fuel equations subst = some result) :
    EliminationTraceTriangular
      (unificationEliminationTrace fuel equations) := by
  induction fuel generalizing equations subst result with
  | zero =>
      simp [unificationEliminationTrace, EliminationTraceTriangular]
  | succ fuel ih =>
      cases hdecompose : Metta.Unify.decomposeAll equations with
      | none =>
          simp [Metta.Unify.unifyRounds, hdecompose] at hrun
      | some constraints =>
          cases constraints with
          | nil =>
              simp [unificationEliminationTrace, hdecompose,
                EliminationTraceTriangular]
          | cons constraint rest =>
              rcases constraint with ⟨key, term⟩
              cases hoccurs : Metta.Subst.occurs key term with
              | true =>
                  simp [Metta.Unify.unifyRounds, hdecompose, hoccurs] at hrun
              | false =>
                  let remaining := rest.map fun constraint =>
                    (Metta.Subst.apply [(key, term)] (.var constraint.1),
                      Metta.Subst.apply [(key, term)] constraint.2)
                  have hrun' :
                      Metta.Unify.unifyRounds fuel remaining
                          (Metta.Subst.extend subst key term) = some result := by
                    simpa [Metta.Unify.unifyRounds, hdecompose, hoccurs,
                      remaining] using hrun
                  have hfresh' :
                      UnifyStateFresh remaining
                        (Metta.Subst.extend subst key term) := by
                    simpa [remaining] using
                      (unifyRound_preserves_freshness
                        hdecompose hoccurs hfresh)
                  have hkeyRecorded :
                      key ∈ mettaSubstKeys
                        (Metta.Subst.extend subst key term) := by
                    simp [Metta.Subst.extend, mettaSubstKeys]
                  have hkeyAbsent : key ∉
                      mettaConstraintVars
                        (unificationEliminationTrace fuel remaining) := by
                    intro hkey
                    exact hfresh' key hkeyRecorded
                      (unificationEliminationTrace_constraintVars_subset
                        fuel remaining key hkey)
                  have htraceEq :
                      unificationEliminationTrace (fuel + 1) equations =
                        (key, term) ::
                          unificationEliminationTrace fuel remaining := by
                    simp [unificationEliminationTrace, hdecompose, hoccurs,
                      remaining]
                  rw [htraceEq]
                  simp only [EliminationTraceTriangular]
                  exact ⟨hkeyAbsent, ih hfresh' hrun'⟩

/-- Whole-binding reconciliation inherits triangularity because it runs the
Robinson loop from the empty substitution. -/
theorem wholeBindingReconciliation_eliminationTrace_triangular
    {bindings : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hreconcile : wholeBindingReconciliation bindings extra = some result) :
    EliminationTraceTriangular
      (unificationEliminationTrace
        (Metta.Bindings.equationFuel
          (Metta.Bindings.equations bindings ++ extra))
        (Metta.Bindings.equations bindings ++ extra)) := by
  have hrun :
      Metta.Unify.unifyRounds
          (Metta.Bindings.equationFuel
            (Metta.Bindings.equations bindings ++ extra))
          (Metta.Bindings.equations bindings ++ extra) [] = some result := by
    simpa [wholeBindingReconciliation, Metta.Bindings.reconcileAll] using
      hreconcile
  exact unificationEliminationTrace_triangular_of_success
    (by simp [UnifyStateFresh, mettaSubstKeys]) hrun

/-- Every selected elimination key passes the occurs check against its own
term.  Unlike triangularity, this fact needs no successful final run: a failed
occurs check contributes no trace entry. -/
theorem unificationEliminationTrace_key_not_mem_value_vars
    (fuel : Nat) (equations : List (Metta.Atom × Metta.Atom)) :
    ∀ key value,
      (key, value) ∈ unificationEliminationTrace fuel equations →
        key ∉ value.vars := by
  induction fuel generalizing equations with
  | zero =>
      simp [unificationEliminationTrace]
  | succ fuel ih =>
      cases hdecompose : Metta.Unify.decomposeAll equations with
      | none => simp [unificationEliminationTrace, hdecompose]
      | some constraints =>
          cases constraints with
          | nil => simp [unificationEliminationTrace, hdecompose]
          | cons constraint rest =>
              rcases constraint with ⟨selectedKey, selectedValue⟩
              cases hoccurs : Metta.Subst.occurs selectedKey selectedValue with
              | true =>
                  simp [unificationEliminationTrace, hdecompose, hoccurs]
              | false =>
                  let remaining := rest.map fun constraint =>
                    (Metta.Subst.apply [(selectedKey, selectedValue)]
                        (.var constraint.1),
                      Metta.Subst.apply [(selectedKey, selectedValue)]
                        constraint.2)
                  have htraceEq :
                      unificationEliminationTrace (fuel + 1) equations =
                        (selectedKey, selectedValue) ::
                          unificationEliminationTrace fuel remaining := by
                    simp [unificationEliminationTrace, hdecompose, hoccurs,
                      remaining]
                  intro key value hmem
                  rw [htraceEq] at hmem
                  simp only [List.mem_cons, Prod.mk.injEq] at hmem
                  rcases hmem with hhead | htail
                  · rcases hhead with ⟨rfl, rfl⟩
                    exact not_mem_vars_of_occurs_eq_false _ _ hoccurs
                  · exact ih remaining key value htail

/-- Updating a valuation outside an atom's variable support leaves that
atom's solution image unchanged. -/
private theorem applyClassSolution_update_of_not_mem_vars
    (valuation : String → Metta.Atom) (key : String)
    (replacement : Metta.Atom) :
    ∀ atom : Metta.Atom, key ∉ atom.vars →
      applyClassSolution (Function.update valuation key replacement) atom =
        applyClassSolution valuation atom := by
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_
  · intro name hnot
    simp [applyClassSolution]
  · intro name hnot
    have hne : name ≠ key := by
      intro heq
      subst name
      exact hnot (by simp [Metta.Atom.vars])
    simp [applyClassSolution, Function.update, hne]
  · intro ground hnot
    simp [applyClassSolution]
  · intro atoms ih hnot
    simp only [applyClassSolution]
    apply congrArg Metta.Atom.expr
    apply List.map_congr_left
    intro atom hatom
    apply ih atom hatom
    intro hkey
    apply hnot
    simp only [Metta.Atom.vars, List.mem_flatten]
    exact ⟨atom.vars,
      List.mem_map.mpr ⟨atom, hatom, rfl⟩, hkey⟩

/-- A concrete valuation for a triangular elimination trace.  Tail constraints
are interpreted first; the selected key is then assigned the interpreted head
term. -/
def eliminationTraceValuation :
    List (String × Metta.Atom) → String → Metta.Atom
  | [] => fun name => .var name
  | (key, value) :: trace =>
      let tailValuation := eliminationTraceValuation trace
      Function.update tailValuation key
        (applyClassSolution tailValuation value)

private theorem not_mem_constraintVars_of_mem
    {trace : List (String × Metta.Atom)} {key : String}
    {constraint : String × Metta.Atom}
    (hfresh : key ∉ mettaConstraintVars trace)
    (hmem : constraint ∈ trace) :
    key ≠ constraint.1 ∧ key ∉ constraint.2.vars := by
  constructor
  · intro heq
    apply hfresh
    unfold mettaConstraintVars
    apply List.mem_flatMap.mpr
    exact ⟨constraint, hmem, by simp [heq]⟩
  · intro hkey
    apply hfresh
    unfold mettaConstraintVars
    apply List.mem_flatMap.mpr
    exact ⟨constraint, hmem, by simp [hkey]⟩

/-- The recursively constructed valuation satisfies every triangular,
occurs-check-clean solve trace. -/
theorem eliminationTraceValuation_satisfies
    (trace : List (String × Metta.Atom))
    (htriangular : EliminationTraceTriangular trace)
    (hoccurs : ∀ key value, (key, value) ∈ trace → key ∉ value.vars) :
    MettaConstraintsSatisfied (eliminationTraceValuation trace) trace := by
  induction trace with
  | nil =>
      simp [MettaConstraintsSatisfied]
  | cons binding trace ih =>
      rcases binding with ⟨key, value⟩
      have htriangular' :
          key ∉ mettaConstraintVars trace ∧
            EliminationTraceTriangular trace := by
        simpa [EliminationTraceTriangular] using htriangular
      have hoccursHead : key ∉ value.vars :=
        hoccurs key value (by simp)
      have hoccursTail : ∀ tailKey tailValue,
          (tailKey, tailValue) ∈ trace → tailKey ∉ tailValue.vars := by
        intro tailKey tailValue hmem
        exact hoccurs tailKey tailValue (by simp [hmem])
      have htail := ih htriangular'.2 hoccursTail
      intro constraint hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with hhead | htailMem
      · subst constraint
        change
          Function.update (eliminationTraceValuation trace) key
              (applyClassSolution (eliminationTraceValuation trace) value) key =
            applyClassSolution
              (Function.update (eliminationTraceValuation trace) key
                (applyClassSolution (eliminationTraceValuation trace) value))
              value
        rw [applyClassSolution_update_of_not_mem_vars
          _ _ _ value hoccursHead]
        simp
      · obtain ⟨hkeyNe, hvalueFresh⟩ :=
          not_mem_constraintVars_of_mem htriangular'.1 htailMem
        have hkeyNe' : constraint.1 ≠ key := Ne.symm hkeyNe
        change
          Function.update (eliminationTraceValuation trace) key
              (applyClassSolution (eliminationTraceValuation trace) value)
              constraint.1 =
            applyClassSolution
              (Function.update (eliminationTraceValuation trace) key
                (applyClassSolution (eliminationTraceValuation trace) value))
              constraint.2
        rw [applyClassSolution_update_of_not_mem_vars
          _ _ _ constraint.2 hvalueFresh]
        simpa [Function.update, hkeyNe'] using htail constraint htailMem

/-- A successful float-free Robinson run constructs a concrete satisfying
valuation for its complete input equation worklist. -/
theorem exists_unifyRounds_equations_satisfied_of_noFloat
    {fuel : Nat} {equations : List (Metta.Atom × Metta.Atom)}
    {result : Metta.Subst}
    (hnoFloat : ∀ equation ∈ equations,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hrun : Metta.Unify.unifyRounds fuel equations [] = some result) :
    ∃ valuation : String → Metta.Atom,
      MettaEquationsSatisfied valuation equations := by
  let trace := unificationEliminationTrace fuel equations
  let valuation := eliminationTraceValuation trace
  have hfresh : UnifyStateFresh equations [] := by
    simp [UnifyStateFresh, mettaSubstKeys]
  have htraceSatisfied : MettaConstraintsSatisfied valuation trace :=
    eliminationTraceValuation_satisfies trace
      (by simpa [trace] using
        unificationEliminationTrace_triangular_of_success hfresh hrun)
      (by intro key value hmem
          exact unificationEliminationTrace_key_not_mem_value_vars _ _
            key value (by simpa [trace] using hmem))
  have hresultEq : result = trace.reverse := by
    simpa [trace] using
      (unifyRounds_result_eq_eliminationTrace_reverse_append hfresh hrun)
  have hresultSatisfied : MettaConstraintsSatisfied valuation result := by
    simpa [hresultEq, MettaConstraintsSatisfied] using htraceSatisfied
  exact ⟨valuation,
    ((unifyRounds_solution_iff valuation hnoFloat hfresh hrun).mp hresultSatisfied).1⟩

/-- A successful whole-binding reconciliation presents exactly the conjunction
of all pre-existing binding constraints and all requested new equations. -/
theorem wholeBindingReconciliation_solution_iff
    (valuation : String → Metta.Atom)
    {bindings : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hbindingsNoFloat : LeaBindingsNoFloat bindings)
    (hextraNoFloat : ∀ equation ∈ extra,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hreconcile :
      wholeBindingReconciliation bindings extra = some result) :
    MettaConstraintsSatisfied valuation result ↔
      LeaBindingSatisfied valuation bindings ∧
        MettaEquationsSatisfied valuation extra := by
  let equations := leaBindingEquations bindings ++ extra
  have hnoFloat : ∀ equation ∈ equations,
      MettaAtomNoFloat equation.1 ∧
        MettaAtomNoFloat equation.2 := by
    intro equation hequation
    simp only [equations, List.mem_append] at hequation
    exact hequation.elim
      (leaBindingEquations_noFloat hbindingsNoFloat equation)
      (hextraNoFloat equation)
  have hrun :
      Metta.Unify.unifyRounds
          (mettaEquationSystemFuel equations) equations [] = some result := by
    simpa [wholeBindingReconciliation, Metta.Bindings.reconcileAll,
      Metta.Bindings.equations, Metta.Bindings.equationFuel, equations] using
        hreconcile
  have htheory := unifyRounds_solution_iff valuation hnoFloat
    (by simp [UnifyStateFresh, mettaSubstKeys]) hrun
  calc
    MettaConstraintsSatisfied valuation result ↔
        MettaEquationsSatisfied valuation equations ∧
          MettaConstraintsSatisfied valuation [] := htheory
    _ ↔ MettaEquationsSatisfied valuation equations := by
      simp [MettaConstraintsSatisfied]
    _ ↔ MettaEquationsSatisfied valuation (leaBindingEquations bindings) ∧
          MettaEquationsSatisfied valuation extra := by
      simpa [equations] using
        mettaEquationsSatisfied_append_iff valuation
          (leaBindingEquations bindings) extra
    _ ↔ LeaBindingSatisfied valuation bindings ∧
          MettaEquationsSatisfied valuation extra :=
      and_congr
        (leaBindingEquations_solution_iff valuation bindings) Iff.rfl

/-- Whole-system reconciliation returns a normalized substitution with no
duplicate keys. -/
theorem wholeBindingReconciliation_result_keys_nodup
    {bindings : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hreconcile :
      wholeBindingReconciliation bindings extra = some result) :
    (mettaSubstKeys result).Nodup := by
  let equations := leaBindingEquations bindings ++ extra
  have hrun :
      Metta.Unify.unifyRounds
          (mettaEquationSystemFuel equations) equations [] = some result := by
    simpa [wholeBindingReconciliation, Metta.Bindings.reconcileAll,
      Metta.Bindings.equations, Metta.Bindings.equationFuel, equations] using
        hreconcile
  exact unifyRounds_result_keys_nodup
    (by simp [mettaSubstKeys])
    (by simp [UnifyStateFresh, mettaSubstKeys]) hrun

/-- Whole-system reconciliation remains inside the HE-translatable fragment. -/
theorem wholeBindingReconciliation_result_noFloat
    {bindings : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hbindingsNoFloat : LeaBindingsNoFloat bindings)
    (hextraNoFloat : ∀ equation ∈ extra,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hreconcile :
      wholeBindingReconciliation bindings extra = some result) :
    MettaSubstNoFloat result := by
  let equations := leaBindingEquations bindings ++ extra
  have hnoFloat : ∀ equation ∈ equations,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2 := by
    intro equation hequation
    simp only [equations, List.mem_append] at hequation
    exact hequation.elim
      (leaBindingEquations_noFloat hbindingsNoFloat equation)
      (hextraNoFloat equation)
  have hrun :
      Metta.Unify.unifyRounds
          (mettaEquationSystemFuel equations) equations [] = some result := by
    simpa [wholeBindingReconciliation, Metta.Bindings.reconcileAll,
      Metta.Bindings.equations, Metta.Bindings.equationFuel, equations] using
        hreconcile
  exact unifyRounds_result_noFloat hnoFloat
    (by simp [MettaSubstNoFloat]) hrun

/-- A successful whole-system reconciliation semantically certifies every
variable alias exposed anywhere in its structural decomposition trace. -/
theorem wholeBindingReconciliation_aliases_satisfied
    (valuation : String → Metta.Atom)
    {bindings : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hbindingsNoFloat : LeaBindingsNoFloat bindings)
    (hextraNoFloat : ∀ equation ∈ extra,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hreconcile :
      wholeBindingReconciliation bindings extra = some result)
    (hresult : MettaConstraintsSatisfied valuation result) :
    ∀ edge ∈ Metta.Bindings.reconciliationAliases bindings extra result,
      valuation edge.1 = valuation edge.2 := by
  have htheory : LeaBindingSatisfied valuation bindings ∧
      MettaEquationsSatisfied valuation extra :=
    (wholeBindingReconciliation_solution_iff valuation
      hbindingsNoFloat hextraNoFloat hreconcile).mp hresult
  have hbindingsSatisfied : MettaEquationsSatisfied valuation
      (leaBindingEquations bindings) :=
    (leaBindingEquations_solution_iff valuation bindings).mpr htheory.1
  have hprimarySatisfied : MettaEquationsSatisfied valuation
      (leaBindingEquations bindings ++ extra) :=
    (mettaEquationsSatisfied_append_iff valuation
      (leaBindingEquations bindings) extra).mpr
        ⟨hbindingsSatisfied, htheory.2⟩
  have hcollisionSatisfied : MettaEquationsSatisfied valuation
      (extra ++ leaBindingEquations bindings) :=
    (mettaEquationsSatisfied_append_iff valuation extra
      (leaBindingEquations bindings)).mpr
        ⟨htheory.2, hbindingsSatisfied⟩
  have hprimaryNoFloat : ∀ equation ∈
      (leaBindingEquations bindings ++ extra),
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2 := by
    intro equation hequation
    simp only [List.mem_append] at hequation
    exact hequation.elim
      (leaBindingEquations_noFloat hbindingsNoFloat equation)
      (hextraNoFloat equation)
  have hcollisionNoFloat : ∀ equation ∈
      (extra ++ leaBindingEquations bindings),
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2 := by
    intro equation hequation
    simp only [List.mem_append] at hequation
    exact hequation.elim
      (hextraNoFloat equation)
      (leaBindingEquations_noFloat hbindingsNoFloat equation)
  intro edge hedge
  simp only [Metta.Bindings.reconciliationAliases,
    List.mem_append] at hedge
  rcases hedge with hprimary | hcollision
  · exact aliasTrace_satisfied_of_equations valuation _ _
      hprimaryNoFloat hprimarySatisfied edge
      (by simpa [Metta.Bindings.equations] using hprimary)
  · exact aliasTrace_satisfied_of_equations valuation _ _
      hcollisionNoFloat hcollisionSatisfied edge
      (by simpa [Metta.Bindings.equations] using hcollision)

/-- Every variable-valued entry in a successful whole-system substitution is
already represented by its successful alias trace.  Thus rebuilding from both
the substitution and the trace cannot introduce an unaccounted class edge. -/
theorem wholeBindingReconciliation_result_alias_mem
    {bindings : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    {left right : String}
    (hreconcile :
      wholeBindingReconciliation bindings extra = some result)
    (hmem : (left, Metta.Atom.var right) ∈ result) :
    (left, right) ∈
      Metta.Bindings.reconciliationAliases bindings extra result := by
  let equations := leaBindingEquations bindings ++ extra
  have hrun :
      Metta.Unify.unifyRounds
          (mettaEquationSystemFuel equations) equations [] = some result := by
    simpa [wholeBindingReconciliation, Metta.Bindings.reconcileAll,
      Metta.Bindings.equations, Metta.Bindings.equationFuel, equations] using
        hreconcile
  have halias :=
    Metta.Unify.varBinding_mem_aliasTrace_of_unifyRounds_empty hrun hmem
  simp only [Metta.Bindings.reconciliationAliases, List.mem_append]
  left
  simpa [Metta.Bindings.equations,
    Metta.Bindings.equationFuel, equations] using halias

/-- Turning a unifier into explicit binding relations preserves its atom
equation presentation exactly, including variable/variable aliases. -/
theorem leaBindingEquations_ofSubst (subst : Metta.Subst) :
    leaBindingEquations (Metta.Bindings.ofSubst subst) =
      subst.map fun binding => (.var binding.1, binding.2) := by
  unfold leaBindingEquations Metta.Bindings.equations Metta.Bindings.ofSubst
  rw [List.map_map]
  apply List.map_congr_left
  intro binding _
  rcases binding with ⟨x, value⟩
  cases value <;> rfl

theorem mettaSubstEquations_solution_iff
    (valuation : String → Metta.Atom) (subst : Metta.Subst) :
    MettaEquationsSatisfied valuation
        (subst.map fun binding => (.var binding.1, binding.2)) ↔
      MettaConstraintsSatisfied valuation subst := by
  constructor
  · intro hall binding hbinding
    have hequation := hall (.var binding.1, binding.2)
      (List.mem_map.mpr ⟨binding, hbinding, rfl⟩)
    simpa [MettaEquationSatisfied, applyClassSolution] using hequation
  · intro hall equation hequation
    obtain ⟨binding, hbinding, rfl⟩ := List.mem_map.mp hequation
    simpa [MettaEquationSatisfied, applyClassSolution] using
      hall binding hbinding

/-- `ofSubst` is a semantics-preserving change of presentation, not a claim
that another engine must return the same substitution list. -/
theorem leaOfSubst_solution_iff
    (valuation : String → Metta.Atom) (subst : Metta.Subst) :
    LeaBindingSatisfied valuation (Metta.Bindings.ofSubst subst) ↔
      MettaConstraintsSatisfied valuation subst := by
  rw [← leaBindingEquations_solution_iff,
    leaBindingEquations_ofSubst]
  exact mettaSubstEquations_solution_iff valuation subst

/-- Retain the explicit equality graph while discarding direct value
presentations that a successful whole-system unifier will normalize. -/
abbrev leaEqualitySkeleton : Metta.Bindings → Metta.Bindings :=
  Metta.Bindings.equalitySkeleton

@[simp] theorem val_not_mem_leaEqualitySkeleton
    {bindings : Metta.Bindings} {x : String} {value : Metta.Atom} :
    Metta.BindingRel.val x value ∉ leaEqualitySkeleton bindings := by
  induction bindings with
  | nil => simp [leaEqualitySkeleton, Metta.Bindings.equalitySkeleton]
  | cons relation rest ih =>
      cases relation <;>
        simp [leaEqualitySkeleton, Metta.Bindings.equalitySkeleton, ih]

@[simp] theorem eq_mem_leaEqualitySkeleton_iff
    {bindings : Metta.Bindings} {x y : String} :
    Metta.BindingRel.eq x y ∈ leaEqualitySkeleton bindings ↔
      Metta.BindingRel.eq x y ∈ bindings := by
  induction bindings with
  | nil => simp [leaEqualitySkeleton, Metta.Bindings.equalitySkeleton]
  | cons relation rest ih =>
      cases relation <;>
        simp [leaEqualitySkeleton, Metta.Bindings.equalitySkeleton, ih]

@[simp] theorem leaEqualityEdges_leaEqualitySkeleton
    (bindings : Metta.Bindings) :
    leaEqualityEdges (leaEqualitySkeleton bindings) =
      leaEqualityEdges bindings := by
  induction bindings with
  | nil => rfl
  | cons relation rest ih =>
      cases relation <;>
        simp [leaEqualitySkeleton, Metta.Bindings.equalitySkeleton,
          leaEqualityEdges, ih]

theorem leaEqualitySkeleton_noFloat (bindings : Metta.Bindings) :
    LeaBindingsNoFloat (leaEqualitySkeleton bindings) := by
  intro x value hmem
  exact (val_not_mem_leaEqualitySkeleton
    (bindings := bindings) hmem).elim

theorem leaBindingsNoFloat_append
    {left right : Metta.Bindings}
    (hleft : LeaBindingsNoFloat left)
    (hright : LeaBindingsNoFloat right) :
    LeaBindingsNoFloat (left ++ right) := by
  intro x value hmem
  simp only [List.mem_append] at hmem
  exact hmem.elim (hleft x value) (hright x value)

theorem leaOfSubst_noFloat
    {subst : Metta.Subst} (hsubst : MettaSubstNoFloat subst) :
    LeaBindingsNoFloat (Metta.Bindings.ofSubst subst) := by
  intro x value hmem
  unfold Metta.Bindings.ofSubst at hmem
  obtain ⟨binding, hbinding, hrelation⟩ := List.mem_map.mp hmem
  rcases binding with ⟨key, target⟩
  cases target with
  | var y => simp at hrelation
  | sym symbol | gnd symbol | expr symbol =>
      simp at hrelation
      rcases hrelation with ⟨rfl, rfl⟩
      exact hsubst key _ hbinding

theorem leaBindingSatisfied_append_iff
    (valuation : String → Metta.Atom)
    (left right : Metta.Bindings) :
    LeaBindingSatisfied valuation (left ++ right) ↔
      LeaBindingSatisfied valuation left ∧
        LeaBindingSatisfied valuation right := by
  constructor
  · rintro ⟨hvalues, hequalities⟩
    constructor
    · exact
        ⟨fun x value hmem => hvalues x value (by simp [hmem]),
          fun x y hmem => hequalities x y (by simp [hmem])⟩
    · exact
        ⟨fun x value hmem => hvalues x value (by simp [hmem]),
          fun x y hmem => hequalities x y (by simp [hmem])⟩
  · rintro
      ⟨⟨hleftValues, hleftEqualities⟩,
        ⟨hrightValues, hrightEqualities⟩⟩
    refine ⟨?_, ?_⟩
    · intro x value hmem
      simp only [List.mem_append] at hmem
      exact hmem.elim
        (hleftValues x value) (hrightValues x value)
    · intro x y hmem
      simp only [List.mem_append] at hmem
      exact hmem.elim
        (hleftEqualities x y) (hrightEqualities x y)

theorem leaEqualitySkeleton_satisfied
    (valuation : String → Metta.Atom) {bindings : Metta.Bindings}
    (h : LeaBindingSatisfied valuation bindings) :
    LeaBindingSatisfied valuation (leaEqualitySkeleton bindings) := by
  rcases h with ⟨hvalues, hequalities⟩
  refine ⟨?_, ?_⟩
  · intro x value hmem
    exact (val_not_mem_leaEqualitySkeleton
      (bindings := bindings) hmem).elim
  · intro x y hmem
    exact hequalities x y (eq_mem_leaEqualitySkeleton_iff.mp hmem)

/-- Normalized reconciliation core: retain the equality skeleton and replace
all direct values by the complete-system unifier presentation.  The executable
repair subsequently restores certified aliases with
`rebuildFromReconciliation`. -/
abbrev rebuildBindingsFromUnifier
    (bindings : Metta.Bindings) (subst : Metta.Subst) : Metta.Bindings :=
  Metta.Bindings.rebuildFromSubst bindings subst

theorem leaEqualityEdges_rebuildBindingsFromUnifier
    (bindings : Metta.Bindings) (subst : Metta.Subst) :
    leaEqualityEdges (rebuildBindingsFromUnifier bindings subst) =
      leaEqualityEdges bindings ++
        leaEqualityEdges (Metta.Bindings.ofSubst subst) := by
  have happend : ∀ left right : Metta.Bindings,
      leaEqualityEdges (left ++ right) =
        leaEqualityEdges left ++ leaEqualityEdges right := by
    intro left
    induction left with
    | nil => simp [leaEqualityEdges]
    | cons relation rest ih =>
        intro right
        cases relation <;> simp [leaEqualityEdges, ih]
  rw [rebuildBindingsFromUnifier, Metta.Bindings.rebuildFromSubst, happend,
    leaEqualityEdges_leaEqualitySkeleton]

private theorem leaEqClass_mono_of_edge_subset
    {left right : Metta.Bindings}
    (hsubset : ∀ edge ∈ leaEqualityEdges left,
      edge ∈ leaEqualityEdges right) {start finish : String}
    (hclass : finish ∈ Metta.Bindings.eqClass left start) :
    finish ∈ Metta.Bindings.eqClass right start := by
  rw [mem_leaEqClass_iff_reachable] at hclass ⊢
  apply hclass.mono
  intro x y hadj
  rw [EqualityClosure.edgeGraph_adj_iff] at hadj ⊢
  rcases hadj with ⟨hne, hedge | hedge⟩
  · exact ⟨hne, Or.inl (hsubset (x, y) hedge)⟩
  · exact ⟨hne, Or.inr (hsubset (y, x) hedge)⟩

private theorem leaEqualityEdges_restoreAlias_subset
    (bindings : Metta.Bindings) (edge : String × String) :
    ∀ oldEdge ∈ leaEqualityEdges bindings,
      oldEdge ∈ leaEqualityEdges
        (Metta.Bindings.restoreAlias bindings edge) := by
  intro oldEdge hold
  rcases edge with ⟨left, right⟩
  unfold Metta.Bindings.restoreAlias
  split
  · exact hold
  · exact leaEqualityEdges_addEqRaw_old bindings left right hold

private theorem leaEqClass_mono_restoreAlias
    (bindings : Metta.Bindings) (edge : String × String)
    {start finish : String}
    (hclass : finish ∈ Metta.Bindings.eqClass bindings start) :
    finish ∈ Metta.Bindings.eqClass
      (Metta.Bindings.restoreAlias bindings edge) start :=
  leaEqClass_mono_of_edge_subset
    (leaEqualityEdges_restoreAlias_subset bindings edge) hclass

private theorem leaEqClass_mono_restoreAliases
    (aliases : List (String × String)) (bindings : Metta.Bindings)
    {start finish : String}
    (hclass : finish ∈ Metta.Bindings.eqClass bindings start) :
    finish ∈ Metta.Bindings.eqClass
      (aliases.foldl Metta.Bindings.restoreAlias bindings) start := by
  induction aliases generalizing bindings with
  | nil => exact hclass
  | cons edge rest ih =>
      exact ih (bindings := Metta.Bindings.restoreAlias bindings edge)
        (leaEqClass_mono_restoreAlias bindings edge hclass)

private theorem restoreAlias_connects_edge
    (bindings : Metta.Bindings) (edge : String × String) :
    edge.2 ∈ Metta.Bindings.eqClass
      (Metta.Bindings.restoreAlias bindings edge) edge.1 := by
  rcases edge with ⟨left, right⟩
  unfold Metta.Bindings.restoreAlias
  split <;> rename_i hconnected
  · simpa using hconnected
  · by_cases heq : left = right
    · subst right
      rw [mem_leaEqClass_iff_reachable]
    · rw [mem_leaEqClass_iff_reachable]
      apply SimpleGraph.Adj.reachable
      rw [EqualityClosure.edgeGraph_adj_iff]
      exact ⟨heq, Or.inl (leaEqualityEdges_addEqRaw_new bindings heq)⟩

private theorem restoreAliases_connects_mem
    (aliases : List (String × String)) (bindings : Metta.Bindings)
    {edge : String × String} (hedge : edge ∈ aliases) :
    edge.2 ∈ Metta.Bindings.eqClass
      (aliases.foldl Metta.Bindings.restoreAlias bindings) edge.1 := by
  induction aliases generalizing bindings with
  | nil => simp at hedge
  | cons head rest ih =>
      simp only [List.mem_cons] at hedge
      rcases hedge with rfl | hedge
      · exact leaEqClass_mono_restoreAliases rest
          (Metta.Bindings.restoreAlias bindings edge)
          (restoreAlias_connects_edge bindings edge)
      · exact ih (bindings := Metta.Bindings.restoreAlias bindings head) hedge

/-- Reconciliation never loses a class connection already explicit in the
candidate binding graph.  Normalized substitution edges and restored aliases
may extend that graph but cannot shrink its closure. -/
theorem rebuildFromReconciliation_preserves_class
    (candidate source : Metta.Bindings)
    (extra : List (Metta.Atom × Metta.Atom)) (subst : Metta.Subst)
    {start finish : String}
    (hclass : finish ∈ Metta.Bindings.eqClass candidate start) :
    finish ∈ Metta.Bindings.eqClass
      (Metta.Bindings.rebuildFromReconciliation
        candidate source extra subst) start := by
  have hcore : finish ∈ Metta.Bindings.eqClass
      (rebuildBindingsFromUnifier candidate subst) start := by
    apply leaEqClass_mono_of_edge_subset (hclass := hclass)
    intro edge hedge
    rw [leaEqualityEdges_rebuildBindingsFromUnifier]
    exact List.mem_append_left _ hedge
  exact leaEqClass_mono_restoreAliases
    (Metta.Bindings.reconciliationAliases source extra subst)
    (rebuildBindingsFromUnifier candidate subst) hcore

/-- Every alias certified by reconciliation is connected in the executable
rebuild output, regardless of whether it was represented by a new direct edge
or was already reachable through the candidate graph. -/
theorem rebuildFromReconciliation_connects_alias
    (candidate source : Metta.Bindings)
    (extra : List (Metta.Atom × Metta.Atom)) (subst : Metta.Subst)
    {edge : String × String}
    (hedge : edge ∈
      Metta.Bindings.reconciliationAliases source extra subst) :
    edge.2 ∈ Metta.Bindings.eqClass
      (Metta.Bindings.rebuildFromReconciliation
        candidate source extra subst) edge.1 := by
  exact restoreAliases_connects_mem
    (Metta.Bindings.reconciliationAliases source extra subst)
    (rebuildBindingsFromUnifier candidate subst) hedge

private theorem leaEqualityEdges_restoreAlias_subset_union
    (bindings : Metta.Bindings) (aliasEdge : String × String)
    {edge : String × String}
    (hmem : edge ∈ leaEqualityEdges
      (Metta.Bindings.restoreAlias bindings aliasEdge)) :
    edge ∈ leaEqualityEdges bindings ∨ edge = aliasEdge := by
  rcases aliasEdge with ⟨left, right⟩
  rcases edge with ⟨x, y⟩
  unfold Metta.Bindings.restoreAlias at hmem
  split at hmem
  · exact Or.inl hmem
  · by_cases heq : left = right
    · subst right
      exact Or.inl (by
        simpa [Metta.Bindings.addEqRaw] using hmem)
    · rcases (mem_leaEqualityEdges_addEqRaw_iff bindings heq).mp hmem with
        ⟨rfl, rfl⟩ | hold
      · exact Or.inr rfl
      · exact Or.inl hold

private theorem leaEqualityEdges_restoreAliases_subset_union
    (aliases : List (String × String)) (bindings : Metta.Bindings)
    {edge : String × String}
    (hmem : edge ∈ leaEqualityEdges
      (aliases.foldl Metta.Bindings.restoreAlias bindings)) :
    edge ∈ leaEqualityEdges bindings ∨ edge ∈ aliases := by
  induction aliases generalizing bindings with
  | nil => exact Or.inl hmem
  | cons aliasEdge rest ih =>
      simp only [List.foldl_cons] at hmem
      rcases ih (bindings := Metta.Bindings.restoreAlias bindings aliasEdge)
          hmem with hhead | hrest
      · rcases leaEqualityEdges_restoreAlias_subset_union
          bindings aliasEdge hhead with hold | rfl
        · exact Or.inl hold
        · exact Or.inr (by simp)
      · exact Or.inr (by simp [hrest])

private theorem leaEqualityEdges_ofSubst_mem_imp_subst_var_mem
    {subst : Metta.Subst} {left right : String}
    (hmem : (left, right) ∈
      leaEqualityEdges (Metta.Bindings.ofSubst subst)) :
    (left, Metta.Atom.var right) ∈ subst := by
  have hrelation :
      Metta.BindingRel.eq left right ∈ Metta.Bindings.ofSubst subst :=
    mem_leaEqualityEdges_iff.mp hmem
  unfold Metta.Bindings.ofSubst at hrelation
  obtain ⟨binding, hbinding, hmapped⟩ := List.mem_map.mp hrelation
  rcases binding with ⟨key, value⟩
  cases value <;> simp_all

/-- Every explicit equality edge in an executable reconciliation rebuild comes
from either the candidate graph or the successful alias trace.  Together with
the two connection lemmas above, this is the exact graph-level quotient
interface for reconciliation. -/
theorem rebuildFromReconciliation_edge_source
    {candidate source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {subst : Metta.Subst}
    (hreconcile : wholeBindingReconciliation source extra = some subst)
    {edge : String × String}
    (hmem : edge ∈ leaEqualityEdges
      (Metta.Bindings.rebuildFromReconciliation
        candidate source extra subst)) :
    edge ∈ leaEqualityEdges candidate ∨
      edge ∈ Metta.Bindings.reconciliationAliases source extra subst := by
  let aliases := Metta.Bindings.reconciliationAliases source extra subst
  have hsplit := leaEqualityEdges_restoreAliases_subset_union
    aliases (rebuildBindingsFromUnifier candidate subst) (by
      simpa [Metta.Bindings.rebuildFromReconciliation, aliases] using hmem)
  rcases hsplit with hcore | halias
  · rw [leaEqualityEdges_rebuildBindingsFromUnifier] at hcore
    rcases List.mem_append.mp hcore with hcandidate | hsubst
    · exact Or.inl hcandidate
    · exact Or.inr
        (wholeBindingReconciliation_result_alias_mem hreconcile
          (leaEqualityEdges_ofSubst_mem_imp_subst_var_mem hsubst))
  · exact Or.inr halias

/-- Restoring one certified alias changes only the equality presentation; it
neither creates nor removes a direct value relation. -/
@[simp] theorem val_mem_restoreAlias_iff
    {bindings : Metta.Bindings} {edge : String × String}
    {key : String} {value : Metta.Atom} :
    Metta.BindingRel.val key value ∈
        Metta.Bindings.restoreAlias bindings edge ↔
      Metta.BindingRel.val key value ∈ bindings := by
  rcases edge with ⟨left, right⟩
  unfold Metta.Bindings.restoreAlias
  split
  · rfl
  · exact Metta.Bindings.val_mem_addEqRaw_iff
      bindings left right key value

/-- A fold of alias restorations is likewise inert on direct values. -/
theorem val_mem_restoreAliases_iff
    (aliases : List (String × String)) (bindings : Metta.Bindings)
    {key : String} {value : Metta.Atom} :
    Metta.BindingRel.val key value ∈
        aliases.foldl Metta.Bindings.restoreAlias bindings ↔
      Metta.BindingRel.val key value ∈ bindings := by
  induction aliases generalizing bindings with
  | nil => rfl
  | cons edge rest ih =>
      rw [List.foldl_cons, ih (Metta.Bindings.restoreAlias bindings edge),
        val_mem_restoreAlias_iff]

/-- A substitution contributes a direct value exactly for one of its
non-variable entries. Variable entries are represented as explicit aliases. -/
theorem val_mem_ofSubst_iff
    {subst : Metta.Subst} {key : String} {value : Metta.Atom} :
    Metta.BindingRel.val key value ∈ Metta.Bindings.ofSubst subst ↔
      (key, value) ∈ subst ∧ ∀ target, value ≠ .var target := by
  constructor
  · intro hmem
    unfold Metta.Bindings.ofSubst at hmem
    obtain ⟨binding, hbinding, hmapped⟩ := List.mem_map.mp hmem
    rcases binding with ⟨source, term⟩
    cases term with
    | var target => simp at hmapped
    | sym name | gnd name | expr name =>
        simp at hmapped
        rcases hmapped with ⟨rfl, rfl⟩
        exact ⟨hbinding, by intro target h; cases h⟩
  · rintro ⟨hmem, hnonvar⟩
    unfold Metta.Bindings.ofSubst
    apply List.mem_map.mpr
    refine ⟨(key, value), hmem, ?_⟩
    cases value with
    | var target => exact (hnonvar target rfl).elim
    | sym name | gnd name | expr name => rfl

/-- Exact raw-value interface for executable whole-system reconciliation.
Candidate values are intentionally replaced by the successful normalized
substitution; subsequent alias restoration affects only equality closure. -/
theorem val_mem_rebuildFromReconciliation_iff
    {candidate source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {subst : Metta.Subst}
    {key : String} {value : Metta.Atom} :
    Metta.BindingRel.val key value ∈
        Metta.Bindings.rebuildFromReconciliation
          candidate source extra subst ↔
      (key, value) ∈ subst ∧ ∀ target, value ≠ .var target := by
  rw [Metta.Bindings.rebuildFromReconciliation,
    val_mem_restoreAliases_iff]
  simp only [Metta.Bindings.rebuildFromSubst, List.mem_append,
    val_not_mem_leaEqualitySkeleton, false_or]
  exact val_mem_ofSubst_iff

/-! ## Variable support of reconciliation and native merge -/

theorem aliasConstraints_endpoint_support
    (constraints : List (String × Metta.Atom))
    {edge : String × String}
    (member : edge ∈ Metta.Unify.aliasConstraints constraints) :
    edge.1 ∈ mettaConstraintVars constraints ∧
      edge.2 ∈ mettaConstraintVars constraints := by
  induction constraints with
  | nil => simp [Metta.Unify.aliasConstraints] at member
  | cons constraint rest ih =>
      rcases constraint with ⟨key, value⟩
      cases value with
      | var other =>
          simp only [Metta.Unify.aliasConstraints, List.mem_cons] at member
          rcases member with rfl | tail
          · simp [mettaConstraintVars, Metta.Atom.vars]
          · obtain ⟨left, right⟩ := ih tail
            constructor
            · exact List.mem_append_right _ left
            · exact List.mem_append_right _ right
      | sym symbol | gnd value | expr children =>
          have tail : edge ∈ Metta.Unify.aliasConstraints rest := member
          obtain ⟨left, right⟩ := ih tail
          constructor
          · exact List.mem_append_right _ left
          · exact List.mem_append_right _ right

theorem aliasTrace_endpoint_support
    (fuel : Nat) (equations : List (Metta.Atom × Metta.Atom))
    {edge : String × String}
    (member : edge ∈ Metta.Unify.aliasTrace fuel equations) :
    edge.1 ∈ mettaEquationVars equations ∧
      edge.2 ∈ mettaEquationVars equations := by
  induction fuel generalizing equations with
  | zero =>
      cases decomposed : Metta.Unify.decomposeAll equations with
      | none => simp [Metta.Unify.aliasTrace, decomposed] at member
      | some constraints =>
          obtain ⟨left, right⟩ := aliasConstraints_endpoint_support constraints
            (by simpa [Metta.Unify.aliasTrace, decomposed] using member)
          exact ⟨decomposeAll_constraintVars_subset decomposed _ left,
            decomposeAll_constraintVars_subset decomposed _ right⟩
  | succ fuel ih =>
      cases decomposed : Metta.Unify.decomposeAll equations with
      | none => simp [Metta.Unify.aliasTrace, decomposed] at member
      | some constraints =>
          cases constraints with
          | nil => simp [Metta.Unify.aliasTrace, decomposed] at member
          | cons constraint rest =>
              rcases constraint with ⟨key, value⟩
              have here (h : edge ∈ Metta.Unify.aliasConstraints ((key, value) :: rest)) :
                  edge.1 ∈ mettaEquationVars equations ∧
                    edge.2 ∈ mettaEquationVars equations := by
                obtain ⟨left, right⟩ := aliasConstraints_endpoint_support _ h
                exact ⟨decomposeAll_constraintVars_subset decomposed _ left,
                  decomposeAll_constraintVars_subset decomposed _ right⟩
              by_cases occurs : Metta.Subst.occurs key value = true
              · exact here (by simpa [Metta.Unify.aliasTrace, decomposed, occurs] using member)
              · simp only [Metta.Unify.aliasTrace, decomposed, occurs, Bool.false_eq_true,
                  ↓reduceIte, List.mem_append] at member
                rcases member with current | later
                · exact here current
                · obtain ⟨left, right⟩ := ih _ later
                  exact ⟨remainingEquationVars_subset_source decomposed _ left,
                    remainingEquationVars_subset_source decomposed _ right⟩

theorem mettaEquationVars_bindings_equations
    (bindings : Metta.Bindings) (name : String) :
    name ∈ mettaEquationVars (Metta.Bindings.equations bindings) ↔
      name ∈ bindings.vars := by
  simp only [mettaEquationVars, Metta.Bindings.equations,
    Metta.Bindings.vars, List.mem_eraseDups, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨equation, ⟨relation, present, rfl⟩, mentioned⟩
    refine ⟨relation, present, ?_⟩
    cases relation <;>
      simpa [Metta.Bindings.relationEquation, Metta.Atom.vars] using mentioned
  · rintro ⟨relation, present, mentioned⟩
    refine ⟨Metta.Bindings.relationEquation relation, ⟨relation, present, rfl⟩, ?_⟩
    cases relation <;>
      simpa [Metta.Bindings.relationEquation, Metta.Atom.vars] using mentioned

theorem wholeBindingReconciliation_constraint_support
    {bindings : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (reconciled : wholeBindingReconciliation bindings extra = some result)
    {name : String} (member : name ∈ mettaConstraintVars result) :
    name ∈ bindings.vars ∨ name ∈ mettaEquationVars extra := by
  obtain ⟨constraint, present, mentioned⟩ := List.mem_flatMap.mp member
  have trace := wholeBindingReconciliation_result_mem_eliminationTrace reconciled present
  have source := unificationEliminationTrace_constraintVars_subset _ _ name
    (List.mem_flatMap.mpr ⟨constraint, trace, mentioned⟩)
  simpa only [mettaEquationVars, List.flatMap_append, List.mem_append,
    ← mettaEquationVars_bindings_equations] using source

theorem reconciliationAliases_endpoint_support
    (bindings : Metta.Bindings)
    (extra : List (Metta.Atom × Metta.Atom)) (result : Metta.Subst)
    {edge : String × String}
    (member : edge ∈ Metta.Bindings.reconciliationAliases bindings extra result) :
    (edge.1 ∈ bindings.vars ∨ edge.1 ∈ mettaEquationVars extra) ∧
      (edge.2 ∈ bindings.vars ∨ edge.2 ∈ mettaEquationVars extra) := by
  simp only [Metta.Bindings.reconciliationAliases, List.mem_append] at member
  rcases member with primary | collision
  · obtain ⟨left, right⟩ := aliasTrace_endpoint_support _ _ primary
    constructor
    · simpa only [mettaEquationVars, List.flatMap_append, List.mem_append,
        ← mettaEquationVars_bindings_equations] using left
    · simpa only [mettaEquationVars, List.flatMap_append, List.mem_append,
        ← mettaEquationVars_bindings_equations] using right
  · obtain ⟨left, right⟩ := aliasTrace_endpoint_support _ _ collision
    constructor
    · simpa only [mettaEquationVars, List.flatMap_append, List.mem_append,
        ← mettaEquationVars_bindings_equations, or_comm] using left
    · simpa only [mettaEquationVars, List.flatMap_append, List.mem_append,
        ← mettaEquationVars_bindings_equations, or_comm] using right



theorem bindingRelation_vars_subset {bindings : Metta.Bindings}
    {relation : Metta.BindingRel} (present : relation ∈ bindings)
    {name : String} (mentioned : name ∈ Metta.Bindings.vars [relation]) :
    name ∈ bindings.vars := by
  simp only [Metta.Bindings.vars, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_eraseDups] at mentioned
  simp only [Metta.Bindings.vars, List.mem_eraseDups, List.mem_flatMap]
  exact ⟨relation, present, mentioned⟩

theorem bindings_vars_append_iff (left right : Metta.Bindings) (name : String) :
    name ∈ Metta.Bindings.vars (left ++ right) ↔
      name ∈ left.vars ∨ name ∈ right.vars := by
  simp only [Metta.Bindings.vars, List.flatMap_append, List.mem_eraseDups,
    List.mem_append]

theorem rebuildFromReconciliation_vars_subset
    {candidate source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (reconciled : wholeBindingReconciliation source extra = some result)
    {name : String}
    (member : name ∈ Metta.Bindings.vars
      (Metta.Bindings.rebuildFromReconciliation candidate source extra result)) :
    name ∈ candidate.vars ∨ name ∈ source.vars ∨ name ∈ mettaEquationVars extra := by
  simp only [Metta.Bindings.vars, List.mem_eraseDups, List.mem_flatMap] at member
  obtain ⟨relation, present, mentioned⟩ := member
  cases relation with
  | val key value =>
      obtain ⟨entry, _⟩ := val_mem_rebuildFromReconciliation_iff.mp present
      apply Or.inr
      apply wholeBindingReconciliation_constraint_support reconciled
      apply List.mem_flatMap.mpr
      exact ⟨(key, value), entry, mentioned⟩
  | eq left right =>
      have edge := rebuildFromReconciliation_edge_source reconciled
        (mem_leaEqualityEdges_iff.mpr present)
      rcases edge with old | added
      · exact Or.inl (bindingRelation_vars_subset
          (mem_leaEqualityEdges_iff.mp old)
          (by simpa [Metta.Bindings.vars] using mentioned))
      · obtain ⟨hleft, hright⟩ := reconciliationAliases_endpoint_support source extra result added
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mentioned
        rcases mentioned with rfl | rfl
        · exact Or.inr hleft
        · exact Or.inr hright

theorem addEqRaw_vars_subset (bindings : Metta.Bindings) (left right : String)
    {name : String} (member : name ∈ (Metta.Bindings.addEqRaw bindings left right).vars) :
    name ∈ bindings.vars ∨ name = left ∨ name = right := by
  unfold Metta.Bindings.addEqRaw at member
  split at member
  · exact Or.inl member
  · split at member
    · exact Or.inl member
    · simp only [Metta.Bindings.vars, List.flatMap_cons, List.mem_eraseDups,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with head | tail
      · exact Or.inr head
      · exact Or.inl (by
          simpa only [Metta.Bindings.vars, List.mem_eraseDups] using tail)

theorem addValRaw_vars_subset (bindings : Metta.Bindings) (key : String) (value : Metta.Atom)
    {name : String} (member : name ∈ (Metta.Bindings.addValRaw bindings key value).vars) :
    name ∈ bindings.vars ∨ name = key ∨ name ∈ value.vars := by
  simp only [Metta.Bindings.addValRaw, Metta.Bindings.vars, List.flatMap_cons,
    List.mem_eraseDups, List.mem_append] at member
  rcases member with head | tail
  · exact Or.inr (by simpa using head)
  · simp only [List.mem_flatMap] at tail
    obtain ⟨relation, present, mentioned⟩ := tail
    exact Or.inl (bindingRelation_vars_subset
      (List.mem_of_mem_filter present) (by simpa [Metta.Bindings.vars] using mentioned))

theorem addVarEquality_vars_subset
    {bindings result : Metta.Bindings} {left right name : String}
    (produced : result ∈ Metta.Bindings.addVarEquality bindings left right)
    (member : name ∈ result.vars) :
    name ∈ bindings.vars ∨ name = left ∨ name = right := by
  cases unified : Metta.Bindings.unifyValues
      ((Metta.Bindings.addEqRaw bindings left right).classValues left) with
  | none => simp [Metta.Bindings.addVarEquality, unified] at produced
  | some subst =>
    cases subst with
    | nil =>
        simp only [Metta.Bindings.addVarEquality, unified, List.mem_singleton] at produced
        subst result
        exact addEqRaw_vars_subset bindings left right member
    | cons entry rest =>
        cases reconciled : Metta.Bindings.reconcileAll bindings
            [(.var left, .var right)] with
        | none => simp [Metta.Bindings.addVarEquality, unified, reconciled] at produced
        | some solution =>
          simp only [Metta.Bindings.addVarEquality, unified, reconciled,
            List.mem_singleton] at produced
          subst result
          have supported := rebuildFromReconciliation_vars_subset reconciled member
          rcases supported with candidate | source | extra
          · exact addEqRaw_vars_subset bindings left right candidate
          · exact Or.inl source
          · exact Or.inr (by simpa [mettaEquationVars, Metta.Atom.vars] using extra)

private theorem addVarBinding_nonvariable_vars_subset
    {bindings result : Metta.Bindings} {key name : String} {value : Metta.Atom}
    (nonvariable : ∀ other, value ≠ .var other)
    (produced : result ∈ Metta.Bindings.addVarBinding bindings key value)
    (member : name ∈ result.vars) :
    name ∈ bindings.vars ∨ name = key ∨ name ∈ value.vars := by
  have expanded : Metta.Bindings.addVarBinding bindings key value =
      match bindings.classValues key with
      | [] => [Metta.Bindings.addValRaw bindings key value]
      | first :: others =>
          match Metta.Bindings.unifyValues (first :: (others ++ [value])) with
          | none => []
          | some [] => [bindings]
          | some (_ :: _) =>
              match Metta.Bindings.reconcileAll bindings [(.var key, value)] with
              | none => []
              | some solution =>
                  [Metta.Bindings.rebuildFromReconciliation bindings bindings
                    [(.var key, value)] solution] := by
    cases value with
    | var other => exact (nonvariable other rfl).elim
    | sym symbol | gnd ground | expr children =>
        cases hvalues : bindings.classValues key <;>
          simp [Metta.Bindings.addVarBinding, hvalues]
        all_goals rfl
  rw [expanded] at produced
  cases values : bindings.classValues key with
  | nil =>
      simp only [values, List.mem_singleton] at produced
      subst result
      exact addValRaw_vars_subset _ _ _ member
  | cons first others =>
    simp only [values] at produced
    cases unified : Metta.Bindings.unifyValues (first :: (others ++ [value])) with
    | none => simp [unified] at produced
    | some subst =>
      cases subst with
      | nil =>
          simp only [unified, List.mem_singleton] at produced
          subst result
          exact Or.inl member
      | cons entry rest =>
          simp only [unified] at produced
          cases reconciled : Metta.Bindings.reconcileAll bindings [(.var key, value)] with
          | none => simp [reconciled] at produced
          | some solution =>
            simp only [reconciled, List.mem_singleton] at produced
            subst result
            have supported := rebuildFromReconciliation_vars_subset reconciled member
            rcases supported with source | source | extra
            · exact Or.inl source
            · exact Or.inl source
            · exact Or.inr (by simpa [mettaEquationVars, Metta.Atom.vars] using extra)

theorem addVarBinding_vars_subset
    {bindings result : Metta.Bindings} {key name : String} {value : Metta.Atom}
    (produced : result ∈ Metta.Bindings.addVarBinding bindings key value)
    (member : name ∈ result.vars) :
    name ∈ bindings.vars ∨ name = key ∨ name ∈ value.vars := by
  cases value with
  | var other =>
      simpa [Metta.Atom.vars] using addVarEquality_vars_subset produced member
  | sym symbol | gnd ground | expr children =>
      exact addVarBinding_nonvariable_vars_subset (by intro other h; cases h) produced member


theorem mergeOne_vars_subset
    {frontier : List Metta.Bindings} {relation : Metta.BindingRel}
    {result : Metta.Bindings} {name : String}
    (produced : result ∈ Metta.Bindings.mergeOne frontier relation)
    (member : name ∈ result.vars) :
    ∃ previous ∈ frontier,
      name ∈ previous.vars ∨ name ∈ Metta.Bindings.vars [relation] := by
  obtain ⟨previous, present, advanced⟩ := List.mem_flatMap.mp produced
  refine ⟨previous, present, ?_⟩
  cases relation with
  | val key value =>
      simpa [Metta.Bindings.vars] using addVarBinding_vars_subset advanced member
  | eq left right =>
      simpa [Metta.Bindings.vars] using addVarEquality_vars_subset advanced member

private theorem merge_fold_vars_subset
    (relations : Metta.Bindings) (frontier : List Metta.Bindings)
    {result : Metta.Bindings} {name : String}
    (produced : result ∈ relations.foldl Metta.Bindings.mergeOne frontier)
    (member : name ∈ result.vars) :
    (∃ previous ∈ frontier, name ∈ previous.vars) ∨ name ∈ relations.vars := by
  induction relations generalizing frontier with
  | nil => exact Or.inl ⟨result, produced, member⟩
  | cons relation rest ih =>
      rcases ih _ produced with prior | remaining
      · obtain ⟨previous, present, mentioned⟩ := prior
        obtain ⟨initial, initialPresent, fromInitial | fromRelation⟩ :=
          mergeOne_vars_subset present mentioned
        · exact Or.inl ⟨initial, initialPresent, fromInitial⟩
        · exact Or.inr (bindingRelation_vars_subset (by simp) fromRelation)
      · exact Or.inr (by
          simpa only [show relation :: rest = [relation] ++ rest from rfl,
            bindings_vars_append_iff] using Or.inr remaining)

/-- Native merge can retain or remove variable names, but cannot invent one.
This includes compound-value reconciliation and restored equality aliases. -/
theorem merge_vars_subset
    {left right result : Metta.Bindings} {name : String}
    (produced : result ∈ Metta.Bindings.merge left right)
    (member : name ∈ result.vars) :
    name ∈ left.vars ∨ name ∈ right.vars := by
  rcases merge_fold_vars_subset right [left] produced member with initial | right
  · obtain ⟨previous, present, mentioned⟩ := initial
    simp only [List.mem_singleton] at present
    subst previous
    exact Or.inl mentioned
  · exact Or.inr right

theorem merge_preserves_outside
    {left right result : Metta.Bindings} {name : String}
    (produced : result ∈ Metta.Bindings.merge left right)
    (outsideLeft : name ∉ left.vars) (outsideRight : name ∉ right.vars) :
    name ∉ result.vars := by
  intro member
  exact (merge_vars_subset produced member).elim outsideLeft outsideRight


theorem rebuildBindingsFromUnifier_noFloat
    {bindings : Metta.Bindings} {subst : Metta.Subst}
    (hsubst : MettaSubstNoFloat subst) :
    LeaBindingsNoFloat (rebuildBindingsFromUnifier bindings subst) := by
  exact leaBindingsNoFloat_append
    (leaEqualitySkeleton_noFloat bindings)
    (leaOfSubst_noFloat hsubst)

/-- Rebuilding from a successful whole-system unifier preserves exactly the
old binding theory conjoined with the requested equations. -/
theorem rebuildBindingsFromUnifier_solution_iff
    (valuation : String → Metta.Atom)
    {bindings : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hbindingsNoFloat : LeaBindingsNoFloat bindings)
    (hextraNoFloat : ∀ equation ∈ extra,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hreconcile :
      wholeBindingReconciliation bindings extra = some result) :
    LeaBindingSatisfied valuation
        (rebuildBindingsFromUnifier bindings result) ↔
      LeaBindingSatisfied valuation bindings ∧
        MettaEquationsSatisfied valuation extra := by
  have hwhole := wholeBindingReconciliation_solution_iff valuation
    hbindingsNoFloat hextraNoFloat hreconcile
  constructor
  · intro hout
    have hparts :=
      (leaBindingSatisfied_append_iff valuation
        (leaEqualitySkeleton bindings)
        (Metta.Bindings.ofSubst result)).mp (by
          simpa [rebuildBindingsFromUnifier,
            Metta.Bindings.rebuildFromSubst] using hout)
    exact hwhole.mp ((leaOfSubst_solution_iff valuation result).mp hparts.2)
  · intro hinput
    have hrebuilt :=
      (leaBindingSatisfied_append_iff valuation
        (leaEqualitySkeleton bindings)
        (Metta.Bindings.ofSubst result)).mpr
          ⟨leaEqualitySkeleton_satisfied valuation hinput.1,
            (leaOfSubst_solution_iff valuation result).mpr
              (hwhole.mpr hinput)⟩
    simpa [rebuildBindingsFromUnifier,
      Metta.Bindings.rebuildFromSubst] using hrebuilt

/-- Raw alias insertion presents exactly the old binding equations conjoined
with the requested variable equality. -/
theorem leaBindingSatisfied_addEqRaw_iff
    (valuation : String → Metta.Atom)
    (bindings : Metta.Bindings) (left right : String) :
    LeaBindingSatisfied valuation
        (Metta.Bindings.addEqRaw bindings left right) ↔
      LeaBindingSatisfied valuation bindings ∧
        valuation left = valuation right := by
  constructor
  · rintro ⟨hvalues, hequalities⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro x value present
      exact hvalues x value
        (Metta.Bindings.mem_addEqRaw_of_mem bindings left right present)
    · intro x y present
      exact hequalities x y
        (Metta.Bindings.mem_addEqRaw_of_mem bindings left right present)
    · by_cases different : left = right
      · exact congrArg valuation different
      · exact hequalities left right
          (Metta.Bindings.eq_mem_addEqRaw bindings left right different)
  · rintro ⟨hold, requested⟩
    refine ⟨?_, ?_⟩
    · intro x value present
      exact hold.1 x value
        ((Metta.Bindings.val_mem_addEqRaw_iff bindings left right x value).mp present)
    · intro x y present
      by_cases different : left = right
      · subst right
        exact hold.2 x y (by
          simpa [Metta.Bindings.addEqRaw] using present)
      · have split := (Metta.Bindings.mem_addEqRaw_iff
          bindings left right different (Metta.BindingRel.eq x y)).mp present
        rcases List.mem_cons.mp split with added | old
        · cases added
          exact requested
        · exact hold.2 x y old

private theorem mettaSubst_lookup_some_mem
    {subst : Metta.Subst} {x : String} {term : Metta.Atom}
    (hlookup : Metta.Subst.lookup subst x = some term) :
    (x, term) ∈ subst := by
  induction subst with
  | nil => simp [Metta.Subst.lookup] at hlookup
  | cons binding rest ih =>
      rcases binding with ⟨key, value⟩
      by_cases hkey : x = key
      · subst key
        simp [Metta.Subst.lookup] at hlookup
        subst value
        simp
      · have hbeq : (x == key) = false := by simp [hkey]
        simp only [Metta.Subst.lookup, hbeq] at hlookup
        exact List.mem_cons_of_mem _ (ih hlookup)

/-- A valuation satisfying a substitution is unchanged by its one-pass
application.  This is denotational and does not require the substitution to
use any particular representative convention. -/
theorem mettaSubst_apply_solution
    (valuation : String → Metta.Atom) {subst : Metta.Subst}
    (hsatisfied : MettaConstraintsSatisfied valuation subst) :
    ∀ atom : Metta.Atom,
      applyClassSolution valuation (Metta.Subst.apply subst atom) =
        applyClassSolution valuation atom := by
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_
  · intro symbol
    simp [Metta.Subst.apply, applyClassSolution]
  · intro x
    cases hlookup : Metta.Subst.lookup subst x with
    | none =>
        simp [Metta.Subst.apply, hlookup, applyClassSolution]
    | some term =>
        have hterm := hsatisfied (x, term)
          (mettaSubst_lookup_some_mem hlookup)
        simpa [Metta.Subst.apply, hlookup, applyClassSolution] using hterm.symm
  · intro ground
    simp [Metta.Subst.apply, applyClassSolution]
  · intro atoms ih
    simp only [Metta.Subst.apply, applyClassSolution, List.map_map]
    congr 1
    apply List.map_congr_left
    exact ih

private theorem mettaSubst_apply_var_noFloat
    {subst : Metta.Subst} (hsubst : MettaSubstNoFloat subst)
    (x : String) :
    MettaAtomNoFloat (Metta.Subst.apply subst (.var x)) := by
  cases hlookup : Metta.Subst.lookup subst x with
  | none => simp [Metta.Subst.apply, hlookup, MettaAtomNoFloat]
  | some term =>
      simpa [Metta.Subst.apply, hlookup] using
        hsubst x term (mettaSubst_lookup_some_mem hlookup)

private theorem leaBindingSatisfied_restoreAlias_imp
    (valuation : String → Metta.Atom) (bindings : Metta.Bindings)
    (edge : String × String) :
    LeaBindingSatisfied valuation
        (Metta.Bindings.restoreAlias bindings edge) →
      LeaBindingSatisfied valuation bindings := by
  rcases edge with ⟨left, right⟩
  unfold Metta.Bindings.restoreAlias
  split
  · exact id
  · exact fun h =>
      (leaBindingSatisfied_addEqRaw_iff
        valuation bindings left right).mp h |>.1

private theorem leaBindingSatisfied_restoreAlias_of
    (valuation : String → Metta.Atom) (bindings : Metta.Bindings)
    (edge : String × String)
    (hedge : valuation edge.1 = valuation edge.2)
    (hbindings : LeaBindingSatisfied valuation bindings) :
    LeaBindingSatisfied valuation
      (Metta.Bindings.restoreAlias bindings edge) := by
  rcases edge with ⟨left, right⟩
  unfold Metta.Bindings.restoreAlias
  split
  · exact hbindings
  · exact (leaBindingSatisfied_addEqRaw_iff
      valuation bindings left right).mpr ⟨hbindings, hedge⟩

private theorem leaBindingSatisfied_restoreAliases_imp
    (valuation : String → Metta.Atom) (aliases : List (String × String))
    (bindings : Metta.Bindings) :
    LeaBindingSatisfied valuation
        (aliases.foldl Metta.Bindings.restoreAlias bindings) →
      LeaBindingSatisfied valuation bindings := by
  induction aliases generalizing bindings with
  | nil => exact id
  | cons edge rest ih =>
      intro hsatisfied
      exact leaBindingSatisfied_restoreAlias_imp valuation bindings edge
        (ih (bindings := Metta.Bindings.restoreAlias bindings edge)
          hsatisfied)

private theorem leaBindingSatisfied_restoreAliases_of
    (valuation : String → Metta.Atom) (aliases : List (String × String))
    (bindings : Metta.Bindings)
    (haliases : ∀ edge ∈ aliases,
      valuation edge.1 = valuation edge.2)
    (hbindings : LeaBindingSatisfied valuation bindings) :
    LeaBindingSatisfied valuation
      (aliases.foldl Metta.Bindings.restoreAlias bindings) := by
  induction aliases generalizing bindings with
  | nil => exact hbindings
  | cons edge rest ih =>
      apply ih
      · intro other hother
        exact haliases other (by simp [hother])
      · exact leaBindingSatisfied_restoreAlias_of valuation bindings edge
          (haliases edge (by simp)) hbindings

private theorem leaBindingsNoFloat_restoreAlias
    {bindings : Metta.Bindings} (hbindings : LeaBindingsNoFloat bindings)
    (edge : String × String) :
    LeaBindingsNoFloat (Metta.Bindings.restoreAlias bindings edge) := by
  rcases edge with ⟨left, right⟩
  unfold Metta.Bindings.restoreAlias
  split
  · exact hbindings
  · intro key value hmem
    exact hbindings key value
      ((Metta.Bindings.val_mem_addEqRaw_iff
        bindings left right key value).mp hmem)

private theorem leaBindingsNoFloat_restoreAliases
    {bindings : Metta.Bindings} (hbindings : LeaBindingsNoFloat bindings)
    (aliases : List (String × String)) :
    LeaBindingsNoFloat
      (aliases.foldl Metta.Bindings.restoreAlias bindings) := by
  induction aliases generalizing bindings with
  | nil => exact hbindings
  | cons edge rest ih =>
      exact ih (leaBindingsNoFloat_restoreAlias hbindings edge)

/-- Alias restoration after whole-system reconciliation changes only the
explicit equality graph, not the complete solution theory.  Every restored
edge is certified by the successful unification trace. -/
theorem rebuildFromReconciliation_solution_iff
    (valuation : String → Metta.Atom)
    {candidate source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {subst : Metta.Subst}
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hextraNoFloat : ∀ equation ∈ extra,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hreconcile :
      wholeBindingReconciliation source extra = some subst) :
    LeaBindingSatisfied valuation
        (Metta.Bindings.rebuildFromReconciliation
          candidate source extra subst) ↔
      LeaBindingSatisfied valuation
        (rebuildBindingsFromUnifier candidate subst) := by
  let base := rebuildBindingsFromUnifier candidate subst
  let aliases := Metta.Bindings.reconciliationAliases source extra subst
  have hshape :
      Metta.Bindings.rebuildFromReconciliation candidate source extra subst =
        aliases.foldl Metta.Bindings.restoreAlias base := by
    rfl
  rw [hshape]
  constructor
  · exact leaBindingSatisfied_restoreAliases_imp valuation aliases base
  · intro hbase
    have hparts :=
      (leaBindingSatisfied_append_iff valuation
        (leaEqualitySkeleton candidate)
        (Metta.Bindings.ofSubst subst)).mp (by
          simpa [base, rebuildBindingsFromUnifier,
            Metta.Bindings.rebuildFromSubst] using hbase)
    have hsubstSatisfied : MettaConstraintsSatisfied valuation subst :=
      (leaOfSubst_solution_iff valuation subst).mp hparts.2
    apply leaBindingSatisfied_restoreAliases_of valuation aliases base
    · intro edge hedge
      exact wholeBindingReconciliation_aliases_satisfied valuation
        hsourceNoFloat hextraNoFloat hreconcile hsubstSatisfied edge hedge
    · exact hbase

theorem rebuildFromReconciliation_noFloat
    {candidate source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {subst : Metta.Subst}
    (hsubst : MettaSubstNoFloat subst) :
    LeaBindingsNoFloat
      (Metta.Bindings.rebuildFromReconciliation
        candidate source extra subst) := by
  exact leaBindingsNoFloat_restoreAliases
    (rebuildBindingsFromUnifier_noFloat hsubst)
    (Metta.Bindings.reconciliationAliases source extra subst)

/-- Equality reconciliation rebuilds from the candidate skeleton, so the new
alias remains explicit even when the whole-system unifier also presents it.
Its solution theory is nevertheless just the old theory conjoined with that
alias. -/
theorem rebuildBindingsFromUnifier_addEq_solution_iff
    (valuation : String → Metta.Atom)
    {bindings : Metta.Bindings} {left right : String}
    {result : Metta.Subst}
    (hbindingsNoFloat : LeaBindingsNoFloat bindings)
    (hreconcile :
      wholeBindingReconciliation bindings
        [(.var left, .var right)] = some result) :
    LeaBindingSatisfied valuation
        (rebuildBindingsFromUnifier
          (Metta.Bindings.addEqRaw bindings left right) result) ↔
      LeaBindingSatisfied valuation bindings ∧
        valuation left = valuation right := by
  have hwhole :
      MettaConstraintsSatisfied valuation result ↔
        LeaBindingSatisfied valuation bindings ∧
          valuation left = valuation right := by
    simpa [MettaEquationsSatisfied, MettaEquationSatisfied,
      applyClassSolution] using
      (wholeBindingReconciliation_solution_iff valuation
        hbindingsNoFloat (by
          intro equation hmem
          simp only [List.mem_singleton] at hmem
          subst equation
          simp [MettaAtomNoFloat]) hreconcile)
  constructor
  · intro hout
    have hparts :=
      (leaBindingSatisfied_append_iff valuation
        (leaEqualitySkeleton
          (Metta.Bindings.addEqRaw bindings left right))
        (Metta.Bindings.ofSubst result)).mp (by
          simpa [rebuildBindingsFromUnifier,
            Metta.Bindings.rebuildFromSubst] using hout)
    exact hwhole.mp ((leaOfSubst_solution_iff valuation result).mp hparts.2)
  · intro hinput
    have hcandidate :
        LeaBindingSatisfied valuation
          (Metta.Bindings.addEqRaw bindings left right) :=
      (leaBindingSatisfied_addEqRaw_iff valuation bindings left right).mpr
        hinput
    have hrebuilt :=
      (leaBindingSatisfied_append_iff valuation
        (leaEqualitySkeleton
          (Metta.Bindings.addEqRaw bindings left right))
        (Metta.Bindings.ofSubst result)).mpr
          ⟨leaEqualitySkeleton_satisfied valuation hcandidate,
            (leaOfSubst_solution_iff valuation result).mpr
              (hwhole.mpr hinput)⟩
    simpa [rebuildBindingsFromUnifier,
      Metta.Bindings.rebuildFromSubst] using hrebuilt

/-- Every successful repaired-LeaTTa alias insertion presents exactly the old
binding theory conjoined with the requested equality, across both the raw and
whole-system reconciliation branches. -/
theorem leaAddVarEquality_solution_iff
    (valuation : String → Metta.Atom)
    {bindings out : Metta.Bindings} {left right : String}
    (hbindingsNoFloat : LeaBindingsNoFloat bindings)
    (hout : out ∈ Metta.Bindings.addVarEquality bindings left right) :
    LeaBindingSatisfied valuation out ↔
      LeaBindingSatisfied valuation bindings ∧
        valuation left = valuation right := by
  cases hunify : Metta.Bindings.unifyValues
      (Metta.Bindings.classValues
        (Metta.Bindings.addEqRaw bindings left right) left) with
  | none =>
      simp [Metta.Bindings.addVarEquality, hunify] at hout
  | some result =>
      cases result with
      | nil =>
          simp [Metta.Bindings.addVarEquality, hunify] at hout
          subst out
          exact
            leaBindingSatisfied_addEqRaw_iff
              valuation bindings left right
      | cons binding rest =>
          cases hreconcile : wholeBindingReconciliation bindings
              [(.var left, .var right)] with
          | none =>
              simp [Metta.Bindings.addVarEquality, hunify,
                hreconcile] at hout
          | some sigma =>
              simp [Metta.Bindings.addVarEquality, hunify,
                hreconcile] at hout
              subst out
              rw [rebuildFromReconciliation_solution_iff valuation
                hbindingsNoFloat (by
                  intro equation hmem
                  simp only [List.mem_singleton] at hmem
                  subst equation
                  simp [MettaAtomNoFloat]) hreconcile]
              exact rebuildBindingsFromUnifier_addEq_solution_iff
                valuation hbindingsNoFloat hreconcile

theorem wholeBindingReconciliation_rebuild_noFloat
    {bindings : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hbindingsNoFloat : LeaBindingsNoFloat bindings)
    (hextraNoFloat : ∀ equation ∈ extra,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hreconcile :
      wholeBindingReconciliation bindings extra = some result) :
    LeaBindingsNoFloat (rebuildBindingsFromUnifier bindings result) :=
  rebuildBindingsFromUnifier_noFloat
    (wholeBindingReconciliation_result_noFloat
      hbindingsNoFloat hextraNoFloat hreconcile)

/-- The weakest representation-independent binding invariant used during
merge: equality classes agree extensionally and both presentations have the
same class-value equation solutions. -/
structure LeaBindingSolutionEquiv
    (b : Bindings) (lb : Metta.Bindings) : Prop where
  classes : ∀ start finish,
    finish ∈ b.eqClass start ↔
      finish ∈ Metta.Bindings.eqClass lb start
  solutions : LeaBindingSolutionTheoryEquiv b lb

/-- HE and LeaTTa atoms agree modulo replacement of a variable by another
member of its already-established HE equality class.  Unlike fully resolved
solution equality, this relation retains the raw variable provenance that a
later nonlinear reconciliation can expose. -/
inductive HELeaAtomClassRel (b : Bindings) : Atom → Metta.Atom → Prop where
  | symbol (name : String) :
      HELeaAtomClassRel b (.symbol name) (.sym name)
  | variable {left right : String} :
      right ∈ b.eqClass left →
        HELeaAtomClassRel b (.var left) (.var right)
  | grounded (value : GroundedValue) :
      HELeaAtomClassRel b (.grounded value)
        (encodeModelAtom (.grounded value))
  | expression {left : List Atom} {right : List Metta.Atom} :
      List.Forall₂ (HELeaAtomClassRel b) left right →
        HELeaAtomClassRel b (.expression left) (.expr right)

mutual

/-- Exact translation is the reflexive case of class-relative atom
agreement. -/
theorem HELeaAtomClassRel.translation (b : Bindings) :
    (atom : Atom) → HELeaAtomClassRel b atom (encodeModelAtom atom)
  | .symbol name => .symbol name
  | .var name => .variable (by
      rw [EqualityClosure.mem_eqClass_iff_reachable])
  | .grounded value => .grounded value
  | .expression atoms =>
      .expression (HELeaAtomClassRel.translationList b atoms)

/-- List companion to exact class-relative atom translation. -/
theorem HELeaAtomClassRel.translationList (b : Bindings) :
    (atoms : List Atom) →
      List.Forall₂ (HELeaAtomClassRel b) atoms (encodeModelAtoms atoms)
  | [] => .nil
  | atom :: atoms => .cons
      (HELeaAtomClassRel.translation b atom)
      (HELeaAtomClassRel.translationList b atoms)

end

mutual

/-- Class-relative atom agreement is monotone when the HE equality closure is
extended. -/
theorem HELeaAtomClassRel.mono
    {before after : Bindings}
    (hmono : ∀ {left right},
      right ∈ before.eqClass left → right ∈ after.eqClass left) :
    ∀ {atom leaAtom}, HELeaAtomClassRel before atom leaAtom →
      HELeaAtomClassRel after atom leaAtom
  | _, _, .symbol name => .symbol name
  | _, _, .variable hclass => .variable (hmono hclass)
  | _, _, .grounded value => .grounded value
  | _, _, .expression hatoms =>
      .expression (HELeaAtomClassRel.monoList hmono hatoms)

/-- List companion to monotonicity of class-relative atom agreement. -/
theorem HELeaAtomClassRel.monoList
    {before after : Bindings}
    (hmono : ∀ {left right},
      right ∈ before.eqClass left → right ∈ after.eqClass left) :
    ∀ {atoms leaAtoms},
      List.Forall₂ (HELeaAtomClassRel before) atoms leaAtoms →
        List.Forall₂ (HELeaAtomClassRel after) atoms leaAtoms
  | _, _, .nil => .nil
  | _, _, .cons hatom hrest => .cons
      (HELeaAtomClassRel.mono hmono hatom)
      (HELeaAtomClassRel.monoList hmono hrest)

end

/-- Class-indexed raw value agreement. Assignment keys may move within one
already-equal class, and variables inside their stored atoms may do likewise;
cross-class provenance is preserved. Multiplicity and relation-list order are
not semantic. -/
def LeaClassValueRelEquiv (b : Bindings) (lb : Metta.Bindings) : Prop :=
  (∀ key value, (key, value) ∈ b.assignments →
    ∃ leaKey leaValue,
      Metta.BindingRel.val leaKey leaValue ∈ lb ∧
        leaKey ∈ b.eqClass key ∧
          HELeaAtomClassRel b value leaValue) ∧
  (∀ leaKey leaValue, Metta.BindingRel.val leaKey leaValue ∈ lb →
    ∃ key value,
      (key, value) ∈ b.assignments ∧
        leaKey ∈ b.eqClass key ∧
          HELeaAtomClassRel b value leaValue)

/-- The compositional binding invariant.  Equality closure and full solution
theory are supplemented by class-indexed raw value provenance, the least
extra information required by the nonlinear reconciliation counterexample. -/
structure LeaBindingCongruence
    (b : Bindings) (lb : Metta.Bindings) : Prop where
  semantic : LeaBindingSolutionEquiv b lb
  classValues : LeaClassValueRelEquiv b lb

/-- Equality-graph theory plus complete binding solution theory constructs the
compositional invariant.  In particular, callers need not expose or compare
the concrete equality-edge presentations. -/
theorem LeaBindingSolutionEquiv.of_theories
    {b : Bindings} {lb : Metta.Bindings}
    (hequalities : LeaEqualityTheoryEquiv b lb)
    (hsolutions : LeaBindingSolutionTheoryEquiv b lb) :
    LeaBindingSolutionEquiv b lb :=
  ⟨fun _ _ => eqClass_mem_iff_of_equalityTheoryEquiv hequalities,
    hsolutions⟩

/-- Direct-value agreement plus equality-graph theory is sufficient for the
full representation-independent invariant.  The two engines may present the
same connected component with different spanning trees. -/
theorem LeaBindingSolutionEquiv.of_value_and_equality_theories
    {b : Bindings} {lb : Metta.Bindings}
    (hvalues : LeaValueRelEquiv b lb)
    (hequalities : LeaEqualityTheoryEquiv b lb) :
    LeaBindingSolutionEquiv b lb := by
  apply LeaBindingSolutionEquiv.of_theories hequalities
  intro valuation
  constructor
  · rintro ⟨hheValues, hheEqualities⟩
    refine ⟨?_, (hequalities valuation).mp hheEqualities⟩
    intro x value hmem
    obtain ⟨heValue, hheValue, rfl⟩ :=
      (hvalues x value).mp hmem
    exact hheValues x heValue hheValue
  · rintro ⟨hleaValues, hleaEqualities⟩
    refine ⟨?_, (hequalities valuation).mpr hleaEqualities⟩
    intro x heValue hmem
    have hlea :
        Metta.BindingRel.val x (encodeModelAtom heValue) ∈ lb :=
      (hvalues x (encodeModelAtom heValue)).mpr
        ⟨heValue, hmem, rfl⟩
    exact hleaValues x (encodeModelAtom heValue) hlea

/-- Exact direct-value agreement plus equality-graph theory constructs the
strong compositional invariant.  This is the common leaf/canonical case; later
reconciliation proofs may use class-relative rather than exact raw values. -/
theorem LeaBindingCongruence.of_value_and_equality_theories
    {b : Bindings} {lb : Metta.Bindings}
    (hvalues : LeaValueRelEquiv b lb)
    (hequalities : LeaEqualityTheoryEquiv b lb) :
    LeaBindingCongruence b lb := by
  refine ⟨LeaBindingSolutionEquiv.of_value_and_equality_theories
    hvalues hequalities, ?_⟩
  constructor
  · intro key value hmem
    refine ⟨key, encodeModelAtom value, ?_, ?_,
      HELeaAtomClassRel.translation b value⟩
    · exact (hvalues key (encodeModelAtom value)).mpr
        ⟨value, hmem, rfl⟩
    · rw [EqualityClosure.mem_eqClass_iff_reachable]
  · intro leaKey leaValue hmem
    obtain ⟨value, hvalue, rfl⟩ :=
      (hvalues leaKey leaValue).mp hmem
    refine ⟨leaKey, value, hvalue, ?_,
      HELeaAtomClassRel.translation b value⟩
    rw [EqualityClosure.mem_eqClass_iff_reachable]

/-- Direct relation-set agreement is one sufficient presentation of solution
equivalence.  Later reconciliation lemmas use the weaker conclusion even when
the returned direct edge sets differ. -/
theorem LeaBindingSolutionEquiv.of_rel
    {b : Bindings} {lb : Metta.Bindings}
    (hequiv : LeaBindingRelEquiv b lb) :
    LeaBindingSolutionEquiv b lb := by
  refine ⟨fun _ _ => eqClass_mem_iff_of_leaBindingRelEquiv hequiv, ?_⟩
  intro valuation
  constructor
  · rintro ⟨hvalues, hequalities⟩
    refine ⟨?_, ?_⟩
    · intro x value hmem
      obtain ⟨heValue, hheValue, rfl⟩ :=
        (hequiv.values x value).mp hmem
      exact hvalues x heValue hheValue
    · intro x y hmem
      have hhe := (hequiv.equalities x y).mp (Or.inl hmem)
      rcases hhe with hxy | hyx
      · exact hequalities x y hxy
      · exact (hequalities y x hyx).symm
  · rintro ⟨hvalues, hequalities⟩
    refine ⟨?_, ?_⟩
    · intro x heValue hmem
      have hlea :
          Metta.BindingRel.val x (encodeModelAtom heValue) ∈ lb :=
        (hequiv.values x (encodeModelAtom heValue)).mpr
          ⟨heValue, hmem, rfl⟩
      exact hvalues x (encodeModelAtom heValue) hlea
    · intro x y hmem
      have hlea := (hequiv.equalities x y).mpr (Or.inl hmem)
      rcases hlea with hxy | hyx
      · exact hequalities x y hxy
      · exact (hequalities y x hyx).symm

/-- Direct relation agreement is also a sufficient presentation of the
strong compositional invariant. -/
theorem LeaBindingCongruence.of_rel
    {b : Bindings} {lb : Metta.Bindings}
    (hequiv : LeaBindingRelEquiv b lb) :
    LeaBindingCongruence b lb := by
  refine ⟨LeaBindingSolutionEquiv.of_rel hequiv, ?_⟩
  constructor
  · intro key value hmem
    refine ⟨key, encodeModelAtom value, ?_, ?_,
      HELeaAtomClassRel.translation b value⟩
    · exact (hequiv.values key (encodeModelAtom value)).mpr
        ⟨value, hmem, rfl⟩
    · rw [EqualityClosure.mem_eqClass_iff_reachable]
  · intro leaKey leaValue hmem
    obtain ⟨value, hvalue, rfl⟩ :=
      (hequiv.values leaKey leaValue).mp hmem
    refine ⟨leaKey, value, hvalue, ?_,
      HELeaAtomClassRel.translation b value⟩
    rw [EqualityClosure.mem_eqClass_iff_reachable]

/-- Empty bindings agree in the strengthened invariant. -/
theorem LeaBindingCongruence.empty :
    LeaBindingCongruence Bindings.empty Metta.Bindings.empty :=
  LeaBindingCongruence.of_rel LeaBindingRelEquiv.empty

/-- A reflexive HE equality and LeaTTa's suppressed reflexive relation have
the same compositional meaning.  This is the presentation-independent leaf
needed when recursive matching encounters the same variable on both sides. -/
theorem LeaBindingCongruence.reflexiveSingleton (v : String) :
    LeaBindingCongruence
      (⟨[], [(v, v)]⟩ : Bindings) Metta.Bindings.empty := by
  apply LeaBindingCongruence.of_value_and_equality_theories
  · intro key value
    simp [Metta.Bindings.empty]
  · intro valuation
    simp [HEEqualitySatisfied, LeaEqualitySatisfied, Metta.Bindings.empty]

private theorem reachable_of_adj_reachable
    {V : Type} {source target : SimpleGraph V}
    (hadj : ∀ ⦃x y⦄, source.Adj x y → target.Reachable x y) :
    ∀ ⦃x y⦄, source.Reachable x y → target.Reachable x y := by
  intro x y hreach
  exact hreach.elim fun walk => by
    induction walk with
    | nil => exact .rfl
    | cons hedge tail ih => exact (hadj hedge).trans (ih tail.reachable)

/-- The equality closure of a successful executable reconciliation is exactly
the closure generated by the candidate graph and the successful alias trace.
Substitution orientation and redundant restored edges disappear at this
quotient boundary. -/
theorem rebuildFromReconciliation_class_iff
    {candidate source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {subst : Metta.Subst}
    (hreconcile : wholeBindingReconciliation source extra = some subst)
    {start finish : String} :
    finish ∈ Metta.Bindings.eqClass
        (Metta.Bindings.rebuildFromReconciliation
          candidate source extra subst) start ↔
      (EqualityClosure.edgeGraph
        (leaEqualityEdges candidate ++
          Metta.Bindings.reconciliationAliases source extra subst)).Reachable
        start finish := by
  rw [mem_leaEqClass_iff_reachable]
  constructor
  · apply reachable_of_adj_reachable
    intro left right hadj
    rw [EqualityClosure.edgeGraph_adj_iff] at hadj
    rcases hadj with ⟨hne, hforward | hreverse⟩
    · rcases rebuildFromReconciliation_edge_source hreconcile hforward with
        hcandidate | halias
      · exact (show (EqualityClosure.edgeGraph
            (leaEqualityEdges candidate ++
              Metta.Bindings.reconciliationAliases source extra subst)).Adj
              left right from
          ⟨hne, Or.inl (List.mem_append_left _ hcandidate)⟩).reachable
      · exact (show (EqualityClosure.edgeGraph
            (leaEqualityEdges candidate ++
              Metta.Bindings.reconciliationAliases source extra subst)).Adj
              left right from
          ⟨hne, Or.inl (List.mem_append_right _ halias)⟩).reachable
    · rcases rebuildFromReconciliation_edge_source hreconcile hreverse with
        hcandidate | halias
      · exact (show (EqualityClosure.edgeGraph
            (leaEqualityEdges candidate ++
              Metta.Bindings.reconciliationAliases source extra subst)).Adj
              left right from
          ⟨hne, Or.inr (List.mem_append_left _ hcandidate)⟩).reachable
      · exact (show (EqualityClosure.edgeGraph
            (leaEqualityEdges candidate ++
              Metta.Bindings.reconciliationAliases source extra subst)).Adj
              left right from
          ⟨hne, Or.inr (List.mem_append_right _ halias)⟩).reachable
  · apply reachable_of_adj_reachable
    intro left right hadj
    rw [EqualityClosure.edgeGraph_adj_iff] at hadj
    have hconnect : ∀ {x y : String}, x ≠ y →
        (x, y) ∈ leaEqualityEdges candidate ++
            Metta.Bindings.reconciliationAliases source extra subst →
          (EqualityClosure.edgeGraph
            (leaEqualityEdges
              (Metta.Bindings.rebuildFromReconciliation
                candidate source extra subst))).Reachable x y := by
      intro x y hne hmem
      rcases List.mem_append.mp hmem with hcandidate | halias
      · apply mem_leaEqClass_iff_reachable.mp
        apply rebuildFromReconciliation_preserves_class
        apply mem_leaEqClass_iff_reachable.mpr
        exact (show
          (EqualityClosure.edgeGraph (leaEqualityEdges candidate)).Adj x y
            from ⟨hne, Or.inl hcandidate⟩).reachable
      · apply mem_leaEqClass_iff_reachable.mp
        exact rebuildFromReconciliation_connects_alias
          candidate source extra subst halias
    rcases hadj with ⟨hne, hforward | hreverse⟩
    · exact hconnect hne hforward
    · exact (hconnect hne.symm hreverse).symm

/-- Adding the same undirected edge preserves any pre-existing equivalence of
connected components. -/
private theorem reachable_sup_edge_congr
    {V : Type} {left right : SimpleGraph V}
    (hreach : ∀ x y, left.Reachable x y ↔ right.Reachable x y)
    (a b x y : V) :
    (left ⊔ SimpleGraph.edge a b).Reachable x y ↔
      (right ⊔ SimpleGraph.edge a b).Reachable x y := by
  constructor
  · apply reachable_of_adj_reachable
    intro u v huv
    rcases huv with hleft | hedge
    · exact (hreach u v).mp hleft.reachable |>.mono le_sup_left
    · exact hedge.reachable.mono le_sup_right
  · apply reachable_of_adj_reachable
    intro u v huv
    rcases huv with hright | hedge
    · exact (hreach u v).mpr hright.reachable |>.mono le_sup_left
    · exact hedge.reachable.mono le_sup_right

/-- Fresh HE assignment presents exactly the old binding equations conjoined
with the new value equation. -/
theorem heBindingSatisfied_assign_fresh_iff
    (valuation : String → Metta.Atom)
    {b : Bindings} {v : String} {value : Atom}
    (hlookup : b.lookup v = none) :
    HEBindingSatisfied valuation (b.assign v value) ↔
      HEBindingSatisfied valuation b ∧
        valuation v =
          applyClassSolution valuation (encodeModelAtom value) := by
  have hbound : b.isBound v = false := by
    simp [Bindings.isBound, hlookup]
  constructor
  · rintro ⟨hvalues, hequalities⟩
    refine ⟨⟨?_, hequalities⟩, ?_⟩
    · intro x oldValue hmem
      exact hvalues x oldValue (by
        simp [Bindings.assign, hbound, hmem])
    · exact hvalues v value (by
        simp [Bindings.assign, hbound])
  · rintro ⟨⟨hvalues, hequalities⟩, hnew⟩
    refine ⟨?_, hequalities⟩
    intro x outValue hmem
    simp only [Bindings.assign, hbound, Bool.false_eq_true, if_false,
      List.mem_append, List.mem_singleton, Prod.mk.injEq] at hmem
    rcases hmem with hold | ⟨rfl, rfl⟩
    · exact hvalues x outValue hold
    · exact hnew

/-- Adding one HE equality presents exactly the old binding equations
conjoined with that equality. -/
theorem heBindingSatisfied_addEquality_iff
    (valuation : String → Metta.Atom)
    (b : Bindings) (left right : String) :
    HEBindingSatisfied valuation (b.addEquality left right) ↔
      HEBindingSatisfied valuation b ∧ valuation left = valuation right := by
  constructor
  · rintro ⟨hvalues, hequalities⟩
    refine ⟨⟨hvalues, ?_⟩, ?_⟩
    · intro x y hmem
      exact hequalities x y (by
        simp [Bindings.addEquality, hmem])
    · exact hequalities left right (by
        simp [Bindings.addEquality])
  · rintro ⟨⟨hvalues, hequalities⟩, hnew⟩
    refine ⟨hvalues, ?_⟩
    intro x y hmem
    simp only [Bindings.addEquality, List.mem_append, List.mem_singleton,
      Prod.mk.injEq] at hmem
    rcases hmem with hold | ⟨rfl, rfl⟩
    · exact hequalities x y hold
    · exact hnew

/-- Raw insertion of one common alias preserves equality classes and complete
solution theory without requiring relation-list or representative agreement. -/
theorem LeaBindingSolutionEquiv.addEqRaw
    {b : Bindings} {lb : Metta.Bindings}
    {queryVar patternVar : String}
    (h : LeaBindingSolutionEquiv b lb)
    (hne : queryVar ≠ patternVar) :
    LeaBindingSolutionEquiv
      (b.addEquality queryVar patternVar)
      (Metta.Bindings.addEqRaw lb patternVar queryVar) := by
  have hne' : patternVar ≠ queryVar := hne.symm
  refine ⟨?_, ?_⟩
  · intro start finish
    have holdReach : ∀ x y,
        (EqualityClosure.edgeGraph b.equalities).Reachable x y ↔
          (EqualityClosure.edgeGraph (leaEqualityEdges lb)).Reachable x y := by
      intro x y
      rw [← EqualityClosure.mem_eqClass_iff_reachable,
        ← mem_leaEqClass_iff_reachable]
      exact h.classes x y
    have hheGraph :
        EqualityClosure.edgeGraph
            (b.addEquality queryVar patternVar).equalities =
          EqualityClosure.edgeGraph b.equalities ⊔
            SimpleGraph.edge queryVar patternVar := by
      ext x y
      simp only [EqualityClosure.edgeGraph_adj_iff,
        Bindings.addEquality, List.mem_append, List.mem_singleton,
        SimpleGraph.sup_adj, SimpleGraph.edge_adj]
      aesop
    have hleaGraph :
        EqualityClosure.edgeGraph
            (leaEqualityEdges
              (Metta.Bindings.addEqRaw lb patternVar queryVar)) =
          EqualityClosure.edgeGraph (leaEqualityEdges lb) ⊔
            SimpleGraph.edge queryVar patternVar := by
      ext x y
      simp only [EqualityClosure.edgeGraph_adj_iff,
        SimpleGraph.sup_adj, SimpleGraph.edge_adj]
      rw [mem_leaEqualityEdges_addEqRaw_iff lb hne',
        mem_leaEqualityEdges_addEqRaw_iff lb hne']
      aesop
    rw [EqualityClosure.mem_eqClass_iff_reachable,
      mem_leaEqClass_iff_reachable, hheGraph, hleaGraph]
    exact reachable_sup_edge_congr holdReach queryVar patternVar start finish
  · intro valuation
    rw [heBindingSatisfied_addEquality_iff, leaBindingSatisfied_addEqRaw_iff]
    exact and_congr (h.solutions valuation) eq_comm

/-- Raw insertion of one common alias preserves the strengthened
compositional invariant.  Existing raw values remain present unchanged, while
their key and atom witnesses lift monotonically into the enlarged equality
closure. -/
theorem LeaBindingCongruence.addEqRaw
    {b : Bindings} {lb : Metta.Bindings}
    {queryVar patternVar : String}
    (h : LeaBindingCongruence b lb)
    (hne : queryVar ≠ patternVar) :
    LeaBindingCongruence
      (b.addEquality queryVar patternVar)
      (Metta.Bindings.addEqRaw lb patternVar queryVar) := by
  have hne' : patternVar ≠ queryVar := hne.symm
  have hclassMono : ∀ {left right : String},
      right ∈ b.eqClass left →
        right ∈ (b.addEquality queryVar patternVar).eqClass left := by
    intro left right hclass
    rw [EqualityClosure.mem_eqClass_iff_reachable] at hclass ⊢
    apply hclass.mono
    intro x y hadj
    rw [EqualityClosure.edgeGraph_adj_iff] at hadj ⊢
    rcases hadj with ⟨hxy, hforward | hreverse⟩
    · exact ⟨hxy, Or.inl (by
        simp [Bindings.addEquality, hforward])⟩
    · exact ⟨hxy, Or.inr (by
        simp [Bindings.addEquality, hreverse])⟩
  refine ⟨h.semantic.addEqRaw hne, ?_⟩
  constructor
  · intro key value hvalue
    obtain ⟨leaKey, leaValue, hleaValue, hkeyClass, hatom⟩ :=
      h.classValues.1 key value hvalue
    refine ⟨leaKey, leaValue, ?_, hclassMono hkeyClass,
      HELeaAtomClassRel.mono hclassMono hatom⟩
    exact Metta.Bindings.mem_addEqRaw_of_mem
      lb patternVar queryVar hleaValue
  · intro leaKey leaValue hvalue
    have holdValue : Metta.BindingRel.val leaKey leaValue ∈ lb := by
      exact (Metta.Bindings.val_mem_addEqRaw_iff
        lb patternVar queryVar leaKey leaValue).mp hvalue
    obtain ⟨key, value, hheValue, hkeyClass, hatom⟩ :=
      h.classValues.2 leaKey leaValue holdValue
    exact ⟨key, value, by
      simpa [Bindings.addEquality] using hheValue,
      hclassMono hkeyClass,
      HELeaAtomClassRel.mono hclassMono hatom⟩

/-! ### Representation-independent binding semantics

Direct equality edges, relation order, and the representative selected for an
equality class are presentations of a binding solution, not its meaning.  The
semantic interface below records exactly the two observations needed by the
equation lane:

* equality classes agree extensionally; and
* every class resolves to the same value through one global permutation of
  unresolved variables.

The *single* permutation is important.  Independent pointwise alpha witnesses
would forget sharing and could equate `[x, x]` with `[y, z]`.  Conversely, no
concrete relation list, edge set, representative chronology, or selected MGU is
part of this interface.
-/

/-- HE's resolved value of one equality class, translated to LeaTTa atoms.
An unresolved variable is observed as itself. -/
def heClassSolutionAt (b : Bindings) (fuel : Nat) (v : String) : Metta.Atom :=
  encodeModelAtom ((b.resolveFull v fuel).getD (.var v))

/-- LeaTTa's resolved value of one equality class.  An unresolved variable is
observed as itself. -/
def leaClassSolution (lb : Metta.Bindings) (v : String) : Metta.Atom :=
  (Metta.Bindings.resolve lb v).getD (.var v)

/-- Joint HE class-value readout on a finite variable scope.  Packing the
solutions into one atom makes variable sharing observable. -/
def heClassSolutionReadout
    (scope : List String) (b : Bindings) (fuel : Nat) : Metta.Atom :=
  .expr (scope.map (heClassSolutionAt b fuel))

/-- Joint LeaTTa class-value readout on a finite variable scope. -/
def leaClassSolutionReadout
    (scope : List String) (lb : Metta.Bindings) : Metta.Atom :=
  .expr (scope.map (leaClassSolution lb))

/-- LeaTTa instantiation is exactly application of its extensional class
solution map. -/
theorem applyClassSolution_lea_eq_instantiate
    (lb : Metta.Bindings) (atom : Metta.Atom) :
    applyClassSolution (leaClassSolution lb) atom =
      Metta.instantiate lb atom := by
  induction atom with
  | expr atoms ih =>
      simp only [applyClassSolution, Metta.instantiate,
        Metta.Bindings.resolveAtom]
      rw [List.map_congr_left ih]
      rfl
  | _ => simp [applyClassSolution, leaClassSolution,
      Metta.instantiate, Metta.Bindings.resolveAtom]

/-- One global solution permutation commutes with semantic substitution.  The
variable-side hypothesis is scoped to the variables observable in `atom`. -/
theorem applyClassSolution_eq_renBy
    {left right : String → Metta.Atom}
    (solutionPerm : Equiv.Perm String) :
    ∀ atom : Metta.Atom,
      (∀ v ∈ atom.vars, left v = renBy solutionPerm (right v)) →
        applyClassSolution left atom =
          renBy solutionPerm (applyClassSolution right atom) := by
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_
  · intro symbol _h
    simp [applyClassSolution, renBy]
  · intro v h
    simpa only [applyClassSolution] using
      h v (by simp [Metta.Atom.vars])
  · intro ground _h
    simp [applyClassSolution, renBy]
  · intro atoms ih h
    simp only [applyClassSolution, renBy, List.map_map]
    congr 1
    apply List.map_congr_left
    intro child hchild
    exact ih child hchild (fun v hv => h v (by
      simp only [Metta.Atom.vars, List.mem_flatten, List.mem_map]
      exact ⟨child.vars, ⟨child, hchild, rfl⟩, hv⟩))

/-- Class-value solutions agree through one global permutation.  The
permutation is existential because the relation itself is proof-valued. -/
def LeaClassSolutionEquivAt
    (scope : List String) (fuel : Nat)
    (b : Bindings) (lb : Metta.Bindings) : Prop :=
  ∃ solutionPerm : Equiv.Perm String, ∀ v ∈ scope,
    leaClassSolution lb v =
      renBy solutionPerm (heClassSolutionAt b fuel v)

/-- Representation-independent agreement of an HE binding solution with a
repaired-LeaTTa binding solution at one HE resolver fuel.

The solution permutation is global across all variables, so the second field
preserves both compound value structure and variable sharing.  A permutation,
rather than an arbitrary function, states that the two engines may choose
different names for the same unresolved solution parameters but may neither
identify nor invent parameters. -/
structure LeaBindingSemanticEquivAt
    (scope : List String) (fuel : Nat)
    (b : Bindings) (lb : Metta.Bindings) : Prop where
  classes : ∀ start finish,
    finish ∈ b.eqClass start ↔
      finish ∈ Metta.Bindings.eqClass lb start
  classSolutions : LeaClassSolutionEquivAt scope fuel b lb

namespace LeaBindingSemanticEquivAt

/-- Restrict semantic agreement to a smaller observation scope. -/
theorem mono {small large : List String} {fuel : Nat}
    {b : Bindings} {lb : Metta.Bindings}
    (hsub : ∀ ⦃v⦄, v ∈ small → v ∈ large)
    (h : LeaBindingSemanticEquivAt large fuel b lb) :
    LeaBindingSemanticEquivAt small fuel b lb := by
  refine ⟨h.classes, ?_⟩
  obtain ⟨solutionPerm, hsolution⟩ := h.classSolutions
  exact ⟨solutionPerm, fun v hv => hsolution v (hsub hv)⟩

/-- The semantic invariant exposes one renaming equation for the complete
joint readout, rather than unrelated pointwise witnesses. -/
theorem readout_eq_renBy {scope : List String} {fuel : Nat}
    {b : Bindings} {lb : Metta.Bindings}
    (h : LeaBindingSemanticEquivAt scope fuel b lb) :
    ∃ solutionPerm : Equiv.Perm String,
      leaClassSolutionReadout scope lb =
        renBy solutionPerm (heClassSolutionReadout scope b fuel) := by
  obtain ⟨solutionPerm, hsolution⟩ := h.classSolutions
  refine ⟨solutionPerm, ?_⟩
  simp only [leaClassSolutionReadout, heClassSolutionReadout, renBy,
    List.map_map]
  congr 1
  apply List.map_congr_left
  intro v hv
  simpa [Function.comp_def] using hsolution v hv

/-- Joint class-value readouts are alpha-equivalent.  Because the entire
scope is packed into one atom, this theorem observes nonlinear sharing. -/
theorem readout_alpha {scope : List String} {fuel : Nat}
    {b : Bindings} {lb : Metta.Bindings}
    (h : LeaBindingSemanticEquivAt scope fuel b lb) :
    Metta.AlphaEq
      (leaClassSolutionReadout scope lb)
      (heClassSolutionReadout scope b fuel) := by
  obtain ⟨solutionPerm, hreadout⟩ := h.readout_eq_renBy
  unfold Metta.AlphaEq
  rw [hreadout]
  exact canonicalizeVars_renBy_of_injective solutionPerm.injective _

/-- Semantic binding agreement transports arbitrary LeaTTa instantiation to
the HE class-solution application through one global permutation. -/
theorem instantiate_eq_renBy_classSolution
    {scope : List String} {fuel : Nat}
    {b : Bindings} {lb : Metta.Bindings}
    (h : LeaBindingSemanticEquivAt scope fuel b lb)
    (atom : Metta.Atom)
    (hvars : ∀ ⦃v⦄, v ∈ atom.vars → v ∈ scope) :
    ∃ solutionPerm : Equiv.Perm String,
      Metta.instantiate lb atom =
        renBy solutionPerm
          (applyClassSolution (heClassSolutionAt b fuel) atom) := by
  obtain ⟨solutionPerm, hsolution⟩ := h.classSolutions
  refine ⟨solutionPerm, ?_⟩
  rw [← applyClassSolution_lea_eq_instantiate]
  exact applyClassSolution_eq_renBy solutionPerm atom
    (fun v hv => hsolution v (hvars hv))

/-- Derived alpha-equivalent instantiation for every atom observed by the
semantic scope.  No representative or MGU equality appears in the statement. -/
theorem instantiate_alpha_classSolution
    {scope : List String} {fuel : Nat}
    {b : Bindings} {lb : Metta.Bindings}
    (h : LeaBindingSemanticEquivAt scope fuel b lb)
    (atom : Metta.Atom)
    (hvars : ∀ ⦃v⦄, v ∈ atom.vars → v ∈ scope) :
    Metta.AlphaEq
      (Metta.instantiate lb atom)
      (applyClassSolution (heClassSolutionAt b fuel) atom) := by
  obtain ⟨solutionPerm, hinstantiate⟩ :=
    h.instantiate_eq_renBy_classSolution atom hvars
  unfold Metta.AlphaEq
  rw [hinstantiate]
  exact canonicalizeVars_renBy_of_injective solutionPerm.injective _

/-- Semantic binding agreement immediately yields the observable alpha
agreement for every resolved class. -/
theorem classSolution_alpha {scope : List String} {fuel : Nat}
    {b : Bindings} {lb : Metta.Bindings}
    (h : LeaBindingSemanticEquivAt scope fuel b lb)
    {v : String} (hv : v ∈ scope) :
    Metta.AlphaEq (leaClassSolution lb v) (heClassSolutionAt b fuel v) := by
  obtain ⟨solutionPerm, hsolution⟩ := h.classSolutions
  unfold Metta.AlphaEq
  rw [hsolution v hv]
  exact canonicalizeVars_renBy_of_injective solutionPerm.injective _

/-- Empty bindings have the same semantic solution at every fuel. -/
theorem empty (scope : List String) (fuel : Nat) :
    LeaBindingSemanticEquivAt scope fuel
      Bindings.empty Metta.Bindings.empty := by
  refine ⟨?_, ?_⟩
  · intro start finish
    rfl
  · refine ⟨Equiv.refl String, ?_⟩
    intro v _hv
    have hlea :
        leaClassSolution Metta.Bindings.empty v = Metta.Atom.var v := by
      simp [leaClassSolution, Metta.Bindings.empty, Metta.Bindings.resolve,
        Metta.Bindings.eqClassOrdered, Metta.Bindings.eqVarsInOrder,
        Metta.Bindings.eqClass, Metta.Bindings.eqClassAux,
        Metta.Bindings.eqStep, Metta.Bindings.classValues,
        Metta.Bindings.lookupVal]
    have hhe :
        heClassSolutionAt Bindings.empty fuel v = Metta.Atom.var v := by
      simp [heClassSolutionAt, Bindings.empty, Bindings.resolveFull,
        Bindings.eqClassOrdered, Bindings.eqVarsInOrder, Bindings.eqClass,
        Bindings.eqClassAux, Bindings.eqStep, Bindings.lookup,
        encodeModelAtom]
    rw [hlea, hhe]
    simp

end LeaBindingSemanticEquivAt

/-- Mirror chronology of the equality projections generated by matching: HE
stores oldest-first `(query, pattern)` edges, while LeaTTa stores newest-first
`eq pattern query` relations. -/
def LeaEqualityChronology (b : Bindings) (lb : Metta.Bindings) : Prop :=
  leaEqualityEdges lb =
    b.equalities.reverse.map fun (queryVar, patternVar) =>
      (patternVar, queryVar)

@[simp] theorem leaEqualityEdges_append (left right : Metta.Bindings) :
    leaEqualityEdges (left ++ right) =
      leaEqualityEdges left ++ leaEqualityEdges right := by
  induction left with
  | nil => rfl
  | cons rel rest ih =>
      cases rel <;> simp [leaEqualityEdges, ih]

@[simp] theorem leaEqualityEdges_reverse (lb : Metta.Bindings) :
    leaEqualityEdges lb.reverse = (leaEqualityEdges lb).reverse := by
  induction lb with
  | nil => rfl
  | cons rel rest ih =>
      cases rel <;>
        simp [List.reverse_cons, leaEqualityEdges, ih]

@[simp] theorem leaEqualityEdges_removeVal (lb : Metta.Bindings) (v : String) :
    leaEqualityEdges (Metta.Bindings.removeVal lb v) =
      leaEqualityEdges lb := by
  unfold Metta.Bindings.removeVal
  induction lb with
  | nil => rfl
  | cons rel rest ih =>
      cases rel with
      | val x value =>
          by_cases hx : x = v <;> simp [leaEqualityEdges, ih, hx]
      | eq x y =>
          simp [leaEqualityEdges, ih]

private theorem leaEqualityEdges_map_eq
    (edges : List (String × String)) :
    leaEqualityEdges
        (edges.map fun (queryVar, patternVar) =>
          Metta.BindingRel.eq patternVar queryVar) =
      edges.map fun (queryVar, patternVar) => (patternVar, queryVar) := by
  induction edges with
  | nil => rfl
  | cons edge rest ih =>
      rcases edge with ⟨queryVar, patternVar⟩
      simp [leaEqualityEdges, ih]

theorem leaEqualityChronology_canonical {b : Bindings}
    (hbare : NoBareVarAssignments b) :
    LeaEqualityChronology b (toLeaTTaMatchBindingsFull b) := by
  have hassign : leaEqualityEdges (toLeaTTaMatchBindings b) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    rintro ⟨x, y⟩ hmem
    rw [mem_leaEqualityEdges_iff] at hmem
    exact eq_not_mem_toLeaTTaMatchBindings hbare x y hmem
  unfold LeaEqualityChronology toLeaTTaMatchBindingsFull
  rw [leaEqualityEdges_append, hassign, List.append_nil]
  unfold toLeaTTaEqualityBindings
  rw [leaEqualityEdges_map_eq]

theorem LeaEqualityChronology.addValRaw
    {b : Bindings} {lb : Metta.Bindings} {v : String} {value : Atom}
    (hchron : LeaEqualityChronology b lb) :
    LeaEqualityChronology (b.assign v value)
      (Metta.Bindings.addValRaw lb v (encodeModelAtom value)) := by
  unfold LeaEqualityChronology at hchron ⊢
  simp only [Metta.Bindings.addValRaw, leaEqualityEdges,
    leaEqualityEdges_removeVal]
  simpa [Bindings.assign] using hchron

theorem LeaEqualityChronology.addEqRaw
    {b : Bindings} {lb : Metta.Bindings} {queryVar patternVar : String}
    (hchron : LeaEqualityChronology b lb)
    (hne : queryVar ≠ patternVar)
    (hnot : Metta.BindingRel.eq patternVar queryVar ∉ lb) :
    LeaEqualityChronology (b.addEquality queryVar patternVar)
      (Metta.Bindings.addEqRaw lb patternVar queryVar) := by
  have hne' : patternVar ≠ queryVar := hne.symm
  unfold LeaEqualityChronology at hchron ⊢
  rw [leaEqualityEdges_addEqRaw_of_not_mem lb hne' hnot]
  simpa [Bindings.addEquality, List.reverse_append] using
    congrArg (fun edges => (patternVar, queryVar) :: edges) hchron

private def leaEdgeOrder (acc : List String) (edge : String × String) : List String :=
  let acc := if acc.contains edge.2 then acc else acc ++ [edge.2]
  if acc.contains edge.1 then acc else acc ++ [edge.1]

private def heEdgeOrder (acc : List String) (edge : String × String) : List String :=
  let acc := if acc.contains edge.1 then acc else acc ++ [edge.1]
  if acc.contains edge.2 then acc else acc ++ [edge.2]

private theorem leaEqVarsInOrder_eq_edges (lb : Metta.Bindings) :
    Metta.Bindings.eqVarsInOrder lb =
      (leaEqualityEdges lb).reverse.foldl leaEdgeOrder [] := by
  induction lb with
  | nil => rfl
  | cons rel rest ih =>
      cases rel with
      | val x value =>
          calc
            Metta.Bindings.eqVarsInOrder (.val x value :: rest) =
                Metta.Bindings.eqVarsInOrder rest := by
              simp [Metta.Bindings.eqVarsInOrder, List.foldl_append]
            _ = (leaEqualityEdges rest).reverse.foldl leaEdgeOrder [] := ih
            _ = (leaEqualityEdges (.val x value :: rest)).reverse.foldl
                leaEdgeOrder [] := by rfl
      | eq x y =>
          calc
            Metta.Bindings.eqVarsInOrder (.eq x y :: rest) =
                leaEdgeOrder (Metta.Bindings.eqVarsInOrder rest) (x, y) := by
              simp [Metta.Bindings.eqVarsInOrder, leaEdgeOrder,
                List.foldl_append]
            _ = leaEdgeOrder
                ((leaEqualityEdges rest).reverse.foldl leaEdgeOrder [])
                (x, y) := by rw [ih]
            _ = (leaEqualityEdges (.eq x y :: rest)).reverse.foldl
                leaEdgeOrder [] := by
              simp [leaEqualityEdges, List.foldl_append]

private theorem mem_leaEdgeOrder_iff
    {acc : List String} {edge : String × String} {v : String} :
    v ∈ leaEdgeOrder acc edge ↔
      v ∈ acc ∨ v = edge.1 ∨ v = edge.2 := by
  rcases edge with ⟨left, right⟩
  simp only [leaEdgeOrder]
  split <;> split <;> simp_all <;> aesop

private theorem mem_leaEdgeOrderFold_iff
    (edges : List (String × String)) (acc : List String) (v : String) :
    v ∈ edges.foldl leaEdgeOrder acc ↔
      v ∈ acc ∨ v ∈ EqualityClosure.edgeNodes edges := by
  induction edges generalizing acc with
  | nil => simp [EqualityClosure.edgeNodes]
  | cons edge rest ih =>
      rw [List.foldl_cons, ih, mem_leaEdgeOrder_iff]
      rcases edge with ⟨left, right⟩
      simp only [EqualityClosure.edgeNodes, List.flatMap_cons,
        List.mem_append, List.mem_cons]
      aesop

/-- LeaTTa representative-order membership is exactly occurrence as an
explicit equality-edge endpoint. -/
theorem mem_leaEqVarsInOrder_iff
    {lb : Metta.Bindings} {v : String} :
    v ∈ Metta.Bindings.eqVarsInOrder lb ↔
      v ∈ EqualityClosure.edgeNodes (leaEqualityEdges lb) := by
  rw [leaEqVarsInOrder_eq_edges,
    mem_leaEdgeOrderFold_iff]
  simp [EqualityClosure.edgeNodes]

private theorem reachable_ne_endpoints_mem_edgeNodes_lea
    {lb : Metta.Bindings} {start finish : String}
    (hne : start ≠ finish)
    (hreach :
      (EqualityClosure.edgeGraph (leaEqualityEdges lb)).Reachable
        start finish) :
    start ∈ EqualityClosure.edgeNodes (leaEqualityEdges lb) ∧
      finish ∈ EqualityClosure.edgeNodes (leaEqualityEdges lb) := by
  apply hreach.elim
  intro walk
  cases walk with
  | nil => exact (hne rfl).elim
  | @cons start next finish hadj tail =>
      have hstart :
          start ∈ EqualityClosure.edgeNodes (leaEqualityEdges lb) := by
        rcases (EqualityClosure.edgeGraph_adj_iff.mp hadj).2 with
          hedge | hedge
        · exact EqualityClosure.left_mem_edgeNodes hedge
        · exact EqualityClosure.right_mem_edgeNodes hedge
      have hfinish :
          finish ∈ start ::
            EqualityClosure.edgeNodes (leaEqualityEdges lb) :=
        EqualityClosure.walk_support_subset_start_edgeNodes
          (SimpleGraph.Walk.cons hadj tail)
          (SimpleGraph.Walk.end_mem_support _)
      refine ⟨hstart, ?_⟩
      rcases List.mem_cons.mp hfinish with hfinish | hfinish
      · exact (hne hfinish.symm).elim
      · exact hfinish

/-- LeaTTa's stable ordered-class view contains exactly the variables in the
underlying undirected equality closure. -/
theorem mem_leaEqClassOrdered_iff
    {lb : Metta.Bindings} {start finish : String} :
    finish ∈ Metta.Bindings.eqClassOrdered lb start ↔
      finish ∈ Metta.Bindings.eqClass lb start := by
  unfold Metta.Bindings.eqClassOrdered
  generalize hfiltered :
      (Metta.Bindings.eqVarsInOrder lb).filter
          (fun w => (Metta.Bindings.eqClass lb start).contains w) = filtered
  cases filtered with
  | nil =>
      simp only [List.mem_singleton]
      constructor
      · rintro rfl
        rw [mem_leaEqClass_iff_reachable]
      · intro hclass
        by_contra hne
        have hne' : start ≠ finish := fun h => hne h.symm
        have hedge :
            finish ∈ EqualityClosure.edgeNodes (leaEqualityEdges lb) :=
          (reachable_ne_endpoints_mem_edgeNodes_lea hne'
            (mem_leaEqClass_iff_reachable.mp hclass)).2
        have horder : finish ∈ Metta.Bindings.eqVarsInOrder lb :=
          mem_leaEqVarsInOrder_iff.mpr hedge
        have hmemFilter : finish ∈
            (Metta.Bindings.eqVarsInOrder lb).filter
              (fun w => (Metta.Bindings.eqClass lb start).contains w) := by
          simp [horder, hclass]
        rw [hfiltered] at hmemFilter
        simp at hmemFilter
  | cons first rest =>
      constructor
      · intro hmem
        have hmem' : finish ∈
            (Metta.Bindings.eqVarsInOrder lb).filter
              (fun w => (Metta.Bindings.eqClass lb start).contains w) := by
          rw [hfiltered]
          exact hmem
        simpa using (List.mem_filter.mp hmem').2
      · intro hclass
        have horder : finish ∈ Metta.Bindings.eqVarsInOrder lb := by
          by_cases hEq : start = finish
          · subst finish
            have hfirst : first ∈
                (Metta.Bindings.eqVarsInOrder lb).filter
                  (fun w =>
                    (Metta.Bindings.eqClass lb start).contains w) := by
              rw [hfiltered]
              simp
            have hfirstOrder :
                first ∈ Metta.Bindings.eqVarsInOrder lb :=
              (List.mem_filter.mp hfirst).1
            have hfirstClass :
                first ∈ Metta.Bindings.eqClass lb start := by
              simpa using (List.mem_filter.mp hfirst).2
            by_cases hsf : start = first
            · simpa [hsf] using hfirstOrder
            · exact mem_leaEqVarsInOrder_iff.mpr
                (reachable_ne_endpoints_mem_edgeNodes_lea hsf
                  (mem_leaEqClass_iff_reachable.mp hfirstClass)).1
          · exact mem_leaEqVarsInOrder_iff.mpr
              (reachable_ne_endpoints_mem_edgeNodes_lea hEq
                (mem_leaEqClass_iff_reachable.mp hclass)).2
        have hmemFilter : finish ∈
            (Metta.Bindings.eqVarsInOrder lb).filter
              (fun w => (Metta.Bindings.eqClass lb start).contains w) := by
          simp [horder, hclass]
        rw [hfiltered] at hmemFilter
        exact hmemFilter

private theorem heEqVarsInOrder_eq_edges (b : Bindings) :
    b.eqVarsInOrder = b.equalities.foldl heEdgeOrder [] := by
  rfl

/-- The mirror chronology makes the independently implemented representative
orders exactly equal. -/
theorem eqVarsInOrder_eq_of_chronology {b : Bindings}
    {lb : Metta.Bindings} (hchron : LeaEqualityChronology b lb) :
    Metta.Bindings.eqVarsInOrder lb = b.eqVarsInOrder := by
  rw [leaEqVarsInOrder_eq_edges, heEqVarsInOrder_eq_edges, hchron]
  simp only [List.map_reverse, List.reverse_reverse, List.foldl_map]
  rfl

/-- Equality-set equivalence fixes class membership, while mirror chronology
fixes its stable order. Together they identify the complete ordered class. -/
theorem eqClassOrdered_eq_of_transport
    {b : Bindings} {lb : Metta.Bindings}
    (hequiv : LeaBindingRelEquiv b lb)
    (hchron : LeaEqualityChronology b lb) (v : String) :
    Metta.Bindings.eqClassOrdered lb v = b.eqClassOrdered v := by
  have horder := eqVarsInOrder_eq_of_chronology hchron
  have hfilter :
      (Metta.Bindings.eqVarsInOrder lb).filter
          (fun w => (Metta.Bindings.eqClass lb v).contains w) =
        b.eqVarsInOrder.filter (fun w => (b.eqClass v).contains w) := by
    rw [horder]
    apply List.filter_congr
    intro w _
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]
    exact (eqClass_mem_iff_of_leaBindingRelEquiv hequiv).symm
  unfold Metta.Bindings.eqClassOrdered Bindings.eqClassOrdered
  rw [hfilter]
  rfl

/-- General representative agreement. This is the order-sensitive crux behind
all concrete matcher/instantiation transport instances. -/
theorem eqRepresentative_eq_of_transport
    {b : Bindings} {lb : Metta.Bindings}
    (hequiv : LeaBindingRelEquiv b lb)
    (hchron : LeaEqualityChronology b lb) (v : String) :
    Metta.Bindings.eqRepresentative lb v = b.eqRepresentative v := by
  unfold Metta.Bindings.eqRepresentative Bindings.eqRepresentative
  rw [eqClassOrdered_eq_of_transport hequiv hchron]

/-- Construction-level transport invariant. Relation-set semantics and
representative chronology are independent fields; resolver agreement remains a
theorem derived from them. -/
structure LeaBindingTransport (b : Bindings) (lb : Metta.Bindings) : Prop where
  relations : LeaBindingRelEquiv b lb
  chronology : LeaEqualityChronology b lb

namespace LeaBindingTransport

theorem empty : LeaBindingTransport Bindings.empty Metta.Bindings.empty := by
  exact ⟨LeaBindingRelEquiv.empty, rfl⟩

theorem canonical {b : Bindings} (hbare : NoBareVarAssignments b) :
    LeaBindingTransport b (toLeaTTaMatchBindingsFull b) :=
  ⟨leaBindingRelEquiv_canonical hbare,
    leaEqualityChronology_canonical hbare⟩

end LeaBindingTransport

/-- Matcher witness carrying enough construction history to derive exact
equality-class and representative agreement. -/
def LeaMatcherTransportFull (query pattern : Atom) (hb : Bindings) : Prop :=
  ∃ lb,
    lb ∈ Metta.matchAtoms (encodeModelAtom pattern) (encodeModelAtom query) ∧
      LeaBindingTransport hb lb

/-- Matcher transport through the compositional equality-class/solution-theory
invariant. -/
def LeaMatcherSolutionTransport
    (query pattern : Atom) (hb : Bindings) : Prop :=
  ∃ lb,
    lb ∈ Metta.matchAtoms (encodeModelAtom pattern) (encodeModelAtom query) ∧
      LeaBindingSolutionEquiv hb lb

/-- Matcher transport through the strengthened compositional invariant.  This
is the induction-facing witness for recursive expression matching. -/
def LeaMatcherCongruenceTransport
    (query pattern : Atom) (hb : Bindings) : Prop :=
  ∃ lb,
    lb ∈ Metta.matchAtoms (encodeModelAtom pattern) (encodeModelAtom query) ∧
      LeaBindingCongruence hb lb

/-- Declarative leaf transport. Every non-expression constructor of the
official HE match relation is realized directly by LeaTTa's matcher. -/
theorem matchRel_leaf_transport
    {query pattern : Atom} {hb : Bindings}
    (hrel : MatchRel query pattern hb)
    (hdisj : VarsDisjoint query pattern)
    (hleaf : ¬ BothExpressions query pattern) :
    LeaMatcherTransportFull query pattern hb := by
  cases hrel with
  | symSym s =>
      refine ⟨[], ?_, LeaBindingTransport.empty⟩
      simp [Metta.matchAtoms, Metta.matchAtomsWith, encodeModelAtom]
  | varVar queryVar patternVar =>
      have hne : patternVar ≠ queryVar := by
        intro h
        subst patternVar
        exact hdisj queryVar
          (by simp [encodeModelAtom, Metta.Atom.vars])
          (by simp [encodeModelAtom, Metta.Atom.vars])
      refine ⟨[Metta.BindingRel.eq patternVar queryVar], ?_, ?_⟩
      · simp [Metta.matchAtoms, Metta.matchAtomsWith, encodeModelAtom, hne]
      · simpa [toLeaTTaMatchBindingsFull, toLeaTTaEqualityBindings,
          toLeaTTaMatchBindings, toLeaTTaMatchSubst,
          Metta.Bindings.ofSubst] using
          (LeaBindingTransport.canonical
            (b := (⟨[], [(queryVar, patternVar)]⟩ : Bindings))
            (by simp [NoBareVarAssignments]))
  | varNonVar hnonvar _hoccurs =>
      rename_i v
      cases pattern with
      | var w => simp [Atom.isVarB] at hnonvar
      | symbol s =>
          refine ⟨[Metta.BindingRel.val v (.sym s)], ?_, ?_⟩
          · have hloop := Metta.Bindings.hasLoop_singleton_val_of_not_mem
              v (.sym s) (by simp [Metta.Atom.vars])
            simp [Metta.matchAtoms, Metta.matchAtomsWith, encodeModelAtom, hloop]
          · simpa [toLeaTTaMatchBindingsFull, toLeaTTaEqualityBindings,
              toLeaTTaMatchBindings, toLeaTTaMatchSubst,
              Metta.Bindings.ofSubst, encodeModelAtom] using
              (LeaBindingTransport.canonical
                (b := (⟨[(v, .symbol s)], []⟩ : Bindings))
                (by simp [NoBareVarAssignments]))
      | grounded g =>
          refine ⟨[Metta.BindingRel.val v (.gnd (encodeModelGround g))], ?_, ?_⟩
          · have hloop := Metta.Bindings.hasLoop_singleton_val_of_not_mem
              v (.gnd (encodeModelGround g)) (by simp [Metta.Atom.vars])
            simp [Metta.matchAtoms, Metta.matchAtomsWith, encodeModelAtom, hloop]
          · simpa [toLeaTTaMatchBindingsFull, toLeaTTaEqualityBindings,
              toLeaTTaMatchBindings, toLeaTTaMatchSubst,
              Metta.Bindings.ofSubst, encodeModelAtom] using
              (LeaBindingTransport.canonical
                (b := (⟨[(v, .grounded g)], []⟩ : Bindings))
                (by simp [NoBareVarAssignments]))
      | expression es =>
          have hnotMem : v ∉ (encodeModelAtom (.expression es)).vars :=
            hdisj v (by simp [encodeModelAtom, Metta.Atom.vars])
          have hoccurs :
              Metta.Subst.occurs v (encodeModelAtom (.expression es)) = false :=
            occurs_eq_false_of_not_mem_vars v _ hnotMem
          change Metta.Subst.occurs v (.expr (encodeModelAtoms es)) = false at hoccurs
          refine ⟨[Metta.BindingRel.val v (.expr (encodeModelAtoms es))], ?_, ?_⟩
          · have hloop := Metta.Bindings.hasLoop_singleton_val_of_not_mem
              v (.expr (encodeModelAtoms es)) (by
                simpa [encodeModelAtom] using hnotMem)
            simp [Metta.matchAtoms, Metta.matchAtomsWith, encodeModelAtom, hoccurs, hloop]
          · simpa [toLeaTTaMatchBindingsFull, toLeaTTaEqualityBindings,
              toLeaTTaMatchBindings, toLeaTTaMatchSubst,
              Metta.Bindings.ofSubst, encodeModelAtom] using
              (LeaBindingTransport.canonical
                (b := (⟨[(v, .expression es)], []⟩ : Bindings))
                (by simp [NoBareVarAssignments]))
  | nonVarVar hnonvar _hoccurs =>
      rename_i v
      have hdisj' : VarsDisjoint (.var v) query := hdisj.symm
      cases query with
      | var w => simp [Atom.isVarB] at hnonvar
      | symbol s =>
          refine ⟨[Metta.BindingRel.val v (.sym s)], ?_, ?_⟩
          · have hloop := Metta.Bindings.hasLoop_singleton_val_of_not_mem
              v (.sym s) (by simp [Metta.Atom.vars])
            simp [Metta.matchAtoms, Metta.matchAtomsWith, encodeModelAtom, hloop]
          · simpa [toLeaTTaMatchBindingsFull, toLeaTTaEqualityBindings,
              toLeaTTaMatchBindings, toLeaTTaMatchSubst,
              Metta.Bindings.ofSubst, encodeModelAtom] using
              (LeaBindingTransport.canonical
                (b := (⟨[(v, .symbol s)], []⟩ : Bindings))
                (by simp [NoBareVarAssignments]))
      | grounded g =>
          refine ⟨[Metta.BindingRel.val v (.gnd (encodeModelGround g))], ?_, ?_⟩
          · have hloop := Metta.Bindings.hasLoop_singleton_val_of_not_mem
              v (.gnd (encodeModelGround g)) (by simp [Metta.Atom.vars])
            simp [Metta.matchAtoms, Metta.matchAtomsWith, encodeModelAtom, hloop]
          · simpa [toLeaTTaMatchBindingsFull, toLeaTTaEqualityBindings,
              toLeaTTaMatchBindings, toLeaTTaMatchSubst,
              Metta.Bindings.ofSubst, encodeModelAtom] using
              (LeaBindingTransport.canonical
                (b := (⟨[(v, .grounded g)], []⟩ : Bindings))
                (by simp [NoBareVarAssignments]))
      | expression es =>
          have hnotMem : v ∉ (encodeModelAtom (.expression es)).vars :=
            hdisj' v (by simp [encodeModelAtom, Metta.Atom.vars])
          have hoccurs :
              Metta.Subst.occurs v (encodeModelAtom (.expression es)) = false :=
            occurs_eq_false_of_not_mem_vars v _ hnotMem
          change Metta.Subst.occurs v (.expr (encodeModelAtoms es)) = false at hoccurs
          refine ⟨[Metta.BindingRel.val v (.expr (encodeModelAtoms es))], ?_, ?_⟩
          · have hloop := Metta.Bindings.hasLoop_singleton_val_of_not_mem
              v (.expr (encodeModelAtoms es)) (by
                simpa [encodeModelAtom] using hnotMem)
            simp [Metta.matchAtoms, Metta.matchAtomsWith, encodeModelAtom, hoccurs, hloop]
          · simpa [toLeaTTaMatchBindingsFull, toLeaTTaEqualityBindings,
              toLeaTTaMatchBindings, toLeaTTaMatchSubst,
              Metta.Bindings.ofSubst, encodeModelAtom] using
              (LeaBindingTransport.canonical
                (b := (⟨[(v, .expression es)], []⟩ : Bindings))
                (by simp [NoBareVarAssignments]))
  | grounded g =>
      refine ⟨[], ?_, LeaBindingTransport.empty⟩
      have hself :
          Metta.Atom.equiv (.gnd (encodeModelGround g))
            (.gnd (encodeModelGround g)) = true := by
        simpa [encodeModelAtom] using encodeModelAtom_grounded_equiv_self g
      simp [Metta.matchAtoms, Metta.matchAtomsWith, encodeModelAtom, hself]
  | @expr ls rs b hlist _ =>
      exact (hleaf ⟨ls, rs, rfl, rfl⟩).elim

/-- Executable leaf matcher transport follows immediately from HE matcher
soundness against the official declarative relation. -/
theorem matchAtoms_leaf_transport
    {query pattern : Atom} {hb : Bindings} {fuel : Nat}
    (hmatch : hb ∈ matchAtoms query pattern fuel)
    (hdisj : VarsDisjoint query pattern)
    (hleaf : ¬ BothExpressions query pattern) :
    LeaMatcherTransportFull query pattern hb :=
  matchRel_leaf_transport (matchAtoms_sound hmatch) hdisj hleaf

/-- Declarative leaf matching preserves the compositional solution invariant.
Unlike representative chronology, this is the induction interface used by
recursive matching and merge reconciliation. -/
theorem matchRel_leaf_solution_transport
    {query pattern : Atom} {hb : Bindings}
    (hrel : MatchRel query pattern hb)
    (hdisj : VarsDisjoint query pattern)
    (hleaf : ¬ BothExpressions query pattern) :
    LeaMatcherSolutionTransport query pattern hb := by
  obtain ⟨lb, hmatch, htransport⟩ :=
    matchRel_leaf_transport hrel hdisj hleaf
  exact ⟨lb, hmatch, LeaBindingSolutionEquiv.of_rel htransport.relations⟩

/-- Executable leaf matching inherits solution-theory transport from its
declarative soundness theorem. -/
theorem matchAtoms_leaf_solution_transport
    {query pattern : Atom} {hb : Bindings} {fuel : Nat}
    (hmatch : hb ∈ matchAtoms query pattern fuel)
    (hdisj : VarsDisjoint query pattern)
    (hleaf : ¬ BothExpressions query pattern) :
    LeaMatcherSolutionTransport query pattern hb :=
  matchRel_leaf_solution_transport (matchAtoms_sound hmatch) hdisj hleaf

/-- Declarative leaf matching establishes the full compositional invariant.
Every leaf witness has direct relation agreement, which is stronger than the
class-relative interface required by recursive matching. -/
theorem matchRel_leaf_congruence_transport
    {query pattern : Atom} {hb : Bindings}
    (hrel : MatchRel query pattern hb)
    (hdisj : VarsDisjoint query pattern)
    (hleaf : ¬ BothExpressions query pattern) :
    LeaMatcherCongruenceTransport query pattern hb := by
  obtain ⟨lb, hmatch, htransport⟩ :=
    matchRel_leaf_transport hrel hdisj hleaf
  exact ⟨lb, hmatch,
    LeaBindingCongruence.of_rel htransport.relations⟩

/-- Executable leaf matching inherits the strengthened transport from HE
matcher soundness. -/
theorem matchAtoms_leaf_congruence_transport
    {query pattern : Atom} {hb : Bindings} {fuel : Nat}
    (hmatch : hb ∈ matchAtoms query pattern fuel)
    (hdisj : VarsDisjoint query pattern)
    (hleaf : ¬ BothExpressions query pattern) :
    LeaMatcherCongruenceTransport query pattern hb :=
  matchRel_leaf_congruence_transport (matchAtoms_sound hmatch) hdisj hleaf

private theorem assignment_not_mem_of_lookup_none
    {assignments : List (String × Atom)} {v : String}
    (hlookup : List.lookup v assignments = none) (value : Atom) :
    (v, value) ∉ assignments := by
  induction assignments with
  | nil => simp
  | cons p rest ih =>
      rcases p with ⟨key, stored⟩
      cases hvk : (v == key) with
      | true => simp [List.lookup_cons, hvk] at hlookup
      | false =>
          have htail : List.lookup v rest = none := by
            simpa [List.lookup_cons, hvk] using hlookup
          intro hmem
          simp only [List.mem_cons, Prod.mk.injEq] at hmem
          rcases hmem with hhead | htailMem
          · rcases hhead with ⟨hvk', rfl⟩
            subst key
            simp at hvk
          · exact ih htail htailMem

/-- Fresh direct-value insertion preserves the order-free binding relation.
The value is required to be non-variable because matcher var/var constraints
travel through the explicit equality lane. -/
theorem LeaBindingRelEquiv.addValRaw_fresh
    {b : Bindings} {lb : Metta.Bindings} {v : String} {value : Atom}
    (hequiv : LeaBindingRelEquiv b lb)
    (hfresh : b.lookup v = none)
    (hnonvar : DeclMatchSpec.Atom.isVarB value = false) :
    LeaBindingRelEquiv (b.assign v value)
      (Metta.Bindings.addValRaw lb v (encodeModelAtom value)) := by
  constructor
  · intro x leaValue
    simp only [Metta.Bindings.addValRaw, Metta.Bindings.removeVal,
      List.mem_cons, List.mem_filter]
    rw [hequiv.values]
    simp only [Bindings.assign, Bindings.isBound, hfresh, Option.isSome_none,
      Bool.false_eq_true, if_false, List.mem_append, List.mem_singleton,
      Prod.mk.injEq]
    constructor
    · intro h
      rcases h with hnew | ⟨hold, hkeep⟩
      · cases hnew
        exact ⟨value, Or.inr ⟨rfl, rfl⟩, rfl⟩
      · rcases hold with ⟨heValue, hmem, rfl⟩
        exact ⟨heValue, Or.inl hmem, rfl⟩
    · rintro ⟨heValue, hmem | hnew, rfl⟩
      · right
        refine ⟨⟨heValue, hmem, rfl⟩, ?_⟩
        have hxv : x ≠ v := by
          intro hxv
          subst x
          exact assignment_not_mem_of_lookup_none hfresh heValue hmem
        simp [hxv]
      · rcases hnew with ⟨rfl, rfl⟩
        left
        cases heValue with
        | var w => simp [DeclMatchSpec.Atom.isVarB] at hnonvar
        | symbol s => rfl
        | grounded g => rfl
        | expression es => rfl
  · intro x y
    simpa [Metta.Bindings.addValRaw, Metta.Bindings.removeVal,
      Bindings.assign, Bindings.isBound, hfresh] using hequiv.equalities x y

/-- Appending a non-reflexive HE alias and prepending the opposite-oriented
LeaTTa alias preserve the same undirected relation set. -/
theorem LeaBindingRelEquiv.addEqRaw
    {b : Bindings} {lb : Metta.Bindings} {queryVar patternVar : String}
    (hequiv : LeaBindingRelEquiv b lb)
    (hne : queryVar ≠ patternVar) :
    LeaBindingRelEquiv (b.addEquality queryVar patternVar)
      (Metta.Bindings.addEqRaw lb patternVar queryVar) := by
  have hne' : patternVar ≠ queryVar := hne.symm
  constructor
  · intro v value
    rw [Metta.Bindings.val_mem_addEqRaw_iff]
    simpa [Bindings.addEquality] using hequiv.values v value
  · intro x y
    have hbase := hequiv.equalities x y
    simp only [Metta.Bindings.mem_addEqRaw_iff lb patternVar queryVar hne',
      List.mem_cons, Metta.BindingRel.eq.injEq, Bindings.addEquality,
      List.mem_append, Prod.mk.injEq]
    aesop

theorem LeaBindingTransport.addValRaw_fresh
    {b : Bindings} {lb : Metta.Bindings} {v : String} {value : Atom}
    (htransport : LeaBindingTransport b lb)
    (hfresh : b.lookup v = none)
    (hnonvar : DeclMatchSpec.Atom.isVarB value = false) :
    LeaBindingTransport (b.assign v value)
      (Metta.Bindings.addValRaw lb v (encodeModelAtom value)) :=
  ⟨htransport.relations.addValRaw_fresh hfresh hnonvar,
    htransport.chronology.addValRaw⟩

theorem LeaBindingTransport.addEqRaw
    {b : Bindings} {lb : Metta.Bindings} {queryVar patternVar : String}
    (htransport : LeaBindingTransport b lb)
    (hne : queryVar ≠ patternVar)
    (hnot : Metta.BindingRel.eq patternVar queryVar ∉ lb) :
    LeaBindingTransport (b.addEquality queryVar patternVar)
      (Metta.Bindings.addEqRaw lb patternVar queryVar) :=
  ⟨htransport.relations.addEqRaw hne,
    htransport.chronology.addEqRaw hne hnot⟩

private theorem addVarBinding_of_empty_class
    {lb : Metta.Bindings} {v : String} {value : Atom}
    (hnonvar : DeclMatchSpec.Atom.isVarB value = false)
    (hclass : Metta.Bindings.classValues lb v = []) :
    Metta.Bindings.addVarBinding lb v (encodeModelAtom value) =
      [Metta.Bindings.addValRaw lb v (encodeModelAtom value)] := by
  cases value <;>
    simp [Metta.Bindings.addVarBinding, hclass, encodeModelAtom,
      DeclMatchSpec.Atom.isVarB] at hnonvar ⊢

private theorem addVarEquality_of_empty_class
    {lb : Metta.Bindings} {patternVar queryVar : String}
    (hclass :
      Metta.Bindings.classValues
          (Metta.Bindings.addEqRaw lb patternVar queryVar) patternVar = []) :
    Metta.Bindings.addVarEquality lb patternVar queryVar =
      [Metta.Bindings.addEqRaw lb patternVar queryVar] := by
  simp only [Metta.Bindings.addVarEquality, hclass,
    Metta.Bindings.unifyValues]

/-- The executable fresh-value branch realizes the raw structural transport.
The class-value premise is explicit here; the general merge theorem will obtain
it from equality-closure correspondence. -/
theorem LeaBindingRelEquiv.addVarBinding_fresh
    {b : Bindings} {lb : Metta.Bindings} {v : String} {value : Atom}
    (hequiv : LeaBindingRelEquiv b lb)
    (hlookup : b.lookup v = none)
    (hnonvar : DeclMatchSpec.Atom.isVarB value = false)
    (hclass : Metta.Bindings.classValues lb v = []) :
    ∃ lb',
      lb' ∈ Metta.Bindings.addVarBinding lb v (encodeModelAtom value) ∧
        LeaBindingRelEquiv (b.assign v value) lb' := by
  refine ⟨Metta.Bindings.addValRaw lb v (encodeModelAtom value), ?_,
    hequiv.addValRaw_fresh hlookup hnonvar⟩
  rw [addVarBinding_of_empty_class hnonvar hclass]
  exact List.mem_singleton_self _

/-- The executable valueless-class equality branch realizes the raw alias
transport. -/
theorem LeaBindingRelEquiv.addVarEquality_valueless
    {b : Bindings} {lb : Metta.Bindings} {queryVar patternVar : String}
    (hequiv : LeaBindingRelEquiv b lb)
    (hne : queryVar ≠ patternVar)
    (hclass :
      Metta.Bindings.classValues
          (Metta.Bindings.addEqRaw lb patternVar queryVar) patternVar = []) :
    ∃ lb',
      lb' ∈ Metta.Bindings.addVarEquality lb patternVar queryVar ∧
        LeaBindingRelEquiv (b.addEquality queryVar patternVar) lb' := by
  refine ⟨Metta.Bindings.addEqRaw lb patternVar queryVar, ?_,
    hequiv.addEqRaw hne⟩
  rw [addVarEquality_of_empty_class hclass]
  exact List.mem_singleton_self _

theorem LeaBindingTransport.addVarBinding_fresh
    {b : Bindings} {lb : Metta.Bindings} {v : String} {value : Atom}
    (htransport : LeaBindingTransport b lb)
    (hlookup : b.lookup v = none)
    (hnonvar : DeclMatchSpec.Atom.isVarB value = false)
    (hclass : Metta.Bindings.classValues lb v = []) :
    ∃ lb',
      lb' ∈ Metta.Bindings.addVarBinding lb v (encodeModelAtom value) ∧
        LeaBindingTransport (b.assign v value) lb' := by
  refine ⟨Metta.Bindings.addValRaw lb v (encodeModelAtom value), ?_,
    htransport.addValRaw_fresh hlookup hnonvar⟩
  rw [addVarBinding_of_empty_class hnonvar hclass]
  exact List.mem_singleton_self _

theorem LeaBindingTransport.addVarEquality_valueless
    {b : Bindings} {lb : Metta.Bindings} {queryVar patternVar : String}
    (htransport : LeaBindingTransport b lb)
    (hne : queryVar ≠ patternVar)
    (hnot : Metta.BindingRel.eq patternVar queryVar ∉ lb)
    (hclass :
      Metta.Bindings.classValues
          (Metta.Bindings.addEqRaw lb patternVar queryVar) patternVar = []) :
    ∃ lb',
      lb' ∈ Metta.Bindings.addVarEquality lb patternVar queryVar ∧
        LeaBindingTransport (b.addEquality queryVar patternVar) lb' := by
  refine ⟨Metta.Bindings.addEqRaw lb patternVar queryVar, ?_,
    htransport.addEqRaw hne hnot⟩
  rw [addVarEquality_of_empty_class hclass]
  exact List.mem_singleton_self _

private theorem leaLookupVal_eq_none_of_no_value
    {lb : Metta.Bindings} {x : String}
    (hno : ∀ value, Metta.BindingRel.val x value ∉ lb) :
    Metta.Bindings.lookupVal lb x = none := by
  induction lb with
  | nil => rfl
  | cons relation rest ih =>
      have htail : ∀ value, Metta.BindingRel.val x value ∉ rest := by
        intro value hmem
        exact hno value (List.mem_cons_of_mem _ hmem)
      cases relation with
      | eq left right =>
          simpa [Metta.Bindings.lookupVal] using ih htail
      | val key value =>
          by_cases hx : x = key
          · subst key
            exact (hno value (by simp)).elim
          · simpa [Metta.Bindings.lookupVal, hx] using ih htail

private theorem no_leaValue_of_lookupVal_eq_none
    {lb : Metta.Bindings} {x : String}
    (hlookup : Metta.Bindings.lookupVal lb x = none) :
    ∀ value, Metta.BindingRel.val x value ∉ lb := by
  induction lb with
  | nil => simp
  | cons relation rest ih =>
      cases relation with
      | eq left right =>
          simpa [Metta.Bindings.lookupVal] using
            ih (by simpa [Metta.Bindings.lookupVal] using hlookup)
      | val key stored =>
          by_cases hx : x = key
          · subst key
            simp [Metta.Bindings.lookupVal] at hlookup
          · have htail : Metta.Bindings.lookupVal rest x = none := by
              simpa [Metta.Bindings.lookupVal, hx] using hlookup
            intro value hmem
            simp only [List.mem_cons, Metta.BindingRel.val.injEq] at hmem
            rcases hmem with hhead | htailMem
            · exact hx hhead.1
            · exact ih htail value htailMem

private theorem removeVal_eq_self_of_lookupVal_eq_none
    {lb : Metta.Bindings} {x : String}
    (hlookup : Metta.Bindings.lookupVal lb x = none) :
    Metta.Bindings.removeVal lb x = lb := by
  unfold Metta.Bindings.removeVal
  apply List.filter_eq_self.mpr
  intro relation hmem
  cases relation with
  | eq => simp
  | val key value =>
      have hne : key ≠ x := by
        intro h
        subst key
        exact no_leaValue_of_lookupVal_eq_none hlookup value hmem
      simp [hne]

/-- Raw insertion at a variable with no direct value presents the old binding
theory conjoined with the inserted value equation. -/
theorem leaBindingSatisfied_addValRaw_fresh_iff
    (valuation : String → Metta.Atom)
    (bindings : Metta.Bindings) (v : String) (value : Metta.Atom)
    (hlookup : Metta.Bindings.lookupVal bindings v = none) :
    LeaBindingSatisfied valuation
        (Metta.Bindings.addValRaw bindings v value) ↔
      LeaBindingSatisfied valuation bindings ∧
        valuation v = applyClassSolution valuation value := by
  have hremove : Metta.Bindings.removeVal bindings v = bindings :=
    removeVal_eq_self_of_lookupVal_eq_none hlookup
  rw [show Metta.Bindings.addValRaw bindings v value =
      [Metta.BindingRel.val v value] ++ bindings by
    simp [Metta.Bindings.addValRaw, hremove]]
  rw [leaBindingSatisfied_append_iff]
  simp [LeaBindingSatisfied, and_comm]

/-- Fresh raw value insertion preserves the compositional solution invariant.
The direct-lookup hypotheses express the normalized fresh branch on each
presentation; no relation ordering or representative premise is used. -/
theorem LeaBindingSolutionEquiv.addValRaw_fresh
    {b : Bindings} {lb : Metta.Bindings}
    {v : String} {value : Atom}
    (h : LeaBindingSolutionEquiv b lb)
    (hheLookup : b.lookup v = none)
    (hleaLookup : Metta.Bindings.lookupVal lb v = none) :
    LeaBindingSolutionEquiv
      (b.assign v value)
      (Metta.Bindings.addValRaw lb v (encodeModelAtom value)) := by
  have hremove : Metta.Bindings.removeVal lb v = lb :=
    removeVal_eq_self_of_lookupVal_eq_none hleaLookup
  have hbound : b.isBound v = false := by
    simp [Bindings.isBound, hheLookup]
  refine ⟨?_, ?_⟩
  · intro start finish
    have holdReach :
        (EqualityClosure.edgeGraph b.equalities).Reachable start finish ↔
          (EqualityClosure.edgeGraph (leaEqualityEdges lb)).Reachable start finish := by
      rw [← EqualityClosure.mem_eqClass_iff_reachable,
        ← mem_leaEqClass_iff_reachable]
      exact h.classes start finish
    rw [EqualityClosure.mem_eqClass_iff_reachable,
      mem_leaEqClass_iff_reachable]
    simpa [Bindings.assign, hbound, Metta.Bindings.addValRaw,
      hremove, leaEqualityEdges] using holdReach
  · intro valuation
    rw [heBindingSatisfied_assign_fresh_iff valuation hheLookup,
      leaBindingSatisfied_addValRaw_fresh_iff valuation lb v _ hleaLookup,
      h.solutions valuation]

/-- Fresh raw value insertion preserves the strengthened compositional
invariant.  Existing raw values retain their provenance because neither
engine changes the equality graph, and the new value is inserted by exact
translation at the same fresh key. -/
theorem LeaBindingCongruence.addValRaw_fresh
    {b : Bindings} {lb : Metta.Bindings}
    {v : String} {value : Atom}
    (h : LeaBindingCongruence b lb)
    (hheLookup : b.lookup v = none)
    (hleaLookup : Metta.Bindings.lookupVal lb v = none) :
    LeaBindingCongruence
      (b.assign v value)
      (Metta.Bindings.addValRaw lb v (encodeModelAtom value)) := by
  have hbound : b.isBound v = false := by
    simp [Bindings.isBound, hheLookup]
  have hremove : Metta.Bindings.removeVal lb v = lb :=
    removeVal_eq_self_of_lookupVal_eq_none hleaLookup
  have hclassMono : ∀ {left right : String},
      right ∈ b.eqClass left → right ∈ (b.assign v value).eqClass left := by
    intro left right hclass
    unfold Bindings.eqClass at hclass ⊢
    simpa [Bindings.assign, hbound] using hclass
  refine ⟨h.semantic.addValRaw_fresh hheLookup hleaLookup, ?_⟩
  constructor
  · intro key stored hmem
    simp only [Bindings.assign, hbound, Bool.false_eq_true, if_false,
      List.mem_append, List.mem_singleton, Prod.mk.injEq] at hmem
    rcases hmem with hold | ⟨rfl, rfl⟩
    · obtain ⟨leaKey, leaValue, hleaValue, hkeyClass, hatom⟩ :=
        h.classValues.1 key stored hold
      have hne : leaKey ≠ v := by
        intro heq
        subst leaKey
        exact no_leaValue_of_lookupVal_eq_none hleaLookup leaValue hleaValue
      refine ⟨leaKey, leaValue, ?_, hclassMono hkeyClass,
        HELeaAtomClassRel.mono hclassMono hatom⟩
      simp [Metta.Bindings.addValRaw, Metta.Bindings.removeVal,
        hleaValue, hne]
    · refine ⟨key, encodeModelAtom stored, ?_, ?_,
        HELeaAtomClassRel.translation (b.assign key stored) stored⟩
      · simp [Metta.Bindings.addValRaw]
      · rw [EqualityClosure.mem_eqClass_iff_reachable]
  · intro leaKey leaValue hmem
    simp only [Metta.Bindings.addValRaw, hremove, List.mem_cons,
      Metta.BindingRel.val.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | hold
    · refine ⟨leaKey, value, ?_, ?_,
        HELeaAtomClassRel.translation (b.assign leaKey value) value⟩
      · simp [Bindings.assign, hbound]
      · rw [EqualityClosure.mem_eqClass_iff_reachable]
    · obtain ⟨key, stored, hstored, hkeyClass, hatom⟩ :=
        h.classValues.2 leaKey leaValue hold
      refine ⟨key, stored, ?_, hclassMono hkeyClass,
        HELeaAtomClassRel.mono hclassMono hatom⟩
      simp [Bindings.assign, hbound, hstored]

/-- The executable fresh-value branch preserves equality classes and complete
solution theory. -/
theorem LeaBindingSolutionEquiv.addVarBinding_fresh
    {b : Bindings} {lb : Metta.Bindings}
    {v : String} {value : Atom}
    (h : LeaBindingSolutionEquiv b lb)
    (hheLookup : b.lookup v = none)
    (hleaLookup : Metta.Bindings.lookupVal lb v = none)
    (hnonvar : DeclMatchSpec.Atom.isVarB value = false)
    (hclass : Metta.Bindings.classValues lb v = []) :
    ∃ lb',
      lb' ∈ Metta.Bindings.addVarBinding lb v (encodeModelAtom value) ∧
        LeaBindingSolutionEquiv (b.assign v value) lb' := by
  refine ⟨Metta.Bindings.addValRaw lb v (encodeModelAtom value), ?_,
    h.addValRaw_fresh hheLookup hleaLookup⟩
  rw [addVarBinding_of_empty_class hnonvar hclass]
  exact List.mem_singleton_self _

/-- The executable fresh-value branch preserves class-indexed raw provenance
as well as equality closure and complete solution theory. -/
theorem LeaBindingCongruence.addVarBinding_fresh
    {b : Bindings} {lb : Metta.Bindings}
    {v : String} {value : Atom}
    (h : LeaBindingCongruence b lb)
    (hheLookup : b.lookup v = none)
    (hleaLookup : Metta.Bindings.lookupVal lb v = none)
    (hnonvar : DeclMatchSpec.Atom.isVarB value = false)
    (hclass : Metta.Bindings.classValues lb v = []) :
    ∃ lb',
      lb' ∈ Metta.Bindings.addVarBinding lb v (encodeModelAtom value) ∧
        LeaBindingCongruence (b.assign v value) lb' := by
  refine ⟨Metta.Bindings.addValRaw lb v (encodeModelAtom value), ?_,
    h.addValRaw_fresh hheLookup hleaLookup⟩
  rw [addVarBinding_of_empty_class hnonvar hclass]
  exact List.mem_singleton_self _

/-- The executable valueless equality branch preserves equality classes and
complete solution theory without any chronology premise. -/
theorem LeaBindingSolutionEquiv.addVarEquality_valueless
    {b : Bindings} {lb : Metta.Bindings}
    {queryVar patternVar : String}
    (h : LeaBindingSolutionEquiv b lb)
    (hne : queryVar ≠ patternVar)
    (hclass :
      Metta.Bindings.classValues
          (Metta.Bindings.addEqRaw lb patternVar queryVar) patternVar = []) :
    ∃ lb',
      lb' ∈ Metta.Bindings.addVarEquality lb patternVar queryVar ∧
        LeaBindingSolutionEquiv
          (b.addEquality queryVar patternVar) lb' := by
  refine ⟨Metta.Bindings.addEqRaw lb patternVar queryVar, ?_, h.addEqRaw hne⟩
  rw [addVarEquality_of_empty_class hclass]
  exact List.mem_singleton_self _

/-- The executable valueless equality branch preserves the strengthened
compositional invariant without exposing relation order or representative
chronology. -/
theorem LeaBindingCongruence.addVarEquality_valueless
    {b : Bindings} {lb : Metta.Bindings}
    {queryVar patternVar : String}
    (h : LeaBindingCongruence b lb)
    (hne : queryVar ≠ patternVar)
    (hclass :
      Metta.Bindings.classValues
          (Metta.Bindings.addEqRaw lb patternVar queryVar) patternVar = []) :
    ∃ lb',
      lb' ∈ Metta.Bindings.addVarEquality lb patternVar queryVar ∧
        LeaBindingCongruence
          (b.addEquality queryVar patternVar) lb' := by
  refine ⟨Metta.Bindings.addEqRaw lb patternVar queryVar, ?_,
    h.addEqRaw hne⟩
  rw [addVarEquality_of_empty_class hclass]
  exact List.mem_singleton_self _

private theorem leaValue_mem_of_lookupVal_eq_some
    {lb : Metta.Bindings} {x : String} {value : Metta.Atom}
    (hlookup : Metta.Bindings.lookupVal lb x = some value) :
    Metta.BindingRel.val x value ∈ lb := by
  induction lb with
  | nil => simp [Metta.Bindings.lookupVal] at hlookup
  | cons relation rest ih =>
      cases relation with
      | eq left right =>
          exact List.mem_cons_of_mem _
            (ih (by simpa [Metta.Bindings.lookupVal] using hlookup))
      | val key stored =>
          by_cases hx : x = key
          · subst key
            simp [Metta.Bindings.lookupVal] at hlookup
            subst stored
            simp
          · exact List.mem_cons_of_mem _
              (ih (by simpa [Metta.Bindings.lookupVal, hx] using hlookup))

private theorem leaBindingSatisfied_eq_of_reachable
    {valuation : String → Metta.Atom} {lb : Metta.Bindings}
    {left right : String}
    (hsatisfied : LeaBindingSatisfied valuation lb)
    (hreach :
      (EqualityClosure.edgeGraph (leaEqualityEdges lb)).Reachable
        left right) :
    valuation left = valuation right := by
  apply hreach.elim
  intro walk
  induction walk with
  | nil => rfl
  | @cons start next finish hadj tail ih =>
      have hstep : valuation start = valuation next := by
        rcases (EqualityClosure.edgeGraph_adj_iff.mp hadj).2 with
          hedge | hedge
        · exact hsatisfied.2 start next
            (mem_leaEqualityEdges_iff.mp hedge)
        · exact (hsatisfied.2 next start
            (mem_leaEqualityEdges_iff.mp hedge)).symm
      exact hstep.trans (ih tail.reachable)

/-- A satisfying valuation is constant on every repaired-LeaTTa equality
class, independently of edge orientation and spanning-tree presentation. -/
theorem LeaBindingSatisfied.eq_of_mem_eqClass
    {valuation : String → Metta.Atom} {bindings : Metta.Bindings}
    (hsatisfied : LeaBindingSatisfied valuation bindings)
    {left right : String}
    (hmem : right ∈ Metta.Bindings.eqClass bindings left) :
    valuation left = valuation right := by
  apply leaBindingSatisfied_eq_of_reachable hsatisfied
  exact mem_leaEqClass_iff_reachable.mp hmem

/-- One proper dependency between repaired-LeaTTa equality classes.  The
normalization invariant makes a special bare-variable-alias exception
unnecessary: such aliases are represented by `eq`, not `val`. -/
def LeaClassDepends
    (bindings : Metta.Bindings) (source target : String) : Prop :=
  ∃ key value dependency,
    Metta.BindingRel.val key value ∈ bindings ∧
    source ∈ Metta.Bindings.eqClass bindings key ∧
    dependency ∈ value.vars ∧
    target ∈ Metta.Bindings.eqClass bindings dependency

/-- Representation-independent semantic loop freedom for normalized
repaired-LeaTTa bindings. -/
def LeaSemanticLoopFree (bindings : Metta.Bindings) : Prop :=
  ∀ name, ¬Relation.TransGen (LeaClassDepends bindings) name name

/-- Class-relative value representation preserves every variable occurrence,
possibly changing its spelling within the same equality class. -/
theorem HELeaAtomClassRel.occurrence
    {b : Bindings} {value : Atom} {leaValue : Metta.Atom} {name : String}
    (hrel : HELeaAtomClassRel b value leaValue) (hoccurs : AtomOccurs value name) :
    ∃ leaName, leaName ∈ leaValue.vars ∧ leaName ∈ b.eqClass name := by
  induction hoccurs generalizing leaValue with
  | var name =>
      cases hrel with
      | «variable» hclass => exact ⟨_, by simp [Metta.Atom.vars], hclass⟩
  | @expression atoms atom name hmem hoccurs ih =>
      cases hrel with
      | @expression _ leaAtoms hrels =>
          have hchild : ∃ leaChild ∈ leaAtoms, HELeaAtomClassRel b atom leaChild := by
            induction hrels with
            | nil => simp at hmem
            | @cons head leaHead tail leaTail hhead htail ihtail =>
                rcases List.mem_cons.mp hmem with heq | hmem
                · subst atom
                  exact ⟨leaHead, by simp, hhead⟩
                · obtain ⟨child, hmember, hrel⟩ := ihtail hmem
                  exact ⟨child, by simp [hmember], hrel⟩
          obtain ⟨leaChild, hchild, hrel⟩ := hchild
          obtain ⟨leaName, hname, hclass⟩ := ih hrel
          refine ⟨leaName, ?_, hclass⟩
          simp only [Metta.Atom.vars, List.mem_flatten, List.mem_map]
          exact ⟨leaChild.vars, ⟨leaChild, hchild, rfl⟩, hname⟩

/-- Class-value congruence transports proper HE dependencies into LeaTTa's
independent dependency graph. -/
theorem LeaBindingCongruence.leaClassDepends_of_he
    {b : Bindings} {lb : Metta.Bindings} (h : LeaBindingCongruence b lb)
    {source target : String} (hdep : ClassDepends b source target) :
    LeaClassDepends lb source target := by
  obtain ⟨key, value, dependency, hstored, hsource, hoccurs, htarget, _⟩ := hdep
  obtain ⟨leaKey, leaValue, hleaStored, hkey, hvalue⟩ := h.classValues.1 key value hstored
  obtain ⟨leaDependency, hleaOccurs, hdepClass⟩ := hvalue.occurrence hoccurs
  refine ⟨leaKey, leaValue, leaDependency, hleaStored, ?_, hleaOccurs, ?_⟩
  · apply (h.semantic.classes leaKey source).mp
    exact (EqualityClosure.eqClass_mem_iff_of_reachable
      (EqualityClosure.mem_eqClass_iff_reachable.mp hkey)).mp hsource
  · apply (h.semantic.classes leaDependency target).mp
    exact (EqualityClosure.eqClass_mem_iff_of_reachable
      (EqualityClosure.mem_eqClass_iff_reachable.mp hdepClass)).mp htarget

/-- Semantic acyclicity transports from LeaTTa to HE without requiring an
agreement between the engines' concrete resolution algorithms. -/
theorem LeaBindingCongruence.heSemanticLoopFree
    {b : Bindings} {lb : Metta.Bindings} (h : LeaBindingCongruence b lb)
    (hfree : LeaSemanticLoopFree lb) : SemanticLoopFree b := by
  intro name hcycle
  apply hfree name
  exact Relation.TransGen.mono (fun _ _ hstep => h.leaClassDepends_of_he hstep)
    name name hcycle

theorem LeaBindingCongruence.heHasLoop_false
    {b : Bindings} {lb : Metta.Bindings} (h : LeaBindingCongruence b lb)
    (hfree : LeaSemanticLoopFree lb) : b.hasLoop = false :=
  (hasLoop_eq_false_iff_semanticLoopFree b).mpr (h.heSemanticLoopFree hfree)

namespace ClassDependencyControls

/-- A raw class can carry a cyclic value hidden behind its first, harmless
value. Distinct assignment keys and normalized constructors do not exclude
this inconsistency. -/
def ignoredClassValue : Metta.Bindings :=
  [.val "x" (.sym "a"), .val "y" (.expr [.sym "f", .var "y"]), .eq "y" "x"]

theorem ignoredClassValue_nonvariable : LeaAssignmentsNonVariable ignoredClassValue := by
  intro key target hmem
  simp [ignoredClassValue] at hmem

theorem ignoredClassValue_irreflexive : LeaEqualitiesIrreflexive ignoredClassValue := by
  intro key hmem
  simp [ignoredClassValue] at hmem
  obtain ⟨rfl, hfalse⟩ := hmem
  exact (by decide : ("y" : String) ≠ "x") hfalse

theorem ignoredClassValue_unique_keys :
    (ignoredClassValue.filterMap fun relation => match relation with
      | .val key _ => some key
      | .eq _ _ => none).Nodup := by decide

theorem ignoredClassValue_no_runtime_loop : ignoredClassValue.hasLoop = false := by
  apply Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.hasLoop_false_of_resolveAtomAux_some
  · rfl
  · intro key hkey
    have hvars : Metta.Bindings.vars ignoredClassValue = ["x", "y"] := by
      simp [ignoredClassValue, Metta.Bindings.vars, Metta.Atom.vars, List.eraseDups_cons]
    rw [hvars] at hkey
    have hfuel (name : String) :
        Metta.Bindings.resolutionFuel ignoredClassValue (.var name) = 9 := by
      simp [ignoredClassValue, Metta.Bindings.resolutionFuel,
        Metta.Bindings.relationResolutionFuel, Metta.Atom.size]
    rcases List.mem_cons.mp hkey with rfl | hkey
    · exact ⟨.sym "a", by rw [hfuel]; rfl⟩
    · have heq : key = "y" := List.mem_singleton.mp hkey
      subst key
      exact ⟨.sym "a", by rw [hfuel]; rfl⟩

theorem ignoredClassValue_semantic_cycle : ¬LeaSemanticLoopFree ignoredClassValue := by
  intro hfree
  apply hfree "y"
  apply Relation.TransGen.single
  refine ⟨"y", .expr [.sym "f", .var "y"], "y", ?_, ?_, ?_, ?_⟩
  · simp [ignoredClassValue]
  · decide
  · simp [Metta.Atom.vars]
  · decide


end ClassDependencyControls

/-- Every semantic dependency edge in a satisfiable normalized LeaTTa record
strictly decreases the size of the satisfying valuation. -/
theorem size_valuation_lt_of_leaClassDepends
    {bindings : Metta.Bindings} {valuation : String → Metta.Atom}
    (hnonvariable : LeaAssignmentsNonVariable bindings)
    (hsatisfied : LeaBindingSatisfied valuation bindings)
    {source target : String}
    (hdepends : LeaClassDepends bindings source target) :
    (valuation target).size < (valuation source).size := by
  rcases hdepends with
    ⟨key, value, dependency, hassignment, hsource,
      hdependency, htarget⟩
  have hvalueNonvariable : ∀ other, value ≠ .var other := by
    intro other heq
    subst value
    exact hnonvariable key other hassignment
  have hproper := size_valuation_lt_apply_of_mem_vars_nonvariable
    valuation hvalueNonvariable hdependency
  have hsourceEq := hsatisfied.eq_of_mem_eqClass hsource
  have htargetEq := hsatisfied.eq_of_mem_eqClass htarget
  have hassignmentEq := hsatisfied.1 key value hassignment
  calc
    (valuation target).size = (valuation dependency).size :=
      congrArg Metta.Atom.size htargetEq.symm
    _ < (applyClassSolution valuation value).size := hproper
    _ = (valuation key).size := congrArg Metta.Atom.size hassignmentEq.symm
    _ = (valuation source).size := congrArg Metta.Atom.size hsourceEq

/-- Satisfiability rules out semantic dependency cycles for every normalized
repaired-LeaTTa binding record.  This deliberately excludes the satisfiable
bare-variable cycle canary, which violates `LeaAssignmentsNonVariable`. -/
theorem leaSemanticLoopFree_of_satisfied_nonvariable
    {bindings : Metta.Bindings} {valuation : String → Metta.Atom}
    (hsatisfied : LeaBindingSatisfied valuation bindings)
    (hnonvariable : LeaAssignmentsNonVariable bindings) :
    LeaSemanticLoopFree bindings := by
  intro name hcycle
  have hstrict : ∀ {source target},
      LeaClassDepends bindings source target →
        (valuation target).size < (valuation source).size :=
    fun hdepends =>
      size_valuation_lt_of_leaClassDepends
        hnonvariable hsatisfied hdepends
  have hstrictPath : ∀ {source target},
      Relation.TransGen (LeaClassDepends bindings) source target →
        (valuation target).size < (valuation source).size := by
    intro source target path
    induction path with
    | single hstep => exact hstrict hstep
    | tail hstep hlast ih => exact (hstrict hlast).trans ih
  exact (Nat.lt_irrefl _ (hstrictPath hcycle))

/-- Every value carried by a repaired-LeaTTa equality class is an equation for
every satisfying valuation, independently of class-member order. -/
theorem leaBindingSatisfied_classValue
    {valuation : String → Metta.Atom} {lb : Metta.Bindings}
    {v : String} {value : Metta.Atom}
    (hsatisfied : LeaBindingSatisfied valuation lb)
    (hvalue : value ∈ Metta.Bindings.classValues lb v) :
    valuation v = applyClassSolution valuation value := by
  unfold Metta.Bindings.classValues at hvalue
  obtain ⟨key, hkey, hlookup⟩ := List.mem_filterMap.mp hvalue
  have hreach :
      (EqualityClosure.edgeGraph (leaEqualityEdges lb)).Reachable v key := by
    rw [← mem_leaEqClass_iff_reachable]
    exact mem_leaEqClassOrdered_iff.mp hkey
  have hbinding : Metta.BindingRel.val key value ∈ lb :=
    leaValue_mem_of_lookupVal_eq_some hlookup
  exact (leaBindingSatisfied_eq_of_reachable hsatisfied hreach).trans
    (hsatisfied.1 key value hbinding)

private theorem leaLookupVal_eq_none_of_classValues_eq_nil
    {lb : Metta.Bindings} {v : String}
    (hvalues : Metta.Bindings.classValues lb v = []) :
    Metta.Bindings.lookupVal lb v = none := by
  unfold Metta.Bindings.classValues at hvalues
  apply List.filterMap_eq_nil_iff.mp hvalues v
  apply mem_leaEqClassOrdered_iff.mpr
  rw [mem_leaEqClass_iff_reachable]

theorem leaClassValue_noFloat
    {lb : Metta.Bindings} (hbindingsNoFloat : LeaBindingsNoFloat lb)
    {v : String} {value : Metta.Atom}
    (hvalue : value ∈ Metta.Bindings.classValues lb v) :
    MettaAtomNoFloat value := by
  unfold Metta.Bindings.classValues at hvalue
  obtain ⟨key, _hkey, hlookup⟩ := List.mem_filterMap.mp hvalue
  exact hbindingsNoFloat key value
    (leaValue_mem_of_lookupVal_eq_some hlookup)

private theorem leaAddVarBinding_nonVar_solution_iff
    (valuation : String → Metta.Atom)
    {bindings out : Metta.Bindings} {v : String} {value : Metta.Atom}
    (hnonvar : ∀ other, value ≠ .var other)
    (hbindingsNoFloat : LeaBindingsNoFloat bindings)
    (hvalueNoFloat : MettaAtomNoFloat value)
    (hout : out ∈ Metta.Bindings.addVarBinding bindings v value) :
    LeaBindingSatisfied valuation out ↔
      LeaBindingSatisfied valuation bindings ∧
        valuation v = applyClassSolution valuation value := by
  have hopen :
      Metta.Bindings.addVarBinding bindings v value =
        match Metta.Bindings.classValues bindings v with
        | [] => [Metta.Bindings.addValRaw bindings v value]
        | values =>
            match Metta.Bindings.unifyValues (values ++ [value]) with
            | none => []
            | some [] => [bindings]
            | some (_ :: _) =>
                match wholeBindingReconciliation bindings [(.var v, value)] with
                | none => []
                | some sigma =>
                    [Metta.Bindings.rebuildFromReconciliation
                      bindings bindings [(.var v, value)] sigma] := by
    cases value with
    | var other => exact (hnonvar other rfl).elim
    | sym | gnd | expr => rfl
  rw [hopen] at hout
  cases hvalues : Metta.Bindings.classValues bindings v with
  | nil =>
      rw [hvalues] at hout
      simp only [List.mem_singleton] at hout
      subst out
      exact leaBindingSatisfied_addValRaw_fresh_iff
        valuation bindings v value
        (leaLookupVal_eq_none_of_classValues_eq_nil hvalues)
  | cons first rest =>
      rw [hvalues] at hout
      simp only at hout
      cases hunify : Metta.Bindings.unifyValues
          ((first :: rest) ++ [value]) with
      | none =>
          rw [hunify] at hout
          simp at hout
      | some result =>
          cases result with
          | nil =>
              rw [hunify] at hout
              simp only [List.mem_singleton] at hout
              subst out
              constructor
              · intro hsatisfied
                refine ⟨hsatisfied, ?_⟩
                have hfirst :
                    first ∈ Metta.Bindings.classValues bindings v := by
                  rw [hvalues]
                  simp
                have hnoFloat : ∀ item ∈
                    (first :: rest) ++ [value],
                    MettaAtomNoFloat item := by
                  intro item hmem
                  simp only [List.mem_append] at hmem
                  rcases hmem with hmem | hmem
                  · exact leaClassValue_noFloat hbindingsNoFloat
                      (by rw [hvalues]; exact hmem)
                  · have hitem : item = value := List.mem_singleton.mp hmem
                    subst item
                    exact hvalueNoFloat
                have hequations :
                    MettaEquationsSatisfied valuation
                      (mettaClassValueEquations
                        ((first :: rest) ++ [value])) :=
                  (unifyValues_solution_iff valuation hnoFloat hunify).mp
                    (by simp [MettaConstraintsSatisfied])
                have hlast :
                    applyClassSolution valuation first =
                      applyClassSolution valuation value := by
                  exact hequations (first, value) (by
                    simp [mettaClassValueEquations])
                exact
                  (leaBindingSatisfied_classValue
                    hsatisfied hfirst).trans hlast
              · exact And.left
          | cons binding restResult =>
              rw [hunify] at hout
              cases hreconcile : wholeBindingReconciliation bindings
                  [(.var v, value)] with
              | none =>
                  rw [hreconcile] at hout
                  simp at hout
              | some sigma =>
                  rw [hreconcile] at hout
                  simp only [List.mem_singleton] at hout
                  subst out
                  have hextraNoFloat : ∀ equation ∈ [(.var v, value)],
                      MettaAtomNoFloat equation.1 ∧
                        MettaAtomNoFloat equation.2 := by
                    intro equation hmem
                    simp only [List.mem_singleton] at hmem
                    subst equation
                    exact ⟨by simp [MettaAtomNoFloat], hvalueNoFloat⟩
                  rw [rebuildFromReconciliation_solution_iff valuation
                    hbindingsNoFloat hextraNoFloat hreconcile]
                  simpa [MettaEquationsSatisfied,
                    MettaEquationSatisfied, applyClassSolution] using
                    (rebuildBindingsFromUnifier_solution_iff valuation
                      hbindingsNoFloat hextraNoFloat hreconcile)

/-- Every successful repaired-LeaTTa value insertion presents exactly the old
binding theory conjoined with the requested value equation. This covers fresh,
already-solved, alias, and whole-system reconciliation branches. -/
theorem leaAddVarBinding_solution_iff
    (valuation : String → Metta.Atom)
    {bindings out : Metta.Bindings} {v : String} {value : Metta.Atom}
    (hbindingsNoFloat : LeaBindingsNoFloat bindings)
    (hvalueNoFloat : MettaAtomNoFloat value)
    (hout : out ∈ Metta.Bindings.addVarBinding bindings v value) :
    LeaBindingSatisfied valuation out ↔
      LeaBindingSatisfied valuation bindings ∧
        valuation v = applyClassSolution valuation value := by
  cases value with
  | var other =>
      simpa [Metta.Bindings.addVarBinding, applyClassSolution] using
        (leaAddVarEquality_solution_iff valuation hbindingsNoFloat hout)
  | sym symbol =>
      exact leaAddVarBinding_nonVar_solution_iff valuation
        (by intro other h; cases h) hbindingsNoFloat hvalueNoFloat hout
  | gnd ground =>
      exact leaAddVarBinding_nonVar_solution_iff valuation
        (by intro other h; cases h) hbindingsNoFloat hvalueNoFloat hout
  | expr atoms =>
      exact leaAddVarBinding_nonVar_solution_iff valuation
        (by intro other h; cases h) hbindingsNoFloat hvalueNoFloat hout

theorem leaBindingsNoFloat_addEqRaw
    {bindings : Metta.Bindings} {left right : String}
    (hbindingsNoFloat : LeaBindingsNoFloat bindings) :
    LeaBindingsNoFloat
      (Metta.Bindings.addEqRaw bindings left right) := by
  intro key value hmem
  exact hbindingsNoFloat key value
    ((Metta.Bindings.val_mem_addEqRaw_iff
      bindings left right key value).mp hmem)

theorem leaBindingsNoFloat_addValRaw
    {bindings : Metta.Bindings} {v : String} {value : Metta.Atom}
    (hbindingsNoFloat : LeaBindingsNoFloat bindings)
    (hvalueNoFloat : MettaAtomNoFloat value) :
    LeaBindingsNoFloat
      (Metta.Bindings.addValRaw bindings v value) := by
  intro key stored hmem
  simp only [Metta.Bindings.addValRaw, List.mem_cons,
    Metta.BindingRel.val.injEq] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | hmem
  · exact hvalueNoFloat
  · apply hbindingsNoFloat key stored
    exact (List.mem_filter.mp hmem).1

/-- Alias insertion preserves the host-float-free fragment on every
successful branch. -/
theorem leaAddVarEquality_result_noFloat
    {bindings out : Metta.Bindings} {left right : String}
    (hbindingsNoFloat : LeaBindingsNoFloat bindings)
    (hout : out ∈ Metta.Bindings.addVarEquality bindings left right) :
    LeaBindingsNoFloat out := by
  cases hunify : Metta.Bindings.unifyValues
      (Metta.Bindings.classValues
        (Metta.Bindings.addEqRaw bindings left right) left) with
  | none =>
      simp [Metta.Bindings.addVarEquality, hunify] at hout
  | some result =>
      cases result with
      | nil =>
          simp [Metta.Bindings.addVarEquality, hunify] at hout
          subst out
          exact leaBindingsNoFloat_addEqRaw hbindingsNoFloat
      | cons binding rest =>
          cases hreconcile : wholeBindingReconciliation bindings
              [(.var left, .var right)] with
          | none =>
              simp [Metta.Bindings.addVarEquality, hunify,
                hreconcile] at hout
          | some sigma =>
              simp [Metta.Bindings.addVarEquality, hunify,
                hreconcile] at hout
              subst out
              exact rebuildFromReconciliation_noFloat
                (wholeBindingReconciliation_result_noFloat
                  hbindingsNoFloat (by
                    intro equation hmem
                    simp only [List.mem_singleton] at hmem
                    subst equation
                    simp [MettaAtomNoFloat]) hreconcile)

private theorem leaAddVarBinding_nonVar_result_noFloat
    {bindings out : Metta.Bindings} {v : String} {value : Metta.Atom}
    (hnonvar : ∀ other, value ≠ .var other)
    (hbindingsNoFloat : LeaBindingsNoFloat bindings)
    (hvalueNoFloat : MettaAtomNoFloat value)
    (hout : out ∈ Metta.Bindings.addVarBinding bindings v value) :
    LeaBindingsNoFloat out := by
  have hopen :
      Metta.Bindings.addVarBinding bindings v value =
        match Metta.Bindings.classValues bindings v with
        | [] => [Metta.Bindings.addValRaw bindings v value]
        | values =>
            match Metta.Bindings.unifyValues (values ++ [value]) with
            | none => []
            | some [] => [bindings]
            | some (_ :: _) =>
                match wholeBindingReconciliation bindings [(.var v, value)] with
                | none => []
                | some sigma =>
                    [Metta.Bindings.rebuildFromReconciliation
                      bindings bindings [(.var v, value)] sigma] := by
    cases value with
    | var other => exact (hnonvar other rfl).elim
    | sym | gnd | expr => rfl
  rw [hopen] at hout
  cases hvalues : Metta.Bindings.classValues bindings v with
  | nil =>
      rw [hvalues] at hout
      simp only [List.mem_singleton] at hout
      subst out
      exact leaBindingsNoFloat_addValRaw
        hbindingsNoFloat hvalueNoFloat
  | cons first rest =>
      rw [hvalues] at hout
      simp only at hout
      cases hunify : Metta.Bindings.unifyValues
          ((first :: rest) ++ [value]) with
      | none =>
          rw [hunify] at hout
          simp at hout
      | some result =>
          cases result with
          | nil =>
              rw [hunify] at hout
              simp only [List.mem_singleton] at hout
              subst out
              exact hbindingsNoFloat
          | cons binding restResult =>
              rw [hunify] at hout
              cases hreconcile : wholeBindingReconciliation bindings
                  [(.var v, value)] with
              | none =>
                  rw [hreconcile] at hout
                  simp at hout
              | some sigma =>
                  rw [hreconcile] at hout
                  simp only [List.mem_singleton] at hout
                  subst out
                  exact rebuildFromReconciliation_noFloat
                    (wholeBindingReconciliation_result_noFloat
                      hbindingsNoFloat (by
                        intro equation hmem
                        simp only [List.mem_singleton] at hmem
                        subst equation
                        exact ⟨by simp [MettaAtomNoFloat],
                          hvalueNoFloat⟩) hreconcile)

/-- Value insertion preserves the host-float-free fragment on every
successful branch. -/
theorem leaAddVarBinding_result_noFloat
    {bindings out : Metta.Bindings} {v : String} {value : Metta.Atom}
    (hbindingsNoFloat : LeaBindingsNoFloat bindings)
    (hvalueNoFloat : MettaAtomNoFloat value)
    (hout : out ∈ Metta.Bindings.addVarBinding bindings v value) :
    LeaBindingsNoFloat out := by
  cases value with
  | var other =>
      exact leaAddVarEquality_result_noFloat hbindingsNoFloat
        (by simpa [Metta.Bindings.addVarBinding] using hout)
  | sym symbol =>
      exact leaAddVarBinding_nonVar_result_noFloat
        (by intro other h; cases h) hbindingsNoFloat hvalueNoFloat hout
  | gnd ground =>
      exact leaAddVarBinding_nonVar_result_noFloat
        (by intro other h; cases h) hbindingsNoFloat hvalueNoFloat hout
  | expr atoms =>
      exact leaAddVarBinding_nonVar_result_noFloat
        (by intro other h; cases h) hbindingsNoFloat hvalueNoFloat hout

/-- Alias insertion preserves the normalized no-bare-variable representation
on every successful branch. -/
theorem leaAddVarEquality_result_assignmentsNonVariable
    {bindings out : Metta.Bindings} {left right : String}
    (hbindings : LeaAssignmentsNonVariable bindings)
    (hout : out ∈ Metta.Bindings.addVarEquality bindings left right) :
    LeaAssignmentsNonVariable out := by
  cases hunify : Metta.Bindings.unifyValues
      (Metta.Bindings.classValues
        (Metta.Bindings.addEqRaw bindings left right) left) with
  | none =>
      simp [Metta.Bindings.addVarEquality, hunify] at hout
  | some result =>
      cases result with
      | nil =>
          simp [Metta.Bindings.addVarEquality, hunify] at hout
          subst out
          exact hbindings.addEqRaw left right
      | cons binding rest =>
          cases hreconcile : Metta.Bindings.reconcileAll bindings
              [(.var left, .var right)] with
          | none =>
              simp [Metta.Bindings.addVarEquality, hunify,
                hreconcile] at hout
          | some sigma =>
              simp [Metta.Bindings.addVarEquality, hunify,
                hreconcile] at hout
              subst out
              exact rebuildFromReconciliation_assignmentsNonVariable
                (Metta.Bindings.addEqRaw bindings left right)
                bindings [(.var left, .var right)] sigma

/-- Alias insertion preserves equality irreflexivity on every successful
branch, including whole-system reconciliation. -/
theorem leaAddVarEquality_result_equalitiesIrreflexive
    {bindings out : Metta.Bindings} {left right : String}
    (hbindings : LeaEqualitiesIrreflexive bindings)
    (hout : out ∈ Metta.Bindings.addVarEquality bindings left right) :
    LeaEqualitiesIrreflexive out := by
  cases hunify : Metta.Bindings.unifyValues
      (Metta.Bindings.classValues
        (Metta.Bindings.addEqRaw bindings left right) left) with
  | none =>
      simp [Metta.Bindings.addVarEquality, hunify] at hout
  | some result =>
      cases result with
      | nil =>
          simp [Metta.Bindings.addVarEquality, hunify] at hout
          subst out
          exact hbindings.addEqRaw left right
      | cons binding rest =>
          cases hreconcile : Metta.Bindings.reconcileAll bindings
              [(.var left, .var right)] with
          | none =>
              simp [Metta.Bindings.addVarEquality, hunify,
                hreconcile] at hout
          | some sigma =>
              simp [Metta.Bindings.addVarEquality, hunify,
                hreconcile] at hout
              subst out
              exact rebuildFromReconciliation_equalitiesIrreflexive
                (hbindings.addEqRaw left right) hreconcile

private theorem leaAddVarBinding_nonVar_result_assignmentsNonVariable
    {bindings out : Metta.Bindings} {key : String} {value : Metta.Atom}
    (hvalue : ∀ target, value ≠ .var target)
    (hbindings : LeaAssignmentsNonVariable bindings)
    (hout : out ∈ Metta.Bindings.addVarBinding bindings key value) :
    LeaAssignmentsNonVariable out := by
  have hopen :
      Metta.Bindings.addVarBinding bindings key value =
        match Metta.Bindings.classValues bindings key with
        | [] => [Metta.Bindings.addValRaw bindings key value]
        | values =>
            match Metta.Bindings.unifyValues (values ++ [value]) with
            | none => []
            | some [] => [bindings]
            | some (_ :: _) =>
                match Metta.Bindings.reconcileAll bindings [(.var key, value)] with
                | none => []
                | some sigma =>
                    [Metta.Bindings.rebuildFromReconciliation
                      bindings bindings [(.var key, value)] sigma] := by
    cases value with
    | var target => exact (hvalue target rfl).elim
    | sym | gnd | expr => rfl
  rw [hopen] at hout
  cases hvalues : Metta.Bindings.classValues bindings key with
  | nil =>
      rw [hvalues] at hout
      simp only [List.mem_singleton] at hout
      subst out
      exact hbindings.addValRaw hvalue
  | cons first rest =>
      rw [hvalues] at hout
      simp only at hout
      cases hunify : Metta.Bindings.unifyValues
          ((first :: rest) ++ [value]) with
      | none =>
          rw [hunify] at hout
          simp at hout
      | some result =>
          cases result with
          | nil =>
              rw [hunify] at hout
              simp only [List.mem_singleton] at hout
              subst out
              exact hbindings
          | cons binding resultRest =>
              rw [hunify] at hout
              cases hreconcile : Metta.Bindings.reconcileAll bindings
                  [(.var key, value)] with
              | none =>
                  rw [hreconcile] at hout
                  simp at hout
              | some sigma =>
                  rw [hreconcile] at hout
                  simp only [List.mem_singleton] at hout
                  subst out
                  exact rebuildFromReconciliation_assignmentsNonVariable
                    bindings bindings [(.var key, value)] sigma

private theorem leaAddVarBinding_nonVar_result_equalitiesIrreflexive
    {bindings out : Metta.Bindings} {key : String} {value : Metta.Atom}
    (hvalue : ∀ target, value ≠ .var target)
    (hbindings : LeaEqualitiesIrreflexive bindings)
    (hout : out ∈ Metta.Bindings.addVarBinding bindings key value) :
    LeaEqualitiesIrreflexive out := by
  have hopen :
      Metta.Bindings.addVarBinding bindings key value =
        match Metta.Bindings.classValues bindings key with
        | [] => [Metta.Bindings.addValRaw bindings key value]
        | values =>
            match Metta.Bindings.unifyValues (values ++ [value]) with
            | none => []
            | some [] => [bindings]
            | some (_ :: _) =>
                match Metta.Bindings.reconcileAll bindings [(.var key, value)] with
                | none => []
                | some sigma =>
                    [Metta.Bindings.rebuildFromReconciliation
                      bindings bindings [(.var key, value)] sigma] := by
    cases value with
    | var target => exact (hvalue target rfl).elim
    | sym | gnd | expr => rfl
  rw [hopen] at hout
  cases hvalues : Metta.Bindings.classValues bindings key with
  | nil =>
      rw [hvalues] at hout
      simp only [List.mem_singleton] at hout
      subst out
      exact hbindings.addValRaw key value
  | cons first rest =>
      rw [hvalues] at hout
      simp only at hout
      cases hunify : Metta.Bindings.unifyValues
          ((first :: rest) ++ [value]) with
      | none =>
          rw [hunify] at hout
          simp at hout
      | some result =>
          cases result with
          | nil =>
              rw [hunify] at hout
              simp only [List.mem_singleton] at hout
              subst out
              exact hbindings
          | cons binding resultRest =>
              rw [hunify] at hout
              cases hreconcile : Metta.Bindings.reconcileAll bindings
                  [(.var key, value)] with
              | none =>
                  rw [hreconcile] at hout
                  simp at hout
              | some sigma =>
                  rw [hreconcile] at hout
                  simp only [List.mem_singleton] at hout
                  subst out
                  exact rebuildFromReconciliation_equalitiesIrreflexive
                    hbindings hreconcile

/-- Value insertion preserves normalized assignment shape.  A variable
payload is routed through equality insertion; every non-variable branch either
adds that genuine value, leaves the record unchanged, or rebuilds it from a
normalized substitution. -/
theorem leaAddVarBinding_result_assignmentsNonVariable
    {bindings out : Metta.Bindings} {key : String} {value : Metta.Atom}
    (hbindings : LeaAssignmentsNonVariable bindings)
    (hout : out ∈ Metta.Bindings.addVarBinding bindings key value) :
    LeaAssignmentsNonVariable out := by
  cases value with
  | var target =>
      exact leaAddVarEquality_result_assignmentsNonVariable hbindings
        (by simpa [Metta.Bindings.addVarBinding] using hout)
  | sym symbol =>
      exact leaAddVarBinding_nonVar_result_assignmentsNonVariable
        (by intro target h; cases h) hbindings hout
  | gnd ground =>
      exact leaAddVarBinding_nonVar_result_assignmentsNonVariable
        (by intro target h; cases h) hbindings hout
  | expr atoms =>
      exact leaAddVarBinding_nonVar_result_assignmentsNonVariable
        (by intro target h; cases h) hbindings hout

/-- Value insertion also preserves the absence of reflexive equality edges. -/
theorem leaAddVarBinding_result_equalitiesIrreflexive
    {bindings out : Metta.Bindings} {key : String} {value : Metta.Atom}
    (hbindings : LeaEqualitiesIrreflexive bindings)
    (hout : out ∈ Metta.Bindings.addVarBinding bindings key value) :
    LeaEqualitiesIrreflexive out := by
  cases value with
  | var target =>
      exact leaAddVarEquality_result_equalitiesIrreflexive hbindings
        (by simpa [Metta.Bindings.addVarBinding] using hout)
  | sym symbol =>
      exact leaAddVarBinding_nonVar_result_equalitiesIrreflexive
        (by intro target h; cases h) hbindings hout
  | gnd ground =>
      exact leaAddVarBinding_nonVar_result_equalitiesIrreflexive
        (by intro target h; cases h) hbindings hout
  | expr atoms =>
      exact leaAddVarBinding_nonVar_result_equalitiesIrreflexive
        (by intro target h; cases h) hbindings hout

private theorem leaMergeOne_result_assignmentsNonVariable
    {seeds : List Metta.Bindings} {relation : Metta.BindingRel}
    {out : Metta.Bindings}
    (hseeds : ∀ seed ∈ seeds, LeaAssignmentsNonVariable seed)
    (hout : out ∈ Metta.Bindings.mergeOne seeds relation) :
    LeaAssignmentsNonVariable out := by
  unfold Metta.Bindings.mergeOne at hout
  obtain ⟨seed, hseed, hout⟩ := List.mem_flatMap.mp hout
  cases relation with
  | val key value =>
      exact leaAddVarBinding_result_assignmentsNonVariable
        (hseeds seed hseed) hout
  | eq left right =>
      exact leaAddVarEquality_result_assignmentsNonVariable
        (hseeds seed hseed) hout

private theorem leaMergeOne_result_equalitiesIrreflexive
    {seeds : List Metta.Bindings} {relation : Metta.BindingRel}
    {out : Metta.Bindings}
    (hseeds : ∀ seed ∈ seeds, LeaEqualitiesIrreflexive seed)
    (hout : out ∈ Metta.Bindings.mergeOne seeds relation) :
    LeaEqualitiesIrreflexive out := by
  unfold Metta.Bindings.mergeOne at hout
  obtain ⟨seed, hseed, hout⟩ := List.mem_flatMap.mp hout
  cases relation with
  | val key value =>
      exact leaAddVarBinding_result_equalitiesIrreflexive
        (hseeds seed hseed) hout
  | eq left right =>
      exact leaAddVarEquality_result_equalitiesIrreflexive
        (hseeds seed hseed) hout

private theorem leaMergeFold_result_assignmentsNonVariable
    {relations : Metta.Bindings} {seeds : List Metta.Bindings}
    {out : Metta.Bindings}
    (hseeds : ∀ seed ∈ seeds, LeaAssignmentsNonVariable seed)
    (hout : out ∈ relations.foldl Metta.Bindings.mergeOne seeds) :
    LeaAssignmentsNonVariable out := by
  induction relations generalizing seeds out with
  | nil =>
      simp only [List.foldl_nil] at hout
      exact hseeds out hout
  | cons relation rest ih =>
      simp only [List.foldl_cons] at hout
      apply ih (out := out) ?_ hout
      intro next hnext
      exact leaMergeOne_result_assignmentsNonVariable hseeds hnext

private theorem leaMergeFold_result_equalitiesIrreflexive
    {relations : Metta.Bindings} {seeds : List Metta.Bindings}
    {out : Metta.Bindings}
    (hseeds : ∀ seed ∈ seeds, LeaEqualitiesIrreflexive seed)
    (hout : out ∈ relations.foldl Metta.Bindings.mergeOne seeds) :
    LeaEqualitiesIrreflexive out := by
  induction relations generalizing seeds out with
  | nil =>
      simp only [List.foldl_nil] at hout
      exact hseeds out hout
  | cons relation rest ih =>
      simp only [List.foldl_cons] at hout
      apply ih (out := out) ?_ hout
      intro next hnext
      exact leaMergeOne_result_equalitiesIrreflexive hseeds hnext

/-- Every successful repaired-LeaTTa merge preserves the invariant that
variable aliases are equality relations rather than value assignments. -/
theorem leaMerge_result_assignmentsNonVariable
    {left right out : Metta.Bindings}
    (hleft : LeaAssignmentsNonVariable left)
    (hout : out ∈ Metta.Bindings.merge left right) :
    LeaAssignmentsNonVariable out := by
  exact leaMergeFold_result_assignmentsNonVariable
    (relations := right) (seeds := [left]) (out := out)
    (by simpa using hleft) (by simpa [Metta.Bindings.merge] using hout)

/-- Every successful repaired-LeaTTa merge preserves equality
irreflexivity. -/
theorem leaMerge_result_equalitiesIrreflexive
    {left right out : Metta.Bindings}
    (hleft : LeaEqualitiesIrreflexive left)
    (hout : out ∈ Metta.Bindings.merge left right) :
    LeaEqualitiesIrreflexive out := by
  exact leaMergeFold_result_equalitiesIrreflexive
    (relations := right) (seeds := [left]) (out := out)
    (by simpa using hleft) (by simpa [Metta.Bindings.merge] using hout)

private theorem leaMergeOne_solution_iff
    {seeds : List Metta.Bindings} {relation : Metta.BindingRel}
    {out : Metta.Bindings}
    (hseedsNoFloat : ∀ seed ∈ seeds, LeaBindingsNoFloat seed)
    (hrelationNoFloat : LeaBindingsNoFloat [relation])
    (hout : out ∈ Metta.Bindings.mergeOne seeds relation) :
    ∃ seed ∈ seeds, ∀ valuation,
      LeaBindingSatisfied valuation out ↔
        LeaBindingSatisfied valuation seed ∧
          LeaBindingSatisfied valuation [relation] := by
  unfold Metta.Bindings.mergeOne at hout
  obtain ⟨seed, hseed, hout⟩ := List.mem_flatMap.mp hout
  refine ⟨seed, hseed, ?_⟩
  cases relation with
  | val v value =>
      intro valuation
      have hvalueNoFloat : MettaAtomNoFloat value :=
        hrelationNoFloat v value (by simp)
      simpa [LeaBindingSatisfied] using
        (leaAddVarBinding_solution_iff valuation
          (hseedsNoFloat seed hseed) hvalueNoFloat hout)
  | eq left right =>
      intro valuation
      simpa [LeaBindingSatisfied] using
        (leaAddVarEquality_solution_iff valuation
          (hseedsNoFloat seed hseed) hout)

private theorem leaMergeOne_result_noFloat
    {seeds : List Metta.Bindings} {relation : Metta.BindingRel}
    {out : Metta.Bindings}
    (hseedsNoFloat : ∀ seed ∈ seeds, LeaBindingsNoFloat seed)
    (hrelationNoFloat : LeaBindingsNoFloat [relation])
    (hout : out ∈ Metta.Bindings.mergeOne seeds relation) :
    LeaBindingsNoFloat out := by
  unfold Metta.Bindings.mergeOne at hout
  obtain ⟨seed, hseed, hout⟩ := List.mem_flatMap.mp hout
  cases relation with
  | val v value =>
      exact leaAddVarBinding_result_noFloat
        (hseedsNoFloat seed hseed)
        (hrelationNoFloat v value (by simp)) hout
  | eq left right =>
      exact leaAddVarEquality_result_noFloat
        (hseedsNoFloat seed hseed) hout

private theorem leaMergeFold_solution_iff
    {relations : Metta.Bindings} {seeds : List Metta.Bindings}
    {out : Metta.Bindings}
    (hseedsNoFloat : ∀ seed ∈ seeds, LeaBindingsNoFloat seed)
    (hrelationsNoFloat : LeaBindingsNoFloat relations)
    (hout : out ∈ relations.foldl Metta.Bindings.mergeOne seeds) :
    ∃ seed ∈ seeds, ∀ valuation,
      LeaBindingSatisfied valuation out ↔
        LeaBindingSatisfied valuation seed ∧
          LeaBindingSatisfied valuation relations := by
  induction relations generalizing seeds out with
  | nil =>
      simp only [List.foldl_nil] at hout
      refine ⟨out, hout, ?_⟩
      intro valuation
      simp [LeaBindingSatisfied]
  | cons relation rest ih =>
      simp only [List.foldl_cons] at hout
      have hrelationNoFloat : LeaBindingsNoFloat [relation] := by
        intro key value hmem
        apply hrelationsNoFloat key value
        exact List.mem_cons.mpr (Or.inl (by simpa using hmem))
      have hrestNoFloat : LeaBindingsNoFloat rest := by
        intro key value hmem
        exact hrelationsNoFloat key value
          (List.mem_cons_of_mem relation hmem)
      have hnextNoFloat : ∀ next ∈
          Metta.Bindings.mergeOne seeds relation,
          LeaBindingsNoFloat next := by
        intro next hnext
        exact leaMergeOne_result_noFloat
          hseedsNoFloat hrelationNoFloat hnext
      obtain ⟨middle, hmiddle, houtTheory⟩ :=
        ih hnextNoFloat hrestNoFloat hout
      obtain ⟨seed, hseed, hmiddleTheory⟩ :=
        leaMergeOne_solution_iff
          hseedsNoFloat hrelationNoFloat hmiddle
      refine ⟨seed, hseed, ?_⟩
      intro valuation
      rw [houtTheory valuation, hmiddleTheory valuation]
      have hcons :=
        leaBindingSatisfied_append_iff valuation [relation] rest
      simpa [and_assoc] using and_congr Iff.rfl hcons.symm

private theorem leaMergeFold_result_noFloat
    {relations : Metta.Bindings} {seeds : List Metta.Bindings}
    {out : Metta.Bindings}
    (hseedsNoFloat : ∀ seed ∈ seeds, LeaBindingsNoFloat seed)
    (hrelationsNoFloat : LeaBindingsNoFloat relations)
    (hout : out ∈ relations.foldl Metta.Bindings.mergeOne seeds) :
    LeaBindingsNoFloat out := by
  induction relations generalizing seeds out with
  | nil =>
      simp only [List.foldl_nil] at hout
      exact hseedsNoFloat out hout
  | cons relation rest ih =>
      simp only [List.foldl_cons] at hout
      have hrelationNoFloat : LeaBindingsNoFloat [relation] := by
        intro key value hmem
        apply hrelationsNoFloat key value
        exact List.mem_cons.mpr (Or.inl (by simpa using hmem))
      have hrestNoFloat : LeaBindingsNoFloat rest := by
        intro key value hmem
        exact hrelationsNoFloat key value
          (List.mem_cons_of_mem relation hmem)
      apply ih (out := out) ?_ hrestNoFloat hout
      intro next hnext
      exact leaMergeOne_result_noFloat
        hseedsNoFloat hrelationNoFloat hnext

/-- A successful repaired-LeaTTa merge presents exactly the conjunction of
the two input binding theories. -/
theorem leaMerge_solution_iff
    (valuation : String → Metta.Atom)
    {left right out : Metta.Bindings}
    (hleftNoFloat : LeaBindingsNoFloat left)
    (hrightNoFloat : LeaBindingsNoFloat right)
    (hout : out ∈ Metta.Bindings.merge left right) :
    LeaBindingSatisfied valuation out ↔
      LeaBindingSatisfied valuation left ∧
        LeaBindingSatisfied valuation right := by
  obtain ⟨seed, hseed, htheory⟩ :=
    leaMergeFold_solution_iff
      (seeds := [left]) (relations := right) (out := out)
      (by simpa using hleftNoFloat) hrightNoFloat (by
        simpa [Metta.Bindings.merge] using hout)
  simp only [List.mem_singleton] at hseed
  subst seed
  exact htheory valuation

/-- A successful repaired-LeaTTa merge remains in the host-float-free
fragment. -/
theorem leaMerge_result_noFloat
    {left right out : Metta.Bindings}
    (hleftNoFloat : LeaBindingsNoFloat left)
    (hrightNoFloat : LeaBindingsNoFloat right)
    (hout : out ∈ Metta.Bindings.merge left right) :
    LeaBindingsNoFloat out := by
  exact leaMergeFold_result_noFloat
    (seeds := [left]) (relations := right) (out := out)
    (by simpa using hleftNoFloat) hrightNoFloat (by
      simpa [Metta.Bindings.merge] using hout)

/-! ### Normalized shape of matcher outputs -/

private structure LeaMatchNormalizationPack (left : Metta.Atom) : Prop where
  result : ∀ {right out},
    out ∈ Metta.matchAtomsWith none left right →
      LeaAssignmentsNonVariable out

private theorem leaMatchAll_result_assignmentsNonVariable_aux
    (lefts : List Metta.Atom)
    (hpacks : ∀ left ∈ lefts, LeaMatchNormalizationPack left) :
    ∀ {rights : List Metta.Atom} {seeds : List Metta.Bindings}
      {out : Metta.Bindings},
      (∀ seed ∈ seeds, LeaAssignmentsNonVariable seed) →
      out ∈ Metta.matchAll none seeds lefts rights →
        LeaAssignmentsNonVariable out := by
  induction lefts with
  | nil =>
      intro rights seeds out hseeds hout
      cases rights with
      | nil =>
          simp only [Metta.matchAll] at hout
          exact hseeds out hout
      | cons right rights => simp [Metta.matchAll] at hout
  | cons left lefts ih =>
      intro rights seeds out hseeds hout
      cases rights with
      | nil => simp [Metta.matchAll] at hout
      | cons right rights =>
          let subs := (Metta.matchAtomsWith none left right).filter
            (fun bindings => !bindings.hasLoop)
          let next := seeds.flatMap fun seed =>
            subs.flatMap fun matched => Metta.Bindings.merge seed matched
          have houtTail :
              out ∈ Metta.matchAll none next lefts rights := by
            simpa [Metta.matchAll, subs, next] using hout
          have hpacksTail : ∀ atom ∈ lefts,
              LeaMatchNormalizationPack atom := by
            intro atom hmem
            exact hpacks atom (by simp [hmem])
          apply ih hpacksTail ?_ houtTail
          intro candidate hcandidate
          obtain ⟨seed, hseed, hcandidate⟩ :=
            List.mem_flatMap.mp hcandidate
          obtain ⟨matched, hmatched, hmerge⟩ :=
            List.mem_flatMap.mp hcandidate
          exact leaMerge_result_assignmentsNonVariable
            (hseeds seed hseed) hmerge

private theorem leaMatchNormalizationPack
    (left : Metta.Atom) : LeaMatchNormalizationPack left := by
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_ left
  · intro symbol
    constructor
    intro right out hout
    cases right with
    | sym other =>
        by_cases heq : symbol = other
        · subst other
          simp [Metta.matchAtomsWith] at hout
          subst out
          exact leaAssignmentsNonVariable_empty
        · simp [Metta.matchAtomsWith, heq] at hout
    | var target =>
        simp [Metta.matchAtomsWith] at hout
        subst out
        simp [LeaAssignmentsNonVariable]
    | gnd grounded =>
        simp [Metta.matchAtomsWith, Metta.Atom.equiv] at hout
    | expr atoms =>
        simp [Metta.matchAtomsWith, Metta.Atom.equiv] at hout
  · intro source
    constructor
    intro right out hout
    cases right with
    | sym symbol =>
        simp [Metta.matchAtomsWith] at hout
        subst out
        simp [LeaAssignmentsNonVariable]
    | var target =>
        by_cases heq : source = target
        · subst target
          simp [Metta.matchAtomsWith] at hout
          subst out
          exact leaAssignmentsNonVariable_empty
        · have hbeq : (source == target) = false := by simp [heq]
          simp [Metta.matchAtomsWith, hbeq] at hout
          subst out
          simp [LeaAssignmentsNonVariable]
    | gnd grounded =>
        simp [Metta.matchAtomsWith] at hout
        subst out
        simp [LeaAssignmentsNonVariable]
    | expr atoms =>
        cases hoccurs : Metta.Subst.occurs source (.expr atoms) with
        | true => simp [Metta.matchAtomsWith, hoccurs] at hout
        | false =>
            simp [Metta.matchAtomsWith, hoccurs] at hout
            subst out
            simp [LeaAssignmentsNonVariable]
  · intro grounded
    constructor
    intro right out hout
    cases right with
    | var target =>
        simp [Metta.matchAtomsWith] at hout
        subst out
        simp [LeaAssignmentsNonVariable]
    | sym symbol =>
        simp [Metta.matchAtomsWith, Metta.Atom.equiv] at hout
    | gnd other =>
        cases hequiv : Metta.Ground.equiv grounded other <;>
          simp [Metta.matchAtomsWith, Metta.Atom.equiv, hequiv] at hout
        subst out
        exact leaAssignmentsNonVariable_empty
    | expr atoms =>
        simp [Metta.matchAtomsWith, Metta.Atom.equiv] at hout
  · intro atoms ih
    constructor
    intro right out hout
    cases right with
    | sym symbol =>
        simp [Metta.matchAtomsWith, Metta.Atom.equiv] at hout
    | var target =>
        cases hoccurs : Metta.Subst.occurs target (.expr atoms) with
        | true => simp [Metta.matchAtomsWith, hoccurs] at hout
        | false =>
            simp [Metta.matchAtomsWith, hoccurs] at hout
            subst out
            simp [LeaAssignmentsNonVariable]
    | gnd grounded =>
        simp [Metta.matchAtomsWith, Metta.Atom.equiv] at hout
    | expr rights =>
        exact leaMatchAll_result_assignmentsNonVariable_aux atoms ih
          (rights := rights) (seeds := [[]]) (out := out)
          (by intro seed hseed
              simp only [List.mem_singleton] at hseed
              subst seed
              exact leaAssignmentsNonVariable_empty)
          (by simpa [Metta.matchAtomsWith] using hout)

/-- Every raw pointwise LeaTTa list match started from normalized seeds remains
normalized.  In particular, cross-child merge-back never turns an alias into
a variable-valued assignment. -/
theorem leaMatchAll_result_assignmentsNonVariable
    {lefts rights : List Metta.Atom} {seeds : List Metta.Bindings}
    {out : Metta.Bindings}
    (hseeds : ∀ seed ∈ seeds, LeaAssignmentsNonVariable seed)
    (hout : out ∈ Metta.matchAll none seeds lefts rights) :
    LeaAssignmentsNonVariable out := by
  exact leaMatchAll_result_assignmentsNonVariable_aux lefts
    (fun left _ => leaMatchNormalizationPack left) hseeds hout

/-- Every raw repaired-LeaTTa atom match has normalized assignment shape.
The public loop filter can therefore reason about genuine compound dependency
cycles without admitting the satisfiable bare-variable cycle canary. -/
theorem leaMatchAtomsWith_result_assignmentsNonVariable
    {left right : Metta.Atom} {out : Metta.Bindings}
    (hout : out ∈ Metta.matchAtomsWith none left right) :
    LeaAssignmentsNonVariable out :=
  (leaMatchNormalizationPack left).result hout

/-- Public matcher outputs inherit the same normalized shape. -/
theorem leaMatchAtoms_result_assignmentsNonVariable
    {left right : Metta.Atom} {out : Metta.Bindings}
    (hout : out ∈ Metta.matchAtoms left right) :
    LeaAssignmentsNonVariable out := by
  have hraw : out ∈ Metta.matchAtomsWith none left right :=
    ((by simpa [Metta.matchAtoms] using hout) :
      out ∈ Metta.matchAtomsWith none left right ∧
        out.hasLoop = false).1
  exact leaMatchAtomsWith_result_assignmentsNonVariable hraw

private structure LeaMatchIrreflexivePack (left : Metta.Atom) : Prop where
  result : ∀ {right out},
    out ∈ Metta.matchAtomsWith none left right →
      LeaEqualitiesIrreflexive out

private theorem leaMatchAll_result_equalitiesIrreflexive_aux
    (lefts : List Metta.Atom)
    (hpacks : ∀ left ∈ lefts, LeaMatchIrreflexivePack left) :
    ∀ {rights : List Metta.Atom} {seeds : List Metta.Bindings}
      {out : Metta.Bindings},
      (∀ seed ∈ seeds, LeaEqualitiesIrreflexive seed) →
      out ∈ Metta.matchAll none seeds lefts rights →
        LeaEqualitiesIrreflexive out := by
  induction lefts with
  | nil =>
      intro rights seeds out hseeds hout
      cases rights with
      | nil =>
          simp only [Metta.matchAll] at hout
          exact hseeds out hout
      | cons right rights => simp [Metta.matchAll] at hout
  | cons left lefts ih =>
      intro rights seeds out hseeds hout
      cases rights with
      | nil => simp [Metta.matchAll] at hout
      | cons right rights =>
          let subs := (Metta.matchAtomsWith none left right).filter
            (fun bindings => !bindings.hasLoop)
          let next := seeds.flatMap fun seed =>
            subs.flatMap fun matched => Metta.Bindings.merge seed matched
          have houtTail :
              out ∈ Metta.matchAll none next lefts rights := by
            simpa [Metta.matchAll, subs, next] using hout
          have hpacksTail : ∀ atom ∈ lefts,
              LeaMatchIrreflexivePack atom := by
            intro atom hmem
            exact hpacks atom (by simp [hmem])
          apply ih hpacksTail ?_ houtTail
          intro candidate hcandidate
          obtain ⟨seed, hseed, hcandidate⟩ :=
            List.mem_flatMap.mp hcandidate
          obtain ⟨matched, hmatched, hmerge⟩ :=
            List.mem_flatMap.mp hcandidate
          exact leaMerge_result_equalitiesIrreflexive
            (hseeds seed hseed) hmerge

private theorem leaMatchIrreflexivePack
    (left : Metta.Atom) : LeaMatchIrreflexivePack left := by
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_ left
  · intro symbol
    constructor
    intro right out hout
    cases right with
    | sym other =>
        by_cases heq : symbol = other
        · subst other
          simp [Metta.matchAtomsWith] at hout
          subst out
          exact leaEqualitiesIrreflexive_empty
        · simp [Metta.matchAtomsWith, heq] at hout
    | var target =>
        simp [Metta.matchAtomsWith] at hout
        subst out
        simp [LeaEqualitiesIrreflexive]
    | gnd grounded =>
        simp [Metta.matchAtomsWith, Metta.Atom.equiv] at hout
    | expr atoms =>
        simp [Metta.matchAtomsWith, Metta.Atom.equiv] at hout
  · intro source
    constructor
    intro right out hout
    cases right with
    | sym symbol =>
        simp [Metta.matchAtomsWith] at hout
        subst out
        simp [LeaEqualitiesIrreflexive]
    | var target =>
        by_cases heq : source = target
        · subst target
          simp [Metta.matchAtomsWith] at hout
          subst out
          exact leaEqualitiesIrreflexive_empty
        · have hbeq : (source == target) = false := by simp [heq]
          simp [Metta.matchAtomsWith, hbeq] at hout
          subst out
          simp [LeaEqualitiesIrreflexive, heq]
    | gnd grounded =>
        simp [Metta.matchAtomsWith] at hout
        subst out
        simp [LeaEqualitiesIrreflexive]
    | expr atoms =>
        cases hoccurs : Metta.Subst.occurs source (.expr atoms) with
        | true => simp [Metta.matchAtomsWith, hoccurs] at hout
        | false =>
            simp [Metta.matchAtomsWith, hoccurs] at hout
            subst out
            simp [LeaEqualitiesIrreflexive]
  · intro grounded
    constructor
    intro right out hout
    cases right with
    | var target =>
        simp [Metta.matchAtomsWith] at hout
        subst out
        simp [LeaEqualitiesIrreflexive]
    | sym symbol =>
        simp [Metta.matchAtomsWith, Metta.Atom.equiv] at hout
    | gnd other =>
        cases hequiv : Metta.Ground.equiv grounded other <;>
          simp [Metta.matchAtomsWith, Metta.Atom.equiv, hequiv] at hout
        subst out
        exact leaEqualitiesIrreflexive_empty
    | expr atoms =>
        simp [Metta.matchAtomsWith, Metta.Atom.equiv] at hout
  · intro atoms ih
    constructor
    intro right out hout
    cases right with
    | sym symbol =>
        simp [Metta.matchAtomsWith, Metta.Atom.equiv] at hout
    | var target =>
        cases hoccurs : Metta.Subst.occurs target (.expr atoms) with
        | true => simp [Metta.matchAtomsWith, hoccurs] at hout
        | false =>
            simp [Metta.matchAtomsWith, hoccurs] at hout
            subst out
            simp [LeaEqualitiesIrreflexive]
    | gnd grounded =>
        simp [Metta.matchAtomsWith, Metta.Atom.equiv] at hout
    | expr rights =>
        exact leaMatchAll_result_equalitiesIrreflexive_aux atoms ih
          (rights := rights) (seeds := [[]]) (out := out)
          (by intro seed hseed
              simp only [List.mem_singleton] at hseed
              subst seed
              exact leaEqualitiesIrreflexive_empty)
          (by simpa [Metta.matchAtomsWith] using hout)

/-- Every raw repaired-LeaTTa atom match is free of reflexive equality
relations. -/
theorem leaMatchAtomsWith_result_equalitiesIrreflexive
    {left right : Metta.Atom} {out : Metta.Bindings}
    (hout : out ∈ Metta.matchAtomsWith none left right) :
    LeaEqualitiesIrreflexive out :=
  (leaMatchIrreflexivePack left).result hout

/-- Public matcher outputs inherit equality irreflexivity. -/
theorem leaMatchAtoms_result_equalitiesIrreflexive
    {left right : Metta.Atom} {out : Metta.Bindings}
    (hout : out ∈ Metta.matchAtoms left right) :
    LeaEqualitiesIrreflexive out := by
  have hraw : out ∈ Metta.matchAtomsWith none left right :=
    ((by simpa [Metta.matchAtoms] using hout) :
      out ∈ Metta.matchAtomsWith none left right ∧
        out.hasLoop = false).1
  exact leaMatchAtomsWith_result_equalitiesIrreflexive hraw

/-- The explicit one-relation loop scan is false on normalized repaired-LeaTTa
bindings.  Variable-valued assignments are absent and every equality edge has
distinct endpoints. -/
theorem leaBindings_directLoop_false
    {bindings : Metta.Bindings}
    (hnonvariable : LeaAssignmentsNonVariable bindings)
    (hirreflexive : LeaEqualitiesIrreflexive bindings) :
    bindings.any (fun relation => match relation with
      | Metta.BindingRel.val left (.var right) => left == right
      | Metta.BindingRel.eq left right => left == right
      | _ => false) = false := by
  rw [List.any_eq_false]
  intro relation hrelation
  cases relation with
  | val key value =>
      cases value with
      | var target => exact (hnonvariable key target hrelation).elim
      | sym symbol => simp
      | gnd ground => simp
      | expr atoms => simp
  | eq left right =>
      have hne : left ≠ right := by
        intro heq
        subst right
        exact hirreflexive left hrelation
      simp [hne]

/-- Consequently, every raw repaired-LeaTTa matcher output passes the direct
self-loop half of `Bindings.hasLoop`; only recursive resolution remains. -/
theorem leaMatchAtomsWith_directLoop_false
    {left right : Metta.Atom} {out : Metta.Bindings}
    (hout : out ∈ Metta.matchAtomsWith none left right) :
    out.any (fun relation => match relation with
      | Metta.BindingRel.val source (.var target) => source == target
      | Metta.BindingRel.eq source target => source == target
      | _ => false) = false := by
  exact leaBindings_directLoop_false
    (leaMatchAtomsWith_result_assignmentsNonVariable hout)
    (leaMatchAtomsWith_result_equalitiesIrreflexive hout)

/-- Remaining static resolver charge.  A value relation is charged until its
key's equality class has been visited; equality edges remain as harmless
constant slack. -/
def leaResolutionRelationBudget
    (visited : List String) : Metta.BindingRel → Nat
  | .val key value => if visited.contains key then 0 else value.size + 1
  | .eq _ _ => 1

/-- The resolver's exact structural budget, refined by the already-visited
classes.  At the empty visited set this is LeaTTa's shipped
`Bindings.resolutionFuel`. -/
def leaResolutionBudget
    (bindings : Metta.Bindings) (visited : List String)
    (atom : Metta.Atom) : Nat :=
  atom.size +
    (bindings.map (leaResolutionRelationBudget visited)).sum + 1

/-- Every variable in the atom denotes a strictly smaller semantic value than
every already-visited ancestor.  This rank invariant prevents the resolver's
class-overlap guard from firing. -/
def LeaResolutionBelowVisited
    (valuation : String → Metta.Atom) (visited : List String)
    (atom : Metta.Atom) : Prop :=
  ∀ dependency ∈ atom.vars, ∀ ancestor ∈ visited,
    (valuation dependency).size < (valuation ancestor).size

@[simp] theorem leaResolutionBelowVisited_nil
    (valuation : String → Metta.Atom) (atom : Metta.Atom) :
    LeaResolutionBelowVisited valuation [] atom := by
  simp [LeaResolutionBelowVisited]

/-- Extending the visited set can only remove value-relation charge. -/
theorem leaResolutionRelationBudget_append_le
    (front visited : List String) (relation : Metta.BindingRel) :
    leaResolutionRelationBudget (front ++ visited) relation ≤
      leaResolutionRelationBudget visited relation := by
  cases relation with
  | eq left right => rfl
  | val key value =>
      by_cases hkeyVisited : key ∈ visited
      · simp [leaResolutionRelationBudget, hkeyVisited]
      · by_cases hkeyFront : key ∈ front
        · simp [leaResolutionRelationBudget, hkeyVisited, hkeyFront]
        · simp [leaResolutionRelationBudget, hkeyVisited, hkeyFront]

/-- Visiting the class that owns a selected value removes at least that
value relation's full `value.size + 1` charge. -/
theorem leaResolutionRelationBudget_sum_drop
    {bindings : Metta.Bindings} {visited cls : List String}
    {key : String} {value : Metta.Atom}
    (hbinding : Metta.BindingRel.val key value ∈ bindings)
    (hkeyClass : key ∈ cls)
    (hdisjoint : cls.any visited.contains = false) :
    (bindings.map
        (leaResolutionRelationBudget (cls ++ visited))).sum +
        (value.size + 1) ≤
      (bindings.map (leaResolutionRelationBudget visited)).sum := by
  obtain ⟨front, suffix, hsplit⟩ := List.mem_iff_append.mp hbinding
  rw [hsplit]
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  have hfront :
      (front.map
          (leaResolutionRelationBudget (cls ++ visited))).sum ≤
        (front.map (leaResolutionRelationBudget visited)).sum :=
    List.sum_le_sum (fun relation _ =>
      leaResolutionRelationBudget_append_le cls visited relation)
  have hsuffix :
      (suffix.map
          (leaResolutionRelationBudget (cls ++ visited))).sum ≤
        (suffix.map (leaResolutionRelationBudget visited)).sum :=
    List.sum_le_sum (fun relation _ =>
      leaResolutionRelationBudget_append_le cls visited relation)
  have hkeyNotVisited : visited.contains key = false := by
    cases hkey : visited.contains key with
    | false => rfl
    | true =>
        exact (List.any_eq_false.mp hdisjoint key hkeyClass hkey).elim
  have hkeyNew : (cls ++ visited).contains key = true := by
    simp [hkeyClass]
  simp only [leaResolutionRelationBudget, hkeyNotVisited, hkeyNew,
    Bool.false_eq_true, ↓reduceIte]
  omega

/-- The initial refined budget is definitionally the runtime fuel. -/
theorem leaResolutionBudget_nil_eq_resolutionFuel
    (bindings : Metta.Bindings) (atom : Metta.Atom) :
    leaResolutionBudget bindings [] atom =
      Metta.Bindings.resolutionFuel bindings atom := by
  unfold leaResolutionBudget Metta.Bindings.resolutionFuel
  have hmap :
      bindings.map (leaResolutionRelationBudget []) =
        bindings.map Metta.Bindings.relationResolutionFuel := by
    apply List.map_congr_left
    intro relation _hrelation
    cases relation <;>
      simp [leaResolutionRelationBudget,
        Metta.Bindings.relationResolutionFuel]
  rw [hmap]

/-- A direct child has strictly smaller structural size than its enclosing
expression. -/
theorem leaAtom_size_lt_expr_of_mem
    {child : Metta.Atom} {atoms : List Metta.Atom}
    (hchild : child ∈ atoms) :
    child.size < (Metta.Atom.expr atoms).size := by
  have hmember : child.size ∈ atoms.map Metta.Atom.size :=
    List.mem_map.mpr ⟨child, hchild, rfl⟩
  have hle : child.size ≤ (atoms.map Metta.Atom.size).sum :=
    List.single_le_sum (by intro _ _; omega) _ hmember
  simp only [Metta.Atom.size]
  omega

/-- Structural expression descent strictly decreases the refined budget. -/
theorem leaResolutionBudget_child_lt
    (bindings : Metta.Bindings) (visited : List String)
    {child : Metta.Atom} {atoms : List Metta.Atom}
    (hchild : child ∈ atoms) :
    leaResolutionBudget bindings visited child <
      leaResolutionBudget bindings visited (.expr atoms) := by
  have hsize := leaAtom_size_lt_expr_of_mem hchild
  simp only [leaResolutionBudget]
  omega

/-- A rank invariant for an expression restricts to each child. -/
theorem LeaResolutionBelowVisited.of_expr_mem
    {valuation : String → Metta.Atom} {visited : List String}
    {child : Metta.Atom} {atoms : List Metta.Atom}
    (hbelow : LeaResolutionBelowVisited valuation visited (.expr atoms))
    (hchild : child ∈ atoms) :
    LeaResolutionBelowVisited valuation visited child := by
  intro dependency hdependency ancestor hancestor
  apply hbelow dependency ?_ ancestor hancestor
  simp only [Metta.Atom.vars, List.mem_flatten, List.mem_map]
  exact ⟨child.vars, ⟨child, hchild, rfl⟩, hdependency⟩

/-- Any value exposed by `classValues` has a concrete stored value relation. -/
theorem leaClassValue_relation
    {bindings : Metta.Bindings} {key : String} {value : Metta.Atom}
    (hvalue : value ∈ Metta.Bindings.classValues bindings key) :
    ∃ storedKey,
      storedKey ∈ Metta.Bindings.eqClassOrdered bindings key ∧
        Metta.BindingRel.val storedKey value ∈ bindings := by
  unfold Metta.Bindings.classValues at hvalue
  obtain ⟨storedKey, hstoredClass, hlookup⟩ :=
    List.mem_filterMap.mp hvalue
  exact ⟨storedKey, hstoredClass,
    leaValue_mem_of_lookupVal_eq_some hlookup⟩

/-- Visiting the owner class and descending into its selected value strictly
decreases the exact refined budget. -/
theorem leaResolutionBudget_classValue_lt
    {bindings : Metta.Bindings} {visited : List String}
    {key : String} {value : Metta.Atom}
    (hvalue : value ∈ Metta.Bindings.classValues bindings key)
    (hdisjoint :
      (Metta.Bindings.eqClassOrdered bindings key).any visited.contains =
        false) :
    leaResolutionBudget bindings
        (Metta.Bindings.eqClassOrdered bindings key ++ visited) value <
      leaResolutionBudget bindings visited (.var key) := by
  obtain ⟨storedKey, hstoredClass, hbinding⟩ :=
    leaClassValue_relation hvalue
  have hdrop := leaResolutionRelationBudget_sum_drop hbinding
    hstoredClass hdisjoint
  simp only [leaResolutionBudget, Metta.Atom.size]
  omega

/-- Normalized class values cannot themselves be bare variables. -/
theorem leaClassValue_nonvariable
    {bindings : Metta.Bindings}
    (hnonvariable : LeaAssignmentsNonVariable bindings)
    {key : String} {value : Metta.Atom}
    (hvalue : value ∈ Metta.Bindings.classValues bindings key) :
    ∀ target, value ≠ .var target := by
  obtain ⟨storedKey, _hstoredClass, hbinding⟩ :=
    leaClassValue_relation hvalue
  intro target heq
  subst value
  exact hnonvariable storedKey target hbinding

/-- A satisfying normalized class value lies below the current variable with
respect to every old or newly visited ancestor. -/
theorem leaResolutionBelowVisited_classValue
    {bindings : Metta.Bindings} {valuation : String → Metta.Atom}
    (hsatisfied : LeaBindingSatisfied valuation bindings)
    (hnonvariable : LeaAssignmentsNonVariable bindings)
    {visited : List String} {key : String} {value : Metta.Atom}
    (hbelow : LeaResolutionBelowVisited valuation visited (.var key))
    (hvalue : value ∈ Metta.Bindings.classValues bindings key) :
    LeaResolutionBelowVisited valuation
      (Metta.Bindings.eqClassOrdered bindings key ++ visited) value := by
  have hvalueNonvariable : ∀ target, value ≠ .var target :=
    leaClassValue_nonvariable hnonvariable hvalue
  have hvalueEq :
      valuation key = applyClassSolution valuation value :=
    leaBindingSatisfied_classValue hsatisfied hvalue
  intro dependency hdependency ancestor hancestor
  have hdependencyLt :
      (valuation dependency).size < (valuation key).size := by
    calc
      (valuation dependency).size <
          (applyClassSolution valuation value).size :=
        size_valuation_lt_apply_of_mem_vars_nonvariable
          valuation hvalueNonvariable hdependency
      _ = (valuation key).size :=
        congrArg Metta.Atom.size hvalueEq.symm
  rcases List.mem_append.mp hancestor with hclass | hvisited
  · have hkeyAncestor : valuation key = valuation ancestor :=
      hsatisfied.eq_of_mem_eqClass
        (mem_leaEqClassOrdered_iff.mp hclass)
    calc
      (valuation dependency).size < (valuation key).size := hdependencyLt
      _ = (valuation ancestor).size :=
        congrArg Metta.Atom.size hkeyAncestor
  · exact hdependencyLt.trans
      (hbelow key (by simp [Metta.Atom.vars]) ancestor hvisited)

/-- The semantic rank invariant makes the resolver's explicit overlap test
false. -/
theorem leaEqClassOrdered_any_visited_false_of_below
    {bindings : Metta.Bindings} {valuation : String → Metta.Atom}
    (hsatisfied : LeaBindingSatisfied valuation bindings)
    {visited : List String} {key : String}
    (hbelow : LeaResolutionBelowVisited valuation visited (.var key)) :
    (Metta.Bindings.eqClassOrdered bindings key).any visited.contains =
      false := by
  rw [List.any_eq_false]
  intro member hmember
  cases hcontains : visited.contains member with
  | false => simp
  | true =>
      have hvisited : member ∈ visited := by
        simpa [List.contains_iff_mem] using hcontains
      have hlt := hbelow key (by simp [Metta.Atom.vars]) member hvisited
      have heq : valuation key = valuation member :=
        hsatisfied.eq_of_mem_eqClass
          (mem_leaEqClassOrdered_iff.mp hmember)
      rw [congrArg Metta.Atom.size heq] at hlt
      exact (Nat.lt_irrefl _ hlt).elim

/-- A satisfying normalized binding set resolves every atom successfully at
the exact refined structural budget.  The proof is strong induction on that
budget: expression descent spends atom size, while class-value descent spends
the selected stored relation's `value.size + 1` charge. -/
theorem leaResolveAtomAux_some_at_budget
    {bindings : Metta.Bindings} {valuation : String → Metta.Atom}
    (hsatisfied : LeaBindingSatisfied valuation bindings)
    (hnonvariable : LeaAssignmentsNonVariable bindings) :
    ∀ (visited : List String) (atom : Metta.Atom),
      LeaResolutionBelowVisited valuation visited atom →
      ∃ resolved,
        Metta.Bindings.resolveAtomAux bindings
          (leaResolutionBudget bindings visited atom) visited atom =
            some resolved := by
  have go : ∀ budget : Nat, ∀ (visited : List String) (atom : Metta.Atom),
      leaResolutionBudget bindings visited atom = budget →
      LeaResolutionBelowVisited valuation visited atom →
      ∃ resolved,
        Metta.Bindings.resolveAtomAux bindings budget visited atom =
          some resolved := by
    intro budget
    induction budget using Nat.strong_induction_on with
    | h budget ih =>
        intro visited atom hbudget hbelow
        cases budget with
        | zero =>
            have hpositive :
                0 < leaResolutionBudget bindings visited atom := by
              simp [leaResolutionBudget]
            omega
        | succ fuel =>
            cases atom with
            | sym symbol =>
                exact ⟨.sym symbol, by
                  simp [Metta.Bindings.resolveAtomAux]⟩
            | gnd ground =>
                exact ⟨.gnd ground, by
                  simp [Metta.Bindings.resolveAtomAux]⟩
            | var key =>
                have hdisjoint :=
                  leaEqClassOrdered_any_visited_false_of_below
                    hsatisfied hbelow
                cases hvalues : Metta.Bindings.classValues bindings key with
                | nil =>
                    exact ⟨.var (Metta.Bindings.eqRepresentative bindings key), by
                      simp [Metta.Bindings.resolveAtomAux, hdisjoint, hvalues]⟩
                | cons value rest =>
                    have hvalueMem :
                        value ∈ Metta.Bindings.classValues bindings key := by
                      simp [hvalues]
                    have hvalueNonvariable : ∀ target, value ≠ .var target :=
                      leaClassValue_nonvariable hnonvariable hvalueMem
                    have hbelowValue :
                        LeaResolutionBelowVisited valuation
                          (Metta.Bindings.eqClassOrdered bindings key ++ visited)
                          value :=
                      leaResolutionBelowVisited_classValue hsatisfied
                        hnonvariable hbelow hvalueMem
                    have hnextLt :
                        leaResolutionBudget bindings
                            (Metta.Bindings.eqClassOrdered bindings key ++ visited)
                            value < Nat.succ fuel := by
                      have hlt := leaResolutionBudget_classValue_lt
                        hvalueMem hdisjoint
                      rw [hbudget] at hlt
                      exact hlt
                    obtain ⟨resolved, hresolved⟩ :=
                      ih (leaResolutionBudget bindings
                            (Metta.Bindings.eqClassOrdered bindings key ++ visited)
                            value)
                        hnextLt
                        (Metta.Bindings.eqClassOrdered bindings key ++ visited)
                        value rfl hbelowValue
                    have hresolvedFuel :
                        Metta.Bindings.resolveAtomAux bindings fuel
                            (Metta.Bindings.eqClassOrdered bindings key ++ visited)
                            value = some resolved :=
                      Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.resolveAtomAux_some_mono hresolved
                        (Nat.le_of_lt_succ hnextLt)
                    cases value with
                    | var target => exact (hvalueNonvariable target rfl).elim
                    | sym symbol =>
                        exact ⟨resolved, by
                          simp [Metta.Bindings.resolveAtomAux, hdisjoint,
                            hvalues, hresolvedFuel]⟩
                    | gnd ground =>
                        exact ⟨resolved, by
                          simp [Metta.Bindings.resolveAtomAux, hdisjoint,
                            hvalues, hresolvedFuel]⟩
                    | expr atoms =>
                        exact ⟨resolved, by
                          simp [Metta.Bindings.resolveAtomAux, hdisjoint,
                            hvalues, hresolvedFuel]⟩
            | expr atoms =>
                have hchildren : ∀ child ∈ atoms, ∃ resolved,
                    Metta.Bindings.resolveAtomAux bindings fuel visited child =
                      some resolved := by
                  intro child hchild
                  have hnextLt :
                      leaResolutionBudget bindings visited child <
                        Nat.succ fuel := by
                    have hlt := leaResolutionBudget_child_lt
                      bindings visited hchild
                    rw [hbudget] at hlt
                    exact hlt
                  obtain ⟨resolved, hresolved⟩ :=
                    ih (leaResolutionBudget bindings visited child)
                      hnextLt visited child rfl
                      (hbelow.of_expr_mem hchild)
                  exact ⟨resolved,
                    Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.resolveAtomAux_some_mono hresolved
                      (Nat.le_of_lt_succ hnextLt)⟩
                have hmap : ∃ resolvedAtoms,
                    atoms.mapM
                        (Metta.Bindings.resolveAtomAux bindings fuel visited) =
                      some resolvedAtoms := by
                  have mapSome : ∀ xs : List Metta.Atom,
                      (∀ child ∈ xs, ∃ resolved,
                        Metta.Bindings.resolveAtomAux bindings fuel visited
                            child = some resolved) →
                      ∃ resolvedAtoms,
                        xs.mapM (Metta.Bindings.resolveAtomAux bindings fuel
                          visited) = some resolvedAtoms := by
                    intro xs
                    induction xs with
                    | nil => intro _hchildren; exact ⟨[], rfl⟩
                    | cons head tail tailIH =>
                        intro hall
                        obtain ⟨resolvedHead, hhead⟩ :=
                          hall head (by simp)
                        obtain ⟨resolvedTail, htail⟩ := tailIH (by
                          intro child hchild
                          exact hall child (by simp [hchild]))
                        exact ⟨resolvedHead :: resolvedTail, by
                          simp [hhead, htail]⟩
                  exact mapSome atoms hchildren
                obtain ⟨resolvedAtoms, hresolvedAtoms⟩ := hmap
                exact ⟨.expr resolvedAtoms, by
                  simp [Metta.Bindings.resolveAtomAux, hresolvedAtoms]⟩
  intro visited atom hbelow
  exact go (leaResolutionBudget bindings visited atom)
    visited atom rfl hbelow

/-- At the empty visited set, the refined theorem specializes exactly to the
runtime fuel used by `Bindings.hasLoop`. -/
theorem leaResolveAtomAux_some_of_satisfied
    {bindings : Metta.Bindings} {valuation : String → Metta.Atom}
    (hsatisfied : LeaBindingSatisfied valuation bindings)
    (hnonvariable : LeaAssignmentsNonVariable bindings)
    (key : String) :
    ∃ resolved,
      Metta.Bindings.resolveAtomAux bindings
          (Metta.Bindings.resolutionFuel bindings (.var key)) [] (.var key) =
        some resolved := by
  simpa [leaResolutionBudget_nil_eq_resolutionFuel] using
    (leaResolveAtomAux_some_at_budget hsatisfied hnonvariable
      [] (.var key) (leaResolutionBelowVisited_nil valuation (.var key)))

/-- Every satisfiable normalized repaired-LeaTTa binding set passes the full
runtime loop check.  Equality irreflexivity discharges the direct scan, while
the refined-budget theorem discharges recursive resolution for every observed
variable. -/
theorem leaBindings_hasLoop_false_of_satisfied
    {bindings : Metta.Bindings} {valuation : String → Metta.Atom}
    (hsatisfied : LeaBindingSatisfied valuation bindings)
    (hnonvariable : LeaAssignmentsNonVariable bindings)
    (hirreflexive : LeaEqualitiesIrreflexive bindings) :
    bindings.hasLoop = false := by
  apply Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.hasLoop_false_of_resolveAtomAux_some
  · exact leaBindings_directLoop_false hnonvariable hirreflexive
  · intro key _hkey
    exact leaResolveAtomAux_some_of_satisfied
      hsatisfied hnonvariable key

/-- Public wrapper for equality-irreflexivity preservation through the raw
list matcher. -/
theorem leaMatchAll_result_equalitiesIrreflexive
    {lefts rights : List Metta.Atom} {seeds : List Metta.Bindings}
    {out : Metta.Bindings}
    (hseeds : ∀ seed ∈ seeds, LeaEqualitiesIrreflexive seed)
    (hout : out ∈ Metta.matchAll none seeds lefts rights) :
    LeaEqualitiesIrreflexive out := by
  exact leaMatchAll_result_equalitiesIrreflexive_aux lefts
    (fun left _ => leaMatchIrreflexivePack left) hseeds hout

/-- Any satisfying raw atom-match output survives LeaTTa's public loop
filter. -/
theorem leaMatchAtomsWith_hasLoop_false_of_satisfied
    {left right : Metta.Atom} {out : Metta.Bindings}
    {valuation : String → Metta.Atom}
    (hout : out ∈ Metta.matchAtomsWith none left right)
    (hsatisfied : LeaBindingSatisfied valuation out) :
    out.hasLoop = false := by
  exact leaBindings_hasLoop_false_of_satisfied hsatisfied
    (leaMatchAtomsWith_result_assignmentsNonVariable hout)
    (leaMatchAtomsWith_result_equalitiesIrreflexive hout)

/-- Any satisfying raw list-match result from the empty seed likewise
survives the public loop boundary. -/
theorem leaMatchAll_empty_hasLoop_false_of_satisfied
    {lefts rights : List Metta.Atom} {out : Metta.Bindings}
    {valuation : String → Metta.Atom}
    (hout : out ∈ Metta.matchAll none [Metta.Bindings.empty] lefts rights)
    (hsatisfied : LeaBindingSatisfied valuation out) :
    out.hasLoop = false := by
  apply leaBindings_hasLoop_false_of_satisfied hsatisfied
  · exact leaMatchAll_result_assignmentsNonVariable
      (by intro seed hseed
          simp only [List.mem_singleton] at hseed
          subst seed
          exact leaAssignmentsNonVariable_empty)
      hout
  · exact leaMatchAll_result_equalitiesIrreflexive
      (by intro seed hseed
          simp only [List.mem_singleton] at hseed
          subst seed
          exact leaEqualitiesIrreflexive_empty)
      hout

/-- Simultaneous semantic and fragment-preservation contract for one fixed
left matcher atom.  The recursive expression proof supplies this contract for
each immediate child before invoking the list matcher. -/
private structure LeaMatchSemanticPack (left : Metta.Atom) : Prop where
  solutionTheory : ∀ {right out},
    MettaAtomNoFloat left → MettaAtomNoFloat right →
    out ∈ Metta.matchAtomsWith none left right →
    ∀ valuation,
      LeaBindingSatisfied valuation out ↔
        MettaEquationSatisfied valuation (left, right)
  resultNoFloat : ∀ {right out},
    MettaAtomNoFloat left → MettaAtomNoFloat right →
    out ∈ Metta.matchAtomsWith none left right →
    LeaBindingsNoFloat out

private theorem leaMatchAll_semanticPack
    (lefts : List Metta.Atom)
    (hpacks : ∀ left ∈ lefts, LeaMatchSemanticPack left) :
    ∀ {rights : List Metta.Atom} {seeds : List Metta.Bindings}
      {out : Metta.Bindings},
      (∀ left ∈ lefts, MettaAtomNoFloat left) →
      (∀ right ∈ rights, MettaAtomNoFloat right) →
      (∀ seed ∈ seeds, LeaBindingsNoFloat seed) →
      out ∈ Metta.matchAll none seeds lefts rights →
      (∃ seed ∈ seeds, ∀ valuation,
        LeaBindingSatisfied valuation out ↔
          LeaBindingSatisfied valuation seed ∧
            MettaAtomListsSatisfied valuation lefts rights) ∧
        LeaBindingsNoFloat out := by
  induction lefts with
  | nil =>
      intro rights seeds out _hlefts hrights hseeds hout
      cases rights with
      | nil =>
          simp only [Metta.matchAll] at hout
          refine ⟨⟨out, hout, ?_⟩, hseeds out hout⟩
          intro valuation
          simp [MettaAtomListsSatisfied]
      | cons right rights =>
          simp [Metta.matchAll] at hout
  | cons left lefts ih =>
      intro rights seeds out hleftNoFloat hrightNoFloat hseedsNoFloat hout
      cases rights with
      | nil =>
          simp [Metta.matchAll] at hout
      | cons right rights =>
          have hleftHead : MettaAtomNoFloat left :=
            hleftNoFloat left (by simp)
          have hrightHead : MettaAtomNoFloat right :=
            hrightNoFloat right (by simp)
          have hleftTail : ∀ atom ∈ lefts, MettaAtomNoFloat atom := by
            intro atom hmem
            exact hleftNoFloat atom (by simp [hmem])
          have hrightTail : ∀ atom ∈ rights, MettaAtomNoFloat atom := by
            intro atom hmem
            exact hrightNoFloat atom (by simp [hmem])
          have hpackHead : LeaMatchSemanticPack left :=
            hpacks left (by simp)
          have hpacksTail : ∀ atom ∈ lefts,
              LeaMatchSemanticPack atom := by
            intro atom hmem
            exact hpacks atom (by simp [hmem])
          let subs := (Metta.matchAtomsWith none left right).filter
            (fun bindings => !bindings.hasLoop)
          let next := seeds.flatMap fun seed =>
            subs.flatMap fun sub => Metta.Bindings.merge seed sub
          have houtTail :
              out ∈ Metta.matchAll none next lefts rights := by
            simpa [Metta.matchAll, subs, next] using hout
          have hnextNoFloat : ∀ nextBinding ∈ next,
              LeaBindingsNoFloat nextBinding := by
            intro nextBinding hnext
            obtain ⟨seed, hseed, hnext⟩ := List.mem_flatMap.mp hnext
            obtain ⟨sub, hsub, hmerge⟩ := List.mem_flatMap.mp hnext
            have hsubRaw : sub ∈ Metta.matchAtomsWith none left right :=
              (List.mem_filter.mp hsub).1
            exact leaMerge_result_noFloat
              (hseedsNoFloat seed hseed)
              (hpackHead.resultNoFloat hleftHead hrightHead hsubRaw)
              hmerge
          obtain ⟨⟨middle, hmiddle, houtTheory⟩, houtNoFloat⟩ :=
            ih hpacksTail hleftTail hrightTail hnextNoFloat houtTail
          obtain ⟨seed, hseed, hmiddle⟩ := List.mem_flatMap.mp hmiddle
          obtain ⟨sub, hsub, hmerge⟩ := List.mem_flatMap.mp hmiddle
          have hsubRaw : sub ∈ Metta.matchAtomsWith none left right :=
            (List.mem_filter.mp hsub).1
          refine ⟨⟨seed, hseed, ?_⟩, houtNoFloat⟩
          intro valuation
          rw [houtTheory valuation,
            leaMerge_solution_iff valuation
              (hseedsNoFloat seed hseed)
              (hpackHead.resultNoFloat hleftHead hrightHead hsubRaw)
              hmerge,
            hpackHead.solutionTheory hleftHead hrightHead hsubRaw valuation]
          simp [MettaAtomListsSatisfied, MettaEquationSatisfied, and_assoc]

private theorem leaMatchSemanticPack
    (left : Metta.Atom) : LeaMatchSemanticPack left := by
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_ left
  · intro symbol
    refine ⟨?_, ?_⟩
    · intro right out hleft hright hout valuation
      cases right with
      | sym other =>
          by_cases h : symbol = other
          · subst other
            simp [Metta.matchAtomsWith] at hout
            subst out
            simp [LeaBindingSatisfied, MettaEquationSatisfied,
              applyClassSolution]
          · simp [Metta.matchAtomsWith, h] at hout
      | var v =>
          simp [Metta.matchAtomsWith] at hout
          subst out
          simp [LeaBindingSatisfied, MettaEquationSatisfied,
            applyClassSolution, eq_comm]
      | gnd ground =>
          simp [Metta.matchAtomsWith, Metta.Atom.equiv] at hout
      | expr atoms =>
          simp [Metta.matchAtomsWith, Metta.Atom.equiv] at hout
    · intro right out hleft hright hout
      cases right with
      | sym other =>
          by_cases h : symbol = other
          · subst other
            simp [Metta.matchAtomsWith] at hout
            subst out
            simp [LeaBindingsNoFloat]
          · simp [Metta.matchAtomsWith, h] at hout
      | var v =>
          simp [Metta.matchAtomsWith] at hout
          subst out
          intro key value hmem
          simp at hmem
          rcases hmem with ⟨rfl, rfl⟩
          simp [MettaAtomNoFloat]
      | gnd ground =>
          simp [Metta.matchAtomsWith, Metta.Atom.equiv] at hout
      | expr atoms =>
          simp [Metta.matchAtomsWith, Metta.Atom.equiv] at hout
  · intro v
    refine ⟨?_, ?_⟩
    · intro right out hleft hright hout valuation
      cases right with
      | sym symbol =>
          simp [Metta.matchAtomsWith] at hout
          subst out
          simp [LeaBindingSatisfied, MettaEquationSatisfied,
            applyClassSolution]
      | var other =>
          by_cases h : v = other
          · subst other
            simp [Metta.matchAtomsWith] at hout
            subst out
            simp [LeaBindingSatisfied, MettaEquationSatisfied,
              applyClassSolution]
          · have hbeq : (v == other) = false := by simp [h]
            simp [Metta.matchAtomsWith, hbeq] at hout
            subst out
            simp [LeaBindingSatisfied, MettaEquationSatisfied,
              applyClassSolution]
      | gnd ground =>
          simp [Metta.matchAtomsWith] at hout
          subst out
          simp [LeaBindingSatisfied, MettaEquationSatisfied,
            applyClassSolution]
      | expr atoms =>
          cases hoccurs : Metta.Subst.occurs v (.expr atoms) with
          | true =>
              simp [Metta.matchAtomsWith, hoccurs] at hout
          | false =>
              simp [Metta.matchAtomsWith, hoccurs] at hout
              subst out
              simp [LeaBindingSatisfied, MettaEquationSatisfied,
                applyClassSolution]
    · intro right out hleft hright hout
      cases right with
      | sym symbol =>
          simp [Metta.matchAtomsWith] at hout
          subst out
          exact leaBindingsNoFloat_addValRaw
            (bindings := []) (by simp [LeaBindingsNoFloat]) hright
      | var other =>
          by_cases h : v = other
          · subst other
            simp [Metta.matchAtomsWith] at hout
            subst out
            simp [LeaBindingsNoFloat]
          · have hbeq : (v == other) = false := by simp [h]
            simp [Metta.matchAtomsWith, hbeq] at hout
            subst out
            simpa [Metta.Bindings.addEqRaw, h] using
              (leaBindingsNoFloat_addEqRaw
                (bindings := []) (left := v) (right := other)
                (by simp [LeaBindingsNoFloat]))
      | gnd ground =>
          simp [Metta.matchAtomsWith] at hout
          subst out
          exact leaBindingsNoFloat_addValRaw
            (bindings := []) (by simp [LeaBindingsNoFloat]) hright
      | expr atoms =>
          cases hoccurs : Metta.Subst.occurs v (.expr atoms) with
          | true =>
              simp [Metta.matchAtomsWith, hoccurs] at hout
          | false =>
              simp [Metta.matchAtomsWith, hoccurs] at hout
              subst out
              exact leaBindingsNoFloat_addValRaw
                (bindings := []) (by simp [LeaBindingsNoFloat]) hright
  · intro ground
    refine ⟨?_, ?_⟩
    · intro right out hleft hright hout valuation
      cases right with
      | sym symbol =>
          simp [Metta.matchAtomsWith, Metta.Atom.equiv] at hout
      | var v =>
          simp [Metta.matchAtomsWith] at hout
          subst out
          simp [LeaBindingSatisfied, MettaEquationSatisfied,
            applyClassSolution, eq_comm]
      | gnd other =>
          cases hequiv : Metta.Ground.equiv ground other with
          | false =>
              simp [Metta.matchAtomsWith, Metta.Atom.equiv, hequiv] at hout
          | true =>
              simp [Metta.matchAtomsWith, Metta.Atom.equiv, hequiv] at hout
              subst out
              have hground : ground = other :=
                ground_eq_of_equiv_of_noFloat hleft hright hequiv
              subst other
              simp [LeaBindingSatisfied, MettaEquationSatisfied,
                applyClassSolution]
      | expr atoms =>
          simp [Metta.matchAtomsWith, Metta.Atom.equiv] at hout
    · intro right out hleft hright hout
      cases right with
      | sym symbol =>
          simp [Metta.matchAtomsWith, Metta.Atom.equiv] at hout
      | var v =>
          simp [Metta.matchAtomsWith] at hout
          subst out
          exact leaBindingsNoFloat_addValRaw
            (bindings := []) (by simp [LeaBindingsNoFloat]) hleft
      | gnd other =>
          cases hequiv : Metta.Ground.equiv ground other with
          | false =>
              simp [Metta.matchAtomsWith, Metta.Atom.equiv, hequiv] at hout
          | true =>
              simp [Metta.matchAtomsWith, Metta.Atom.equiv, hequiv] at hout
              subst out
              simp [LeaBindingsNoFloat]
      | expr atoms =>
          simp [Metta.matchAtomsWith, Metta.Atom.equiv] at hout
  · intro atoms ih
    refine ⟨?_, ?_⟩
    · intro right out hleft hright hout valuation
      cases right with
      | sym symbol =>
          simp [Metta.matchAtomsWith, Metta.Atom.equiv] at hout
      | var v =>
          cases hoccurs : Metta.Subst.occurs v (.expr atoms) with
          | true =>
              simp [Metta.matchAtomsWith, hoccurs] at hout
          | false =>
              simp [Metta.matchAtomsWith, hoccurs] at hout
              subst out
              simp [LeaBindingSatisfied, MettaEquationSatisfied,
                applyClassSolution, eq_comm]
      | gnd ground =>
          simp [Metta.matchAtomsWith, Metta.Atom.equiv] at hout
      | expr rights =>
          obtain ⟨⟨seed, hseed, htheory⟩, _houtNoFloat⟩ :=
            leaMatchAll_semanticPack atoms ih
              (by simpa [MettaAtomNoFloat] using hleft)
              (by simpa [MettaAtomNoFloat] using hright)
              (by intro seed hmem
                  simp at hmem
                  subst seed
                  simp [LeaBindingsNoFloat]) hout
          simp only [List.mem_singleton] at hseed
          subst seed
          simpa [LeaBindingSatisfied, MettaEquationSatisfied,
            MettaAtomListsSatisfied, applyClassSolution] using
            htheory valuation
    · intro right out hleft hright hout
      cases right with
      | sym symbol =>
          simp [Metta.matchAtomsWith, Metta.Atom.equiv] at hout
      | var v =>
          cases hoccurs : Metta.Subst.occurs v (.expr atoms) with
          | true =>
              simp [Metta.matchAtomsWith, hoccurs] at hout
          | false =>
              simp [Metta.matchAtomsWith, hoccurs] at hout
              subst out
              exact leaBindingsNoFloat_addValRaw
                (bindings := []) (by simp [LeaBindingsNoFloat]) hleft
      | gnd ground =>
          simp [Metta.matchAtomsWith, Metta.Atom.equiv] at hout
      | expr rights =>
          exact (leaMatchAll_semanticPack atoms ih
            (by simpa [MettaAtomNoFloat] using hleft)
            (by simpa [MettaAtomNoFloat] using hright)
            (by intro seed hmem
                simp at hmem
                subst seed
                simp [LeaBindingsNoFloat]) hout).2

/-- Every successful repaired-LeaTTa matcher output presents exactly the
equation between its two input atoms on the HE-translatable fragment. -/
theorem leaMatchAtoms_solution_iff
    (valuation : String → Metta.Atom)
    {left right : Metta.Atom} {out : Metta.Bindings}
    (hleftNoFloat : MettaAtomNoFloat left)
    (hrightNoFloat : MettaAtomNoFloat right)
    (hout : out ∈ Metta.matchAtoms left right) :
    LeaBindingSatisfied valuation out ↔
      MettaEquationSatisfied valuation (left, right) := by
  have hraw : out ∈ Metta.matchAtomsWith none left right :=
    ((by simpa [Metta.matchAtoms] using hout) :
      out ∈ Metta.matchAtomsWith none left right ∧ out.hasLoop = false).1
  exact (leaMatchSemanticPack left).solutionTheory
    hleftNoFloat hrightNoFloat hraw valuation

/-- Repaired-LeaTTa matching cannot leave the HE-translatable fragment. -/
theorem leaMatchAtoms_result_noFloat
    {left right : Metta.Atom} {out : Metta.Bindings}
    (hleftNoFloat : MettaAtomNoFloat left)
    (hrightNoFloat : MettaAtomNoFloat right)
    (hout : out ∈ Metta.matchAtoms left right) :
    LeaBindingsNoFloat out := by
  have hraw : out ∈ Metta.matchAtomsWith none left right :=
    ((by simpa [Metta.matchAtoms] using hout) :
      out ∈ Metta.matchAtomsWith none left right ∧ out.hasLoop = false).1
  exact (leaMatchSemanticPack left).resultNoFloat
    hleftNoFloat hrightNoFloat hraw

/-! ### Actual native matcher models and dependency admission -/

/-- A valuation respects equality classes and a selected value in each nonempty class. The choice may vary
across classes and need not follow any list order. -/
def LeaClassChoiceSatisfied (valuation : String → Metta.Atom)
    (bindings : Metta.Bindings) : Prop :=
  (∀ source target, target ∈ Metta.Bindings.eqClass bindings source →
    valuation source = valuation target) ∧
  (∀ key, Metta.Bindings.classValues bindings key ≠ [] →
    ∃ value ∈ Metta.Bindings.classValues bindings key,
      valuation key = applyClassSolution valuation value)

/-- Any choice of one value equation per nonempty class generates the full
stored theory. Native insertion and reconciliation preserve this invariant;
cycle admission remains a separate final check. -/
def LeaClassChoiceBasis (bindings : Metta.Bindings) : Prop :=
  ∀ valuation, LeaClassChoiceSatisfied valuation bindings →
    LeaBindingSatisfied valuation bindings

/-- Homomorphic substitution depends only on the variables occurring in its
argument. -/
theorem applyClassSolution_congr_support
    {left right : String → Metta.Atom} (atom : Metta.Atom)
    (hagrees : ∀ name ∈ atom.vars, left name = right name) :
    applyClassSolution left atom = applyClassSolution right atom := by
  induction atom using Metta.Atom.recAux with
  | sym name => simp [applyClassSolution]
  | var name => simpa only [applyClassSolution] using hagrees name (by simp [Metta.Atom.vars])
  | gnd ground => simp [applyClassSolution]
  | expr atoms ih =>
      simp only [applyClassSolution]
      congr 1
      apply List.map_congr_left
      intro atom hmem
      apply ih atom hmem
      intro name hname
      apply hagrees name
      simp only [Metta.Atom.vars, List.mem_flatten, List.mem_map]
      exact ⟨atom.vars, ⟨atom, hmem, rfl⟩, hname⟩

/-- Interpreting an already interpreted term composes its valuations. -/
theorem applyClassSolution_comp
    (outer inner : String → Metta.Atom) (atom : Metta.Atom) :
    applyClassSolution outer (applyClassSolution inner atom) =
      applyClassSolution (fun name => applyClassSolution outer (inner name)) atom := by
  induction atom using Metta.Atom.recAux with
  | sym name => simp [applyClassSolution]
  | var name => simp [applyClassSolution]
  | gnd ground => simp [applyClassSolution]
  | expr atoms ih =>
      simp only [applyClassSolution, List.map_map]
      congr 1
      exact List.map_congr_left ih

/-- Any substitution into a binding model is again a binding model. -/
theorem LeaBindingSatisfied.postcompose
    {model : String → Metta.Atom} {bindings : Metta.Bindings}
    (hmodel : LeaBindingSatisfied model bindings) (outer : String → Metta.Atom) :
    LeaBindingSatisfied (fun name => applyClassSolution outer (model name)) bindings := by
  constructor
  · intro key value hmem
    change applyClassSolution outer (model key) = _
    rw [hmodel.1 key value hmem, applyClassSolution_comp]
  · intro left right hmem
    exact congrArg (applyClassSolution outer) (hmodel.2 left right hmem)

/-- With the free classes fixed, selected equations have at most one finite
model whenever all stored constraints have a non-variable finite model. -/
theorem LeaClassChoiceSatisfied.eq_of_model
    {bindings : Metta.Bindings} {selected model : String → Metta.Atom}
    (hnonvariable : LeaAssignmentsNonVariable bindings)
    (hselected : LeaClassChoiceSatisfied selected bindings)
    (hmodel : LeaBindingSatisfied model bindings)
    (hfree : ∀ key, Metta.Bindings.classValues bindings key = [] →
      selected key = model key) : selected = model := by
  have hkeys : ∀ bound key, (model key).size = bound → selected key = model key := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound ih =>
        intro key hsize
        cases hvalues : Metta.Bindings.classValues bindings key with
        | nil => exact hfree key hvalues
        | cons first rest =>
            obtain ⟨value, hvalue, hselectedKey⟩ :=
              hselected.2 key (by simp [hvalues])
            have hmodelKey := leaBindingSatisfied_classValue hmodel hvalue
            rw [hselectedKey, hmodelKey]
            apply applyClassSolution_congr_support
            intro dependency hdependency
            have hlt := size_valuation_lt_apply_of_mem_vars_nonvariable model
              (leaClassValue_nonvariable hnonvariable hvalue) hdependency
            rw [← hmodelKey, hsize] at hlt
            exact ih (model dependency).size hlt dependency rfl
  funext key
  exact hkeys (model key).size key rfl

/-- A model whose free-class images remain variables of those same classes
makes the selected equations a complete basis. -/
theorem leaClassChoiceBasis_of_model_free_classes
    {bindings : Metta.Bindings} {model : String → Metta.Atom}
    (hnonvariable : LeaAssignmentsNonVariable bindings)
    (hmodel : LeaBindingSatisfied model bindings)
    (hfree : ∀ key, Metta.Bindings.classValues bindings key = [] →
      ∃ representative, model key = .var representative ∧
        representative ∈ Metta.Bindings.eqClass bindings key) :
    LeaClassChoiceBasis bindings := by
  intro valuation hselected
  have hcomposed := hmodel.postcompose valuation
  have hagreement : valuation =
      fun name => applyClassSolution valuation (model name) := by
    apply hselected.eq_of_model hnonvariable hcomposed
    intro key hkey
    obtain ⟨representative, hmodelKey, hclass⟩ := hfree key hkey
    rw [hmodelKey]
    simpa only [applyClassSolution] using hselected.1 key representative hclass
  exact hagreement.symm ▸ hcomposed
/-- Empty value support is a property of an equality class, independently of
which member is used to query it. -/
theorem leaClassValues_nil_of_mem_class
    {bindings : Metta.Bindings} {key member : String}
    (hclass : member ∈ Metta.Bindings.eqClass bindings key)
    (hempty : Metta.Bindings.classValues bindings key = []) :
    Metta.Bindings.classValues bindings member = [] := by
  unfold Metta.Bindings.classValues at hempty ⊢
  apply List.filterMap_eq_nil_iff.mpr
  intro name hvariable
  apply List.filterMap_eq_nil_iff.mp hempty name
  apply mem_leaEqClassOrdered_iff.mpr
  rw [mem_leaEqClass_iff_reachable] at hclass ⊢
  exact hclass.trans (mem_leaEqClass_iff_reachable.mp
    (mem_leaEqClassOrdered_iff.mp hvariable))

/-- A trace whose free-class entries are class-internal aliases leaves those
free classes represented by their own variables. -/
theorem eliminationTraceValuation_free_class
    (trace : List (String × Metta.Atom)) (bindings : Metta.Bindings)
    (hentries : ∀ key value, (key, value) ∈ trace →
      Metta.Bindings.classValues bindings key = [] →
        ∃ target, value = .var target ∧
          target ∈ Metta.Bindings.eqClass bindings key) :
    ∀ key, Metta.Bindings.classValues bindings key = [] →
      ∃ representative, eliminationTraceValuation trace key = .var representative ∧
        representative ∈ Metta.Bindings.eqClass bindings key := by
  induction trace with
  | nil =>
      intro key _
      refine ⟨key, rfl, ?_⟩
      rw [mem_leaEqClass_iff_reachable]
  | cons binding trace ih =>
      obtain ⟨headKey, headValue⟩ := binding
      have htail : ∀ key value, (key, value) ∈ trace →
          Metta.Bindings.classValues bindings key = [] →
          ∃ target, value = .var target ∧
            target ∈ Metta.Bindings.eqClass bindings key := by
        intro key value hmem
        exact hentries key value (by simp [hmem])
      intro key hempty
      by_cases hkey : key = headKey
      · subst headKey
        obtain ⟨target, rfl, hclass⟩ :=
          hentries key headValue (by simp) hempty
        obtain ⟨representative, hvalue, hrepresentative⟩ :=
          ih htail target (leaClassValues_nil_of_mem_class hclass hempty)
        refine ⟨representative, ?_, ?_⟩
        · simpa [eliminationTraceValuation, applyClassSolution] using hvalue
        · rw [mem_leaEqClass_iff_reachable] at hclass hrepresentative ⊢
          exact hclass.trans hrepresentative
      · obtain ⟨representative, hvalue, hrepresentative⟩ := ih htail key hempty
        refine ⟨representative, ?_, hrepresentative⟩
        simpa [eliminationTraceValuation, Function.update, hkey] using hvalue

/-- Rebuilding a successful reconciliation leaves no non-variable trace entry
in a class with no stored value. -/
theorem reconciliation_trace_free_entries
    {candidate source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hrun : wholeBindingReconciliation source extra = some result) :
    ∀ key value, (key, value) ∈ result →
      Metta.Bindings.classValues
        (Metta.Bindings.rebuildFromReconciliation candidate source extra result) key = [] →
      ∃ target, value = .var target ∧ target ∈ Metta.Bindings.eqClass
        (Metta.Bindings.rebuildFromReconciliation candidate source extra result) key := by
  intro key value hmem hempty
  cases value with
  | var target =>
      exact ⟨target, rfl, rebuildFromReconciliation_connects_alias
        candidate source extra result
        (wholeBindingReconciliation_result_alias_mem hrun hmem)⟩
  | sym name | gnd name | expr name =>
      exact (no_leaValue_of_lookupVal_eq_none
        (leaLookupVal_eq_none_of_classValues_eq_nil hempty) _
          (val_mem_rebuildFromReconciliation_iff.mpr
            ⟨hmem, by intro target h; cases h⟩)).elim

/-- The concrete triangular valuation models the exact successful reconciliation
result, including all entries that are not selected by class lookup. -/
theorem reconciliation_trace_valuation_satisfies
    {source : Metta.Bindings} {extra : List (Metta.Atom × Metta.Atom)}
    {result : Metta.Subst}
    (hrun : wholeBindingReconciliation source extra = some result) :
    MettaConstraintsSatisfied
      (eliminationTraceValuation (unificationEliminationTrace
        (Metta.Bindings.equationFuel (Metta.Bindings.equations source ++ extra))
        (Metta.Bindings.equations source ++ extra))) result := by
  have htrace := eliminationTraceValuation_satisfies
    (unificationEliminationTrace
      (Metta.Bindings.equationFuel (Metta.Bindings.equations source ++ extra))
      (Metta.Bindings.equations source ++ extra))
    (wholeBindingReconciliation_eliminationTrace_triangular hrun)
    (unificationEliminationTrace_key_not_mem_value_vars _ _)
  simpa only [wholeBindingReconciliation_result_eq_eliminationTrace_reverse hrun,
    MettaConstraintsSatisfied, List.mem_reverse] using htrace

/-- Whole-system reconciliation establishes the complete selected-equation
basis. Candidate equalities must follow from the equations actually reconciled;
this is discharged by each native operation constructing the candidate. -/
theorem rebuildFromReconciliation_classChoiceBasis
    {candidate source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hextraNoFloat : ∀ equation ∈ extra,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hrun : wholeBindingReconciliation source extra = some result)
    (hcandidate : ∀ valuation, LeaBindingSatisfied valuation source →
      MettaEquationsSatisfied valuation extra → LeaEqualitySatisfied valuation candidate) :
    LeaClassChoiceBasis
      (Metta.Bindings.rebuildFromReconciliation candidate source extra result) := by
  let trace := unificationEliminationTrace
    (Metta.Bindings.equationFuel (Metta.Bindings.equations source ++ extra))
    (Metta.Bindings.equations source ++ extra)
  let model := eliminationTraceValuation trace
  have hresult : MettaConstraintsSatisfied model result :=
    reconciliation_trace_valuation_satisfies hrun
  have hsource := (wholeBindingReconciliation_solution_iff model
    hsourceNoFloat hextraNoFloat hrun).mp hresult
  have hequalities := hcandidate model hsource.1 hsource.2
  have hbase : LeaBindingSatisfied model (rebuildBindingsFromUnifier candidate result) := by
    apply (leaBindingSatisfied_append_iff model
      (leaEqualitySkeleton candidate) (Metta.Bindings.ofSubst result)).mpr
    constructor
    · constructor
      · intro key value hmem
        exact (val_not_mem_leaEqualitySkeleton hmem).elim
      · intro left right hmem
        exact hequalities left right (eq_mem_leaEqualitySkeleton_iff.mp hmem)
    · exact (leaOfSubst_solution_iff model result).mpr hresult
  have hmodel := (rebuildFromReconciliation_solution_iff model
    hsourceNoFloat hextraNoFloat hrun).mpr hbase
  apply leaClassChoiceBasis_of_model_free_classes
    (rebuildFromReconciliation_assignmentsNonVariable candidate source extra result) hmodel
  apply eliminationTraceValuation_free_class
  intro key value hmem hempty
  apply reconciliation_trace_free_entries hrun key value ?_ hempty
  rw [wholeBindingReconciliation_result_eq_eliminationTrace_reverse hrun]
  simpa only [List.mem_reverse] using hmem

/-- Class-value membership records the selected lookup at a connected key. -/
theorem leaClassValue_mem_iff
    {bindings : Metta.Bindings} {key : String} {value : Metta.Atom} :
    value ∈ Metta.Bindings.classValues bindings key ↔
      ∃ member, member ∈ Metta.Bindings.eqClass bindings key ∧
        Metta.Bindings.lookupVal bindings member = some value := by
  simp only [Metta.Bindings.classValues, List.mem_filterMap]
  constructor
  · rintro ⟨member, hclass, hlookup⟩
    exact ⟨member, mem_leaEqClassOrdered_iff.mp hclass, hlookup⟩
  · rintro ⟨member, hclass, hlookup⟩
    exact ⟨member, mem_leaEqClassOrdered_iff.mpr hclass, hlookup⟩

/-- The variables of a selected class value are part of the whole stored support. -/
theorem leaClassValue_vars_subset
    {bindings : Metta.Bindings} {key : String} {value : Metta.Atom}
    (member : value ∈ Metta.Bindings.classValues bindings key) :
    value.vars ⊆ bindings.vars := by
  intro name mentioned
  obtain ⟨owner, _, lookup⟩ := leaClassValue_mem_iff.mp member
  exact bindingRelation_vars_subset (lookupVal_some_val_mem lookup)
    (by simp [Metta.Bindings.vars,mentioned])

/-! ## Disjoint binding components -/

private theorem leaEdge_endpoint_vars {bindings : Metta.Bindings} {left right : String}
    (edge : (left,right) ∈ leaEqualityEdges bindings) :
    left ∈ bindings.vars ∧ right ∈ bindings.vars := by
  have present := mem_leaEqualityEdges_iff.mp edge
  constructor <;> apply bindingRelation_vars_subset present <;> simp [Metta.Bindings.vars]

/-- Equality walks originating outside the frame cannot enter that frame
when the complete supports of the two components are disjoint. -/
theorem leaEqualityReachable_append_frame
    {front frame : Metta.Bindings} (disjoint : List.Disjoint front.vars frame.vars)
    {start finish : String} (outside : start ∉ frame.vars)
    (reachable : (EqualityClosure.edgeGraph (leaEqualityEdges (front ++ frame))).Reachable start finish) :
    (EqualityClosure.edgeGraph (leaEqualityEdges front)).Reachable start finish ∧
      finish ∉ frame.vars := by
  obtain ⟨walk⟩ := reachable
  induction walk with
  | nil => exact ⟨.rfl,outside⟩
  | @cons first next last edge tail ih =>
    have localEdge : (EqualityClosure.edgeGraph (leaEqualityEdges front)).Adj first next := by
      rw [EqualityClosure.edgeGraph_adj_iff] at edge ⊢
      refine ⟨edge.1,?_⟩
      rw [leaEqualityEdges_append] at edge
      rcases edge.2 with forward | backward
      · rcases List.mem_append.mp forward with localEdge | frameEdge
        · exact Or.inl localEdge
        · exact (outside (leaEdge_endpoint_vars frameEdge).1).elim
      · rcases List.mem_append.mp backward with localEdge | frameEdge
        · exact Or.inr localEdge
        · exact (outside (leaEdge_endpoint_vars frameEdge).2).elim
    have nextIn : next ∈ front.vars := by
      rcases (EqualityClosure.edgeGraph_adj_iff.mp localEdge).2 with forward | backward
      · exact (leaEdge_endpoint_vars forward).2
      · exact (leaEdge_endpoint_vars backward).1
    obtain ⟨restReachable,lastOutside⟩ := ih (List.disjoint_left.mp disjoint nextIn)
    exact ⟨localEdge.reachable.trans restReachable,lastOutside⟩

theorem mem_leaEqClass_append_frame_iff
    {front frame : Metta.Bindings} (disjoint : List.Disjoint front.vars frame.vars)
    {start finish : String} (outside : start ∉ frame.vars) :
    finish ∈ Metta.Bindings.eqClass (front ++ frame) start ↔
      finish ∈ Metta.Bindings.eqClass front start := by
  rw [mem_leaEqClass_iff_reachable,mem_leaEqClass_iff_reachable]
  constructor
  · intro reachable
    exact (leaEqualityReachable_append_frame disjoint outside reachable).1
  · intro reachable
    apply reachable.mono
    intro x y edge
    rw [EqualityClosure.edgeGraph_adj_iff] at edge ⊢
    refine ⟨edge.1,?_⟩
    rw [leaEqualityEdges_append]
    rcases edge.2 with forward | backward
    · exact Or.inl (List.mem_append_left _ forward)
    · exact Or.inr (List.mem_append_left _ backward)

private theorem filter_insertLast (predicate : String → Bool) (names : List String) (name : String) :
    (if names.contains name then names else names ++ [name]).filter predicate =
      if predicate name then
        if (names.filter predicate).contains name then names.filter predicate
        else names.filter predicate ++ [name]
      else names.filter predicate := by
  cases selected : predicate name <;>
    by_cases present : name ∈ names <;> simp [selected,present,List.filter_append]

theorem leaEqVarsInOrder_cons_val (front : Metta.Bindings) (name : String) (value : Metta.Atom) :
    Metta.Bindings.eqVarsInOrder (.val name value::front)=Metta.Bindings.eqVarsInOrder front := by
  simp [Metta.Bindings.eqVarsInOrder,List.foldl_append]

theorem leaEqVarsInOrder_cons_eq (front : Metta.Bindings) (left right : String) :
    Metta.Bindings.eqVarsInOrder (.eq left right::front) =
      (let names := Metta.Bindings.eqVarsInOrder front
       let names := if names.contains right then names else names ++ [right]
       if names.contains left then names else names ++ [left]) := by
  simp [Metta.Bindings.eqVarsInOrder,List.foldl_append]

/-- Filtering the representative chronology erases every entirely foreign
frame entry, even though that frame precedes the local edges chronologically. -/
theorem filter_leaEqVarsInOrder_append_frame
    (front frame : Metta.Bindings) (predicate : String → Bool)
    (frameFalse : ∀ name ∈ frame.vars,predicate name=false) :
    (Metta.Bindings.eqVarsInOrder (front++frame)).filter predicate =
      (Metta.Bindings.eqVarsInOrder front).filter predicate := by
  induction front with
  | nil =>
    apply List.filter_eq_nil_iff.mpr
    intro name present
    have endpoint := mem_leaEqVarsInOrder_iff.mp present
    simp only [EqualityClosure.edgeNodes,List.mem_flatMap] at endpoint
    obtain ⟨⟨left,right⟩,edge,inEdge⟩ := endpoint
    have endpoints := leaEdge_endpoint_vars edge
    have named : name=left ∨ name=right := by simpa using inEdge
    rcases named with rfl | rfl
    · exact Bool.eq_false_iff.mp (frameFalse _ endpoints.1)
    · exact Bool.eq_false_iff.mp (frameFalse _ endpoints.2)
  | cons relation rest ih =>
    cases relation with
    | val name value => simpa only [List.cons_append,leaEqVarsInOrder_cons_val] using ih
    | eq left right =>
      simp only [List.cons_append,leaEqVarsInOrder_cons_eq]
      rw [filter_insertLast,filter_insertLast,filter_insertLast,filter_insertLast,ih]

/-- Both equality membership and its stable representative order stay local. -/
theorem leaEqClassOrdered_append_frame
    {front frame : Metta.Bindings} (disjoint : List.Disjoint front.vars frame.vars)
    {key : String} (outside : key ∉ frame.vars) :
    Metta.Bindings.eqClassOrdered (front++frame) key = Metta.Bindings.eqClassOrdered front key := by
  have predicates : (fun name => (Metta.Bindings.eqClass (front++frame) key).contains name) =
      (fun name => (Metta.Bindings.eqClass front key).contains name) := by
    funext name
    apply Bool.eq_iff_iff.mpr
    simp only [List.contains_iff_mem]
    exact mem_leaEqClass_append_frame_iff disjoint outside
  have frameFalse : ∀ name ∈ frame.vars,(Metta.Bindings.eqClass front key).contains name=false := by
    intro name present
    apply Bool.eq_false_iff.mpr
    intro member
    have inLocal : name ∈ Metta.Bindings.eqClass front key := List.contains_iff_mem.mp member
    have inFull := (mem_leaEqClass_append_frame_iff disjoint outside).mpr inLocal
    exact (leaEqualityReachable_append_frame disjoint outside
      (mem_leaEqClass_iff_reachable.mp inFull)).2 present
  unfold Metta.Bindings.eqClassOrdered
  rw [predicates,filter_leaEqVarsInOrder_append_frame front frame _ frameFalse]

/-- The frame supplies no value for a local or otherwise fresh name. -/
theorem leaLookupVal_append_frame (front frame : Metta.Bindings) {key : String}
    (outside : key ∉ frame.vars) :
    Metta.Bindings.lookupVal (front++frame) key = Metta.Bindings.lookupVal front key := by
  have noLookup := lookupVal_none_of_not_mem_keys (fun member => outside (bindingValueKey_mem_vars member))
  rw [lookupVal_append,noLookup]
  cases Metta.Bindings.lookupVal front key <;> rfl

/-- Every selected value of an isolated local class is exactly the original
value, retaining the native class order and first-value policy. -/
theorem leaClassValues_append_frame
    {front frame : Metta.Bindings} (disjoint : List.Disjoint front.vars frame.vars)
    {key : String} (outside : key ∉ frame.vars) :
    Metta.Bindings.classValues (front++frame) key = Metta.Bindings.classValues front key := by
  unfold Metta.Bindings.classValues
  rw [leaEqClassOrdered_append_frame disjoint outside]
  apply List.filterMap_congr
  intro name member
  apply leaLookupVal_append_frame
  have inFull := (mem_leaEqClass_append_frame_iff disjoint outside).mpr
    (mem_leaEqClassOrdered_iff.mp member)
  exact (leaEqualityReachable_append_frame disjoint outside
    (mem_leaEqClass_iff_reachable.mp inFull)).2

theorem leaEqRepresentative_append_frame
    {front frame : Metta.Bindings} (disjoint : List.Disjoint front.vars frame.vars)
    {key : String} (outside : key ∉ frame.vars) :
    Metta.Bindings.eqRepresentative (front ++ frame) key =
      Metta.Bindings.eqRepresentative front key := by
  unfold Metta.Bindings.eqRepresentative
  rw [leaEqClassOrdered_append_frame disjoint outside]

private theorem leaEqualityGraph_append_comm (front frame : Metta.Bindings) :
    EqualityClosure.edgeGraph (leaEqualityEdges (front ++ frame)) =
      EqualityClosure.edgeGraph (leaEqualityEdges (frame ++ front)) := by
  ext x y
  simp only [EqualityClosure.edgeGraph_adj_iff,leaEqualityEdges_append,List.mem_append]
  tauto

theorem leaEqualityReachable_append_left_frame
    {front frame : Metta.Bindings} (disjoint : List.Disjoint front.vars frame.vars)
    {start finish : String} (outside : start ∉ front.vars)
    (reachable : (EqualityClosure.edgeGraph (leaEqualityEdges (front ++ frame))).Reachable start finish) :
    (EqualityClosure.edgeGraph (leaEqualityEdges frame)).Reachable start finish ∧
      finish ∉ front.vars := by
  rw [leaEqualityGraph_append_comm] at reachable
  exact leaEqualityReachable_append_frame disjoint.symm outside reachable

theorem mem_leaEqClass_append_left_frame_iff
    {front frame : Metta.Bindings} (disjoint : List.Disjoint front.vars frame.vars)
    {start finish : String} (outside : start ∉ front.vars) :
    finish ∈ Metta.Bindings.eqClass (front ++ frame) start ↔
      finish ∈ Metta.Bindings.eqClass frame start := by
  rw [mem_leaEqClass_iff_reachable,leaEqualityGraph_append_comm,
    ← mem_leaEqClass_iff_reachable]
  exact mem_leaEqClass_append_frame_iff disjoint.symm outside

/-- Foreign prefix entries disappear from representative chronology when its
predicate selects only the other binding component. -/
theorem filter_leaEqVarsInOrder_append_left_frame
    (front frame : Metta.Bindings) (predicate : String → Bool)
    (frontFalse : ∀ name ∈ front.vars,predicate name=false) :
    (Metta.Bindings.eqVarsInOrder (front++frame)).filter predicate =
      (Metta.Bindings.eqVarsInOrder frame).filter predicate := by
  induction front with
  | nil => rfl
  | cons relation rest ih =>
    have restFalse : ∀ name ∈ Metta.Bindings.vars rest,predicate name=false := by
      intro name present
      apply frontFalse name
      simp only [Metta.Bindings.vars,List.flatMap_cons,List.mem_eraseDups,List.mem_append] at present ⊢
      exact Or.inr present
    cases relation with
    | val name value =>
      simpa only [List.cons_append,leaEqVarsInOrder_cons_val] using ih restFalse
    | eq left right =>
      have leftFalse := frontFalse left (by simp [Metta.Bindings.vars])
      have rightFalse := frontFalse right (by simp [Metta.Bindings.vars])
      simp only [List.cons_append,leaEqVarsInOrder_cons_eq]
      rw [filter_insertLast,leftFalse]
      simp only [Bool.false_eq_true,↓reduceIte]
      rw [filter_insertLast,rightFalse]
      simp only [Bool.false_eq_true,↓reduceIte]
      exact ih restFalse

theorem leaEqClassOrdered_append_left_frame
    {front frame : Metta.Bindings} (disjoint : List.Disjoint front.vars frame.vars)
    {key : String} (outside : key ∉ front.vars) :
    Metta.Bindings.eqClassOrdered (front++frame) key = Metta.Bindings.eqClassOrdered frame key := by
  have predicates : (fun name => (Metta.Bindings.eqClass (front++frame) key).contains name) =
      (fun name => (Metta.Bindings.eqClass frame key).contains name) := by
    funext name
    apply Bool.eq_iff_iff.mpr
    simp only [List.contains_iff_mem]
    exact mem_leaEqClass_append_left_frame_iff disjoint outside
  have frontFalse : ∀ name ∈ front.vars,(Metta.Bindings.eqClass frame key).contains name=false := by
    intro name present
    apply Bool.eq_false_iff.mpr
    intro member
    have inLocal : name ∈ Metta.Bindings.eqClass frame key := List.contains_iff_mem.mp member
    have inFull := (mem_leaEqClass_append_left_frame_iff disjoint outside).mpr inLocal
    exact (leaEqualityReachable_append_left_frame disjoint outside
      (mem_leaEqClass_iff_reachable.mp inFull)).2 present
  unfold Metta.Bindings.eqClassOrdered
  rw [predicates,filter_leaEqVarsInOrder_append_left_frame front frame _ frontFalse]

theorem leaLookupVal_append_left_frame (front frame : Metta.Bindings) {key : String}
    (outside : key ∉ front.vars) :
    Metta.Bindings.lookupVal (front++frame) key = Metta.Bindings.lookupVal frame key := by
  have noLookup := lookupVal_none_of_not_mem_keys (fun member => outside (bindingValueKey_mem_vars member))
  rw [lookupVal_append,noLookup]
  rfl

theorem leaClassValues_append_left_frame
    {front frame : Metta.Bindings} (disjoint : List.Disjoint front.vars frame.vars)
    {key : String} (outside : key ∉ front.vars) :
    Metta.Bindings.classValues (front++frame) key = Metta.Bindings.classValues frame key := by
  unfold Metta.Bindings.classValues
  rw [leaEqClassOrdered_append_left_frame disjoint outside]
  apply List.filterMap_congr
  intro name member
  apply leaLookupVal_append_left_frame
  have inFull := (mem_leaEqClass_append_left_frame_iff disjoint outside).mpr
    (mem_leaEqClassOrdered_iff.mp member)
  exact (leaEqualityReachable_append_left_frame disjoint outside
    (mem_leaEqClass_iff_reachable.mp inFull)).2

/-- Recursive resolution only inspects the selected ordered classes and values
reachable from its query. Agreement on a closed variable region therefore
preserves successes, visited-set cycle refusals, and explicit cutoffs. -/
theorem leaResolveAtomAux_congr_on_region
    (left right : Metta.Bindings) (region : String → Prop)
    (classesAgree : ∀ key,region key →
      Metta.Bindings.eqClassOrdered left key=Metta.Bindings.eqClassOrdered right key)
    (valuesAgree : ∀ key,region key →
      Metta.Bindings.classValues left key=Metta.Bindings.classValues right key)
    (valueClosed : ∀ key,region key → ∀ value ∈ Metta.Bindings.classValues right key,
      ∀ name ∈ value.vars,region name)
    (fuel : Nat) (visited : List String) (atom : Metta.Atom)
    (inside : ∀ key ∈ atom.vars,region key) :
    Metta.Bindings.resolveAtomAux left fuel visited atom =
      Metta.Bindings.resolveAtomAux right fuel visited atom := by
  induction fuel generalizing visited atom with
  | zero => rfl
  | succ fuel ih =>
    cases atom with
    | sym symbol | gnd ground => rfl
    | var key =>
      have keyInside := inside key (by simp [Metta.Atom.vars])
      have representatives : Metta.Bindings.eqRepresentative left key =
          Metta.Bindings.eqRepresentative right key := by
        unfold Metta.Bindings.eqRepresentative
        rw [classesAgree key keyInside]
      simp only [Metta.Bindings.resolveAtomAux,classesAgree key keyInside,
        valuesAgree key keyInside,representatives]
      split
      · rfl
      · cases values : Metta.Bindings.classValues right key with
        | nil => rfl
        | cons value rest =>
          have valueInside := valueClosed key keyInside value
            (show value ∈ Metta.Bindings.classValues right key by rw [values]; simp)
          cases value with
          | var other =>
            simp only
            split
            · rfl
            · exact ih _ _ valueInside
          | sym symbol | gnd ground | expr children => exact ih _ _ valueInside
    | expr children =>
      have equalMap : children.mapM (Metta.Bindings.resolveAtomAux left fuel visited) =
          children.mapM (Metta.Bindings.resolveAtomAux right fuel visited) := by
        induction children with
        | nil => rfl
        | cons child rest restIH =>
          simp only [List.mapM_cons]
          rw [ih _ child (fun key present => inside key (by
            simp only [Metta.Atom.vars,List.map_cons,List.flatten_cons,List.mem_append]
            exact Or.inl present))]
          rw [restIH (fun key present => inside key (by
            simp only [Metta.Atom.vars,List.map_cons,List.flatten_cons,List.mem_append] at present ⊢
            exact Or.inr present))]
      simp only [Metta.Bindings.resolveAtomAux,equalMap]

/-- Appending a separate binding component cannot change local resolution,
including its cycle refusals and explicit fuel cutoff. -/
theorem leaResolveAtomAux_append_frame
    {front frame : Metta.Bindings} (disjoint : List.Disjoint front.vars frame.vars)
    (fuel : Nat) (visited : List String) (atom : Metta.Atom)
    (outside : ∀ key ∈ atom.vars, key ∉ frame.vars) :
    Metta.Bindings.resolveAtomAux (front ++ frame) fuel visited atom =
      Metta.Bindings.resolveAtomAux front fuel visited atom := by
  apply leaResolveAtomAux_congr_on_region (front++frame) front (fun key => key ∉ frame.vars)
    (fun _ => leaEqClassOrdered_append_frame disjoint)
    (fun _ => leaClassValues_append_frame disjoint)
    ?_ fuel visited atom outside
  intro key _ value member name mentioned inFrame
  exact List.disjoint_left.mp disjoint (leaClassValue_vars_subset member mentioned) inFrame

/-- An isolated prefix cannot change resolution inside the suffix. -/
theorem leaResolveAtomAux_append_left_frame
    {front frame : Metta.Bindings} (disjoint : List.Disjoint front.vars frame.vars)
    (fuel : Nat) (visited : List String) (atom : Metta.Atom)
    (outside : ∀ key ∈ atom.vars,key ∉ front.vars) :
    Metta.Bindings.resolveAtomAux (front++frame) fuel visited atom =
      Metta.Bindings.resolveAtomAux frame fuel visited atom := by
  apply leaResolveAtomAux_congr_on_region (front++frame) frame (fun key => key ∉ front.vars)
    (fun _ => leaEqClassOrdered_append_left_frame disjoint)
    (fun _ => leaClassValues_append_left_frame disjoint)
    ?_ fuel visited atom outside
  intro key _ value member name mentioned inFront
  exact List.disjoint_left.mp disjoint inFront (leaClassValue_vars_subset member mentioned)

/-- Two fresh non-variable values followed by a separate valueless equality
are inserted without reconciling or normalizing the unrelated caller. The
native caller-cycle refusal remains a separate boundary. -/
theorem merge_fresh_two_values_one_equality
    (caller : Metta.Bindings) (templateKey payloadKey patternKey binder : String)
    (template payload : Metta.Atom)
    (disjoint : List.Disjoint
      (Metta.Bindings.vars [.val templateKey template, .val payloadKey payload, .eq patternKey binder])
      caller.vars)
    (templateNonvar : ∀ key, template ≠ .var key)
    (payloadNonvar : ∀ key, payload ≠ .var key)
    (keys : payloadKey ≠ templateKey)
    (patternBinder : patternKey ≠ binder)
    (patternPayload : patternKey ≠ payloadKey)
    (patternTemplate : patternKey ≠ templateKey)
    (binderPayload : binder ≠ payloadKey)
    (binderTemplate : binder ≠ templateKey) :
    Metta.Bindings.merge caller
        [.val templateKey template, .val payloadKey payload, .eq patternKey binder] =
      [[.eq patternKey binder, .val payloadKey payload, .val templateKey template] ++ caller] := by
  let matched : Metta.Bindings :=
    [.val templateKey template, .val payloadKey payload, .eq patternKey binder]
  have pieceSeparated (piece : Metta.Bindings) (included : piece ⊆ matched) :
      List.Disjoint piece.vars caller.vars := by
    apply List.disjoint_left.mpr
    intro name present
    apply List.disjoint_left.mp disjoint
    simp only [Metta.Bindings.vars, List.mem_eraseDups, List.mem_flatMap] at present ⊢
    obtain ⟨relation, inPiece, mentioned⟩ := present
    exact ⟨relation,included inPiece,mentioned⟩
  have templateFresh : templateKey ∉ caller.vars :=
    List.disjoint_left.mp disjoint
      (bindingRelation_vars_subset (by simp [matched] : .val templateKey template ∈ matched)
        (by simp [Metta.Bindings.vars]))
  have payloadFresh : payloadKey ∉ caller.vars :=
    List.disjoint_left.mp disjoint
      (bindingRelation_vars_subset (by simp [matched] : .val payloadKey payload ∈ matched)
        (by simp [Metta.Bindings.vars]))
  have patternFresh : patternKey ∉ caller.vars :=
    List.disjoint_left.mp disjoint
      (bindingRelation_vars_subset (by simp [matched] : .eq patternKey binder ∈ matched)
        (by simp [Metta.Bindings.vars]))
  have templateStep : Metta.Bindings.merge caller [.val templateKey template] =
      [[.val templateKey template] ++ caller] :=
    merge_singleton_val_eq_of_fresh_class (Bindings.outside_class templateFresh).2
      templateNonvar (fun member => templateFresh (bindingValueKey_mem_vars member))
  have payloadClass : Metta.Bindings.classValues (.val templateKey template :: caller) payloadKey = [] := by
    change Metta.Bindings.classValues ([.val templateKey template] ++ caller) payloadKey = []
    rw [leaClassValues_append_frame (pieceSeparated _ (by simp [matched])) payloadFresh]
    exact (ValueBindings.classValues_lookupVal (.val .nil) payloadKey).1
      (by simp [Metta.Bindings.lookupVal,keys])
  have payloadStep : Metta.Bindings.merge (.val templateKey template :: caller)
      [.val payloadKey payload] = [[.val payloadKey payload, .val templateKey template] ++ caller] := by
    apply merge_singleton_val_eq_of_fresh_class payloadClass payloadNonvar
    simp only [bindingValueKeys, List.mem_cons, not_or]
    exact ⟨keys, fun member => payloadFresh (bindingValueKey_mem_vars member)⟩
  have equalityClass : Metta.Bindings.classValues
      (.eq patternKey binder :: .val payloadKey payload :: .val templateKey template :: caller)
      patternKey = [] := by
    change Metta.Bindings.classValues
      ([.eq patternKey binder, .val payloadKey payload, .val templateKey template] ++ caller)
      patternKey = []
    rw [leaClassValues_append_frame (pieceSeparated _ (by
      intro relation present
      simpa [matched,or_comm,or_left_comm,or_assoc] using present)) patternFresh]
    exact Bindings.classValues_one_eq_two_vals_left_eq_nil
      patternKey binder payloadKey templateKey payload template patternBinder
      patternPayload patternTemplate binderPayload binderTemplate
  have equalityStep : Metta.Bindings.merge
      (.val payloadKey payload :: .val templateKey template :: caller)
      [.eq patternKey binder] =
      [[.eq patternKey binder, .val payloadKey payload, .val templateKey template] ++ caller] :=
    merge_singleton_eq_eq_of_valueless_class patternBinder equalityClass (by
      intro present
      rcases List.mem_cons.mp present with impossible | present
      · cases impossible
      rcases List.mem_cons.mp present with impossible | present
      · cases impossible
      exact patternFresh (bindingRelation_vars_subset present (by
        simp [Metta.Bindings.vars])))
  change Metta.Bindings.mergeOne
    (Metta.Bindings.mergeOne
      (Metta.Bindings.mergeOne [caller] (.val templateKey template)) (.val payloadKey payload))
    (.eq patternKey binder) = _
  change Metta.Bindings.mergeOne [caller] (.val templateKey template) = _ at templateStep
  rw [templateStep]
  simp only [List.singleton_append]
  change Metta.Bindings.mergeOne [(.val templateKey template :: caller)] (.val payloadKey payload) = _ at payloadStep
  rw [payloadStep]
  exact equalityStep

/-! ## Variable support of recursive resolution -/

theorem eqRepresentative_ne_of_outside
    {bindings : Metta.Bindings} {fresh key : String}
    (outside : fresh ∉ bindings.vars) (different : key ≠ fresh) :
    Metta.Bindings.eqRepresentative bindings key ≠ fresh := by
  have classAvoids : ∀ name ∈ Metta.Bindings.eqClassOrdered bindings key, name ≠ fresh := by
    intro name present equal
    subst name
    have symmetric := (mem_leaEqClass_iff_reachable.mp
      (mem_leaEqClassOrdered_iff.mp present)).symm
    have back : key ∈ Metta.Bindings.eqClassOrdered bindings fresh :=
      mem_leaEqClassOrdered_iff.mpr (mem_leaEqClass_iff_reachable.mpr symmetric)
    rw [(Bindings.outside_class outside).1] at back
    exact different (List.mem_singleton.mp back)
  unfold Metta.Bindings.eqRepresentative
  cases ordered : Metta.Bindings.eqClassOrdered bindings key with
  | nil => exact different
  | cons first rest =>
      exact classAvoids first (by rw [ordered]; simp)

theorem classValue_preserves_outside
    {bindings : Metta.Bindings} {fresh key : String} {value : Metta.Atom}
    (outside : fresh ∉ bindings.vars)
    (member : value ∈ Metta.Bindings.classValues bindings key) :
    fresh ∉ value.vars := by
  intro mentioned
  exact outside (leaClassValue_vars_subset member mentioned)

theorem resolveAtomAux_preserves_outside
    {bindings : Metta.Bindings} {fresh : String}
    (outside : fresh ∉ bindings.vars) (fuel : Nat)
    (visited : List String) (atom result : Metta.Atom)
    (atomAvoids : fresh ∉ atom.vars)
    (resolved : Metta.Bindings.resolveAtomAux bindings fuel visited atom = some result) :
    fresh ∉ result.vars := by
  induction fuel generalizing visited atom result with
  | zero => simp [Metta.Bindings.resolveAtomAux] at resolved
  | succ fuel ih =>
    cases atom with
    | sym symbol | gnd ground =>
        simp only [Metta.Bindings.resolveAtomAux, Option.some.injEq] at resolved
        subst result
        exact atomAvoids
    | var key =>
        have different : key ≠ fresh := by simpa [Metta.Atom.vars, eq_comm] using atomAvoids
        have representativeAvoids : fresh ∉ (Metta.Atom.var
            (Metta.Bindings.eqRepresentative bindings key)).vars := by
          simpa [Metta.Atom.vars, eq_comm] using eqRepresentative_ne_of_outside outside different
        cases checked : (Metta.Bindings.eqClassOrdered bindings key).any visited.contains with
        | true => simp [Metta.Bindings.resolveAtomAux, checked] at resolved
        | false =>
          cases values : Metta.Bindings.classValues bindings key with
          | nil =>
              simp only [Metta.Bindings.resolveAtomAux, checked, Bool.false_eq_true,
                ↓reduceIte, values, Option.some.injEq] at resolved
              subst result
              exact representativeAvoids
          | cons value rest =>
              have valueAvoids := classValue_preserves_outside outside
                (by rw [values]; exact List.mem_cons_self)
              cases value with
              | sym symbol | gnd ground | expr children =>
                  apply ih _ _ _ valueAvoids
                  simpa only [Metta.Bindings.resolveAtomAux, checked,
                    Bool.false_eq_true, ↓reduceIte, values] using resolved
              | var other =>
                  by_cases internal : (Metta.Bindings.eqClassOrdered bindings key).contains other = true
                  · by_cases singleton : (Metta.Bindings.eqClassOrdered bindings key).length == 1
                    · simp only [Metta.Bindings.resolveAtomAux, checked, Bool.false_eq_true,
                        ↓reduceIte, values, internal, singleton] at resolved
                      cases resolved
                    · simp only [Metta.Bindings.resolveAtomAux, checked, Bool.false_eq_true,
                        ↓reduceIte, values, internal, singleton, Option.some.injEq] at resolved
                      subst result
                      exact representativeAvoids
                  · apply ih _ _ _ valueAvoids
                    simpa only [Metta.Bindings.resolveAtomAux, checked,
                      Bool.false_eq_true, ↓reduceIte, values, internal] using resolved
    | expr children =>
        have listAvoids : ∀ (source target : List Metta.Atom),
            (∀ child ∈ source, fresh ∉ child.vars) →
            source.mapM (Metta.Bindings.resolveAtomAux bindings fuel visited) = some target →
            ∀ child ∈ target, fresh ∉ child.vars := by
          intro source
          induction source with
          | nil =>
              intro target _ mapped
              simp at mapped
              subst target
              simp
          | cons head tail tailIH =>
              intro target avoids mapped
              cases headResult : Metta.Bindings.resolveAtomAux bindings fuel visited head with
              | none => simp [List.mapM_cons, headResult] at mapped
              | some headValue =>
                cases tailResult : tail.mapM (Metta.Bindings.resolveAtomAux bindings fuel visited) with
                | none => simp [List.mapM_cons, headResult, tailResult] at mapped
                | some tailValues =>
                    simp [List.mapM_cons, headResult, tailResult] at mapped
                    subst target
                    intro child present
                    rcases List.mem_cons.mp present with equal | later
                    · rw [equal]
                      exact ih visited head headValue (avoids head (by simp)) headResult
                    · exact tailIH tailValues (fun item present => avoids item (by simp [present]))
                        tailResult child later
        cases mapped : children.mapM (Metta.Bindings.resolveAtomAux bindings fuel visited) with
        | none => simp [Metta.Bindings.resolveAtomAux, mapped] at resolved
        | some outputs =>
          simp only [Metta.Bindings.resolveAtomAux, mapped, Option.some.injEq] at resolved
          subst result
          intro member
          simp only [Metta.Atom.vars, List.mem_flatten, List.mem_map] at member
          obtain ⟨_, ⟨child, present, rfl⟩, mentioned⟩ := member
          exact listAvoids children outputs (by
            intro item present mentioned
            exact atomAvoids (by
              simp only [Metta.Atom.vars, List.mem_flatten, List.mem_map]
              exact ⟨item.vars, ⟨item, present, rfl⟩, mentioned⟩)) mapped child present mentioned


theorem resolve_preserves_outside
    {bindings : Metta.Bindings} {fresh key : String} {result : Metta.Atom}
    (outside : fresh ∉ bindings.vars) (different : key ≠ fresh)
    (resolved : Metta.Bindings.resolve bindings key = some result) :
    fresh ∉ result.vars := by
  unfold Metta.Bindings.resolve at resolved
  dsimp only at resolved
  split at resolved
  · cases resolved
  · exact resolveAtomAux_preserves_outside outside _ [] (.var key) result
      (by simpa [Metta.Atom.vars, eq_comm] using different) resolved

/-- Resolution through arbitrary stored aliases and open values introduces no
name absent from both the input atom and the complete binding record. -/
theorem instantiate_preserves_outside
    {bindings : Metta.Bindings} {fresh : String}
    (outside : fresh ∉ bindings.vars) (atom : Metta.Atom)
    (atomAvoids : fresh ∉ atom.vars) :
    fresh ∉ (Metta.instantiate bindings atom).vars := by
  induction atom with
  | sym symbol | gnd ground =>
      simp [Metta.instantiate, Metta.Bindings.resolveAtom, Metta.Atom.vars]
  | var key =>
      cases resolved : Metta.Bindings.resolve bindings key with
      | none => simpa only [Metta.instantiate, Metta.Bindings.resolveAtom, resolved,
          Option.getD_none] using atomAvoids
      | some result =>
          simpa only [Metta.instantiate, Metta.Bindings.resolveAtom, resolved,
            Option.getD_some] using resolve_preserves_outside outside
              (by simpa [Metta.Atom.vars, eq_comm] using atomAvoids) resolved
  | expr children ih =>
      intro mentioned
      simp only [Metta.instantiate, Metta.Bindings.resolveAtom, Metta.Atom.vars,
        List.mem_flatten, List.mem_map] at mentioned
      obtain ⟨_, ⟨child, ⟨original, present, rfl⟩, rfl⟩, member⟩ := mentioned
      exact ih original present (by
        intro originalMember
        apply atomAvoids
        simp only [Metta.Atom.vars, List.mem_flatten, List.mem_map]
        exact ⟨original.vars, ⟨original, present, rfl⟩, originalMember⟩) member


/-- Connected class queries carry the same values, without fixing list order. -/
theorem leaClassValue_mem_of_class
    {bindings : Metta.Bindings} {key other : String} {value : Metta.Atom}
    (hclass : other ∈ Metta.Bindings.eqClass bindings key)
    (hvalue : value ∈ Metta.Bindings.classValues bindings other) :
    value ∈ Metta.Bindings.classValues bindings key := by
  obtain ⟨member, hmember, hlookup⟩ := leaClassValue_mem_iff.mp hvalue
  apply leaClassValue_mem_iff.mpr
  refine ⟨member, ?_, hlookup⟩
  rw [mem_leaEqClass_iff_reachable] at hclass hmember ⊢
  exact hclass.trans hmember

/-- A new value relation does not alter equality connectivity. -/
theorem leaClass_cons_val_iff (bindings : Metta.Bindings)
    (key : String) (value : Metta.Atom) (start finish : String) :
    finish ∈ Metta.Bindings.eqClass (.val key value :: bindings) start ↔
      finish ∈ Metta.Bindings.eqClass bindings start := by
  rw [mem_leaEqClass_iff_reachable, mem_leaEqClass_iff_reachable]
  rfl

/-- At a free class, adding a direct value preserves every old class-value
occurrence and adds exactly the new value to that class. -/
theorem leaClassValue_cons_fresh_iff
    {bindings : Metta.Bindings} {key : String} {value : Metta.Atom}
    (hfree : Metta.Bindings.classValues bindings key = [])
    (start : String) (stored : Metta.Atom) :
    stored ∈ Metta.Bindings.classValues (.val key value :: bindings) start ↔
      stored ∈ Metta.Bindings.classValues bindings start ∨
        (stored = value ∧ key ∈ Metta.Bindings.eqClass bindings start) := by
  rw [leaClassValue_mem_iff]
  constructor
  · rintro ⟨member, hclass, hlookup⟩
    have holdClass := (leaClass_cons_val_iff bindings key value start member).mp hclass
    by_cases hkey : member = key
    · subst member
      simp only [Metta.Bindings.lookupVal, beq_self_eq_true, if_true,
        Option.some.injEq] at hlookup
      exact Or.inr ⟨hlookup.symm, holdClass⟩
    · left
      apply leaClassValue_mem_iff.mpr
      exact ⟨member, holdClass, by simpa [Metta.Bindings.lookupVal, hkey] using hlookup⟩
  · rintro (hold | ⟨rfl, hclass⟩)
    · obtain ⟨member, hmember, hlookup⟩ := leaClassValue_mem_iff.mp hold
      have hne : member ≠ key := by
        intro heq
        subst member
        rw [leaLookupVal_eq_none_of_classValues_eq_nil hfree] at hlookup
        cases hlookup
      exact ⟨member, (leaClass_cons_val_iff bindings key value start member).mpr hmember,
        by simpa [Metta.Bindings.lookupVal, hne] using hlookup⟩
    · exact ⟨key, (leaClass_cons_val_iff bindings key stored start key).mpr hclass,
        by simp [Metta.Bindings.lookupVal]⟩

/-- Fresh value insertion preserves the complete chosen-equation basis even
when the inserted value later creates a cycle. Final admission checks cycles. -/
theorem leaClassChoiceBasis_cons_fresh
    {bindings : Metta.Bindings} {key : String} {value : Metta.Atom}
    (hbasis : LeaClassChoiceBasis bindings)
    (hfree : Metta.Bindings.classValues bindings key = []) :
    LeaClassChoiceBasis (.val key value :: bindings) := by
  intro valuation hselected
  have hold : LeaClassChoiceSatisfied valuation bindings := by
    constructor
    · intro start finish hclass
      exact hselected.1 start finish
        ((leaClass_cons_val_iff bindings key value start finish).mpr hclass)
    · intro start hnonempty
      have hnewNonempty : Metta.Bindings.classValues (.val key value :: bindings) start ≠ [] := by
        intro hempty
        obtain ⟨stored, hstored⟩ := List.exists_mem_of_ne_nil _ hnonempty
        have hnew := (leaClassValue_cons_fresh_iff (value := value) hfree start stored).mpr (Or.inl hstored)
        simp [hempty] at hnew
      obtain ⟨stored, hstored, hequation⟩ := hselected.2 start hnewNonempty
      rcases (leaClassValue_cons_fresh_iff (value := value) hfree start stored).mp hstored with hold | ⟨rfl, hclass⟩
      · exact ⟨stored, hold, hequation⟩
      · exfalso
        apply hnonempty
        apply leaClassValues_nil_of_mem_class (key := key) ?_ hfree
        rw [mem_leaEqClass_iff_reachable] at hclass ⊢
        exact hclass.symm
  have hfull := hbasis valuation hold
  have hnewValue : valuation key = applyClassSolution valuation value := by
    have hnewNonempty : Metta.Bindings.classValues (.val key value :: bindings) key ≠ [] := by
      intro hempty
      have hnew := (leaClassValue_cons_fresh_iff hfree key value).mpr
        (Or.inr ⟨rfl, by rw [mem_leaEqClass_iff_reachable]⟩)
      simp [hempty] at hnew
    obtain ⟨stored, hstored, hequation⟩ := hselected.2 key hnewNonempty
    rcases (leaClassValue_cons_fresh_iff hfree key stored).mp hstored with hold | ⟨rfl, _⟩
    · simp [hfree] at hold
    · exact hequation
  constructor
  · intro name stored hmem
    simp only [List.mem_cons, Metta.BindingRel.val.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | hmem
    · exact hnewValue
    · exact hfull.1 name stored hmem
  · intro left right hmem
    exact hfull.2 left right (by simpa using hmem)

@[simp] theorem leaLookupVal_addEqRaw (bindings : Metta.Bindings)
    (left right key : String) :
    Metta.Bindings.lookupVal (Metta.Bindings.addEqRaw bindings left right) key =
      Metta.Bindings.lookupVal bindings key := by
  exact Metta.Bindings.lookupVal_addEqRaw bindings left right key

theorem leaClass_addEqRaw_mono {bindings : Metta.Bindings} (left right : String)
    {start finish : String} (hclass : finish ∈ Metta.Bindings.eqClass bindings start) :
    finish ∈ Metta.Bindings.eqClass (Metta.Bindings.addEqRaw bindings left right) start := by
  apply leaEqClass_mono_of_edge_subset (hclass := hclass)
  intro edge hedge
  exact leaEqualityEdges_addEqRaw_old bindings left right hedge

theorem leaClassValue_addEqRaw_mono {bindings : Metta.Bindings} (left right : String)
    {key : String} {value : Metta.Atom}
    (hvalue : value ∈ Metta.Bindings.classValues bindings key) :
    value ∈ Metta.Bindings.classValues (Metta.Bindings.addEqRaw bindings left right) key := by
  obtain ⟨member, hclass, hlookup⟩ := leaClassValue_mem_iff.mp hvalue
  exact leaClassValue_mem_iff.mpr ⟨member, leaClass_addEqRaw_mono left right hclass,
    by simpa using hlookup⟩

/-- A new connection either existed before insertion or enters the newly
joined component. -/
theorem leaClass_addEqRaw_old_or_joined
    {bindings : Metta.Bindings} {left right start finish : String}
    (hclass : finish ∈ Metta.Bindings.eqClass (Metta.Bindings.addEqRaw bindings left right) start) :
    finish ∈ Metta.Bindings.eqClass bindings start ∨
      left ∈ Metta.Bindings.eqClass (Metta.Bindings.addEqRaw bindings left right) start := by
  by_cases heq : left = right
  · exact Or.inl (by simpa [Metta.Bindings.addEqRaw, heq] using hclass)
  rw [mem_leaEqClass_iff_reachable] at hclass ⊢
  rw [mem_leaEqClass_iff_reachable]
  obtain ⟨walk⟩ := hclass
  induction walk with
  | nil => exact Or.inl .rfl
  | @cons a b c edge path ih =>
      have hnewReach := edge.reachable
      rw [EqualityClosure.edgeGraph_adj_iff] at edge
      have hedge : (a, b) ∈ leaEqualityEdges bindings ∨ (b, a) ∈ leaEqualityEdges bindings ∨
          (a = left ∧ b = right) ∨ (a = right ∧ b = left) := by
        rcases edge.2 with forward | reverse
        · rcases (mem_leaEqualityEdges_addEqRaw_iff bindings heq).mp forward with
            added | hold
          · exact Or.inr (Or.inr (Or.inl added))
          · exact Or.inl hold
        · rcases (mem_leaEqualityEdges_addEqRaw_iff bindings heq).mp reverse with
            added | hold
          · exact Or.inr (Or.inr (Or.inr ⟨added.2, added.1⟩))
          · exact Or.inr (Or.inl hold)
      rcases hedge with hold | hold | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases ih with holdPath | hjoined
        · exact Or.inl ((SimpleGraph.Adj.reachable
            ((EqualityClosure.edgeGraph_adj_iff).mpr ⟨edge.1, Or.inl hold⟩)).trans holdPath)
        · exact Or.inr (hnewReach.trans hjoined)
      · rcases ih with holdPath | hjoined
        · exact Or.inl ((SimpleGraph.Adj.reachable
            ((EqualityClosure.edgeGraph_adj_iff).mpr ⟨edge.1, Or.inr hold⟩)).trans holdPath)
        · exact Or.inr (hnewReach.trans hjoined)
      · exact Or.inr .rfl
      · exact Or.inr hnewReach

/-- A class reconciled without emitting constraints already has equal images
under every valuation. -/
theorem unifyValues_empty_images_equal
    {values : List Metta.Atom}
    (hnoFloat : ∀ value ∈ values, MettaAtomNoFloat value)
    (hrun : Metta.Bindings.unifyValues values = some [])
    (valuation : String → Metta.Atom)
    {left right : Metta.Atom} (hleft : left ∈ values) (hright : right ∈ values) :
    applyClassSolution valuation left = applyClassSolution valuation right := by
  have htheory := (unifyValues_solution_iff valuation hnoFloat hrun).mp
    (by simp [MettaConstraintsSatisfied])
  cases values with
  | nil => simp at hleft
  | cons first rest =>
      have hfirst : ∀ value ∈ first :: rest,
          applyClassSolution valuation first = applyClassSolution valuation value := by
        intro value hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · rfl
        · exact htheory (first, value) (by simp [mettaClassValueEquations, hmem])
      exact (hfirst left hleft).symm.trans (hfirst right hright)

/-- Inserting an alias without a nontrivial reconciliation preserves the
chosen-equation basis; all values in the joined class have already agreed. -/
theorem leaClassChoiceBasis_addEqRaw_of_trivial
    {bindings : Metta.Bindings} {left right : String}
    (hbasis : LeaClassChoiceBasis bindings)
    (hnoFloat : LeaBindingsNoFloat bindings)
    (hrun : Metta.Bindings.unifyValues
      (Metta.Bindings.classValues (Metta.Bindings.addEqRaw bindings left right) left) = some []) :
    LeaClassChoiceBasis (Metta.Bindings.addEqRaw bindings left right) := by
  let candidate := Metta.Bindings.addEqRaw bindings left right
  have hcandNoFloat : LeaBindingsNoFloat candidate := leaBindingsNoFloat_addEqRaw hnoFloat
  intro valuation hselected
  have hold : LeaClassChoiceSatisfied valuation bindings := by
    constructor
    · intro start finish hclass
      exact hselected.1 start finish (leaClass_addEqRaw_mono left right hclass)
    · intro key hnonempty
      obtain ⟨oldValue, holdValue⟩ := List.exists_mem_of_ne_nil _ hnonempty
      have hnewValue := leaClassValue_addEqRaw_mono left right holdValue
      have hnewNonempty : Metta.Bindings.classValues candidate key ≠ [] := by
        intro hempty
        simp only [candidate] at hempty
        rw [hempty] at hnewValue
        exact List.not_mem_nil hnewValue
      obtain ⟨newValue, hchosen, hequation⟩ := hselected.2 key hnewNonempty
      obtain ⟨member, hmember, hlookup⟩ := leaClassValue_mem_iff.mp hchosen
      rcases leaClass_addEqRaw_old_or_joined hmember with holdClass | hjoined
      · exact ⟨newValue, leaClassValue_mem_iff.mpr
          ⟨member, holdClass, by simpa [candidate] using hlookup⟩, hequation⟩
      · have hreverse : key ∈ Metta.Bindings.eqClass candidate left := by
          rw [mem_leaEqClass_iff_reachable] at hjoined ⊢
          exact hjoined.symm
        have hchosenJoined := leaClassValue_mem_of_class hreverse hchosen
        have holdJoined := leaClassValue_mem_of_class hreverse hnewValue
        have hsame := unifyValues_empty_images_equal
          (fun value hvalue => leaClassValue_noFloat hcandNoFloat hvalue)
          hrun valuation hchosenJoined holdJoined
        exact ⟨oldValue, holdValue, hequation.trans hsame⟩
  apply (leaBindingSatisfied_addEqRaw_iff valuation bindings left right).mpr
  refine ⟨hbasis valuation hold, hselected.1 left right ?_⟩
  by_cases heq : left = right
  · subst right
    rw [mem_leaEqClass_iff_reachable]
  · rw [mem_leaEqClass_iff_reachable]
    apply SimpleGraph.Adj.reachable
    rw [EqualityClosure.edgeGraph_adj_iff]
    exact ⟨heq, Or.inl (leaEqualityEdges_addEqRaw_new bindings heq)⟩

/-- Every successful native alias insertion preserves a complete chosen-equation
basis. Its nontrivial branch uses the actual whole-system reconciliation. -/
theorem leaAddVarEquality_result_classChoiceBasis
    {bindings out : Metta.Bindings} {left right : String}
    (hbasis : LeaClassChoiceBasis bindings)
    (hnoFloat : LeaBindingsNoFloat bindings)
    (hout : out ∈ Metta.Bindings.addVarEquality bindings left right) :
    LeaClassChoiceBasis out := by
  cases hunify : Metta.Bindings.unifyValues
      (Metta.Bindings.classValues (Metta.Bindings.addEqRaw bindings left right) left) with
  | none => simp [Metta.Bindings.addVarEquality, hunify] at hout
  | some subst =>
      cases subst with
      | nil =>
          simp [Metta.Bindings.addVarEquality, hunify] at hout
          subst out
          exact leaClassChoiceBasis_addEqRaw_of_trivial hbasis hnoFloat hunify
      | cons head rest =>
          cases hrun : wholeBindingReconciliation bindings [(.var left, .var right)] with
          | none => simp [Metta.Bindings.addVarEquality, hunify, hrun] at hout
          | some result =>
              simp [Metta.Bindings.addVarEquality, hunify, hrun] at hout
              subst out
              refine rebuildFromReconciliation_classChoiceBasis hnoFloat ?_ hrun ?_
              · intro equation hmem
                simp only [List.mem_singleton] at hmem
                subst equation
                simp [MettaAtomNoFloat]
              · intro valuation hmodel hextra x y hmem
                have hjoined := (leaBindingSatisfied_addEqRaw_iff valuation bindings left right).mpr
                  ⟨hmodel, by simpa [MettaEquationsSatisfied, MettaEquationSatisfied,
                    applyClassSolution] using hextra⟩
                exact hjoined.2 x y hmem

private theorem leaAddVarBinding_nonVar_result_classChoiceBasis
    {bindings out : Metta.Bindings} {key : String} {value : Metta.Atom}
    (hnonvar : ∀ target, value ≠ .var target)
    (hbasis : LeaClassChoiceBasis bindings)
    (hnoFloat : LeaBindingsNoFloat bindings)
    (hvalueNoFloat : MettaAtomNoFloat value)
    (hout : out ∈ Metta.Bindings.addVarBinding bindings key value) :
    LeaClassChoiceBasis out := by
  have hopen : Metta.Bindings.addVarBinding bindings key value =
      match Metta.Bindings.classValues bindings key with
      | [] => [Metta.Bindings.addValRaw bindings key value]
      | values =>
          match Metta.Bindings.unifyValues (values ++ [value]) with
          | none => []
          | some [] => [bindings]
          | some (_ :: _) =>
              match wholeBindingReconciliation bindings [(.var key, value)] with
              | none => []
              | some result => [Metta.Bindings.rebuildFromReconciliation bindings bindings
                  [(.var key, value)] result] := by
    cases value <;> try rfl
    exact (hnonvar _ rfl).elim
  rw [hopen] at hout
  cases hvalues : Metta.Bindings.classValues bindings key with
  | nil =>
      simp only [hvalues, List.mem_singleton] at hout
      subst out
      rw [show Metta.Bindings.addValRaw bindings key value = .val key value :: bindings by
        simp [Metta.Bindings.addValRaw, removeVal_eq_self_of_lookupVal_eq_none
          (leaLookupVal_eq_none_of_classValues_eq_nil hvalues)]]
      exact leaClassChoiceBasis_cons_fresh hbasis hvalues
  | cons first rest =>
      rw [hvalues] at hout
      change out ∈ (match Metta.Bindings.unifyValues ((first :: rest) ++ [value]) with
        | none => []
        | some [] => [bindings]
        | some (_ :: _) =>
            match wholeBindingReconciliation bindings [(.var key, value)] with
            | none => []
            | some result => [Metta.Bindings.rebuildFromReconciliation bindings bindings
                [(.var key, value)] result]) at hout
      cases hunify : Metta.Bindings.unifyValues ((first :: rest) ++ [value]) with
      | none => rw [hunify] at hout; simp at hout
      | some subst =>
          cases subst with
          | nil =>
              rw [hunify] at hout
              simp only [List.mem_singleton] at hout
              subst out
              exact hbasis
          | cons entry tail =>
              rw [hunify] at hout
              cases hrun : wholeBindingReconciliation bindings [(.var key, value)] with
              | none => simp [hrun] at hout
              | some result =>
                  simp [hrun] at hout
                  subst out
                  refine rebuildFromReconciliation_classChoiceBasis hnoFloat ?_ hrun ?_
                  · intro equation hmem
                    simp only [List.mem_singleton] at hmem
                    subst equation
                    exact ⟨by simp [MettaAtomNoFloat], hvalueNoFloat⟩
                  · intro valuation hmodel _
                    exact hmodel.2

/-- Native value insertion preserves the basis on all branches, including
fresh assignments that require a later cycle filter. -/
theorem leaAddVarBinding_result_classChoiceBasis
    {bindings out : Metta.Bindings} {key : String} {value : Metta.Atom}
    (hbasis : LeaClassChoiceBasis bindings)
    (hnoFloat : LeaBindingsNoFloat bindings)
    (hvalueNoFloat : MettaAtomNoFloat value)
    (hout : out ∈ Metta.Bindings.addVarBinding bindings key value) :
    LeaClassChoiceBasis out := by
  cases value with
  | var target =>
      exact leaAddVarEquality_result_classChoiceBasis hbasis hnoFloat
        (by simpa [Metta.Bindings.addVarBinding] using hout)
  | sym name | gnd name | expr name =>
      exact leaAddVarBinding_nonVar_result_classChoiceBasis
        (by intro target h; cases h) hbasis hnoFloat hvalueNoFloat hout

@[simp] theorem leaClassChoiceBasis_empty : LeaClassChoiceBasis [] := by
  intro valuation _
  simp [LeaBindingSatisfied]

theorem leaClassChoiceBasis_singleton_value (key : String) (value : Metta.Atom) :
    LeaClassChoiceBasis [.val key value] :=
  leaClassChoiceBasis_cons_fresh leaClassChoiceBasis_empty (by simp)

theorem leaClassChoiceBasis_singleton_equality (left right : String) :
    LeaClassChoiceBasis [.eq left right] := by
  intro valuation hselected
  constructor
  · simp
  · intro first second hmem
    simp only [List.mem_singleton, Metta.BindingRel.eq.injEq] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    apply hselected.1 first second
    rw [mem_leaEqClass_iff_reachable]
    by_cases heq : first = second
    · subst second
      exact .rfl
    · apply SimpleGraph.Adj.reachable
      rw [EqualityClosure.edgeGraph_adj_iff]
      exact ⟨heq, Or.inl (by simp [leaEqualityEdges])⟩

private theorem leaMergeOne_result_classChoiceBasis
    {seeds : List Metta.Bindings} {relation : Metta.BindingRel} {out : Metta.Bindings}
    (hseeds : ∀ seed ∈ seeds, LeaClassChoiceBasis seed)
    (hseedsNoFloat : ∀ seed ∈ seeds, LeaBindingsNoFloat seed)
    (hrelation : LeaBindingsNoFloat [relation])
    (hout : out ∈ Metta.Bindings.mergeOne seeds relation) :
    LeaClassChoiceBasis out := by
  obtain ⟨seed, hseed, hout⟩ := List.mem_flatMap.mp hout
  cases relation with
  | val key value =>
      exact leaAddVarBinding_result_classChoiceBasis
        (hseeds seed hseed) (hseedsNoFloat seed hseed)
        (hrelation key value (by simp)) hout
  | eq left right =>
      exact leaAddVarEquality_result_classChoiceBasis
        (hseeds seed hseed) (hseedsNoFloat seed hseed) hout

private theorem leaMergeFold_result_classChoiceBasis
    {relations : Metta.Bindings} {seeds : List Metta.Bindings} {out : Metta.Bindings}
    (hseeds : ∀ seed ∈ seeds, LeaClassChoiceBasis seed)
    (hseedsNoFloat : ∀ seed ∈ seeds, LeaBindingsNoFloat seed)
    (hrelations : LeaBindingsNoFloat relations)
    (hout : out ∈ relations.foldl Metta.Bindings.mergeOne seeds) :
    LeaClassChoiceBasis out := by
  induction relations generalizing seeds out with
  | nil => exact hseeds out hout
  | cons relation rest ih =>
      have hhead : LeaBindingsNoFloat [relation] := by
        intro key value hmem
        exact hrelations key value (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hmem)))
      have hrest : LeaBindingsNoFloat rest := by
        intro key value hmem
        exact hrelations key value (List.mem_cons_of_mem _ hmem)
      exact ih
        (fun next hnext => leaMergeOne_result_classChoiceBasis hseeds hseedsNoFloat hhead hnext)
        (fun next hnext => leaMergeOne_result_noFloat hseedsNoFloat hhead hnext)
        hrest hout

/-- Actual merge preserves the basis of its accumulator. Incoming relations
need only be in the float-free fragment; their own basis is not assumed. -/
theorem leaMerge_result_classChoiceBasis
    {left right out : Metta.Bindings}
    (hleft : LeaClassChoiceBasis left)
    (hleftNoFloat : LeaBindingsNoFloat left)
    (hrightNoFloat : LeaBindingsNoFloat right)
    (hout : out ∈ Metta.Bindings.merge left right) :
    LeaClassChoiceBasis out := by
  exact leaMergeFold_result_classChoiceBasis
    (seeds := [left]) (relations := right)
    (by simpa using hleft) (by simpa using hleftNoFloat) hrightNoFloat hout

/-- Pointwise matching preserves the accumulator basis even across nested
expression matches and temporary cyclic candidates. -/
theorem leaMatchAll_result_classChoiceBasis
    {lefts rights : List Metta.Atom} {seeds : List Metta.Bindings} {out : Metta.Bindings}
    (hlefts : ∀ atom ∈ lefts, MettaAtomNoFloat atom)
    (hrights : ∀ atom ∈ rights, MettaAtomNoFloat atom)
    (hseeds : ∀ seed ∈ seeds, LeaClassChoiceBasis seed)
    (hseedsNoFloat : ∀ seed ∈ seeds, LeaBindingsNoFloat seed)
    (hout : out ∈ Metta.matchAll none seeds lefts rights) :
    LeaClassChoiceBasis out := by
  induction lefts generalizing rights seeds out with
  | nil =>
      cases rights with
      | nil => exact hseeds out hout
      | cons head tail => simp [Metta.matchAll] at hout
  | cons left lefts ih =>
      cases rights with
      | nil => simp [Metta.matchAll] at hout
      | cons right rights =>
          let next := seeds.flatMap fun seed => (Metta.matchAtoms left right).flatMap
            fun matched => Metta.Bindings.merge seed matched
          have htail : out ∈ Metta.matchAll none next lefts rights := by
            simpa [Metta.matchAll, Metta.matchAtoms, next] using hout
          have hmatched : ∀ matched ∈ Metta.matchAtoms left right,
              LeaBindingsNoFloat matched :=
            fun _ hmem => leaMatchAtoms_result_noFloat
              (hlefts left (by simp)) (hrights right (by simp)) hmem
          apply ih (rights := rights) (seeds := next)
            (fun atom hmem => hlefts atom (by simp [hmem]))
            (fun atom hmem => hrights atom (by simp [hmem])) ?_ ?_ htail
          · intro candidate hcandidate
            obtain ⟨seed, hseed, hcandidate⟩ := List.mem_flatMap.mp hcandidate
            obtain ⟨matched, hmatch, hmerge⟩ := List.mem_flatMap.mp hcandidate
            exact leaMerge_result_classChoiceBasis (hseeds seed hseed)
              (hseedsNoFloat seed hseed) (hmatched matched hmatch) hmerge
          · intro candidate hcandidate
            obtain ⟨seed, hseed, hcandidate⟩ := List.mem_flatMap.mp hcandidate
            obtain ⟨matched, hmatch, hmerge⟩ := List.mem_flatMap.mp hcandidate
            exact leaMerge_result_noFloat (hseedsNoFloat seed hseed)
              (hmatched matched hmatch) hmerge

/-- The complete default matcher builds the class-choice invariant before its
final cycle filter. This theorem follows actual insertion and reconciliation. -/
theorem leaMatchAtomsWith_result_classChoiceBasis
    {left right : Metta.Atom} {out : Metta.Bindings}
    (hleft : MettaAtomNoFloat left) (hright : MettaAtomNoFloat right)
    (hout : out ∈ Metta.matchAtomsWith none left right) :
    LeaClassChoiceBasis out := by
  cases left <;> cases right
  all_goals first
    | exact leaMatchAll_result_classChoiceBasis
        (by simpa [MettaAtomNoFloat] using hleft)
        (by simpa [MettaAtomNoFloat] using hright)
        (by simp) (by simp [LeaBindingsNoFloat]) hout
    | (simp only [Metta.matchAtomsWith] at hout
       split at hout <;> simp only [List.mem_singleton, List.not_mem_nil] at hout
       all_goals first
         | contradiction
         | (subst out; exact leaClassChoiceBasis_empty)
         | (subst out; exact leaClassChoiceBasis_singleton_value _ _)
         | (subst out; exact leaClassChoiceBasis_singleton_equality _ _))

/-- All queries to one LeaTTa equality class use the same stable ordering. -/
theorem leaEqClassOrdered_eq_of_mem_class
    {bindings : Metta.Bindings} {left right : String}
    (hclass : right ∈ Metta.Bindings.eqClass bindings left) :
    Metta.Bindings.eqClassOrdered bindings left =
      Metta.Bindings.eqClassOrdered bindings right := by
  have hreach := mem_leaEqClass_iff_reachable.mp hclass
  have hfilter :
      (Metta.Bindings.eqVarsInOrder bindings).filter
          (fun name => (Metta.Bindings.eqClass bindings left).contains name) =
      (Metta.Bindings.eqVarsInOrder bindings).filter
          (fun name => (Metta.Bindings.eqClass bindings right).contains name) := by
    apply List.filter_congr
    intro name _
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem,
      mem_leaEqClass_iff_reachable, mem_leaEqClass_iff_reachable]
    exact ⟨fun h => hreach.symm.trans h, fun h => hreach.trans h⟩
  unfold Metta.Bindings.eqClassOrdered
  rw [hfilter]
  generalize hfiltered :
    (Metta.Bindings.eqVarsInOrder bindings).filter
      (fun name => (Metta.Bindings.eqClass bindings right).contains name) = filtered
  cases filtered with
  | cons first rest => rfl
  | nil =>
      by_cases heq : left = right
      · simp [heq]
      · exfalso
        have hleftOrder := mem_leaEqVarsInOrder_iff.mpr
          (reachable_ne_endpoints_mem_edgeNodes_lea heq hreach).1
        have hleftClass : left ∈ Metta.Bindings.eqClass bindings right :=
          mem_leaEqClass_iff_reachable.mpr hreach.symm
        have hleftFilter := List.mem_filter.mpr
          ⟨hleftOrder, (List.contains_iff_mem).mpr hleftClass⟩
        rw [hfiltered] at hleftFilter
        exact List.not_mem_nil hleftFilter

/-- A successful resolution already fixes its result under the same accepted
native binding record. The proof uses selected class values and does not
assume that every stored class value has a common semantic solution. -/
theorem resolveAtomAux_result_fixed_of_hasLoop_false
    {bindings : Metta.Bindings} (admitted : Metta.Bindings.hasLoop bindings=false)
    (fuel : Nat) (visited : List String) (atom result : Metta.Atom)
    (resolved : Metta.Bindings.resolveAtomAux bindings fuel visited atom=some result) :
    Metta.instantiate bindings result=result := by
  induction fuel generalizing visited atom result with
  | zero => simp [Metta.Bindings.resolveAtomAux] at resolved
  | succ fuel ih =>
    cases atom with
    | sym symbol | gnd ground =>
      simp only [Metta.Bindings.resolveAtomAux,Option.some.injEq] at resolved
      subst result
      simp only [Metta.instantiate,Metta.Bindings.resolveAtom]
    | var key =>
      have representativeIn : Metta.Bindings.eqRepresentative bindings key ∈
          Metta.Bindings.eqClass bindings key := by
        apply mem_leaEqClassOrdered_iff.mp
        have nonempty := Bindings.eqClassOrdered_ne_nil bindings key
        unfold Metta.Bindings.eqRepresentative
        cases ordered : Metta.Bindings.eqClassOrdered bindings key with
        | nil => exact (nonempty ordered).elim
        | cons head rest => simp
      have representativeFixed
          (returned : result=.var (Metta.Bindings.eqRepresentative bindings key)) :
          Metta.instantiate bindings result=result := by
        rw [returned]
        calc
          Metta.instantiate bindings (.var (Metta.Bindings.eqRepresentative bindings key)) =
              Metta.instantiate bindings (.var key) :=
            (Bindings.instantiate_var_eq_of_eqClassOrdered_eq admitted
              (leaEqClassOrdered_eq_of_mem_class representativeIn)).symm
          _ = result := (Bindings.resolveAtomAux_some_eq_instantiate admitted _ resolved).symm
          _ = .var (Metta.Bindings.eqRepresentative bindings key) := returned
      cases checked : (Metta.Bindings.eqClassOrdered bindings key).any visited.contains with
      | true => simp [Metta.Bindings.resolveAtomAux,checked] at resolved
      | false =>
        cases values : Metta.Bindings.classValues bindings key with
        | nil =>
          apply representativeFixed
          simpa only [Metta.Bindings.resolveAtomAux,checked,Bool.false_eq_true,
            ↓reduceIte,values,Option.some.injEq] using resolved.symm
        | cons value rest =>
          cases value with
          | sym symbol | gnd ground | expr children =>
            apply ih _ _ _
            simpa only [Metta.Bindings.resolveAtomAux,checked,Bool.false_eq_true,
              ↓reduceIte,values] using resolved
          | var other =>
            by_cases internal : (Metta.Bindings.eqClassOrdered bindings key).contains other=true
            · by_cases singleton : (Metta.Bindings.eqClassOrdered bindings key).length == 1
              · simp only [Metta.Bindings.resolveAtomAux,checked,Bool.false_eq_true,
                  ↓reduceIte,values,internal,singleton] at resolved
                cases resolved
              · apply representativeFixed
                simpa only [Metta.Bindings.resolveAtomAux,checked,Bool.false_eq_true,
                  ↓reduceIte,values,internal,singleton,Option.some.injEq] using resolved.symm
            · apply ih _ _ _
              simpa only [Metta.Bindings.resolveAtomAux,checked,Bool.false_eq_true,
                ↓reduceIte,values,internal] using resolved
    | expr children =>
      have listFixed : ∀ source target,
          List.mapM (Metta.Bindings.resolveAtomAux bindings fuel visited) source=some target →
          List.map (Metta.instantiate bindings) target=target := by
        intro source
        induction source with
        | nil =>
          intro target mapped
          simp at mapped
          subst target
          rfl
        | cons head tail tailIH =>
          intro target mapped
          cases headResult : Metta.Bindings.resolveAtomAux bindings fuel visited head with
          | none => simp [List.mapM_cons,headResult] at mapped
          | some headValue =>
            cases tailResult : List.mapM (Metta.Bindings.resolveAtomAux bindings fuel visited) tail with
            | none => simp [List.mapM_cons,headResult,tailResult] at mapped
            | some tailValues =>
              simp [List.mapM_cons,headResult,tailResult] at mapped
              subst target
              simp only [List.map_cons,ih visited head headValue headResult,
                tailIH tailValues tailResult]
      cases mapped : children.mapM (Metta.Bindings.resolveAtomAux bindings fuel visited) with
      | none => simp [Metta.Bindings.resolveAtomAux,mapped] at resolved
      | some outputs =>
        simp only [Metta.Bindings.resolveAtomAux,mapped,Option.some.injEq] at resolved
        subst result
        simp only [Metta.instantiate,Metta.Bindings.resolveAtom]
        change Metta.Atom.expr (outputs.map (Metta.instantiate bindings))=Metta.Atom.expr outputs
        rw [listFixed children outputs mapped]

/-- The native loop filter suffices for idempotent instantiation, even on raw
records whose unselected class values are mutually inconsistent. -/
theorem instantiate_idempotent_of_hasLoop_false
    {bindings : Metta.Bindings} (admitted : Metta.Bindings.hasLoop bindings=false)
    (atom : Metta.Atom) :
    Metta.instantiate bindings (Metta.instantiate bindings atom)=Metta.instantiate bindings atom := by
  induction atom using Metta.Atom.recAux with
  | sym name => simp only [Metta.instantiate,Metta.Bindings.resolveAtom]
  | gnd ground => simp only [Metta.instantiate,Metta.Bindings.resolveAtom]
  | var key =>
    obtain ⟨value,resolved⟩ := Bindings.resolveAtomAux_some_of_hasLoop_false admitted key
    rw [Bindings.instantiate_var_of_resolveAtomAux_some resolved]
    exact resolveAtomAux_result_fixed_of_hasLoop_false admitted _ _ _ _ resolved
  | expr children ih =>
    simp only [Metta.instantiate,Metta.Bindings.resolveAtom]
    change Metta.Atom.expr ((children.map (Metta.instantiate bindings)).map (Metta.instantiate bindings)) =
      Metta.Atom.expr (children.map (Metta.instantiate bindings))
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro child member
    exact ih child member

/-- The actual native resolver produces a chosen-equation model whenever its
own complete loop check succeeds on normalized assignments. -/
theorem leaClassSolution_classChoiceSatisfied
    {bindings : Metta.Bindings}
    (hnonvariable : LeaAssignmentsNonVariable bindings)
    (hloop : Metta.Bindings.hasLoop bindings = false) :
    LeaClassChoiceSatisfied (leaClassSolution bindings) bindings := by
  constructor
  · intro left right hclass
    simpa only [leaClassSolution, Metta.instantiate, Metta.Bindings.resolveAtom] using
      (Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.instantiate_var_eq_of_eqClassOrdered_eq
        hloop (leaEqClassOrdered_eq_of_mem_class hclass))
  · intro key hnonempty
    cases hvalues : Metta.Bindings.classValues bindings key with
    | nil => exact (hnonempty hvalues).elim
    | cons value rest =>
        have hvalue : value ∈ Metta.Bindings.classValues bindings key := by simp [hvalues]
        refine ⟨value, by simp, ?_⟩
        rw [applyClassSolution_lea_eq_instantiate]
        simpa only [leaClassSolution, Metta.instantiate, Metta.Bindings.resolveAtom] using
          (Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.instantiate_first_class_value
            hloop hvalues (leaClassValue_nonvariable hnonvariable hvalue))

/-- Every successful default matcher output's actual native instantiation is a
model of every stored relation, including values hidden behind class selection. -/
theorem leaMatchAtoms_classSolution_satisfies
    {left right : Metta.Atom} {out : Metta.Bindings}
    (hleft : MettaAtomNoFloat left) (hright : MettaAtomNoFloat right)
    (hout : out ∈ Metta.matchAtoms left right) :
    LeaBindingSatisfied (leaClassSolution out) out := by
  obtain ⟨hraw, hloop⟩ : out ∈ Metta.matchAtomsWith none left right ∧ out.hasLoop = false := by
    simpa [Metta.matchAtoms] using hout
  exact leaMatchAtomsWith_result_classChoiceBasis hleft hright hraw
    (leaClassSolution out)
    (leaClassSolution_classChoiceSatisfied
      (leaMatchAtomsWith_result_assignmentsNonVariable hraw) hloop)

/-- Successful default matching constructs a finite satisfying valuation. -/
theorem leaMatchAtoms_exists_satisfied
    {left right : Metta.Atom} {out : Metta.Bindings}
    (hleft : MettaAtomNoFloat left) (hright : MettaAtomNoFloat right)
    (hout : out ∈ Metta.matchAtoms left right) :
    ∃ valuation, LeaBindingSatisfied valuation out :=
  ⟨leaClassSolution out, leaMatchAtoms_classSolution_satisfies hleft hright hout⟩

/-- Native successful matching excludes cycles in the full independent
class/compound dependency graph, rather than merely its selected-value graph. -/
theorem leaMatchAtoms_semanticLoopFree
    {left right : Metta.Atom} {out : Metta.Bindings}
    (hleft : MettaAtomNoFloat left) (hright : MettaAtomNoFloat right)
    (hout : out ∈ Metta.matchAtoms left right) :
    LeaSemanticLoopFree out :=
  leaSemanticLoopFree_of_satisfied_nonvariable
    (leaMatchAtoms_classSolution_satisfies hleft hright hout)
    (leaMatchAtoms_result_assignmentsNonVariable hout)


/-- Successful matching makes its input atoms equal under the actual native
instantiation, not just under an abstract existential valuation. -/
theorem leaMatchAtoms_instantiate_eq
    {left right : Metta.Atom} {out : Metta.Bindings}
    (hleft : MettaAtomNoFloat left) (hright : MettaAtomNoFloat right)
    (hout : out ∈ Metta.matchAtoms left right) :
    Metta.instantiate out left = Metta.instantiate out right := by
  have hmodel := leaMatchAtoms_classSolution_satisfies hleft hright hout
  have hequation := (leaMatchAtoms_solution_iff (leaClassSolution out)
    hleft hright hout).mp hmodel
  simpa only [MettaEquationSatisfied, applyClassSolution_lea_eq_instantiate] using hequation

namespace ClassDependencyControls

/-- A Boolean pass on a hand-built record does not establish the invariant
proved for actual matcher outputs. -/
theorem ignoredClassValue_not_classChoiceBasis :
    ¬LeaClassChoiceBasis ignoredClassValue := by
  intro hbasis
  exact ignoredClassValue_semantic_cycle
    (leaSemanticLoopFree_of_satisfied_nonvariable
      (hbasis (leaClassSolution ignoredClassValue)
        (leaClassSolution_classChoiceSatisfied
          ignoredClassValue_nonvariable ignoredClassValue_no_runtime_loop))
      ignoredClassValue_nonvariable)

/-- The hidden-cycle raw record cannot be returned by successful default
matching anywhere in the float-free fragment. -/
theorem ignoredClassValue_not_match_output
    {left right : Metta.Atom}
    (hleft : MettaAtomNoFloat left) (hright : MettaAtomNoFloat right) :
    ignoredClassValue ∉ Metta.matchAtoms left right := by
  intro hout
  exact ignoredClassValue_semantic_cycle (leaMatchAtoms_semanticLoopFree hleft hright hout)

/-- Two different stored occurrences may agree in one equality class. -/
def coherentClassValues : Metta.Bindings :=
  [.eq "y" "x", .val "y" (.sym "a"), .val "x" (.sym "a")]

theorem coherentClassValues_classChoiceBasis : LeaClassChoiceBasis coherentClassValues := by
  let seed : Metta.Bindings :=
    [.val "y" (.sym "a"), .val "x" (.sym "a")]
  have hseed : LeaClassChoiceBasis seed :=
    leaClassChoiceBasis_cons_fresh
      (leaClassChoiceBasis_singleton_value "x" (.sym "a")) (by rfl)
  have hraw : Metta.Bindings.addEqRaw seed "y" "x" = coherentClassValues := by
    rw [Metta.Bindings.addEqRaw_of_not_mem seed "y" "x" (by decide) (by
      simp [seed])]
    rfl
  have hbasis := leaClassChoiceBasis_addEqRaw_of_trivial
    (bindings := seed) (left := "y") (right := "x") hseed
    (by intro key value hmem
        simp only [seed, List.mem_cons, List.not_mem_nil, or_false,
          Metta.BindingRel.val.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [MettaAtomNoFloat])
    (by
      rw [hraw]
      change Metta.Bindings.unifyValues [.sym "a", .sym "a"] = some []
      simp [Metta.Bindings.unifyValues, Metta.Unify.unifyRounds,
        Metta.Unify.decomposeAll, Metta.Unify.decomposeEq,
        Metta.Atom.size])
  rwa [hraw] at hbasis

end ClassDependencyControls

private theorem heAssignment_mem_of_lookup_eq_some
    {assignments : List (String × Atom)} {x : String} {value : Atom}
    (hlookup : List.lookup x assignments = some value) :
    (x, value) ∈ assignments := by
  induction assignments with
  | nil => simp at hlookup
  | cons binding rest ih =>
      rcases binding with ⟨key, stored⟩
      by_cases hx : x = key
      · subst key
        simp at hlookup
        subst stored
        simp
      · have hbeq : (x == key) = false := by simp [hx]
        have htail : List.lookup x rest = some value := by
          simpa [List.lookup_cons, hbeq] using hlookup
        exact List.mem_cons_of_mem _ (ih htail)

private theorem heBindingSatisfied_eq_of_reachable
    {valuation : String → Metta.Atom} {b : Bindings} {left right : String}
    (hsatisfied : HEBindingSatisfied valuation b)
    (hreach :
      (EqualityClosure.edgeGraph b.equalities).Reachable left right) :
    valuation left = valuation right := by
  apply hreach.elim
  intro walk
  induction walk with
  | nil => rfl
  | @cons start next finish hadj tail ih =>
      have hstep : valuation start = valuation next := by
        rcases (EqualityClosure.edgeGraph_adj_iff.mp hadj).2 with hedge | hedge
        · exact hsatisfied.2 start next hedge
        · exact (hsatisfied.2 next start hedge).symm
      exact hstep.trans (ih tail.reachable)

/-- Every value carried by an HE equality class is an equation for every
satisfying valuation, independent of the class's representative order. -/
theorem heBindingSatisfied_classValue
    {valuation : String → Metta.Atom} {b : Bindings}
    {v : String} {value : Atom}
    (hsatisfied : HEBindingSatisfied valuation b)
    (hvalue : value ∈ b.classValues v) :
    valuation v = applyClassSolution valuation (encodeModelAtom value) := by
  unfold Bindings.classValues at hvalue
  obtain ⟨key, hkey, hlookup⟩ := List.mem_filterMap.mp hvalue
  have hreach :
      (EqualityClosure.edgeGraph b.equalities).Reachable v key := by
    rw [← EqualityClosure.mem_eqClass_iff_reachable]
    exact EqualityClosure.mem_eqClassOrdered_iff.mp hkey
  have hassignment : (key, value) ∈ b.assignments :=
    heAssignment_mem_of_lookup_eq_some (by
      simpa [Bindings.lookup] using hlookup)
  exact (heBindingSatisfied_eq_of_reachable hsatisfied hreach).trans
    (hsatisfied.1 key value hassignment)

private theorem heLookup_eq_none_of_classValues_eq_nil
    {b : Bindings} {v : String} (hvalues : b.classValues v = []) :
    b.lookup v = none := by
  unfold Bindings.classValues at hvalues
  apply List.filterMap_eq_nil_iff.mp hvalues v
  rw [EqualityClosure.mem_eqClassOrdered_iff,
    EqualityClosure.mem_eqClass_iff_reachable]

/-- Simultaneous solution-theory contract for the five mutually recursive HE
matcher/merge operations at one executable fuel. -/
structure HESolutionTheoryPack (fuel : Nat) : Prop where
  matchTheory : ∀ {left right out},
    out ∈ matchAtoms left right fuel →
      ∀ valuation,
        HEBindingSatisfied valuation out ↔
          HEAtomEquationSatisfied valuation left right
  listTheory : ∀ {lefts rights seeds out},
    out ∈ matchAtomsList lefts rights seeds fuel →
      ∃ seed ∈ seeds, ∀ valuation,
        HEBindingSatisfied valuation out ↔
          HEBindingSatisfied valuation seed ∧
            HEAtomListEquationsSatisfied valuation lefts rights
  mergeTheory : ∀ {left right out},
    out ∈ mergeBindings left right fuel →
      ∀ valuation,
        HEBindingSatisfied valuation out ↔
          HEBindingSatisfied valuation left ∧
            HEBindingSatisfied valuation right
  addValueTheory : ∀ {b v value out},
    out ∈ addVarBinding b v value fuel →
      ∀ valuation,
        HEBindingSatisfied valuation out ↔
          HEBindingSatisfied valuation b ∧
            valuation v =
              applyClassSolution valuation (encodeModelAtom value)
  addEqualityTheory : ∀ {b left right out},
    out ∈ addVarEquality b left right fuel →
      ∀ valuation,
        HEBindingSatisfied valuation out ↔
          HEBindingSatisfied valuation b ∧
            valuation left = valuation right

private theorem heSolutionTheoryPack_zero : HESolutionTheoryPack 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro left right out hmem
    simp [matchAtoms] at hmem
  · intro lefts rights seeds out hmem
    simp [matchAtomsList] at hmem
  · intro left right out hmem
    simp [mergeBindings] at hmem
  · intro b v value out hmem
    simp [addVarBinding] at hmem
  · intro b left right out hmem
    simp [addVarEquality] at hmem

private theorem heAtomListEquations_replicate_append_iff
    (valuation : String → Metta.Atom) (first value : Atom) :
    ∀ rest : List Atom,
      (∀ other ∈ rest,
        HEAtomEquationSatisfied valuation first other) →
      (HEAtomListEquationsSatisfied valuation
          (List.replicate (rest ++ [value]).length first) (rest ++ [value]) ↔
        HEAtomEquationSatisfied valuation first value) := by
  intro rest
  induction rest with
  | nil =>
      intro _
      simp [HEAtomListEquationsSatisfied]
  | cons other rest ih =>
      intro hall
      have hother : HEAtomEquationSatisfied valuation first other :=
        hall other (by simp)
      have htail : ∀ item ∈ rest,
          HEAtomEquationSatisfied valuation first item := by
        intro item hmem
        exact hall item (by simp [hmem])
      simpa [List.replicate_succ, HEAtomListEquationsSatisfied, hother] using
        ih htail

private theorem heAtomListEquations_replicate
    (valuation : String → Metta.Atom) (first : Atom) :
    ∀ rest : List Atom,
      (∀ other ∈ rest,
        HEAtomEquationSatisfied valuation first other) →
      HEAtomListEquationsSatisfied valuation
        (List.replicate rest.length first) rest := by
  intro rest
  induction rest with
  | nil =>
      intro _
      trivial
  | cons other rest ih =>
      intro hall
      have hother := hall other (by simp)
      have htail : ∀ item ∈ rest,
          HEAtomEquationSatisfied valuation first item := by
        intro item hmem
        exact hall item (by simp [hmem])
      simpa [List.replicate_succ, HEAtomListEquationsSatisfied, hother] using
        ih htail

private theorem heAddValueTheory_succ
    {fuel : Nat} (ih : HESolutionTheoryPack fuel)
    {b : Bindings} {v : String} {value : Atom} {out : Bindings}
    (hout : out ∈ addVarBinding b v value (fuel + 1)) :
    ∀ valuation,
      HEBindingSatisfied valuation out ↔
        HEBindingSatisfied valuation b ∧
          valuation v =
            applyClassSolution valuation (encodeModelAtom value) := by
  simp only [addVarBinding] at hout
  cases hvalues : b.classValues v with
  | nil =>
      simp [hvalues] at hout
      subst out
      exact fun valuation =>
        heBindingSatisfied_assign_fresh_iff valuation
          (heLookup_eq_none_of_classValues_eq_nil hvalues)
  | cons first rest =>
      simp only [hvalues] at hout
      by_cases hconsistent : Bindings.valuesConsistent (first :: rest) = true
      · rw [if_pos hconsistent] at hout
        by_cases hsame : first = value
        · have hbeq : (first == value) = true := by simp [hsame]
          rw [if_pos hbeq] at hout
          simp only [List.mem_singleton] at hout
          subst out
          intro valuation
          constructor
          · intro hsatisfied
            refine ⟨hsatisfied, ?_⟩
            have hfirst : first ∈ b.classValues v := by
              rw [hvalues]
              simp
            simpa [hsame] using
              heBindingSatisfied_classValue hsatisfied hfirst
          · exact And.left
        · have hbeq : ¬(first == value) = true := by simpa using hsame
          rw [if_neg hbeq] at hout
          obtain ⟨matched, hmatched, hmerged⟩ := List.mem_flatMap.mp hout
          intro valuation
          rw [ih.mergeTheory hmerged, ih.matchTheory hmatched]
          have hfirst : first ∈ b.classValues v := by
            rw [hvalues]
            simp
          constructor
          · rintro ⟨hsatisfied, hequation⟩
            exact ⟨hsatisfied,
              (heBindingSatisfied_classValue hsatisfied hfirst).trans
                hequation⟩
          · rintro ⟨hsatisfied, hnew⟩
            exact ⟨hsatisfied,
              (heBindingSatisfied_classValue hsatisfied hfirst).symm.trans
                hnew⟩
      · rw [if_neg hconsistent] at hout
        obtain ⟨matched, hmatched, hmerged⟩ := List.mem_flatMap.mp hout
        intro valuation
        rw [ih.mergeTheory hmerged]
        obtain ⟨seed, hseed, hmatchedTheory⟩ := ih.listTheory hmatched
        have hseedEmpty : seed = Bindings.empty := by simpa using hseed
        subst seed
        rw [hmatchedTheory]
        have hempty : HEBindingSatisfied valuation Bindings.empty := by
          simp [HEBindingSatisfied, Bindings.empty]
        simp only [hempty, true_and]
        have hfirstMem : first ∈ b.classValues v := by
          rw [hvalues]
          simp
        constructor
        · rintro ⟨hsatisfied, hlist⟩
          have hrest : ∀ other ∈ rest,
              HEAtomEquationSatisfied valuation first other := by
            intro other hother
            have hotherMem : other ∈ b.classValues v := by
              rw [hvalues]
              simp [hother]
            exact (heBindingSatisfied_classValue hsatisfied hfirstMem).symm.trans
              (heBindingSatisfied_classValue hsatisfied hotherMem)
          have hfinal :=
            (heAtomListEquations_replicate_append_iff
              valuation first value rest hrest).mp hlist
          exact ⟨hsatisfied,
            (heBindingSatisfied_classValue hsatisfied hfirstMem).trans hfinal⟩
        · rintro ⟨hsatisfied, hnew⟩
          have hrest : ∀ other ∈ rest,
              HEAtomEquationSatisfied valuation first other := by
            intro other hother
            have hotherMem : other ∈ b.classValues v := by
              rw [hvalues]
              simp [hother]
            exact (heBindingSatisfied_classValue hsatisfied hfirstMem).symm.trans
              (heBindingSatisfied_classValue hsatisfied hotherMem)
          exact ⟨hsatisfied,
            (heAtomListEquations_replicate_append_iff
              valuation first value rest hrest).mpr
                ((heBindingSatisfied_classValue
                  hsatisfied hfirstMem).symm.trans hnew)⟩

private theorem heAddEqualityTheory_succ
    {fuel : Nat} (ih : HESolutionTheoryPack fuel)
    {b : Bindings} {left right : String} {out : Bindings}
    (hout : out ∈ addVarEquality b left right (fuel + 1)) :
    ∀ valuation,
      HEBindingSatisfied valuation out ↔
        HEBindingSatisfied valuation b ∧
          valuation left = valuation right := by
  simp only [addVarEquality] at hout
  let candidate := b.addEquality left right
  change out ∈
    (if Bindings.valuesConsistent (candidate.classValues left) then
      [candidate]
    else
      match candidate.classValues left with
      | [] => []
      | first :: [second] =>
          (matchAtoms first second fuel).flatMap fun matched =>
            mergeBindings candidate matched fuel
      | first :: rest =>
          (matchAtomsList (List.replicate rest.length first) rest
              [Bindings.empty] fuel).flatMap fun matched =>
            mergeBindings candidate matched fuel) at hout
  by_cases hconsistent :
      Bindings.valuesConsistent (candidate.classValues left) = true
  · rw [if_pos hconsistent] at hout
    simp only [List.mem_singleton] at hout
    subst out
    exact fun valuation => by
      simpa [candidate] using
        heBindingSatisfied_addEquality_iff valuation b left right
  · rw [if_neg hconsistent] at hout
    cases hvalues : candidate.classValues left with
    | nil =>
        simp [hvalues, Bindings.valuesConsistent] at hconsistent
    | cons first rest =>
        simp only [hvalues] at hout
        cases rest with
        | nil =>
            simp [hvalues, Bindings.valuesConsistent] at hconsistent
        | cons second tail =>
            cases tail with
            | nil =>
                obtain ⟨matched, hmatched, hmerged⟩ :=
                  List.mem_flatMap.mp hout
                intro valuation
                rw [ih.mergeTheory hmerged, ih.matchTheory hmatched]
                constructor
                · rintro ⟨hcandidate, _⟩
                  exact (heBindingSatisfied_addEquality_iff
                    valuation b left right).mp (by
                      simpa [candidate] using hcandidate)
                · intro hbase
                  have hcandidate : HEBindingSatisfied valuation candidate := by
                    simpa [candidate] using
                      (heBindingSatisfied_addEquality_iff
                        valuation b left right).mpr hbase
                  have hfirst : first ∈ candidate.classValues left := by
                    rw [hvalues]
                    simp
                  have hsecond : second ∈ candidate.classValues left := by
                    rw [hvalues]
                    simp
                  exact ⟨hcandidate,
                    (heBindingSatisfied_classValue
                      hcandidate hfirst).symm.trans
                        (heBindingSatisfied_classValue hcandidate hsecond)⟩
            | cons third tail =>
                obtain ⟨matched, hmatched, hmerged⟩ :=
                  List.mem_flatMap.mp hout
                intro valuation
                rw [ih.mergeTheory hmerged]
                obtain ⟨seed, hseed, hmatchedTheory⟩ :=
                  ih.listTheory hmatched
                have hseedEmpty : seed = Bindings.empty := by
                  simpa using hseed
                subst seed
                rw [hmatchedTheory]
                have hempty : HEBindingSatisfied valuation Bindings.empty := by
                  simp [HEBindingSatisfied, Bindings.empty]
                simp only [hempty, true_and]
                constructor
                · rintro ⟨hcandidate, _⟩
                  exact (heBindingSatisfied_addEquality_iff
                    valuation b left right).mp (by
                      simpa [candidate] using hcandidate)
                · intro hbase
                  have hcandidate : HEBindingSatisfied valuation candidate := by
                    simpa [candidate] using
                      (heBindingSatisfied_addEquality_iff
                        valuation b left right).mpr hbase
                  have hfirst : first ∈ candidate.classValues left := by
                    rw [hvalues]
                    simp
                  have hall : ∀ other ∈ second :: third :: tail,
                      HEAtomEquationSatisfied valuation first other := by
                    intro other hother
                    have hotherMem : other ∈ candidate.classValues left := by
                      rw [hvalues]
                      simp [hother]
                    exact (heBindingSatisfied_classValue
                      hcandidate hfirst).symm.trans
                        (heBindingSatisfied_classValue hcandidate hotherMem)
                  exact ⟨hcandidate,
                    heAtomListEquations_replicate valuation first
                      (second :: third :: tail) hall⟩

private def HEAssignmentsSatisfied
    (valuation : String → Metta.Atom) (assignments : List (String × Atom)) : Prop :=
  ∀ x value, (x, value) ∈ assignments →
    valuation x = applyClassSolution valuation (encodeModelAtom value)

private def HEEqualitiesSatisfied
    (valuation : String → Metta.Atom) (equalities : List (String × String)) : Prop :=
  ∀ left right, (left, right) ∈ equalities →
    valuation left = valuation right

@[simp] private theorem heAssignmentsSatisfied_cons_iff
    (valuation : String → Metta.Atom) (v : String) (value : Atom)
    (rest : List (String × Atom)) :
    HEAssignmentsSatisfied valuation ((v, value) :: rest) ↔
      valuation v = applyClassSolution valuation (encodeModelAtom value) ∧
        HEAssignmentsSatisfied valuation rest := by
  constructor
  · intro hall
    refine ⟨hall v value (by simp), ?_⟩
    intro x other hmem
    exact hall x other (by simp [hmem])
  · rintro ⟨hhead, htail⟩ x other hmem
    simp only [List.mem_cons, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | hmem
    · exact hhead
    · exact htail x other hmem

@[simp] private theorem heEqualitiesSatisfied_cons_iff
    (valuation : String → Metta.Atom) (left right : String)
    (rest : List (String × String)) :
    HEEqualitiesSatisfied valuation ((left, right) :: rest) ↔
      valuation left = valuation right ∧
        HEEqualitiesSatisfied valuation rest := by
  constructor
  · intro hall
    refine ⟨hall left right (by simp), ?_⟩
    intro x y hmem
    exact hall x y (by simp [hmem])
  · rintro ⟨hhead, htail⟩ x y hmem
    simp only [List.mem_cons, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | hmem
    · exact hhead
    · exact htail x y hmem

private theorem heAssignmentFoldTheory
    {fuel : Nat} (ih : HESolutionTheoryPack fuel)
    (assignments : List (String × Atom)) :
    ∀ {seeds out},
      out ∈ assignments.foldl
        (fun (acc : List Bindings) (binding : String × Atom) =>
          acc.flatMap fun b =>
          addVarBinding b binding.1 binding.2 fuel) seeds →
      ∃ seed ∈ seeds, ∀ valuation,
        HEBindingSatisfied valuation out ↔
          HEBindingSatisfied valuation seed ∧
            HEAssignmentsSatisfied valuation assignments := by
  induction assignments with
  | nil =>
      intro seeds out hout
      exact ⟨out, hout, fun _ => by
        simp [HEAssignmentsSatisfied]⟩
  | cons binding rest ihRest =>
      rcases binding with ⟨v, value⟩
      intro seeds out hout
      simp only [List.foldl_cons] at hout
      obtain ⟨mid, hmid, houtTheory⟩ := ihRest hout
      obtain ⟨seed, hseed, hadded⟩ := List.mem_flatMap.mp hmid
      refine ⟨seed, hseed, ?_⟩
      intro valuation
      rw [houtTheory, ih.addValueTheory hadded,
        heAssignmentsSatisfied_cons_iff]
      simp [and_assoc]

private theorem heEqualityFoldTheory
    {fuel : Nat} (ih : HESolutionTheoryPack fuel)
    (equalities : List (String × String)) :
    ∀ {seeds out},
      out ∈ equalities.foldl
        (fun (acc : List Bindings) (equality : String × String) =>
          acc.flatMap fun b =>
          addVarEquality b equality.1 equality.2 fuel) seeds →
      ∃ seed ∈ seeds, ∀ valuation,
        HEBindingSatisfied valuation out ↔
          HEBindingSatisfied valuation seed ∧
            HEEqualitiesSatisfied valuation equalities := by
  induction equalities with
  | nil =>
      intro seeds out hout
      exact ⟨out, hout, fun _ => by
        simp [HEEqualitiesSatisfied]⟩
  | cons equality rest ihRest =>
      rcases equality with ⟨left, right⟩
      intro seeds out hout
      simp only [List.foldl_cons] at hout
      obtain ⟨mid, hmid, houtTheory⟩ := ihRest hout
      obtain ⟨seed, hseed, hadded⟩ := List.mem_flatMap.mp hmid
      refine ⟨seed, hseed, ?_⟩
      intro valuation
      rw [houtTheory, ih.addEqualityTheory hadded,
        heEqualitiesSatisfied_cons_iff]
      simp [and_assoc]

private theorem heMergeTheory_succ
    {fuel : Nat} (ih : HESolutionTheoryPack fuel)
    {left right out : Bindings}
    (hout : out ∈ mergeBindings left right (fuel + 1)) :
    ∀ valuation,
      HEBindingSatisfied valuation out ↔
        HEBindingSatisfied valuation left ∧
          HEBindingSatisfied valuation right := by
  simp only [mergeBindings] at hout
  obtain ⟨mid, hmid, houtTheory⟩ :=
    heEqualityFoldTheory ih right.equalities hout
  obtain ⟨seed, hseed, hmidTheory⟩ :=
    heAssignmentFoldTheory ih right.assignments hmid
  have hseedLeft : seed = left := by simpa using hseed
  subst seed
  intro valuation
  rw [houtTheory, hmidTheory]
  change
    ((HEBindingSatisfied valuation left ∧
          HEAssignmentsSatisfied valuation right.assignments) ∧
        HEEqualitiesSatisfied valuation right.equalities) ↔
      HEBindingSatisfied valuation left ∧
        (HEAssignmentsSatisfied valuation right.assignments ∧
          HEEqualitiesSatisfied valuation right.equalities)
  simp [and_assoc]

private theorem heListTheory_succ
    {fuel : Nat} (ih : HESolutionTheoryPack fuel)
    {lefts rights : List Atom} {seeds : List Bindings} {out : Bindings}
    (hout : out ∈ matchAtomsList lefts rights seeds (fuel + 1)) :
    ∃ seed ∈ seeds, ∀ valuation,
      HEBindingSatisfied valuation out ↔
        HEBindingSatisfied valuation seed ∧
          HEAtomListEquationsSatisfied valuation lefts rights := by
  cases lefts with
  | nil =>
      cases rights with
      | nil =>
          simp [matchAtomsList] at hout
          exact ⟨out, hout, fun _ => by
            simp [HEAtomListEquationsSatisfied]⟩
      | cons right rights =>
          simp [matchAtomsList] at hout
  | cons left lefts =>
      cases rights with
      | nil =>
          simp [matchAtomsList] at hout
      | cons right rights =>
          simp only [matchAtomsList] at hout
          obtain ⟨mid, hmid, houtTheory⟩ := ih.listTheory hout
          obtain ⟨seed, hseed, hmid⟩ := List.mem_flatMap.mp hmid
          obtain ⟨matched, hmatched, hmerged⟩ := List.mem_flatMap.mp hmid
          refine ⟨seed, hseed, ?_⟩
          intro valuation
          rw [houtTheory, ih.mergeTheory hmerged, ih.matchTheory hmatched]
          simp [HEAtomListEquationsSatisfied, and_assoc]

private theorem heAtomListEquations_iff_expressionEquation
    (valuation : String → Metta.Atom) :
    ∀ {lefts rights : List Atom}, lefts.length = rights.length →
      (HEAtomListEquationsSatisfied valuation lefts rights ↔
        HEAtomEquationSatisfied valuation
          (.expression lefts) (.expression rights)) := by
  intro lefts
  induction lefts with
  | nil =>
      intro rights hlength
      cases rights with
      | nil =>
          simp [HEAtomListEquationsSatisfied, HEAtomEquationSatisfied,
            encodeModelAtom, encodeModelAtoms, applyClassSolution]
      | cons right rights => simp at hlength
  | cons left lefts ih =>
      intro rights hlength
      cases rights with
      | nil => simp at hlength
      | cons right rights =>
          have htail : lefts.length = rights.length := by
            simpa using hlength
          simp [HEAtomListEquationsSatisfied, HEAtomEquationSatisfied,
            encodeModelAtom, encodeModelAtoms, applyClassSolution, ih htail]

private theorem heMatchTheory_succ
    {fuel : Nat} (ih : HESolutionTheoryPack fuel)
    {left right : Atom} {out : Bindings}
    (hout : out ∈ matchAtoms left right (fuel + 1)) :
    ∀ valuation,
      HEBindingSatisfied valuation out ↔
        HEAtomEquationSatisfied valuation left right := by
  cases left with
  | symbol leftSymbol =>
      cases right with
      | symbol rightSymbol =>
          by_cases heq : leftSymbol = rightSymbol
          · subst rightSymbol
            simp [matchAtoms, getMetaType, Atom.symbolType] at hout
            have houtEmpty : out = Bindings.empty := by simpa using hout.1
            subst out
            simp [HEBindingSatisfied, HEAtomEquationSatisfied,
              Bindings.empty, encodeModelAtom, applyClassSolution]
          · simp [matchAtoms, getMetaType, Atom.symbolType, heq] at hout
      | var v =>
          simp [matchAtoms, getMetaType, Atom.symbolType,
            Atom.variableType] at hout
          have houtAssign : out = Bindings.empty.assign v (.symbol leftSymbol) := by
            simpa using hout.1
          subst out
          simp [HEBindingSatisfied, HEAtomEquationSatisfied, Bindings.empty,
            Bindings.assign, Bindings.isBound, Bindings.lookup,
            encodeModelAtom, applyClassSolution, eq_comm]
      | grounded ground =>
          simp [matchAtoms, getMetaType, Atom.symbolType,
            Atom.groundedType] at hout
      | expression atoms =>
          simp [matchAtoms, getMetaType, Atom.symbolType,
            Atom.expressionType] at hout
  | var v =>
      cases right with
      | symbol symbol =>
          simp [matchAtoms, getMetaType, Atom.symbolType,
            Atom.variableType] at hout
          have houtAssign : out = Bindings.empty.assign v (.symbol symbol) := by
            simpa using hout.1
          subst out
          simp [HEBindingSatisfied, HEAtomEquationSatisfied, Bindings.empty,
            Bindings.assign, Bindings.isBound, Bindings.lookup,
            encodeModelAtom, applyClassSolution]
      | var w =>
          simp [matchAtoms, getMetaType, Atom.variableType] at hout
          have houtEq : out = Bindings.empty.addEquality v w := by
            simpa using hout.1
          subst out
          simp [HEBindingSatisfied, HEAtomEquationSatisfied, Bindings.empty,
            Bindings.addEquality, encodeModelAtom, applyClassSolution]
      | grounded ground =>
          simp [matchAtoms, getMetaType, Atom.variableType,
            Atom.groundedType] at hout
          have houtAssign : out = Bindings.empty.assign v (.grounded ground) := by
            simpa using hout.1
          subst out
          simp [HEBindingSatisfied, HEAtomEquationSatisfied, Bindings.empty,
            Bindings.assign, Bindings.isBound, Bindings.lookup,
            encodeModelAtom, applyClassSolution]
      | expression atoms =>
          simp [matchAtoms, getMetaType, Atom.variableType,
            Atom.expressionType] at hout
          have houtAssign : out = Bindings.empty.assign v (.expression atoms) := by
            simpa using hout.1
          subst out
          simp [HEBindingSatisfied, HEAtomEquationSatisfied, Bindings.empty,
            Bindings.assign, Bindings.isBound, Bindings.lookup,
            encodeModelAtom, applyClassSolution]
  | grounded leftGround =>
      cases right with
      | symbol symbol =>
          simp [matchAtoms, getMetaType, Atom.symbolType,
            Atom.groundedType] at hout
      | var v =>
          simp [matchAtoms, getMetaType, Atom.variableType,
            Atom.groundedType] at hout
          have houtAssign : out = Bindings.empty.assign v (.grounded leftGround) := by
            simpa using hout.1
          subst out
          simp [HEBindingSatisfied, HEAtomEquationSatisfied, Bindings.empty,
            Bindings.assign, Bindings.isBound, Bindings.lookup,
            encodeModelAtom, applyClassSolution, eq_comm]
      | grounded rightGround =>
          by_cases heq : leftGround = rightGround
          · subst rightGround
            simp [matchAtoms, getMetaType, Atom.groundedType] at hout
            have houtEmpty : out = Bindings.empty := by simpa using hout.1
            subst out
            simp [HEBindingSatisfied, HEAtomEquationSatisfied,
              Bindings.empty, encodeModelAtom, applyClassSolution]
          · simp [matchAtoms, getMetaType, Atom.groundedType, heq] at hout
      | expression atoms =>
          simp [matchAtoms, getMetaType, Atom.expressionType,
            Atom.groundedType] at hout
  | expression lefts =>
      cases right with
      | symbol symbol =>
          simp [matchAtoms, getMetaType, Atom.symbolType,
            Atom.expressionType] at hout
      | var v =>
          simp [matchAtoms, getMetaType, Atom.variableType,
            Atom.expressionType] at hout
          have houtAssign : out = Bindings.empty.assign v (.expression lefts) := by
            simpa using hout.1
          subst out
          simp [HEBindingSatisfied, HEAtomEquationSatisfied, Bindings.empty,
            Bindings.assign, Bindings.isBound, Bindings.lookup,
            encodeModelAtom, applyClassSolution, eq_comm]
      | grounded ground =>
          simp [matchAtoms, getMetaType, Atom.expressionType,
            Atom.groundedType] at hout
      | expression rights =>
          by_cases hlength : lefts.length = rights.length
          · simp [matchAtoms, getMetaType, Atom.expressionType, hlength] at hout
            obtain ⟨hlist, _hloop⟩ := hout
            obtain ⟨seed, hseed, htheory⟩ := ih.listTheory hlist
            have hseedEmpty : seed = Bindings.empty := by simpa using hseed
            subst seed
            intro valuation
            rw [htheory]
            have hempty : HEBindingSatisfied valuation Bindings.empty := by
              simp [HEBindingSatisfied, Bindings.empty]
            rw [heAtomListEquations_iff_expressionEquation valuation hlength]
            simp [hempty]
          · simp [matchAtoms, getMetaType, Atom.expressionType,
              hlength] at hout

/-- Every successful HE matcher/merge result presents exactly the conjunction
of the equations consumed along that execution. -/
theorem heSolutionTheoryPack (fuel : Nat) : HESolutionTheoryPack fuel := by
  induction fuel with
  | zero => exact heSolutionTheoryPack_zero
  | succ fuel ih =>
      simpa [Nat.succ_eq_add_one] using
        (HESolutionTheoryPack.mk
          (fun _ => heMatchTheory_succ ih ‹_›)
          (fun _ => heListTheory_succ ih ‹_›)
          (fun _ => heMergeTheory_succ ih ‹_›)
          (fun _ => heAddValueTheory_succ ih ‹_›)
          (fun _ => heAddEqualityTheory_succ ih ‹_›))

theorem heMatchAtoms_solution_iff
    (valuation : String → Metta.Atom)
    {left right : Atom} {out : Bindings} {fuel : Nat}
    (hout : out ∈ matchAtoms left right fuel) :
    HEBindingSatisfied valuation out ↔
      HEAtomEquationSatisfied valuation left right :=
  (heSolutionTheoryPack fuel).matchTheory hout valuation

theorem heMergeBindings_solution_iff
    (valuation : String → Metta.Atom)
    {left right out : Bindings} {fuel : Nat}
    (hout : out ∈ mergeBindings left right fuel) :
    HEBindingSatisfied valuation out ↔
      HEBindingSatisfied valuation left ∧
        HEBindingSatisfied valuation right :=
  (heSolutionTheoryPack fuel).mergeTheory hout valuation

theorem heAddVarBinding_solution_iff
    (valuation : String → Metta.Atom)
    {b : Bindings} {v : String} {value : Atom} {out : Bindings} {fuel : Nat}
    (hout : out ∈ addVarBinding b v value fuel) :
    HEBindingSatisfied valuation out ↔
      HEBindingSatisfied valuation b ∧
        valuation v =
          applyClassSolution valuation (encodeModelAtom value) :=
  (heSolutionTheoryPack fuel).addValueTheory hout valuation

theorem heAddVarEquality_solution_iff
    (valuation : String → Metta.Atom)
    {b : Bindings} {left right : String} {out : Bindings} {fuel : Nat}
    (hout : out ∈ addVarEquality b left right fuel) :
    HEBindingSatisfied valuation out ↔
      HEBindingSatisfied valuation b ∧
        valuation left = valuation right :=
  (heSolutionTheoryPack fuel).addEqualityTheory hout valuation

/-- Paired successful value insertions preserve cross-engine solution theory.
No equality of intermediate matchers, substitutions, or representatives is
required. -/
theorem addVarBinding_solutionTheory_of_successes
    {b heOut : Bindings} {lb leaOut : Metta.Bindings}
    {v : String} {value : Atom} {fuel : Nat}
    (hbase : LeaBindingSolutionTheoryEquiv b lb)
    (hlbNoFloat : LeaBindingsNoFloat lb)
    (hhe : heOut ∈ addVarBinding b v value fuel)
    (hlea : leaOut ∈
      Metta.Bindings.addVarBinding lb v (encodeModelAtom value)) :
    LeaBindingSolutionTheoryEquiv heOut leaOut := by
  intro valuation
  rw [heAddVarBinding_solution_iff valuation hhe,
    hbase valuation,
    leaAddVarBinding_solution_iff valuation hlbNoFloat
      (encodeModelAtom_noFloat value) hlea]

/-- Paired successful equality insertions preserve cross-engine solution
theory independently of edge orientation. -/
theorem addVarEquality_solutionTheory_of_successes
    {b heOut : Bindings} {lb leaOut : Metta.Bindings}
    {left right : String} {fuel : Nat}
    (hbase : LeaBindingSolutionTheoryEquiv b lb)
    (hlbNoFloat : LeaBindingsNoFloat lb)
    (hhe : heOut ∈ addVarEquality b left right fuel)
    (hlea : leaOut ∈ Metta.Bindings.addVarEquality lb left right) :
    LeaBindingSolutionTheoryEquiv heOut leaOut := by
  intro valuation
  rw [heAddVarEquality_solution_iff valuation hhe,
    hbase valuation,
    leaAddVarEquality_solution_iff valuation hlbNoFloat hlea]

/-- Paired successful recursive merges preserve complete solution theory. This
is the representation-independent merge invariant: each side denotes the
conjunction of its two inputs, regardless of the solve order used internally. -/
theorem mergeBindings_solutionTheory_of_successes
    {heLeft heRight heOut : Bindings}
    {leaLeft leaRight leaOut : Metta.Bindings} {fuel : Nat}
    (hleft : LeaBindingSolutionTheoryEquiv heLeft leaLeft)
    (hright : LeaBindingSolutionTheoryEquiv heRight leaRight)
    (hleaLeftNoFloat : LeaBindingsNoFloat leaLeft)
    (hleaRightNoFloat : LeaBindingsNoFloat leaRight)
    (hhe : heOut ∈ mergeBindings heLeft heRight fuel)
    (hlea : leaOut ∈ Metta.Bindings.merge leaLeft leaRight) :
    LeaBindingSolutionTheoryEquiv heOut leaOut := by
  intro valuation
  rw [heMergeBindings_solution_iff valuation hhe,
    hleft valuation, hright valuation,
    leaMerge_solution_iff valuation
      hleaLeftNoFloat hleaRightNoFloat hlea]

/-- Paired successful recursive matcher outputs have the same complete
solution theory.  The executable call orientations are intentionally opposite:
HE receives query then pattern, while LeaTTa receives pattern then query. -/
theorem matchAtoms_solutionTheory_of_successes
    {query pattern : Atom} {heOut : Bindings}
    {leaOut : Metta.Bindings} {fuel : Nat}
    (hhe : heOut ∈ matchAtoms query pattern fuel)
    (hlea : leaOut ∈ Metta.matchAtoms
      (encodeModelAtom pattern) (encodeModelAtom query)) :
    LeaBindingSolutionTheoryEquiv heOut leaOut := by
  intro valuation
  rw [heMatchAtoms_solution_iff valuation hhe,
    leaMatchAtoms_solution_iff valuation
      (encodeModelAtom_noFloat pattern)
      (encodeModelAtom_noFloat query) hlea]
  simp [HEAtomEquationSatisfied, MettaEquationSatisfied, eq_comm]

/-- If an HE operation and repaired LeaTTa whole-system reconciliation consume
the same equations, their successful outputs have the same complete solution
theory.  This is deliberately independent of returned MGU shape and relation
order. -/
theorem rebuildBindingsFromUnifier_solutionTheory_of_heTheory
    {b heOut : Bindings} {lb : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hbase : LeaBindingSolutionTheoryEquiv b lb)
    (hlbNoFloat : LeaBindingsNoFloat lb)
    (hextraNoFloat : ∀ equation ∈ extra,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hreconcile :
      wholeBindingReconciliation lb extra = some result)
    (hheTheory : ∀ valuation,
      HEBindingSatisfied valuation heOut ↔
        HEBindingSatisfied valuation b ∧
          MettaEquationsSatisfied valuation extra) :
    LeaBindingSolutionTheoryEquiv heOut
      (rebuildBindingsFromUnifier lb result) := by
  intro valuation
  rw [hheTheory valuation, hbase valuation,
    rebuildBindingsFromUnifier_solution_iff valuation
      hlbNoFloat hextraNoFloat hreconcile]

/-- The executable alias-restoring rebuild has the same cross-engine solution
theory as its normalized core.  This is the runtime-shaped reconciliation
interface used by recursive matcher and merge transport. -/
theorem rebuildFromReconciliation_solutionTheory_of_heTheory
    {b heOut : Bindings} {source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hbase : LeaBindingSolutionTheoryEquiv b source)
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hextraNoFloat : ∀ equation ∈ extra,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hreconcile :
      wholeBindingReconciliation source extra = some result)
    (hheTheory : ∀ valuation,
      HEBindingSatisfied valuation heOut ↔
        HEBindingSatisfied valuation b ∧
          MettaEquationsSatisfied valuation extra) :
    LeaBindingSolutionTheoryEquiv heOut
      (Metta.Bindings.rebuildFromReconciliation
        source source extra result) := by
  intro valuation
  rw [rebuildFromReconciliation_solution_iff valuation
      hsourceNoFloat hextraNoFloat hreconcile,
    hheTheory valuation, hbase valuation,
    rebuildBindingsFromUnifier_solution_iff valuation
      hsourceNoFloat hextraNoFloat hreconcile]

/-- Quotient-level reconciliation interface: once an HE result is shown to
carry the candidate-plus-trace equality closure, the already-proved equation
theory theorem upgrades it to the full compositional binding invariant.  This
keeps the remaining matcher proof focused on class connectivity rather than
substitution presentation. -/
theorem rebuildFromReconciliation_solutionEquiv_of_heTheory_and_classes
    {b heOut : Bindings} {source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hbase : LeaBindingSolutionTheoryEquiv b source)
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hextraNoFloat : ∀ equation ∈ extra,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hreconcile : wholeBindingReconciliation source extra = some result)
    (hheTheory : ∀ valuation,
      HEBindingSatisfied valuation heOut ↔
        HEBindingSatisfied valuation b ∧
          MettaEquationsSatisfied valuation extra)
    (hclasses : ∀ start finish,
      finish ∈ heOut.eqClass start ↔
        (EqualityClosure.edgeGraph
          (leaEqualityEdges source ++
            Metta.Bindings.reconciliationAliases source extra result)).Reachable
          start finish) :
    LeaBindingSolutionEquiv heOut
      (Metta.Bindings.rebuildFromReconciliation
        source source extra result) := by
  refine ⟨?_, rebuildFromReconciliation_solutionTheory_of_heTheory
    hbase hsourceNoFloat hextraNoFloat hreconcile hheTheory⟩
  intro start finish
  rw [hclasses start finish,
    ← rebuildFromReconciliation_class_iff hreconcile]

/-- Structural interface between an HE output and the non-variable entries of
a repaired-LeaTTa whole-system substitution.  It is deliberately indexed by
the HE output closure: substitution keys and variables inside stored terms may
move within a connected class, but not across classes. -/
def LeaSubstClassValueRel (heOut : Bindings) (result : Metta.Subst) : Prop :=
  (∀ key value, (key, value) ∈ heOut.assignments →
    ∃ leaKey leaValue,
      (leaKey, leaValue) ∈ result ∧
        (∀ target, leaValue ≠ .var target) ∧
          leaKey ∈ heOut.eqClass key ∧
            HELeaAtomClassRel heOut value leaValue) ∧
  (∀ leaKey leaValue, (leaKey, leaValue) ∈ result →
    (∀ target, leaValue ≠ .var target) →
      ∃ key value,
        (key, value) ∈ heOut.assignments ∧
          leaKey ∈ heOut.eqClass key ∧
            HELeaAtomClassRel heOut value leaValue)

/-- Against a raw `ofSubst` presentation, the general class-value relation
is exactly substitution provenance.  This isolates the value-bearing part of
the structural invariant: variable entries and their equality closure are
deliberately absent from both sides. -/
theorem leaClassValueRelEquiv_ofSubst_iff_substClassValueRel
    {heOut : Bindings} {result : Metta.Subst} :
    LeaClassValueRelEquiv heOut (Metta.Bindings.ofSubst result) ↔
      LeaSubstClassValueRel heOut result := by
  constructor
  · intro h
    constructor
    · intro key value hvalue
      obtain ⟨leaKey, leaValue, hleaValue, hclass, hatom⟩ :=
        h.1 key value hvalue
      obtain ⟨hresult, hnonvar⟩ := val_mem_ofSubst_iff.mp hleaValue
      exact ⟨leaKey, leaValue, hresult, hnonvar, hclass, hatom⟩
    · intro leaKey leaValue hresult hnonvar
      obtain ⟨key, value, hvalue, hclass, hatom⟩ :=
        h.2 leaKey leaValue (val_mem_ofSubst_iff.mpr ⟨hresult, hnonvar⟩)
      exact ⟨key, value, hvalue, hclass, hatom⟩
  · intro h
    constructor
    · intro key value hvalue
      obtain ⟨leaKey, leaValue, hresult, hnonvar, hclass, hatom⟩ :=
        h.1 key value hvalue
      exact ⟨leaKey, leaValue,
        val_mem_ofSubst_iff.mpr ⟨hresult, hnonvar⟩, hclass, hatom⟩
    · intro leaKey leaValue hleaValue
      obtain ⟨hresult, hnonvar⟩ := val_mem_ofSubst_iff.mp hleaValue
      exact h.2 leaKey leaValue hresult hnonvar

/-- The same class-indexed provenance contract stated against a syntactic
elimination trace.  This is the induction form used to compare LeaTTa's
Robinson steps with HE's sequential match/merge derivation. -/
def LeaEliminationTraceClassValueRel
    (heOut : Bindings) (trace : List (String × Metta.Atom)) : Prop :=
  (∀ key value, (key, value) ∈ heOut.assignments →
    ∃ leaKey leaValue,
      (leaKey, leaValue) ∈ trace ∧
        (∀ target, leaValue ≠ .var target) ∧
          leaKey ∈ heOut.eqClass key ∧
            HELeaAtomClassRel heOut value leaValue) ∧
  (∀ leaKey leaValue, (leaKey, leaValue) ∈ trace →
    (∀ target, leaValue ≠ .var target) →
      ∃ key value,
        (key, value) ∈ heOut.assignments ∧
          leaKey ∈ heOut.eqClass key ∧
            HELeaAtomClassRel heOut value leaValue)

/-- Successful whole-system reconciliation identifies substitution provenance
with elimination-trace provenance exactly.  The remaining cross-engine proof
may therefore induct over syntactic elimination rather than reason about an
opaque normalized MGU. -/
theorem leaSubstClassValueRel_iff_eliminationTrace
    {heOut : Bindings} {bindings : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hreconcile : wholeBindingReconciliation bindings extra = some result) :
    LeaSubstClassValueRel heOut result ↔
      LeaEliminationTraceClassValueRel heOut
        (unificationEliminationTrace
          (Metta.Bindings.equationFuel
            (Metta.Bindings.equations bindings ++ extra))
          (Metta.Bindings.equations bindings ++ extra)) := by
  unfold LeaSubstClassValueRel LeaEliminationTraceClassValueRel
  simp_rw [wholeBindingReconciliation_result_mem_iff_eliminationTrace
    hreconcile]

/-- Alias restoration and the candidate skeleton are invisible to raw value
provenance.  Consequently the strengthened value invariant for a rebuilt
binding is exactly `LeaSubstClassValueRel` against the successful normalized
substitution. -/
theorem leaClassValueRelEquiv_rebuildFromReconciliation_iff
    {heOut : Bindings} {candidate source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst} :
    LeaClassValueRelEquiv heOut
        (Metta.Bindings.rebuildFromReconciliation
          candidate source extra result) ↔
      LeaSubstClassValueRel heOut result := by
  constructor
  · intro hvalues
    constructor
    · intro key value hmem
      obtain ⟨leaKey, leaValue, hleaValue, hclass, hatom⟩ :=
        hvalues.1 key value hmem
      obtain ⟨hsubst, hnonvar⟩ :=
        val_mem_rebuildFromReconciliation_iff.mp hleaValue
      exact ⟨leaKey, leaValue, hsubst, hnonvar, hclass, hatom⟩
    · intro leaKey leaValue hsubst hnonvar
      exact hvalues.2 leaKey leaValue
        (val_mem_rebuildFromReconciliation_iff.mpr ⟨hsubst, hnonvar⟩)
  · intro hsubst
    constructor
    · intro key value hmem
      obtain ⟨leaKey, leaValue, hmemSubst, hnonvar, hclass, hatom⟩ :=
        hsubst.1 key value hmem
      exact ⟨leaKey, leaValue,
        val_mem_rebuildFromReconciliation_iff.mpr ⟨hmemSubst, hnonvar⟩,
        hclass, hatom⟩
    · intro leaKey leaValue hmem
      obtain ⟨hmemSubst, hnonvar⟩ :=
        val_mem_rebuildFromReconciliation_iff.mp hmem
      exact hsubst.2 leaKey leaValue hmemSubst hnonvar

/-- Strengthened whole-reconciliation interface.  Complete equation theory,
exact class closure, and the single structural substitution-provenance premise
assemble the compositional invariant without comparing MGU lists or equality
spanning trees. -/
theorem rebuildFromReconciliation_congruence_of_heTheory_classes_and_values
    {b heOut : Bindings} {source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hbase : LeaBindingCongruence b source)
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hextraNoFloat : ∀ equation ∈ extra,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hreconcile : wholeBindingReconciliation source extra = some result)
    (hheTheory : ∀ valuation,
      HEBindingSatisfied valuation heOut ↔
        HEBindingSatisfied valuation b ∧
          MettaEquationsSatisfied valuation extra)
    (hclasses : ∀ start finish,
      finish ∈ heOut.eqClass start ↔
        (EqualityClosure.edgeGraph
          (leaEqualityEdges source ++
            Metta.Bindings.reconciliationAliases source extra result)).Reachable
          start finish)
    (hvalues : LeaSubstClassValueRel heOut result) :
    LeaBindingCongruence heOut
      (Metta.Bindings.rebuildFromReconciliation
        source source extra result) := by
  refine ⟨rebuildFromReconciliation_solutionEquiv_of_heTheory_and_classes
      hbase.semantic.solutions hsourceNoFloat hextraNoFloat hreconcile
        hheTheory hclasses, ?_⟩
  exact leaClassValueRelEquiv_rebuildFromReconciliation_iff.mpr hvalues

/-- Successful HE value insertion and repaired LeaTTa reconciliation agree on
all binding solutions, even when their unifiers choose different variable
representatives. -/
theorem rebuild_addVarBinding_solutionTheory
    {b heOut : Bindings} {lb : Metta.Bindings}
    {v : String} {value : Atom} {fuel : Nat} {result : Metta.Subst}
    (hbase : LeaBindingSolutionTheoryEquiv b lb)
    (hlbNoFloat : LeaBindingsNoFloat lb)
    (hhe : heOut ∈ addVarBinding b v value fuel)
    (hreconcile :
      wholeBindingReconciliation lb
        [(.var v, encodeModelAtom value)] = some result) :
    LeaBindingSolutionTheoryEquiv heOut
      (rebuildBindingsFromUnifier lb result) := by
  apply rebuildBindingsFromUnifier_solutionTheory_of_heTheory
    hbase hlbNoFloat (hreconcile := hreconcile)
  · intro equation hmem
    simp only [List.mem_singleton] at hmem
    subst equation
    exact ⟨by simp [MettaAtomNoFloat], encodeModelAtom_noFloat value⟩
  · intro valuation
    rw [heAddVarBinding_solution_iff valuation hhe]
    simp [MettaEquationsSatisfied, MettaEquationSatisfied,
      applyClassSolution]

/-- Successful HE alias insertion and repaired LeaTTa reconciliation agree on
all binding solutions, independently of equality-edge orientation. -/
theorem rebuild_addVarEquality_solutionTheory
    {b heOut : Bindings} {lb : Metta.Bindings}
    {left right : String} {fuel : Nat} {result : Metta.Subst}
    (hbase : LeaBindingSolutionTheoryEquiv b lb)
    (hlbNoFloat : LeaBindingsNoFloat lb)
    (hhe : heOut ∈ addVarEquality b left right fuel)
    (hreconcile :
      wholeBindingReconciliation lb
        [(.var left, .var right)] = some result) :
    LeaBindingSolutionTheoryEquiv heOut
      (rebuildBindingsFromUnifier
        (Metta.Bindings.addEqRaw lb left right) result) := by
  intro valuation
  rw [heAddVarEquality_solution_iff valuation hhe,
    hbase valuation,
    rebuildBindingsFromUnifier_addEq_solution_iff valuation
      hlbNoFloat hreconcile]

/-- Runtime-shaped value reconciliation, including certified alias
restoration, preserves complete cross-engine solution theory. -/
theorem rebuildReconciliation_addVarBinding_solutionTheory
    {b heOut : Bindings} {lb : Metta.Bindings}
    {v : String} {value : Atom} {fuel : Nat} {result : Metta.Subst}
    (hbase : LeaBindingSolutionTheoryEquiv b lb)
    (hlbNoFloat : LeaBindingsNoFloat lb)
    (hhe : heOut ∈ addVarBinding b v value fuel)
    (hreconcile :
      wholeBindingReconciliation lb
        [(.var v, encodeModelAtom value)] = some result) :
    LeaBindingSolutionTheoryEquiv heOut
      (Metta.Bindings.rebuildFromReconciliation lb lb
        [(.var v, encodeModelAtom value)] result) := by
  apply rebuildFromReconciliation_solutionTheory_of_heTheory
    hbase hlbNoFloat (hreconcile := hreconcile)
  · intro equation hmem
    simp only [List.mem_singleton] at hmem
    subst equation
    exact ⟨by simp [MettaAtomNoFloat], encodeModelAtom_noFloat value⟩
  · intro valuation
    rw [heAddVarBinding_solution_iff valuation hhe]
    simp [MettaEquationsSatisfied, MettaEquationSatisfied,
      applyClassSolution]

/-- Runtime-shaped equality reconciliation preserves complete cross-engine
solution theory while retaining the inserted equality edge in the candidate
skeleton. -/
theorem rebuildReconciliation_addVarEquality_solutionTheory
    {b heOut : Bindings} {lb : Metta.Bindings}
    {left right : String} {fuel : Nat} {result : Metta.Subst}
    (hbase : LeaBindingSolutionTheoryEquiv b lb)
    (hlbNoFloat : LeaBindingsNoFloat lb)
    (hhe : heOut ∈ addVarEquality b left right fuel)
    (hreconcile :
      wholeBindingReconciliation lb
        [(.var left, .var right)] = some result) :
    LeaBindingSolutionTheoryEquiv heOut
      (Metta.Bindings.rebuildFromReconciliation
        (Metta.Bindings.addEqRaw lb left right) lb
        [(.var left, .var right)] result) := by
  intro valuation
  rw [rebuildFromReconciliation_solution_iff valuation
      hlbNoFloat (by
        intro equation hmem
        simp only [List.mem_singleton] at hmem
        subst equation
        simp [MettaAtomNoFloat]) hreconcile,
    heAddVarEquality_solution_iff valuation hhe,
    hbase valuation,
    rebuildBindingsFromUnifier_addEq_solution_iff valuation
      hlbNoFloat hreconcile]

private theorem heLookup_eq_some_of_assignment_mem_nodup
    {assignments : List (String × Atom)}
    (hkeys : (assignments.map Prod.fst).Nodup)
    {x : String} {value : Atom} (hmem : (x, value) ∈ assignments) :
    List.lookup x assignments = some value := by
  induction assignments with
  | nil => cases hmem
  | cons binding rest ih =>
      rcases binding with ⟨key, stored⟩
      simp only [List.mem_cons, Prod.mk.injEq] at hmem
      have hkeysTail : (rest.map Prod.fst).Nodup := by
        simpa using (List.nodup_cons.mp hkeys).2
      rcases hmem with hhead | htail
      · rcases hhead with ⟨rfl, rfl⟩
        simp
      · have hkeyFresh : key ∉ rest.map Prod.fst := by
          simpa using (List.nodup_cons.mp hkeys).1
        have hx : x ≠ key := by
          intro h
          subst x
          apply hkeyFresh
          exact List.mem_map_of_mem htail
        have hbeq : (x == key) = false := by simp [hx]
        simpa [List.lookup_cons, hbeq] using ih hkeysTail htail

/-- Relation agreement and HE assignment-key uniqueness identify direct value
lookups exactly. Equality edges do not participate in either direct lookup. -/
theorem leaLookupVal_eq_map_lookup_of_transport
    {b : Bindings} {lb : Metta.Bindings}
    (htransport : LeaBindingTransport b lb)
    (hkeys : AssignmentsNodup b) (x : String) :
    Metta.Bindings.lookupVal lb x =
      Option.map encodeModelAtom (b.lookup x) := by
  cases hlea : Metta.Bindings.lookupVal lb x with
  | none =>
      cases hhe : b.lookup x with
      | none => rfl
      | some value =>
          have hmem : (x, value) ∈ b.assignments :=
            heAssignment_mem_of_lookup_eq_some (by
              simpa [Bindings.lookup] using hhe)
          have hleaMem :
              Metta.BindingRel.val x (encodeModelAtom value) ∈ lb :=
            (htransport.relations.values x (encodeModelAtom value)).2
              ⟨value, hmem, rfl⟩
          exact (no_leaValue_of_lookupVal_eq_none hlea
            (encodeModelAtom value) hleaMem).elim
  | some leaValue =>
      have hleaMem : Metta.BindingRel.val x leaValue ∈ lb :=
        leaValue_mem_of_lookupVal_eq_some hlea
      obtain ⟨heValue, hmem, rfl⟩ :=
        (htransport.relations.values x leaValue).1 hleaMem
      have hhe : b.lookup x = some heValue := by
        unfold Bindings.lookup
        exact heLookup_eq_some_of_assignment_mem_nodup hkeys hmem
      simp [hhe]

/-- Ordered-class and direct-lookup agreement identify every class value, in
the same canonical order, up to atom translation. -/
theorem leaClassValues_eq_map_of_transport
    {b : Bindings} {lb : Metta.Bindings}
    (htransport : LeaBindingTransport b lb)
    (hkeys : AssignmentsNodup b) (v : String) :
    Metta.Bindings.classValues lb v =
      (b.classValues v).map encodeModelAtom := by
  unfold Metta.Bindings.classValues Bindings.classValues
  rw [eqClassOrdered_eq_of_transport htransport.relations
    htransport.chronology v]
  induction b.eqClassOrdered v with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.filterMap_cons]
      rw [leaLookupVal_eq_map_lookup_of_transport htransport hkeys x]
      cases b.lookup x <;> simp [ih]

/-- Class-value emptiness is representation independent. This is the
order-free fact needed by both fresh merge branches. -/
theorem leaClassValues_eq_nil_of_transport
    {b : Bindings} {lb : Metta.Bindings}
    (htransport : LeaBindingTransport b lb) {v : String}
    (hvalues : b.classValues v = []) :
    Metta.Bindings.classValues lb v = [] := by
  unfold Metta.Bindings.classValues
  apply List.filterMap_eq_nil_iff.mpr
  intro x hxClass
  have hxHE : x ∈ b.eqClassOrdered v := by
    rw [← eqClassOrdered_eq_of_transport htransport.relations
      htransport.chronology v]
    exact hxClass
  have hlookup : b.lookup x = none := by
    unfold Bindings.classValues at hvalues
    exact List.filterMap_eq_nil_iff.mp hvalues x hxHE
  apply leaLookupVal_eq_none_of_no_value
  intro value hval
  obtain ⟨heValue, hmem, _⟩ :=
    (htransport.relations.values x value).mp hval
  exact assignment_not_mem_of_lookup_none hlookup heValue hmem

private theorem heClassValues_ne_nil_of_assignment_mem_of_class
    {b : Bindings} {v key : String} {value : Atom}
    (hassignment : (key, value) ∈ b.assignments)
    (hclass : key ∈ b.eqClass v) :
    b.classValues v ≠ [] := by
  intro hempty
  have hordered : key ∈ b.eqClassOrdered v :=
    EqualityClosure.mem_eqClassOrdered_iff.mpr hclass
  have hlookupNot : List.lookup key b.assignments ≠ none := by
    intro hlookup
    exact assignment_not_mem_of_lookup_none hlookup value hassignment
  cases hlookup : List.lookup key b.assignments with
  | none => exact hlookupNot hlookup
  | some stored =>
      have hstored : stored ∈ b.classValues v := by
        unfold Bindings.classValues
        exact List.mem_filterMap.mpr ⟨key, hordered, by
          simpa [Bindings.lookup] using hlookup⟩
      rw [hempty] at hstored
      simp at hstored

/-- Class-value emptiness follows from the strengthened invariant without any
ordered-class or representative agreement.  A LeaTTa value in the class would
map back to an HE assignment in the same connected component. -/
theorem leaClassValues_eq_nil_of_congruence
    {b : Bindings} {lb : Metta.Bindings}
    (h : LeaBindingCongruence b lb) {v : String}
    (hvalues : b.classValues v = []) :
    Metta.Bindings.classValues lb v = [] := by
  by_contra hnonempty
  cases hclassValues : Metta.Bindings.classValues lb v with
  | nil => exact (hnonempty hclassValues).elim
  | cons leaValue rest =>
    have hleaClassValue :
        leaValue ∈ Metta.Bindings.classValues lb v := by
      rw [hclassValues]
      simp
    unfold Metta.Bindings.classValues at hleaClassValue
    obtain ⟨leaKey, hleaOrdered, hleaLookup⟩ :=
      List.mem_filterMap.mp hleaClassValue
    have hleaBinding : Metta.BindingRel.val leaKey leaValue ∈ lb :=
      leaValue_mem_of_lookupVal_eq_some hleaLookup
    obtain ⟨key, value, hassignment, hkeyClass, _hatom⟩ :=
      h.classValues.2 leaKey leaValue hleaBinding
    have hvLeaKey : leaKey ∈ b.eqClass v :=
      (h.semantic.classes v leaKey).mpr
        (mem_leaEqClassOrdered_iff.mp hleaOrdered)
    have hvKey : key ∈ b.eqClass v := by
      rw [EqualityClosure.mem_eqClass_iff_reachable] at hvLeaKey hkeyClass ⊢
      exact hvLeaKey.trans hkeyClass.symm
    exact (heClassValues_ne_nil_of_assignment_mem_of_class
      hassignment hvKey) hvalues

/-- Nonempty HE class values also remain nonempty on the LeaTTa side.  This
uses only bidirectional raw-value provenance and equality-closure agreement;
the selected lookup value and class order may differ. -/
theorem leaClassValues_ne_nil_of_congruence
    {b : Bindings} {lb : Metta.Bindings}
    (h : LeaBindingCongruence b lb) {v : String}
    (hvalues : b.classValues v ≠ []) :
    Metta.Bindings.classValues lb v ≠ [] := by
  intro hleaEmpty
  cases hheClass : b.classValues v with
  | nil => exact hvalues hheClass
  | cons heValue rest =>
    have hheClassValue : heValue ∈ b.classValues v := by
      rw [hheClass]
      simp
    unfold Bindings.classValues at hheClassValue
    obtain ⟨key, hkeyOrdered, hheLookup⟩ :=
      List.mem_filterMap.mp hheClassValue
    have hassignment : (key, heValue) ∈ b.assignments :=
      heAssignment_mem_of_lookup_eq_some (by
        simpa [Bindings.lookup] using hheLookup)
    obtain ⟨leaKey, leaValue, hleaBinding, hleaKeyClass, _hatom⟩ :=
      h.classValues.1 key heValue hassignment
    have hvKey : key ∈ b.eqClass v :=
      EqualityClosure.mem_eqClassOrdered_iff.mp hkeyOrdered
    have hvLeaKey : leaKey ∈ b.eqClass v := by
      rw [EqualityClosure.mem_eqClass_iff_reachable] at hvKey hleaKeyClass ⊢
      exact hvKey.trans hleaKeyClass
    have hleaOrdered : leaKey ∈ Metta.Bindings.eqClassOrdered lb v :=
      mem_leaEqClassOrdered_iff.mpr
        ((h.semantic.classes v leaKey).mp hvLeaKey)
    have hlookupNot : Metta.Bindings.lookupVal lb leaKey ≠ none := by
      intro hlookup
      exact no_leaValue_of_lookupVal_eq_none
        hlookup leaValue hleaBinding
    cases hleaLookup : Metta.Bindings.lookupVal lb leaKey with
    | none => exact hlookupNot hleaLookup
    | some stored =>
        have hstored : stored ∈ Metta.Bindings.classValues lb v := by
          unfold Metta.Bindings.classValues
          exact List.mem_filterMap.mpr ⟨leaKey, hleaOrdered, hleaLookup⟩
        rw [hleaEmpty] at hstored
        simp at hstored

/-- The strengthened invariant identifies class-value emptiness exactly while
remaining agnostic about class order, multiplicity, and representative. -/
theorem leaClassValues_eq_nil_iff_of_congruence
    {b : Bindings} {lb : Metta.Bindings}
    (h : LeaBindingCongruence b lb) (v : String) :
    Metta.Bindings.classValues lb v = [] ↔ b.classValues v = [] := by
  constructor
  · intro hlea
    by_contra hhe
    exact (leaClassValues_ne_nil_of_congruence h hhe) hlea
  · exact leaClassValues_eq_nil_of_congruence h

/-- Fresh HE value insertion transports through the strengthened invariant
using only class-value emptiness, with direct lookup emptiness derived on both
sides. -/
theorem LeaBindingCongruence.addVarBinding_fresh_of_heClass
    {b : Bindings} {lb : Metta.Bindings} {v : String} {value : Atom}
    (h : LeaBindingCongruence b lb)
    (hnonvar : DeclMatchSpec.Atom.isVarB value = false)
    (hclass : b.classValues v = []) :
    ∃ lb',
      lb' ∈ Metta.Bindings.addVarBinding lb v (encodeModelAtom value) ∧
        LeaBindingCongruence (b.assign v value) lb' := by
  have hleaClass : Metta.Bindings.classValues lb v = [] :=
    leaClassValues_eq_nil_of_congruence h hclass
  exact h.addVarBinding_fresh
    (heLookup_eq_none_of_classValues_eq_nil hclass)
    (leaLookupVal_eq_none_of_classValues_eq_nil hleaClass)
    hnonvar hleaClass

/-- Valueless class joining transports through the strengthened invariant;
only connected-class emptiness is used, not class order. -/
theorem LeaBindingCongruence.addVarEquality_valueless_of_heClass
    {b : Bindings} {lb : Metta.Bindings}
    {queryVar patternVar : String}
    (h : LeaBindingCongruence b lb)
    (hne : queryVar ≠ patternVar)
    (hclass :
      (b.addEquality queryVar patternVar).classValues queryVar = []) :
    ∃ lb',
      lb' ∈ Metta.Bindings.addVarEquality lb patternVar queryVar ∧
        LeaBindingCongruence
          (b.addEquality queryVar patternVar) lb' := by
  let candidate := Metta.Bindings.addEqRaw lb patternVar queryVar
  have hcand :
      LeaBindingCongruence
        (b.addEquality queryVar patternVar) candidate :=
    h.addEqRaw hne
  have hreach :
      (EqualityClosure.edgeGraph
        (b.addEquality queryVar patternVar).equalities).Reachable
          queryVar patternVar := by
    apply SimpleGraph.Adj.reachable
    exact ⟨hne, Or.inl (by simp [Bindings.addEquality])⟩
  have hclassPattern :
      (b.addEquality queryVar patternVar).classValues patternVar = [] := by
    rw [← EqualityClosure.classValues_eq_of_reachable hreach]
    exact hclass
  have hleaClass : Metta.Bindings.classValues candidate patternVar = [] :=
    leaClassValues_eq_nil_of_congruence hcand hclassPattern
  exact h.addVarEquality_valueless hne hleaClass

/-- Fresh HE value insertion transports through LeaTTa without an external
class premise: emptiness follows from the binding invariant. -/
theorem LeaBindingTransport.addVarBinding_fresh_of_heClass
    {b : Bindings} {lb : Metta.Bindings} {v : String} {value : Atom}
    (htransport : LeaBindingTransport b lb)
    (hlookup : b.lookup v = none)
    (hnonvar : DeclMatchSpec.Atom.isVarB value = false)
    (hclass : b.classValues v = []) :
    ∃ lb',
      lb' ∈ Metta.Bindings.addVarBinding lb v (encodeModelAtom value) ∧
        LeaBindingTransport (b.assign v value) lb' :=
  htransport.addVarBinding_fresh hlookup hnonvar
    (leaClassValues_eq_nil_of_transport htransport hclass)

/-- Valueless HE class joining transports through LeaTTa with the joined-class
emptiness derived after the raw alias is added on both sides. -/
theorem LeaBindingTransport.addVarEquality_valueless_of_heClass
    {b : Bindings} {lb : Metta.Bindings} {queryVar patternVar : String}
    (htransport : LeaBindingTransport b lb)
    (hne : queryVar ≠ patternVar)
    (hnot : Metta.BindingRel.eq patternVar queryVar ∉ lb)
    (hclass : (b.addEquality queryVar patternVar).classValues queryVar = []) :
    ∃ lb',
      lb' ∈ Metta.Bindings.addVarEquality lb patternVar queryVar ∧
        LeaBindingTransport (b.addEquality queryVar patternVar) lb' := by
  let candidate := Metta.Bindings.addEqRaw lb patternVar queryVar
  have hcand : LeaBindingTransport (b.addEquality queryVar patternVar) candidate :=
    htransport.addEqRaw hne hnot
  have hreach :
      (EqualityClosure.edgeGraph
        (b.addEquality queryVar patternVar).equalities).Reachable
          queryVar patternVar := by
    apply SimpleGraph.Adj.reachable
    exact ⟨hne, Or.inl (by simp [Bindings.addEquality])⟩
  have hclassPattern :
      (b.addEquality queryVar patternVar).classValues patternVar = [] := by
    rw [← EqualityClosure.classValues_eq_of_reachable hreach]
    exact hclass
  have hlea : Metta.Bindings.classValues candidate patternVar = [] := by
    exact leaClassValues_eq_nil_of_transport hcand hclassPattern
  exact htransport.addVarEquality_valueless hne hnot hlea

private def seededOverwriteLeaBase : Metta.Bindings :=
  [Metta.BindingRel.val "p" (.expr [.sym "f", .var "a"]),
    Metta.BindingRel.val "a" (.sym "old")]

private def seededOverwriteHEBase : Bindings :=
  ⟨[("p", .expression [.symbol "f", .var "a"]),
    ("a", .symbol "old")], []⟩

private def seededOverwriteHERight : Bindings :=
  ⟨[("p", .expression [.symbol "f", .symbol "new"])], []⟩

/-- NEGATIVE REPAIR ORACLE: repaired LeaTTa and faithful HE both reject the
secondary conflict instead of overwriting the seeded value `a = old`. -/
theorem seededOverwrite_reconciliation_rejected :
    Metta.Bindings.addVarBinding seededOverwriteLeaBase "p"
          (.expr [.sym "f", .sym "new"]) = [] ∧
      mergeBindings seededOverwriteHEBase seededOverwriteHERight 30 = [] := by
  constructor
  · simp (config := { maxSteps := 1000000 })
      [seededOverwriteLeaBase,
        Metta.Bindings.addVarBinding, Metta.Bindings.unifyValues,
        Metta.Bindings.reconcileAll, Metta.Bindings.equations,
        Metta.Bindings.relationEquation, Metta.Bindings.equationFuel,
        Metta.Bindings.classValues, Metta.Bindings.eqClassOrdered,
        Metta.Bindings.eqVarsInOrder, Metta.Bindings.eqClass,
        Metta.Bindings.eqClassAux, Metta.Bindings.eqStep,
        Metta.Bindings.lookupVal, Metta.Unify.unifyRounds,
        Metta.Unify.decomposeAll, Metta.Unify.decomposeEq,
        Metta.Unify.decomposeList, Metta.Subst.apply,
        Metta.Subst.lookup, Metta.Subst.extend, Metta.Subst.erase,
        Metta.Atom.size]
  · decide

/-- NEGATIVE REPAIR ORACLE: reconciling the complete binding equation system
rejects the seeded overwrite instead of forgetting `a = old`. -/
theorem seededOverwrite_whole_reconciliation_rejects :
    wholeBindingReconciliation seededOverwriteLeaBase
      [(.var "p", .expr [.sym "f", .sym "new"])] = none := by
  simp (config := { maxSteps := 1000000 })
    [seededOverwriteLeaBase, wholeBindingReconciliation,
      Metta.Bindings.reconcileAll, Metta.Bindings.equations,
      Metta.Bindings.relationEquation, Metta.Bindings.equationFuel,
      Metta.Unify.unifyRounds,
      Metta.Unify.decomposeAll, Metta.Unify.decomposeEq,
      Metta.Unify.decomposeList, Metta.Subst.occurs,
      Metta.Subst.apply, Metta.Subst.lookup, Metta.Atom.size]

/-- POSITIVE REPAIR ORACLE: complete-system reconciliation still derives the
nonlinear alias `a = b` while retaining the original assignment for `p`. -/
theorem nonlinear_whole_reconciliation_succeeds :
    wholeBindingReconciliation
        [Metta.BindingRel.val "p" (.expr [.sym "f", .var "a"])]
        [(.var "p", .expr [.sym "f", .var "b"])] =
      some [("a", .var "b"),
        ("p", .expr [.sym "f", .var "a"])] := by
  simp (config := { maxSteps := 1000000 })
    [wholeBindingReconciliation, Metta.Bindings.reconcileAll,
      Metta.Bindings.equations, Metta.Bindings.relationEquation,
      Metta.Bindings.equationFuel,
      Metta.Unify.unifyRounds, Metta.Unify.decomposeAll,
      Metta.Unify.decomposeEq, Metta.Unify.decomposeList,
      Metta.Subst.occurs, Metta.Subst.apply, Metta.Subst.lookup,
      Metta.Subst.extend, Metta.Subst.erase, Metta.Atom.size]

private def nonlinearValuePattern : Atom :=
  .expression [.symbol "g", .var "p", .var "p"]

private def nonlinearValueQuery : Atom :=
  .expression
    [.symbol "g", .expression [.symbol "f", .var "a"],
      .expression [.symbol "f", .var "b"]]

private def nonlinearValueHEBindings : Bindings :=
  ⟨[("p", .expression [.symbol "f", .var "a"])], [("a", "b")]⟩

private def nonlinearValueLeaBindings : Metta.Bindings :=
  [Metta.BindingRel.eq "a" "b",
    Metta.BindingRel.val "p" (.expr [.sym "f", .var "a"])]

/-- A successful nonlinear value reconciliation in both engines. The equality
edge has the same undirected meaning, but the two resolver conventions choose
different concrete members of its class. -/
theorem nonlinearValue_reconciliation_match_oracles :
    nonlinearValueHEBindings ∈
        matchAtoms nonlinearValueQuery nonlinearValuePattern 30 ∧
      nonlinearValueLeaBindings ∈
        Metta.matchAtoms (encodeModelAtom nonlinearValuePattern)
          (encodeModelAtom nonlinearValueQuery) := by
  constructor
  · decide
  · have hloop : Metta.Bindings.hasLoop
        [Metta.BindingRel.eq "a" "b",
          Metta.BindingRel.val "p" (.expr [.sym "f", .var "a"])] = false := by
      apply Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.hasLoop_false_of_resolveAtomAux_some
      · rfl
      · intro x hx
        have hvars : Metta.Bindings.vars
            [Metta.BindingRel.eq "a" "b",
              Metta.BindingRel.val "p" (.expr [.sym "f", .var "a"])] =
            ["a", "b", "p"] := by
          simp [Metta.Bindings.vars, Metta.Atom.vars, List.eraseDups_cons]
        rw [hvars] at hx
        simp at hx
        have hfuel (v : String) : Metta.Bindings.resolutionFuel
            [Metta.BindingRel.eq "a" "b",
              Metta.BindingRel.val "p" (.expr [.sym "f", .var "a"])]
            (.var v) = 7 := by
          simp [Metta.Bindings.resolutionFuel,
            Metta.Bindings.relationResolutionFuel, Metta.Atom.size]
        rcases hx with rfl | rfl | rfl
        · exact ⟨.var "b", by rw [hfuel]; rfl⟩
        · exact ⟨.var "b", by rw [hfuel]; rfl⟩
        · exact ⟨.expr [.sym "f", .var "b"], by rw [hfuel]; rfl⟩
    have hpaLoop : Metta.Bindings.hasLoop
        [Metta.BindingRel.val "p" (.expr [.sym "f", .var "a"])] = false :=
      Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _ (by simp [Metta.Atom.vars])
    have hpbLoop : Metta.Bindings.hasLoop
        [Metta.BindingRel.val "p" (.expr [.sym "f", .var "b"])] = false :=
      Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _ (by simp [Metta.Atom.vars])
    simp (config := { maxSteps := 1000000 })
      [nonlinearValuePattern, nonlinearValueQuery,
        nonlinearValueLeaBindings, encodeModelAtom, encodeModelAtoms,
        hloop, hpaLoop, hpbLoop,
        Metta.matchAtoms, Metta.matchAtomsWith, Metta.matchAll,
        Metta.Bindings.merge, Metta.Bindings.mergeOne,
        Metta.Bindings.addVarBinding, Metta.Bindings.unifyValues,
        Metta.Bindings.reconcileAll, Metta.Bindings.equations,
        Metta.Bindings.relationEquation, Metta.Bindings.equationFuel,
        Metta.Bindings.rebuildFromReconciliation,
        Metta.Bindings.reconciliationAliases,
        Metta.Bindings.restoreAlias,
        Metta.Bindings.rebuildFromSubst, Metta.Bindings.equalitySkeleton,
        Metta.Bindings.ofSubst,
        Metta.Bindings.classValues, Metta.Bindings.eqClassOrdered,
        Metta.Bindings.eqVarsInOrder, Metta.Bindings.eqClass,
        Metta.Bindings.eqClassAux, Metta.Bindings.eqStep,
        Metta.Bindings.lookupVal, Metta.Bindings.addValRaw,
        Metta.Bindings.removeVal,
        Metta.Unify.aliasTrace, Metta.Unify.aliasConstraints,
        Metta.Unify.unifyRounds, Metta.Unify.decomposeAll,
        Metta.Unify.decomposeEq, Metta.Unify.decomposeList,
        Metta.Subst.occurs, Metta.Subst.apply, Metta.Subst.lookup,
        Metta.Subst.extend, Metta.Subst.erase, List.filter_cons,
        BEq.beq, Metta.Atom.size]

theorem nonlinearValue_reconciliation_relations :
    LeaBindingRelEquiv nonlinearValueHEBindings nonlinearValueLeaBindings := by
  constructor
  · intro v value
    simp [nonlinearValueHEBindings, nonlinearValueLeaBindings, encodeModelAtom]
  · intro x y
    simp only [nonlinearValueHEBindings, nonlinearValueLeaBindings,
      List.mem_cons, List.not_mem_nil, or_false,
      Metta.BindingRel.eq.injEq, Prod.mk.injEq]
    aesop

/-- The nonlinear reconciliation has the same complete equation-solution
theory even though its representative chronology differs. -/
theorem nonlinearValue_solution_transport :
    LeaBindingSolutionEquiv
      nonlinearValueHEBindings nonlinearValueLeaBindings :=
  LeaBindingSolutionEquiv.of_rel nonlinearValue_reconciliation_relations

/-- The strengthened invariant accepts the repaired nonlinear reconciliation:
its stored compound value is preserved exactly, while representative choice
inside the connected `a=b` class remains quotiented. -/
theorem nonlinearValue_binding_congruence :
    LeaBindingCongruence
      nonlinearValueHEBindings nonlinearValueLeaBindings :=
  LeaBindingCongruence.of_rel nonlinearValue_reconciliation_relations

private theorem nonlinearValue_leaClassSolution_p :
    leaClassSolution nonlinearValueLeaBindings "p" =
      .expr [.sym "f", .var "b"] := by
  have hcond :
      ((Metta.Bindings.eqClassOrdered nonlinearValueLeaBindings "p" == ["p"]) &&
        (Metta.Bindings.classValues nonlinearValueLeaBindings "p").isEmpty) =
        false := by
    rfl
  have hfuel :
      Metta.Bindings.resolutionFuel nonlinearValueLeaBindings (.var "p") = 7 := by
    change Metta.Bindings.resolutionFuel
      [Metta.BindingRel.eq "a" "b",
        Metta.BindingRel.val "p" (.expr [.sym "f", .var "a"])]
      (.var "p") = 7
    simp [Metta.Bindings.resolutionFuel,
      Metta.Bindings.relationResolutionFuel, Metta.Atom.size]
  have hresolve :
      Metta.Bindings.resolve nonlinearValueLeaBindings "p" =
        some (.expr [.sym "f", .var "b"]) := by
    simp only [Metta.Bindings.resolve, hcond, Bool.false_eq_true, if_false]
    rw [hfuel]
    rfl
  simp [leaClassSolution, hresolve]

private theorem nonlinearValue_leaClassSolution_a :
    leaClassSolution nonlinearValueLeaBindings "a" = .var "b" := by
  change
    (Metta.Bindings.resolve
      [Metta.BindingRel.eq "a" "b",
        Metta.BindingRel.val "p" (.expr [.sym "f", .var "a"])]
      "a").getD (.var "a") = .var "b"
  rfl

private theorem nonlinearValue_leaClassSolution_b :
    leaClassSolution nonlinearValueLeaBindings "b" = .var "b" := by
  change
    (Metta.Bindings.resolve
      [Metta.BindingRel.eq "a" "b",
        Metta.BindingRel.val "p" (.expr [.sym "f", .var "a"])]
      "b").getD (.var "b") = .var "b"
  rfl

private theorem nonlinearValue_heClassSolution_p :
    heClassSolutionAt nonlinearValueHEBindings 30 "p" =
      .expr [.sym "f", .var "a"] := by
  change encodeModelAtom
    (((⟨[("p", .expression [.symbol "f", .var "a"])], [("a", "b")]⟩ :
      Bindings).resolveFull "p" 30).getD (.var "p")) =
        .expr [.sym "f", .var "a"]
  rfl

private theorem nonlinearValue_heClassSolution_a :
    heClassSolutionAt nonlinearValueHEBindings 30 "a" = .var "a" := by
  change encodeModelAtom
    (((⟨[("p", .expression [.symbol "f", .var "a"])], [("a", "b")]⟩ :
      Bindings).resolveFull "a" 30).getD (.var "a")) = .var "a"
  rfl

private theorem nonlinearValue_heClassSolution_b :
    heClassSolutionAt nonlinearValueHEBindings 30 "b" = .var "a" := by
  change encodeModelAtom
    (((⟨[("p", .expression [.symbol "f", .var "a"])], [("a", "b")]⟩ :
      Bindings).resolveFull "b" 30).getD (.var "b")) = .var "a"
  rfl

/-- POSITIVE: the nonlinear reconciliation rejected by the old
chronology-sensitive transport satisfies the semantic invariant.  One global
swap relates the independently selected unresolved class representatives and
preserves their sharing inside the compound value of `p`. -/
theorem nonlinearValue_semantic_transport :
    LeaBindingSemanticEquivAt ["p", "a", "b"] 30
      nonlinearValueHEBindings nonlinearValueLeaBindings := by
  refine ⟨?_, ?_⟩
  · intro start finish
    exact eqClass_mem_iff_of_leaBindingRelEquiv
      nonlinearValue_reconciliation_relations
  · refine ⟨Equiv.swap "a" "b", ?_⟩
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · rw [nonlinearValue_leaClassSolution_p,
        nonlinearValue_heClassSolution_p]
      simp [renBy]
    · rw [nonlinearValue_leaClassSolution_a,
        nonlinearValue_heClassSolution_a]
      simp
    · rw [nonlinearValue_leaClassSolution_b,
        nonlinearValue_heClassSolution_b]
      simp

/-- NEGATIVE: exact representative chronology is not a general matcher
invariant once class values are reconciled by independent unification
algorithms. -/
theorem nonlinearValue_not_full_transport :
    ¬ LeaBindingTransport nonlinearValueHEBindings nonlinearValueLeaBindings := by
  intro htransport
  have hchron := htransport.chronology
  simp [LeaEqualityChronology, nonlinearValueHEBindings,
    nonlinearValueLeaBindings, leaEqualityEdges] at hchron

/-- The semantic transport succeeds exactly where the superseded chronology
transport fails.  This paired oracle prevents future strengthening back to a
presentation-sensitive invariant. -/
theorem nonlinearValue_semantic_not_chronological :
    LeaBindingSemanticEquivAt ["p", "a", "b"] 30
        nonlinearValueHEBindings nonlinearValueLeaBindings ∧
      ¬ LeaBindingTransport nonlinearValueHEBindings nonlinearValueLeaBindings := by
  exact ⟨nonlinearValue_semantic_transport,
    nonlinearValue_not_full_transport⟩

/-- POSITIVE: the conformance observable survives the representative choice.
Both resolvers preserve the same variable-sharing shape. -/
theorem nonlinearValue_instantiation_alpha :
    Metta.AlphaEq
      (Metta.instantiate nonlinearValueLeaBindings
        (.expr [.sym "h", .var "p"]))
      (encodeModelAtom
        (nonlinearValueHEBindings.applyFull
          (.expression [.symbol "h", .var "p"]) 30)) := by
  have hlea :
      Metta.instantiate nonlinearValueLeaBindings
          (.expr [.sym "h", .var "p"]) =
        .expr [.sym "h", .expr [.sym "f", .var "b"]] := by
    have hcond :
        ((Metta.Bindings.eqClassOrdered nonlinearValueLeaBindings "p" == ["p"]) &&
          (Metta.Bindings.classValues nonlinearValueLeaBindings "p").isEmpty) = false := by
      rfl
    have hfuel :
        Metta.Bindings.resolutionFuel nonlinearValueLeaBindings (.var "p") = 7 := by
      change Metta.Bindings.resolutionFuel
        [Metta.BindingRel.eq "a" "b",
          Metta.BindingRel.val "p" (.expr [.sym "f", .var "a"])]
        (.var "p") = 7
      simp [Metta.Bindings.resolutionFuel,
        Metta.Bindings.relationResolutionFuel, Metta.Atom.size]
    have hresolve :
        Metta.Bindings.resolve nonlinearValueLeaBindings "p" =
          some (.expr [.sym "f", .var "b"]) := by
      simp only [Metta.Bindings.resolve, hcond, Bool.false_eq_true, if_false]
      rw [hfuel]
      rfl
    simp [Metta.instantiate, Metta.Bindings.resolveAtom, hresolve]
  have hhe :
      nonlinearValueHEBindings.applyFull
          (.expression [.symbol "h", .var "p"]) 30 =
        .expression [.symbol "h", .expression [.symbol "f", .var "a"]] := by
    decide
  rw [hlea, hhe]
  change Metta.AlphaEq
    (.expr [.sym "h", .expr [.sym "f", .var "b"]])
    (.expr [.sym "h", .expr [.sym "f", .var "a"]])
  unfold Metta.AlphaEq Metta.canonicalizeVars
  simp [Metta.Atom.vars, Metta.distinctVarsAux, Metta.renameVars]

private def connectedPattern : Atom :=
  .expression [.symbol "g", .var "p", .var "p"]

private def connectedQuery : Atom :=
  .expression [.symbol "g", .var "q1", .var "q2"]

private def connectedHEBindings : Bindings :=
  ⟨[], [("q1", "p"), ("q2", "p")]⟩

private def connectedLeaBindings : Metta.Bindings :=
  [Metta.BindingRel.eq "p" "q2", Metta.BindingRel.eq "p" "q1"]

/-- The minimal binding-level connected-class regression is a witness of the
general representation-independent relation, despite opposite edge order. -/
theorem connectedClass_binding_transport :
    connectedLeaBindings ∈
        Metta.matchAtoms (encodeModelAtom connectedPattern)
          (encodeModelAtom connectedQuery) ∧
      LeaBindingRelEquiv connectedHEBindings connectedLeaBindings := by
  constructor
  · have hmatch :
        Metta.matchAtoms
            (.expr [.sym "g", .var "p", .var "p"])
            (.expr [.sym "g", .var "q1", .var "q2"]) =
          [connectedLeaBindings] := by
        rfl
    simpa [connectedPattern, connectedQuery, encodeModelAtom,
      encodeModelAtoms] using congrArg (connectedLeaBindings ∈ ·) hmatch
  · constructor
    · intro v value
      simp [connectedHEBindings, connectedLeaBindings]
    · intro x y
      simp only [connectedHEBindings, connectedLeaBindings, List.mem_cons,
        List.not_mem_nil, or_false, Metta.BindingRel.eq.injEq,
        Prod.mk.injEq]
      aesop

theorem connectedClass_full_transport :
    connectedLeaBindings ∈
        Metta.matchAtoms (encodeModelAtom connectedPattern)
          (encodeModelAtom connectedQuery) ∧
      LeaBindingTransport connectedHEBindings connectedLeaBindings := by
  refine ⟨connectedClass_binding_transport.1,
    connectedClass_binding_transport.2, ?_⟩
  rfl

/-- The adversarial two-query-variable class is an instance of the general
representative theorem, not a separate convention-specific calculation. -/
theorem connectedClass_representatives_agree (v : String) :
    Metta.Bindings.eqRepresentative connectedLeaBindings v =
      connectedHEBindings.eqRepresentative v :=
  eqRepresentative_eq_of_transport
    connectedClass_full_transport.2.relations
    connectedClass_full_transport.2.chronology v

/-- Equality-only bindings resolve one variable identically in both engines.
Two units of HE fuel cover the outer `applyFull` and inner resolver steps. -/
theorem applyFull_var_eq_instantiate_of_noAssignments
    {b : Bindings} {lb : Metta.Bindings}
    (htransport : LeaBindingTransport b lb)
    (hassign : b.assignments = []) (v : String) (fuel : Nat) :
    encodeModelAtom (b.applyFull (.var v) (fuel + 2)) =
      Metta.instantiate lb (encodeModelAtom (.var v)) := by
  have hheValues : b.classValues v = [] := by
    simp [Bindings.classValues, Bindings.lookup, hassign]
  have hleaValues : Metta.Bindings.classValues lb v = [] :=
    leaClassValues_eq_nil_of_transport htransport hheValues
  have hordered := eqClassOrdered_eq_of_transport
    htransport.relations htransport.chronology v
  have hrep := eqRepresentative_eq_of_transport
    htransport.relations htransport.chronology v
  have hlookup : ∀ x, b.lookup x = none := by
    intro x
    simp [Bindings.lookup, hassign]
  have hfind : (b.eqClassOrdered v).findSome? b.lookup = none := by
    rw [List.findSome?_eq_none_iff]
    intro x _
    simp [Bindings.lookup, hassign]
  simp only [encodeModelAtom, Metta.instantiate, Metta.Bindings.resolveAtom]
  by_cases htriv : b.eqClassOrdered v = [v]
  · have htrivLea : Metta.Bindings.eqClassOrdered lb v = [v] := by
      rw [hordered]
      exact htriv
    simp [Bindings.applyFull, Bindings.resolveFull,
      htriv,
      Metta.Bindings.resolve, hleaValues, htrivLea, hlookup,
      encodeModelAtom]
  · have htrivLea : Metta.Bindings.eqClassOrdered lb v ≠ [v] := by
      simpa [hordered] using htriv
    simp [Bindings.applyFull, Bindings.resolveFull,
      Bindings.resolveAtomFullAux, hfind, htriv,
      Metta.Bindings.resolve, Metta.Bindings.resolveAtomAux,
      Metta.Bindings.resolutionFuel, hleaValues,
      hordered, hrep, Bindings.eqRepresentative, encodeModelAtom]

/-- Equality-only instantiation agrees exactly on every atom once HE fuel
covers the atom depth. -/
theorem applyFull_eq_instantiate_of_noAssignments
    {b : Bindings} {lb : Metta.Bindings}
    (htransport : LeaBindingTransport b lb)
    (hassign : b.assignments = []) :
    ∀ fuel atom, atomDepth atom + 2 ≤ fuel →
      encodeModelAtom (b.applyFull atom fuel) =
        Metta.instantiate lb (encodeModelAtom atom) := by
  intro fuel
  induction fuel with
  | zero =>
      intro atom hdepth
      omega
  | succ fuel ih =>
      intro atom hdepth
      cases fuel with
      | zero =>
          cases atom <;> simp [atomDepth] at hdepth
      | succ fuel' =>
          cases atom with
          | symbol symbol =>
              simp [Bindings.applyFull, Metta.instantiate,
                Metta.Bindings.resolveAtom, encodeModelAtom]
          | var v =>
              exact applyFull_var_eq_instantiate_of_noAssignments
                htransport hassign v fuel'
          | grounded ground =>
              simp [Bindings.applyFull, Metta.instantiate,
                Metta.Bindings.resolveAtom, encodeModelAtom]
          | expression atoms =>
              have hlist :
                  ∀ atoms : List Atom, listDepth atoms + 2 ≤ fuel' + 1 →
                    encodeModelAtoms
                        (atoms.map (fun atom => b.applyFull atom (fuel' + 1))) =
                      (encodeModelAtoms atoms).map
                        (Metta.Bindings.resolveAtom lb) := by
                intro atoms
                induction atoms with
                | nil =>
                    intro _
                    rfl
                | cons atom atoms ihAtoms =>
                    intro hatoms
                    simp [encodeModelAtoms, listDepth] at hatoms ⊢
                    have hhead : atomDepth atom + 2 ≤ fuel' + 1 := by omega
                    have htail : listDepth atoms + 2 ≤ fuel' + 1 := by omega
                    constructor
                    · simpa [Metta.instantiate] using ih atom hhead
                    · exact ihAtoms htail
              have hatoms : listDepth atoms + 2 ≤ fuel' + 1 := by
                simp [atomDepth] at hdepth
                omega
              simpa [Bindings.applyFull, Metta.instantiate,
                Metta.Bindings.resolveAtom, encodeModelAtom] using
                hlist atoms hatoms

/-- The semantic invariant genuinely generalizes the earlier exact
chronology transport: on the equality-only lane, the old construction proof
induces semantic agreement with the identity solution permutation. -/
theorem LeaBindingTransport.semantic_of_noAssignments
    {b : Bindings} {lb : Metta.Bindings}
    (htransport : LeaBindingTransport b lb)
    (hassign : b.assignments = [])
    (scope : List String) (fuel : Nat) (hfuel : 1 ≤ fuel) :
    LeaBindingSemanticEquivAt scope fuel b lb := by
  refine ⟨?_, ?_⟩
  · intro start finish
    exact eqClass_mem_iff_of_leaBindingRelEquiv htransport.relations
  · refine ⟨Equiv.refl String, ?_⟩
    intro v _hv
    have happly :=
      applyFull_eq_instantiate_of_noAssignments
        htransport hassign (fuel + 1) (.var v) (by
          simp [atomDepth]
          omega)
    have hhe :
        heClassSolutionAt b fuel v =
          encodeModelAtom (b.applyFull (.var v) (fuel + 1)) := by
      cases hresolve : b.resolveFull v fuel <;>
        simp [heClassSolutionAt, Bindings.applyFull, hresolve]
    have hlea :
        leaClassSolution lb v =
          Metta.instantiate lb (encodeModelAtom (.var v)) := by
      simp [leaClassSolution, Metta.instantiate,
        Metta.Bindings.resolveAtom, encodeModelAtom]
    rw [hlea, hhe, renBy_refl]
    exact happly.symm

/-- Canonical equality-free matcher bindings induce the semantic invariant on
the assignment lane.  The hypotheses are the actual solved-form conditions
used by the existing assignment substitution theorem; no resolver agreement is
assumed as a field. -/
theorem semantic_canonical_of_noEqualities
    {b : Bindings}
    (heq : b.equalities = [])
    (hno : NoVarAssignmentValues b)
    (hkeys : AssignmentsNodup b)
    (hfresh : ValueKeysFreshForValues (toLeaTTaMatchBindings b))
    (scope : List String) (fuel : Nat) (hfuel : 1 ≤ fuel) :
    LeaBindingSemanticEquivAt scope fuel b
      (toLeaTTaMatchBindingsFull b) := by
  have hbare : NoBareVarAssignments b := by
    intro v x hmem
    apply hno
    unfold Bindings.lookup
    exact heLookup_eq_some_of_assignment_mem_nodup hkeys hmem
  have htransport :
      LeaBindingTransport b (toLeaTTaMatchBindingsFull b) :=
    LeaBindingTransport.canonical hbare
  refine ⟨?_, ?_⟩
  · intro start finish
    exact eqClass_mem_iff_of_leaBindingRelEquiv htransport.relations
  · refine ⟨Equiv.refl String, ?_⟩
    intro v _hv
    have happly :
        encodeModelAtom (b.applyFull (.var v) (fuel + 1)) =
          Metta.instantiate (toLeaTTaMatchBindings b)
            (encodeModelAtom (.var v)) := by
      rw [Bindings.applyFull_no_equalities heq]
      exact
        encodeModelAtom_apply_eq_instantiate_matchBindings_of_noVarAssignmentValues
          hno hkeys hfresh (fuel + 1) (.var v) (by
            simp [atomDepth]
            omega)
    have hfull :
        toLeaTTaMatchBindingsFull b = toLeaTTaMatchBindings b := by
      simp [toLeaTTaMatchBindingsFull, toLeaTTaEqualityBindings, heq]
    have hhe :
        heClassSolutionAt b fuel v =
          encodeModelAtom (b.applyFull (.var v) (fuel + 1)) := by
      cases hresolve : b.resolveFull v fuel <;>
        simp [heClassSolutionAt, Bindings.applyFull, hresolve]
    have hlea :
        leaClassSolution (toLeaTTaMatchBindingsFull b) v =
          Metta.instantiate (toLeaTTaMatchBindings b)
            (encodeModelAtom (.var v)) := by
      rw [hfull]
      simp [leaClassSolution, Metta.instantiate,
        Metta.Bindings.resolveAtom, encodeModelAtom]
    rw [hlea, hhe, renBy_refl]
    exact happly.symm

/-- One fresh, non-variable assignment has the same semantic class solution in
HE and repaired LeaTTa.  This is the assignment-side leaf invariant used by
both variable/non-variable matcher orientations. -/
theorem singletonAssignment_semantic
    {key : String} {value : Atom}
    (hnonvar : DeclMatchSpec.Atom.isVarB value = false)
    (hfresh : key ∉ (encodeModelAtom value).vars)
    (scope : List String) (fuel : Nat) (hfuel : 1 ≤ fuel) :
    LeaBindingSemanticEquivAt scope fuel
      (⟨[(key, value)], []⟩ : Bindings)
      [Metta.BindingRel.val key (encodeModelAtom value)] := by
  have hrelation :
      toLeaTTaAssignmentRel (key, value) =
        Metta.BindingRel.val key (encodeModelAtom value) := by
    cases value <;>
      simp_all [toLeaTTaAssignmentRel, DeclMatchSpec.Atom.isVarB,
        encodeModelAtom]
  have hno : NoVarAssignmentValues
      (⟨[(key, value)], []⟩ : Bindings) := by
    intro v x hlookup
    have hmem : (v, .var x) ∈ [(key, value)] :=
      heAssignment_mem_of_lookup_eq_some (by
        simpa [Bindings.lookup] using hlookup)
    simp only [List.mem_singleton, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, hvalue⟩
    subst value
    simp [DeclMatchSpec.Atom.isVarB] at hnonvar
  have hkeys : AssignmentsNodup
      (⟨[(key, value)], []⟩ : Bindings) := by
    simp [AssignmentsNodup]
  have hbindings :
      toLeaTTaMatchBindings (⟨[(key, value)], []⟩ : Bindings) =
        [Metta.BindingRel.val key (encodeModelAtom value)] := by
    rw [toLeaTTaMatchBindings_eq_map]
    simpa using congrArg (fun relation => [relation]) hrelation
  have hfreshBindings :
      ValueKeysFreshForValues
        (toLeaTTaMatchBindings (⟨[(key, value)], []⟩ : Bindings)) := by
    rw [hbindings]
    exact singleton_valueKeysFreshForValues hfresh
  simpa [toLeaTTaMatchBindingsFull, toLeaTTaEqualityBindings,
    hbindings] using
    (semantic_canonical_of_noEqualities
      (b := (⟨[(key, value)], []⟩ : Bindings)) rfl hno hkeys
      hfreshBindings scope fuel hfuel)

/-- A repaired-LeaTTa matcher witness whose binding result agrees with one HE
matcher result by equality-class and class-solution semantics. -/
def LeaMatcherSemanticTransportAt
    (scope : List String) (fuel : Nat)
    (query pattern : Atom) (hb : Bindings) : Prop :=
  ∃ lb,
    lb ∈ Metta.matchAtoms (encodeModelAtom pattern) (encodeModelAtom query) ∧
      LeaBindingSemanticEquivAt scope fuel hb lb

/-- Every non-expression constructor of the declarative HE matcher is realized
by repaired LeaTTa with representation-independent binding semantics. -/
theorem matchRel_leaf_semantic_transport
    {scope : List String} {solutionFuel : Nat}
    {query pattern : Atom} {hb : Bindings}
    (hrel : MatchRel query pattern hb)
    (hdisj : VarsDisjoint query pattern)
    (hleaf : ¬ BothExpressions query pattern)
    (hfuel : 1 ≤ solutionFuel) :
    LeaMatcherSemanticTransportAt scope solutionFuel query pattern hb := by
  cases hrel with
  | symSym s =>
      exact ⟨[], by
        simp [Metta.matchAtoms, Metta.matchAtomsWith, encodeModelAtom],
        LeaBindingSemanticEquivAt.empty scope solutionFuel⟩
  | varVar queryVar patternVar =>
      have hne : patternVar ≠ queryVar := by
        intro h
        subst patternVar
        exact hdisj queryVar
          (by simp [encodeModelAtom, Metta.Atom.vars])
          (by simp [encodeModelAtom, Metta.Atom.vars])
      refine ⟨[Metta.BindingRel.eq patternVar queryVar], ?_, ?_⟩
      · simp [Metta.matchAtoms, Metta.matchAtomsWith, encodeModelAtom, hne]
      · have htransport :
            LeaBindingTransport
              (⟨[], [(queryVar, patternVar)]⟩ : Bindings)
              [Metta.BindingRel.eq patternVar queryVar] := by
          simpa [toLeaTTaMatchBindingsFull, toLeaTTaEqualityBindings,
            toLeaTTaMatchBindings, toLeaTTaMatchSubst,
            Metta.Bindings.ofSubst] using
            (LeaBindingTransport.canonical
              (b := (⟨[], [(queryVar, patternVar)]⟩ : Bindings))
              (by simp [NoBareVarAssignments]))
        exact htransport.semantic_of_noAssignments rfl scope solutionFuel hfuel
  | varNonVar hnonvar _hoccurs =>
      rename_i v
      cases pattern with
      | var w => simp [DeclMatchSpec.Atom.isVarB] at hnonvar
      | symbol s =>
          refine ⟨[Metta.BindingRel.val v (.sym s)], ?_, ?_⟩
          · have hloop := Metta.Bindings.hasLoop_singleton_val_of_not_mem
              v (.sym s) (by simp [Metta.Atom.vars])
            simp [Metta.matchAtoms, Metta.matchAtomsWith, encodeModelAtom, hloop]
          · exact singletonAssignment_semantic hnonvar (by
              simp [encodeModelAtom, Metta.Atom.vars]) scope solutionFuel hfuel
      | grounded g =>
          refine ⟨[Metta.BindingRel.val v (.gnd (encodeModelGround g))], ?_, ?_⟩
          · have hloop := Metta.Bindings.hasLoop_singleton_val_of_not_mem
              v (.gnd (encodeModelGround g)) (by simp [Metta.Atom.vars])
            simp [Metta.matchAtoms, Metta.matchAtomsWith, encodeModelAtom, hloop]
          · exact singletonAssignment_semantic hnonvar (by
              simp [encodeModelAtom, Metta.Atom.vars]) scope solutionFuel hfuel
      | expression es =>
          have hfresh : v ∉ (encodeModelAtom (.expression es)).vars :=
            hdisj v (by simp [encodeModelAtom, Metta.Atom.vars])
          have hoccurs :
              Metta.Subst.occurs v (encodeModelAtom (.expression es)) = false :=
            occurs_eq_false_of_not_mem_vars v _ hfresh
          change Metta.Subst.occurs v (.expr (encodeModelAtoms es)) = false at hoccurs
          refine ⟨[Metta.BindingRel.val v (.expr (encodeModelAtoms es))], ?_, ?_⟩
          · have hloop := Metta.Bindings.hasLoop_singleton_val_of_not_mem
              v (.expr (encodeModelAtoms es)) (by
                simpa [encodeModelAtom] using hfresh)
            simp [Metta.matchAtoms, Metta.matchAtomsWith, encodeModelAtom, hoccurs, hloop]
          · exact singletonAssignment_semantic hnonvar hfresh
              scope solutionFuel hfuel
  | nonVarVar hnonvar _hoccurs =>
      rename_i v
      have hdisj' : VarsDisjoint (.var v) query := hdisj.symm
      cases query with
      | var w => simp [DeclMatchSpec.Atom.isVarB] at hnonvar
      | symbol s =>
          refine ⟨[Metta.BindingRel.val v (.sym s)], ?_, ?_⟩
          · have hloop := Metta.Bindings.hasLoop_singleton_val_of_not_mem
              v (.sym s) (by simp [Metta.Atom.vars])
            simp [Metta.matchAtoms, Metta.matchAtomsWith, encodeModelAtom, hloop]
          · exact singletonAssignment_semantic hnonvar (by
              simp [encodeModelAtom, Metta.Atom.vars]) scope solutionFuel hfuel
      | grounded g =>
          refine ⟨[Metta.BindingRel.val v (.gnd (encodeModelGround g))], ?_, ?_⟩
          · have hloop := Metta.Bindings.hasLoop_singleton_val_of_not_mem
              v (.gnd (encodeModelGround g)) (by simp [Metta.Atom.vars])
            simp [Metta.matchAtoms, Metta.matchAtomsWith, encodeModelAtom, hloop]
          · exact singletonAssignment_semantic hnonvar (by
              simp [encodeModelAtom, Metta.Atom.vars]) scope solutionFuel hfuel
      | expression es =>
          have hfresh : v ∉ (encodeModelAtom (.expression es)).vars :=
            hdisj' v (by simp [encodeModelAtom, Metta.Atom.vars])
          have hoccurs :
              Metta.Subst.occurs v (encodeModelAtom (.expression es)) = false :=
            occurs_eq_false_of_not_mem_vars v _ hfresh
          change Metta.Subst.occurs v (.expr (encodeModelAtoms es)) = false at hoccurs
          refine ⟨[Metta.BindingRel.val v (.expr (encodeModelAtoms es))], ?_, ?_⟩
          · have hloop := Metta.Bindings.hasLoop_singleton_val_of_not_mem
              v (.expr (encodeModelAtoms es)) (by
                simpa [encodeModelAtom] using hfresh)
            simp [Metta.matchAtoms, Metta.matchAtomsWith, encodeModelAtom, hoccurs, hloop]
          · exact singletonAssignment_semantic hnonvar hfresh
              scope solutionFuel hfuel
  | grounded g =>
      refine ⟨[], ?_, LeaBindingSemanticEquivAt.empty scope solutionFuel⟩
      have hself :
          Metta.Atom.equiv (.gnd (encodeModelGround g))
            (.gnd (encodeModelGround g)) = true := by
        simpa [encodeModelAtom] using encodeModelAtom_grounded_equiv_self g
      simp [Metta.matchAtoms, Metta.matchAtomsWith, encodeModelAtom, hself]
  | @expr ls rs b hlist _ =>
      exact (hleaf ⟨ls, rs, rfl, rfl⟩).elim

/-- Executable leaf matching inherits semantic transport from its declarative
soundness theorem. -/
theorem matchAtoms_leaf_semantic_transport
    {scope : List String} {solutionFuel matcherFuel : Nat}
    {query pattern : Atom} {hb : Bindings}
    (hmatch : hb ∈ matchAtoms query pattern matcherFuel)
    (hdisj : VarsDisjoint query pattern)
    (hleaf : ¬ BothExpressions query pattern)
    (hfuel : 1 ≤ solutionFuel) :
    LeaMatcherSemanticTransportAt scope solutionFuel query pattern hb :=
  matchRel_leaf_semantic_transport
    (matchAtoms_sound hmatch) hdisj hleaf hfuel

/-- The connected equality-class regression is a semantic transport instance;
its exact representative agreement is useful evidence but is not part of the
new contract. -/
theorem connectedClass_semantic_transport :
    LeaBindingSemanticEquivAt ["p", "q1", "q2"] 19
      connectedHEBindings connectedLeaBindings :=
  connectedClass_full_transport.2.semantic_of_noAssignments
    rfl ["p", "q1", "q2"] 19 (by omega)

/-- Both observables of the minimal connected class agree: reading both query
variables preserves co-reference, and instantiating the RHS selects the same
representative. -/
theorem connectedClass_instantiation_observables :
    Metta.instantiate connectedLeaBindings
        (.expr [.var "q1", .var "q2"]) =
      encodeModelAtom
        (connectedHEBindings.applyFull
          (.expression [.var "q1", .var "q2"]) 20) ∧
    Metta.instantiate connectedLeaBindings
        (.expr [.sym "f", .var "p"]) =
      encodeModelAtom
        (connectedHEBindings.applyFull
          (.expression [.symbol "f", .var "p"]) 20) := by
  constructor
  · exact (applyFull_eq_instantiate_of_noAssignments
      connectedClass_full_transport.2 rfl 20
      (.expression [.var "q1", .var "q2"]) (by decide)).symm
  · exact (applyFull_eq_instantiate_of_noAssignments
      connectedClass_full_transport.2 rfl 20
      (.expression [.symbol "f", .var "p"]) (by decide)).symm

/-- Kernel oracle for the order-sensitive adversary: HE chooses the first query
variable q1, preserves co-reference, and uses the same representative for the
rule variable. -/
theorem connectedClass_he_applyFull_oracles :
    connectedHEBindings.applyFull
        (.expression [.var "q1", .var "q2"]) 20 =
      .expression [.var "q1", .var "q1"] ∧
    connectedHEBindings.applyFull
        (.expression [.symbol "f", .var "p"]) 20 =
      .expression [.symbol "f", .var "q1"] := by
  decide

/-- The LeaTTa observables select that same concrete representative. -/
theorem connectedClass_lea_instantiate_oracles :
    Metta.instantiate
        [Metta.BindingRel.eq "p" "q2", Metta.BindingRel.eq "p" "q1"]
        (.expr [.var "q1", .var "q2"]) =
      .expr [.var "q1", .var "q1"] ∧
    Metta.instantiate
        [Metta.BindingRel.eq "p" "q2", Metta.BindingRel.eq "p" "q1"]
        (.expr [.sym "f", .var "p"]) =
      .expr [.sym "f", .var "q1"] := by
  constructor
  · calc
      Metta.instantiate connectedLeaBindings
          (.expr [.var "q1", .var "q2"]) =
          encodeModelAtom
            (connectedHEBindings.applyFull
              (.expression [.var "q1", .var "q2"]) 20) :=
        connectedClass_instantiation_observables.1
      _ = .expr [.var "q1", .var "q1"] := by
        rw [connectedClass_he_applyFull_oracles.1]
        rfl
  · calc
      Metta.instantiate connectedLeaBindings
          (.expr [.sym "f", .var "p"]) =
          encodeModelAtom
            (connectedHEBindings.applyFull
              (.expression [.symbol "f", .var "p"]) 20) :=
        connectedClass_instantiation_observables.2
      _ = .expr [.sym "f", .var "q1"] := by
        rw [connectedClass_he_applyFull_oracles.2]
        rfl

/-- POSITIVE: opposite-oriented variable matching is transported as an explicit
equality relation. -/
example :
    LeaMatcherTransportFull (.var "query") (.var "pattern")
      ⟨[], [("query", "pattern")]⟩ := by
  apply matchRel_leaf_transport (.varVar "query" "pattern")
  · intro v hvQuery hvPattern
    simp [encodeModelAtom, Metta.Atom.vars] at hvQuery hvPattern
    subst v
    simp at hvPattern
  · simp [BothExpressions]

/-- NEGATIVE: standardizing apart is necessary because LeaTTa suppresses a
reflexive alias while HE's raw var/var constructor records one. -/
example :
    ¬ LeaBindingRelEquiv
        ⟨[], [("x", "x")]⟩
        (Metta.matchAtoms (.var "x") (.var "x")).head! := by
  change ¬ LeaBindingRelEquiv ⟨[], [("x", "x")]⟩ []
  intro h
  have hlea := (h.equalities "x" "x").mpr (by simp)
  simp at hlea

private def aliasTraceProbePattern : Atom :=
  .expression [.symbol "g", .symbol "k", .var "rp", .var "rp"]

private def aliasTraceProbeQuery : Atom :=
  .expression [.symbol "g", .var "qb",
    .expression [.symbol "f", .var "qa"],
    .expression [.symbol "f", .var "qb"]]

private def aliasTraceProbeHEBindings : Bindings :=
  ⟨[("qb", .symbol "k"),
      ("rp", .expression [.symbol "f", .var "qa"])],
    [("qa", "qb")]⟩

private def aliasTraceProbeLeaBindings : Metta.Bindings :=
  [Metta.BindingRel.eq "qa" "qb",
    Metta.BindingRel.val "qa" (.sym "k"),
    Metta.BindingRel.val "qb" (.sym "k"),
    Metta.BindingRel.val "rp" (.expr [.sym "f", .var "qa"])]

private def aliasTraceProbeValuesOnly : Metta.Bindings :=
  [Metta.BindingRel.val "qa" (.sym "k"),
    Metta.BindingRel.val "qb" (.sym "k"),
    Metta.BindingRel.val "rp" (.expr [.sym "f", .var "qa"])]

/-- POSITIVE REPAIR ORACLE: a variable equality exposed only after recursive
compound decomposition survives whole-system normalization as an explicit
class edge.  Both engines retain the same alias despite choosing normalized
value presentations independently. -/
theorem aliasTraceProbe_match_oracles :
    aliasTraceProbeHEBindings ∈
        matchAtoms aliasTraceProbeQuery aliasTraceProbePattern 40 ∧
      Metta.matchAtoms (encodeModelAtom aliasTraceProbePattern)
          (encodeModelAtom aliasTraceProbeQuery) =
        [aliasTraceProbeLeaBindings] := by
  constructor
  · decide
  · have hloop : Metta.Bindings.hasLoop
        [Metta.BindingRel.eq "qa" "qb",
          Metta.BindingRel.val "qa" (.sym "k"),
          Metta.BindingRel.val "qb" (.sym "k"),
          Metta.BindingRel.val "rp" (.expr [.sym "f", .var "qa"])] = false := by
      apply Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.hasLoop_false_of_resolveAtomAux_some
      · rfl
      · intro x hx
        have hvars : Metta.Bindings.vars
            [Metta.BindingRel.eq "qa" "qb",
              Metta.BindingRel.val "qa" (.sym "k"),
              Metta.BindingRel.val "qb" (.sym "k"),
              Metta.BindingRel.val "rp" (.expr [.sym "f", .var "qa"])] =
            ["qa", "qb", "rp"] := by
          simp [Metta.Bindings.vars, Metta.Atom.vars, List.eraseDups_cons]
        rw [hvars] at hx
        simp at hx
        have hfuel (v : String) : Metta.Bindings.resolutionFuel
            [Metta.BindingRel.eq "qa" "qb",
              Metta.BindingRel.val "qa" (.sym "k"),
              Metta.BindingRel.val "qb" (.sym "k"),
              Metta.BindingRel.val "rp" (.expr [.sym "f", .var "qa"])]
            (.var v) = 11 := by
          simp [Metta.Bindings.resolutionFuel,
            Metta.Bindings.relationResolutionFuel, Metta.Atom.size]
        rcases hx with rfl | rfl | rfl
        · exact ⟨.sym "k", by rw [hfuel]; rfl⟩
        · exact ⟨.sym "k", by rw [hfuel]; rfl⟩
        · exact ⟨.expr [.sym "f", .sym "k"], by rw [hfuel]; rfl⟩
    have hqbLoop : Metta.Bindings.hasLoop
        [Metta.BindingRel.val "qb" (.sym "k")] = false :=
      Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _ (by simp [Metta.Atom.vars])
    have hrpqaLoop : Metta.Bindings.hasLoop
        [Metta.BindingRel.val "rp" (.expr [.sym "f", .var "qa"])] = false :=
      Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _ (by simp [Metta.Atom.vars])
    have hrpqbLoop : Metta.Bindings.hasLoop
        [Metta.BindingRel.val "rp" (.expr [.sym "f", .var "qb"])] = false :=
      Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _ (by simp [Metta.Atom.vars])
    simp (config := { maxSteps := 1000000 })
      [aliasTraceProbePattern, aliasTraceProbeQuery,
        aliasTraceProbeLeaBindings, encodeModelAtom, encodeModelAtoms,
        hloop, hqbLoop, hrpqaLoop, hrpqbLoop,
        Metta.matchAtoms, Metta.matchAtomsWith, Metta.matchAll,
        Metta.Bindings.merge, Metta.Bindings.mergeOne,
        Metta.Bindings.addVarBinding, Metta.Bindings.unifyValues,
        Metta.Bindings.reconcileAll, Metta.Bindings.equations,
        Metta.Bindings.relationEquation, Metta.Bindings.equationFuel,
        Metta.Bindings.rebuildFromReconciliation,
        Metta.Bindings.reconciliationAliases,
        Metta.Bindings.restoreAlias,
        Metta.Bindings.rebuildFromSubst, Metta.Bindings.equalitySkeleton,
        Metta.Bindings.ofSubst,
        Metta.Bindings.classValues, Metta.Bindings.eqClassOrdered,
        Metta.Bindings.eqVarsInOrder, Metta.Bindings.eqClass,
        Metta.Bindings.eqClassAux, Metta.Bindings.eqStep,
        Metta.Bindings.lookupVal, Metta.Bindings.addEqRaw,
        Metta.Bindings.addValRaw,
        Metta.Bindings.removeVal,
        Metta.Unify.aliasTrace, Metta.Unify.aliasConstraints,
        Metta.Unify.unifyRounds, Metta.Unify.decomposeAll,
        Metta.Unify.decomposeEq, Metta.Unify.decomposeList,
        Metta.Subst.occurs, Metta.Subst.apply, Metta.Subst.lookup,
        Metta.Subst.extend, Metta.Subst.erase, List.filter_cons,
        BEq.beq, Metta.Atom.size]

theorem aliasTraceProbe_connected_class_preserved :
    "qb" ∈ Metta.Bindings.eqClass aliasTraceProbeLeaBindings "qa" := by
  decide

/-- NEGATIVE REGRESSION ORACLE: equal normalized values do not by themselves
encode the explicit equality-class closure required by HE matching. -/
theorem aliasTraceProbe_values_only_lose_class :
    "qb" ∉ Metta.Bindings.eqClass aliasTraceProbeValuesOnly "qa" := by
  decide

private def aliasForkProbePattern : Atom :=
  .expression [.symbol "g", .var "p", .var "p"]

private def aliasForkProbeQuery : Atom :=
  .expression [.symbol "g",
    .expression [.symbol "f", .var "x", .var "x", .var "y", .var "z"],
    .expression [.symbol "f", .var "z", .var "y", .symbol "k", .symbol "k"]]

private def aliasForkProbeHEBindings : Bindings :=
  ⟨[("p", .expression
        [.symbol "f", .var "x", .var "x", .var "y", .var "z"]),
      ("y", .symbol "k")],
    [("x", "z"), ("x", "y")]⟩

private def aliasForkProbeLeaBindings : Metta.Bindings :=
  [Metta.BindingRel.val "y" (.sym "k"),
    Metta.BindingRel.eq "z" "y",
    Metta.BindingRel.eq "x" "z",
    Metta.BindingRel.val "p"
      (.expr [.sym "f", .var "x", .var "x", .var "y", .var "z"])]

/-- POSITIVE TRACE-COMPLETENESS ORACLE: two aliases sharing `x` are followed
by grounding both branches.  Repaired LeaTTa retains a connected spanning tree
`x-z-y`, while HE retains `z-x-y`; neither representative chronology nor
direct-edge identity is required. -/
theorem aliasForkProbe_match_oracles :
    aliasForkProbeHEBindings ∈
        matchAtoms aliasForkProbeQuery aliasForkProbePattern 100 ∧
      Metta.matchAtoms (encodeModelAtom aliasForkProbePattern)
          (encodeModelAtom aliasForkProbeQuery) =
        [aliasForkProbeLeaBindings] := by
  constructor
  · decide
  · have hloop : Metta.Bindings.hasLoop
        [Metta.BindingRel.val "y" (.sym "k"),
          Metta.BindingRel.eq "z" "y", Metta.BindingRel.eq "x" "z",
          Metta.BindingRel.val "p"
            (.expr [.sym "f", .var "x", .var "x", .var "y", .var "z"])] = false := by
      apply Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.hasLoop_false_of_resolveAtomAux_some
      · rfl
      · intro x hx
        have hvars : Metta.Bindings.vars
            [Metta.BindingRel.val "y" (.sym "k"),
              Metta.BindingRel.eq "z" "y", Metta.BindingRel.eq "x" "z",
              Metta.BindingRel.val "p"
                (.expr [.sym "f", .var "x", .var "x", .var "y", .var "z"])] =
            ["y", "z", "x", "p"] := by
          simp [Metta.Bindings.vars, Metta.Atom.vars, List.eraseDups_cons]
        rw [hvars] at hx
        simp at hx
        have hfuel (v : String) : Metta.Bindings.resolutionFuel
            [Metta.BindingRel.val "y" (.sym "k"),
              Metta.BindingRel.eq "z" "y", Metta.BindingRel.eq "x" "z",
              Metta.BindingRel.val "p"
                (.expr [.sym "f", .var "x", .var "x", .var "y", .var "z"])]
            (.var v) = 13 := by
          simp [Metta.Bindings.resolutionFuel,
            Metta.Bindings.relationResolutionFuel, Metta.Atom.size]
        rcases hx with rfl | rfl | rfl | rfl
        · exact ⟨.sym "k", by rw [hfuel]; set_option maxRecDepth 2048 in rfl⟩
        · exact ⟨.sym "k", by rw [hfuel]; set_option maxRecDepth 2048 in rfl⟩
        · exact ⟨.sym "k", by rw [hfuel]; set_option maxRecDepth 2048 in rfl⟩
        · exact ⟨.expr [.sym "f", .sym "k", .sym "k", .sym "k", .sym "k"], by
            rw [hfuel]
            set_option maxRecDepth 2048 in rfl⟩
    have hpLeftLoop : Metta.Bindings.hasLoop
        [Metta.BindingRel.val "p"
          (.expr [.sym "f", .var "x", .var "x", .var "y", .var "z"])] = false :=
      Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _ (by simp [Metta.Atom.vars])
    have hpRightLoop : Metta.Bindings.hasLoop
        [Metta.BindingRel.val "p"
          (.expr [.sym "f", .var "z", .var "y", .sym "k", .sym "k"])] = false :=
      Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _ (by simp [Metta.Atom.vars])
    simp (config := { maxSteps := 1000000 })
      [aliasForkProbePattern, aliasForkProbeQuery,
        aliasForkProbeLeaBindings, encodeModelAtom, encodeModelAtoms,
        hloop, hpLeftLoop, hpRightLoop,
        Metta.matchAtoms, Metta.matchAtomsWith, Metta.matchAll,
        Metta.Bindings.merge, Metta.Bindings.mergeOne,
        Metta.Bindings.addVarBinding, Metta.Bindings.unifyValues,
        Metta.Bindings.reconcileAll, Metta.Bindings.equations,
        Metta.Bindings.relationEquation, Metta.Bindings.equationFuel,
        Metta.Bindings.rebuildFromReconciliation,
        Metta.Bindings.reconciliationAliases,
        Metta.Bindings.restoreAlias,
        Metta.Bindings.rebuildFromSubst, Metta.Bindings.equalitySkeleton,
        Metta.Bindings.ofSubst,
        Metta.Bindings.classValues, Metta.Bindings.eqClassOrdered,
        Metta.Bindings.eqVarsInOrder, Metta.Bindings.eqClass,
        Metta.Bindings.eqClassAux, Metta.Bindings.eqStep,
        Metta.Bindings.lookupVal, Metta.Bindings.addValRaw,
        Metta.Bindings.removeVal,
        Metta.Unify.aliasTrace, Metta.Unify.aliasConstraints,
        Metta.Unify.unifyRounds, Metta.Unify.decomposeAll,
        Metta.Unify.decomposeEq, Metta.Unify.decomposeList,
        Metta.Subst.occurs, Metta.Subst.apply, Metta.Subst.lookup,
        Metta.Subst.extend, Metta.Subst.erase, Metta.Atom.size]

/-- The forked spanning trees carry the same equality classes and complete
binding solution theory. -/
theorem aliasForkProbe_solution_transport :
    LeaBindingSolutionEquiv
      aliasForkProbeHEBindings aliasForkProbeLeaBindings := by
  apply LeaBindingSolutionEquiv.of_value_and_equality_theories
  · intro v value
    constructor
    · intro hmem
      simp [aliasForkProbeLeaBindings] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨.symbol "k", by
          simp [aliasForkProbeHEBindings], rfl⟩
      · exact ⟨.expression
            [.symbol "f", .var "x", .var "x", .var "y", .var "z"],
          by simp [aliasForkProbeHEBindings], rfl⟩
    · rintro ⟨heValue, hmem, rfl⟩
      simp [aliasForkProbeHEBindings] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp [aliasForkProbeLeaBindings, encodeModelAtom, encodeModelAtoms]
      · simp [aliasForkProbeLeaBindings, encodeModelAtom]
  · intro valuation
    constructor
    · intro hhe
      have hxz : valuation "x" = valuation "z" :=
        hhe "x" "z" (by simp [aliasForkProbeHEBindings])
      have hxy : valuation "x" = valuation "y" :=
        hhe "x" "y" (by simp [aliasForkProbeHEBindings])
      intro left right hmem
      have hcases :
          (left = "z" ∧ right = "y") ∨
            (left = "x" ∧ right = "z") := by
        simpa [aliasForkProbeLeaBindings] using hmem
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hxz.symm.trans hxy
      · exact hxz
    · intro hlea
      have hzy : valuation "z" = valuation "y" :=
        hlea "z" "y" (by simp [aliasForkProbeLeaBindings])
      have hxz : valuation "x" = valuation "z" :=
        hlea "x" "z" (by simp [aliasForkProbeLeaBindings])
      intro left right hmem
      have hcases :
          (left = "x" ∧ right = "z") ∨
            (left = "x" ∧ right = "y") := by
        simpa [aliasForkProbeHEBindings] using hmem
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hxz
      · exact hxz.trans hzy

/-- POSITIVE: the strengthened compositional invariant quotients the forked
spanning-tree presentations while retaining the exact provenance of both
stored values. -/
theorem aliasForkProbe_binding_congruence :
    LeaBindingCongruence
      aliasForkProbeHEBindings aliasForkProbeLeaBindings := by
  refine ⟨aliasForkProbe_solution_transport, ?_⟩
  constructor
  · intro key value hmem
    simp [aliasForkProbeHEBindings] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨"p",
        .expr [.sym "f", .var "x", .var "x", .var "y", .var "z"],
        by simp [aliasForkProbeLeaBindings], ?_,
        HELeaAtomClassRel.translation aliasForkProbeHEBindings _⟩
      rw [EqualityClosure.mem_eqClass_iff_reachable]
    · refine ⟨"y", .sym "k", by
        simp [aliasForkProbeLeaBindings], ?_,
        HELeaAtomClassRel.translation aliasForkProbeHEBindings _⟩
      rw [EqualityClosure.mem_eqClass_iff_reachable]
  · intro leaKey leaValue hmem
    simp [aliasForkProbeLeaBindings] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨"y", .symbol "k", by
        simp [aliasForkProbeHEBindings], ?_,
        HELeaAtomClassRel.translation aliasForkProbeHEBindings _⟩
      rw [EqualityClosure.mem_eqClass_iff_reachable]
    · refine ⟨"p",
        .expression [.symbol "f", .var "x", .var "x", .var "y", .var "z"],
        by simp [aliasForkProbeHEBindings], ?_,
        HELeaAtomClassRel.translation aliasForkProbeHEBindings _⟩
      rw [EqualityClosure.mem_eqClass_iff_reachable]

/-- NEGATIVE: direct undirected-edge equality is too strong for recursive
reconciliation even though equality-class closure agrees exactly. -/
theorem aliasForkProbe_not_direct_relation_transport :
    ¬ LeaBindingRelEquiv
      aliasForkProbeHEBindings aliasForkProbeLeaBindings := by
  intro htransport
  have hxy := (htransport.equalities "x" "y").mpr
    (Or.inl (by simp [aliasForkProbeHEBindings]))
  simp [aliasForkProbeLeaBindings] at hxy

private def valueProvenanceProbeHEBase : Bindings :=
  ⟨[("p", .expression [.symbol "f", .var "x"]),
    ("x", .symbol "k"), ("y", .symbol "k")], []⟩

private def valueProvenanceProbeLeaBase : Metta.Bindings :=
  [Metta.BindingRel.val "p" (.expr [.sym "f", .var "y"]),
    Metta.BindingRel.val "x" (.sym "k"),
    Metta.BindingRel.val "y" (.sym "k")]

private def valueProvenanceProbeHEOut : Bindings :=
  ⟨[("p", .expression [.symbol "f", .var "x"]),
    ("x", .symbol "k"), ("y", .symbol "k")], [("x", "z")]⟩

private def valueProvenanceProbeLeaOut : Metta.Bindings :=
  [Metta.BindingRel.eq "y" "z",
    Metta.BindingRel.val "z" (.sym "k"),
    Metta.BindingRel.val "y" (.sym "k"),
    Metta.BindingRel.val "x" (.sym "k"),
    Metta.BindingRel.val "p" (.expr [.sym "f", .var "y"])]

/-- NEGATIVE INVARIANT ORACLE: equality closure plus global equation-solution
theory does not retain which unresolved class variable occurs inside a stored
class value.  The bases below therefore satisfy the current quotient even
though `p` stores `f x` on the HE side and `f y` on the LeaTTa side. -/
theorem valueProvenanceProbe_base_solution_equiv :
    LeaBindingSolutionEquiv
      valueProvenanceProbeHEBase valueProvenanceProbeLeaBase := by
  apply LeaBindingSolutionEquiv.of_theories
  · intro valuation
    simp [HEEqualitySatisfied, LeaEqualitySatisfied,
      valueProvenanceProbeHEBase, valueProvenanceProbeLeaBase]
  · intro valuation
    constructor
    · rintro ⟨hvalues, _hequalities⟩
      have hp := hvalues "p"
        (.expression [.symbol "f", .var "x"])
        (by simp [valueProvenanceProbeHEBase])
      have hx := hvalues "x" (.symbol "k")
        (by simp [valueProvenanceProbeHEBase])
      have hy := hvalues "y" (.symbol "k")
        (by simp [valueProvenanceProbeHEBase])
      refine ⟨?_, ?_⟩
      · intro key value hmem
        simp [valueProvenanceProbeLeaBase] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simpa [encodeModelAtom, encodeModelAtoms, applyClassSolution,
            hx, hy] using hp
        · simpa [encodeModelAtom, applyClassSolution] using hx
        · simpa [encodeModelAtom, applyClassSolution] using hy
      · intro left right hmem
        simp [valueProvenanceProbeLeaBase] at hmem
    · rintro ⟨hvalues, _hequalities⟩
      have hp := hvalues "p" (.expr [.sym "f", .var "y"])
        (by simp [valueProvenanceProbeLeaBase])
      have hx := hvalues "x" (.sym "k")
        (by simp [valueProvenanceProbeLeaBase])
      have hy := hvalues "y" (.sym "k")
        (by simp [valueProvenanceProbeLeaBase])
      refine ⟨?_, ?_⟩
      · intro key value hmem
        simp [valueProvenanceProbeHEBase] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simpa [encodeModelAtom, encodeModelAtoms, applyClassSolution,
            hx, hy] using hp
        · simpa [encodeModelAtom, applyClassSolution] using hx
        · simpa [encodeModelAtom, applyClassSolution] using hy
      · intro left right hmem
        simp [valueProvenanceProbeHEBase] at hmem

/-- The strengthened invariant rejects the provenance-erasing base pair even
before reconciliation: `x` and `y` inhabit distinct equality classes, so the
stored atoms `f x` and `f y` are not class-relative variants. -/
theorem valueProvenanceProbe_base_not_congruence :
    ¬ LeaBindingCongruence
      valueProvenanceProbeHEBase valueProvenanceProbeLeaBase := by
  intro hcongruence
  obtain ⟨leaKey, leaValue, hleaValue, hkeyClass, hatom⟩ :=
    hcongruence.classValues.1 "p"
      (.expression [.symbol "f", .var "x"])
      (by simp [valueProvenanceProbeHEBase])
  have hkey : leaKey = "p" := by
    simpa [valueProvenanceProbeHEBase, Bindings.eqClass,
      Bindings.eqClassAux, Bindings.eqStep] using hkeyClass
  subst leaKey
  have hvalue : leaValue = .expr [.sym "f", .var "y"] := by
    simpa [valueProvenanceProbeLeaBase] using hleaValue
  subst leaValue
  cases hatom with
  | expression hatoms =>
      cases hatoms with
      | cons hsymbol htail =>
          cases hsymbol
          cases htail with
          | cons hvariable hnil =>
              cases hvariable
              rename_i hxy
              have hnot : "y" ∉ valueProvenanceProbeHEBase.eqClass "x" := by
                decide
              exact hnot hxy

/-- Both engines successfully extend the solution-equivalent bases by the
same interface equation `p = f z`, but expose different latent variable
provenance in their equality graphs. -/
theorem valueProvenanceProbe_add_oracles :
    valueProvenanceProbeHEOut ∈
        addVarBinding valueProvenanceProbeHEBase "p"
          (.expression [.symbol "f", .var "z"]) 30 ∧
      Metta.Bindings.addVarBinding valueProvenanceProbeLeaBase "p"
          (.expr [.sym "f", .var "z"]) =
        [valueProvenanceProbeLeaOut] := by
  constructor
  · decide
  · simp (config := { maxSteps := 1000000 })
      [valueProvenanceProbeLeaBase, valueProvenanceProbeLeaOut,
        Metta.Bindings.addVarBinding, Metta.Bindings.unifyValues,
        Metta.Bindings.reconcileAll, Metta.Bindings.equations,
        Metta.Bindings.relationEquation, Metta.Bindings.equationFuel,
        Metta.Bindings.rebuildFromReconciliation,
        Metta.Bindings.reconciliationAliases,
        Metta.Bindings.restoreAlias,
        Metta.Bindings.rebuildFromSubst, Metta.Bindings.equalitySkeleton,
        Metta.Bindings.ofSubst,
        Metta.Bindings.classValues, Metta.Bindings.eqClassOrdered,
        Metta.Bindings.eqVarsInOrder, Metta.Bindings.eqClass,
        Metta.Bindings.eqClassAux, Metta.Bindings.eqStep,
        Metta.Bindings.lookupVal,
        Metta.Unify.aliasTrace, Metta.Unify.aliasConstraints,
        Metta.Unify.unifyRounds, Metta.Unify.decomposeAll,
        Metta.Unify.decomposeEq, Metta.Unify.decomposeList,
        Metta.Subst.occurs, Metta.Subst.apply, Metta.Subst.lookup,
        Metta.Subst.extend, Metta.Subst.erase, Metta.Atom.size]
    split
    · rfl
    · rename_i hnot
      exfalso
      apply hnot
      decide

/-- The successful extensions still have the same complete equation-solution
theory.  The missing information is specifically raw class-value provenance,
not satisfiability. -/
theorem valueProvenanceProbe_output_solution_theory :
    LeaBindingSolutionTheoryEquiv
      valueProvenanceProbeHEOut valueProvenanceProbeLeaOut := by
  exact addVarBinding_solutionTheory_of_successes
    valueProvenanceProbe_base_solution_equiv.solutions
    (by
      intro key value hmem
      simp [valueProvenanceProbeLeaBase] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [MettaAtomNoFloat])
    valueProvenanceProbe_add_oracles.1
    (by
      have hmem : valueProvenanceProbeLeaOut ∈
          Metta.Bindings.addVarBinding valueProvenanceProbeLeaBase "p"
            (.expr [.sym "f", .var "z"]) := by
        rw [valueProvenanceProbe_add_oracles.2]
        simp
      simpa [encodeModelAtom, encodeModelAtoms] using hmem)

/-- NEGATIVE: the current equality-closure plus global-solution invariant is
not preserved by nontrivial value reconciliation.  A compositional invariant
must additionally relate raw class values modulo variables already connected
in the corresponding equality classes. -/
theorem valueProvenanceProbe_output_not_solution_equiv :
    ¬ LeaBindingSolutionEquiv
      valueProvenanceProbeHEOut valueProvenanceProbeLeaOut := by
  intro htransport
  have hxzHE : "z" ∈ valueProvenanceProbeHEOut.eqClass "x" := by
    decide
  have hxzLea := (htransport.classes "x" "z").mp hxzHE
  have : "z" ∉ Metta.Bindings.eqClass valueProvenanceProbeLeaOut "x" := by
    decide
  exact this hxzLea

end Mettapedia.Languages.MeTTa.HE.LeaTTaBridge

/-! ## Isolated solved frames through whole-system reconciliation -/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Metta

/-- Successful decomposition of a reflexive equation creates no constraints.
This allows non-reflexive grounded equality to reject without inventing a
constraint on an otherwise unconstrained variable. -/
theorem decomposeEq_self_success_empty :
    ∀ (atom : Metta.Atom) {constraints : List (String × Metta.Atom)},
      Metta.Unify.decomposeEq atom atom = some constraints → constraints = [] := by
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_
  · intro symbol constraints step
    simpa [Metta.Unify.decomposeEq] using step.symm
  · intro key constraints step
    simpa [Metta.Unify.decomposeEq] using step.symm
  · intro ground constraints step
    simp only [Metta.Unify.decomposeEq] at step
    split at step
    · exact Option.some.inj step.symm
    · contradiction
  · intro atoms ih constraints step
    change Metta.Unify.decomposeList atoms atoms = some constraints at step
    induction atoms generalizing constraints with
    | nil => simpa [Metta.Unify.decomposeList] using step.symm
    | cons head tail tailIH =>
      cases first : Metta.Unify.decomposeEq head head with
      | none => simp [Metta.Unify.decomposeList,first] at step
      | some front =>
        have frontEmpty := ih head (by simp) first
        cases rest : Metta.Unify.decomposeList tail tail with
        | none => simp [Metta.Unify.decomposeList,first,rest] at step
        | some back =>
          have backEmpty := tailIH (fun atom member => ih atom (by simp [member])) rest
          simp [Metta.Unify.decomposeList,first,rest,frontEmpty,backEmpty] at step
          exact step

theorem decomposeEq_var_of_ne_self (key : String) (term : Metta.Atom)
    (different : term ≠ .var key) :
    Metta.Unify.decomposeEq (.var key) term=some [(key,term)] := by
  cases term with
  | var other =>
    have distinct : key ≠ other := fun equal => different (by rw [equal])
    simp [Metta.Unify.decomposeEq,distinct]
  | sym symbol | gnd ground | expr children => rfl

/-- A solved frame stores private keys with fixed values. Its values may
contain public holes, but never another private frame key. -/
structure IsolatedSolveFrame where
  privateKey : String → Prop
  value : String → Metta.Atom
  caller : String → Prop
  private_not_caller : ∀ key, privateKey key → ¬caller key
  value_no_private : ∀ key,privateKey key → ∀ name ∈ (value key).vars,¬privateKey name
  value_no_caller : ∀ key,privateKey key → ∀ name ∈ (value key).vars,¬caller name

namespace IsolatedSolveFrame

def InsideCaller (frame : IsolatedSolveFrame) (atom : Metta.Atom) : Prop :=
  ∀ key ∈ atom.vars,frame.caller key

def Constraint (frame : IsolatedSolveFrame) (key : String) (term : Metta.Atom) : Prop :=
  (frame.privateKey key ∧ term=frame.value key) ∨
    (frame.caller key ∧ frame.InsideCaller term)

/-- The caller's equations and a solved private frame can be interleaved.
Reflexive equations account for repeated copies of an eliminated frame row. -/
def Equation (frame : IsolatedSolveFrame) (left right : Metta.Atom) : Prop :=
  left=right ∨
    (∃ key,frame.privateKey key ∧ left=.var key ∧ right=frame.value key) ∨
    (frame.InsideCaller left ∧ frame.InsideCaller right)

theorem decompose_constraint (frame : IsolatedSolveFrame)
    {left right : Metta.Atom} {constraints : List (String × Metta.Atom)}
    (legal : frame.Equation left right)
    (step : Metta.Unify.decomposeEq left right=some constraints)
    {key : String} {term : Metta.Atom} (present : (key,term)∈constraints) :
    frame.Constraint key term := by
  rcases legal with same | ⟨source,privateSource,rfl,rfl⟩ | ⟨leftInside,rightInside⟩
  · subst right
    rw [decomposeEq_self_success_empty left step] at present
    contradiction
  · have different : frame.value source ≠ .var source := by
      intro same
      exact frame.value_no_private source privateSource source
        (by rw [same]; simp [Metta.Atom.vars]) privateSource
    rw [decomposeEq_var_of_ne_self source (frame.value source) different] at step
    have shape : constraints=[(source,frame.value source)] := Option.some.inj step.symm
    rw [shape,List.mem_singleton,Prod.mk.injEq] at present
    rcases present with ⟨rfl,rfl⟩
    exact Or.inl ⟨privateSource,rfl⟩
  · right
    have support := decomposeEq_constraintVars_subset left right constraints step
    have source : key∈mettaConstraintVars constraints := by
      apply List.mem_flatMap.mpr
      exact ⟨(key,term),present,by simp⟩
    have keyInside := (List.mem_append.mp (support key source)).elim
      (leftInside key) (rightInside key)
    refine ⟨keyInside,?_⟩
    intro name mentioned
    have source : name∈mettaConstraintVars constraints := by
      apply List.mem_flatMap.mpr
      exact ⟨(key,term),present,by simp [mentioned]⟩
    exact (List.mem_append.mp (support name source)).elim
      (leftInside name) (rightInside name)

theorem decomposeAll_constraints (frame : IsolatedSolveFrame)
    {equations : List (Metta.Atom × Metta.Atom)}
    {constraints : List (String × Metta.Atom)}
    (legal : ∀ equation ∈ equations,frame.Equation equation.1 equation.2)
    (step : Metta.Unify.decomposeAll equations=some constraints) :
    ∀ entry ∈ constraints,frame.Constraint entry.1 entry.2 := by
  induction equations generalizing constraints with
  | nil => simp [Metta.Unify.decomposeAll] at step; subst constraints; simp
  | cons equation rest ih =>
    cases first : Metta.Unify.decomposeEq equation.1 equation.2 with
    | none => simp [Metta.Unify.decomposeAll,first] at step
    | some front =>
      cases remaining : Metta.Unify.decomposeAll rest with
      | none => simp [Metta.Unify.decomposeAll,first,remaining] at step
      | some back =>
        have shape : constraints=front++back := by
          simpa [Metta.Unify.decomposeAll,first,remaining] using step.symm
        subst constraints
        intro entry present
        rcases List.mem_append.mp present with inFront | inBack
        · exact frame.decompose_constraint (legal equation (by simp)) first inFront
        · exact ih (fun e member => legal e (by simp [member])) remaining entry inBack

theorem apply_singleton_outside (key : String) (value : Metta.Atom) :
    ∀ (atom : Metta.Atom),key ∉ atom.vars →
      Metta.Subst.apply [(key,value)] atom=atom := by
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_
  · intro symbol _; simp [Metta.Subst.apply]
  · intro other outside
    have different : other ≠ key := by
      intro equal
      exact outside (by simp [Metta.Atom.vars,equal])
    simp [Metta.Subst.apply,Metta.Subst.lookup,different]
  · intro ground _; simp [Metta.Subst.apply]
  · intro atoms ih outside
    simp only [Metta.Subst.apply]
    apply congrArg Metta.Atom.expr
    calc
      atoms.map (Metta.Subst.apply [(key,value)]) = atoms.map id := by
        apply List.map_congr_left
        intro atom present
        apply ih atom present
        intro mentioned
        apply outside
        simp only [Metta.Atom.vars,List.mem_flatten,List.mem_map]
        exact ⟨atom.vars,⟨atom,present,rfl⟩,mentioned⟩
      _ = atoms := List.map_id atoms

theorem caller_apply (frame : IsolatedSolveFrame)
    {key : String} {value atom : Metta.Atom}
    (valueInside : frame.InsideCaller value) (atomInside : frame.InsideCaller atom) :
    frame.InsideCaller (Metta.Subst.apply [(key,value)] atom) := by
  intro name mentioned
  exact (mem_vars_apply_singleton atom mentioned).elim
    (atomInside name) (valueInside name)

theorem constraint_substituted (frame : IsolatedSolveFrame)
    {key other : String} {value term : Metta.Atom}
    (selected : frame.Constraint key value) (remaining : frame.Constraint other term) :
    frame.Equation (Metta.Subst.apply [(key,value)] (.var other))
      (Metta.Subst.apply [(key,value)] term) := by
  rcases selected with ⟨privateKey,rfl⟩ | ⟨callerKey,valueInside⟩
  · rcases remaining with ⟨privateOther,rfl⟩ | ⟨callerOther,termInside⟩
    · have rightFixed : Metta.Subst.apply [(key,frame.value key)] (frame.value other)=
          frame.value other := apply_singleton_outside key (frame.value key)
            (frame.value other) (fun present =>
              frame.value_no_private other privateOther key present privateKey)
      rw [rightFixed]
      by_cases same : other=key
      · subst other
        exact Or.inl (by simp [Metta.Subst.apply,Metta.Subst.lookup])
      · right; left
        refine ⟨other,privateOther,?_,rfl⟩
        simp [Metta.Subst.apply,Metta.Subst.lookup,same]
    · have outsideKey : key ∉ term.vars := fun mentioned =>
        frame.private_not_caller key privateKey (termInside key mentioned)
      have different : other≠key := fun same =>
        frame.private_not_caller key privateKey (same ▸ callerOther)
      rw [apply_singleton_outside key (frame.value key) term outsideKey]
      right; right
      refine ⟨?_,termInside⟩
      simpa [Metta.Subst.apply,Metta.Subst.lookup,different,InsideCaller,Metta.Atom.vars]
        using callerOther
  · rcases remaining with ⟨privateOther,rfl⟩ | ⟨callerOther,termInside⟩
    · have different : other≠key := fun same =>
        frame.private_not_caller other privateOther (same.symm ▸ callerKey)
      have outsideKey : key ∉ (frame.value other).vars := fun mentioned =>
        frame.value_no_caller other privateOther key mentioned callerKey
      right; left
      refine ⟨other,privateOther,?_,?_⟩
      · simp [Metta.Subst.apply,Metta.Subst.lookup,different]
      · exact apply_singleton_outside key value (frame.value other) outsideKey
    · right; right
      exact ⟨frame.caller_apply valueInside (by
        intro name mentioned
        have same : name=other := by simpa [Metta.Atom.vars] using mentioned
        exact same ▸ callerOther),frame.caller_apply valueInside termInside⟩

/-- Robinson elimination cannot turn a public hole into a private assignment
or let a caller constraint acquire an isolated frame's variables. -/
theorem unifyRounds_constraints (frame : IsolatedSolveFrame)
    {fuel : Nat} {equations : List (Metta.Atom × Metta.Atom)}
    {seed result : Metta.Subst}
    (legal : ∀ equation ∈ equations,frame.Equation equation.1 equation.2)
    (seedLegal : ∀ entry ∈ seed,frame.Constraint entry.1 entry.2)
    (step : Metta.Unify.unifyRounds fuel equations seed=some result) :
    ∀ entry ∈ result,frame.Constraint entry.1 entry.2 := by
  induction fuel generalizing equations seed result with
  | zero =>
    cases decomposed : Metta.Unify.decomposeAll equations with
    | none => simp [Metta.Unify.unifyRounds,decomposed] at step
    | some constraints =>
      cases constraints with
      | nil =>
        have same : seed=result := by simpa [Metta.Unify.unifyRounds,decomposed] using step
        exact same ▸ seedLegal
      | cons first rest => simp [Metta.Unify.unifyRounds,decomposed] at step
  | succ fuel ih =>
    cases decomposed : Metta.Unify.decomposeAll equations with
    | none => simp [Metta.Unify.unifyRounds,decomposed] at step
    | some constraints =>
      cases constraints with
      | nil =>
        have same : seed=result := by simpa [Metta.Unify.unifyRounds,decomposed] using step
        exact same ▸ seedLegal
      | cons first rest =>
        rcases first with ⟨key,value⟩
        have constraintsLegal := frame.decomposeAll_constraints legal decomposed
        have selected := constraintsLegal (key,value) (by simp)
        cases occurs : Metta.Subst.occurs key value with
        | true => simp [Metta.Unify.unifyRounds,decomposed,occurs] at step
        | false =>
          apply ih (equations := rest.map fun entry =>
            (Metta.Subst.apply [(key,value)] (.var entry.1),
             Metta.Subst.apply [(key,value)] entry.2))
              (seed := Metta.Subst.extend seed key value) ?_ ?_ ?_
          · intro equation present
            obtain ⟨entry,member,rfl⟩ := List.mem_map.mp present
            exact frame.constraint_substituted selected
              (constraintsLegal entry (by simp [member]))
          · intro entry present
            simp only [Metta.Subst.extend,List.mem_cons,Metta.Subst.erase] at present
            rcases present with rfl | old
            · exact selected
            · exact seedLegal entry (List.mem_of_mem_filter old)
          · simpa only [Metta.Unify.unifyRounds,decomposed,occurs,Bool.false_eq_true,
              ↓reduceIte] using step

theorem aliasConstraints_legal (frame : IsolatedSolveFrame)
    {constraints : List (String × Metta.Atom)}
    (legal : ∀ entry ∈ constraints,frame.Constraint entry.1 entry.2)
    {edge : String × String} (present : edge∈Metta.Unify.aliasConstraints constraints) :
    frame.Constraint edge.1 (.var edge.2) := by
  induction constraints with
  | nil => simp [Metta.Unify.aliasConstraints] at present
  | cons entry rest ih =>
    rcases entry with ⟨key,term⟩
    cases term with
    | var other =>
      simp only [Metta.Unify.aliasConstraints,List.mem_cons] at present
      rcases present with rfl | tail
      · exact legal (key,.var other) (by simp)
      · exact ih (fun entry member => legal entry (by simp [member])) tail
    | sym symbol | gnd ground | expr children =>
      exact ih (fun entry member => legal entry (by simp [member])) present

/-- Alias discovery respects the same frame even before success is known.
The trace cannot connect a caller name to a private slot or public hole. -/
theorem aliasTrace_constraints (frame : IsolatedSolveFrame)
    (fuel : Nat) {equations : List (Metta.Atom × Metta.Atom)}
    (legal : ∀ equation ∈ equations,frame.Equation equation.1 equation.2) :
    ∀ edge ∈ Metta.Unify.aliasTrace fuel equations,frame.Constraint edge.1 (.var edge.2) := by
  induction fuel generalizing equations with
  | zero =>
    cases decomposed : Metta.Unify.decomposeAll equations with
    | none => simp [Metta.Unify.aliasTrace,decomposed]
    | some constraints =>
      simpa only [Metta.Unify.aliasTrace,decomposed] using
        fun edge present => frame.aliasConstraints_legal
          (frame.decomposeAll_constraints legal decomposed) (edge := edge) present
  | succ fuel ih =>
    cases decomposed : Metta.Unify.decomposeAll equations with
    | none => simp [Metta.Unify.aliasTrace,decomposed]
    | some constraints =>
      cases constraints with
      | nil => simp [Metta.Unify.aliasTrace,decomposed]
      | cons first rest =>
        rcases first with ⟨key,value⟩
        have constraintsLegal := frame.decomposeAll_constraints legal decomposed
        have here := fun edge present => frame.aliasConstraints_legal constraintsLegal
          (edge := edge) present
        cases occurs : Metta.Subst.occurs key value with
        | true => simpa only [Metta.Unify.aliasTrace,decomposed,occurs,↓reduceIte] using here
        | false =>
          simp only [Metta.Unify.aliasTrace,decomposed,occurs,Bool.false_eq_true,↓reduceIte]
          intro edge present
          rcases List.mem_append.mp present with current | later
          · exact here edge current
          · apply ih ?_ edge later
            intro equation member
            obtain ⟨entry,entryPresent,rfl⟩ := List.mem_map.mp member
            exact frame.constraint_substituted (constraintsLegal (key,value) (by simp))
              (constraintsLegal entry (by simp [entryPresent]))

def Relation (frame : IsolatedSolveFrame) : Metta.BindingRel → Prop
  | .val key value => frame.Constraint key value
  | .eq left right => frame.Constraint left (.var right)

def BindingsLegal (frame : IsolatedSolveFrame) (bindings : Metta.Bindings) : Prop :=
  ∀ relation ∈ bindings,frame.Relation relation

theorem constraint_equation (frame : IsolatedSolveFrame)
    {key : String} {value : Metta.Atom} (legal : frame.Constraint key value) :
    frame.Equation (.var key) value := by
  rcases legal with ⟨privateKey,rfl⟩ | ⟨callerKey,valueInside⟩
  · exact Or.inr (Or.inl ⟨key,privateKey,rfl,rfl⟩)
  · exact Or.inr (Or.inr ⟨by simpa [InsideCaller,Metta.Atom.vars] using callerKey,valueInside⟩)

theorem binding_equations (frame : IsolatedSolveFrame)
    {bindings : Metta.Bindings} (legal : frame.BindingsLegal bindings) :
    ∀ equation ∈ bindings.equations,frame.Equation equation.1 equation.2 := by
  intro equation present
  obtain ⟨relation,member,rfl⟩ := List.mem_map.mp present
  have good := legal relation member
  cases relation with
  | val key value | eq key value => exact frame.constraint_equation good

theorem reconcileAll_constraints (frame : IsolatedSolveFrame)
    {bindings : Metta.Bindings} {extra : List (Metta.Atom × Metta.Atom)}
    {result : Metta.Subst}
    (legal : frame.BindingsLegal bindings)
    (extraLegal : ∀ equation ∈ extra,frame.Equation equation.1 equation.2)
    (step : Metta.Bindings.reconcileAll bindings extra=some result) :
    ∀ entry ∈ result,frame.Constraint entry.1 entry.2 := by
  apply frame.unifyRounds_constraints ?_ (by simp) step
  intro equation present
  exact (List.mem_append.mp present).elim
    (frame.binding_equations legal equation) (extraLegal equation)

theorem reconciliationAliases_constraints (frame : IsolatedSolveFrame)
    {bindings : Metta.Bindings} (extra : List (Metta.Atom × Metta.Atom)) (result : Metta.Subst)
    (legal : frame.BindingsLegal bindings)
    (extraLegal : ∀ equation ∈ extra,frame.Equation equation.1 equation.2) :
    ∀ edge ∈ Metta.Bindings.reconciliationAliases bindings extra result,
      frame.Constraint edge.1 (.var edge.2) := by
  intro edge present
  rcases List.mem_append.mp present with primary | collisionFirst
  · apply frame.aliasTrace_constraints _ ?_ edge primary
    intro equation member
    exact (List.mem_append.mp member).elim
      (frame.binding_equations legal equation) (extraLegal equation)
  · apply frame.aliasTrace_constraints _ ?_ edge collisionFirst
    intro equation member
    exact (List.mem_append.mp member).elim
      (extraLegal equation) (frame.binding_equations legal equation)

theorem addEqRaw_legal (frame : IsolatedSolveFrame)
    {bindings : Metta.Bindings} {left right : String}
    (legal : frame.BindingsLegal bindings) (edge : frame.Constraint left (.var right)) :
    frame.BindingsLegal (bindings.addEqRaw left right) := by
  unfold Metta.Bindings.addEqRaw
  split
  · exact legal
  · split
    · exact legal
    · intro relation present
      rcases List.mem_cons.mp present with rfl | old
      · exact edge
      · exact legal relation old

theorem addValRaw_legal (frame : IsolatedSolveFrame)
    {bindings : Metta.Bindings} {key : String} {value : Metta.Atom}
    (legal : frame.BindingsLegal bindings) (entry : frame.Constraint key value) :
    frame.BindingsLegal (bindings.addValRaw key value) := by
  intro relation present
  rcases List.mem_cons.mp present with rfl | old
  · exact entry
  · exact legal relation (List.mem_of_mem_filter old)

theorem restoreAlias_legal (frame : IsolatedSolveFrame)
    {bindings : Metta.Bindings} {edge : String × String}
    (legal : frame.BindingsLegal bindings) (entry : frame.Constraint edge.1 (.var edge.2)) :
    frame.BindingsLegal (bindings.restoreAlias edge) := by
  unfold Metta.Bindings.restoreAlias
  split
  · exact legal
  · exact frame.addEqRaw_legal legal entry

theorem equalitySkeleton_legal (frame : IsolatedSolveFrame)
    {bindings : Metta.Bindings} (legal : frame.BindingsLegal bindings) :
    frame.BindingsLegal bindings.equalitySkeleton := by
  induction bindings with
  | nil => simp [Metta.Bindings.equalitySkeleton,BindingsLegal]
  | cons head rest ih =>
    have tail := ih (fun relation member => legal relation (by simp [member]))
    cases head with
    | val key value => exact tail
    | eq left right =>
      intro relation present
      rcases List.mem_cons.mp present with rfl | old
      · exact legal (.eq left right) (by simp)
      · exact tail relation old

theorem restoreAliases_legal (frame : IsolatedSolveFrame)
    (edges : List (String × String)) (bindings : Metta.Bindings)
    (legal : frame.BindingsLegal bindings)
    (rows : ∀ edge∈edges,frame.Constraint edge.1 (.var edge.2)) :
    frame.BindingsLegal (edges.foldl Metta.Bindings.restoreAlias bindings) := by
  induction edges generalizing bindings with
  | nil => exact legal
  | cons edge tail ih =>
    exact ih _ (frame.restoreAlias_legal legal (rows edge (by simp)))
      (fun entry member => rows entry (by simp [member]))

theorem rebuild_legal (frame : IsolatedSolveFrame)
    {candidate source : Metta.Bindings} {extra : List (Metta.Atom × Metta.Atom)}
    {result : Metta.Subst}
    (candidateLegal : frame.BindingsLegal candidate)
    (sourceLegal : frame.BindingsLegal source)
    (extraLegal : ∀ equation ∈ extra,frame.Equation equation.1 equation.2)
    (step : Metta.Bindings.reconcileAll source extra=some result) :
    frame.BindingsLegal (Metta.Bindings.rebuildFromReconciliation candidate source extra result) := by
  have solution := frame.reconcileAll_constraints sourceLegal extraLegal step
  have aliases := frame.reconciliationAliases_constraints extra result sourceLegal extraLegal
  have core : frame.BindingsLegal (Metta.Bindings.rebuildFromSubst candidate result) := by
    intro relation present
    rcases List.mem_append.mp present with old | substituted
    · exact frame.equalitySkeleton_legal candidateLegal relation old
    · obtain ⟨entry,member,rfl⟩ := List.mem_map.mp substituted
      have good := solution entry member
      rcases entry with ⟨key,value⟩
      cases value <;> exact good
  exact frame.restoreAliases_legal _ _ core aliases

theorem addVarEquality_legal (frame : IsolatedSolveFrame)
    {bindings result : Metta.Bindings} {left right : String}
    (legal : frame.BindingsLegal bindings) (edge : frame.Constraint left (.var right))
    (produced : result∈Metta.Bindings.addVarEquality bindings left right) :
    frame.BindingsLegal result := by
  cases unified : Metta.Bindings.unifyValues
      ((bindings.addEqRaw left right).classValues left) with
  | none => simp [Metta.Bindings.addVarEquality,unified] at produced
  | some solution =>
    cases solution with
    | nil =>
      have same : result=bindings.addEqRaw left right := by
        simpa only [Metta.Bindings.addVarEquality,unified,List.mem_singleton] using produced
      rw [same]
      exact frame.addEqRaw_legal legal edge
    | cons first rest =>
      cases reconciled : Metta.Bindings.reconcileAll bindings [(.var left,.var right)] with
      | none => simp [Metta.Bindings.addVarEquality,unified,reconciled] at produced
      | some all =>
        have same : result=Metta.Bindings.rebuildFromReconciliation
            (bindings.addEqRaw left right) bindings [(.var left,.var right)] all := by
          simpa only [Metta.Bindings.addVarEquality,unified,reconciled,List.mem_singleton] using produced
        rw [same]
        exact frame.rebuild_legal (frame.addEqRaw_legal legal edge) legal
          (by intro equation member; rw [List.mem_singleton.mp member]
              exact frame.constraint_equation edge) reconciled

private theorem addVarBinding_nonvar_legal (frame : IsolatedSolveFrame)
    {bindings result : Metta.Bindings} {key : String} {value : Metta.Atom}
    (nonvariable : ∀ other,value≠.var other)
    (legal : frame.BindingsLegal bindings) (entry : frame.Constraint key value)
    (produced : result∈Metta.Bindings.addVarBinding bindings key value) :
    frame.BindingsLegal result := by
  have expanded : Metta.Bindings.addVarBinding bindings key value=
      match bindings.classValues key with
      | [] => [bindings.addValRaw key value]
      | first::rest =>
        match Metta.Bindings.unifyValues (first::(rest++[value])) with
        | none => []
        | some [] => [bindings]
        | some (_::_) =>
          match Metta.Bindings.reconcileAll bindings [(.var key,value)] with
          | none => []
          | some all => [Metta.Bindings.rebuildFromReconciliation bindings bindings
              [(.var key,value)] all] := by
    cases value with
    | var other => exact (nonvariable other rfl).elim
    | sym name | gnd name | expr name =>
      cases values : bindings.classValues key <;>
        simp only [Metta.Bindings.addVarBinding,values,List.cons_append]
      all_goals rfl
  rw [expanded] at produced
  cases values : bindings.classValues key with
  | nil =>
    have same : result=bindings.addValRaw key value := by
      simpa only [values,List.mem_singleton] using produced
    rw [same]
    exact frame.addValRaw_legal legal entry
  | cons first rest =>
    simp only [values] at produced
    cases unified : Metta.Bindings.unifyValues (first::(rest++[value])) with
    | none => simp [unified] at produced
    | some solution =>
      cases solution with
      | nil =>
        have same : result=bindings := by simpa only [unified,List.mem_singleton] using produced
        exact same ▸ legal
      | cons head tail =>
        simp only [unified] at produced
        cases reconciled : Metta.Bindings.reconcileAll bindings [(.var key,value)] with
        | none => simp [reconciled] at produced
        | some all =>
          have same : result=Metta.Bindings.rebuildFromReconciliation bindings bindings
              [(.var key,value)] all := by
            simpa only [reconciled,List.mem_singleton] using produced
          rw [same]
          exact frame.rebuild_legal legal legal
            (by intro equation member; rw [List.mem_singleton.mp member]
                exact frame.constraint_equation entry) reconciled

theorem addVarBinding_legal (frame : IsolatedSolveFrame)
    {bindings result : Metta.Bindings} {key : String} {value : Metta.Atom}
    (legal : frame.BindingsLegal bindings) (entry : frame.Constraint key value)
    (produced : result∈Metta.Bindings.addVarBinding bindings key value) :
    frame.BindingsLegal result := by
  cases value with
  | var other => exact frame.addVarEquality_legal legal entry produced
  | sym name | gnd name | expr name =>
    exact frame.addVarBinding_nonvar_legal (by intro other same; cases same) legal entry produced

theorem mergeOne_legal (frame : IsolatedSolveFrame)
    {seeds : List Metta.Bindings} {relation : Metta.BindingRel} {result : Metta.Bindings}
    (seedLegal : ∀ bindings∈seeds,frame.BindingsLegal bindings)
    (relationLegal : frame.Relation relation)
    (produced : result∈Metta.Bindings.mergeOne seeds relation) :
    frame.BindingsLegal result := by
  obtain ⟨bindings,member,advanced⟩ := List.mem_flatMap.mp produced
  cases relation with
  | val key value => exact frame.addVarBinding_legal (seedLegal bindings member) relationLegal advanced
  | eq left right => exact frame.addVarEquality_legal (seedLegal bindings member) relationLegal advanced

theorem mergeFold_legal (frame : IsolatedSolveFrame)
    (relations : Metta.Bindings) (seeds : List Metta.Bindings)
    (seedLegal : ∀ bindings∈seeds,frame.BindingsLegal bindings)
    (relationsLegal : frame.BindingsLegal relations) :
    ∀ result∈relations.foldl Metta.Bindings.mergeOne seeds,frame.BindingsLegal result := by
  induction relations generalizing seeds with
  | nil => exact seedLegal
  | cons relation rest ih =>
    apply ih
    · intro result member
      exact frame.mergeOne_legal seedLegal (relationsLegal relation (by simp)) member
    · intro row member
      exact relationsLegal row (by simp [member])

/-- The complete native merge respects interleaved fixed private slots and
the caller region. This includes every reconciliation and alias-restoration
branch, without requiring consistent or normalized raw caller records. -/
theorem merge_legal (frame : IsolatedSolveFrame)
    {left right result : Metta.Bindings}
    (leftLegal : frame.BindingsLegal left) (rightLegal : frame.BindingsLegal right)
    (produced : result∈Metta.Bindings.merge left right) :
    frame.BindingsLegal result := by
  exact frame.mergeFold_legal right [left] (by simpa using leftLegal) rightLegal result produced

theorem merge_head_fallback_legal (frame : IsolatedSolveFrame)
    {left right fallback : Metta.Bindings}
    (leftLegal : frame.BindingsLegal left) (rightLegal : frame.BindingsLegal right)
    (fallbackLegal : frame.BindingsLegal fallback) :
    frame.BindingsLegal ((Metta.Bindings.merge left right).head?.getD fallback) := by
  cases merged : Metta.Bindings.merge left right with
  | nil => simpa only [merged,List.head?_nil,Option.getD_none] using fallbackLegal
  | cons result rest =>
    simpa only [merged,List.head?_cons,Option.getD_some] using
      frame.merge_legal leftLegal rightLegal (result := result) (by rw [merged]; simp)

namespace Controls

def openFrame : IsolatedSolveFrame where
  privateKey key := key="pattern" ∨ key="atom" ∨ key="template"
  value key := if key="pattern" then .var "x"
    else if key="atom" then .sym "A" else .expr [.sym "pair",.var "x",.var "y"]
  caller key := key="c" ∨ key="d"
  private_not_caller := by intro key privateKey; rcases privateKey with rfl | rfl | rfl <;> decide
  value_no_private := by
    intro key privateKey
    rcases privateKey with rfl | rfl | rfl <;> simp [Metta.Atom.vars]
  value_no_caller := by
    intro key privateKey
    rcases privateKey with rfl | rfl | rfl <;> simp [Metta.Atom.vars]

def incoming : Metta.Bindings :=
  [.val "c" (.expr [.sym "pair",.var "d"]),.val "d" (.sym "A")]

def localRows : Metta.Bindings :=
  [.eq "pattern" "x",.val "atom" (.sym "A"),
    .val "template" (.expr [.sym "pair",.var "x",.var "y"])]

theorem incoming_legal : openFrame.BindingsLegal incoming := by
  simp [BindingsLegal,incoming,Relation,Constraint,InsideCaller,openFrame,Metta.Atom.vars]

theorem local_legal : openFrame.BindingsLegal localRows := by
  simp [BindingsLegal,localRows,Relation,Constraint,InsideCaller,openFrame,Metta.Atom.vars]

theorem actual_merge_legal (result : Metta.Bindings)
    (produced : result∈Metta.Bindings.merge incoming (localRows++incoming)) :
    openFrame.BindingsLegal result :=
  openFrame.merge_legal incoming_legal
    (by intro relation member
        exact (List.mem_append.mp member).elim (local_legal relation) (incoming_legal relation)) produced

def actualRetained : Metta.Bindings :=
  Metta.Minimal.restrictBnd ["x","y","c","d"]
    ((Metta.Bindings.merge incoming (localRows++incoming)).head?.getD (localRows++incoming))

#guard !(Metta.Bindings.merge incoming (localRows++incoming)).isEmpty
#guard Metta.instantiate actualRetained (.var "x") == .var "x"
#guard Metta.instantiate actualRetained (.var "y") == .var "y"
#guard Metta.instantiate actualRetained (.var "c") == .expr [.sym "pair",.sym "A"]

/-- A caller that assigns a public hole violates the isolated-frame contract;
its different readout is visible, rather than removed by an equality quotient. -/
theorem public_hole_capture_not_legal : ¬openFrame.Relation (.val "x" (.sym "captured")) := by
  simp [Relation,Constraint,InsideCaller,openFrame]

#guard Metta.instantiate
  ((Metta.Bindings.merge [.val "x" (.sym "captured")] localRows).head?.getD []) (.var "x")
    == .sym "captured"

end Controls

end IsolatedSolveFrame
end Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
