import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.MegalodonHOTG.SetTheory
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.MegalodonHOTG.Streams
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ZFSetUniverses
import Mettapedia.TypeTheory.MaterialSets.Hypersets.Streams

/-!
# Hypersets as a class of the package

Over the tower inside the sets, and over the set theory with its rule constants, one family
declares hypersets with no equation:

* `hset : class`
* `hIn : hset → hset → prop`
* `ofSet : set → hset`
* `solve : Π (A : set). (A → A → prop) → A → hset`
* `solveLabelled : Π (A : set). Π (B : set). (A → B → A → prop) → A → hset`

`solve A R a` is the hyperset at the node `a` of the graph `R` on the members of `A`.
The set model at the chain `stages` reads `hset` as the set of codes of the hypersets of the
lower universe, `hIn` as their membership through `codeMem`, `ofSet` as the code of the
hyperset of a set, and `solve` as the code of the decoration of the graph.

Positive example: on the one-member set whose member is related to itself, `solve` is `Ω`,
a member of itself, and the only hyperset `x` with `x = {x}`. The two-member set whose
members are each related to the other gives the same `Ω` at both members, and the two graphs
differ. The stream that repeats one label is `solveLabelled` on a one-node graph; the label
is the hyperset of a set.

On a graph with exactly one edge out of every member, `solveLabelled` and the stream package
read the same process: the codes of the labels along the one path, read as hypersets of sets,
form a stream of the stream package over the hyperset codes (`labelCodeStream`,
`labelCodeStream_mem`), and two such graphs have the same value of `solveLabelled` exactly when
they have the same stream of label codes (`solveLabelledValue_eq_iff_labelCodeStream_eq`).

Negative example: `Ω` is the image under `ofSet` of no set. A package that declares a set `x`
together with a proof of `In x x` has no set model at the reading of the sets, while `solve`
gives such an `x` among the hypersets. Membership induction holds for the images of sets and
fails for hypersets, at `Ω`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace MegalodonHOTG

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open HSet
open ZFSetUniverseClosure (Closed CofinalInaccessibles univOf univOf_closed mem_univOf)
open ZFSetUniverseLift (carrierCode mem_carrierCode lift lift_mem_lift lift_empty lift_singleton
  lift_unorderedPair lowerValue lift_lowerValue lowerValue_lift carrierCode_transitive
  univOf_mem_carrierCode)
open ZFSetInterpretation (universeSet)
open ZFSetDependentProducts (graph graph_congr)
open ZFSetTraceProducts (traceLam traceApp tracePiSet traceApp_graph_beta traceApp_empty)
open ZFSetTraceProofDecoding (truthCode mem_truthCode)

universe u

/-! ## A graph on the members of a lifted set -/

section GraphReading

/-- The nodes of a set of the next universe: the small copy of the members of its lower value. -/
abbrev nodeSetOf (A : ZFSet.{u + 1}) : Type u :=
  Shrink.{u} (lowerValue A)

/-- The member of the next universe named by a small node. -/
noncomputable def upperNode (A : ZFSet.{u + 1}) (i : nodeSetOf A) : ZFSet.{u + 1} :=
  lift ((equivShrink.{u} (lowerValue A)).symm i).1

/-- A member of a lifted set, as a small node. -/
noncomputable def nodeOfMember {A a : ZFSet.{u + 1}} (hA : A ∈ carrierCode.{u}) (ha : a ∈ A) :
    nodeSetOf A :=
  equivShrink.{u} (lowerValue A) ⟨lowerValue a, by
    have haC : a ∈ carrierCode := carrierCode_transitive A hA ha
    rw [← lift_mem_lift, lift_lowerValue haC, lift_lowerValue hA]
    exact ha⟩

/-- The small node of a member names that member. -/
theorem upperNode_nodeOfMember {A a : ZFSet.{u + 1}} (hA : A ∈ carrierCode.{u}) (ha : a ∈ A) :
    upperNode A (nodeOfMember hA ha) = a := by
  unfold upperNode nodeOfMember
  rw [Equiv.symm_apply_apply]
  exact lift_lowerValue (carrierCode_transitive A hA ha)

/-- A small node names a member of the lifted set. -/
theorem upperNode_mem {A : ZFSet.{u + 1}} (hA : A ∈ carrierCode.{u}) (i : nodeSetOf A) :
    upperNode A i ∈ A := by
  unfold upperNode
  have hmem : lift ((equivShrink.{u} (lowerValue A)).symm i).1 ∈ lift (lowerValue A) :=
    lift_mem_lift.mpr ((equivShrink.{u} (lowerValue A)).symm i).2
  rwa [lift_lowerValue hA] at hmem

/-- The small node of the member named by a small node is that node. -/
theorem nodeOfMember_upperNode {A : ZFSet.{u + 1}} (hA : A ∈ carrierCode.{u}) (i : nodeSetOf A) :
    nodeOfMember hA (upperNode_mem hA i) = i := by
  unfold nodeOfMember upperNode
  exact (congrArg (equivShrink.{u} (lowerValue A))
      (Subtype.ext (lowerValue_lift ((equivShrink.{u} (lowerValue A)).symm i).1))).trans
    (Equiv.apply_symm_apply _ i)

/-- The edge relation a trace relation gives on the small nodes. -/
def relOf (A R : ZFSet.{u + 1}) (i j : nodeSetOf A) : Prop :=
  (∅ : ZFSet.{u + 1}) ∈ traceApp (traceApp R (upperNode A i)) (upperNode A j)

/-- The edge relation, read on members. -/
theorem relOf_iff {A R a b : ZFSet.{u + 1}} (hA : A ∈ carrierCode.{u}) (ha : a ∈ A) (hb : b ∈ A) :
    relOf A R (nodeOfMember hA ha) (nodeOfMember hA hb) ↔
      (∅ : ZFSet.{u + 1}) ∈ traceApp (traceApp R a) b := by
  unfold relOf
  rw [upperNode_nodeOfMember hA ha, upperNode_nodeOfMember hA hb]

/-- The code of the decoration of `R` at the member `a`, and the empty set outside the domain. -/
noncomputable def solveCode (A R a : ZFSet.{u + 1}) : ZFSet.{u + 1} :=
  @dite _ (A ∈ carrierCode.{u} ∧ a ∈ A) (Classical.propDecidable _)
    (fun h => code (decorate (relOf A R) (nodeOfMember h.1 h.2)))
    (fun _ => ∅)

/-- On a member of a lifted set, `solveCode` is the code of the decoration. -/
theorem solveCode_eq {A R a : ZFSet.{u + 1}} (hA : A ∈ carrierCode.{u}) (ha : a ∈ A) :
    solveCode A R a = code (decorate (relOf A R) (nodeOfMember hA ha)) := by
  unfold solveCode
  rw [dif_pos (h := Classical.propDecidable _) ⟨hA, ha⟩]

/-- The code of a decoration is a hyperset code. -/
theorem solveCode_mem {A R a : ZFSet.{u + 1}} (hA : A ∈ carrierCode.{u}) (ha : a ∈ A) :
    solveCode A R a ∈ hsetCode := by
  rw [solveCode_eq hA ha]
  exact mem_hsetCode.mpr ⟨decorate (relOf A R) (nodeOfMember hA ha), rfl⟩

/-- Decoding `solveCode` returns the decoration. -/
theorem decode_solveCode {A R a : ZFSet.{u + 1}} (hA : A ∈ carrierCode.{u}) (ha : a ∈ A) :
    decodeHSet (solveCode A R a) = decorate (relOf A R) (nodeOfMember hA ha) := by
  rw [solveCode_eq hA ha, decodeHSet_code]

/-- **Anti-foundation for `solve`**: the members at `a` are the solutions at the children of `a`. -/
theorem solve_members {A R a : ZFSet.{u + 1}} (hA : A ∈ carrierCode.{u}) (ha : a ∈ A) {z : HSet.{u}} :
    z ∈ decodeHSet (solveCode A R a) ↔
      ∃ b, b ∈ A ∧ (∅ : ZFSet.{u + 1}) ∈ traceApp (traceApp R a) b ∧
        z = decodeHSet (solveCode A R b) := by
  rw [decode_solveCode hA ha, mem_decorate]
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨upperNode A j, upperNode_mem hA j, ?_, ?_⟩
    · unfold relOf at hj
      rw [upperNode_nodeOfMember hA ha] at hj
      exact hj
    · rw [decode_solveCode hA (upperNode_mem hA j), nodeOfMember_upperNode hA j]
  · rintro ⟨b, hb, hrel, rfl⟩
    refine ⟨nodeOfMember hA hb, ?_, ?_⟩
    · unfold relOf
      rw [upperNode_nodeOfMember hA ha, upperNode_nodeOfMember hA hb]
      exact hrel
    · rw [decode_solveCode hA hb]

/-- **Anti-foundation, uniqueness**: a family with the membership of `solve` is `solve`. -/
theorem solve_unique {A R : ZFSet.{u + 1}} (hA : A ∈ carrierCode.{u}) (d : ZFSet.{u + 1} → HSet.{u})
    (hd : ∀ a, a ∈ A → ∀ y : HSet.{u}, y ∈ d a ↔
      ∃ b, b ∈ A ∧ (∅ : ZFSet.{u + 1}) ∈ traceApp (traceApp R a) b ∧ y = d b) :
    ∀ a, a ∈ A → d a = decodeHSet (solveCode A R a) := by
  intro a ha
  let δ : nodeSetOf A → HSet.{u} := fun i => d (upperNode A i)
  have hδ : IsDecoration (relOf A R) δ := by
    intro i y
    rw [hd (upperNode A i) (upperNode_mem hA i)]
    constructor
    · rintro ⟨b, hb, hrel, rfl⟩
      refine ⟨nodeOfMember hA hb, ?_, ?_⟩
      · unfold relOf
        rw [upperNode_nodeOfMember hA hb]
        exact hrel
      · simp only [δ]
        rw [upperNode_nodeOfMember hA hb]
    · rintro ⟨j, hj, he⟩
      refine ⟨upperNode A j, upperNode_mem hA j, ?_, ?_⟩
      · unfold relOf at hj
        exact hj
      · simpa only [δ] using he.symm
  rw [decode_solveCode hA ha, ← congrFun hδ.eq_decorate (nodeOfMember hA ha)]
  simp only [δ]
  rw [upperNode_nodeOfMember hA ha]

/-- A graph in which every node has a child is decorated by `Ω` at every node. -/
theorem decorate_quineAtom_of_child {α : Type u} {r : α → α → Prop} (child : ∀ i, ∃ j, r i j)
    (i : α) : decorate r i = quineAtom := by
  have hd : IsDecoration r (fun _ => quineAtom) := by
    intro a y
    rw [mem_quineAtom]
    constructor
    · intro hy
      obtain ⟨j, hj⟩ := child a
      exact ⟨j, hj, hy.symm⟩
    · rintro ⟨_, _, hy⟩
      exact hy.symm
  exact (congrFun hd.eq_decorate i).symm

/-- The trace relation that relates every member of `A` to every member. -/
noncomputable def totalRel (A : ZFSet.{u + 1}) : ZFSet.{u + 1} :=
  traceLam (graph A fun _ => traceLam (graph A fun _ => truthCode.{u + 1} True))

/-- A total trace relation holds on every pair of small nodes. -/
theorem totalRel_rel {A : ZFSet.{u + 1}} (hA : A ∈ carrierCode.{u}) (i j : nodeSetOf A) :
    relOf A (totalRel A) i j := by
  unfold relOf totalRel
  rw [traceApp_graph_beta _ (upperNode_mem hA i), traceApp_graph_beta _ (upperNode_mem hA j)]
  exact (mem_truthCode True _).mpr ⟨rfl, trivial⟩

/-- Every node of a total trace relation has a child. -/
theorem totalRel_child {A : ZFSet.{u + 1}} (hA : A ∈ carrierCode.{u}) (i : nodeSetOf A) :
    ∃ j, relOf A (totalRel A) i j :=
  ⟨i, totalRel_rel hA i i⟩

/-- The one-member set of the lower universe whose member is the empty set. -/
def oneLower : ZFSet.{u} := {∅}

/-- The one-member set, lifted. -/
def oneSet : ZFSet.{u + 1} := lift oneLower

/-- The lifted one-member set is the singleton of the empty set. -/
theorem oneSet_spec : oneSet.{u} = {∅} := by
  unfold oneSet oneLower
  rw [lift_singleton, lift_empty]

/-- The empty set is the member of the one-member set. -/
theorem onePoint_mem : (∅ : ZFSet.{u + 1}) ∈ oneSet := by
  rw [oneSet_spec]
  exact ZFSet.mem_singleton.mpr rfl

/-- The one-member set is a lifted set. -/
theorem oneSet_carrier : oneSet.{u} ∈ carrierCode.{u} :=
  mem_carrierCode.mpr ⟨oneLower, rfl⟩

/-- **On the one-member loop, `solve` is the code of `Ω`.** -/
theorem loop_solveCode : solveCode oneSet (totalRel oneSet) ∅ = code quineAtom.{u} := by
  rw [solveCode_eq oneSet_carrier onePoint_mem]
  rw [decorate_quineAtom_of_child (totalRel_child oneSet_carrier)]

/-- The code of `Ω` is a member of itself. -/
theorem loop_codeMem_self :
    codeMem (solveCode oneSet (totalRel oneSet) ∅) (solveCode oneSet (totalRel oneSet) ∅) := by
  rw [loop_solveCode, codeMem_code]
  exact quineAtom_mem_self

/-- The two-member set of the lower universe, the empty set and its singleton. -/
def twoLower : ZFSet.{u} := {∅, {∅}}

/-- The two-member set, lifted. -/
def twoSet : ZFSet.{u + 1} := lift twoLower

/-- The lifted two-member set is the pair of the empty set and its singleton. -/
theorem twoSet_spec : twoSet.{u} = ({∅, {∅}} : ZFSet.{u + 1}) := by
  unfold twoSet twoLower
  rw [lift_unorderedPair, lift_singleton, lift_empty]

/-- The members of the two-member set are the empty set and its singleton. -/
theorem two_mem_iff {x : ZFSet.{u + 1}} : x ∈ twoSet ↔ x = ∅ ∨ x = {∅} := by
  rw [twoSet_spec, ZFSet.mem_pair]

/-- The two-member set is a lifted set. -/
theorem twoSet_carrier : twoSet.{u} ∈ carrierCode.{u} :=
  mem_carrierCode.mpr ⟨twoLower, rfl⟩

/-- The other member of the two-member set. -/
noncomputable def other (x : ZFSet.{u + 1}) : ZFSet.{u + 1} :=
  @dite _ (x = ∅) (Classical.propDecidable _) (fun _ => {∅}) (fun _ => ∅)

/-- The other member of the empty set is its singleton. -/
theorem other_empty : other.{u} ∅ = {∅} := by
  unfold other
  rw [dif_pos (h := Classical.propDecidable _) rfl]

/-- The singleton of the empty set differs from the empty set. -/
theorem singleton_empty_ne : ({∅} : ZFSet.{u + 1}) ≠ ∅ := by
  intro h
  have mem : (∅ : ZFSet.{u + 1}) ∈ ({∅} : ZFSet.{u + 1}) := ZFSet.mem_singleton.mpr rfl
  rw [h] at mem
  exact ZFSet.notMem_empty _ mem

/-- The other member of the singleton is the empty set. -/
theorem other_singleton : other.{u} {∅} = ∅ := by
  unfold other
  rw [dif_neg (h := Classical.propDecidable _) singleton_empty_ne]

/-- The other member of a member is a member. -/
theorem other_mem {x : ZFSet.{u + 1}} (hx : x ∈ twoSet) : other x ∈ twoSet := by
  rcases two_mem_iff.mp hx with rfl | rfl
  · rw [other_empty, two_mem_iff]
    exact Or.inr rfl
  · rw [other_singleton, two_mem_iff]
    exact Or.inl rfl

/-- The trace relation that sends each member of the two-member set to the other. -/
noncomputable def swapRel : ZFSet.{u + 1} :=
  traceLam (graph twoSet fun x => traceLam (graph twoSet fun y => truthCode.{u + 1} (y = other x)))

/-- The swap relation relates each small node to the node of the other member. -/
theorem swap_rel_other (i : nodeSetOf twoSet) :
    relOf twoSet swapRel i (nodeOfMember twoSet_carrier (other_mem (upperNode_mem twoSet_carrier i))) := by
  unfold relOf swapRel
  have hx : upperNode twoSet i ∈ twoSet := upperNode_mem twoSet_carrier i
  rw [traceApp_graph_beta _ hx]
  have hy : other (upperNode twoSet i) ∈ twoSet := other_mem hx
  rw [traceApp_graph_beta _ (by rw [upperNode_nodeOfMember twoSet_carrier hy]; exact hy)]
  rw [upperNode_nodeOfMember twoSet_carrier hy]
  exact (mem_truthCode _ _).mpr ⟨rfl, rfl⟩

/-- Every node of the swap relation has a child. -/
theorem swap_child (i : nodeSetOf twoSet) : ∃ j, relOf twoSet swapRel i j :=
  ⟨nodeOfMember twoSet_carrier (other_mem (upperNode_mem twoSet_carrier i)), swap_rel_other i⟩

/-- **On the two-member swap, `solve` is the code of `Ω` at every member.** -/
theorem swap_solveCode {a : ZFSet.{u + 1}} (ha : a ∈ twoSet) :
    solveCode twoSet swapRel a = code quineAtom.{u} := by
  rw [solveCode_eq twoSet_carrier ha]
  rw [decorate_quineAtom_of_child swap_child]

/-- The one-member set and the two-member set differ. -/
theorem oneSet_ne_twoSet : oneSet.{u} ≠ twoSet := by
  intro h
  have mem : ({∅} : ZFSet.{u + 1}) ∈ twoSet := two_mem_iff.mpr (Or.inr rfl)
  rw [← h, oneSet_spec, ZFSet.mem_singleton] at mem
  exact singleton_empty_ne mem

/-- The one-member loop relates its member to itself. -/
theorem loop_self_edge :
    (∅ : ZFSet.{u + 1}) ∈ traceApp (traceApp (totalRel oneSet) ∅) ∅ := by
  unfold totalRel
  rw [traceApp_graph_beta _ onePoint_mem, traceApp_graph_beta _ onePoint_mem]
  exact (mem_truthCode True _).mpr ⟨rfl, trivial⟩

/-- The swap relation does not relate the empty set to itself. -/
theorem swap_no_self_edge : (∅ : ZFSet.{u + 1}) ∉ traceApp (traceApp swapRel ∅) ∅ := by
  unfold swapRel
  have hempty : (∅ : ZFSet.{u + 1}) ∈ twoSet := two_mem_iff.mpr (Or.inl rfl)
  have outer : traceApp (traceLam (graph twoSet fun x =>
      traceLam (graph twoSet fun y => truthCode.{u + 1} (y = other x)))) ∅ =
      traceLam (graph twoSet fun y => truthCode.{u + 1} (y = other ∅)) :=
    traceApp_graph_beta _ hempty
  rw [outer]
  have inner : traceApp (traceLam (graph twoSet fun y => truthCode.{u + 1} (y = other ∅))) ∅ =
      truthCode.{u + 1} (∅ = other ∅) :=
    traceApp_graph_beta _ hempty
  rw [inner]
  intro h
  have eq := (mem_truthCode _ _).mp h
  rw [other_empty] at eq
  exact singleton_empty_ne eq.2.symm

/-- **The loop and the swap are different graphs**, and both solutions are the code of `Ω`. -/
theorem loop_rel_ne_swap : totalRel oneSet ≠ swapRel := by
  intro h
  exact swap_no_self_edge (h ▸ loop_self_edge)

/-- `ofSet` preserves and reflects membership, on codes. -/
theorem ofSet_mem_iff {x y : ZFSet.{u}} :
    codeMem (code (ofZFSet x)) (code (ofZFSet y)) ↔ y ∈ x := by
  rw [codeMem_code, ofZFSet_mem_ofZFSet_iff]

/-- `ofSet` is injective, on codes. -/
theorem ofSet_code_injective {x y : ZFSet.{u}} (h : code (ofZFSet x) = code (ofZFSet y)) : x = y :=
  ofZFSet_injective (code_injective h)

/-- A hyperset is the image of a set exactly when it is well-founded. -/
theorem ofSet_image_iff_wf {x : HSet.{u}} : (∃ a : ZFSet.{u}, x = ofZFSet a) ↔ x.WF := by
  constructor
  · rintro ⟨a, rfl⟩
    exact wf_ofZFSet a
  · intro hx
    exact ⟨toZFSet x, (ofZFSet_toZFSet_of_wf hx).symm⟩

/-- The code of a hyperset is the code of a set exactly when the hyperset is well-founded. -/
theorem code_ofSet_iff_wf {x : HSet.{u}} :
    (∃ a : ZFSet.{u}, code x = code (ofZFSet a)) ↔ x.WF := by
  constructor
  · rintro ⟨a, h⟩
    rw [code_injective h]
    exact wf_ofZFSet a
  · intro hx
    exact ⟨toZFSet x, congrArg code (ofZFSet_toZFSet_of_wf hx).symm⟩

/-- A code equals the code of its decoding. -/
theorem code_of_decode {y : ZFSet.{u + 1}} (hy : y ∈ hsetCode) : code (decodeHSet y) = y := by
  obtain ⟨x, rfl⟩ := mem_hsetCode.mp hy
  rw [decodeHSet_code]

/-- The only code of a hyperset `x` with `x = {x}` is the code of `Ω`. -/
theorem code_singleton_self_iff {y : ZFSet.{u + 1}} (hy : y ∈ hsetCode) :
    decodeHSet y = {decodeHSet y} ↔ y = code quineAtom.{u} := by
  rw [eq_singleton_self_iff]
  constructor
  · intro h
    rw [← code_of_decode hy, h]
  · intro h
    rw [h, decodeHSet_code]

/-- **Membership induction holds for the images of sets.** -/
theorem ofSet_induction (P : HSet.{u} → Prop)
    (step : ∀ a : ZFSet.{u}, (∀ b : ZFSet.{u}, b ∈ a → P (ofZFSet b)) → P (ofZFSet a))
    (a : ZFSet.{u}) : P (ofZFSet a) :=
  ZFSet.inductionOn (p := fun z => P (ofZFSet z)) a fun x hx => step x hx

/-- **Membership induction fails for hypersets**: it fails at `Ω`, which is a member of itself. -/
theorem not_hset_induction :
    ¬ ∀ P : HSet.{u} → Prop, (∀ x, (∀ y, y ∈ x → P y) → P x) → ∀ x, P x := by
  intro ind
  have step : ∀ x : HSet.{u}, (∀ y : HSet.{u}, y ∈ x → y ∉ y) → x ∉ x := by
    intro x hx hxx
    exact hx x hxx hxx
  exact (ind (fun x => x ∉ x) step quineAtom) quineAtom_mem_self

/-- Membership induction fails for `codeMem` on the set of hyperset codes, at the code of `Ω`. -/
theorem not_codeMem_induction :
    ¬ ∀ P : ZFSet.{u + 1} → Prop,
      (∀ x, x ∈ hsetCode → (∀ y, codeMem x y → y ∈ hsetCode → P y) → P x) →
        ∀ x, x ∈ hsetCode → P x := by
  intro ind
  have mem : code quineAtom.{u} ∈ hsetCode := mem_hsetCode.mpr ⟨quineAtom, rfl⟩
  have self : codeMem (code quineAtom.{u}) (code quineAtom) := codeMem_code.mpr quineAtom_mem_self
  have step : ∀ x, x ∈ hsetCode →
      (∀ y, codeMem x y → y ∈ hsetCode → ¬ codeMem y y) → ¬ codeMem x x := by
    intro x hx hstep hxx
    exact hstep x hxx hx hxx
  exact ind (fun x => ¬ codeMem x x) step (code quineAtom) mem self

/-- The code of `Ω` is the code of no set. -/
theorem quineAtom_ne_ofSet (a : ZFSet.{u}) : code quineAtom.{u} ≠ code (ofZFSet a) :=
  code_quineAtom_ne_ofZFSet a

end GraphReading

/-! ## The values of the constants, read on codes -/

section Values

/-- The value of `hset`: the set of all hyperset codes. -/
noncomputable def hsetValue : ZFSet.{u + 1} := hsetCode

/-- The value of `hIn`: membership of hypersets, through `codeMem`. -/
noncomputable def hInValue : ZFSet.{u + 1} :=
  traceLam (graph hsetCode fun x => traceLam (graph hsetCode fun y => truthCode.{u + 1} (codeMem x y)))

/-- The value of `ofSet`: the code of the hyperset of the lower set. -/
noncomputable def ofSetValue : ZFSet.{u + 1} :=
  traceLam (graph carrierCode.{u} fun a => code (ofZFSet (lowerValue a)))

/-- The value of `solve`: the code of the decoration of the graph at the member. -/
noncomputable def solveValue : ZFSet.{u + 1} :=
  traceLam (graph carrierCode.{u} fun A =>
    traceLam (graph (tracePiSet A fun _ => tracePiSet A fun _ => truthValues.{u + 1}) fun R =>
      traceLam (graph A fun a => solveCode A R a)))

/-- `hIn` at two hyperset codes is the truth value of `codeMem`. -/
theorem hInValue_apply {x y : ZFSet.{u + 1}} (hx : x ∈ hsetCode) (hy : y ∈ hsetCode) :
    traceApp (traceApp hInValue x) y = truthCode.{u + 1} (codeMem x y) := by
  unfold hInValue
  rw [traceApp_graph_beta _ hx, traceApp_graph_beta _ hy]

/-- `ofSet` at a lifted set is the code of the hyperset of its lower value. -/
theorem ofSetValue_apply {a : ZFSet.{u + 1}} (ha : a ∈ carrierCode.{u}) :
    traceApp ofSetValue a = code (ofZFSet (lowerValue a)) := by
  unfold ofSetValue
  rw [traceApp_graph_beta _ ha]

/-- `ofSet` at the lift of a set is the code of the hyperset of that set. -/
theorem ofSetValue_lift (x : ZFSet.{u}) :
    traceApp ofSetValue (lift x) = code (ofZFSet x) := by
  rw [ofSetValue_apply (mem_carrierCode.mpr ⟨x, rfl⟩), lowerValue_lift]

/-- A total trace relation is a relation on the members. -/
theorem totalRel_mem (A : ZFSet.{u + 1}) :
    totalRel A ∈ tracePiSet A fun _ => tracePiSet A fun _ => truthValues.{u + 1} := by
  unfold totalRel
  exact traceLam_graph_mem fun _ _ => traceLam_graph_mem fun _ _ => truthCode_mem_truthValues _

/-- The swap relation is a relation on the two members. -/
theorem swapRel_mem :
    swapRel ∈ tracePiSet twoSet fun _ => tracePiSet twoSet fun _ => truthValues.{u + 1} := by
  unfold swapRel
  exact traceLam_graph_mem fun _ _ => traceLam_graph_mem fun _ _ => truthCode_mem_truthValues _

/-- `solve` at a member of a lifted set is `solveCode`. -/
theorem solveValue_apply {A R a : ZFSet.{u + 1}} (hA : A ∈ carrierCode.{u})
    (hR : R ∈ tracePiSet A fun _ => tracePiSet A fun _ => truthValues.{u + 1}) (ha : a ∈ A) :
    traceApp (traceApp (traceApp solveValue A) R) a = solveCode A R a := by
  unfold solveValue
  rw [traceApp_graph_beta _ hA, traceApp_graph_beta _ hR, traceApp_graph_beta _ ha]

/-- On the one-member loop, the value of `solve` is the code of `Ω`. -/
theorem loop_solveValue :
    traceApp (traceApp (traceApp solveValue oneSet) (totalRel oneSet)) ∅ = code quineAtom.{u} := by
  rw [solveValue_apply oneSet_carrier (totalRel_mem oneSet) onePoint_mem, loop_solveCode]

/-- On the two-member swap, the value of `solve` is the code of `Ω` at every member. -/
theorem swap_solveValue {a : ZFSet.{u + 1}} (ha : a ∈ twoSet) :
    traceApp (traceApp (traceApp solveValue twoSet) swapRel) a = code quineAtom.{u} := by
  rw [solveValue_apply twoSet_carrier swapRel_mem ha, swap_solveCode ha]

/-- The loop is a member of itself through the value of `hIn`. -/
theorem loop_hIn_value :
    (∅ : ZFSet.{u + 1}) ∈ traceApp (traceApp hInValue (solveCode oneSet (totalRel oneSet) ∅))
      (solveCode oneSet (totalRel oneSet) ∅) := by
  rw [hInValue_apply (solveCode_mem oneSet_carrier onePoint_mem)
    (solveCode_mem oneSet_carrier onePoint_mem)]
  exact (mem_truthCode _ _).mpr ⟨rfl, loop_codeMem_self⟩

end Values

/-! ## A labelled graph, and the stream that repeats one label -/

section Labelled

/-- The edge relation a labelled trace relation gives on the small nodes. -/
def labelRel (A B R : ZFSet.{u + 1}) (i : nodeSetOf A) (j : nodeSetOf B) (k : nodeSetOf A) :
    Prop :=
  (∅ : ZFSet.{u + 1}) ∈
    traceApp (traceApp (traceApp R (upperNode A i)) (upperNode B j)) (upperNode A k)

/-- The label a small node of the label set names: the hyperset of its lower set. -/
noncomputable def labelOf (B : ZFSet.{u + 1}) (j : nodeSetOf B) : HSet.{u} :=
  ofZFSet (lowerValue (upperNode B j))

/-- The code of the labelled decoration of `R` at the member `a`, and the empty set outside. -/
noncomputable def solveLabelledCode (A B R a : ZFSet.{u + 1}) : ZFSet.{u + 1} :=
  @dite _ (A ∈ carrierCode.{u} ∧ B ∈ carrierCode.{u} ∧ a ∈ A) (Classical.propDecidable _)
    (fun h => code (decorateLabelled (labelRel A B R) (labelOf B) (nodeOfMember h.1 h.2.2)))
    (fun _ => ∅)

/-- On members of lifted sets, `solveLabelledCode` is the code of the labelled decoration. -/
theorem solveLabelledCode_eq {A B R a : ZFSet.{u + 1}} (hA : A ∈ carrierCode.{u})
    (hB : B ∈ carrierCode.{u}) (ha : a ∈ A) :
    solveLabelledCode A B R a =
      code (decorateLabelled (labelRel A B R) (labelOf B) (nodeOfMember hA ha)) := by
  unfold solveLabelledCode
  rw [dif_pos (h := Classical.propDecidable _) ⟨hA, hB, ha⟩]

/-- The code of a labelled decoration is a hyperset code. -/
theorem solveLabelledCode_mem {A B R a : ZFSet.{u + 1}} (hA : A ∈ carrierCode.{u})
    (hB : B ∈ carrierCode.{u}) (ha : a ∈ A) : solveLabelledCode A B R a ∈ hsetCode := by
  rw [solveLabelledCode_eq hA hB ha]
  exact mem_hsetCode.mpr ⟨decorateLabelled (labelRel A B R) (labelOf B) (nodeOfMember hA ha), rfl⟩

/-- The value of `solveLabelled`. -/
noncomputable def solveLabelledValue : ZFSet.{u + 1} :=
  traceLam (graph carrierCode.{u} fun A =>
    traceLam (graph carrierCode.{u} fun B =>
      traceLam (graph (tracePiSet A fun _ => tracePiSet B fun _ =>
        tracePiSet A fun _ => truthValues.{u + 1}) fun R =>
        traceLam (graph A fun a => solveLabelledCode A B R a))))

/-- `solveLabelled` at members of lifted sets is `solveLabelledCode`. -/
theorem solveLabelledValue_apply {A B R a : ZFSet.{u + 1}} (hA : A ∈ carrierCode.{u})
    (hB : B ∈ carrierCode.{u})
    (hR : R ∈ tracePiSet A fun _ => tracePiSet B fun _ => tracePiSet A fun _ => truthValues.{u + 1})
    (ha : a ∈ A) :
    traceApp (traceApp (traceApp (traceApp solveLabelledValue A) B) R) a =
      solveLabelledCode A B R a := by
  unfold solveLabelledValue
  rw [traceApp_graph_beta _ hA, traceApp_graph_beta _ hB, traceApp_graph_beta _ hR,
    traceApp_graph_beta _ ha]

/-- The one-member set of labels whose member is `b`, lifted. -/
def labelSet (b : ZFSet.{u}) : ZFSet.{u + 1} := lift {b}

/-- The lifted label set is the singleton of the lift of `b`. -/
theorem labelSet_spec (b : ZFSet.{u}) : labelSet b = {lift b} := by
  unfold labelSet
  rw [lift_singleton]

/-- The label set is a lifted set. -/
theorem labelSet_carrier (b : ZFSet.{u}) : labelSet b ∈ carrierCode.{u} :=
  mem_carrierCode.mpr ⟨{b}, rfl⟩

/-- The lift of `b` is the member of the label set. -/
theorem labelPoint_mem (b : ZFSet.{u}) : lift b ∈ labelSet b := by
  rw [labelSet_spec, ZFSet.mem_singleton]

/-- Every small node of the label set names `b`. -/
theorem labelOf_labelSet (b : ZFSet.{u}) (j : nodeSetOf (labelSet b)) :
    labelOf (labelSet b) j = ofZFSet b := by
  have hmem : upperNode (labelSet b) j ∈ labelSet b := upperNode_mem (labelSet_carrier b) j
  have hmem' : upperNode (labelSet b) j ∈ ({lift b} : ZFSet.{u + 1}) :=
    (congrArg (fun s => upperNode (labelSet b) j ∈ s) (labelSet_spec b)).mp hmem
  have heq : upperNode (labelSet b) j = lift b := ZFSet.mem_singleton.mp hmem'
  unfold labelOf
  rw [heq, lowerValue_lift]

/-- The trace relation of the one-node loop labelled by the single label `b`. -/
noncomputable def repeatRelTrace (b : ZFSet.{u}) : ZFSet.{u + 1} :=
  traceLam (graph oneSet fun _ => traceLam (graph (labelSet b) fun _ =>
    traceLam (graph oneSet fun _ => truthCode.{u + 1} True)))

/-- The repeating relation holds on the only nodes. -/
theorem repeatRel_holds (b : ZFSet.{u}) (i : nodeSetOf oneSet) (j : nodeSetOf (labelSet b))
    (k : nodeSetOf oneSet) : labelRel oneSet (labelSet b) (repeatRelTrace b) i j k := by
  unfold labelRel repeatRelTrace
  rw [traceApp_graph_beta _ (upperNode_mem oneSet_carrier i),
    traceApp_graph_beta _ (upperNode_mem (labelSet_carrier b) j),
    traceApp_graph_beta _ (upperNode_mem oneSet_carrier k)]
  exact (mem_truthCode True _).mpr ⟨rfl, trivial⟩

/-- The repeating relation is a labelled relation on the one-member sets. -/
theorem repeatRel_mem (b : ZFSet.{u}) :
    repeatRelTrace b ∈ tracePiSet oneSet fun _ =>
      tracePiSet (labelSet b) fun _ => tracePiSet oneSet fun _ => truthValues.{u + 1} := by
  unfold repeatRelTrace
  exact traceLam_graph_mem fun _ _ => traceLam_graph_mem fun _ _ =>
    traceLam_graph_mem fun _ _ => truthCode_mem_truthValues _

/-- The labelled loop decorates as the stream that repeats the hyperset of `b`. -/
theorem repeat_decorate (b : ZFSet.{u}) (i : nodeSetOf oneSet) :
    decorateLabelled (labelRel oneSet (labelSet b) (repeatRelTrace b)) (labelOf (labelSet b)) i =
      repeatStream (ofZFSet b) := by
  have hd : IsLabelledDecoration (labelRel oneSet (labelSet b) (repeatRelTrace b))
      (labelOf (labelSet b)) (fun _ => repeatStream (ofZFSet b)) := by
    intro a y
    constructor
    · intro hy
      rw [repeatStream_spec, HSet.mem_singleton] at hy
      refine ⟨nodeOfMember (labelSet_carrier b) (labelPoint_mem b),
        nodeOfMember oneSet_carrier onePoint_mem,
        repeatRel_holds b a (nodeOfMember (labelSet_carrier b) (labelPoint_mem b))
          (nodeOfMember oneSet_carrier onePoint_mem), ?_⟩
      rw [hy, labelOf_labelSet]
    · rintro ⟨j, _, _, rfl⟩
      rw [labelOf_labelSet]
      have hmem : kpair (ofZFSet b) (repeatStream (ofZFSet b)) ∈
          ({kpair (ofZFSet b) (repeatStream (ofZFSet b))} : HSet.{u}) :=
        HSet.mem_singleton_self _
      have hset : ({kpair (ofZFSet b) (repeatStream (ofZFSet b))} : HSet.{u}) =
          repeatStream (ofZFSet b) := (repeatStream_spec (ofZFSet b)).symm
      exact (congrArg (fun s : HSet.{u} =>
        kpair (ofZFSet b) (repeatStream (ofZFSet b)) ∈ s) hset).mp hmem
  exact (congrFun hd.eq_decorateLabelled i).symm

/-- **The stream that repeats the hyperset of `b` is `solveLabelled` on the one-node loop.** -/
theorem repeat_solveLabelled (b : ZFSet.{u}) :
    solveLabelledCode oneSet (labelSet b) (repeatRelTrace b) ∅ =
      code (repeatStream (ofZFSet b)) := by
  rw [solveLabelledCode_eq oneSet_carrier (labelSet_carrier b) onePoint_mem]
  exact congrArg code (repeat_decorate b (nodeOfMember oneSet_carrier onePoint_mem))

/-- The value of `solveLabelled` on the repeating loop is the code of the repeating stream. -/
theorem repeat_solveLabelledValue (b : ZFSet.{u}) :
    traceApp (traceApp (traceApp (traceApp solveLabelledValue oneSet) (labelSet b))
      (repeatRelTrace b)) ∅ = code (repeatStream (ofZFSet b)) := by
  rw [solveLabelledValue_apply oneSet_carrier (labelSet_carrier b) (repeatRel_mem b) onePoint_mem,
    repeat_solveLabelled]

end Labelled

/-! ## A deterministic graph and the stream of its labels -/

section StreamReading

/-- The stream of the codes of the labels along a deterministic labelled graph, from the small
node `i`: at the number `n`, the code of the hyperset of the `n`-th label. -/
noncomputable def labelCodeStream {A B R : ZFSet.{u + 1}} (hdet : Deterministic (labelRel A B R))
    (i : nodeSetOf A) : ZFSet.{u + 1} :=
  traceLam (graph ZFSet.omega fun n => code (labelOf B (hdet.labels i (natOf n))))

/-- The stream of label codes is a stream of the stream package over the hyperset codes. -/
theorem labelCodeStream_mem {A B R : ZFSet.{u + 1}} (hdet : Deterministic (labelRel A B R))
    (i : nodeSetOf A) : labelCodeStream hdet i ∈ Streams.streamSet hsetValue.{u} :=
  traceLam_graph_mem fun _ _ => mem_hsetCode.mpr ⟨_, rfl⟩

/-- At the numeral `k`, the stream of label codes is the code of the `k`-th label. -/
theorem labelCodeStream_numeral {A B R : ZFSet.{u + 1}} (hdet : Deterministic (labelRel A B R))
    (i : nodeSetOf A) (k : ℕ) :
    traceApp (labelCodeStream hdet i) (numeral k) = code (labelOf B (hdet.labels i k)) := by
  unfold labelCodeStream
  rw [traceApp_graph_beta _ (numeral_mem_omega k), natOf_numeral]

/-- **The two readings of a stream, for the package's values**: on deterministic labelled graphs,
the values of `solveLabelled` at two members are equal exactly when the streams of the codes of
their labels, streams of the stream package, are equal. -/
theorem solveLabelledValue_eq_iff_labelCodeStream_eq {A B R a A' B' R' a' : ZFSet.{u + 1}}
    (hA : A ∈ carrierCode.{u}) (hB : B ∈ carrierCode.{u})
    (hR : R ∈ tracePiSet A fun _ => tracePiSet B fun _ => tracePiSet A fun _ => truthValues.{u + 1})
    (ha : a ∈ A) (hdet : Deterministic (labelRel A B R))
    (hA' : A' ∈ carrierCode.{u}) (hB' : B' ∈ carrierCode.{u})
    (hR' : R' ∈ tracePiSet A' fun _ => tracePiSet B' fun _ =>
      tracePiSet A' fun _ => truthValues.{u + 1})
    (ha' : a' ∈ A') (hdet' : Deterministic (labelRel A' B' R')) :
    traceApp (traceApp (traceApp (traceApp solveLabelledValue A) B) R) a =
        traceApp (traceApp (traceApp (traceApp solveLabelledValue A') B') R') a' ↔
      labelCodeStream hdet (nodeOfMember hA ha) = labelCodeStream hdet' (nodeOfMember hA' ha') := by
  rw [solveLabelledValue_apply hA hB hR ha, solveLabelledValue_apply hA' hB' hR' ha',
    solveLabelledCode_eq hA hB ha, solveLabelledCode_eq hA' hB' ha', code_injective.eq_iff,
    decorateLabelled_eq_iff_comp_labels hdet hdet']
  constructor
  · intro h
    unfold labelCodeStream
    exact congrArg traceLam (graph_congr fun n _ => congrArg code (congrFun h (natOf n)))
  · intro h
    funext k
    have hk := congrArg (fun s => traceApp s (numeral k)) h
    simp only [labelCodeStream_numeral] at hk
    exact code_injective hk

end StreamReading

variable {L : Type} [LevelOrder L]

/-! ## The constants -/

section Names

/-- The class of hypersets. -/
def hsetN : DeclName := .str .anonymous "hset"

/-- Membership of hypersets. -/
def hInN : DeclName := .str .anonymous "hIn"

/-- The hyperset of a set. -/
def ofSetN : DeclName := .str .anonymous "ofSet"

/-- The hyperset at a node of a graph on a set. -/
def solveN : DeclName := .str .anonymous "solve"

/-- The hyperset at a node of a labelled graph on a set. -/
def solveLabelledN : DeclName := .str .anonymous "solveLabelled"

/-- A set declared to be a member of itself. -/
def selfSetN : DeclName := .str .anonymous "selfSet"

/-- A proof that the declared set is a member of itself. -/
def selfInN : DeclName := .str .anonymous "selfIn"

end Names

section Terms

variable {n : Nat}

/-- The class `hset`. -/
abbrev cHset : CTm (Head L) n := .const hsetN

/-- `hIn x y`. -/
abbrev cHIn (x y : CTm (Head L) n) : CTm (Head L) n := .app (.app (.const hInN) x) y

/-- `ofSet a`. -/
abbrev cOfSet (a : CTm (Head L) n) : CTm (Head L) n := .app (.const ofSetN) a

/-- `solve A R a`. -/
abbrev cSolve (A R a : CTm (Head L) n) : CTm (Head L) n :=
  .app (.app (.app (.const solveN) A) R) a

/-- `solveLabelled A B R a`. -/
abbrev cSolveLabelled (A B R a : CTm (Head L) n) : CTm (Head L) n :=
  .app (.app (.app (.app (.const solveLabelledN) A) B) R) a

/-- The type of `hset`: a class. -/
abbrev hsetType : CTm (Head L) n := allClasses

/-- The type of `hIn`: two hypersets give a proposition. -/
abbrev hInType : CTm (Head L) n := .pi cHset (.pi cHset cProp)

/-- The type of `ofSet`: a set gives a hyperset. -/
abbrev ofSetType : CTm (Head L) n := .pi allSets cHset

/-- The type of `solve`: a set, a relation on it, and a member. -/
abbrev solveType : CTm (Head L) n :=
  .pi allSets (.pi (.pi (.var 0) (.pi (.var 1) cProp)) (.pi (.var 1) cHset))

/-- The type of `solveLabelled`: two sets, a labelled relation, and a member of the first. -/
abbrev solveLabelledType : CTm (Head L) n :=
  .pi allSets (.pi allSets
    (.pi (.pi (.var 1) (.pi (.var 1) (.pi (.var 3) cProp))) (.pi (.var 2) cHset)))

end Terms

variable (L) in
/-- **The table of the hyperset constants**: each with its type, and no equation. -/
def hypersetTable : List (DeclName × CTm (Head L) 0) :=
  [(hsetN, hsetType), (hInN, hInType), (ofSetN, ofSetType), (solveN, solveType),
    (solveLabelledN, solveLabelledType)]

variable (L) in
/-- The declarations of the hyperset constants. -/
def hypersetDecls : DeclName → Option (CTm (Head L) 0) := tableLookup (hypersetTable L)

variable (L) in
/-- **The set theory on rule constants, with the hyperset constants**, and no equation. -/
abbrev hypersetTheory := withRules L (hypersetTable L)

variable (L) in
/-- The table that declares a set together with a proof that it is a member of itself. -/
def selfMemberTable : List (DeclName × CTm (Head L) 0) :=
  [(selfSetN, allSets), (selfInN, cHolds (cIn (.const selfSetN) (.const selfSetN)))]

variable (L) in
/-- The set theory on rule constants, with a self-membered set. -/
abbrev selfMemberTheory := withRules L (selfMemberTable L)

section Declared

omit [LevelOrder L] in
/-- `hset` is declared at `class`. -/
theorem hypersetDecls_hset : hypersetDecls L hsetN = some hsetType := rfl

omit [LevelOrder L] in
/-- `hIn` is declared at `hset → hset → prop`. -/
theorem hypersetDecls_hIn : hypersetDecls L hInN = some hInType := rfl

omit [LevelOrder L] in
/-- `ofSet` is declared at `set → hset`. -/
theorem hypersetDecls_ofSet : hypersetDecls L ofSetN = some ofSetType := rfl

omit [LevelOrder L] in
/-- `solve` is declared at its type. -/
theorem hypersetDecls_solve : hypersetDecls L solveN = some solveType := rfl

omit [LevelOrder L] in
/-- `solveLabelled` is declared at its type. -/
theorem hypersetDecls_solveLabelled : hypersetDecls L solveLabelledN = some solveLabelledType := rfl

/-- A hyperset constant is new to the constants of set theory. -/
theorem hyperset_not_set {c : DeclName} {T : CTm (Head L) 0}
    (declared : hypersetDecls L c = some T) : setDecls L c = none := by
  have row := tableLookup_mem declared
  simp only [hypersetTable, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at row
  rcases row with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

omit [LevelOrder L] in
/-- A hyperset constant is new to the rule constants. -/
theorem hyperset_not_rule {c : DeclName} {T : CTm (Head L) 0}
    (declared : hypersetDecls L c = some T) : ruleDecls L c = none := by
  have row := tableLookup_mem declared
  simp only [hypersetTable, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at row
  rcases row with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- A constant of set theory is new to the hyperset constants. -/
theorem set_not_hyperset {c : DeclName} {T : CTm (Head L) 0}
    (declared : setDecls L c = some T) : hypersetDecls L c = none := by
  have row := tableLookup_mem declared
  simp only [setTable, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at row
  rcases row with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

omit [LevelOrder L] in
/-- A rule constant is new to the hyperset constants. -/
theorem rule_not_hyperset {c : DeclName} {T : CTm (Head L) 0}
    (declared : ruleDecls L c = some T) : hypersetDecls L c = none := by
  have row := tableLookup_mem declared
  simp only [ruleTable, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at row
  rcases row with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- A hyperset constant is declared in the table with the rules at its type. -/
theorem hyperset_in_rules {c : DeclName} {T : CTm (Head L) 0}
    (declared : hypersetDecls L c = some T) :
    tableLookup (rulesTable L (hypersetTable L)) c = some T := by
  unfold rulesTable
  rw [tableLookup_append, tableLookup_append]
  rw [show tableLookup (setTable L) c = none from hyperset_not_set declared]
  rw [show tableLookup (ruleTable L) c = none from hyperset_not_rule declared]
  exact declared

/-- The self-membership proof is declared in its package. -/
theorem selfIn_declared :
    tableLookup (rulesTable L (selfMemberTable L)) selfInN =
      some (cHolds (cIn (.const selfSetN) (.const selfSetN))) := by
  rw [rulesTable, tableLookup_append, tableLookup_append]
  rw [show tableLookup (setTable L) selfInN = none from rfl]
  rw [show tableLookup (ruleTable L) selfInN = none from rfl]
  rfl

end Declared

/-! ## In the judgment -/

section Judgment

/-- **A package over the hypersets**: over the set theory, and it declares the hyperset
constants at their types. The typings of this section hold in every such package. -/
structure OverHypersets {R' : Rules (Head L)} (Q : ChurchRules R') : Prop where
  sets : OverSetTheory Q
  declared : ∀ {c : DeclName} {T : CTm (Head L) 0}, hypersetDecls L c = some T →
    Q.constantType c = some T

/-- The package of the hypersets is over the hypersets. -/
theorem hypersetTheory_over : OverHypersets (hypersetTheory L) where
  sets := (withRules_over (hypersetTable L)).sets
  declared := fun declared => withRules_declared.trans (hyperset_in_rules declared)

variable {R' : Rules (Head L)} {Q : ChurchRules R'} {n : Nat} {Γ : CCtx (Head L) n}
  (covers : OverHypersets Q)

include covers in
/-- The type of `hset` is formed, one universe above `allClasses`. -/
theorem hsetType_formed : CTyped Q Γ hsetType (.head (.sort (.succ (.const (.above 1))))) :=
  .headType (covers.sets.contains.headTyping (LevelTower.HeadTyping.sort _))

include covers in
/-- **`hset` is a class.** -/
theorem hset_typed : CTyped Q Γ (.const hsetN) hsetType :=
  definition_typed (covers.declared hypersetDecls_hset)
    (hsetType_formed (n := 0) (Γ := .nil) covers)
    (covers.sets.contains.isUniverse (.sort _))

include covers in
/-- The type of `hIn` is a type of `allClasses`. -/
theorem hInType_formed : CTyped Q Γ hInType allClasses :=
  classToClass_typed covers.sets.contains (hset_typed covers)
    (classToSet_typed (n := n + 1) (Γ := .snoc Γ cHset) covers.sets.contains
      (hset_typed covers (n := n + 1) (Γ := .snoc Γ cHset))
      (prop_isSet covers.sets (n := n + 2) (Γ := .snoc (.snoc Γ cHset) cHset)))

include covers in
/-- **`hIn` takes two hypersets to a proposition.** -/
theorem hIn_typed : CTyped Q Γ (.const hInN) hInType :=
  definition_typed (covers.declared hypersetDecls_hIn)
    (hInType_formed (n := 0) (Γ := .nil) covers)
    (covers.sets.contains.isUniverse (.sort _))

include covers in
/-- The membership of two hypersets is a proposition. -/
theorem cHIn_typed {x y : CTm (Head L) n} (hx : CTyped Q Γ x cHset) (hy : CTyped Q Γ y cHset) :
    CTyped Q Γ (cHIn x y) cProp :=
  .appElim (B := cProp) (.appElim (B := .pi cHset cProp) (hIn_typed covers) hx) hy

include covers in
/-- The type of `ofSet` is a type of `allClasses`. -/
theorem ofSetType_formed : CTyped Q Γ ofSetType allClasses :=
  classToClass_typed covers.sets.contains (sets_typed covers.sets.contains)
    (hset_typed covers (n := n + 1) (Γ := .snoc Γ allSets))

include covers in
/-- **`ofSet` takes a set to a hyperset.** -/
theorem ofSet_typed : CTyped Q Γ (.const ofSetN) ofSetType :=
  definition_typed (covers.declared hypersetDecls_ofSet)
    (ofSetType_formed (n := 0) (Γ := .nil) covers)
    (covers.sets.contains.isUniverse (.sort _))

include covers in
/-- The hyperset of a set is a hyperset. -/
theorem cOfSet_typed {a : CTm (Head L) n} (ha : CTyped Q Γ a allSets) :
    CTyped Q Γ (cOfSet a) cHset :=
  .appElim (B := cHset) (ofSet_typed covers) ha

include covers in
/-- The type of `solve` is a type of `allClasses`. -/
theorem solveType_formed : CTyped Q Γ solveType allClasses :=
  classToClass_typed covers.sets.contains (sets_typed covers.sets.contains)
    (setToClass_typed (n := n + 1) (Γ := .snoc Γ allSets) covers.sets.contains
      (family_isSet (n := n + 1) (Γ := .snoc Γ allSets) covers.sets.contains
        (CDerivable.var (P := Q) 0)
        (family_isSet (n := n + 2) (Γ := .snoc (.snoc Γ allSets) (.var 0)) covers.sets.contains
          (CDerivable.var (P := Q) 1)
          (prop_isSet covers.sets (n := n + 3)
            (Γ := .snoc (.snoc (.snoc Γ allSets) (.var 0)) (.var 1)))))
      (setToClass_typed (n := n + 2)
        (Γ := .snoc (.snoc Γ allSets) (.pi (.var 0) (.pi (.var 1) cProp))) covers.sets.contains
        (CDerivable.var (P := Q) 1)
        (hset_typed covers (n := n + 3)
          (Γ := .snoc (.snoc (.snoc Γ allSets) (.pi (.var 0) (.pi (.var 1) cProp))) (.var 1)))))

include covers in
/-- **`solve` has its type.** -/
theorem solve_typed : CTyped Q Γ (.const solveN) solveType :=
  definition_typed (covers.declared hypersetDecls_solve)
    (solveType_formed (n := 0) (Γ := .nil) covers)
    (covers.sets.contains.isUniverse (.sort _))

include covers in
/-- **`solve A R a` is a hyperset** when `A` is a set, `R` is a relation on `A`, and `a` is a
member of `A`. -/
theorem cSolve_typed {A R a : CTm (Head L) n} (hA : CTyped Q Γ A allSets)
    (hR : CTyped Q Γ R (.pi A (.pi (A.rename wk) cProp))) (ha : CTyped Q Γ a A) :
    CTyped Q Γ (cSolve A R a) cHset := by
  have first : CTyped Q Γ (.app (.const solveN) A)
      (.pi (.pi A (.pi (A.rename wk) cProp)) (.pi (A.rename wk) cHset)) :=
    .appElim (B := .pi (.pi (.var 0) (.pi (.var 1) cProp)) (.pi (.var 1) cHset))
      (solve_typed covers) hA
  have second := CDerivable.appElim (B := .pi (A.rename wk) cHset) first hR
  have same : CTm.inst0 R (.pi (A.rename wk) cHset) = .pi A cHset := by
    show CTm.pi (CTm.inst0 R (CTm.rename wk A)) cHset = _
    rw [CTm.inst0_rename_wk R A]
  rw [same] at second
  exact .appElim (B := cHset) second ha

include covers in
/-- The type of `solveLabelled` is a type of `allClasses`. -/
theorem solveLabelledType_formed : CTyped Q Γ solveLabelledType allClasses := by
  let Γ1 : CCtx (Head L) (n + 1) := .snoc Γ allSets
  let Γ2 : CCtx (Head L) (n + 2) := .snoc Γ1 allSets
  let rel : CTm (Head L) (n + 2) := .pi (.var 1) (.pi (.var 1) (.pi (.var 3) cProp))
  let Γ3 : CCtx (Head L) (n + 3) := .snoc Γ2 (.var 1)
  let Γ4 : CCtx (Head L) (n + 4) := .snoc Γ3 (.var 1)
  let ΓR : CCtx (Head L) (n + 3) := .snoc Γ2 rel
  have relSet : CTyped Q Γ2 rel allSets :=
    family_isSet (n := n + 2) (Γ := Γ2) covers.sets.contains (CDerivable.var (P := Q) 1)
      (family_isSet (n := n + 3) (Γ := Γ3) covers.sets.contains (CDerivable.var (P := Q) 1)
        (family_isSet (n := n + 4) (Γ := Γ4) covers.sets.contains (CDerivable.var (P := Q) 3)
          (prop_isSet covers.sets (n := n + 5) (Γ := .snoc Γ4 (.var 3)))))
  have resultClass : CTyped Q ΓR (.pi (.var 2) cHset) allClasses :=
    setToClass_typed (n := n + 3) (Γ := ΓR) covers.sets.contains (CDerivable.var (P := Q) 2)
      (hset_typed covers (n := n + 4) (Γ := .snoc ΓR (.var 2)))
  have inner : CTyped Q Γ2 (.pi rel (.pi (.var 2) cHset)) allClasses :=
    setToClass_typed (n := n + 2) (Γ := Γ2) covers.sets.contains relSet resultClass
  have mid : CTyped Q Γ1 (.pi allSets (.pi rel (.pi (.var 2) cHset))) allClasses :=
    classToClass_typed (n := n + 1) (Γ := Γ1) covers.sets.contains
      (sets_typed covers.sets.contains (n := n + 1) (Γ := Γ1)) inner
  exact classToClass_typed covers.sets.contains (sets_typed covers.sets.contains) mid

include covers in
/-- **`solveLabelled` has its type.** -/
theorem solveLabelled_typed : CTyped Q Γ (.const solveLabelledN) solveLabelledType :=
  definition_typed (covers.declared hypersetDecls_solveLabelled)
    (solveLabelledType_formed (n := 0) (Γ := .nil) covers)
    (covers.sets.contains.isUniverse (.sort _))

include covers in
/-- **`solveLabelled A B R a` is a hyperset** when `A` and `B` are sets, `R` relates a member of
`A`, a label of `B` and a member of `A`, and `a` is a member of `A`. -/
theorem cSolveLabelled_typed {A B R a : CTm (Head L) n} (hA : CTyped Q Γ A allSets)
    (hB : CTyped Q Γ B allSets)
    (hR : CTyped Q Γ R (.pi A (.pi (B.rename wk) (.pi ((A.rename wk).rename wk) cProp))))
    (ha : CTyped Q Γ a A) : CTyped Q Γ (cSolveLabelled A B R a) cHset := by
  have first : CTyped Q Γ (.app (.const solveLabelledN) A)
      (.pi allSets
        (.pi (.pi (A.rename wk)
            (.pi (.var 1) (.pi (((A.rename wk).rename wk).rename wk) cProp)))
          (.pi ((A.rename wk).rename wk) cHset))) :=
    .appElim
      (B := .pi allSets
        (.pi (.pi (.var 1) (.pi (.var 1) (.pi (.var 3) cProp))) (.pi (.var 2) cHset)))
      (solveLabelled_typed covers) hA
  have second :=
    CDerivable.appElim
      (B := .pi (.pi (A.rename wk)
          (.pi (.var 1) (.pi (((A.rename wk).rename wk).rename wk) cProp)))
        (.pi ((A.rename wk).rename wk) cHset))
      first hB
  have relType : CTm.inst0 B
      (.pi (.pi (A.rename wk)
          (.pi (.var 1) (.pi (((A.rename wk).rename wk).rename wk) cProp)))
        (.pi ((A.rename wk).rename wk) cHset)) =
      .pi (.pi A (.pi (B.rename wk) (.pi ((A.rename wk).rename wk) cProp)))
        (.pi (A.rename wk) cHset) := by
    show CTm.pi
        (CTm.pi (CTm.inst0 B (CTm.rename wk A))
          (CTm.pi (CTm.subst (CTm.liftSub (CTm.subst0 B)) (.var 1))
            (CTm.pi (CTm.subst (CTm.liftSub (CTm.liftSub (CTm.subst0 B)))
                (CTm.rename wk (CTm.rename wk (CTm.rename wk A)))) cProp)))
        (CTm.pi (CTm.subst (CTm.liftSub (CTm.subst0 B))
            (CTm.rename wk (CTm.rename wk A))) cHset) = _
    rw [CTm.inst0_rename_wk B A]
    have labelVar : CTm.subst (CTm.liftSub (CTm.subst0 B)) (.var 1) = B.rename wk := by
      have idx : (1 : Fin (n + 2)) = Fin.succ (0 : Fin (n + 1)) := Fin.ext rfl
      show CTm.liftSub (CTm.subst0 B) (1 : Fin (n + 2)) = _
      exact (congrArg (CTm.liftSub (CTm.subst0 B)) idx).trans
        ((CTm.liftSub_succ (CTm.subst0 B) (0 : Fin (n + 1))).trans
          (congrArg (CTm.rename wk) (CTm.subst0_zero B)))
    rw [labelVar]
    have openA : CTm.subst (CTm.subst0 B) (CTm.rename wk A) = A :=
      CTm.inst0_rename_wk B A
    simp only [CTm.subst_liftSub_wk, openA]
  rw [relType] at second
  have third := CDerivable.appElim (B := .pi (A.rename wk) cHset) second hR
  have same : CTm.inst0 R (.pi (A.rename wk) cHset) = .pi A cHset := by
    show CTm.pi (CTm.inst0 R (CTm.rename wk A)) cHset = _
    rw [CTm.inst0_rename_wk R A]
  rw [same] at third
  exact .appElim (B := cHset) third ha

end Judgment

/-! ## The set model -/

section Model

/-- The value of a hyperset constant, and the empty set at every other name. -/
noncomputable def hypersetValue (c : DeclName) : ZFSet.{u + 1} :=
  if c = hsetN then hsetValue
  else if c = hInN then hInValue
  else if c = ofSetN then ofSetValue
  else if c = solveN then solveValue
  else if c = solveLabelledN then solveLabelledValue
  else ∅

/-- The value of `hset`. -/
theorem hypersetValue_hset : hypersetValue hsetN = hsetValue := by
  unfold hypersetValue
  rw [if_pos rfl]

/-- The value of `hIn`. -/
theorem hypersetValue_hIn : hypersetValue hInN = hInValue := by
  unfold hypersetValue
  rw [if_neg (by decide), if_pos rfl]

/-- The value of `ofSet`. -/
theorem hypersetValue_ofSet : hypersetValue ofSetN = ofSetValue := by
  unfold hypersetValue
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]

/-- The value of `solve`. -/
theorem hypersetValue_solve : hypersetValue solveN = solveValue := by
  unfold hypersetValue
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]

/-- The value of `solveLabelled`. -/
theorem hypersetValue_solveLabelled : hypersetValue solveLabelledN = solveLabelledValue := by
  unfold hypersetValue
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]

/-- The values of the package: a hyperset constant at its value, and every other name at the
value it has in the set theory. -/
noncomputable def hypersetFamilyValues (all classes : ZFSet.{u + 1})
    (around : ZFSet.{u + 1} → ZFSet.{u + 1}) (c : DeclName) : ZFSet.{u + 1} :=
  match hypersetDecls L c with
  | some _ => hypersetValue c
  | none => setValues all classes around c

omit [LevelOrder L] in
/-- A hyperset constant is read at its hyperset value. -/
theorem hypersetFamilyValues_hyperset {all classes : ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}} {c : DeclName} {T : CTm (Head L) 0}
    (declared : hypersetDecls L c = some T) :
    hypersetFamilyValues (L := L) all classes around c = hypersetValue c := by
  unfold hypersetFamilyValues
  rw [declared]

omit [LevelOrder L] in
/-- A name the hypersets do not declare is read at its value in the set theory. -/
theorem hypersetFamilyValues_other {all classes : ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}} {c : DeclName} (missing : hypersetDecls L c = none) :
    hypersetFamilyValues (L := L) all classes around c = setValues all classes around c := by
  unfold hypersetFamilyValues
  rw [missing]

/-- An assignment that agrees with the hyperset values on the names of the package reads the
constants of set theory at their set values. -/
theorem reads_of_hypersetFamily {all classes : ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}} {consts : DeclName → ZFSet.{u + 1}}
    (agrees : ∀ c, tableLookup (rulesTable L (hypersetTable L)) c ≠ none →
      consts c = hypersetFamilyValues (L := L) all classes around c) :
    Reads L all classes around consts := by
  intro c hc
  cases found : setDecls L c with
  | none => exact absurd found hc
  | some T =>
    rw [agrees c (by
      rw [rulesTable_set found]
      exact Option.some_ne_none _), hypersetFamilyValues_other (set_not_hyperset found)]

variable (large : CofinalInaccessibles.{u + 1}) {ground : ZFSet.{u + 1}} (ν : Nat → Above L)

/-- The reading of a hyperset constant lies in the value of its type. -/
theorem hypersetValue_in_type {consts : DeclName → ZFSet.{u + 1}}
    (hsetRead : consts hsetN = hsetCode) (propRead : consts propN = truthValues.{u + 1})
    {c : DeclName} {T : CTm (Head L) 0} (row : (c, T) ∈ hypersetTable L) :
    hypersetValue c ∈ ev (lowerSetsHeads (L := L) large ground ν) consts T Fin.elim0 := by
  simp only [hypersetTable, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at row
  rcases row with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [hypersetValue_hset]
    show hsetValue ∈ lowerSetsHeads (L := L) large ground ν (.sort (.const (.above 1)))
    rw [lowerSets_allClasses]
    exact hsetCode_mem_of_carrierCode_mem (univOf_closed large carrierCode.{u})
      (mem_univOf large carrierCode.{u})
  · rw [hypersetValue_hIn]
    show hInValue ∈ tracePiSet (consts hsetN) fun _ => tracePiSet (consts hsetN) fun _ => consts propN
    rw [hsetRead, propRead]
    exact traceLam_graph_mem fun _ _ => traceLam_graph_mem fun _ _ => truthCode_mem_truthValues _
  · rw [hypersetValue_ofSet]
    show ofSetValue ∈ tracePiSet
        (lowerSetsHeads (L := L) large ground ν (.sort (.const (.above 0)))) fun _ => consts hsetN
    rw [lowerSets_allSets, hsetRead]
    exact traceLam_graph_mem fun _ _ => mem_hsetCode.mpr ⟨ofZFSet (lowerValue _), rfl⟩
  · rw [hypersetValue_solve]
    show solveValue ∈ tracePiSet
        (lowerSetsHeads (L := L) large ground ν (.sort (.const (.above 0)))) fun A =>
        tracePiSet (tracePiSet A fun _ => tracePiSet A fun _ => consts propN) fun _ =>
          tracePiSet A fun _ => consts hsetN
    rw [lowerSets_allSets, hsetRead, propRead]
    exact traceLam_graph_mem fun A hA => traceLam_graph_mem fun _ _ =>
      traceLam_graph_mem fun a ha => solveCode_mem hA ha
  · rw [hypersetValue_solveLabelled]
    show solveLabelledValue ∈ tracePiSet
        (lowerSetsHeads (L := L) large ground ν (.sort (.const (.above 0)))) fun A =>
        tracePiSet (lowerSetsHeads (L := L) large ground ν (.sort (.const (.above 0)))) fun B =>
          tracePiSet (tracePiSet A fun _ => tracePiSet B fun _ =>
            tracePiSet A fun _ => consts propN) fun _ =>
            tracePiSet A fun _ => consts hsetN
    rw [lowerSets_allSets, hsetRead, propRead]
    exact traceLam_graph_mem fun A hA => traceLam_graph_mem fun B hB =>
      traceLam_graph_mem fun _ _ => traceLam_graph_mem fun a ha =>
        solveLabelledCode_mem hA hB ha

variable (small : CofinalInaccessibles.{u})

include small in
/-- **Every value of the package lies in the set of its constant's type**, at the chain `stages`. -/
theorem hypersetRows_typed
    (groundTyped : ground ∈ universeSet large ZFSet.omega (LevelOrder.bot : L))
    (consts : DeclName → ZFSet.{u + 1})
    (agreesFamily : ∀ c, tableLookup (rulesTable L (hypersetTable L)) c ≠ none →
      consts c = hypersetFamilyValues (L := L) (stages (L := L) large (.above 0))
        (stages (L := L) large (.above 1)) (univOf large) c)
    {c : DeclName} {T : CTm (Head L) 0}
    (declared : tableLookup (rulesTable L (hypersetTable L)) c = some T) :
    hypersetFamilyValues (L := L) (stages (L := L) large (.above 0))
      (stages (L := L) large (.above 1)) (univOf large) c ∈
        ev (lowerSetsHeads (L := L) large ground ν) consts T Fin.elim0 := by
  have reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      (univOf large) consts := reads_of_hypersetFamily agreesFamily
  rcases rulesTable_cases declared with known | ⟨_, rule⟩ | ⟨_, _, row⟩
  · rw [hypersetFamilyValues_other (set_not_hyperset known)]
    exact setValues_typed (V := stages (L := L) large) (around := univOf large) (ν := ν) reads
      (stages_closedChain small large) groundTyped (fun hx => univOf_mem_carrierCode small large hx)
      known
  · rw [hypersetFamilyValues_other (rule_not_hyperset rule),
      setValues_undeclared _ _ _ (ruleDecls_new rule)]
    exact ruleTable_typed reads (stages_closedChain small large) (tableLookup_mem rule)
  · have declaredH : hypersetDecls L c = some T := by
      have row' := row
      simp only [hypersetTable, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at row'
      rcases row' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
    rw [hypersetFamilyValues_hyperset declaredH]
    have hsetRead : consts hsetN = hsetCode := by
      have eq := agreesFamily hsetN (by
        rw [hyperset_in_rules hypersetDecls_hset]
        exact Option.some_ne_none _)
      rw [eq, hypersetFamilyValues_hyperset hypersetDecls_hset, hypersetValue_hset]
      rfl
    have propRead : consts propN = truthValues.{u + 1} := reads.prop
    exact hypersetValue_in_type large ν hsetRead propRead row

/-- **The assignment of the package**: hyperset constants at their values, the constants of set
theory at their set values, and every rule constant at the empty set. -/
noncomputable def hypersetConsts : DeclName → ZFSet.{u + 1} :=
  familyConsts (fun _ => ∅) (tableLookup (rulesTable L (hypersetTable L)))
    (hypersetFamilyValues (L := L) (stages (L := L) large (.above 0))
      (stages (L := L) large (.above 1)) (univOf large))

include small in
/-- **The hypersets have a set model** at the chain `stages`, relative to cofinally many
inaccessible cardinals in two universes. The package contains the set theory and the rule
constants, and it has no equation. -/
theorem lowerSets_hypersetTheory_setModel
    (groundTyped : ground ∈ universeSet large ZFSet.omega (LevelOrder.bot : L)) :
    SetModel (lowerSetsHeads (L := L) large ground ν) (hypersetConsts (L := L) large)
      (hypersetTheory L) :=
  family_setModel_read (heads := lowerSetsHeads (L := L) large ground ν)
    (base := fun _ => ∅) (decls := tableLookup (rulesTable L (hypersetTable L))) (eqs := [])
    (bare L)
    (fun consts _ => lowerSets_setModel small large ν groundTyped consts) (fun _ _ => rfl)
    (hypersetFamilyValues (L := L) (stages (L := L) large (.above 0))
      (stages (L := L) large (.above 1)) (univOf large))
    (fun consts _ agreesFamily {_ _} declared =>
      hypersetRows_typed large ν small groundTyped consts agreesFamily declared)
    (fun _ _ _ _ member => absurd member List.not_mem_nil)

include large small in
/-- **Consistency of the hypersets**: no closed term proves that the empty set is a member of
itself. -/
theorem hypersetTheory_consistent (t : CTm (Head L) 0) :
    ¬ CTyped (hypersetTheory L) .nil t (cHolds (cIn cEmpty cEmpty)) := by
  let groundMem := empty_mem_universeSet large ZFSet.omega (LevelOrder.bot : L)
  refine CDerivable.no_closed_inhabitant
    (lowerSets_hypersetTheory_setModel large (fun _ => LevelOrder.bot) small groundMem)
    (fun z inside => ?_) t
  have reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      (univOf large) (hypersetConsts large) :=
    reads_of_hypersetFamily fun _ declared => familyConsts_declared declared
  change z ∈ traceApp (hypersetConsts large holdsN)
    (traceApp (traceApp (hypersetConsts large inN) (hypersetConsts large emptyN))
      (hypersetConsts large emptyN)) at inside
  rw [reads.holds, reads.in, reads.empty,
    inValue_apply (empty_mem_all (stages_closedChain small large) groundMem)
      (empty_mem_all (stages_closedChain small large) groundMem),
    holdsValue_apply (truthCode_mem_truthValues _)] at inside
  exact ZFSet.notMem_empty _ ((mem_truthCode _ _).mp inside).2

end Model

/-! ## Steps keep types and set values -/

section Steps

variable {n : Nat} {Θ : CCtx (Head L) n}

/-- **The type formers of the hypersets are injective and distinct.** -/
theorem hypersetTheory_formerFacts : CFormerFacts (hypersetTheory L) := constants_formerFacts

/-- The hypersets have no declared step. -/
theorem hypersetTheory_noSteps {l r : CTm (Head L) n} :
    ¬ (hypersetTheory L).computation.step l r := constants_noSteps

/-- The declared steps of the hypersets are equalities: there are none. -/
theorem hypersetTheory_admitted : CRootAdmitted (hypersetTheory L) := constants_admitted

/-- **Every reduction of a term typed in the hypersets is an equality at its type.** -/
theorem hypersetTheory_reduces_equal {t s T : CTm (Head L) n}
    (formed : CCtxFormed (hypersetTheory L) Θ) (reduces : CReduces (hypersetTheory L) t s)
    (typing : CTyped (hypersetTheory L) Θ t T) : CEqual (hypersetTheory L) Θ t s T :=
  constants_reduces_equal formed reduces typing

/-- **Every reduction of a term typed in the hypersets keeps its type.** -/
theorem hypersetTheory_reduces_typed {t s T : CTm (Head L) n}
    (formed : CCtxFormed (hypersetTheory L) Θ) (reduces : CReduces (hypersetTheory L) t s)
    (typing : CTyped (hypersetTheory L) Θ t T) : CTyped (hypersetTheory L) Θ s T :=
  constants_reduces_typed formed reduces typing

/-- **A term typed in the hypersets keeps its set value along every reduction**, in every set
model of the package. -/
theorem hypersetTheory_reduction_keeps_value {heads : Head L → ZFSet.{u + 1}}
    {consts : DeclName → ZFSet.{u + 1}} (model : SetModel heads consts (hypersetTheory L))
    {t s T : CTm (Head L) n} (formed : CCtxFormed (hypersetTheory L) Θ)
    (typing : CTyped (hypersetTheory L) Θ t T) (reduces : CReduces (hypersetTheory L) t s)
    (ρ : Env.{u + 1} n) (sat : Sat heads consts Θ ρ) : ev heads consts t ρ = ev heads consts s ρ :=
  constants_reduction_keeps_value model formed typing reduces ρ sat

end Steps

/-! ## A self-membered set has no set model -/

section SelfMember

/-- At every reading of the constants of set theory, the type of a proof that the declared set
is a member of itself is empty. -/
theorem selfMember_type_empty {all classes : ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}} {heads : Head L → ZFSet.{u + 1}}
    {consts : DeclName → ZFSet.{u + 1}} (reads : Reads L all classes around consts)
    {z : ZFSet.{u + 1}} :
    z ∉ ev heads consts (cHolds (cIn (.const selfSetN) (.const selfSetN))) Fin.elim0 := by
  intro hz
  change z ∈ traceApp (consts holdsN)
    (traceApp (traceApp (consts inN) (consts selfSetN)) (consts selfSetN)) at hz
  rw [reads.holds, reads.in] at hz
  by_cases hx : consts selfSetN ∈ all
  · rw [inValue_apply hx hx, holdsValue_apply (truthCode_mem_truthValues _)] at hz
    exact ZFSet.mem_irrefl _ ((mem_truthCode _ _).mp hz).2
  · have hin : inValue all ∈ tracePiSet all fun _ => tracePiSet all fun _ => truthValues := by
      unfold inValue
      exact traceLam_graph_mem fun _ _ => traceLam_graph_mem fun _ _ => truthCode_mem_truthValues _
    have happ : traceApp (inValue all) (consts selfSetN) = ∅ :=
      traceApp_eq_empty_of_not_mem hin hx
    rw [happ, traceApp_empty, holdsValue_apply
      (ZFSet.mem_powerset.mpr fun _ h => False.elim (ZFSet.notMem_empty _ h))] at hz
    exact ZFSet.notMem_empty _ hz

/-- **A package that declares a set `x` with a proof of `In x x` has no set model** at a reading
of the constants of set theory. `solve` on the one-member loop gives such an `x` among the
hypersets (`loop_codeMem_self`). -/
theorem selfMemberTheory_no_setModel {all classes : ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}} (heads : Head L → ZFSet.{u + 1})
    (consts : DeclName → ZFSet.{u + 1}) (reads : Reads L all classes around consts) :
    ¬ SetModel heads consts (selfMemberTheory L) :=
  family_no_setModel_of_empty (decls := tableLookup (rulesTable L (selfMemberTable L))) (eqs := [])
    (bare L) rfl selfIn_declared consts fun _ => selfMember_type_empty reads

end SelfMember

end MegalodonHOTG

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
