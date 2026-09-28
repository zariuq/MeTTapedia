import Mettapedia.TypeTheory.MaterialSets.DependentSum
import Mettapedia.Logic.HOL.Embedding.ZFSetContextualIdentity
import Mettapedia.SetTheory.ZFSet.OrderedPair

/-!
# Set-coded membership proofs in a closed universe

The contextual set model (`ZFSetContextualInterpretation`) interprets `set` by
a set-coded universe `U`, its terms by members of `U`, and `holds (In x X)` by
the proof fibre `truthCode (x ∈ X)`, a subset of `{∅}`. Evidence of membership is
then the type `Elements (truthCode (x ∈ X))` of proof codes, and propositional
membership is a theorem about them: every proof code is `∅` (`propositional`).
Recovery builds the code `∅` from the fact of membership, without choice.

For a closed universe `U` (`ZFSetUniverseClosure.Closed`), the operations of the
interface are the set operations inside `U`: `Image` by replacement, `Union` by
`⋃₀`, pairs by Kuratowski pairs and their projections. `El X` is the model's
dependent sum `Σ x : set. holds (In x X)` (`elEquivCode`, `elCode_eq_sigmaFamily`).

Equality of sets is interpreted by the identity type of `ZFSetContextualIdentity`,
whose fibre is `truthCode (X = Y)`. Extensionality supplies its witness
(`extPoint`). Its `J` never changes a set code (`j_val`), so transport of any
set-coded family along an identity witness is the identity on codes
(`transport_val`). At the family `El`, along the witness of extensionality, it is
the transport of the identity reading (`transport_el`).

`ZFSetUniverseClosure.smallUniverse` is a closed universe without a cardinal
hypothesis (`small`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Instances.SetCodedProofs

open Mettapedia.Logic.HOL.Embedding
open Mettapedia.SetTheory
open ZFSetUniverseClosure (Closed)
open ZFSetDependentProducts (Elements)
open ZFSetTraceProofDecoding (truthCode mem_truthCode)
open ZFSetContextualInterpretation (SetFamily Section Extension)
open ZFSetContextualIdentity (formation elimination)

universe u

section Evidence

variable (U : ZFSet.{u})

/-- Evidence of `holds (In x X)`: the proof codes in `truthCode (x ∈ X)`. -/
abbrev Mem (x X : Elements U) : Type (u + 1) := Elements (truthCode.{u} (x.1 ∈ X.1))

/-- The proof code of a membership. -/
def proofCode {x X : Elements U} (hx : x.1 ∈ X.1) : Mem U x X :=
  ⟨∅, (mem_truthCode _ _).mpr ⟨rfl, hx⟩⟩

theorem mem_of_proof {x X : Elements U} (p : Mem U x X) : x.1 ∈ X.1 :=
  ((mem_truthCode _ _).mp p.2).2

theorem proof_val {x X : Elements U} (p : Mem U x X) : p.1 = ∅ :=
  ((mem_truthCode _ _).mp p.2).1

theorem nonempty_mem_iff {x X : Elements U} : Nonempty (Mem U x X) ↔ x.1 ∈ X.1 :=
  ⟨fun ⟨p⟩ => mem_of_proof U p, fun hx => ⟨proofCode U hx⟩⟩

/-- Every membership proof code is `∅`, so membership is propositional. -/
theorem propositional : PropositionalMembership (Mem U) :=
  fun _ _ => ⟨fun p q => Subtype.ext ((proof_val U p).trans (proof_val U q).symm)⟩

/-- The proof code is rebuilt from the fact of membership. -/
def recovery : EvidenceRecovery (Mem U) :=
  ⟨fun h => proofCode U (h.elim fun p => mem_of_proof U p)⟩

/-- The set code of `El X = Σ x : set. holds (In x X)`: pairs of a member of `U`
and a proof code of its membership in `X`. -/
noncomputable def elCode (X : ZFSet.{u}) : ZFSet.{u} :=
  ZFSetDependentProducts.sigmaSet U fun x => truthCode.{u} (x ∈ X)

/-- `El X` is the model's dependent sum `Σ x : set. holds (In x X)`. -/
noncomputable def elEquivCode (X : Elements U) : El (Mem U) X ≃ Elements (elCode U X.1) :=
  (Equiv.psigmaEquivSigma fun x : Elements U => Mem U x X).trans
    (ZFSetDependentProducts.sigmaEquiv U fun x => truthCode.{u} (x ∈ X.1)).symm

theorem elEquivCode_apply_val (X : Elements U) (a : El (Mem U) X) :
    (elEquivCode U X a).1 = ZFSet.pair a.1.1 a.2.1 := rfl

/-- The pair code of a decoded member. -/
theorem pair_elEquivCode_symm (X : Elements U) (c : Elements (elCode U X.1)) :
    ZFSet.pair ((elEquivCode U X).symm c).1.1 ((elEquivCode U X).symm c).2.1 = c.1 :=
  congrArg Subtype.val
    ((ZFSetDependentProducts.sigmaEquiv U fun x => truthCode.{u} (x ∈ X.1)).symm_apply_apply c)

/-- `elCode` is the dependent sum `sigmaFamily` of the contextual set model, at
the type `set` and the family `holds (In x X)`. -/
theorem elCode_eq_sigmaFamily (X : Elements U) :
    ZFSetContextualInterpretation.sigmaFamily (fun _ : PUnit.{u + 2} => U)
        (fun p => truthCode.{u} (p.2.1 ∈ X.1)) PUnit.unit = elCode U X.1 :=
  ZFSetDependentProducts.sigmaSet_congr fun x hx =>
    ZFSetContextualInterpretation.totalFamily_at U (fun y => truthCode.{u} (y.1 ∈ X.1)) ⟨x, hx⟩

/-- No member of the empty set has a proof code. -/
theorem el_empty_isEmpty (empty : Elements U) (hempty : empty.1 = ∅) :
    IsEmpty (El (Mem U) empty) :=
  ⟨fun a => ZFSet.notMem_empty a.1.1 (hempty ▸ mem_of_proof U a.2)⟩

end Evidence

/-! ## The set operations inside a closed universe -/

section Operations

variable {U : ZFSet.{u}} (closed : Closed U)
include closed

theorem mem_universe {x : ZFSet.{u}} (X : Elements U) (hx : x ∈ X.1) : x ∈ U :=
  closed.transitive X.1 X.2 hx

/-- A family on the members of `X`, extended by `∅` outside `X`. -/
noncomputable def extend {X : Elements U} (F : El (Mem U) X → Elements U) (x : ZFSet.{u}) :
    ZFSet.{u} := by
  classical
  exact if hx : x ∈ X.1 then (F ⟨⟨x, mem_universe closed X hx⟩, proofCode U hx⟩).1 else ∅

theorem extend_el {X : Elements U} (F : El (Mem U) X → Elements U) (a : El (Mem U) X) :
    extend closed F a.1.1 = (F a).1 := by
  unfold extend
  rw [dif_pos (mem_of_proof U a.2)]
  exact congrArg (fun c => (F c).1) (El.ext (propositional U) rfl)

theorem extend_mem {X : Elements U} (F : El (Mem U) X → Elements U) (x : ZFSet.{u})
    (hx : x ∈ X.1) : extend closed F x ∈ U := by
  unfold extend
  rw [dif_pos hx]
  exact (F _).2

noncomputable def dependentReplacement : DependentReplacement (Mem U) where
  image X F := ⟨ZFSetHenkinInterpretation.replacement X.1 (extend closed F),
    closed.replacement_mem X.2 _ (extend_mem closed F)⟩
  mem_image F a := proofCode U (ZFSetHenkinInterpretation.mem_replacement.mpr
    ⟨a.1.1, mem_of_proof U a.2, extend_el closed F a⟩)
  exists_of_mem_image := fun {X F _} m => by
    obtain ⟨x, hx, e⟩ := ZFSetHenkinInterpretation.mem_replacement.mp (mem_of_proof U m)
    let a : El (Mem U) X := ⟨⟨x, mem_universe closed X hx⟩, proofCode U hx⟩
    exact ⟨a, Subtype.ext ((extend_el closed F a).symm.trans e)⟩

def union : UnionOperation (Mem U) where
  union Y := ⟨ZFSet.sUnion Y.1, closed.union_mem Y.2⟩
  mem_union hx hW :=
    proofCode U (ZFSet.mem_sUnion_of_mem (mem_of_proof U hx) (mem_of_proof U hW))
  exists_of_mem_union := fun {_ Y} m => by
    obtain ⟨W, hW, hx⟩ := ZFSet.mem_sUnion.mp (mem_of_proof U m)
    exact ⟨⟨W, mem_universe closed Y hW⟩, ⟨proofCode U hx⟩, ⟨proofCode U hW⟩⟩

theorem first_mem {z : ZFSet.{u}} (hz : z ∈ U) : ZFSetOrderedPair.first z ∈ U :=
  closed.union_mem (closed.separation_mem (closed.union_mem hz) _)

theorem second_mem {z : ZFSet.{u}} (hz : z ∈ U) : ZFSetOrderedPair.second z ∈ U :=
  closed.union_mem (closed.separation_mem (closed.union_mem hz) _)

noncomputable def pairing : Pairing (Elements U) where
  pair x y := ⟨ZFSet.pair x.1 y.1, closed.pair_mem x.2 y.2⟩
  fst z := ⟨ZFSetOrderedPair.first z.1, first_mem closed z.2⟩
  snd z := ⟨ZFSetOrderedPair.second z.1, second_mem closed z.2⟩
  fst_pair x y := Subtype.ext (ZFSetOrderedPair.first_pair x.1 y.1)
  snd_pair x y := Subtype.ext (ZFSetOrderedPair.second_pair x.1 y.1)

theorem extensional : Extensional (Mem U) := fun {X Y} coext =>
  Subtype.ext <| ZFSet.ext fun z =>
    ⟨fun hz => (nonempty_mem_iff U).mp
        ((coext ⟨z, mem_universe closed X hz⟩).mp ((nonempty_mem_iff U).mpr hz)),
      fun hz => (nonempty_mem_iff U).mp
        ((coext ⟨z, mem_universe closed Y hz⟩).mpr ((nonempty_mem_iff U).mpr hz))⟩

/-- The set of pairs and the dependent sum of member types, in the set-coded
model. -/
noncomputable def sigmaSetEquiv (X : Elements U) (B : El (Mem U) X → Elements U) :
    El (Mem U) (sigmaSet (dependentReplacement closed) (union closed) (pairing closed) X B) ≃
      Σ' a : El (Mem U) X, El (Mem U) (B a) :=
  MaterialSets.sigmaSetEquiv (dependentReplacement closed) (union closed) (pairing closed)
    (propositional U) (recovery U) X B

end Operations

/-! ## Identity of sets and `J` -/

section Identity

/-- The model's `J` never changes a set code: its value at any point of the
identity context has the code of the base at the left endpoint. -/
theorem j_val {Γ : Type (u + 1)} {a : SetFamily Γ}
    (motive : SetFamily (formation.identityContext a))
    (base : Section (motive ∘ elimination.reflexivitySubstitution a))
    (point : formation.identityContext a) :
    (elimination.j motive base point).1 = (base point.1.1).1 := by
  rcases point with ⟨⟨⟨γ, left⟩, right⟩, witness⟩
  have endpoints : left = right := ((mem_truthCode (left = right) witness.1).mp witness.2).2
  subst endpoints
  have canonical : witness = ⟨∅, (mem_truthCode (left = left) ∅).mpr ⟨rfl, rfl⟩⟩ :=
    Subtype.ext ((mem_truthCode (left = left) witness.1).mp witness.2).1
  subst canonical
  rfl

/-- The motive of transport, `C (x, y, p) := P x → P y`, as a set-coded family
of function graphs. -/
noncomputable def transportMotive {Γ : Type (u + 1)} {a : SetFamily Γ}
    (P : SetFamily (Extension a)) : SetFamily (formation.identityContext a) :=
  fun q => ZFSetDependentProducts.piSet (P q.1.1) fun _ => P ⟨q.1.1.1, q.1.2⟩

/-- At reflexivity, the base of transport is the identity graph. -/
noncomputable def transportBase {Γ : Type (u + 1)} {a : SetFamily Γ}
    (P : SetFamily (Extension a)) :
    Section (transportMotive P ∘ elimination.reflexivitySubstitution a) :=
  fun p => ⟨ZFSetDependentProducts.graph (P p) id,
    ZFSetDependentProducts.graph_mem_piSet fun _ hx => hx⟩

/-- Transport of a set-coded family along a point of the identity context,
computed by the model's `J`. -/
noncomputable def transport {Γ : Type (u + 1)} {a : SetFamily Γ}
    (P : SetFamily (Extension a)) (point : formation.identityContext a)
    (e : Elements (P point.1.1)) : Elements (P ⟨point.1.1.1, point.1.2⟩) :=
  ZFSetDependentProducts.graphValue
    (elimination.j (transportMotive P) (transportBase P) point) e

/-- Transport along any identity witness is the identity on set codes. -/
theorem transport_val {Γ : Type (u + 1)} {a : SetFamily Γ} (P : SetFamily (Extension a))
    (point : formation.identityContext a) (e : Elements (P point.1.1)) :
    (transport P point e).1 = e.1 := by
  refine (ZFSetDependentProducts.graphValue_unique _ e e.1 ?_).symm
  rw [j_val]
  exact ZFSetDependentProducts.pair_mem_graph.mpr ⟨e.2, rfl⟩

/-- The family `El` over the type `set` of the closed context. -/
noncomputable def elFamily (U : ZFSet.{u}) :
    SetFamily (Extension (fun _ : PUnit.{u + 2} => U)) :=
  fun p => elCode U p.2.1

/-- The identity witness supplied by extensionality, as a point of the
identity context of `set`. -/
noncomputable def extPoint {U : ZFSet.{u}} (closed : Closed U) {X Y : Elements U}
    (coext : ∀ z, Nonempty (Mem U z X) ↔ Nonempty (Mem U z Y)) :
    formation.identityContext (fun _ : PUnit.{u + 2} => U) :=
  ⟨⟨⟨PUnit.unit, X⟩, Y⟩, ⟨∅, (mem_truthCode (X = Y) ∅).mpr ⟨rfl, extensional closed coext⟩⟩⟩

/-- `J` at the family `El`, along the witness of extensionality, is the
transport of the identity reading: it keeps each member. -/
theorem transport_el {U : ZFSet.{u}} (closed : Closed U) {X Y : Elements U}
    (coext : ∀ z, Nonempty (Mem U z X) ↔ Nonempty (Mem U z Y)) (a : El (Mem U) X) :
    (elEquivCode U Y).symm (transport (elFamily U) (extPoint closed coext) (elEquivCode U X a)) =
      MaterialSets.transport (extensional closed coext) a := by
  apply El.ext (propositional U)
  rw [MaterialSets.transport_fst]
  apply Subtype.ext
  have decoded := (pair_elEquivCode_symm U Y
    (transport (elFamily U) (extPoint closed coext) (elEquivCode U X a))).trans
      ((transport_val (elFamily U) (extPoint closed coext) (elEquivCode U X a)).trans
        (elEquivCode_apply_val U X a))
  exact (ZFSet.pair_inj.mp decoded).1

end Identity

/-! ## A closed universe without a cardinal hypothesis -/

section Small

/-- `Image` inside the closed universe given by Lean's lower universe level. -/
noncomputable def small : DependentReplacement (Mem ZFSetUniverseClosure.smallUniverse.{u}) :=
  dependentReplacement ZFSetUniverseClosure.smallUniverse_closed

end Small

end Mettapedia.TypeTheory.MaterialSets.Instances.SetCodedProofs
