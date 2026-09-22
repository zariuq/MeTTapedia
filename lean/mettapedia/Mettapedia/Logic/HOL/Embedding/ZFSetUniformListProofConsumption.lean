import Mettapedia.Logic.HOL.Embedding.ZFSetUniformListModel
import Mettapedia.Logic.HOL.Embedding.ZFSetListClosure
import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProducts

/-!
# Source HOL proof consumption on actual separated list sets

The source universal implication acts between actual separated sets of list
codes. Its graph is built using the same set-product representation as the
contextual model. Application agrees with the retained HOL proof interpreter,
and preserves the original input code. The map-fusion instance uses the
existing source congruence proof and its original induction proof dependency.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetUniformListProofConsumption

open UniformListInduction UniformListMapFusion
open ZFSetDependentProducts ZFSetUniformListModel
open ZFSetTraceProducts
open HenkinDependentFamilyInterpretation HenkinPredicateFamilyInterpretation

universe u

variable {Γ Δ : Ctx BaseSort}

noncomputable def refinementCode (a : ZFSet.{u})
    (φ : Formula Symbol (sequence :: Γ)) (ρ : AdmissibleContext (model a) Γ) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ hz : z ∈ ZFSetList.listCode a,
    ((model a).denote φ ((model a).extend (σ := sequence) ρ.1
      (show Elements (ZFSetList.listCode a) from ⟨z, hz⟩))).down) (ZFSetList.listCode a)

theorem mem_refinementCode (a : ZFSet.{u}) (φ : Formula Symbol (sequence :: Γ))
    (ρ : AdmissibleContext (model a) Γ) (z : ZFSet.{u}) :
    z ∈ refinementCode a φ ρ ↔ ∃ hz : z ∈ ZFSetList.listCode a,
      ((model a).denote φ ((model a).extend (σ := sequence) ρ.1
        (show Elements (ZFSetList.listCode a) from ⟨z, hz⟩))).down := by
  rw [refinementCode, ZFSet.mem_sep]
  exact ⟨fun h => h.2, fun ⟨hz, hp⟩ => ⟨hz, hz, hp⟩⟩

noncomputable def refinementEquiv (a : ZFSet.{u})
    (φ : Formula Symbol (sequence :: Γ)) (ρ : AdmissibleContext (model a) Γ) :
    Elements (refinementCode a φ ρ) ≃ refinementFamily (model a) φ ρ where
  toFun point :=
    let present := (mem_refinementCode a φ ρ point.1).mp point.2
    ⟨⟨⟨point.1, present.choose⟩, by trivial⟩, ⟨⟨present.choose_spec⟩⟩⟩
  invFun point := ⟨point.1.1.1, (mem_refinementCode a φ ρ point.1.1.1).mpr
    ⟨point.1.1.2, point.2.down.down⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem refinementCode_substitution (a : ZFSet.{u})
    (φ : Formula Symbol (sequence :: Γ)) (θ : Subst Symbol Γ Δ)
    (ρ : AdmissibleContext (model a) Δ) :
    refinementCode a (HOL.subst (Subst.lift θ) φ) ρ =
      refinementCode a φ (interpretSubstitution (model a) θ ρ) := by
  apply ZFSet.ext
  intro z
  simp only [mem_refinementCode]
  apply exists_congr
  intro hz
  rw [Soundness.denote_subst]
  erw [Soundness.substVal_lift]
  rfl

noncomputable def refinementMap (a : ZFSet.{u})
    {hypotheses : List (Formula Symbol Γ)} {φ ψ : Formula Symbol (sequence :: Γ)}
    (proof : ProofSyntax Symbol hypotheses (.all (.imp φ ψ)))
    (ρ : SatisfiedContext (model a) hypotheses)
    (point : Elements (refinementCode a φ ρ.1)) : Elements (refinementCode a ψ ρ.1) :=
  (refinementEquiv a ψ ρ.1).symm
    (refinementMapOfProof (model a) (respects a) proof ρ
      (refinementEquiv a φ ρ.1 point))

theorem refinementMap_preserves_code (a : ZFSet.{u})
    {hypotheses : List (Formula Symbol Γ)} {φ ψ : Formula Symbol (sequence :: Γ)}
    (proof : ProofSyntax Symbol hypotheses (.all (.imp φ ψ)))
    (ρ : SatisfiedContext (model a) hypotheses) (point : Elements (refinementCode a φ ρ.1)) :
    (refinementMap a proof ρ point).1 = point.1 := rfl

noncomputable def refinementGraph (a : ZFSet.{u})
    {hypotheses : List (Formula Symbol Γ)} {φ ψ : Formula Symbol (sequence :: Γ)}
    (proof : ProofSyntax Symbol hypotheses (.all (.imp φ ψ)))
    (ρ : SatisfiedContext (model a) hypotheses) :
    Elements (piSet (refinementCode a φ ρ.1) (fun _ => refinementCode a ψ ρ.1)) :=
  encodeFunction (refinementMap a proof ρ)

theorem refinementGraph_apply (a : ZFSet.{u})
    {hypotheses : List (Formula Symbol Γ)} {φ ψ : Formula Symbol (sequence :: Γ)}
    (proof : ProofSyntax Symbol hypotheses (.all (.imp φ ψ)))
    (ρ : SatisfiedContext (model a) hypotheses) (point : Elements (refinementCode a φ ρ.1)) :
    graphValue (a := refinementCode a φ ρ.1) (b := fun _ => refinementCode a ψ ρ.1)
      (refinementGraph a proof ρ) point = refinementMap a proof ρ point :=
  congrFun (decode_encode_function (a := refinementCode a φ ρ.1)
    (b := fun _ => refinementCode a ψ ρ.1) (refinementMap a proof ρ)) point

/-- The actual graph route commutes with the independently defined source
proof interpreter, not just with an independently proved fusion equation. -/
theorem refinementGraph_square (a : ZFSet.{u})
    {hypotheses : List (Formula Symbol Γ)} {φ ψ : Formula Symbol (sequence :: Γ)}
    (proof : ProofSyntax Symbol hypotheses (.all (.imp φ ψ)))
    (ρ : SatisfiedContext (model a) hypotheses) (point : Elements (refinementCode a φ ρ.1)) :
    refinementEquiv a ψ ρ.1
      (graphValue (a := refinementCode a φ ρ.1) (b := fun _ => refinementCode a ψ ρ.1)
        (refinementGraph a proof ρ) point) =
      refinementMapOfProof (model a) (respects a) proof ρ (refinementEquiv a φ ρ.1 point) := by
  rw [refinementGraph_apply]
  exact (refinementEquiv a ψ ρ.1).apply_symm_apply _

theorem refinementCode_mem {U a : ZFSet.{u}}
    (closed : ZFSetUniverseClosure.Closed U) (carrierMember : a ∈ U)
    (indices : ZFSetIndexedClosure.finiteRankIndex ∈ U)
    (φ : Formula Symbol (sequence :: Γ)) (ρ : AdmissibleContext (model a) Γ) :
    refinementCode a φ ρ ∈ U :=
  closed.separation_mem (ZFSetListClosure.listCode_mem closed carrierMember indices) _

/-- The graph itself belongs to the same universe once the independently
justified natural-index seed is present; external smallness is not substituted
for that closure premise. -/
theorem refinementGraph_mem {U a : ZFSet.{u}}
    (closed : ZFSetUniverseClosure.Closed U) (carrierMember : a ∈ U)
    (indices : ZFSetIndexedClosure.finiteRankIndex ∈ U)
    {hypotheses : List (Formula Symbol Γ)} {φ ψ : Formula Symbol (sequence :: Γ)}
    (proof : ProofSyntax Symbol hypotheses (.all (.imp φ ψ)))
    (ρ : SatisfiedContext (model a) hypotheses) : (refinementGraph a proof ρ).1 ∈ U :=
  closed.transitive _
    (closed.piSet_mem (refinementCode_mem closed carrierMember indices φ ρ.1)
      (fun _ => refinementCode a ψ ρ.1)
      (fun _ _ => refinementCode_mem closed carrierMember indices ψ ρ.1))
    (refinementGraph a proof ρ).2

/-! ## The same proof-induced map in the alternative trace presentation -/

noncomputable def traceGraph (a : ZFSet.{u})
    {hypotheses : List (Formula Symbol Γ)} {φ ψ : Formula Symbol (sequence :: Γ)}
    (proof : ProofSyntax Symbol hypotheses (.all (.imp φ ψ)))
    (ρ : SatisfiedContext (model a) hypotheses) :
    Elements (tracePiSet (refinementCode a φ ρ.1) (fun _ => refinementCode a ψ ρ.1)) :=
  traceEncode (refinementMap a proof ρ)

theorem traceGraph_apply (a : ZFSet.{u})
    {hypotheses : List (Formula Symbol Γ)} {φ ψ : Formula Symbol (sequence :: Γ)}
    (proof : ProofSyntax Symbol hypotheses (.all (.imp φ ψ)))
    (ρ : SatisfiedContext (model a) hypotheses) (point : Elements (refinementCode a φ ρ.1)) :
    traceValue (a := refinementCode a φ ρ.1) (b := fun _ => refinementCode a ψ ρ.1)
      (traceGraph a proof ρ) point = refinementMap a proof ρ point :=
  congrFun (trace_beta (a := refinementCode a φ ρ.1)
    (b := fun _ => refinementCode a ψ ρ.1) (refinementMap a proof ρ)) point

theorem traceGraph_application_agreement (a : ZFSet.{u})
    {hypotheses : List (Formula Symbol Γ)} {φ ψ : Formula Symbol (sequence :: Γ)}
    (proof : ProofSyntax Symbol hypotheses (.all (.imp φ ψ)))
    (ρ : SatisfiedContext (model a) hypotheses) (point : Elements (refinementCode a φ ρ.1)) :
    traceValue (a := refinementCode a φ ρ.1) (b := fun _ => refinementCode a ψ ρ.1)
      (traceGraph a proof ρ) point =
    graphValue (a := refinementCode a φ ρ.1) (b := fun _ => refinementCode a ψ ρ.1)
      (refinementGraph a proof ρ) point := by
  rw [traceGraph_apply, refinementGraph_apply]

theorem traceGraph_square (a : ZFSet.{u})
    {hypotheses : List (Formula Symbol Γ)} {φ ψ : Formula Symbol (sequence :: Γ)}
    (proof : ProofSyntax Symbol hypotheses (.all (.imp φ ψ)))
    (ρ : SatisfiedContext (model a) hypotheses) (point : Elements (refinementCode a φ ρ.1)) :
    refinementEquiv a ψ ρ.1
      (traceValue (a := refinementCode a φ ρ.1) (b := fun _ => refinementCode a ψ ρ.1)
        (traceGraph a proof ρ) point) =
      refinementMapOfProof (model a) (respects a) proof ρ (refinementEquiv a φ ρ.1 point) := by
  rw [traceGraph_application_agreement]
  exact refinementGraph_square a proof ρ point

theorem traceGraph_mem {U a : ZFSet.{u}}
    (closed : ZFSetUniverseClosure.Closed U) (carrierMember : a ∈ U)
    (indices : ZFSetIndexedClosure.finiteRankIndex ∈ U)
    {hypotheses : List (Formula Symbol Γ)} {φ ψ : Formula Symbol (sequence :: Γ)}
    (proof : ProofSyntax Symbol hypotheses (.all (.imp φ ψ)))
    (ρ : SatisfiedContext (model a) hypotheses) : (traceGraph a proof ρ).1 ∈ U :=
  closed.traceLam_mem (refinementGraph_mem closed carrierMember indices proof ρ)

/-! ## An arbitrary predicate consumed through the retained fusion proof -/

noncomputable def propertyValue {a : ZFSet.{u}}
    (property : Elements (ZFSetList.listCode a) → Prop) :
    AdmissibleValue (model a) predicate := ⟨fun xs => ⟨property xs⟩, by trivial⟩

noncomputable def propertyContext {a : ZFSet.{u}}
    (property : Elements (ZFSetList.listCode a) → Prop) (f g : Elements a → Elements a) :
    SatisfiedContext (model a) (theory (Γ := [predicate, mapping, mapping])) :=
  UniformListPredicateFamily.extendTheoryContext (model a) (functionContext f g)
    (propertyValue property)

def before : Formula Symbol [sequence, predicate, mapping, mapping] :=
  UniformListPredicateFamily.beforeFusion (.var .vz) (.var (.vs (.vs .vz))) (.var (.vs .vz))

def after : Formula Symbol [sequence, predicate, mapping, mapping] :=
  UniformListPredicateFamily.afterFusion (.var .vz) (.var (.vs (.vs .vz))) (.var (.vs .vz))

def sourceConsumer : ProofSyntax Symbol theory (.all (.imp before after)) :=
  UniformListPredicateFamily.refinementForwardProof (.var .vz)
    (.var (.vs (.vs .vz))) (.var (.vs .vz))

noncomputable def inputPoint {a : ZFSet.{u}}
    (property : Elements (ZFSetList.listCode a) → Prop) (f g : Elements a → Elements a)
    (xs : Elements (ZFSetList.listCode a)) (holds : property (mapValue f (mapValue g xs))) :
    Elements (refinementCode a before (propertyContext property f g).1) :=
  ⟨xs.1, (mem_refinementCode a before _ xs.1).mpr ⟨xs.2, holds⟩⟩

noncomputable def consumedPoint {a : ZFSet.{u}}
    (property : Elements (ZFSetList.listCode a) → Prop) (f g : Elements a → Elements a)
    (xs : Elements (ZFSetList.listCode a)) (holds : property (mapValue f (mapValue g xs))) :
    Elements (refinementCode a after (propertyContext property f g).1) :=
  graphValue (a := refinementCode a before (propertyContext property f g).1)
    (b := fun _ => refinementCode a after (propertyContext property f g).1)
    (refinementGraph a sourceConsumer (propertyContext property f g))
    (inputPoint property f g xs holds)

theorem consumedPoint_code {a : ZFSet.{u}}
    (property : Elements (ZFSetList.listCode a) → Prop) (f g : Elements a → Elements a)
    (xs : Elements (ZFSetList.listCode a)) (holds : property (mapValue f (mapValue g xs))) :
    (consumedPoint property f g xs holds).1 = xs.1 := by
  unfold consumedPoint
  rw [refinementGraph_apply]
  rfl

theorem consumedPoint_property {a : ZFSet.{u}}
    (property : Elements (ZFSetList.listCode a) → Prop) (f g : Elements a → Elements a)
    (xs : Elements (ZFSetList.listCode a)) (holds : property (mapValue f (mapValue g xs))) :
    property (mapValue (fun x => f (g x)) xs) := by
  have present := (mem_refinementCode a after (propertyContext property f g).1
    (consumedPoint property f g xs holds).1).mp (consumedPoint property f g xs holds).2
  rw [consumedPoint_code] at present
  exact present.choose_spec

namespace Controls

def two : ZFSet.{u} := {∅, ZFSet.powerset ∅}
def zero : Elements two.{u} := ⟨∅, ZFSet.mem_pair.mpr (Or.inl rfl)⟩
def one : Elements two.{u} := ⟨ZFSet.powerset ∅, ZFSet.mem_pair.mpr (Or.inr rfl)⟩

theorem zero_ne_one : zero.{u} ≠ one := by
  intro equal
  have member : (∅ : ZFSet.{u}) ∈ ZFSet.powerset ∅ :=
    ZFSet.mem_powerset.mpr (ZFSet.empty_subset _)
  have underlying := congrArg Subtype.val equal
  change (∅ : ZFSet.{u}) = ZFSet.powerset ∅ at underlying
  rw [← underlying] at member
  exact ZFSet.notMem_empty _ member

noncomputable def singleton : Elements (ZFSetList.listCode two.{u}) :=
  ZFSetList.cons zero (ZFSetList.nil two)

theorem wrong_singleton :
    mapValue (fun _ => one.{u}) (mapValue (fun _ => zero) singleton) ≠
      mapValue (fun _ => zero) singleton := by
  intro equal
  simp only [mapValue_eq, singleton, ZFSetList.map_cons, ZFSetList.map_nil] at equal
  exact zero_ne_one (ZFSetList.cons_injective equal).1.symm

/-- This is a countermodel for the actual wrong HOL sentence over the same
validated five-assumption theory, not just a mismatched certificate. -/
theorem wrongFusion_invalid :
    ¬ (model two.{u}).models (UniformListMapFusion.Controls.wrongFusion (Γ := [])) := by
  intro valid
  exact wrong_singleton
    (valid (fun _ => one) trivial (fun _ => zero) trivial singleton trivial)

/-- The correct theorem with those same noncommuting functions is supplied
by the original retained proof. -/
theorem correct_singleton_from_source :
    mapValue (fun _ => one.{u}) (mapValue (fun _ => zero) singleton) =
      mapValue (fun _ => one) singleton :=
  retainedFusion_equation (fun _ => one) (fun _ => zero) singleton

end Controls

#print axioms refinementEquiv
#print axioms refinementCode_substitution
#print axioms refinementMap_preserves_code
#print axioms refinementGraph_apply
#print axioms refinementGraph_square
#print axioms refinementGraph_mem
#print axioms traceGraph_apply
#print axioms traceGraph_application_agreement
#print axioms traceGraph_square
#print axioms traceGraph_mem
#print axioms consumedPoint_code
#print axioms consumedPoint_property
#print axioms Controls.wrongFusion_invalid
#print axioms Controls.correct_singleton_from_source

end Mettapedia.Logic.HOL.Embedding.ZFSetUniformListProofConsumption
