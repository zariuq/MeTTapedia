import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.Consistency
import Mettapedia.Logic.TheoryModel.IdentityCarve

/-!
# Controls: Type : Type, identity, and impredicativity in the set model

**Type : Type has no set model.** A package in which a head types itself is
derivable as such (`typeInType_derives`, and its candidate erasure
`typeInType_candidate`), yet no set model of it exists: a set model would put
the universe's value inside itself, against the irreflexivity of membership
(`no_setModel_of_selfTyping`, `no_setModel_typeInType`). The candidate's tower
package has the model `standardTowerModel` (positive control).

**Identity is extensional in the model.** Identity values are subsingletons
(`ev_id_subsingleton`). The model therefore validates `UIP` as a typing rule
(`uip_holds`) and equality reflection (`reflection_holds`); the candidate
judgment has neither rule, so this is a statement about the model's theory,
not about derivability. In the vocabulary of identity structures, the identity
of every set is thin (`setIdentity_sat_uip`) and lies in the h-set fragment
(`setIdentity_mem_hsetFragment`), so the model's identity structures do not
host the groupoid laws faithfully (`setIdentities_not_hostsFaithfully`, an
instance of `IdentityProofs.not_hostsFaithfully_of_subset_thin`).

**Impredicativity: truth values yes, proof-relevant types no.**

* *Positive.* A trace product of truth values is a truth value, over any
  domain whatever (`tracePiSet_truthCode`, `tracePiSet_subset_singleton`). So
  truth values are closed under quantification over every set, the universes
  and the truth values themselves included: this is the reading of an
  impredicative quantifier `all@A` into `Ω = 𝒫 {∅}`, with its decoder
  `holds (all@A f) ⟶ Π (x : A). holds (f x)` a literal set identity.
* *Negative, by Cantor.* A transitive set containing a set with two distinct
  elements does not contain the trace product of the constant family at that
  set (`not_mem_tracePiSet_const`). Hence in any set model with transitive
  universes, a universe that is impredicative for its own dependent functions
  interprets every one of its types as a subsingleton
  (`impredicative_universe_subsingleton`). Each level of the tower is
  predicative for proof-relevant families (`tower_level_predicative`) and
  impredicative for truth values (`tower_level_truth_impredicative`).

The candidate's rule format uses one `join` for Π and for Σ, and Σ over a
universe never lands in a universe of truth values; its impredicativity enters
through the proposition codes, whose reading is the positive case above.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace Controls

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles Closed)
open ZFSetInterpretation (universeSet universeSet_closed seed_mem_universeSet)
open ZFSetDependentProducts (graph piSet mem_piSet graph_mem_piSet pair_mem_graph mem_familyUnion)
open ZFSetTraceProducts (traceLam traceApp tracePiSet mem_tracePiSet mem_traceLam
  traceApp_graph_beta)
open ZFSetTraceProofDecoding (truthCode mem_truthCode truthCode_subset)
open Mettapedia.Logic.TheoryModel
open Mettapedia.Logic.TheoryModel.IdentityProofs

universe u

/-! ## Type : Type -/

/-- One universe that types itself, with every universe rule. -/
def typeInTypeRules : Rules Unit where
  headTyping _ _ := True
  isUniverse _ := True
  join _ _ _ := True
  cumulative _ _ := True
  headEq _ _ := True

/-- Its annotation: no declared constants and no root steps. -/
abbrev typeInType : ChurchRules typeInTypeRules :=
  ChurchRules.empty typeInTypeRules (fun _ => rfl)

/-- `⊢ U : U` is derivable. -/
theorem typeInType_derives : CDerivable typeInType (.typing .nil (.head ()) (.head ())) :=
  .headType trivial

/-- Its erasure is a candidate derivation of `⊢ U : U`. -/
theorem typeInType_candidate :
    Derivable typeInTypeRules (.typing .nil (.head ()) (.head ())) :=
  typeInType_derives.erase

/-- **A package in which a head types itself has no set model.** -/
theorem no_setModel_of_selfTyping {Head : Type} {R : Rules Head} {P : ChurchRules R} {h : Head}
    (self : R.headTyping h h) (heads : Head → ZFSet.{u}) (consts : DeclName → ZFSet.{u}) :
    ¬ SetModel heads consts P :=
  fun model => model.universes.headTyping_irrefl h self

/-- **Type : Type has no set model.** -/
theorem no_setModel_typeInType (heads : Unit → ZFSet.{u}) (consts : DeclName → ZFSet.{u}) :
    ¬ SetModel heads consts typeInType :=
  no_setModel_of_selfTyping (h := ()) trivial heads consts

/-- Positive control: under `CofinalInaccessibles.{u}` the candidate's tower
package has a set model, so none of its heads types itself. -/
theorem tower_no_selfTyping (h : CofinalInaccessibles.{u}) (head : Tower.Head) :
    ¬ Tower.rules.headTyping head head :=
  fun self => no_setModel_of_selfTyping (P := towerPackage) self _ _ (standardTowerModel h)

/-! ## Identity -/

section Identity

variable {Head : Type} {heads : Head → ZFSet.{u}} {consts : DeclName → ZFSet.{u}}

/-- Identity values are subsingletons. -/
theorem ev_id_subsingleton {n : Nat} (A a b : CTm Head n) (ρ : Env.{u} n) {p q : ZFSet.{u}}
    (hp : p ∈ ev heads consts (.id A a b) ρ) (hq : q ∈ ev heads consts (.id A a b) ρ) :
    p = q :=
  ((mem_truthCode _ _).mp hp).1.trans ((mem_truthCode _ _).mp hq).1.symm

/-- **UIP holds in the set model**: two proofs of one identity are equal,
witnessed by reflexivity at the identity of the identity type. -/
theorem uip_holds {n : Nat} {Γ : CCtx Head n} {A a b p q : CTm Head n}
    (hp : Holds heads consts (.typing Γ p (.id A a b)))
    (hq : Holds heads consts (.typing Γ q (.id A a b))) :
    Holds heads consts (.typing Γ (.refl p) (.id (.id A a b) p q)) := by
  intro ρ sat
  exact (mem_truthCode _ _).mpr ⟨rfl, ev_id_subsingleton A a b ρ (hp ρ sat) (hq ρ sat)⟩

/-- **Equality reflection holds in the set model.** -/
theorem reflection_holds {n : Nat} {Γ : CCtx Head n} {A a b p : CTm Head n}
    (hp : Holds heads consts (.typing Γ p (.id A a b)))
    (ha : Holds heads consts (.typing Γ a A)) :
    Holds heads consts (.equality Γ a b A) :=
  fun ρ sat => ⟨((mem_truthCode _ _).mp (hp ρ sat)).2, ha ρ sat⟩

end Identity

/-- The identity structure of a set in the model: points are its elements,
and the proofs of `x = y` are the elements of the identity value. -/
noncomputable def setIdentity (X : ZFSet.{u}) : IdStructure.{u + 1} where
  Pt := {x : ZFSet.{u} // x ∈ X}
  Pf x y := {p : ZFSet.{u} // p ∈ truthCode (x.1 = y.1)}
  refl x := ⟨∅, empty_mem_truthCode_eq x.1⟩
  inv p := ⟨∅, (mem_truthCode _ _).mpr ⟨rfl, ((mem_truthCode _ _).mp p.2).2.symm⟩⟩
  comp p q := ⟨∅, (mem_truthCode _ _).mpr
    ⟨rfl, ((mem_truthCode _ _).mp p.2).2.trans ((mem_truthCode _ _).mp q.2).2⟩⟩

theorem setIdentity_pf_eq (X : ZFSet.{u}) {x y : (setIdentity X).Pt}
    (p q : (setIdentity X).Pf x y) : p = q :=
  Subtype.ext (((mem_truthCode _ _).mp p.2).1.trans ((mem_truthCode _ _).mp q.2).1.symm)

/-- The identity of every set is thin. -/
theorem setIdentity_sat_uip (X : ZFSet.{u}) : (setIdentity X).Sat .uip :=
  fun p q => setIdentity_pf_eq X p q

/-- **The identity of every set lies in the h-set fragment.** -/
theorem setIdentity_mem_hsetFragment (X : ZFSet.{u}) : setIdentity X ∈ hsetFragment := by
  refine ⟨mem_models_groupoidLaws ?_ ?_ ?_ ?_ ?_, ?_⟩
  · exact fun _ _ _ => setIdentity_pf_eq X _ _
  · exact fun _ => setIdentity_pf_eq X _ _
  · exact fun _ => setIdentity_pf_eq X _ _
  · exact fun _ => setIdentity_pf_eq X _ _
  · exact fun _ => setIdentity_pf_eq X _ _
  · intro φ hφ
    rw [Set.mem_singleton_iff.mp hφ]
    exact setIdentity_sat_uip X

/-- The identity structures of the set model. -/
def setIdentities : Set IdStructure.{u + 1} := Set.range setIdentity

theorem setIdentities_subset_thin : setIdentities.{u} ⊆ thin := by
  rintro _ ⟨X, rfl⟩
  exact setIdentity_sat_uip X

/-- **The model's identity is the h-set carve**: its identity structures do
not host the groupoid laws faithfully. -/
theorem setIdentities_not_hostsFaithfully :
    ¬ HostsFaithfully IdStructure.Sat setIdentities.{u} groupoidLaws :=
  not_hostsFaithfully_of_subset_thin setIdentities_subset_thin

/-! ## Impredicativity -/

private theorem value_of_mem_piSet {a f x : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (hf : f ∈ piSet a b) (hx : x ∈ a) : ∃ y, ZFSet.pair x y ∈ f ∧ y ∈ b x := by
  obtain ⟨y, hy, _⟩ := (mem_piSet.mp hf).1.2 x hx
  exact ⟨y, hy, (mem_piSet.mp hf).2 x hx y hy⟩

/-- A trace product whose fibres are truth values is a truth value. -/
theorem tracePiSet_subset_singleton {a : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (fibres : ∀ x ∈ a, b x ⊆ {∅}) : tracePiSet a b ⊆ {∅} := by
  intro t ht
  obtain ⟨f, hf, rfl⟩ := mem_tracePiSet.mp ht
  refine ZFSet.mem_singleton.mpr (ZFSet.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩)
  · obtain ⟨x, y, w, hxy, hwy, rfl⟩ := mem_traceLam.mp hz
    have hx : x ∈ a := (ZFSet.pair_mem_prod.mp ((mem_piSet.mp hf).1.1 hxy)).1
    have hy : y = ∅ := ZFSet.mem_singleton.mp (fibres x hx ((mem_piSet.mp hf).2 x hx y hxy))
    rw [hy] at hwy
    exact absurd hwy (ZFSet.notMem_empty w)
  · exact absurd hz (ZFSet.notMem_empty z)

/-- **The reading of an impredicative quantifier**: the trace product of a
family of truth values over any domain is the truth value of the universal
statement. -/
theorem tracePiSet_truthCode (a : ZFSet.{u}) (P : ZFSet.{u} → Prop) :
    tracePiSet a (fun x => truthCode (P x)) = truthCode (∀ x ∈ a, P x) := by
  apply ZFSet.ext
  intro t
  rw [mem_truthCode]
  constructor
  · intro ht
    refine ⟨ZFSet.mem_singleton.mp
      (tracePiSet_subset_singleton (fun x _ => truthCode_subset (P x)) ht), fun x hx => ?_⟩
    obtain ⟨f, hf, rfl⟩ := mem_tracePiSet.mp ht
    obtain ⟨y, _, hy⟩ := value_of_mem_piSet hf hx
    exact ((mem_truthCode _ _).mp hy).2
  · rintro ⟨rfl, all⟩
    have hg : graph a (fun _ => ∅) ∈ piSet a (fun x => truthCode (P x)) :=
      graph_mem_piSet fun x hx => (mem_truthCode _ _).mpr ⟨rfl, all x hx⟩
    refine mem_tracePiSet.mpr ⟨_, hg, ZFSet.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
    · obtain ⟨x, y, w, hxy, hwy, rfl⟩ := mem_traceLam.mp hz
      rw [(pair_mem_graph.mp hxy).2.symm] at hwy
      exact absurd hwy (ZFSet.notMem_empty w)
    · exact absurd hz (ZFSet.notMem_empty z)

/-- **Cantor.** A transitive set containing a set with two distinct elements
does not contain the trace product of the constant family at that set. -/
theorem not_mem_tracePiSet_const {U B b₀ b₁ : ZFSet.{u}} (transitive : U.IsTransitive)
    (h₀ : b₀ ∈ B) (h₁ : b₁ ∈ B) (distinct : b₀ ≠ b₁) :
    tracePiSet U (fun _ => B) ∉ U := by
  classical
  intro closed
  let χ : Set {x // x ∈ U} → ZFSet.{u} → ZFSet.{u} :=
    fun S X => if ∃ hX : X ∈ U, (⟨X, hX⟩ : {x // x ∈ U}) ∈ S then b₁ else b₀
  have χ_mem : ∀ S X, χ S X ∈ B := by
    intro S X
    by_cases hX : ∃ hX : X ∈ U, (⟨X, hX⟩ : {x // x ∈ U}) ∈ S
    · simp only [χ, if_pos hX]
      exact h₁
    · simp only [χ, if_neg hX]
      exact h₀
  let code : Set {x // x ∈ U} → {x // x ∈ U} := fun S =>
    ⟨traceLam (graph U (χ S)),
      transitive.subset_of_mem closed (traceLam_graph_mem fun X _ => χ_mem S X)⟩
  apply Function.cantor_injective code
  intro S S' same
  have values : ∀ X (hX : X ∈ U), χ S X = χ S' X := by
    intro X hX
    have := congrArg (fun t => traceApp t X) (congrArg Subtype.val same)
    simp only [code, traceApp_graph_beta _ hX] at this
    exact this
  ext ⟨X, hX⟩
  have e := values X hX
  constructor
  · intro inS
    by_contra notInS'
    have lhs : χ S X = b₁ := if_pos ⟨hX, inS⟩
    have rhs : χ S' X = b₀ := if_neg fun ⟨_, h⟩ => notInS' h
    exact distinct (rhs.symm.trans (e.symm.trans lhs))
  · intro inS'
    by_contra notInS
    have lhs : χ S X = b₀ := if_neg fun ⟨_, h⟩ => notInS h
    have rhs : χ S' X = b₁ := if_pos ⟨hX, inS'⟩
    exact distinct (lhs.symm.trans (e.trans rhs))

/-- **An impredicative universe with transitive value is proof-irrelevant.**
In a set model, if a universe `u` of type `v` is closed under dependent
functions over itself (`join v u u`) and its value is transitive, every type
in it has at most one element. -/
theorem impredicative_universe_subsingleton {Head : Type} {R : Rules Head} {P : ChurchRules R}
    {heads : Head → ZFSet.{u}} {consts : DeclName → ZFSet.{u}} (model : SetModel heads consts P)
    {uHead v : Head} (typed : R.headTyping uHead v) (impredicative : R.join v uHead uHead)
    (transitive : (heads uHead).IsTransitive) {B : ZFSet.{u}} (hB : B ∈ heads uHead)
    {b₀ b₁ : ZFSet.{u}} (h₀ : b₀ ∈ B) (h₁ : b₁ ∈ B) : b₀ = b₁ := by
  by_contra distinct
  exact not_mem_tracePiSet_const transitive h₀ h₁ distinct
    (model.universes.pi_mem impredicative (model.universes.headTyping_mem typed)
      (fun _ => B) (fun _ _ => hB))

/-- Each level of the tower is predicative for proof-relevant families: the
functions from the level into the two-element set `{∅, {∅}}` escape it. -/
theorem tower_level_predicative (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (k : Nat) :
    tracePiSet (universeSet h seed k) (fun _ => ({∅, {∅}} : ZFSet.{u})) ∉ universeSet h seed k :=
  not_mem_tracePiSet_const (universeSet_closed h seed k).transitive
    (ZFSet.mem_insert _ _) (ZFSet.mem_insert_of_mem _ (ZFSet.mem_singleton.mpr rfl))
    (fun e => ZFSet.notMem_empty ∅ (by
      have : (∅ : ZFSet.{u}) ∈ ({∅} : ZFSet.{u}) := ZFSet.mem_singleton.mpr rfl
      rwa [← e] at this))

/-- Each level of the tower is impredicative for truth values: quantifying a
family of truth values over any level, however large, stays in the bottom
level. -/
theorem tower_level_truth_impredicative (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    (j k : Nat) (P : ZFSet.{u} → Prop) :
    tracePiSet (universeSet h seed k) (fun x => truthCode (P x)) ∈ universeSet h seed j := by
  rw [tracePiSet_truthCode]
  exact CumulativePiSigmaId.ZFSetTraceUniverseInterpretation.truthCode_mem h seed j _

end Controls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
