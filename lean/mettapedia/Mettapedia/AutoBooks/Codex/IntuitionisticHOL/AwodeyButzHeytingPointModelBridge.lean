import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzHeyting
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzHigherOrderPointModelBridge

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v

namespace HigherOrderPointHeytingGlobalModelBridge

variable {Base : Type u} {Const : Ty Base → Type v}

/--
Minimal one-point witness for the full topological layer over a global model.

The existing higher-order point bridge packages term evaluation over the discrete
one-point carrier, but the stronger Heyting layer still needs a full
`TopologicalInterpretation` together with a typed identification between the
model carriers and that interpretation's fibers.
-/
structure OnePointTopologicalWitness (M : GlobalModel Base Const) where
  toTopologicalInterpretation : TopologicalInterpretation Base Const PUnit
  carrierEquiv : ∀ τ : Ty Base, M.Carrier τ ≃ (toTopologicalInterpretation.space τ).Carrier
  carrierEquiv_proj : ∀ (τ : Ty Base) (x : M.Carrier τ),
    (toTopologicalInterpretation.space τ).proj (carrierEquiv τ x) = ()
  const_eq : ∀ {τ : Ty Base} (c : Const τ),
    carrierEquiv τ (M.const c) = (toTopologicalInterpretation.const c).toContinuousMap ()

namespace OnePointTopologicalWitness

variable {M : GlobalModel Base Const} (W : OnePointTopologicalWitness M)

/-- Context spaces of the witnessed full topological interpretation. -/
abbrev ctxSpace (Γ : Ctx Base) : EtaleSpace PUnit :=
  W.toTopologicalInterpretation.ctxSpace Γ

/-- Encode a semantic carrier element into the witnessed one-point topological fiber. -/
abbrev encode {τ : Ty Base} (x : M.Carrier τ) :
    (W.toTopologicalInterpretation.space τ).Carrier :=
  W.carrierEquiv τ x

/-- Decode a witnessed one-point topological fiber element back to the model carrier. -/
abbrev decode {τ : Ty Base}
    (x : (W.toTopologicalInterpretation.space τ).Carrier) : M.Carrier τ :=
  (W.carrierEquiv τ).symm x

@[simp] theorem decode_encode {τ : Ty Base} (x : M.Carrier τ) :
    W.decode (W.encode x) = x :=
  (W.carrierEquiv τ).left_inv x

@[simp] theorem encode_decode {τ : Ty Base}
    (x : (W.toTopologicalInterpretation.space τ).Carrier) :
    W.encode (W.decode x) = x :=
  (W.carrierEquiv τ).right_inv x

@[simp] theorem encode_proj {τ : Ty Base} (x : M.Carrier τ) :
    (W.toTopologicalInterpretation.space τ).proj (W.encode x) = () :=
  W.carrierEquiv_proj τ x

@[simp] theorem ctx_proj_eq_unit
    {Γ : Ctx Base}
    (γ : (W.ctxSpace Γ).Carrier) :
    (W.ctxSpace Γ).proj γ = () :=
  Subsingleton.elim _ _

/--
Encode a point of the archive-free one-point higher-order context carrier into
the context carrier of the witnessed full topological interpretation.
-/
noncomputable def encodeCtx :
    {Γ : Ctx Base} →
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier →
      (W.ctxSpace Γ).Carrier
  | [], _ => by
      simpa using (PUnit.unit : (EtaleSpace.terminal PUnit).Carrier)
  | σ :: Γ, γ => by
      change
        (EtaleSpace.prod (W.toTopologicalInterpretation.space σ) (W.ctxSpace Γ)).Carrier
      refine ⟨
        (W.encode
            (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.headVal (M := M) γ),
          encodeCtx
            (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.tailCtx (M := M) γ)),
        ?_⟩
      calc
        (W.toTopologicalInterpretation.space σ).proj
            (W.encode
              (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.headVal (M := M) γ)) = () := by
              exact W.encode_proj
                (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.headVal (M := M) γ)
        _ = (W.ctxSpace Γ).proj
              (encodeCtx
                (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.tailCtx (M := M) γ)) := by
              exact (W.ctx_proj_eq_unit _).symm

/--
Decode a point of the witnessed full topological context carrier back to the
archive-free one-point higher-order context carrier.
-/
noncomputable def decodeCtx :
    {Γ : Ctx Base} →
      (W.ctxSpace Γ).Carrier →
      (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier
  | [], _ => by
      simpa using (PUnit.unit : (EtaleSpace.terminal PUnit).Carrier)
  | σ :: Γ, γ => by
      change
        (EtaleSpace.prod
          ((HigherOrderPointTopologicalGlobalModelBridge.basicInterp (M := M)).space σ)
          (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ)).Carrier
      refine ⟨
        ((HigherOrderPointTopologicalGlobalModelBridge.basicInterp.pointCarrier
            (M := M) (τ := σ)
            (W.decode
              (EtaleSpace.prodFst (W.toTopologicalInterpretation.space σ) (W.ctxSpace Γ) γ))),
          decodeCtx
            (EtaleSpace.prodSnd (W.toTopologicalInterpretation.space σ) (W.ctxSpace Γ) γ)),
        ?_⟩
      simp [HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctx_proj_eq_unit]

@[simp] theorem encodeCtx_nil :
    W.encodeCtx (Γ := []) PUnit.unit = PUnit.unit :=
  rfl

@[simp] theorem decodeCtx_nil :
    W.decodeCtx (Γ := []) PUnit.unit = PUnit.unit :=
  rfl

@[simp] theorem encode_const
    {τ : Ty Base} (c : Const τ) :
    W.encode (M.const c) = (W.toTopologicalInterpretation.const c).toContinuousMap () :=
  W.const_eq c

/-- Encode a proposition carrier element into the explicit proposition space. -/
abbrev encodeProp (p : M.Carrier .prop) :
    W.toTopologicalInterpretation.propSpace.Carrier :=
  W.toTopologicalInterpretation.propCarrierCast (W.encode p)

/-- Decode an explicit proposition-space point back to the native proposition carrier. -/
abbrev decodeProp
    (p : W.toTopologicalInterpretation.propSpace.Carrier) : M.Carrier .prop :=
  W.decode (W.toTopologicalInterpretation.propCarrierUncast p)

@[simp] theorem decodeProp_encodeProp (p : M.Carrier .prop) :
    W.decodeProp (W.encodeProp p) = p := by
  unfold decodeProp encodeProp
  simp

@[simp] theorem encodeProp_decodeProp
    (p : W.toTopologicalInterpretation.propSpace.Carrier) :
    W.encodeProp (W.decodeProp p) = p := by
  unfold decodeProp encodeProp
  simp

@[simp] theorem encodeProp_proj (p : M.Carrier .prop) :
    W.toTopologicalInterpretation.propSpace.proj (W.encodeProp p) = () := by
  unfold encodeProp
  rw [W.toTopologicalInterpretation.propProjCast]

end OnePointTopologicalWitness

/--
Minimal one-point witness for the proposition-space layer.

This is the connective-only stage between the concrete full topological witness
and the full Heyting interpretation. Equality and quantifiers are intentionally
left for the next layer.
-/
structure OnePointPropositionWitness (M : GlobalModel Base Const)
    extends OnePointTopologicalWitness M where
  propTop : toTopologicalInterpretation.propSpace.GlobalSection
  propBot : toTopologicalInterpretation.propSpace.GlobalSection
  fiberMeet : PropFiberPair toTopologicalInterpretation.propSpace →
    toTopologicalInterpretation.propSpace.Carrier
  fiberJoin : PropFiberPair toTopologicalInterpretation.propSpace →
    toTopologicalInterpretation.propSpace.Carrier
  fiberHimp : PropFiberPair toTopologicalInterpretation.propSpace →
    toTopologicalInterpretation.propSpace.Carrier
  propTop_eq :
    propTop.toContinuousMap () = toOnePointTopologicalWitness.encodeProp M.topP
  propBot_eq :
    propBot.toContinuousMap () = toOnePointTopologicalWitness.encodeProp M.botP
  fiberMeet_eq : ∀ (p q : M.Carrier .prop),
    fiberMeet
        ⟨(toOnePointTopologicalWitness.encodeProp p,
          toOnePointTopologicalWitness.encodeProp q), by simp⟩ =
      toOnePointTopologicalWitness.encodeProp (M.andP p q)
  fiberJoin_eq : ∀ (p q : M.Carrier .prop),
    fiberJoin
        ⟨(toOnePointTopologicalWitness.encodeProp p,
          toOnePointTopologicalWitness.encodeProp q), by simp⟩ =
      toOnePointTopologicalWitness.encodeProp (M.orP p q)
  fiberHimp_eq : ∀ (p q : M.Carrier .prop),
    fiberHimp
        ⟨(toOnePointTopologicalWitness.encodeProp p,
          toOnePointTopologicalWitness.encodeProp q), by simp⟩ =
      toOnePointTopologicalWitness.encodeProp (M.impP p q)

namespace OnePointPropositionWitness

variable {M : GlobalModel Base Const} (W : OnePointPropositionWitness M)

/-- Forget the proposition-space packaging and recover the underlying topological witness. -/
abbrev toTopological : OnePointTopologicalWitness M :=
  W.toOnePointTopologicalWitness

@[simp] theorem fiberMeet_proj
    (pq : PropFiberPair W.toTopologicalInterpretation.propSpace) :
    W.toTopologicalInterpretation.propSpace.proj (W.fiberMeet pq) =
      W.toTopologicalInterpretation.propSpace.proj pq.val.1 :=
  Subsingleton.elim _ _

@[simp] theorem fiberJoin_proj
    (pq : PropFiberPair W.toTopologicalInterpretation.propSpace) :
    W.toTopologicalInterpretation.propSpace.proj (W.fiberJoin pq) =
      W.toTopologicalInterpretation.propSpace.proj pq.val.1 :=
  Subsingleton.elim _ _

@[simp] theorem fiberHimp_proj
    (pq : PropFiberPair W.toTopologicalInterpretation.propSpace) :
    W.toTopologicalInterpretation.propSpace.proj (W.fiberHimp pq) =
      W.toTopologicalInterpretation.propSpace.proj pq.val.1 :=
  Subsingleton.elim _ _

@[simp] theorem propTop_apply :
    W.propTop.toContinuousMap () = W.encodeProp M.topP :=
  W.propTop_eq

@[simp] theorem propBot_apply :
    W.propBot.toContinuousMap () = W.encodeProp M.botP :=
  W.propBot_eq

@[simp] theorem fiberMeet_apply (p q : M.Carrier .prop) :
    W.fiberMeet ⟨(W.encodeProp p, W.encodeProp q), by simp⟩ =
      W.encodeProp (M.andP p q) :=
  W.fiberMeet_eq p q

@[simp] theorem fiberJoin_apply (p q : M.Carrier .prop) :
    W.fiberJoin ⟨(W.encodeProp p, W.encodeProp q), by simp⟩ =
      W.encodeProp (M.orP p q) :=
  W.fiberJoin_eq p q

@[simp] theorem fiberHimp_apply (p q : M.Carrier .prop) :
    W.fiberHimp ⟨(W.encodeProp p, W.encodeProp q), by simp⟩ =
      W.encodeProp (M.impP p q) :=
  W.fiberHimp_eq p q

end OnePointPropositionWitness

/--
Minimal concrete one-point witness for the Heyting layer.

This packages a full one-point `HeytingTopologicalInterpretation` together with
its typed carrier identification back to the archive-free global-model point
bridge. The remaining blocker is to *construct* such a witness for the intended
Awodey-Butz models, not to guess what interface the stronger theorem needs.
-/
structure OnePointHeytingWitness (M : GlobalModel Base Const)
    extends OnePointTopologicalWitness M where
  toHeytingInterpretation : HeytingTopologicalInterpretation Base Const PUnit
  underlying_eq :
    toHeytingInterpretation.toTopologicalInterpretation = toTopologicalInterpretation

namespace OnePointHeytingWitness

variable {M : GlobalModel Base Const} (W : OnePointHeytingWitness M)

/-- Forget the one-point compatibility data and recover the concrete Heyting interpretation. -/
abbrev toHeyting : HeytingTopologicalInterpretation Base Const PUnit :=
  W.toHeytingInterpretation

@[simp] theorem toHeyting_toTopological :
    W.toHeyting.toTopologicalInterpretation = W.toTopologicalInterpretation :=
  W.underlying_eq

end OnePointHeytingWitness

section ConcreteOnePointWitness

open EtaleSpace
open SimpleQuantifiedTopologicalGlobalModelBridge
open CategoryTheory
open TopologicalSpace
open TopologicalSpace.Opens

variable (M : GlobalModel Base Const)

@[simp] theorem point_base_proj_eq_unit {E : EtaleSpace PUnit} (x : E.Carrier) :
    E.proj x = () :=
  Subsingleton.elim _ _

/-- Any point in an etale space over `PUnit` determines a global section. -/
noncomputable def globalSectionOfPoint {E : EtaleSpace PUnit} (x : E.Carrier) :
    E.GlobalSection where
  toContinuousMap :=
    { toFun := fun _ => x
      continuous_toFun := continuous_const }
  proj_comp := by
    funext u
    cases u
    exact point_base_proj_eq_unit x

@[simp] theorem globalSectionOfPoint_apply {E : EtaleSpace PUnit} (x : E.Carrier) (u : PUnit) :
    (globalSectionOfPoint x).toContinuousMap u = x :=
  rfl

/-- The discrete one-point etale space is fiberwise equivalent to its carrier type. -/
def pointEtaleCarrierEquiv (A : Type*) : A ≃ (pointEtale A).Carrier where
  toFun := fun a => ((), a)
  invFun := Prod.snd
  left_inv := by
    intro a
    rfl
  right_inv := by
    intro p
    cases p
    rfl

/-- Every local morphism over a nonempty open of `PUnit` is just a function on carriers. -/
noncomputable def functionOfLocalMorphism
    {F E : EtaleSpace PUnit} {U : Opens PUnit}
    (f : LocalMorphism F E U) (hU : () ∈ U) :
    F.Carrier → E.Carrier :=
  fun x => f.toFun ⟨x, by simpa [point_base_proj_eq_unit x] using hU⟩

/-- Any carrier function yields a local morphism over the top open of `PUnit`. -/
noncomputable def localMorphismOfFunction
    {F E : EtaleSpace PUnit}
    (f : F.Carrier → E.Carrier) :
    LocalMorphism F E ⊤ where
  toFun := fun x => f x.1
  continuous_toFun := by
    let _ : DiscreteTopology F.Carrier := EtaleSpace.discreteTopology_of_discrete_base F
    exact (continuous_of_discreteTopology : Continuous f).comp continuous_subtype_val
  fiberwise := by
    intro x
    simp

@[simp] theorem functionOfLocalMorphism_localMorphismOfFunction
    {F E : EtaleSpace PUnit}
    (f : F.Carrier → E.Carrier) :
    functionOfLocalMorphism (localMorphismOfFunction f) (show () ∈ (⊤ : Opens PUnit) from by simp) = f := by
  funext x
  rfl

theorem restrict_localMorphismOfFunction_functionOfLocalMorphism
    {F E : EtaleSpace PUnit} {U : Opens PUnit}
    (f : LocalMorphism F E U) (hU : () ∈ U) :
    LocalMorphism.restrict (homOfLE (show U ≤ (⊤ : Opens PUnit) from by intro x _hx; simp)) 
        (localMorphismOfFunction (functionOfLocalMorphism f hU)) = f := by
  ext x
  simp [functionOfLocalMorphism, localMorphismOfFunction]

/-- Decode a germ in the one-point exponential as an honest carrier function. -/
noncomputable def functionOfExpCarrier
    {F E : EtaleSpace PUnit}
    (q : (EtaleSpace.exp F E).Carrier) :
    F.Carrier → E.Carrier :=
  Quotient.liftOn q
    (fun a =>
      functionOfLocalMorphism a.2.morphism a.2.mem_nbhd)
    (by
      intro a b h
      funext x
      rcases h with ⟨hbase, W, hxW, hWa, hWb, hEq⟩
      have hxW' : F.proj x ∈ W := by
        simpa [point_base_proj_eq_unit x] using hxW
      have hVal :
          (LocalMorphism.restrict (homOfLE hWa) a.2.morphism).toFun ⟨x, hxW'⟩ =
            (LocalMorphism.restrict (homOfLE hWb) b.2.morphism).toFun ⟨x, hxW'⟩ := by
        simpa using congrFun (congrArg LocalMorphism.toFun hEq) ⟨x, hxW'⟩
      simpa [functionOfLocalMorphism, point_base_proj_eq_unit] using hVal)

/-- Encode an honest carrier function as a germ in the one-point exponential. -/
noncomputable def expCarrierOfFunction
    {F E : EtaleSpace PUnit}
    (f : F.Carrier → E.Carrier) :
    (EtaleSpace.exp F E).Carrier :=
  EtaleSpace.sectionMapOfLocalMorphism (localMorphismOfFunction f) ⟨(), by simp⟩

@[simp] theorem functionOfExpCarrier_expCarrierOfFunction
    {F E : EtaleSpace PUnit}
    (f : F.Carrier → E.Carrier) :
    functionOfExpCarrier (expCarrierOfFunction f) = f := by
  funext x
  change functionOfLocalMorphism (localMorphismOfFunction f) (by simp) x = f x
  rfl

@[simp] theorem expCarrierOfFunction_functionOfExpCarrier
    {F E : EtaleSpace PUnit}
    (q : (EtaleSpace.exp F E).Carrier) :
    expCarrierOfFunction (functionOfExpCarrier q) = q := by
  refine Quotient.inductionOn q ?_
  intro a
  let f : F.Carrier → E.Carrier := functionOfLocalMorphism a.2.morphism a.2.mem_nbhd
  have hSame :
      ExpRaw.SameGerm
        ⟨(), {
          nbhd := (⊤ : Opens PUnit)
          mem_nbhd := by simp
          morphism := localMorphismOfFunction f
        }⟩
        a := by
    refine ⟨Subsingleton.elim _ _, a.2.nbhd, ?_, ?_, le_rfl, ?_⟩
    · simpa using a.2.mem_nbhd
    · intro x hx
      simp
    · simpa [f] using
        restrict_localMorphismOfFunction_functionOfLocalMorphism
          (f := a.2.morphism) a.2.mem_nbhd
  exact
    (EtaleSpace.sectionMapOfLocalMorphism_eq_iff_sameGerm
      (localMorphismOfFunction f) a.2.morphism
      ⟨(), by simp⟩
      ⟨a.1, a.2.mem_nbhd⟩).2 hSame

/-- Exponentials over the one-point base collapse to ordinary function spaces. -/
noncomputable def expCarrierEquivFunction
    (F E : EtaleSpace PUnit) :
    (EtaleSpace.exp F E).Carrier ≃ (F.Carrier → E.Carrier) where
  toFun := functionOfExpCarrier
  invFun := expCarrierOfFunction
  left_inv := expCarrierOfFunction_functionOfExpCarrier
  right_inv := functionOfExpCarrier_expCarrierOfFunction

/-- Arrow carriers in a global model are equivalent to honest functions. -/
def arrowCarrierEquiv (σ τ : Ty Base) :
    M.Carrier (.arr σ τ) ≃ (M.Carrier σ → M.Carrier τ) where
  toFun := fun f x => M.app f x
  invFun := fun f => M.lam f
  left_inv := by
    intro f
    simpa using M.eta f
  right_inv := by
    intro f
    funext x
    simpa using M.beta f x

/-- The recursive one-point topological carrier family attached to a global model. -/
noncomputable def onePointSpace : Ty Base → EtaleSpace PUnit
  | .prop => pointEtale (M.Carrier .prop)
  | .base b => pointEtale (M.Carrier (.base b))
  | .arr σ τ => EtaleSpace.exp (onePointSpace σ) (onePointSpace τ)

/-- Typed carrier equivalence between the global model and the one-point topological family. -/
noncomputable def onePointCarrierEquiv : ∀ τ : Ty Base, M.Carrier τ ≃ (onePointSpace (M := M) τ).Carrier
  | .prop => pointEtaleCarrierEquiv (M.Carrier .prop)
  | .base b => pointEtaleCarrierEquiv (M.Carrier (.base b))
  | .arr σ τ =>
      (arrowCarrierEquiv (M := M) σ τ).trans <|
        (Equiv.arrowCongr (onePointCarrierEquiv σ) (onePointCarrierEquiv τ)).trans <|
          (expCarrierEquivFunction (onePointSpace (M := M) σ) (onePointSpace (M := M) τ)).symm

/-- Constants become global sections via the concrete carrier equivalence. -/
noncomputable def onePointConstSection :
    {τ : Ty Base} → Const τ → (onePointSpace (M := M) τ).GlobalSection
  | τ, c => globalSectionOfPoint ((onePointCarrierEquiv (M := M) τ) (M.const c))

/-- The concrete one-point full topological interpretation induced by a global model. -/
noncomputable def concreteOnePointTopologicalInterpretation :
    TopologicalInterpretation Base Const PUnit where
  space := onePointSpace (M := M)
  const := onePointConstSection (M := M)
  propSpace := pointEtale (M.Carrier .prop)
  baseSpace := fun b => pointEtale (M.Carrier (.base b))
  space_prop := rfl
  space_base := by
    intro b
    rfl
  space_arr := by
    intro σ τ
    rfl

/-- A concrete inhabitant of the minimal one-point topological witness layer. -/
noncomputable def concreteOnePointTopologicalWitness :
    OnePointTopologicalWitness M where
  toTopologicalInterpretation := concreteOnePointTopologicalInterpretation (M := M)
  carrierEquiv := onePointCarrierEquiv (M := M)
  carrierEquiv_proj := by
    intro τ x
    exact point_base_proj_eq_unit ((onePointCarrierEquiv (M := M) τ) x)
  const_eq := by
    intro τ c
    simp [concreteOnePointTopologicalInterpretation, onePointConstSection, globalSectionOfPoint]

@[simp] theorem concreteOnePointTopologicalWitness_encode
    {τ : Ty Base} (x : M.Carrier τ) :
    (concreteOnePointTopologicalWitness (M := M)).encode x =
      (onePointCarrierEquiv (M := M) τ) x :=
  rfl

@[simp] theorem concreteOnePointTopologicalWitness_const
    {τ : Ty Base} (c : Const τ) :
    (concreteOnePointTopologicalWitness (M := M)).encode (M.const c) =
      (concreteOnePointTopologicalInterpretation (M := M).const c).toContinuousMap () :=
  by
    simp [concreteOnePointTopologicalWitness, concreteOnePointTopologicalInterpretation,
      onePointConstSection, globalSectionOfPoint]

private noncomputable def concretePropTopSection :
    (concreteOnePointTopologicalInterpretation (M := M)).propSpace.GlobalSection :=
  globalSectionOfPoint ((concreteOnePointTopologicalWitness (M := M)).encodeProp M.topP)

private noncomputable def concretePropBotSection :
    (concreteOnePointTopologicalInterpretation (M := M)).propSpace.GlobalSection :=
  globalSectionOfPoint ((concreteOnePointTopologicalWitness (M := M)).encodeProp M.botP)

private noncomputable def concreteFiberMeet
    (pq : PropFiberPair (concreteOnePointTopologicalInterpretation (M := M)).propSpace) :
    (concreteOnePointTopologicalInterpretation (M := M)).propSpace.Carrier :=
  (concreteOnePointTopologicalWitness (M := M)).encodeProp
    (M.andP
      ((concreteOnePointTopologicalWitness (M := M)).decodeProp pq.val.1)
      ((concreteOnePointTopologicalWitness (M := M)).decodeProp pq.val.2))

private noncomputable def concreteFiberJoin
    (pq : PropFiberPair (concreteOnePointTopologicalInterpretation (M := M)).propSpace) :
    (concreteOnePointTopologicalInterpretation (M := M)).propSpace.Carrier :=
  (concreteOnePointTopologicalWitness (M := M)).encodeProp
    (M.orP
      ((concreteOnePointTopologicalWitness (M := M)).decodeProp pq.val.1)
      ((concreteOnePointTopologicalWitness (M := M)).decodeProp pq.val.2))

private noncomputable def concreteFiberHimp
    (pq : PropFiberPair (concreteOnePointTopologicalInterpretation (M := M)).propSpace) :
    (concreteOnePointTopologicalInterpretation (M := M)).propSpace.Carrier :=
  (concreteOnePointTopologicalWitness (M := M)).encodeProp
    (M.impP
      ((concreteOnePointTopologicalWitness (M := M)).decodeProp pq.val.1)
      ((concreteOnePointTopologicalWitness (M := M)).decodeProp pq.val.2))

/-- Concrete connective-only proposition witness above the one-point topological witness. -/
noncomputable def concreteOnePointPropositionWitness :
    OnePointPropositionWitness M where
  toOnePointTopologicalWitness := concreteOnePointTopologicalWitness (M := M)
  propTop := concretePropTopSection (M := M)
  propBot := concretePropBotSection (M := M)
  fiberMeet := concreteFiberMeet (M := M)
  fiberJoin := concreteFiberJoin (M := M)
  fiberHimp := concreteFiberHimp (M := M)
  propTop_eq := by
    change
      (globalSectionOfPoint
        ((concreteOnePointTopologicalWitness (M := M)).encodeProp M.topP)).toContinuousMap () =
        (concreteOnePointTopologicalWitness (M := M)).encodeProp M.topP
    exact globalSectionOfPoint_apply _ ()
  propBot_eq := by
    change
      (globalSectionOfPoint
        ((concreteOnePointTopologicalWitness (M := M)).encodeProp M.botP)).toContinuousMap () =
        (concreteOnePointTopologicalWitness (M := M)).encodeProp M.botP
    exact globalSectionOfPoint_apply _ ()
  fiberMeet_eq := by
    intro p q
    simp [concreteFiberMeet]
  fiberJoin_eq := by
    intro p q
    simp [concreteFiberJoin]
  fiberHimp_eq := by
    intro p q
    simp [concreteFiberHimp]

@[simp] theorem concreteOnePointPropositionWitness_top :
    (concreteOnePointPropositionWitness (M := M)).propTop.toContinuousMap () =
      (concreteOnePointPropositionWitness (M := M)).encodeProp M.topP := by
  exact (concreteOnePointPropositionWitness (M := M)).propTop_apply

@[simp] theorem concreteOnePointPropositionWitness_meet
    (p q : M.Carrier .prop) :
    (concreteOnePointPropositionWitness (M := M)).fiberMeet
        ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp p,
          (concreteOnePointPropositionWitness (M := M)).encodeProp q), by simp⟩ =
      (concreteOnePointPropositionWitness (M := M)).encodeProp (M.andP p q) := by
  exact (concreteOnePointPropositionWitness (M := M)).fiberMeet_apply p q

@[simp] theorem concreteOnePointPropositionWitness_himp
    (p q : M.Carrier .prop) :
    (concreteOnePointPropositionWitness (M := M)).fiberHimp
        ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp p,
          (concreteOnePointPropositionWitness (M := M)).encodeProp q), by simp⟩ =
      (concreteOnePointPropositionWitness (M := M)).encodeProp (M.impP p q) := by
  exact (concreteOnePointPropositionWitness (M := M)).fiberHimp_apply p q

open HigherOrderPointTopologicalGlobalModelBridge

/-- The native proposition carrier obtained by evaluating a full HOL formula at
the one-point topological context. -/
noncomputable abbrev pointFormulaValue
    {Γ : Ctx Base}
    (φ : Formula Const Γ)
    (γ : (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier) :
    M.Carrier .prop :=
  HigherOrderPointTopologicalGlobalModelBridge.basicInterp.pointCarrierVal (M := M)
    (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.eval (M := M) φ γ)

@[simp] theorem pointFormulaValue_eq_semilocalEval
    {Γ : Ctx Base}
    (φ : Formula Const Γ)
    (γ : (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier) :
    pointFormulaValue (M := M) φ γ =
      SemilocalModel.eval M.toSemilocalModel
        (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.decodeEnv (M := M) γ) φ := by
  unfold pointFormulaValue
  exact
    (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.eval_val_decode
      (M := M) (t := φ) γ)

@[simp] theorem pointFormulaValue_top
    {Γ : Ctx Base}
    (γ : (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier) :
    pointFormulaValue (M := M) (Term.top : Formula Const Γ) γ = M.topP := by
  simp [pointFormulaValue, SemilocalModel.eval]

@[simp] theorem pointFormulaValue_and
    {Γ : Ctx Base}
    (φ ψ : Formula Const Γ)
    (γ : (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier) :
    pointFormulaValue (M := M) (Term.and φ ψ) γ =
      M.andP (pointFormulaValue (M := M) φ γ) (pointFormulaValue (M := M) ψ γ) := by
  simp [pointFormulaValue, SemilocalModel.eval]

@[simp] theorem pointFormulaValue_or
    {Γ : Ctx Base}
    (φ ψ : Formula Const Γ)
    (γ : (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier) :
    pointFormulaValue (M := M) (Term.or φ ψ) γ =
      M.orP (pointFormulaValue (M := M) φ γ) (pointFormulaValue (M := M) ψ γ) := by
  simp [pointFormulaValue, SemilocalModel.eval]

@[simp] theorem pointFormulaValue_imp
    {Γ : Ctx Base}
    (φ ψ : Formula Const Γ)
    (γ : (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier) :
    pointFormulaValue (M := M) (Term.imp φ ψ) γ =
      M.impP (pointFormulaValue (M := M) φ γ) (pointFormulaValue (M := M) ψ γ) := by
  simp [pointFormulaValue, SemilocalModel.eval]

@[simp] theorem concreteOnePointPropositionWitness_formula_top
    {Γ : Ctx Base}
    (γ : (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier) :
    (concreteOnePointPropositionWitness (M := M)).propTop.toContinuousMap () =
      (concreteOnePointPropositionWitness (M := M)).encodeProp
        (pointFormulaValue (M := M) (Term.top : Formula Const Γ) γ) := by
  rw [pointFormulaValue_top]
  exact concreteOnePointPropositionWitness_top (M := M)

@[simp] theorem concreteOnePointPropositionWitness_formula_and
    {Γ : Ctx Base}
    (φ ψ : Formula Const Γ)
    (γ : (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier) :
    (concreteOnePointPropositionWitness (M := M)).fiberMeet
        ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
            (pointFormulaValue (M := M) φ γ),
          (concreteOnePointPropositionWitness (M := M)).encodeProp
            (pointFormulaValue (M := M) ψ γ)), by simp⟩ =
      (concreteOnePointPropositionWitness (M := M)).encodeProp
        (pointFormulaValue (M := M) (Term.and φ ψ) γ) := by
  rw [concreteOnePointPropositionWitness_meet]
  simp [pointFormulaValue, SemilocalModel.eval]

@[simp] theorem concreteOnePointPropositionWitness_formula_or
    {Γ : Ctx Base}
    (φ ψ : Formula Const Γ)
    (γ : (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier) :
    (concreteOnePointPropositionWitness (M := M)).fiberJoin
        ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
            (pointFormulaValue (M := M) φ γ),
          (concreteOnePointPropositionWitness (M := M)).encodeProp
            (pointFormulaValue (M := M) ψ γ)), by simp⟩ =
      (concreteOnePointPropositionWitness (M := M)).encodeProp
        (pointFormulaValue (M := M) (Term.or φ ψ) γ) := by
  rw [(concreteOnePointPropositionWitness (M := M)).fiberJoin_apply]
  simp [pointFormulaValue, SemilocalModel.eval]

@[simp] theorem concreteOnePointPropositionWitness_formula_imp
    {Γ : Ctx Base}
    (φ ψ : Formula Const Γ)
    (γ : (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier) :
    (concreteOnePointPropositionWitness (M := M)).fiberHimp
        ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
            (pointFormulaValue (M := M) φ γ),
          (concreteOnePointPropositionWitness (M := M)).encodeProp
            (pointFormulaValue (M := M) ψ γ)), by simp⟩ =
      (concreteOnePointPropositionWitness (M := M)).encodeProp
        (pointFormulaValue (M := M) (Term.imp φ ψ) γ) := by
  rw [concreteOnePointPropositionWitness_himp]
  simp [pointFormulaValue, SemilocalModel.eval]

@[simp] theorem truthEval_eq_truth_pointFormulaValue
    {Γ : Ctx Base}
    (φ : Formula Const Γ)
    (γ : (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier) :
    HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthEval (M := M) φ γ =
      M.truth (pointFormulaValue (M := M) φ γ) := by
  rfl

theorem not_derivable_of_connective_formula_witness_counterexample
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    (χ : Formula Const Γ)
    (γ : (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) Δ γ = ⊤)
    (w :
      (concreteOnePointPropositionWitness (M := M)).toTopologicalInterpretation.propSpace.Carrier)
    (hw :
      M.truth ((concreteOnePointPropositionWitness (M := M)).decodeProp w) ≠ ⊤)
    (hχ :
      M.truth ((concreteOnePointPropositionWitness (M := M)).decodeProp w) =
        HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthEval
          (M := M) χ γ) :
    ¬ Derivable (Base := Base) (Const := Const) Δ χ := by
  apply
    HigherOrderPointTopologicalGlobalModelBridge.basicInterp.not_derivable_of_truth_counterexample
      (M := M) (Δ := Δ) (φ := χ) γ hΔ
  intro hTruth
  exact hw (hχ.trans hTruth)

theorem connective_formula_witness_coherent_top_of_derivable
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {χ : Formula Const Γ}
    (hder : Derivable (Base := Base) (Const := Const) Δ χ)
    (γ : (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) Δ γ = ⊤)
    (w :
      (concreteOnePointPropositionWitness (M := M)).toTopologicalInterpretation.propSpace.Carrier)
    (hχ :
      M.truth ((concreteOnePointPropositionWitness (M := M)).decodeProp w) =
        HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthEval
          (M := M) χ γ) :
    M.truth ((concreteOnePointPropositionWitness (M := M)).decodeProp w) = ⊤ := by
  by_contra hw
  exact
    (not_derivable_of_connective_formula_witness_counterexample
      (M := M) (χ := χ) γ hΔ w hw hχ) hder

theorem connective_formula_witness_top_of_truthValidSequent
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {χ : Formula Const Γ}
    (hvalid :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.TruthValidSequent
        (M := M) Δ χ)
    (γ : (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) Δ γ = ⊤)
    (w :
      (concreteOnePointPropositionWitness (M := M)).toTopologicalInterpretation.propSpace.Carrier)
    (hχ :
      M.truth ((concreteOnePointPropositionWitness (M := M)).decodeProp w) =
        HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthEval
          (M := M) χ γ) :
    M.truth ((concreteOnePointPropositionWitness (M := M)).decodeProp w) = ⊤ := by
  have htop_le :
      (⊤ : M.Omega) ≤
        M.truth ((concreteOnePointPropositionWitness (M := M)).decodeProp w) := by
    rw [hχ]
    rw [← hΔ]
    exact hvalid γ
  exact le_antisymm le_top htop_le

theorem connective_formula_witness_truth_eq_truthEval
    {Γ : Ctx Base}
    (χ : Formula Const Γ)
    (γ : (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier)
    (w :
      (concreteOnePointPropositionWitness (M := M)).toTopologicalInterpretation.propSpace.Carrier)
    (hw :
      w =
        (concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) χ γ)) :
    M.truth ((concreteOnePointPropositionWitness (M := M)).decodeProp w) =
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthEval
        (M := M) χ γ := by
  calc
    M.truth ((concreteOnePointPropositionWitness (M := M)).decodeProp w) =
      M.truth
        ((concreteOnePointPropositionWitness (M := M)).decodeProp
          ((concreteOnePointPropositionWitness (M := M)).encodeProp
            (pointFormulaValue (M := M) χ γ))) := by
          rw [hw]
    _ = M.truth (pointFormulaValue (M := M) χ γ) := by
          simp
    _ =
        HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthEval
          (M := M) χ γ := by
          symm
          exact truthEval_eq_truth_pointFormulaValue (M := M) χ γ

theorem not_derivable_of_and_formula_witness_counterexample
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    (φ ψ : Formula Const Γ)
    (γ : (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) Δ γ = ⊤)
    (hAnd :
      M.truth
        ((concreteOnePointPropositionWitness (M := M)).decodeProp
          ((concreteOnePointPropositionWitness (M := M)).fiberMeet
            ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
                (pointFormulaValue (M := M) φ γ),
              (concreteOnePointPropositionWitness (M := M)).encodeProp
                (pointFormulaValue (M := M) ψ γ)), by simp⟩)) ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const) Δ (Term.and φ ψ) := by
  refine not_derivable_of_connective_formula_witness_counterexample
    (M := M) (χ := Term.and φ ψ) γ hΔ
    ((concreteOnePointPropositionWitness (M := M)).fiberMeet
      ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) φ γ),
        (concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) ψ γ)), by simp⟩)
    hAnd ?_
  exact connective_formula_witness_truth_eq_truthEval
    (M := M) (Term.and φ ψ) γ
    ((concreteOnePointPropositionWitness (M := M)).fiberMeet
      ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) φ γ),
        (concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) ψ γ)), by simp⟩)
    (concreteOnePointPropositionWitness_formula_and (M := M) φ ψ γ)

theorem not_derivable_of_or_formula_witness_counterexample
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    (φ ψ : Formula Const Γ)
    (γ : (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) Δ γ = ⊤)
    (hOr :
      M.truth
        ((concreteOnePointPropositionWitness (M := M)).decodeProp
          ((concreteOnePointPropositionWitness (M := M)).fiberJoin
            ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
                (pointFormulaValue (M := M) φ γ),
              (concreteOnePointPropositionWitness (M := M)).encodeProp
                (pointFormulaValue (M := M) ψ γ)), by simp⟩)) ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const) Δ (Term.or φ ψ) := by
  refine not_derivable_of_connective_formula_witness_counterexample
    (M := M) (χ := Term.or φ ψ) γ hΔ
    ((concreteOnePointPropositionWitness (M := M)).fiberJoin
      ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) φ γ),
        (concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) ψ γ)), by simp⟩)
    hOr ?_
  exact connective_formula_witness_truth_eq_truthEval
    (M := M) (Term.or φ ψ) γ
    ((concreteOnePointPropositionWitness (M := M)).fiberJoin
      ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) φ γ),
        (concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) ψ γ)), by simp⟩)
    (concreteOnePointPropositionWitness_formula_or (M := M) φ ψ γ)

theorem not_derivable_of_imp_formula_witness_counterexample
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    (φ ψ : Formula Const Γ)
    (γ : (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) Δ γ = ⊤)
    (hImp :
      M.truth
        ((concreteOnePointPropositionWitness (M := M)).decodeProp
          ((concreteOnePointPropositionWitness (M := M)).fiberHimp
            ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
                (pointFormulaValue (M := M) φ γ),
              (concreteOnePointPropositionWitness (M := M)).encodeProp
                (pointFormulaValue (M := M) ψ γ)), by simp⟩)) ≠ ⊤) :
    ¬ Derivable (Base := Base) (Const := Const) Δ (Term.imp φ ψ) := by
  refine not_derivable_of_connective_formula_witness_counterexample
    (M := M) (χ := Term.imp φ ψ) γ hΔ
    ((concreteOnePointPropositionWitness (M := M)).fiberHimp
      ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) φ γ),
        (concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) ψ γ)), by simp⟩)
    hImp ?_
  exact connective_formula_witness_truth_eq_truthEval
    (M := M) (Term.imp φ ψ) γ
    ((concreteOnePointPropositionWitness (M := M)).fiberHimp
      ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) φ γ),
        (concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) ψ γ)), by simp⟩)
    (concreteOnePointPropositionWitness_formula_imp (M := M) φ ψ γ)

theorem and_formula_witness_coherent_top_of_derivable
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    (φ ψ : Formula Const Γ)
    (hder : Derivable (Base := Base) (Const := Const) Δ (Term.and φ ψ))
    (γ : (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) Δ γ = ⊤) :
    M.truth
      ((concreteOnePointPropositionWitness (M := M)).decodeProp
        ((concreteOnePointPropositionWitness (M := M)).fiberMeet
          ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
              (pointFormulaValue (M := M) φ γ),
            (concreteOnePointPropositionWitness (M := M)).encodeProp
              (pointFormulaValue (M := M) ψ γ)), by simp⟩)) = ⊤ := by
  refine connective_formula_witness_coherent_top_of_derivable
    (M := M) hder γ hΔ
    ((concreteOnePointPropositionWitness (M := M)).fiberMeet
      ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) φ γ),
        (concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) ψ γ)), by simp⟩) ?_
  exact connective_formula_witness_truth_eq_truthEval
    (M := M) (Term.and φ ψ) γ
    ((concreteOnePointPropositionWitness (M := M)).fiberMeet
      ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) φ γ),
        (concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) ψ γ)), by simp⟩)
    (concreteOnePointPropositionWitness_formula_and (M := M) φ ψ γ)

theorem or_formula_witness_coherent_top_of_derivable
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    (φ ψ : Formula Const Γ)
    (hder : Derivable (Base := Base) (Const := Const) Δ (Term.or φ ψ))
    (γ : (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) Δ γ = ⊤) :
    M.truth
      ((concreteOnePointPropositionWitness (M := M)).decodeProp
        ((concreteOnePointPropositionWitness (M := M)).fiberJoin
          ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
              (pointFormulaValue (M := M) φ γ),
            (concreteOnePointPropositionWitness (M := M)).encodeProp
              (pointFormulaValue (M := M) ψ γ)), by simp⟩)) = ⊤ := by
  refine connective_formula_witness_coherent_top_of_derivable
    (M := M) hder γ hΔ
    ((concreteOnePointPropositionWitness (M := M)).fiberJoin
      ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) φ γ),
        (concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) ψ γ)), by simp⟩) ?_
  exact connective_formula_witness_truth_eq_truthEval
    (M := M) (Term.or φ ψ) γ
    ((concreteOnePointPropositionWitness (M := M)).fiberJoin
      ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) φ γ),
        (concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) ψ γ)), by simp⟩)
    (concreteOnePointPropositionWitness_formula_or (M := M) φ ψ γ)

theorem imp_formula_witness_coherent_top_of_derivable
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    (φ ψ : Formula Const Γ)
    (hder : Derivable (Base := Base) (Const := Const) Δ (Term.imp φ ψ))
    (γ : (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) Δ γ = ⊤) :
    M.truth
      ((concreteOnePointPropositionWitness (M := M)).decodeProp
        ((concreteOnePointPropositionWitness (M := M)).fiberHimp
          ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
              (pointFormulaValue (M := M) φ γ),
            (concreteOnePointPropositionWitness (M := M)).encodeProp
              (pointFormulaValue (M := M) ψ γ)), by simp⟩)) = ⊤ := by
  refine connective_formula_witness_coherent_top_of_derivable
    (M := M) hder γ hΔ
    ((concreteOnePointPropositionWitness (M := M)).fiberHimp
      ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) φ γ),
        (concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) ψ γ)), by simp⟩) ?_
  exact connective_formula_witness_truth_eq_truthEval
    (M := M) (Term.imp φ ψ) γ
    ((concreteOnePointPropositionWitness (M := M)).fiberHimp
      ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) φ γ),
        (concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) ψ γ)), by simp⟩)
    (concreteOnePointPropositionWitness_formula_imp (M := M) φ ψ γ)

theorem and_formula_witness_top_of_truthValidSequent
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    (φ ψ : Formula Const Γ)
    (hvalid :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.TruthValidSequent
        (M := M) Δ (Term.and φ ψ))
    (γ : (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) Δ γ = ⊤) :
    M.truth
      ((concreteOnePointPropositionWitness (M := M)).decodeProp
        ((concreteOnePointPropositionWitness (M := M)).fiberMeet
          ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
              (pointFormulaValue (M := M) φ γ),
            (concreteOnePointPropositionWitness (M := M)).encodeProp
              (pointFormulaValue (M := M) ψ γ)), by simp⟩)) = ⊤ := by
  refine connective_formula_witness_top_of_truthValidSequent
    (M := M) hvalid γ hΔ
    ((concreteOnePointPropositionWitness (M := M)).fiberMeet
      ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) φ γ),
        (concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) ψ γ)), by simp⟩) ?_
  exact connective_formula_witness_truth_eq_truthEval
    (M := M) (Term.and φ ψ) γ
    ((concreteOnePointPropositionWitness (M := M)).fiberMeet
      ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) φ γ),
        (concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) ψ γ)), by simp⟩)
    (concreteOnePointPropositionWitness_formula_and (M := M) φ ψ γ)

theorem or_formula_witness_top_of_truthValidSequent
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    (φ ψ : Formula Const Γ)
    (hvalid :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.TruthValidSequent
        (M := M) Δ (Term.or φ ψ))
    (γ : (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) Δ γ = ⊤) :
    M.truth
      ((concreteOnePointPropositionWitness (M := M)).decodeProp
        ((concreteOnePointPropositionWitness (M := M)).fiberJoin
          ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
              (pointFormulaValue (M := M) φ γ),
            (concreteOnePointPropositionWitness (M := M)).encodeProp
              (pointFormulaValue (M := M) ψ γ)), by simp⟩)) = ⊤ := by
  refine connective_formula_witness_top_of_truthValidSequent
    (M := M) hvalid γ hΔ
    ((concreteOnePointPropositionWitness (M := M)).fiberJoin
      ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) φ γ),
        (concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) ψ γ)), by simp⟩) ?_
  exact connective_formula_witness_truth_eq_truthEval
    (M := M) (Term.or φ ψ) γ
    ((concreteOnePointPropositionWitness (M := M)).fiberJoin
      ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) φ γ),
        (concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) ψ γ)), by simp⟩)
    (concreteOnePointPropositionWitness_formula_or (M := M) φ ψ γ)

theorem imp_formula_witness_top_of_truthValidSequent
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    (φ ψ : Formula Const Γ)
    (hvalid :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.TruthValidSequent
        (M := M) Δ (Term.imp φ ψ))
    (γ : (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) Δ γ = ⊤) :
    M.truth
      ((concreteOnePointPropositionWitness (M := M)).decodeProp
        ((concreteOnePointPropositionWitness (M := M)).fiberHimp
          ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
              (pointFormulaValue (M := M) φ γ),
            (concreteOnePointPropositionWitness (M := M)).encodeProp
              (pointFormulaValue (M := M) ψ γ)), by simp⟩)) = ⊤ := by
  refine connective_formula_witness_top_of_truthValidSequent
    (M := M) hvalid γ hΔ
    ((concreteOnePointPropositionWitness (M := M)).fiberHimp
      ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) φ γ),
        (concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) ψ γ)), by simp⟩) ?_
  exact connective_formula_witness_truth_eq_truthEval
    (M := M) (Term.imp φ ψ) γ
    ((concreteOnePointPropositionWitness (M := M)).fiberHimp
      ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) φ γ),
        (concreteOnePointPropositionWitness (M := M)).encodeProp
          (pointFormulaValue (M := M) ψ γ)), by simp⟩)
    (concreteOnePointPropositionWitness_formula_imp (M := M) φ ψ γ)

end ConcreteOnePointWitness

end HigherOrderPointHeytingGlobalModelBridge

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
