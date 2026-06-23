import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzHeyting
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzHigherOrderPointModelBridge
import Mettapedia.Logic.HOL.LindenbaumSet
import Mettapedia.Logic.HOL.Semantics.Extensionality

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v w w'

namespace HigherOrderPointHeytingGlobalModelBridge

variable {Base : Type u} {Const : Ty Base → Type v}

/--
Minimal one-point witness for the full topological layer over a global model.

The existing higher-order point bridge packages term evaluation over the discrete
one-point carrier, but the stronger Heyting layer still needs a full
`TopologicalInterpretation` together with a typed identification between the
model carriers and that interpretation's fibers.
-/
structure OnePointTopologicalWitness (M : GlobalModel.{u, v, 0, w'} Base Const) where
  toTopologicalInterpretation : TopologicalInterpretation.{u, v, 0, 0} Base Const PUnit
  carrierEquiv : ∀ τ : Ty Base, M.Carrier τ ≃ (toTopologicalInterpretation.space τ).Carrier
  carrierEquiv_proj : ∀ (τ : Ty Base) (x : M.Carrier τ),
    (toTopologicalInterpretation.space τ).proj (carrierEquiv τ x) = ()
  const_eq : ∀ {τ : Ty Base} (c : Const τ),
    carrierEquiv τ (M.const c) = (toTopologicalInterpretation.const c).toContinuousMap ()

namespace OnePointTopologicalWitness

variable {M : GlobalModel.{u, v, 0, w'} Base Const} (W : OnePointTopologicalWitness M)

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
      exact PUnit.unit
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
      exact PUnit.unit
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

theorem prop_ext
    {p q : W.toTopologicalInterpretation.propSpace.Carrier}
    (h : W.decodeProp p = W.decodeProp q) :
    p = q := by
  calc
    p = W.encodeProp (W.decodeProp p) := (W.encodeProp_decodeProp p).symm
    _ = W.encodeProp (W.decodeProp q) := by rw [h]
    _ = q := W.encodeProp_decodeProp q

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
structure OnePointPropositionWitness (M : GlobalModel.{u, v, 0, w'} Base Const)
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

variable {M : GlobalModel.{u, v, 0, w'} Base Const} (W : OnePointPropositionWitness M)

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

theorem prop_ext
    {p q : W.toTopologicalInterpretation.propSpace.Carrier}
    (h : W.decodeProp p = W.decodeProp q) :
    p = q :=
  W.toTopological.prop_ext h

end OnePointPropositionWitness

/--
Carrier-level proposition laws needed to turn the concrete one-point
connective operations into the corresponding fiberwise Heyting algebra fields.

`GlobalModel` itself records preservation of truth values into a Heyting frame;
these equalities are stronger carrier equalities, so they are kept as explicit
data rather than inferred from non-injective truth semantics.
-/
structure PropCarrierHeytingLaws (M : GlobalModel Base Const) where
  and_idempotent : ∀ p : M.Carrier .prop, M.andP p p = p
  and_top : ∀ p : M.Carrier .prop, M.andP p M.topP = p
  and_bot : ∀ p : M.Carrier .prop, M.andP M.botP p = M.botP
  and_comm : ∀ p q : M.Carrier .prop, M.andP p q = M.andP q p
  and_assoc : ∀ p q r : M.Carrier .prop,
    M.andP (M.andP p q) r = M.andP p (M.andP q r)
  or_upper : ∀ p q : M.Carrier .prop, M.andP p (M.orP p q) = p
  or_comm : ∀ p q : M.Carrier .prop, M.orP p q = M.orP q p
  or_assoc : ∀ p q r : M.Carrier .prop,
    M.orP (M.orP p q) r = M.orP p (M.orP q r)
  or_bot : ∀ p : M.Carrier .prop, M.orP p M.botP = p
  and_proj_fst : ∀ p q : M.Carrier .prop, M.andP (M.andP p q) p = M.andP p q
  and_proj_snd : ∀ p q : M.Carrier .prop, M.andP (M.andP p q) q = M.andP p q
  and_or_distrib_left : ∀ p q r : M.Carrier .prop,
    M.andP p (M.orP q r) = M.orP (M.andP p q) (M.andP p r)
  and_or_distrib : ∀ p q r : M.Carrier .prop,
    M.andP (M.orP p q) r = M.orP (M.andP p r) (M.andP q r)
  or_lub : ∀ p q r : M.Carrier .prop,
    M.andP p r = p →
    M.andP q r = q →
    M.andP (M.orP p q) r = M.orP p q
  himp_adj : ∀ a b c : M.Carrier .prop,
    (M.andP (M.andP a b) c = M.andP a b) ↔
      (M.andP a (M.impP b c) = a)

/--
Faithful-carrier source data for `PropCarrierHeytingLaws`.

Lindenbaum-style carriers already have a `HeytingAlgebra` instance; a model
whose proposition operations are definitionally or theoremwise faithful to that
algebra can use this record to produce the carrier laws needed by the concrete
one-point Heyting witness. In particular, the implication law below is ordinary
Heyting residuation transported along these carrier identifications.
-/
structure PropCarrierFaithfulHeytingSource (M : GlobalModel Base Const)
    [HeytingAlgebra (M.Carrier .prop)] where
  top_eq : M.topP = ⊤
  bot_eq : M.botP = ⊥
  and_eq : ∀ p q : M.Carrier .prop, M.andP p q = p ⊓ q
  or_eq : ∀ p q : M.Carrier .prop, M.orP p q = p ⊔ q
  imp_eq : ∀ p q : M.Carrier .prop, M.impP p q = p ⇨ q

namespace PropCarrierFaithfulHeytingSource

variable {M : GlobalModel Base Const} [HeytingAlgebra (M.Carrier .prop)]

def toPropCarrierHeytingLaws
    (S : PropCarrierFaithfulHeytingSource M) :
    PropCarrierHeytingLaws M where
  and_idempotent := by
    intro p
    simp [S.and_eq]
  and_top := by
    intro p
    simp [S.and_eq, S.top_eq]
  and_bot := by
    intro p
    simp [S.and_eq, S.bot_eq]
  and_comm := by
    intro p q
    simp [S.and_eq, inf_comm]
  and_assoc := by
    intro p q r
    simp [S.and_eq, inf_assoc]
  or_upper := by
    intro p q
    simp [S.and_eq, S.or_eq]
  or_comm := by
    intro p q
    simp [S.or_eq, sup_comm]
  or_assoc := by
    intro p q r
    simp [S.or_eq, sup_assoc]
  or_bot := by
    intro p
    simp [S.or_eq, S.bot_eq]
  and_proj_fst := by
    intro p q
    simp [S.and_eq]
  and_proj_snd := by
    intro p q
    simp [S.and_eq]
  and_or_distrib_left := by
    intro p q r
    simp [S.and_eq, S.or_eq, inf_sup_left]
  and_or_distrib := by
    intro p q r
    simp [S.and_eq, S.or_eq, inf_sup_right]
  or_lub := by
    intro p q r hp hq
    have hp_le : p ≤ r := by
      rw [← hp]
      simp [S.and_eq]
    have hq_le : q ≤ r := by
      rw [← hq]
      simp [S.and_eq]
    rw [S.and_eq, S.or_eq]
    exact le_antisymm inf_le_left (le_inf le_rfl (sup_le hp_le hq_le))
  himp_adj := by
    intro a b c
    constructor
    · intro h
      have hfaithful : (a ⊓ b) ⊓ c = a ⊓ b := by
        simpa [S.and_eq] using h
      have hab_le_c : a ⊓ b ≤ c := by
        rw [← hfaithful]
        exact inf_le_right
      have ha_le_imp : a ≤ b ⇨ c := (le_himp_iff).2 hab_le_c
      rw [S.and_eq, S.imp_eq]
      exact le_antisymm inf_le_left (le_inf le_rfl ha_le_imp)
    · intro h
      have hfaithful : a ⊓ (b ⇨ c) = a := by
        simpa [S.and_eq, S.imp_eq] using h
      have ha_le_imp : a ≤ b ⇨ c := by
        rw [← hfaithful]
        exact inf_le_right
      have hab_le_c : a ⊓ b ≤ c := (le_himp_iff).1 ha_le_imp
      have hresult : (a ⊓ b) ⊓ c = a ⊓ b :=
        le_antisymm inf_le_left (le_inf le_rfl hab_le_c)
      simpa [S.and_eq] using hresult

end PropCarrierFaithfulHeytingSource

/--
Truth-level laws required of the equality proposition operation.

This is intentionally only an abstract theorem shape over an arbitrary
`GlobalModel`: the prop-only Lindenbaum quotient model in this file is not a
source for typed equality. A later canonical-carrier construction must provide
these laws from the actual quotient/extensionality story for every type.
-/
structure EqualityCarrierLaws (M : GlobalModel Base Const) where
  eq_refl_top : ∀ {τ : Ty Base} (x : M.Carrier τ),
    M.truth (M.eqP x x) = ⊤
  eq_symm_top : ∀ {τ : Ty Base} (x y : M.Carrier τ),
    M.truth (M.eqP x y) = ⊤ → M.truth (M.eqP y x) = ⊤
  eq_trans_top : ∀ {τ : Ty Base} (x y z : M.Carrier τ),
    M.truth (M.eqP x y) = ⊤ →
    M.truth (M.eqP y z) = ⊤ →
    M.truth (M.eqP x z) = ⊤
  eq_prop_intro_top : ∀ (p q : M.Carrier .prop),
    M.truth (M.impP p q) = ⊤ →
    M.truth (M.impP q p) = ⊤ →
    M.truth (M.eqP p q) = ⊤
  eq_prop_el_left_le : ∀ (p q : M.Carrier .prop),
    M.truth (M.eqP p q) ≤ M.truth (M.impP p q)
  eq_prop_el_right_le : ∀ (p q : M.Carrier .prop),
    M.truth (M.eqP p q) ≤ M.truth (M.impP q p)
  eq_app_fun_top : ∀ {σ τ : Ty Base}
    (f g : M.Carrier (σ ⇒ τ)) (x : M.Carrier σ),
    M.truth (M.eqP f g) = ⊤ →
    M.truth (M.eqP (M.app f x) (M.app g x)) = ⊤
  eq_app_arg_top : ∀ {σ τ : Ty Base}
    (f : M.Carrier (σ ⇒ τ)) (x y : M.Carrier σ),
    M.truth (M.eqP x y) = ⊤ →
    M.truth (M.eqP (M.app f x) (M.app f y)) = ⊤
  eq_lam_top : ∀ {σ τ : Ty Base}
    (f g : M.Carrier σ → M.Carrier τ),
    (∀ x, M.truth (M.eqP (f x) (g x)) = ⊤) →
    M.truth (M.eqP (M.lam f) (M.lam g)) = ⊤
  eq_funext_top : ∀ {σ τ : Ty Base}
    (f g : M.Carrier (σ ⇒ τ)),
    M.truth (M.allP fun x => M.eqP (M.app f x) (M.app g x)) = ⊤ →
    M.truth (M.eqP f g) = ⊤

namespace EqualityCarrierLaws

variable {M : GlobalModel Base Const}

theorem beta_top
    (E : EqualityCarrierLaws M)
    {σ τ : Ty Base}
    (f : M.Carrier σ → M.Carrier τ)
    (x : M.Carrier σ) :
    M.truth (M.eqP (M.app (M.lam f) x) (f x)) = ⊤ := by
  rw [M.beta]
  exact EqualityCarrierLaws.eq_refl_top E (f x)

theorem eta_top
    (E : EqualityCarrierLaws M)
    {σ τ : Ty Base}
    (f : M.Carrier (σ ⇒ τ)) :
    M.truth (M.eqP (M.lam (fun x => M.app f x)) f) = ⊤ := by
  rw [M.eta]
  exact EqualityCarrierLaws.eq_refl_top E f

theorem eq_prop_el_left_top
    (E : EqualityCarrierLaws M)
    {p q : M.Carrier .prop}
    (h : M.truth (M.eqP p q) = ⊤) :
    M.truth (M.impP p q) = ⊤ := by
  apply top_unique
  rw [← h]
  exact EqualityCarrierLaws.eq_prop_el_left_le E p q

theorem eq_prop_el_right_top
    (E : EqualityCarrierLaws M)
    {p q : M.Carrier .prop}
    (h : M.truth (M.eqP p q) = ⊤) :
    M.truth (M.impP q p) = ⊤ := by
  apply top_unique
  rw [← h]
  exact EqualityCarrierLaws.eq_prop_el_right_le E p q

end EqualityCarrierLaws

/--
Exact source shape still needed from the full canonical/extensional carrier.

The trusted HOL side already has an extensional relation on Henkin carriers
(`PreModel.Eqv`); the missing bridge is a proof that the canonical `GlobalModel`
carrier interprets `eqP` by that relation, including proposition elimination as
truth-value inequalities and function extensionality through `allP`.
-/
structure CanonicalExtensionalEqualityCarrierSource
    (M : GlobalModel Base Const) where
  Eqv : (τ : Ty Base) → M.Carrier τ → M.Carrier τ → Prop
  truth_eq_top_of_eqv : ∀ {τ : Ty Base} {x y : M.Carrier τ},
    Eqv τ x y → M.truth (M.eqP x y) = ⊤
  eqv_of_truth_eq_top : ∀ {τ : Ty Base} {x y : M.Carrier τ},
    M.truth (M.eqP x y) = ⊤ → Eqv τ x y
  eqv_refl : ∀ {τ : Ty Base} (x : M.Carrier τ), Eqv τ x x
  eqv_symm : ∀ {τ : Ty Base} {x y : M.Carrier τ},
    Eqv τ x y → Eqv τ y x
  eqv_trans : ∀ {τ : Ty Base} {x y z : M.Carrier τ},
    Eqv τ x y → Eqv τ y z → Eqv τ x z
  eqv_prop_intro_top : ∀ (p q : M.Carrier .prop),
    M.truth (M.impP p q) = ⊤ →
    M.truth (M.impP q p) = ⊤ →
    Eqv .prop p q
  eq_prop_el_left_le : ∀ (p q : M.Carrier .prop),
    M.truth (M.eqP p q) ≤ M.truth (M.impP p q)
  eq_prop_el_right_le : ∀ (p q : M.Carrier .prop),
    M.truth (M.eqP p q) ≤ M.truth (M.impP q p)
  eqv_app_fun : ∀ {σ τ : Ty Base}
    (f g : M.Carrier (σ ⇒ τ)) (x : M.Carrier σ),
    Eqv (σ ⇒ τ) f g → Eqv τ (M.app f x) (M.app g x)
  eqv_app_arg : ∀ {σ τ : Ty Base}
    (f : M.Carrier (σ ⇒ τ)) (x y : M.Carrier σ),
    Eqv σ x y → Eqv τ (M.app f x) (M.app f y)
  eqv_lam : ∀ {σ τ : Ty Base}
    (f g : M.Carrier σ → M.Carrier τ),
    (∀ x, Eqv τ (f x) (g x)) → Eqv (σ ⇒ τ) (M.lam f) (M.lam g)
  eqv_funext_top : ∀ {σ τ : Ty Base}
    (f g : M.Carrier (σ ⇒ τ)),
    M.truth (M.allP fun x => M.eqP (M.app f x) (M.app g x)) = ⊤ →
    Eqv (σ ⇒ τ) f g

namespace CanonicalExtensionalEqualityCarrierSource

variable {M : GlobalModel Base Const}

def toEqualityCarrierLaws
    (S : CanonicalExtensionalEqualityCarrierSource M) :
    EqualityCarrierLaws M where
  eq_refl_top := by
    intro τ x
    exact S.truth_eq_top_of_eqv (S.eqv_refl x)
  eq_symm_top := by
    intro τ x y hxy
    exact S.truth_eq_top_of_eqv (S.eqv_symm (S.eqv_of_truth_eq_top hxy))
  eq_trans_top := by
    intro τ x y z hxy hyz
    exact S.truth_eq_top_of_eqv
      (S.eqv_trans (S.eqv_of_truth_eq_top hxy) (S.eqv_of_truth_eq_top hyz))
  eq_prop_intro_top := by
    intro p q hpq hqp
    exact S.truth_eq_top_of_eqv (S.eqv_prop_intro_top p q hpq hqp)
  eq_prop_el_left_le := S.eq_prop_el_left_le
  eq_prop_el_right_le := S.eq_prop_el_right_le
  eq_app_fun_top := by
    intro σ τ f g x hfg
    exact S.truth_eq_top_of_eqv
      (S.eqv_app_fun f g x (S.eqv_of_truth_eq_top hfg))
  eq_app_arg_top := by
    intro σ τ f x y hxy
    exact S.truth_eq_top_of_eqv
      (S.eqv_app_arg f x y (S.eqv_of_truth_eq_top hxy))
  eq_lam_top := by
    intro σ τ f g hfg
    exact S.truth_eq_top_of_eqv
      (S.eqv_lam f g fun x => S.eqv_of_truth_eq_top (hfg x))
  eq_funext_top := by
    intro σ τ f g hfg
    exact S.truth_eq_top_of_eqv (S.eqv_funext_top f g hfg)

end CanonicalExtensionalEqualityCarrierSource

/--
Audit bridge from a `GlobalModel` carrier to a real HOL extensional carrier.

This deliberately does not assert that the current prop-only Lindenbaum quotient
is the full canonical carrier. It isolates the typed data the eventual canonical
quotient must supply: an embedding into a `PreModel` carrier together with
admissibility, so equality can be read through `PreModel.Eqv`.
-/
structure PreModelEqvCarrierAudit
    (M : GlobalModel Base Const) where
  H : PreModel.{u, v, w} Base Const
  embed : ∀ τ : Ty Base, M.Carrier τ → Ty.denote H.Carrier τ
  embed_adm : ∀ {τ : Ty Base} (x : M.Carrier τ), H.adm τ (embed τ x)

namespace PreModelEqvCarrierAudit

variable {M : GlobalModel Base Const}

def Eqv
    (A : PreModelEqvCarrierAudit M)
    (τ : Ty Base) (x y : M.Carrier τ) : Prop :=
  PreModel.Eqv A.H τ (A.embed τ x) (A.embed τ y)

theorem eqv_refl_source_field
    (A : PreModelEqvCarrierAudit M) :
    ∀ {τ : Ty Base} (x : M.Carrier τ), A.Eqv τ x x := by
  intro τ x
  exact PreModel.eqv_refl A.H (A.embed_adm x)

end PreModelEqvCarrierAudit

/--
Truth-reflection source data for equality against the real HOL extensional
relation.

This is the first non-reflexivity field that the eventual typed canonical
carrier must justify: `eqP` is true exactly when the embedded carrier elements
are related by `PreModel.Eqv`.
-/
structure PreModelEqvTruthSource
    (M : GlobalModel Base Const)
    extends PreModelEqvCarrierAudit.{u, v, w} M where
  eqP_truth_iff_eqv : ∀ {τ : Ty Base} {x y : M.Carrier τ},
    M.truth (M.eqP x y) = ⊤ ↔
      PreModel.Eqv H τ (embed τ x) (embed τ y)

namespace PreModelEqvTruthSource

variable {M : GlobalModel Base Const}

abbrev Eqv
    (S : PreModelEqvTruthSource M)
    (τ : Ty Base) (x y : M.Carrier τ) : Prop :=
  S.toPreModelEqvCarrierAudit.Eqv τ x y

theorem truth_eq_top_of_eqv_source_field
    (S : PreModelEqvTruthSource M)
    {τ : Ty Base} {x y : M.Carrier τ}
    (h : S.Eqv τ x y) :
    M.truth (M.eqP x y) = ⊤ := by
  exact (S.eqP_truth_iff_eqv (τ := τ) (x := x) (y := y)).2 h

theorem eqv_of_truth_eq_top_source_field
    (S : PreModelEqvTruthSource M)
    {τ : Ty Base} {x y : M.Carrier τ}
    (h : M.truth (M.eqP x y) = ⊤) :
    S.Eqv τ x y := by
  exact (S.eqP_truth_iff_eqv (τ := τ) (x := x) (y := y)).1 h

end PreModelEqvTruthSource

/--
The precise theorem still missing from the full canonical-carrier route.

For the prop-only Lindenbaum quotient, this proposition should not be claimed:
that model has only the proposition algebra sourced. The future full canonical
model must provide this source from typed term quotients and extensionality.
-/
def CanonicalExtensionalEqualitySourceTheorem
    (M : GlobalModel Base Const) : Prop :=
  Nonempty (CanonicalExtensionalEqualityCarrierSource M)

theorem equalityCarrierLaws_of_canonicalExtensionalEqualitySourceTheorem
    {M : GlobalModel Base Const}
    (h : CanonicalExtensionalEqualitySourceTheorem (Base := Base) (Const := Const) M) :
    EqualityCarrierLaws M := by
  rcases h with ⟨S⟩
  exact S.toEqualityCarrierLaws

namespace LindenbaumQuotientPropGlobalModel

variable {Base : Type u} {Const : Ty Base → Type v}

/-
A minimal global model whose proposition carrier is the closed-formula
Lindenbaum quotient of a theory.

This is not intended as the final Henkin/Awodey-Butz canonical model: non-
proposition carriers and quantifiers are deliberately inert. Its role is the
small, concrete bridge needed here: the proposition carrier is exactly the
trusted quotient carrier, and the proposition connectives are exactly its
Heyting operations.
-/

abbrev PropCarrier (T : ClosedTheorySet Const) : Type _ :=
  ClosedTheorySet.ProvablyEquivalent.LindenbaumSet (Const := Const) T

def Carrier (T : ClosedTheorySet Const) : Ty Base → Type _
  | .prop => PropCarrier T
  | .base _ => PUnit
  | .arr σ τ => Carrier T σ → Carrier T τ

instance instHeytingAlgebraCarrierProp (T : ClosedTheorySet Const) :
    HeytingAlgebra (Carrier (Base := Base) T .prop) :=
  inferInstanceAs (HeytingAlgebra (PropCarrier T))

def defaultValue (T : ClosedTheorySet Const) : (τ : Ty Base) → Carrier T τ
  | .prop => (⊤ : PropCarrier T)
  | .base _ => PUnit.unit
  | .arr _ τ => fun _ => defaultValue T τ

noncomputable def model (T : ClosedTheorySet Const) : GlobalModel Base Const where
  toApplicativeStructure :=
    { Carrier := Carrier T
      const := fun {τ} _ => defaultValue T τ
      app := fun f x => f x
      lam := fun f => f
      beta := by
        intro σ τ f x
        rfl
      eta := by
        intro σ τ f
        rfl }
  Omega := PUnit
  frame := inferInstance
  truth := fun _ => PUnit.unit
  extent := fun {_} _ => PUnit.unit
  topP := (⊤ : PropCarrier T)
  botP := (⊥ : PropCarrier T)
  andP := fun p q => ((p : PropCarrier T) ⊓ (q : PropCarrier T))
  orP := fun p q => ((p : PropCarrier T) ⊔ (q : PropCarrier T))
  impP := fun p q => ((p : PropCarrier T) ⇨ (q : PropCarrier T))
  eqP := fun _ _ => (⊤ : PropCarrier T)
  allP := fun _ => (⊤ : PropCarrier T)
  exP := fun _ => (⊤ : PropCarrier T)
  truth_top := Subsingleton.elim _ _
  truth_bot := Subsingleton.elim _ _
  truth_and := by
    intro p q
    exact Subsingleton.elim _ _
  truth_or := by
    intro p q
    exact Subsingleton.elim _ _
  truth_imp := by
    intro p q
    exact Subsingleton.elim _ _
  truth_all := by
    intro σ f
    exact Subsingleton.elim _ _
  truth_ex := by
    intro σ f
    exact Subsingleton.elim _ _
  global := by
    intro τ x
    exact Subsingleton.elim _ _

instance instHeytingAlgebraModelCarrierProp (T : ClosedTheorySet Const) :
    HeytingAlgebra ((model (Base := Base) (Const := Const) T).Carrier .prop) :=
  inferInstanceAs (HeytingAlgebra (Carrier (Base := Base) T .prop))

noncomputable def faithfulHeytingSource
    (T : ClosedTheorySet Const) :
    PropCarrierFaithfulHeytingSource (model (Base := Base) (Const := Const) T) where
  top_eq := rfl
  bot_eq := rfl
  and_eq := by
    intro p q
    rfl
  or_eq := by
    intro p q
    rfl
  imp_eq := by
    intro p q
    rfl

noncomputable def sourcedHeytingLaws
    (T : ClosedTheorySet Const) :
    PropCarrierHeytingLaws (model (Base := Base) (Const := Const) T) :=
  (faithfulHeytingSource (Base := Base) (Const := Const) T).toPropCarrierHeytingLaws

end LindenbaumQuotientPropGlobalModel

/--
The first one-point Heyting field cluster: concrete operations together with
the projection/continuity and fiberwise algebra laws required by
`HeytingTopologicalInterpretation`, stopping before global section operations,
equality, and quantifiers.
-/
structure OnePointHeytingAlgebraWitness (M : GlobalModel.{u, v, 0, w'} Base Const)
    extends OnePointPropositionWitness M where
  fiberMeet_continuous : Continuous fiberMeet
  fiberJoin_continuous : Continuous fiberJoin
  fiberHimp_continuous : Continuous fiberHimp
  fiberMeet_idempotent : ∀ p : toTopologicalInterpretation.propSpace.Carrier,
    fiberMeet ⟨(p, p), rfl⟩ = p
  fiberMeet_top : ∀ p : toTopologicalInterpretation.propSpace.Carrier,
    let topAtP := propTop.toContinuousMap (toTopologicalInterpretation.propSpace.proj p)
    have h : toTopologicalInterpretation.propSpace.proj p =
        toTopologicalInterpretation.propSpace.proj topAtP :=
      (congrFun propTop.proj_comp (toTopologicalInterpretation.propSpace.proj p)).symm
    fiberMeet ⟨(p, topAtP), h⟩ = p
  fiberMeet_bot : ∀ p : toTopologicalInterpretation.propSpace.Carrier,
    let botAtP := propBot.toContinuousMap (toTopologicalInterpretation.propSpace.proj p)
    have h : toTopologicalInterpretation.propSpace.proj botAtP =
        toTopologicalInterpretation.propSpace.proj p :=
      congrFun propBot.proj_comp (toTopologicalInterpretation.propSpace.proj p)
    fiberMeet ⟨(botAtP, p), h⟩ = botAtP
  fiberMeet_comm : ∀ pq : PropFiberPair toTopologicalInterpretation.propSpace,
    fiberMeet pq = fiberMeet ⟨(pq.val.2, pq.val.1), pq.property.symm⟩
  fiberMeet_assoc : ∀ (p q r : toTopologicalInterpretation.propSpace.Carrier)
    (hpq : toTopologicalInterpretation.propSpace.proj p =
      toTopologicalInterpretation.propSpace.proj q)
    (hqr : toTopologicalInterpretation.propSpace.proj q =
      toTopologicalInterpretation.propSpace.proj r),
    let pq_pair : PropFiberPair toTopologicalInterpretation.propSpace := ⟨(p, q), hpq⟩
    let qr_pair : PropFiberPair toTopologicalInterpretation.propSpace := ⟨(q, r), hqr⟩
    let meet_pq := fiberMeet pq_pair
    let meet_qr := fiberMeet qr_pair
    have h1 : toTopologicalInterpretation.propSpace.proj meet_pq =
        toTopologicalInterpretation.propSpace.proj r :=
      (OnePointPropositionWitness.fiberMeet_proj toOnePointPropositionWitness pq_pair).trans
        (hpq.trans hqr)
    have h2 : toTopologicalInterpretation.propSpace.proj p =
        toTopologicalInterpretation.propSpace.proj meet_qr :=
      hpq.trans
        (OnePointPropositionWitness.fiberMeet_proj toOnePointPropositionWitness qr_pair).symm
    fiberMeet ⟨(meet_pq, r), h1⟩ = fiberMeet ⟨(p, meet_qr), h2⟩
  fiberJoin_upper : ∀ pq : PropFiberPair toTopologicalInterpretation.propSpace,
    let joinPQ := fiberJoin pq
    have h1 : toTopologicalInterpretation.propSpace.proj pq.val.1 =
        toTopologicalInterpretation.propSpace.proj joinPQ :=
      (OnePointPropositionWitness.fiberJoin_proj toOnePointPropositionWitness pq).symm
    fiberMeet ⟨(pq.val.1, joinPQ), h1⟩ = pq.val.1
  fiberJoin_comm : ∀ pq : PropFiberPair toTopologicalInterpretation.propSpace,
    fiberJoin pq = fiberJoin ⟨(pq.val.2, pq.val.1), pq.property.symm⟩
  fiberMeet_proj_fst : ∀ pq : PropFiberPair toTopologicalInterpretation.propSpace,
    let meet := fiberMeet pq
    have h : toTopologicalInterpretation.propSpace.proj meet =
        toTopologicalInterpretation.propSpace.proj pq.val.1 :=
      OnePointPropositionWitness.fiberMeet_proj toOnePointPropositionWitness pq
    fiberMeet ⟨(meet, pq.val.1), h⟩ = meet
  fiberMeet_proj_snd : ∀ pq : PropFiberPair toTopologicalInterpretation.propSpace,
    let meet := fiberMeet pq
    have h : toTopologicalInterpretation.propSpace.proj meet =
        toTopologicalInterpretation.propSpace.proj pq.val.2 :=
      (OnePointPropositionWitness.fiberMeet_proj toOnePointPropositionWitness pq).trans
        pq.property
    fiberMeet ⟨(meet, pq.val.2), h⟩ = meet
  fiberMeet_join_distrib : ∀ (p q r : toTopologicalInterpretation.propSpace.Carrier)
    (hpq : toTopologicalInterpretation.propSpace.proj p =
      toTopologicalInterpretation.propSpace.proj q)
    (hqr : toTopologicalInterpretation.propSpace.proj q =
      toTopologicalInterpretation.propSpace.proj r),
    let pq_join := fiberJoin ⟨(p, q), hpq⟩
    let pr_meet := fiberMeet ⟨(p, r), hpq.trans hqr⟩
    let qr_meet := fiberMeet ⟨(q, r), hqr⟩
    have h_join_r : toTopologicalInterpretation.propSpace.proj pq_join =
        toTopologicalInterpretation.propSpace.proj r :=
      (OnePointPropositionWitness.fiberJoin_proj toOnePointPropositionWitness
        ⟨(p, q), hpq⟩).trans (hpq.trans hqr)
    have h_pr_qr : toTopologicalInterpretation.propSpace.proj pr_meet =
        toTopologicalInterpretation.propSpace.proj qr_meet :=
      (OnePointPropositionWitness.fiberMeet_proj toOnePointPropositionWitness
        ⟨(p, r), hpq.trans hqr⟩).trans
        (hpq.trans
          (OnePointPropositionWitness.fiberMeet_proj toOnePointPropositionWitness
            ⟨(q, r), hqr⟩).symm)
    fiberMeet ⟨(pq_join, r), h_join_r⟩ =
      fiberJoin ⟨(pr_meet, qr_meet), h_pr_qr⟩
  fiberJoin_lub : ∀ (p q r : toTopologicalInterpretation.propSpace.Carrier)
    (hpq : toTopologicalInterpretation.propSpace.proj p =
      toTopologicalInterpretation.propSpace.proj q)
    (hpr : toTopologicalInterpretation.propSpace.proj p =
      toTopologicalInterpretation.propSpace.proj r)
    (_hp_le_r : fiberMeet ⟨(p, r), hpr⟩ = p)
    (_hq_le_r : fiberMeet ⟨(q, r), hpq.symm.trans hpr⟩ = q),
    let pq_join := fiberJoin ⟨(p, q), hpq⟩
    have h_join_r : toTopologicalInterpretation.propSpace.proj pq_join =
        toTopologicalInterpretation.propSpace.proj r :=
      (OnePointPropositionWitness.fiberJoin_proj toOnePointPropositionWitness
        ⟨(p, q), hpq⟩).trans hpr
    fiberMeet ⟨(pq_join, r), h_join_r⟩ = pq_join
  fiberHimp_adj : ∀ (a b c : toTopologicalInterpretation.propSpace.Carrier)
    (hab : toTopologicalInterpretation.propSpace.proj a =
      toTopologicalInterpretation.propSpace.proj b)
    (hbc : toTopologicalInterpretation.propSpace.proj b =
      toTopologicalInterpretation.propSpace.proj c),
    let bc_pair : PropFiberPair toTopologicalInterpretation.propSpace := ⟨(b, c), hbc⟩
    let ab_pair : PropFiberPair toTopologicalInterpretation.propSpace := ⟨(a, b), hab⟩
    let meet_ab := fiberMeet ab_pair
    let himp_bc := fiberHimp bc_pair
    have h_meet_c : toTopologicalInterpretation.propSpace.proj meet_ab =
        toTopologicalInterpretation.propSpace.proj c :=
      (OnePointPropositionWitness.fiberMeet_proj toOnePointPropositionWitness ab_pair).trans
        (hab.trans hbc)
    have h_a_himp : toTopologicalInterpretation.propSpace.proj a =
        toTopologicalInterpretation.propSpace.proj himp_bc :=
      hab.trans
        (OnePointPropositionWitness.fiberHimp_proj toOnePointPropositionWitness bc_pair).symm
    (fiberMeet ⟨(meet_ab, c), h_meet_c⟩ = meet_ab) ↔
      (fiberMeet ⟨(a, himp_bc), h_a_himp⟩ = a)

namespace OnePointHeytingAlgebraWitness

variable {M : GlobalModel.{u, v, 0, w'} Base Const} (W : OnePointHeytingAlgebraWitness M)

abbrev toProposition : OnePointPropositionWitness M :=
  W.toOnePointPropositionWitness

@[simp] theorem fiberMeet_proj
    (pq : PropFiberPair W.toTopologicalInterpretation.propSpace) :
    W.toTopologicalInterpretation.propSpace.proj (W.fiberMeet pq) =
      W.toTopologicalInterpretation.propSpace.proj pq.val.1 :=
  W.toProposition.fiberMeet_proj pq

@[simp] theorem fiberJoin_proj
    (pq : PropFiberPair W.toTopologicalInterpretation.propSpace) :
    W.toTopologicalInterpretation.propSpace.proj (W.fiberJoin pq) =
      W.toTopologicalInterpretation.propSpace.proj pq.val.1 :=
  W.toProposition.fiberJoin_proj pq

@[simp] theorem fiberHimp_proj
    (pq : PropFiberPair W.toTopologicalInterpretation.propSpace) :
    W.toTopologicalInterpretation.propSpace.proj (W.fiberHimp pq) =
      W.toTopologicalInterpretation.propSpace.proj pq.val.1 :=
  W.toProposition.fiberHimp_proj pq

end OnePointHeytingAlgebraWitness

/--
The second one-point Heyting field cluster: global-section connectives and
their algebraic laws, still stopping before equality and quantifiers.
-/
structure OnePointHeytingSectionWitness (M : GlobalModel.{u, v, 0, w'} Base Const)
    extends OnePointHeytingAlgebraWitness M where
  propMeet : toTopologicalInterpretation.propSpace.GlobalSection →
    toTopologicalInterpretation.propSpace.GlobalSection →
    toTopologicalInterpretation.propSpace.GlobalSection
  propJoin : toTopologicalInterpretation.propSpace.GlobalSection →
    toTopologicalInterpretation.propSpace.GlobalSection →
    toTopologicalInterpretation.propSpace.GlobalSection
  propHimp : toTopologicalInterpretation.propSpace.GlobalSection →
    toTopologicalInterpretation.propSpace.GlobalSection →
    toTopologicalInterpretation.propSpace.GlobalSection
  propMeet_comm : ∀ a b, propMeet a b = propMeet b a
  propMeet_assoc : ∀ a b c, propMeet (propMeet a b) c = propMeet a (propMeet b c)
  propMeet_top : ∀ a, propMeet a propTop = a
  propJoin_comm : ∀ a b, propJoin a b = propJoin b a
  propJoin_assoc : ∀ a b c, propJoin (propJoin a b) c = propJoin a (propJoin b c)
  propJoin_bot : ∀ a, propJoin a propBot = a
  propMeet_join_distrib : ∀ a b c,
    propMeet a (propJoin b c) = propJoin (propMeet a b) (propMeet a c)
  propHimp_adj : ∀ a b c,
    propMeet (propMeet a b) c = propMeet a b ↔ propMeet a (propHimp b c) = a

namespace OnePointHeytingSectionWitness

variable {M : GlobalModel.{u, v, 0, w'} Base Const} (W : OnePointHeytingSectionWitness M)

abbrev toAlgebra : OnePointHeytingAlgebraWitness M :=
  W.toOnePointHeytingAlgebraWitness

end OnePointHeytingSectionWitness

/--
Minimal concrete one-point witness for the Heyting layer.

This packages a full one-point `HeytingTopologicalInterpretation` together with
its typed carrier identification back to the archive-free global-model point
bridge. The remaining blocker is to *construct* such a witness for the intended
Awodey-Butz models, not to guess what interface the stronger theorem needs.
-/
structure OnePointHeytingWitness (M : GlobalModel.{u, v, 0, w'} Base Const)
    extends OnePointTopologicalWitness M where
  toHeytingInterpretation : HeytingTopologicalInterpretation.{u, v, 0} Base Const PUnit
  underlying_eq :
    toHeytingInterpretation.toTopologicalInterpretation = toTopologicalInterpretation

namespace OnePointHeytingWitness

variable {M : GlobalModel.{u, v, 0, w'} Base Const} (W : OnePointHeytingWitness M)

/-- Forget the one-point compatibility data and recover the concrete Heyting interpretation. -/
abbrev toHeyting : HeytingTopologicalInterpretation.{u, v, 0} Base Const PUnit :=
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

variable (M : GlobalModel.{u, v, 0, w'} Base Const)

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

theorem globalSection_ext {E : EtaleSpace PUnit} {s t : E.GlobalSection}
    (h : s.toContinuousMap () = t.toContinuousMap ()) :
    s = t := by
  cases s with
  | mk smap sproj =>
    cases t with
    | mk tmap tproj =>
      have hmap : smap = tmap := by
        ext u
        cases u
        exact h
      cases hmap
      have hproj : sproj = tproj := Subsingleton.elim _ _
      cases hproj
      rfl

theorem onePointPropGlobalSection_ext
    {M : GlobalModel.{u, v, 0, w'} Base Const}
    (W : OnePointPropositionWitness M)
    {s t : W.toTopologicalInterpretation.propSpace.GlobalSection}
    (h : W.decodeProp (s.toContinuousMap ()) = W.decodeProp (t.toContinuousMap ())) :
    s = t :=
  globalSection_ext (W.prop_ext h)

namespace OnePointHeytingAlgebraWitness

variable {M : GlobalModel.{u, v, 0, w'} Base Const} (W : OnePointHeytingAlgebraWitness M)

def propSectionPair
    (a b : W.toTopologicalInterpretation.propSpace.GlobalSection) :
    PropFiberPair W.toTopologicalInterpretation.propSpace :=
  ⟨(a.toContinuousMap (), b.toContinuousMap ()), by
    exact Subsingleton.elim _ _⟩

noncomputable def propMeetOfPoint
    (a b : W.toTopologicalInterpretation.propSpace.GlobalSection) :
    W.toTopologicalInterpretation.propSpace.GlobalSection :=
  globalSectionOfPoint (W.fiberMeet (W.propSectionPair a b))

noncomputable def propJoinOfPoint
    (a b : W.toTopologicalInterpretation.propSpace.GlobalSection) :
    W.toTopologicalInterpretation.propSpace.GlobalSection :=
  globalSectionOfPoint (W.fiberJoin (W.propSectionPair a b))

noncomputable def propHimpOfPoint
    (a b : W.toTopologicalInterpretation.propSpace.GlobalSection) :
    W.toTopologicalInterpretation.propSpace.GlobalSection :=
  globalSectionOfPoint (W.fiberHimp (W.propSectionPair a b))

@[simp] theorem propMeetOfPoint_apply
    (a b : W.toTopologicalInterpretation.propSpace.GlobalSection) :
    (W.propMeetOfPoint a b).toContinuousMap () =
      W.fiberMeet (W.propSectionPair a b) :=
  rfl

@[simp] theorem propJoinOfPoint_apply
    (a b : W.toTopologicalInterpretation.propSpace.GlobalSection) :
    (W.propJoinOfPoint a b).toContinuousMap () =
      W.fiberJoin (W.propSectionPair a b) :=
  rfl

@[simp] theorem propHimpOfPoint_apply
    (a b : W.toTopologicalInterpretation.propSpace.GlobalSection) :
    (W.propHimpOfPoint a b).toContinuousMap () =
      W.fiberHimp (W.propSectionPair a b) :=
  rfl

end OnePointHeytingAlgebraWitness

/-- Any fiber-pair operation over the one-point base is continuous. -/
theorem continuous_propFiberPair_of_onePoint
    {E : EtaleSpace PUnit}
    (f : PropFiberPair E → E.Carrier) :
    Continuous f := by
  haveI : DiscreteTopology E.Carrier := EtaleSpace.discreteTopology_of_discrete_base E
  haveI : DiscreteTopology (E.Carrier × E.Carrier) := inferInstance
  haveI : DiscreteTopology (PropFiberPair E) := inferInstance
  exact continuous_of_discreteTopology

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
    TopologicalInterpretation.{u, v, 0, 0} Base Const PUnit where
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
    rfl

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
    rfl

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

@[simp] theorem concreteOnePointPropositionWitness_join
    (p q : M.Carrier .prop) :
    (concreteOnePointPropositionWitness (M := M)).fiberJoin
        ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp p,
          (concreteOnePointPropositionWitness (M := M)).encodeProp q), by simp⟩ =
      (concreteOnePointPropositionWitness (M := M)).encodeProp (M.orP p q) := by
  exact (concreteOnePointPropositionWitness (M := M)).fiberJoin_apply p q

@[simp] theorem concreteOnePointPropositionWitness_himp
    (p q : M.Carrier .prop) :
    (concreteOnePointPropositionWitness (M := M)).fiberHimp
        ⟨((concreteOnePointPropositionWitness (M := M)).encodeProp p,
          (concreteOnePointPropositionWitness (M := M)).encodeProp q), by simp⟩ =
      (concreteOnePointPropositionWitness (M := M)).encodeProp (M.impP p q) := by
  exact (concreteOnePointPropositionWitness (M := M)).fiberHimp_apply p q

theorem concreteOnePointPropositionWitness_fiberMeet_decode
    (p q : (concreteOnePointPropositionWitness (M := M)).toTopologicalInterpretation.propSpace.Carrier)
    (h : (concreteOnePointPropositionWitness (M := M)).toTopologicalInterpretation.propSpace.proj p =
      (concreteOnePointPropositionWitness (M := M)).toTopologicalInterpretation.propSpace.proj q) :
    (concreteOnePointPropositionWitness (M := M)).fiberMeet ⟨(p, q), h⟩ =
      (concreteOnePointPropositionWitness (M := M)).encodeProp
        (M.andP
          ((concreteOnePointPropositionWitness (M := M)).decodeProp p)
          ((concreteOnePointPropositionWitness (M := M)).decodeProp q)) := by
  let W := concreteOnePointPropositionWitness (M := M)
  have hp : p = W.encodeProp (W.decodeProp p) := (W.encodeProp_decodeProp p).symm
  have hq : q = W.encodeProp (W.decodeProp q) := (W.encodeProp_decodeProp q).symm
  rw [hp, hq]
  change W.fiberMeet ⟨(W.encodeProp (W.decodeProp p), W.encodeProp (W.decodeProp q)), by simp⟩ =
    W.encodeProp (M.andP (W.decodeProp p) (W.decodeProp q))
  exact W.fiberMeet_apply (W.decodeProp p) (W.decodeProp q)

theorem concreteOnePointPropositionWitness_fiberJoin_decode
    (p q : (concreteOnePointPropositionWitness (M := M)).toTopologicalInterpretation.propSpace.Carrier)
    (h : (concreteOnePointPropositionWitness (M := M)).toTopologicalInterpretation.propSpace.proj p =
      (concreteOnePointPropositionWitness (M := M)).toTopologicalInterpretation.propSpace.proj q) :
    (concreteOnePointPropositionWitness (M := M)).fiberJoin ⟨(p, q), h⟩ =
      (concreteOnePointPropositionWitness (M := M)).encodeProp
        (M.orP
          ((concreteOnePointPropositionWitness (M := M)).decodeProp p)
          ((concreteOnePointPropositionWitness (M := M)).decodeProp q)) := by
  let W := concreteOnePointPropositionWitness (M := M)
  have hp : p = W.encodeProp (W.decodeProp p) := (W.encodeProp_decodeProp p).symm
  have hq : q = W.encodeProp (W.decodeProp q) := (W.encodeProp_decodeProp q).symm
  rw [hp, hq]
  change W.fiberJoin ⟨(W.encodeProp (W.decodeProp p), W.encodeProp (W.decodeProp q)), by simp⟩ =
    W.encodeProp (M.orP (W.decodeProp p) (W.decodeProp q))
  exact W.fiberJoin_apply (W.decodeProp p) (W.decodeProp q)

theorem concreteOnePointPropositionWitness_fiberHimp_decode
    (p q : (concreteOnePointPropositionWitness (M := M)).toTopologicalInterpretation.propSpace.Carrier)
    (h : (concreteOnePointPropositionWitness (M := M)).toTopologicalInterpretation.propSpace.proj p =
      (concreteOnePointPropositionWitness (M := M)).toTopologicalInterpretation.propSpace.proj q) :
    (concreteOnePointPropositionWitness (M := M)).fiberHimp ⟨(p, q), h⟩ =
      (concreteOnePointPropositionWitness (M := M)).encodeProp
        (M.impP
          ((concreteOnePointPropositionWitness (M := M)).decodeProp p)
          ((concreteOnePointPropositionWitness (M := M)).decodeProp q)) := by
  let W := concreteOnePointPropositionWitness (M := M)
  have hp : p = W.encodeProp (W.decodeProp p) := (W.encodeProp_decodeProp p).symm
  have hq : q = W.encodeProp (W.decodeProp q) := (W.encodeProp_decodeProp q).symm
  rw [hp, hq]
  change W.fiberHimp ⟨(W.encodeProp (W.decodeProp p), W.encodeProp (W.decodeProp q)), by simp⟩ =
    W.encodeProp (M.impP (W.decodeProp p) (W.decodeProp q))
  exact W.fiberHimp_apply (W.decodeProp p) (W.decodeProp q)

@[simp] theorem concreteOnePointPropositionWitness_decode_fiberMeet
    (p q : (concreteOnePointPropositionWitness (M := M)).toTopologicalInterpretation.propSpace.Carrier)
    (h : (concreteOnePointPropositionWitness (M := M)).toTopologicalInterpretation.propSpace.proj p =
      (concreteOnePointPropositionWitness (M := M)).toTopologicalInterpretation.propSpace.proj q) :
    (concreteOnePointPropositionWitness (M := M)).decodeProp
        ((concreteOnePointPropositionWitness (M := M)).fiberMeet ⟨(p, q), h⟩) =
      M.andP
        ((concreteOnePointPropositionWitness (M := M)).decodeProp p)
        ((concreteOnePointPropositionWitness (M := M)).decodeProp q) := by
  rw [concreteOnePointPropositionWitness_fiberMeet_decode]
  simp

@[simp] theorem concreteOnePointPropositionWitness_decode_fiberJoin
    (p q : (concreteOnePointPropositionWitness (M := M)).toTopologicalInterpretation.propSpace.Carrier)
    (h : (concreteOnePointPropositionWitness (M := M)).toTopologicalInterpretation.propSpace.proj p =
      (concreteOnePointPropositionWitness (M := M)).toTopologicalInterpretation.propSpace.proj q) :
    (concreteOnePointPropositionWitness (M := M)).decodeProp
        ((concreteOnePointPropositionWitness (M := M)).fiberJoin ⟨(p, q), h⟩) =
      M.orP
        ((concreteOnePointPropositionWitness (M := M)).decodeProp p)
        ((concreteOnePointPropositionWitness (M := M)).decodeProp q) := by
  rw [concreteOnePointPropositionWitness_fiberJoin_decode]
  simp

@[simp] theorem concreteOnePointPropositionWitness_decode_fiberHimp
    (p q : (concreteOnePointPropositionWitness (M := M)).toTopologicalInterpretation.propSpace.Carrier)
    (h : (concreteOnePointPropositionWitness (M := M)).toTopologicalInterpretation.propSpace.proj p =
      (concreteOnePointPropositionWitness (M := M)).toTopologicalInterpretation.propSpace.proj q) :
    (concreteOnePointPropositionWitness (M := M)).decodeProp
        ((concreteOnePointPropositionWitness (M := M)).fiberHimp ⟨(p, q), h⟩) =
      M.impP
        ((concreteOnePointPropositionWitness (M := M)).decodeProp p)
        ((concreteOnePointPropositionWitness (M := M)).decodeProp q) := by
  rw [concreteOnePointPropositionWitness_fiberHimp_decode]
  simp

noncomputable def concreteOnePointHeytingAlgebraWitness
    (laws : PropCarrierHeytingLaws M) :
    OnePointHeytingAlgebraWitness M where
  toOnePointPropositionWitness := concreteOnePointPropositionWitness (M := M)
  fiberMeet_continuous := by
    change Continuous (concreteFiberMeet (M := M))
    exact continuous_propFiberPair_of_onePoint _
  fiberJoin_continuous := by
    change Continuous (concreteFiberJoin (M := M))
    exact continuous_propFiberPair_of_onePoint _
  fiberHimp_continuous := by
    change Continuous (concreteFiberHimp (M := M))
    exact continuous_propFiberPair_of_onePoint _
  fiberMeet_idempotent := by
    intro p
    let W := concreteOnePointPropositionWitness (M := M)
    exact W.prop_ext (by
      show W.decodeProp (W.fiberMeet ⟨(p, p), rfl⟩) = W.decodeProp p
      rw [concreteOnePointPropositionWitness_decode_fiberMeet]
      exact laws.and_idempotent (W.decodeProp p))
  fiberMeet_top := by
    intro p
    let W := concreteOnePointPropositionWitness (M := M)
    have htop :
        W.propTop.toContinuousMap (W.toTopologicalInterpretation.propSpace.proj p) =
          W.encodeProp M.topP := by
      have hunit : W.toTopologicalInterpretation.propSpace.proj p = () :=
        Subsingleton.elim _ _
      rw [hunit]
      exact W.propTop_apply
    rw [htop]
    exact W.prop_ext (by
      show W.decodeProp (W.fiberMeet ⟨(p, W.encodeProp M.topP), by simp⟩) =
        W.decodeProp p
      rw [concreteOnePointPropositionWitness_decode_fiberMeet]
      exact laws.and_top (W.decodeProp p))
  fiberMeet_bot := by
    intro p
    let W := concreteOnePointPropositionWitness (M := M)
    have hbot :
        W.propBot.toContinuousMap (W.toTopologicalInterpretation.propSpace.proj p) =
          W.encodeProp M.botP := by
      have hunit : W.toTopologicalInterpretation.propSpace.proj p = () :=
        Subsingleton.elim _ _
      rw [hunit]
      exact W.propBot_apply
    rw [hbot]
    exact W.prop_ext (by
      show W.decodeProp (W.fiberMeet ⟨(W.encodeProp M.botP, p), by simp⟩) =
        W.decodeProp (W.encodeProp M.botP)
      rw [concreteOnePointPropositionWitness_decode_fiberMeet]
      simp [W, laws.and_bot])
  fiberMeet_comm := by
    intro pq
    let W := concreteOnePointPropositionWitness (M := M)
    exact W.prop_ext (by
      show W.decodeProp (W.fiberMeet pq) =
        W.decodeProp (W.fiberMeet ⟨(pq.val.2, pq.val.1), pq.property.symm⟩)
      rw [concreteOnePointPropositionWitness_decode_fiberMeet,
        concreteOnePointPropositionWitness_decode_fiberMeet]
      exact laws.and_comm (W.decodeProp pq.val.1) (W.decodeProp pq.val.2))
  fiberMeet_assoc := by
    intro p q r hpq hqr
    let W := concreteOnePointPropositionWitness (M := M)
    exact W.prop_ext (by
      show
        W.decodeProp
            (W.fiberMeet
              ⟨(W.fiberMeet ⟨(p, q), hpq⟩, r),
                (W.fiberMeet_proj ⟨(p, q), hpq⟩).trans (hpq.trans hqr)⟩) =
          W.decodeProp
            (W.fiberMeet
              ⟨(p, W.fiberMeet ⟨(q, r), hqr⟩),
                hpq.trans (W.fiberMeet_proj ⟨(q, r), hqr⟩).symm⟩)
      rw [concreteOnePointPropositionWitness_decode_fiberMeet,
        concreteOnePointPropositionWitness_decode_fiberMeet,
        concreteOnePointPropositionWitness_decode_fiberMeet,
        concreteOnePointPropositionWitness_decode_fiberMeet]
      exact laws.and_assoc (W.decodeProp p) (W.decodeProp q) (W.decodeProp r))
  fiberJoin_upper := by
    intro pq
    let W := concreteOnePointPropositionWitness (M := M)
    exact W.prop_ext (by
      show
        W.decodeProp
            (W.fiberMeet
              ⟨(pq.val.1, W.fiberJoin pq), (W.fiberJoin_proj pq).symm⟩) =
          W.decodeProp pq.val.1
      rw [concreteOnePointPropositionWitness_decode_fiberMeet,
        concreteOnePointPropositionWitness_decode_fiberJoin]
      exact laws.or_upper (W.decodeProp pq.val.1) (W.decodeProp pq.val.2))
  fiberJoin_comm := by
    intro pq
    let W := concreteOnePointPropositionWitness (M := M)
    exact W.prop_ext (by
      show W.decodeProp (W.fiberJoin pq) =
        W.decodeProp (W.fiberJoin ⟨(pq.val.2, pq.val.1), pq.property.symm⟩)
      rw [concreteOnePointPropositionWitness_decode_fiberJoin,
        concreteOnePointPropositionWitness_decode_fiberJoin]
      exact laws.or_comm (W.decodeProp pq.val.1) (W.decodeProp pq.val.2))
  fiberMeet_proj_fst := by
    intro pq
    let W := concreteOnePointPropositionWitness (M := M)
    exact W.prop_ext (by
      show W.decodeProp (W.fiberMeet ⟨(W.fiberMeet pq, pq.val.1), W.fiberMeet_proj pq⟩) =
        W.decodeProp (W.fiberMeet pq)
      rw [concreteOnePointPropositionWitness_decode_fiberMeet,
        concreteOnePointPropositionWitness_decode_fiberMeet]
      exact laws.and_proj_fst (W.decodeProp pq.val.1) (W.decodeProp pq.val.2))
  fiberMeet_proj_snd := by
    intro pq
    let W := concreteOnePointPropositionWitness (M := M)
    exact W.prop_ext (by
      show
        W.decodeProp
            (W.fiberMeet
              ⟨(W.fiberMeet pq, pq.val.2), (W.fiberMeet_proj pq).trans pq.property⟩) =
          W.decodeProp (W.fiberMeet pq)
      rw [concreteOnePointPropositionWitness_decode_fiberMeet,
        concreteOnePointPropositionWitness_decode_fiberMeet]
      exact laws.and_proj_snd (W.decodeProp pq.val.1) (W.decodeProp pq.val.2))
  fiberMeet_join_distrib := by
    intro p q r hpq hqr
    let W := concreteOnePointPropositionWitness (M := M)
    exact W.prop_ext (by
      show
        W.decodeProp
            (W.fiberMeet
              ⟨(W.fiberJoin ⟨(p, q), hpq⟩, r),
                (W.fiberJoin_proj ⟨(p, q), hpq⟩).trans (hpq.trans hqr)⟩) =
          W.decodeProp
            (W.fiberJoin
              ⟨(W.fiberMeet ⟨(p, r), hpq.trans hqr⟩, W.fiberMeet ⟨(q, r), hqr⟩),
                (W.fiberMeet_proj ⟨(p, r), hpq.trans hqr⟩).trans
                  (hpq.trans (W.fiberMeet_proj ⟨(q, r), hqr⟩).symm)⟩)
      rw [concreteOnePointPropositionWitness_decode_fiberMeet,
        concreteOnePointPropositionWitness_decode_fiberJoin,
        concreteOnePointPropositionWitness_decode_fiberJoin,
        concreteOnePointPropositionWitness_decode_fiberMeet,
        concreteOnePointPropositionWitness_decode_fiberMeet]
      exact laws.and_or_distrib (W.decodeProp p) (W.decodeProp q) (W.decodeProp r))
  fiberJoin_lub := by
    intro p q r hpq hpr hp_le_r hq_le_r
    let W := concreteOnePointPropositionWitness (M := M)
    have hp_le_r' : M.andP (W.decodeProp p) (W.decodeProp r) = W.decodeProp p := by
      have hdecode :
          W.decodeProp (W.fiberMeet ⟨(p, r), hpr⟩) = W.decodeProp p :=
        congrArg W.decodeProp hp_le_r
      simpa [W, concreteOnePointPropositionWitness_decode_fiberMeet] using hdecode
    have hq_le_r' : M.andP (W.decodeProp q) (W.decodeProp r) = W.decodeProp q := by
      have hdecode :
          W.decodeProp (W.fiberMeet ⟨(q, r), hpq.symm.trans hpr⟩) = W.decodeProp q :=
        congrArg W.decodeProp hq_le_r
      simpa [W, concreteOnePointPropositionWitness_decode_fiberMeet] using hdecode
    exact W.prop_ext (by
      show
        W.decodeProp
            (W.fiberMeet
              ⟨(W.fiberJoin ⟨(p, q), hpq⟩, r),
                (W.fiberJoin_proj ⟨(p, q), hpq⟩).trans hpr⟩) =
          W.decodeProp (W.fiberJoin ⟨(p, q), hpq⟩)
      rw [concreteOnePointPropositionWitness_decode_fiberMeet,
        concreteOnePointPropositionWitness_decode_fiberJoin]
      exact laws.or_lub (W.decodeProp p) (W.decodeProp q) (W.decodeProp r)
        hp_le_r' hq_le_r')
  fiberHimp_adj := by
    intro a b c hab hbc
    let W := concreteOnePointPropositionWitness (M := M)
    constructor
    · intro hleft
      have hleft' :
          M.andP (M.andP (W.decodeProp a) (W.decodeProp b)) (W.decodeProp c) =
            M.andP (W.decodeProp a) (W.decodeProp b) := by
        have hdecode :
            W.decodeProp
                (W.fiberMeet
                  ⟨(W.fiberMeet ⟨(a, b), hab⟩, c),
                    (W.fiberMeet_proj ⟨(a, b), hab⟩).trans (hab.trans hbc)⟩) =
            W.decodeProp (W.fiberMeet ⟨(a, b), hab⟩) :=
          congrArg W.decodeProp hleft
        simpa [W, concreteOnePointPropositionWitness_decode_fiberMeet] using hdecode
      have hright' :
          M.andP (W.decodeProp a) (M.impP (W.decodeProp b) (W.decodeProp c)) =
            W.decodeProp a :=
        (laws.himp_adj (W.decodeProp a) (W.decodeProp b) (W.decodeProp c)).1 hleft'
      exact W.prop_ext (by
        show
          W.decodeProp
              (W.fiberMeet
                ⟨(a, W.fiberHimp ⟨(b, c), hbc⟩),
                  hab.trans (W.fiberHimp_proj ⟨(b, c), hbc⟩).symm⟩) =
            W.decodeProp a
        simpa [W, concreteOnePointPropositionWitness_decode_fiberMeet,
          concreteOnePointPropositionWitness_decode_fiberHimp] using hright')
    · intro hright
      have hright' :
          M.andP (W.decodeProp a) (M.impP (W.decodeProp b) (W.decodeProp c)) =
            W.decodeProp a := by
        have hdecode :
            W.decodeProp
                (W.fiberMeet
                  ⟨(a, W.fiberHimp ⟨(b, c), hbc⟩),
                    hab.trans (W.fiberHimp_proj ⟨(b, c), hbc⟩).symm⟩) =
            W.decodeProp a :=
          congrArg W.decodeProp hright
        simpa [W, concreteOnePointPropositionWitness_decode_fiberMeet,
          concreteOnePointPropositionWitness_decode_fiberHimp] using hdecode
      have hleft' :
          M.andP (M.andP (W.decodeProp a) (W.decodeProp b)) (W.decodeProp c) =
            M.andP (W.decodeProp a) (W.decodeProp b) :=
        (laws.himp_adj (W.decodeProp a) (W.decodeProp b) (W.decodeProp c)).2 hright'
      exact W.prop_ext (by
        show
          W.decodeProp
              (W.fiberMeet
                ⟨(W.fiberMeet ⟨(a, b), hab⟩, c),
                  (W.fiberMeet_proj ⟨(a, b), hab⟩).trans (hab.trans hbc)⟩) =
            W.decodeProp (W.fiberMeet ⟨(a, b), hab⟩)
        simpa [W, concreteOnePointPropositionWitness_decode_fiberMeet] using hleft')

@[simp] theorem concreteOnePointHeytingAlgebraWitness_decode_propMeetOfPoint
    (laws : PropCarrierHeytingLaws M)
    (a b :
      (((concreteOnePointHeytingAlgebraWitness (M := M) laws).toTopologicalInterpretation.propSpace).GlobalSection)) :
    (concreteOnePointPropositionWitness (M := M)).decodeProp
        ((((concreteOnePointHeytingAlgebraWitness (M := M) laws).propMeetOfPoint a b).toContinuousMap) ()) =
      M.andP
        ((concreteOnePointPropositionWitness (M := M)).decodeProp
          (a.toContinuousMap ()))
        ((concreteOnePointPropositionWitness (M := M)).decodeProp
          (b.toContinuousMap ())) := by
  let P := concreteOnePointPropositionWitness (M := M)
  change P.decodeProp
      ((globalSectionOfPoint
        (P.fiberMeet ⟨(a.toContinuousMap (), b.toContinuousMap ()), by
          exact Subsingleton.elim _ _⟩)).toContinuousMap ()) =
    M.andP (P.decodeProp (a.toContinuousMap ())) (P.decodeProp (b.toContinuousMap ()))
  rw [globalSectionOfPoint_apply]
  exact concreteOnePointPropositionWitness_decode_fiberMeet
    (M := M) (a.toContinuousMap ()) (b.toContinuousMap _) _

@[simp] theorem concreteOnePointHeytingAlgebraWitness_decode_propJoinOfPoint
    (laws : PropCarrierHeytingLaws M)
    (a b :
      (((concreteOnePointHeytingAlgebraWitness (M := M) laws).toTopologicalInterpretation.propSpace).GlobalSection)) :
    (concreteOnePointPropositionWitness (M := M)).decodeProp
        ((((concreteOnePointHeytingAlgebraWitness (M := M) laws).propJoinOfPoint a b).toContinuousMap) ()) =
      M.orP
        ((concreteOnePointPropositionWitness (M := M)).decodeProp
          (a.toContinuousMap ()))
        ((concreteOnePointPropositionWitness (M := M)).decodeProp
          (b.toContinuousMap ())) := by
  let P := concreteOnePointPropositionWitness (M := M)
  change P.decodeProp
      ((globalSectionOfPoint
        (P.fiberJoin ⟨(a.toContinuousMap (), b.toContinuousMap ()), by
          exact Subsingleton.elim _ _⟩)).toContinuousMap ()) =
    M.orP (P.decodeProp (a.toContinuousMap ())) (P.decodeProp (b.toContinuousMap ()))
  rw [globalSectionOfPoint_apply]
  exact concreteOnePointPropositionWitness_decode_fiberJoin
    (M := M) (a.toContinuousMap ()) (b.toContinuousMap _) _

@[simp] theorem concreteOnePointHeytingAlgebraWitness_decode_propHimpOfPoint
    (laws : PropCarrierHeytingLaws M)
    (a b :
      (((concreteOnePointHeytingAlgebraWitness (M := M) laws).toTopologicalInterpretation.propSpace).GlobalSection)) :
    (concreteOnePointPropositionWitness (M := M)).decodeProp
        ((((concreteOnePointHeytingAlgebraWitness (M := M) laws).propHimpOfPoint a b).toContinuousMap) ()) =
      M.impP
        ((concreteOnePointPropositionWitness (M := M)).decodeProp
          (a.toContinuousMap ()))
        ((concreteOnePointPropositionWitness (M := M)).decodeProp
          (b.toContinuousMap ())) := by
  let P := concreteOnePointPropositionWitness (M := M)
  change P.decodeProp
      ((globalSectionOfPoint
        (P.fiberHimp ⟨(a.toContinuousMap (), b.toContinuousMap ()), by
          exact Subsingleton.elim _ _⟩)).toContinuousMap ()) =
    M.impP (P.decodeProp (a.toContinuousMap ())) (P.decodeProp (b.toContinuousMap ()))
  rw [globalSectionOfPoint_apply]
  exact concreteOnePointPropositionWitness_decode_fiberHimp
    (M := M) (a.toContinuousMap ()) (b.toContinuousMap _) _

private noncomputable def concretePropMeetSection
    (a b : (concreteOnePointTopologicalInterpretation (M := M)).propSpace.GlobalSection) :
    (concreteOnePointTopologicalInterpretation (M := M)).propSpace.GlobalSection :=
  let P := concreteOnePointPropositionWitness (M := M)
  globalSectionOfPoint
    (P.encodeProp (M.andP (P.decodeProp (a.toContinuousMap ()))
      (P.decodeProp (b.toContinuousMap ()))))

private noncomputable def concretePropJoinSection
    (a b : (concreteOnePointTopologicalInterpretation (M := M)).propSpace.GlobalSection) :
    (concreteOnePointTopologicalInterpretation (M := M)).propSpace.GlobalSection :=
  let P := concreteOnePointPropositionWitness (M := M)
  globalSectionOfPoint
    (P.encodeProp (M.orP (P.decodeProp (a.toContinuousMap ()))
      (P.decodeProp (b.toContinuousMap ()))))

private noncomputable def concretePropHimpSection
    (a b : (concreteOnePointTopologicalInterpretation (M := M)).propSpace.GlobalSection) :
    (concreteOnePointTopologicalInterpretation (M := M)).propSpace.GlobalSection :=
  let P := concreteOnePointPropositionWitness (M := M)
  globalSectionOfPoint
    (P.encodeProp (M.impP (P.decodeProp (a.toContinuousMap ()))
      (P.decodeProp (b.toContinuousMap ()))))

@[simp] private theorem concretePropMeetSection_decode
    (a b : (concreteOnePointTopologicalInterpretation (M := M)).propSpace.GlobalSection) :
    (concreteOnePointPropositionWitness (M := M)).decodeProp
        ((concretePropMeetSection (M := M) a b).toContinuousMap ()) =
      M.andP
        ((concreteOnePointPropositionWitness (M := M)).decodeProp (a.toContinuousMap ()))
        ((concreteOnePointPropositionWitness (M := M)).decodeProp (b.toContinuousMap ())) := by
  let P := concreteOnePointPropositionWitness (M := M)
  change
    P.decodeProp
        ((globalSectionOfPoint
          (P.encodeProp
            (M.andP (P.decodeProp (a.toContinuousMap ()))
              (P.decodeProp (b.toContinuousMap ()))))).toContinuousMap ()) =
      M.andP (P.decodeProp (a.toContinuousMap ()))
        (P.decodeProp (b.toContinuousMap ()))
  rw [globalSectionOfPoint_apply]
  exact P.decodeProp_encodeProp _

@[simp] private theorem concretePropJoinSection_decode
    (a b : (concreteOnePointTopologicalInterpretation (M := M)).propSpace.GlobalSection) :
    (concreteOnePointPropositionWitness (M := M)).decodeProp
        ((concretePropJoinSection (M := M) a b).toContinuousMap ()) =
      M.orP
        ((concreteOnePointPropositionWitness (M := M)).decodeProp (a.toContinuousMap ()))
        ((concreteOnePointPropositionWitness (M := M)).decodeProp (b.toContinuousMap ())) := by
  let P := concreteOnePointPropositionWitness (M := M)
  change
    P.decodeProp
        ((globalSectionOfPoint
          (P.encodeProp
            (M.orP (P.decodeProp (a.toContinuousMap ()))
              (P.decodeProp (b.toContinuousMap ()))))).toContinuousMap ()) =
      M.orP (P.decodeProp (a.toContinuousMap ()))
        (P.decodeProp (b.toContinuousMap ()))
  rw [globalSectionOfPoint_apply]
  exact P.decodeProp_encodeProp _

@[simp] private theorem concretePropHimpSection_decode
    (a b : (concreteOnePointTopologicalInterpretation (M := M)).propSpace.GlobalSection) :
    (concreteOnePointPropositionWitness (M := M)).decodeProp
        ((concretePropHimpSection (M := M) a b).toContinuousMap ()) =
      M.impP
        ((concreteOnePointPropositionWitness (M := M)).decodeProp (a.toContinuousMap ()))
        ((concreteOnePointPropositionWitness (M := M)).decodeProp (b.toContinuousMap ())) := by
  let P := concreteOnePointPropositionWitness (M := M)
  change
    P.decodeProp
        ((globalSectionOfPoint
          (P.encodeProp
            (M.impP (P.decodeProp (a.toContinuousMap ()))
              (P.decodeProp (b.toContinuousMap ()))))).toContinuousMap ()) =
      M.impP (P.decodeProp (a.toContinuousMap ()))
        (P.decodeProp (b.toContinuousMap ()))
  rw [globalSectionOfPoint_apply]
  exact P.decodeProp_encodeProp _

noncomputable def concreteOnePointHeytingSectionWitness
    (laws : PropCarrierHeytingLaws M) :
    OnePointHeytingSectionWitness M :=
  let A := concreteOnePointHeytingAlgebraWitness (M := M) laws
  let P := concreteOnePointPropositionWitness (M := M)
  { toOnePointHeytingAlgebraWitness := A
    propMeet := concretePropMeetSection (M := M)
    propJoin := concretePropJoinSection (M := M)
    propHimp := concretePropHimpSection (M := M)
    propMeet_comm := by
      intro a b
      change concretePropMeetSection (M := M) a b =
        concretePropMeetSection (M := M) b a
      apply onePointPropGlobalSection_ext P
      change
        P.decodeProp ((concretePropMeetSection (M := M) a b).toContinuousMap ()) =
          P.decodeProp ((concretePropMeetSection (M := M) b a).toContinuousMap ())
      rw [concretePropMeetSection_decode, concretePropMeetSection_decode]
      exact laws.and_comm (P.decodeProp (a.toContinuousMap ()))
        (P.decodeProp (b.toContinuousMap ()))
    propMeet_assoc := by
      intro a b c
      change concretePropMeetSection (M := M) (concretePropMeetSection (M := M) a b) c =
        concretePropMeetSection (M := M) a (concretePropMeetSection (M := M) b c)
      apply onePointPropGlobalSection_ext P
      change
        P.decodeProp
            ((concretePropMeetSection (M := M)
              (concretePropMeetSection (M := M) a b) c).toContinuousMap ()) =
          P.decodeProp
            ((concretePropMeetSection (M := M) a
              (concretePropMeetSection (M := M) b c)).toContinuousMap ())
      rw [concretePropMeetSection_decode, concretePropMeetSection_decode,
        concretePropMeetSection_decode, concretePropMeetSection_decode]
      exact laws.and_assoc (P.decodeProp (a.toContinuousMap ()))
        (P.decodeProp (b.toContinuousMap ()))
        (P.decodeProp (c.toContinuousMap ()))
    propMeet_top := by
      intro a
      change concretePropMeetSection (M := M) a A.propTop = a
      apply onePointPropGlobalSection_ext P
      change
        P.decodeProp ((concretePropMeetSection (M := M) a A.propTop).toContinuousMap ()) =
          P.decodeProp (a.toContinuousMap ())
      rw [concretePropMeetSection_decode]
      have htop : P.decodeProp (A.propTop.toContinuousMap ()) = M.topP := by
        change P.decodeProp (P.encodeProp M.topP) = M.topP
        exact P.decodeProp_encodeProp M.topP
      exact htop ▸ laws.and_top (P.decodeProp (a.toContinuousMap ()))
    propJoin_comm := by
      intro a b
      change concretePropJoinSection (M := M) a b =
        concretePropJoinSection (M := M) b a
      apply onePointPropGlobalSection_ext P
      change
        P.decodeProp ((concretePropJoinSection (M := M) a b).toContinuousMap ()) =
          P.decodeProp ((concretePropJoinSection (M := M) b a).toContinuousMap ())
      rw [concretePropJoinSection_decode, concretePropJoinSection_decode]
      exact laws.or_comm (P.decodeProp (a.toContinuousMap ()))
        (P.decodeProp (b.toContinuousMap ()))
    propJoin_assoc := by
      intro a b c
      change concretePropJoinSection (M := M) (concretePropJoinSection (M := M) a b) c =
        concretePropJoinSection (M := M) a (concretePropJoinSection (M := M) b c)
      apply onePointPropGlobalSection_ext P
      change
        P.decodeProp
            ((concretePropJoinSection (M := M)
              (concretePropJoinSection (M := M) a b) c).toContinuousMap ()) =
          P.decodeProp
            ((concretePropJoinSection (M := M) a
              (concretePropJoinSection (M := M) b c)).toContinuousMap ())
      rw [concretePropJoinSection_decode, concretePropJoinSection_decode,
        concretePropJoinSection_decode, concretePropJoinSection_decode]
      exact laws.or_assoc (P.decodeProp (a.toContinuousMap ()))
        (P.decodeProp (b.toContinuousMap ()))
        (P.decodeProp (c.toContinuousMap ()))
    propJoin_bot := by
      intro a
      change concretePropJoinSection (M := M) a A.propBot = a
      apply onePointPropGlobalSection_ext P
      change
        P.decodeProp ((concretePropJoinSection (M := M) a A.propBot).toContinuousMap ()) =
          P.decodeProp (a.toContinuousMap ())
      rw [concretePropJoinSection_decode]
      have hbot : P.decodeProp (A.propBot.toContinuousMap ()) = M.botP := by
        change P.decodeProp (P.encodeProp M.botP) = M.botP
        exact P.decodeProp_encodeProp M.botP
      exact hbot ▸ laws.or_bot (P.decodeProp (a.toContinuousMap ()))
    propMeet_join_distrib := by
      intro a b c
      change concretePropMeetSection (M := M) a (concretePropJoinSection (M := M) b c) =
        concretePropJoinSection (M := M)
          (concretePropMeetSection (M := M) a b)
          (concretePropMeetSection (M := M) a c)
      apply onePointPropGlobalSection_ext P
      change
        P.decodeProp
            ((concretePropMeetSection (M := M) a
              (concretePropJoinSection (M := M) b c)).toContinuousMap ()) =
          P.decodeProp
            ((concretePropJoinSection (M := M)
              (concretePropMeetSection (M := M) a b)
              (concretePropMeetSection (M := M) a c)).toContinuousMap ())
      rw [concretePropMeetSection_decode, concretePropJoinSection_decode,
        concretePropJoinSection_decode, concretePropMeetSection_decode,
        concretePropMeetSection_decode]
      exact laws.and_or_distrib_left (P.decodeProp (a.toContinuousMap ()))
        (P.decodeProp (b.toContinuousMap ()))
        (P.decodeProp (c.toContinuousMap ()))
    propHimp_adj := by
      intro a b c
      constructor
      · intro h
        change concretePropMeetSection (M := M)
            (concretePropMeetSection (M := M) a b) c =
          concretePropMeetSection (M := M) a b at h
        have hcarrier := by
          have hdecode :=
            congrArg (fun s => P.decodeProp (s.toContinuousMap ())) h
          change
            P.decodeProp
                ((concretePropMeetSection (M := M)
                  (concretePropMeetSection (M := M) a b) c).toContinuousMap ()) =
              P.decodeProp ((concretePropMeetSection (M := M) a b).toContinuousMap ()) at hdecode
          simpa only [P, propTy, concretePropMeetSection_decode] using hdecode
        have hright :
            M.andP (P.decodeProp (a.toContinuousMap ()))
                (M.impP (P.decodeProp (b.toContinuousMap ()))
                  (P.decodeProp (c.toContinuousMap ()))) =
              P.decodeProp (a.toContinuousMap ()) :=
          (laws.himp_adj
            (P.decodeProp (a.toContinuousMap ()))
            (P.decodeProp (b.toContinuousMap ()))
            (P.decodeProp (c.toContinuousMap ()))).1 hcarrier
        change concretePropMeetSection (M := M) a (concretePropHimpSection (M := M) b c) = a
        apply onePointPropGlobalSection_ext P
        change
          P.decodeProp
              ((concretePropMeetSection (M := M) a
                (concretePropHimpSection (M := M) b c)).toContinuousMap ()) =
            P.decodeProp (a.toContinuousMap ())
        rw [concretePropMeetSection_decode, concretePropHimpSection_decode]
        exact hright
      · intro h
        change concretePropMeetSection (M := M) a (concretePropHimpSection (M := M) b c) =
          a at h
        have hcarrier := by
          have hdecode :=
            congrArg (fun s => P.decodeProp (s.toContinuousMap ())) h
          change
            P.decodeProp
                ((concretePropMeetSection (M := M) a
                  (concretePropHimpSection (M := M) b c)).toContinuousMap ()) =
              P.decodeProp (a.toContinuousMap ()) at hdecode
          rw [concretePropMeetSection_decode, concretePropHimpSection_decode] at hdecode
          exact hdecode
        have hleft :=
          (laws.himp_adj
            (P.decodeProp (a.toContinuousMap ()))
            (P.decodeProp (b.toContinuousMap ()))
            (P.decodeProp (c.toContinuousMap ()))).2 hcarrier
        change concretePropMeetSection (M := M)
            (concretePropMeetSection (M := M) a b) c =
          concretePropMeetSection (M := M) a b
        apply onePointPropGlobalSection_ext P
        change
          P.decodeProp
              ((concretePropMeetSection (M := M)
                (concretePropMeetSection (M := M) a b) c).toContinuousMap ()) =
            P.decodeProp ((concretePropMeetSection (M := M) a b).toContinuousMap ())
        exact hleft }

@[simp] theorem concreteOnePointHeytingSectionWitness_propMeet_eq_propMeetOfPoint
    (laws : PropCarrierHeytingLaws M)
    (a b :
      (((concreteOnePointHeytingSectionWitness (M := M) laws).toTopologicalInterpretation.propSpace).GlobalSection)) :
    (concreteOnePointHeytingSectionWitness (M := M) laws).propMeet a b =
      (concreteOnePointHeytingAlgebraWitness (M := M) laws).propMeetOfPoint a b := by
  let P := concreteOnePointPropositionWitness (M := M)
  apply onePointPropGlobalSection_ext P
  change
    P.decodeProp ((concretePropMeetSection (M := M) a b).toContinuousMap ()) =
      P.decodeProp
        (((concreteOnePointHeytingAlgebraWitness (M := M) laws).propMeetOfPoint a b).toContinuousMap ())
  rw [concretePropMeetSection_decode]
  exact (concreteOnePointHeytingAlgebraWitness_decode_propMeetOfPoint
    (M := M) laws a b).symm

@[simp] theorem concreteOnePointHeytingSectionWitness_propJoin_eq_propJoinOfPoint
    (laws : PropCarrierHeytingLaws M)
    (a b :
      (((concreteOnePointHeytingSectionWitness (M := M) laws).toTopologicalInterpretation.propSpace).GlobalSection)) :
    (concreteOnePointHeytingSectionWitness (M := M) laws).propJoin a b =
      (concreteOnePointHeytingAlgebraWitness (M := M) laws).propJoinOfPoint a b := by
  let P := concreteOnePointPropositionWitness (M := M)
  apply onePointPropGlobalSection_ext P
  change
    P.decodeProp ((concretePropJoinSection (M := M) a b).toContinuousMap ()) =
      P.decodeProp
        (((concreteOnePointHeytingAlgebraWitness (M := M) laws).propJoinOfPoint a b).toContinuousMap ())
  rw [concretePropJoinSection_decode]
  exact (concreteOnePointHeytingAlgebraWitness_decode_propJoinOfPoint
    (M := M) laws a b).symm

@[simp] theorem concreteOnePointHeytingSectionWitness_propHimp_eq_propHimpOfPoint
    (laws : PropCarrierHeytingLaws M)
    (a b :
      (((concreteOnePointHeytingSectionWitness (M := M) laws).toTopologicalInterpretation.propSpace).GlobalSection)) :
    (concreteOnePointHeytingSectionWitness (M := M) laws).propHimp a b =
      (concreteOnePointHeytingAlgebraWitness (M := M) laws).propHimpOfPoint a b := by
  let P := concreteOnePointPropositionWitness (M := M)
  apply onePointPropGlobalSection_ext P
  change
    P.decodeProp ((concretePropHimpSection (M := M) a b).toContinuousMap ()) =
      P.decodeProp
        (((concreteOnePointHeytingAlgebraWitness (M := M) laws).propHimpOfPoint a b).toContinuousMap ())
  rw [concretePropHimpSection_decode]
  exact (concreteOnePointHeytingAlgebraWitness_decode_propHimpOfPoint
    (M := M) laws a b).symm

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

@[simp] theorem pointFormulaValue_eq
    {Γ : Ctx Base} {τ : Ty Base}
    (t u : Term Const Γ τ)
    (γ : (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier) :
    pointFormulaValue (M := M) (Term.eq t u) γ =
      M.eqP
        (SemilocalModel.eval M.toSemilocalModel
          (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.decodeEnv (M := M) γ) t)
        (SemilocalModel.eval M.toSemilocalModel
          (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.decodeEnv (M := M) γ) u) := by
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

theorem formula_witness_truth_eq_truthEval
    {Γ : Ctx Base}
    (χ : Formula Const Γ)
    (γ : (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier) :
    M.truth
        ((concreteOnePointPropositionWitness (M := M)).decodeProp
          ((concreteOnePointPropositionWitness (M := M)).encodeProp
            (pointFormulaValue (M := M) χ γ))) =
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthEval
        (M := M) χ γ := by
  exact connective_formula_witness_truth_eq_truthEval
    (M := M) χ γ
    ((concreteOnePointPropositionWitness (M := M)).encodeProp
      (pointFormulaValue (M := M) χ γ)) rfl

theorem formula_witness_top_of_truthValidSequent
    {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)}
    {χ : Formula Const Γ}
    (hvalid :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.TruthValidSequent
        (M := M) Δ χ)
    (γ : (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.ctxSpace (M := M) Γ).Carrier)
    (hΔ :
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.truthAntecedent
        (M := M) Δ γ = ⊤) :
    M.truth
        ((concreteOnePointPropositionWitness (M := M)).decodeProp
          ((concreteOnePointPropositionWitness (M := M)).encodeProp
            (pointFormulaValue (M := M) χ γ))) = ⊤ := by
  refine connective_formula_witness_top_of_truthValidSequent
    (M := M) hvalid γ hΔ
    ((concreteOnePointPropositionWitness (M := M)).encodeProp
      (pointFormulaValue (M := M) χ γ)) ?_
  exact formula_witness_truth_eq_truthEval (M := M) χ γ

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
  rw [concreteOnePointPropositionWitness_formula_and (M := M) φ ψ γ]
  exact formula_witness_top_of_truthValidSequent (M := M) (χ := Term.and φ ψ)
    hvalid γ hΔ

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
  rw [concreteOnePointPropositionWitness_formula_or (M := M) φ ψ γ]
  exact formula_witness_top_of_truthValidSequent (M := M) (χ := Term.or φ ψ)
    hvalid γ hΔ

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
