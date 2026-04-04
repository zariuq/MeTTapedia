import Mathlib.Order.ULift
import Mettapedia.Logic.HOL.ParamWorld
import Mettapedia.Logic.HOL.Semantics.HeytingHenkin

namespace Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-!
# Growing-World Semantic Carrier  [MAINLINE]

This file begins the direct semantic packaging for the parameterized root route.
The current layer names the base-type carrier over growing worlds, without yet
committing to the full `HeytingPreModel` structure.

Positive example:
a constant symbol at base type gives a canonical section present at every world.

Negative example:
this file does not yet define the truth theorem or the final
`RootCounterworld -> HeytingHenkinModel` bridge.
-/

namespace GrowingWorld

/-- Universe-lifted truth object for the direct growing-model route.

`HeytingPreModel` expects both the truth object and the base carriers to live in
the same ambient universe `Type (max (u + 1) w)`. The raw growing-world truth
object `GrowingWorld.Ω` is smaller, so the direct route lifts it explicitly at
the semantic packaging layer.

Positive example:
the lifted truth object still carries the same Kripke/Henkin order structure as
the raw upper-set truth values.

Negative example:
this does not yet define the final premodel; it only repairs the universe level
of the truth object used by that future packaging.
-/
abbrev ModelΩ
    (Base : Type u) (Const : Ty Base → Type v) :
    Type (max (u + 1) v) :=
  ULift.{max (u + 1) v, max u v} (GrowingWorld.Ω (Base := Base) (Const := Const))

/-- Embed a raw growing-world truth value into the universe-lifted truth
object. -/
abbrev liftTruth
    (p : GrowingWorld.Ω (Base := Base) (Const := Const)) :
    ModelΩ (Base := Base) (Const := Const) :=
  ULift.up p

@[simp] theorem down_liftTruth
    (p : GrowingWorld.Ω (Base := Base) (Const := Const)) :
    (liftTruth (Base := Base) (Const := Const) p).down = p :=
  rfl

@[simp] theorem liftTruth_down
    (p : ModelΩ (Base := Base) (Const := Const)) :
    liftTruth (Base := Base) (Const := Const) p.down = p := by
  cases p
  rfl

instance : HImp (ModelΩ (Base := Base) (Const := Const)) where
  himp p q := ULift.up (p.down ⇨ q.down)

@[simp] theorem down_himp
    (p q : ModelΩ (Base := Base) (Const := Const)) :
    (p ⇨ q).down = (p.down ⇨ q.down) :=
  rfl

noncomputable instance : Order.Frame (ModelΩ (Base := Base) (Const := Const)) := by
  let _ : Order.Frame (GrowingWorld.Ω (Base := Base) (Const := Const)) := inferInstance
  refine Order.Frame.mk ?_ ?_
  · intro a b c
    change a.down ≤ b.down ⇨ c.down ↔ a.down ⊓ b.down ≤ c.down
    exact (le_himp_iff (a := a.down) (b := b.down) (c := c.down))
  · intro a
    apply ULift.down_injective
    simp

/-- A supported future-local base-type individual for the growing-domain route.

Instead of requiring a single global section defined at every world, a base
section is only required on an upward-closed support of worlds. This is the
right carrier shape for growing domains: a local parameter term born at some
future world should become available above that world without forcing an
artificial root-world value.

Positive example:
an original base constant gives a section supported at all worlds.

Negative example:
this file still does not package the full `HeytingPreModel`; it only repairs
the carrier layer so future local inhabitants are representable.
-/
structure BaseSection
    (Base : Type u) (Const : Ty Base → Type v)
    (b : Base) : Type (max (u + 1) v) where
  support : UpperSet (GrowingWorld Base Const)
  termAt :
    ∀ {W : GrowingWorld Base Const},
      W ∈ support →
        ClosedTerm (ParamConst Const W.ctx) (.base b)

/-- The principal future of a world inside the growing frame. -/
def principalSupport
    (W : GrowingWorld Base Const) :
    UpperSet (GrowingWorld Base Const) :=
  ⟨{V | W ≤ V}, by
    intro U V hUV hWU
    exact le_trans hWU hUV
  ⟩

@[simp] theorem mem_principalSupport
    {U V : GrowingWorld Base Const} :
    V ∈ principalSupport (Base := Base) (Const := Const) U ↔ U ≤ V :=
  Iff.rfl

/-- A local closed base term defines a supported section on its honest future.

Positive example:
the fresh parameter constant at a one-step extension yields a base section
supported exactly above that extension world.

Negative example:
this constructor does not yet prove any recursive coherence theorem beyond the
transport built into `transportClosedTerm`.
-/
noncomputable def localSection
    {b : Base}
    (W : GrowingWorld Base Const)
    (t : ClosedTerm (ParamConst Const W.ctx) (.base b)) :
    BaseSection Base Const b where
  support := principalSupport (Base := Base) (Const := Const) W
  termAt hV := transportClosedTerm (Base := Base) (Const := Const) hV t

/-- The fresh head parameter at a base-typed one-step extension yields a
supported base section.

Positive example:
this is the simplest future-local inhabitant that the old global-section
carrier could not represent at all.

Negative example:
this only handles the distinguished newest parameter, not arbitrary local
closed terms.
-/
noncomputable def freshParamSection
    {Γ : Ctx Base} {b : Base}
    (W : PrimeTheory Const (.base b :: Γ)) :
    BaseSection Base Const b :=
  localSection
    (Base := Base)
    (Const := Const)
    ⟨.base b :: Γ, W⟩
    (.const (ParamConst.param (.vz : Var (.base b :: Γ) (.base b))))

theorem nonempty_baseSection_of_param_world
    {Γ : Ctx Base} {b : Base}
    (W : PrimeTheory Const (.base b :: Γ)) :
    Nonempty (BaseSection Base Const b) :=
  ⟨freshParamSection (Base := Base) (Const := Const) W⟩

/-- Truth value of worldwise availability for a supported base section.

This packages `support` as an `Ω`-truth value using the same order convention
as the growing-world truth object.
-/
def supportTruth
    {b : Base}
    (x : BaseSection Base Const b) :
    GrowingWorld.Ω (Base := Base) (Const := Const) :=
  OrderDual.ofDual x.support

/-- Universe-lifted availability truth for supported base sections. -/
def baseAvailability
    {b : Base}
    (x : BaseSection Base Const b) :
    ModelΩ (Base := Base) (Const := Const) :=
  liftTruth (Base := Base) (Const := Const)
    (supportTruth (Base := Base) (Const := Const) x)

@[simp] theorem down_baseAvailability
    {b : Base}
    (x : BaseSection Base Const b) :
    (baseAvailability x).down = supportTruth x :=
  rfl

/-- Transporting an original base constant across a context equality is trivial.

Positive example:
if `Δ = Γ`, the same original constant denotes the same closed term on both
parameterized signatures.

Negative example:
this does not yet transport arbitrary local parameter constants, whose indices
do depend on the context.
-/
lemma cast_closedTerm_const_base
    {Γ Δ : Ctx Base} {b : Base}
    (h : Δ = Γ) (c : Const (.base b)) :
    cast (by cases h; rfl) (.const (Sum.inl c) : ClosedTerm (ParamConst Const Γ) (.base b)) =
      (.const (ParamConst.base c) : ClosedTerm (ParamConst Const Δ) (.base b)) := by
  cases h
  rfl

/-- The constant section generated by an original base constant.

Positive example:
the denotation of an original individual constant should be world-invariant in
the direct growing model.

Negative example:
this only applies to constants of base type, not arbitrary higher-order
constants.
-/
noncomputable def constSection
    {b : Base}
    (c : Const (.base b)) :
    BaseSection Base Const b where
  support := ⊤
  termAt _ := .const (ParamConst.base c)

@[simp] theorem constSection_termAt
    {b : Base}
    (c : Const (.base b))
    {W : GrowingWorld Base Const}
    (hW : W ∈ (constSection (Base := Base) (Const := Const) c).support) :
    (constSection (Base := Base) (Const := Const) c).termAt hW =
      .const (ParamConst.base c) :=
  rfl

@[simp] theorem supportTruth_constSection
    {b : Base}
    (c : Const (.base b)) :
    supportTruth (constSection c) =
        OrderDual.ofDual
          (⊤ : UpperSet (GrowingWorld Base Const)) := by
  rfl

@[simp] theorem supportTruth_freshParamSection
    {Γ : Ctx Base} {b : Base}
    (W : PrimeTheory Const (.base b :: Γ)) :
    supportTruth (freshParamSection W) =
        OrderDual.ofDual
          (principalSupport ⟨.base b :: Γ, W⟩) := by
  rfl

/-- The local equality formula comparing two supported base sections at a world
where both are available. -/
def eqFormulaAt
    {b : Base}
    (x y : BaseSection Base Const b)
    {W : GrowingWorld Base Const}
    (hx : W ∈ x.support)
    (hy : W ∈ y.support) :
    ClosedFormula (ParamConst Const W.ctx) :=
  .eq (x.termAt hx) (y.termAt hy)

@[simp] theorem eqFormulaAt_constSection
    {b : Base}
    (c d : Const (.base b))
    {W : GrowingWorld Base Const}
    (hc : W ∈ (constSection (Base := Base) (Const := Const) c).support)
    (hd : W ∈ (constSection (Base := Base) (Const := Const) d).support) :
    eqFormulaAt (Base := Base) (Const := Const)
        (constSection (Base := Base) (Const := Const) c)
        (constSection (Base := Base) (Const := Const) d)
        hc
        hd =
      .eq (.const (ParamConst.base c)) (.const (ParamConst.base d)) :=
  rfl

/-- Equality reflexivity is always present in a prime-theory world. -/
theorem eq_refl_mem_at_world
    {τ : Ty Base}
    (W : GrowingWorld Base Const)
    (t : ClosedTerm (ParamConst Const W.ctx) τ) :
    (.eq t t : ClosedFormula (ParamConst Const W.ctx)) ∈ W.theory.carrier := by
  exact W.theory.closed <|
    ClosedTheorySet.provable_of_closedTheory
      (Const := ParamConst Const W.ctx)
      (T := W.theory.carrier)
      (Δ := [])
      (hΔ := by
        intro ψ hψ
        cases hψ)
      (.eqRefl t)

/-- Equality symmetry is closed in every prime-theory world. -/
theorem eq_symm_mem_at_world
    {τ : Ty Base}
    {W : GrowingWorld Base Const}
    {t u : ClosedTerm (ParamConst Const W.ctx) τ}
    (h : (.eq t u : ClosedFormula (ParamConst Const W.ctx)) ∈ W.theory.carrier) :
    (.eq u t : ClosedFormula (ParamConst Const W.ctx)) ∈ W.theory.carrier := by
  have hProv : ClosedTheorySet.Provable
      (Const := ParamConst Const W.ctx)
      W.theory.carrier
      (.eq u t : ClosedFormula (ParamConst Const W.ctx)) := by
    rcases ClosedTheorySet.provable_of_mem
      (Const := ParamConst Const W.ctx)
      (T := W.theory.carrier)
      h with ⟨support, hSup, d⟩
    exact ⟨support, hSup, .eqSymm d⟩
  exact W.theory.closed hProv

/-- Equality transitivity is closed in every prime-theory world. -/
theorem eq_trans_mem_at_world
    {τ : Ty Base}
    {W : GrowingWorld Base Const}
    {t u v : ClosedTerm (ParamConst Const W.ctx) τ}
    (htu : (.eq t u : ClosedFormula (ParamConst Const W.ctx)) ∈ W.theory.carrier)
    (huv : (.eq u v : ClosedFormula (ParamConst Const W.ctx)) ∈ W.theory.carrier) :
    (.eq t v : ClosedFormula (ParamConst Const W.ctx)) ∈ W.theory.carrier := by
  have hProv : ClosedTheorySet.Provable
      (Const := ParamConst Const W.ctx)
      W.theory.carrier
      (.eq t v : ClosedFormula (ParamConst Const W.ctx)) := by
    rcases ClosedTheorySet.provable_of_mem
      (Const := ParamConst Const W.ctx)
      (T := W.theory.carrier)
      htu with ⟨support₁, hSup₁, d₁⟩
    rcases ClosedTheorySet.provable_of_mem
      (Const := ParamConst Const W.ctx)
      (T := W.theory.carrier)
      huv with ⟨support₂, hSup₂, d₂⟩
    exact ⟨support₁ ++ support₂, by
      intro φ hφ
      rcases List.mem_append.mp hφ with hφ | hφ
      · exact hSup₁ φ hφ
      · exact hSup₂ φ hφ,
      .eqTrans
        (ExtDerivation.mono
          (Δ := support₁)
          (Δ' := support₁ ++ support₂)
          (φ := .eq t u)
          (by
            intro ξ hξ
            exact List.mem_append.mpr (.inl hξ))
          d₁)
        (ExtDerivation.mono
          (Δ := support₂)
          (Δ' := support₁ ++ support₂)
          (φ := .eq u v)
          (by
            intro ξ hξ
            exact List.mem_append.mpr (.inr hξ))
          d₂)⟩
  exact W.theory.closed hProv

/-- Base-equality support for supported sections.

A world belongs to `eqSupport x y` when every honest future world:
1. agrees on availability of `x` and `y`, and
2. validates their local equality formula whenever both are available.

This support-coherence strengthening is the key repair ensuring transitivity.
-/
def eqSupport
    {b : Base}
    (x y : BaseSection Base Const b) :
    UpperSet (GrowingWorld Base Const) :=
  ⟨
    {W | ∀ {V : GrowingWorld Base Const}, W ≤ V →
      (V ∈ x.support ↔ V ∈ y.support) ∧
      ∀ (hx : V ∈ x.support) (hy : V ∈ y.support),
        eqFormulaAt (Base := Base) (Const := Const) x y hx hy ∈ V.theory.carrier},
    by
      intro U V hUV hU X hVX
      exact hU (le_trans hUV hVX)
  ⟩

/-- Truth value of base equality support in the growing-world truth object. -/
def eqTruth
    {b : Base}
    (x y : BaseSection Base Const b) :
    GrowingWorld.Ω (Base := Base) (Const := Const) :=
  OrderDual.ofDual (eqSupport (Base := Base) (Const := Const) x y)

/-- Universe-lifted base equality support truth for supported sections. -/
def baseEq
    {b : Base}
    (x y : BaseSection Base Const b) :
    ModelΩ (Base := Base) (Const := Const) :=
  liftTruth (Base := Base) (Const := Const)
    (eqTruth (Base := Base) (Const := Const) x y)

@[simp] theorem down_baseEq
    {b : Base}
    (x y : BaseSection Base Const b) :
    (baseEq (Base := Base) (Const := Const) x y).down =
      eqTruth (Base := Base) (Const := Const) x y :=
  rfl

/-- Reflexive membership of supported-section equality support. -/
theorem mem_eqSupport_refl
    {b : Base}
    (x : BaseSection Base Const b)
    (W : GrowingWorld Base Const) :
    W ∈ eqSupport (Base := Base) (Const := Const) x x := by
  intro V hWV
  refine ⟨Iff.rfl, ?_⟩
  intro hx hy
  have hxy : hx = hy := Subsingleton.elim hx hy
  subst hxy
  simpa [eqFormulaAt] using
    eq_refl_mem_at_world (Base := Base) (Const := Const) V (x.termAt hx)

/-- Symmetric membership transfer for supported-section equality support. -/
theorem mem_eqSupport_symm
    {b : Base}
    {x y : BaseSection Base Const b}
    {W : GrowingWorld Base Const}
    (hxy : W ∈ eqSupport (Base := Base) (Const := Const) x y) :
    W ∈ eqSupport (Base := Base) (Const := Const) y x := by
  intro V hWV
  have hxyV := hxy hWV
  refine ⟨hxyV.1.symm, ?_⟩
  intro hy hx
  exact eq_symm_mem_at_world (Base := Base) (Const := Const)
    (h := hxyV.2 hx hy)

/-- Transitive membership transfer for supported-section equality support. -/
theorem mem_eqSupport_trans
    {b : Base}
    {x y z : BaseSection Base Const b}
    {W : GrowingWorld Base Const}
    (hxy : W ∈ eqSupport (Base := Base) (Const := Const) x y)
    (hyz : W ∈ eqSupport (Base := Base) (Const := Const) y z) :
    W ∈ eqSupport (Base := Base) (Const := Const) x z := by
  intro V hWV
  have hxyV := hxy hWV
  have hyzV := hyz hWV
  refine ⟨?_, ?_⟩
  · constructor
    · intro hx
      exact hyzV.1.mp (hxyV.1.mp hx)
    · intro hz
      exact hxyV.1.mpr (hyzV.1.mpr hz)
  · intro hx hz
    let hy : V ∈ y.support := hxyV.1.mp hx
    exact eq_trans_mem_at_world (Base := Base) (Const := Const)
      (htu := hxyV.2 hx hy)
      (huv := hyzV.2 hy hz)

end GrowingWorld

end Mettapedia.Logic.HOL
