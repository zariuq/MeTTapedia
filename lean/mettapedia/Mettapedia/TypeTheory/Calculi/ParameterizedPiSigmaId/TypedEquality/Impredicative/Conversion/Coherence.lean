import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Laws
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.DecoderShape

/-!
# Decoder coherence in the conversion model

A code and its decoding are read alike on both sides of the conversion model.

**Value side.** The value side is generic over its realizer algebra, and its
decoder coherence reads realizers only through the laws of the algebra:
Girard's clause of a constant domain and codomain over a nonempty index is the
function space (C1), Girard's clause over the valid arguments of a carrier's pack
is Girard's clause over the carrier's meanings (C2), and the identity candidate
reads its proposition up to equivalence (C3). The algebra of equality candidates
has these laws, so at the value model of the conversion model, for every decoder
rule, a code interpreted at a level and its decoding have one pack, and they are
related by the universe relation at that level: one pack and one shape at every
world reached by a morphism (`NInterp.decoder_coherent`,
`NInterp.decoder_related`). The decodings are interpreted by the proof packs of
the codes' meanings (`NInterp.holds_imp`, `NInterp.holds_all`,
`NInterp.id_carrier`).

**Realizer side.** Every candidate reads its realizer type through the type's
typed weak-head reducts (`ECand.redTy`). So when the realizer side decodes a
code, every candidate reads the code's decoder spine as it reads the decoding
(`ECand.decoding`), and at the three decoder rules the meaning of a code reads,
at the realizer type `holds c`, the clause of the decoding:

* C1: at `holds (imp p q)`, the function space: functions whose applications
  to arguments related at `holds p` are related at `holds q`
  (`arrow_holds_imp`);
* C2: at `holds (a f)`, for a quantifier `a` over a closed carrier `A`, Girard's
  clause: functions whose applications, at every index, to arguments related at
  `A` are related at `holds (f s)` (`piOver_holds_all`);
* C3: at `holds (e x y)`, for an equation `e` at a closed carrier `A`, the
  identity clause of `Id A x y`: reflexivity proofs related by `E` when the
  proposition holds, and terms reaching neutral terms (`ident_holds_eq`).

Together: a code and its decoding have one pack, and the realizers of each value
of it relate the same terms at the code's decoder spine as at its decoding
(`NInterp.decoder_coherent_realizers`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Conversion

open Normalization
open UniverseLevel (LevelOrder)
open Consistency (Kind Carrier World Truth Read)

variable {Head L : Type} [LevelOrder L]

/-! ## The value side -/

section Values

variable {M : NModel Head L} (laws : M.Laws) {l : L} {n : Nat} {ξ : World M.reading n}
include laws

/-- **C1 on the value side**: the decoding of an implication is interpreted by
the proof pack of the function space of the two meanings. -/
theorem NInterp.holds_imp {p q : Tm Head n} {X Y : ECand M.side} (hp : Truth M.reading ξ p X)
    (hq : Truth M.reading ξ q Y) :
    NInterp M l ξ
      (.pi (.app (.const M.holds) p) (.app (.const M.holds) (Presentation.rename wk q)))
      (ValueSide.holdsPack M.value n ((ecandAlgebra M.side).arrow X Y)) :=
  ValueSide.interp_holds_imp laws.value hp hq

/-- **C2 on the value side**: the decoding of a quantifier over an interpretable
carrier is interpreted by the proof pack of Girard's clause over the meanings of
the carrier. -/
theorem NInterp.holds_all {k : Kind} {K : Carrier k} (hK : K.Interpretable M.toModel)
    {f : Tm Head n} {φ : K.V M.reading → ECand M.side}
    (read : Read M.reading ξ f (.arr K .prop) φ) :
    NInterp M l ξ (.pi (liftClosed (K.term M.toModel))
        (.app (.const M.holds) (.app (Presentation.rename wk f) (.var 0))))
      (ValueSide.holdsPack M.value n
        (ECand.piOver ((ecandAlgebra M.side).Real M.toSetting M.star M.num K) φ)) :=
  ValueSide.interp_holds_all laws.value hK read

/-- **C3 on the value side**: the decoding of an equation over an interpretable
carrier is interpreted by the proof pack of the identity candidate of the
equality of the endpoints' meanings. -/
theorem NInterp.id_carrier {k : Kind} {K : Carrier k} (hK : K.Interpretable M.toModel)
    {x y : Tm Head n} {v w : K.V M.reading} (rx : Read M.reading ξ x K v)
    (ry : Read M.reading ξ y K w) :
    NInterp M l ξ (.id (liftClosed (K.term M.toModel)) x y)
      (ValueSide.holdsPack M.value n (ECand.ident M.side (v = w))) :=
  ValueSide.interp_id_carrier laws.value hK rx ry

variable {D : Decoders Head} (decodes : Consistency.Decodes M.toModel D)
include decodes

/-- The decoding of an interpreted code is interpreted by the pack of the code. -/
theorem NInterp.decoder_interp {x y : Tm Head n} (step : DecoderStep D x y) {P : NPack M n}
    (hx : NInterp M l ξ x P) : NInterp M l ξ y P :=
  ValueSide.decoder_interp laws.value decodes step hx

/-- **A code and its decoding have one pack wherever both are interpreted at a
level**, for every decoder rule. -/
theorem NInterp.decoder_coherent {x y : Tm Head n} (step : DecoderStep D x y)
    {P₁ P₂ : NPack M n} (hx : NInterp M l ξ x P₁) (hy : NInterp M l ξ y P₂) :
    P₁ = P₂ :=
  ValueSide.decoder_coherent laws.value decodes step hx hy

/-- **A code interpreted at a level and its decoding are related in the universe
relation at that level**: at every world reached by a morphism they have one pack
and one shape. -/
theorem NInterp.decoder_related {x y : Tm Head n} (step : DecoderStep D x y) {P : NPack M n}
    (hx : NInterp M l ξ x P) : (ValueSide.universePack M.value (NInterp M l) ξ).rel x y :=
  ValueSide.decoder_related laws.value decodes step hx

end Values

/-! ## The realizer side -/

/-- The codomain of a decoding under a renaming, at an argument. -/
theorem inst0_holds_rename_wk {m k : Nat} (h : DeclName) (s : Tm Head k) (ρ : Ren m k)
    (q : Tm Head m) :
    inst0 s (Presentation.rename (liftRen ρ) (.app (.const h) (Presentation.rename wk q))) =
      .app (.const h) (Presentation.rename ρ q) := by
  change Tm.app (.const h)
    (inst0 s (Presentation.rename (liftRen ρ) (Presentation.rename wk q))) = _
  rw [rename_liftRen_wk, inst0_rename_wk]

/-- The codomain of a quantifier's decoding under a renaming, at an argument. -/
theorem inst0_holds_app_rename_wk {m k : Nat} (h : DeclName) (s : Tm Head k) (ρ : Ren m k)
    (f : Tm Head m) :
    inst0 s (Presentation.rename (liftRen ρ)
        (.app (.const h) (.app (Presentation.rename wk f) (.var 0)))) =
      .app (.const h) (.app (Presentation.rename ρ f) s) := by
  change Tm.app (.const h) (Tm.app (inst0 s (Presentation.rename (liftRen ρ)
    (Presentation.rename wk f))) s) = _
  rw [rename_liftRen_wk, inst0_rename_wk]

section Realizers

variable {T : RealizerSide Head L} {D : Decoders Head}
  (decodes : ∀ {n : Nat} {x y : Tm Head n}, DecoderStep D x y → T.R.computation.step x y)
  {m : Nat} {Δ : Ctx Head m}
include decodes

/-- A decoding step between two types typed at one universe is a typed
reduction of types. -/
theorem decoding_redTy {x y : Tm Head m} (step : DecoderStep D x y) {u : Head}
    (hu : T.R.isUniverse u) (hx : Typed T.R Δ x (.head u)) (hy : Typed T.R Δ y (.head u)) :
    RedTy T.R T.roles Δ x y :=
  (RedTm.root (roles := T.roles) (decodes step) hx hy).toRedTy hu

/-- **Every candidate reads a decoder spine as it reads the decoding**, in a
formed context, when both are typed at one universe. -/
theorem ECand.decoding (X : ECand T) (formed : CtxFormed T.R Δ) {x y : Tm Head m}
    (step : DecoderStep D x y) {u : Head} (hu : T.R.isUniverse u)
    (hx : Typed T.R Δ x (.head u)) (hy : Typed T.R Δ y (.head u)) :
    X.rel Δ x = X.rel Δ y :=
  X.redTy formed (decoding_redTy decodes step hu hx hy)

/-- **C1 on the realizer side.** At the realizer type `holds (imp p q)`, the
function space from `X` to `Y` relates the terms reaching weak-head normal
functions, related by `E`, whose applications, after every renaming into a
formed context, to arguments related by `X` at `holds p` are related by `Y` at
`holds q`. -/
theorem arrow_holds_imp (X Y : ECand T) {p q : Tm Head m} {u : Head} (hu : T.R.isUniverse u)
    (hx : Typed T.R Δ (.app (.const D.holds) (.app (.app (.const D.imp) p) q)) (.head u))
    (hy : Typed T.R Δ (.pi (.app (.const D.holds) p)
      (.app (.const D.holds) (Presentation.rename wk q))) (.head u)) {t t' : Tm Head m} :
    ((ecandAlgebra T).arrow X Y).rel Δ (.app (.const D.holds) (.app (.app (.const D.imp) p) q))
        t t' ↔
      FunNf T Δ (.app (.const D.holds) (.app (.app (.const D.imp) p) q)) t ∧
        FunNf T Δ (.app (.const D.holds) (.app (.app (.const D.imp) p) q)) t' ∧
        T.E.convTm Δ t t' (.app (.const D.holds) (.app (.app (.const D.imp) p) q)) ∧
        ∀ {k : Nat} {Θ : Ctx Head k} {ρ : Ren m k}, CtxRen Δ Θ ρ → CtxFormed T.R Θ →
          ∀ {s s' : Tm Head k},
            X.rel Θ (.app (.const D.holds) (Presentation.rename ρ p)) s s' →
            Y.rel Θ (.app (.const D.holds) (Presentation.rename ρ q))
              (.app (Presentation.rename ρ t) s) (.app (Presentation.rename ρ t') s') := by
  refine (ECand.piOver_rel_pi (d := fun _ : Unit => X) (c := fun _ => Y)
    (decoding_redTy decodes (.imp p q) hu hx hy)).trans ⟨?_, ?_⟩
  · rintro ⟨fn, fn', cv, app⟩
    refine ⟨fn, fn', cv, fun ren formed s s' hs => ?_⟩
    have h := app () ⟨ren, formed⟩ hs
    rwa [inst0_holds_rename_wk] at h
  · rintro ⟨fn, fn', cv, app⟩
    refine ⟨fn, fn', cv, fun _ => ?_⟩
    intro k Θ ρ world s s' hs
    rw [inst0_holds_rename_wk]
    exact app world.1 world.2 hs

/-- **C2 on the realizer side.** At the realizer type `holds (a f)`, for a
quantifier `a` over a closed carrier `A`, Girard's clause over an index relates
the terms reaching weak-head normal functions, related by `E`, whose
applications, at every index, after every renaming into a formed context, to
arguments related at `A` by the index's domain candidate are related at
`holds (f s)` by its codomain candidate. -/
theorem piOver_holds_all {ι : Type} (d c : ι → ECand T) {a : DeclName} {A : Tm Head 0}
    (carrier : D.allCarrier a = some A) {f : Tm Head m} {u : Head} (hu : T.R.isUniverse u)
    (hx : Typed T.R Δ (.app (.const D.holds) (.app (.const a) f)) (.head u))
    (hy : Typed T.R Δ (.pi (liftClosed A)
      (.app (.const D.holds) (.app (Presentation.rename wk f) (.var 0)))) (.head u))
    {t t' : Tm Head m} :
    (ECand.piOver d c).rel Δ (.app (.const D.holds) (.app (.const a) f)) t t' ↔
      FunNf T Δ (.app (.const D.holds) (.app (.const a) f)) t ∧
        FunNf T Δ (.app (.const D.holds) (.app (.const a) f)) t' ∧
        T.E.convTm Δ t t' (.app (.const D.holds) (.app (.const a) f)) ∧
        ∀ (i : ι) {k : Nat} {Θ : Ctx Head k} {ρ : Ren m k}, CtxRen Δ Θ ρ →
          CtxFormed T.R Θ →
          ∀ {s s' : Tm Head k}, (d i).rel Θ (liftClosed A) s s' →
            (c i).rel Θ (.app (.const D.holds) (.app (Presentation.rename ρ f) s))
              (.app (Presentation.rename ρ t) s) (.app (Presentation.rename ρ t') s') := by
  refine (ECand.piOver_rel_pi (d := d) (c := c)
    (decoding_redTy decodes (.all carrier f) hu hx hy)).trans ⟨?_, ?_⟩
  · rintro ⟨fn, fn', cv, app⟩
    refine ⟨fn, fn', cv, fun i {k Θ ρ} ren formed s s' hs => ?_⟩
    have hs' : (d i).rel Θ (Presentation.rename ρ (liftClosed A)) s s' := by
      rwa [rename_liftClosed]
    have h := app i ⟨ren, formed⟩ hs'
    rwa [inst0_holds_app_rename_wk] at h
  · rintro ⟨fn, fn', cv, app⟩
    refine ⟨fn, fn', cv, fun i => ?_⟩
    intro k Θ ρ world s s' hs
    rw [rename_liftClosed] at hs
    rw [inst0_holds_app_rename_wk]
    exact app i world.1 world.2 hs

/-- **C3 on the realizer side.** At the realizer type `holds (e x y)`, for an
equation `e` at a closed carrier `A`, the identity candidate of a proposition
`P` relates the terms reaching reflexivity proofs, related by `E`, when `P`
holds, and the terms reaching neutral terms that `E` compares. -/
theorem ident_holds_eq (P : Prop) {e : DeclName} {A : Tm Head 0}
    (carrier : D.eqCarrier e = some A) {x y : Tm Head m} {u : Head} (hu : T.R.isUniverse u)
    (hx : Typed T.R Δ (.app (.const D.holds) (.app (.app (.const e) x) y)) (.head u))
    (hy : Typed T.R Δ (.id (liftClosed A) x y) (.head u)) {t t' : Tm Head m} :
    (ECand.ident T P).rel Δ (.app (.const D.holds) (.app (.app (.const e) x) y)) t t' ↔
      NeRel T Δ (.app (.const D.holds) (.app (.app (.const e) x) y)) t t' ∨
        (ReflNf T Δ (.app (.const D.holds) (.app (.app (.const e) x) y)) t ∧
          ReflNf T Δ (.app (.const D.holds) (.app (.app (.const e) x) y)) t' ∧
          T.E.convTm Δ t t' (.app (.const D.holds) (.app (.app (.const e) x) y)) ∧ P) :=
  or_congr Iff.rfl
    ⟨fun ⟨_, rest⟩ => rest,
      fun rest => ⟨⟨_, _, _, decoding_redTy decodes (.eq carrier x y) hu hx hy⟩, rest⟩⟩

end Realizers

/-! ## Both sides -/

/-- **Decoder coherence in the conversion model.** For a decoder rule of the value
side, a code interpreted at a level and its decoding have one pack; and when the
realizer side decodes a code, every realizer of every value of that pack reads
the code's decoder spine as it reads the decoding, in a formed context, both
typed at one universe. -/
theorem NInterp.decoder_coherent_realizers {M : NModel Head L} (laws : M.Laws)
    {D : Decoders Head} (decodes : Consistency.Decodes M.toModel D) {D' : Decoders Head}
    (rdecodes : ∀ {n : Nat} {x y : Tm Head n}, DecoderStep D' x y →
      M.side.R.computation.step x y)
    {l : L} {n : Nat} {ξ : World M.reading n} {x y : Tm Head n} (step : DecoderStep D x y)
    {P₁ P₂ : NPack M n} (hx : NInterp M l ξ x P₁) (hy : NInterp M l ξ y P₂) {m : Nat}
    {Δ : Ctx Head m} (formed : CtxFormed M.side.R Δ) {x' y' : Tm Head m}
    (step' : DecoderStep D' x' y') {u : Head} (hu : M.side.R.isUniverse u)
    (hx' : Typed M.side.R Δ x' (.head u)) (hy' : Typed M.side.R Δ y' (.head u)) :
    P₁ = P₂ ∧ ∀ a : Tm Head n, (P₁.real a).rel Δ x' = (P₂.real a).rel Δ y' := by
  obtain rfl := NInterp.decoder_coherent laws decodes step hx hy
  exact ⟨rfl, fun a => (P₁.real a).decoding rdecodes formed step' hu hx' hy'⟩

end Conversion
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
