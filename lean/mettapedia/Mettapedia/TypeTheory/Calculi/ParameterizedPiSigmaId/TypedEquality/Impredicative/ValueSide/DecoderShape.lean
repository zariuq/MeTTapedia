import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Decoding

/-!
# Codes and their decodings have one shape

The transport inspects the weak-head normal forms of types: every interpreted
type reduces to a universe, a type constant, a dependent function or pair
type, a form at which the transport returns its method (`MethodForm`), or a
term stuck on the daimon (`SInterp.typeForm`, in `InterpLaws`).

The universe relation relates types with one pack and one shape. A code and
its decoding have one pack (`decoder_coherent`); they have one shape too, for
every decoder rule (`decoder_shape`):

* `holds c` is a leaf: it reduces to a form at which the transport returns its
  method (`MethodForm`), and its pack relates every pair;
* the decoding of an implication, `Π (holds p) (holds q)`, and of a
  quantifier, `Π (x : A). holds (f x)`, are dependent function types into
  leaves over a domain of one shape with itself (`carrier_shape`), so they are
  hereditarily total, as `holds` of their code is;
* the decoding of an equation, `Id A x y`, is a leaf.

So a code interpreted at a level and its decoding are related by the universe
relation over the interpretation at that level (`decoder_related`): at every
world reached by a morphism they have one pack and one shape. This is decoder
coherence in the relation without a skeleton, at every decoder rule.

Controls: a type of one shape with a decoding is hereditarily total, so no
decoding is of one shape with a universe (`Shape.holds_not_univ`); the carrier
`num → num` is of one shape with itself by the clause of dependent function
types, not as a hereditarily total type (`numArrow_shape`); `Σ num num` is of
one shape with itself by the clause of dependent pair types
(`shape_numPair`), and the pairs of proofs `Σ (holds p) (holds q)` form a
hereditarily total type (`shape_holdsPair`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ValueSide

open Normalization
open UniverseLevel (LevelOrder)
open Consistency (Kind Carrier World Morph Truth)
open Realizability (Daimonic)

variable {Head L : Type} [LevelOrder L]

variable {V : Model Head L}

/-! ## Leaves -/

section Leaves

variable (laws : V.Laws) {l : L} {below : L → IPack V} {n : Nat} {ξ : World V.reading n}
include laws

/-- A type that reduces to a form at which the transport returns its method is
a leaf: a non-universe head, an identity type, a decoding, or a rigid spine
other than the codes and the decoder. -/
theorem Shape.of_methodForm {X w : Tm Head n} {P : Pack V n} (interp : SInterp V l below ξ X P)
    (red : WhRed V.rules V.roles X w) (form : MethodForm V w) :
    Shape V (SInterp V l below) .total ξ X X := by
  have normal := form.whnf laws
  have total : ∀ a b, P.rel a b := by
    rcases form with ⟨h, rfl, hh⟩ | ⟨A, a, b, rfl⟩ | ⟨c, rfl⟩ |
      ⟨T, args, rfl, role, notProp, notHolds⟩
    · rcases interp.head_inv laws red with ⟨hu, -⟩ | ⟨-, rfl⟩
      · exact absurd hu hh
      · exact fun _ _ => trivial
    · obtain ⟨R, rfl, -⟩ := interp.id_inv laws red
      exact fun _ _ => trivial
    · obtain ⟨X, -, rfl⟩ := interp.holds_inv laws red
      exact fun _ _ => trivial
    · rw [interp.deterministic laws (.rigid red role notProp notHolds)]
      exact fun _ _ => trivial
  refine .leaf ⟨⟨P, interp, total⟩, fun u r hu => ?_, fun c hc r => ?_, fun A B r => ?_⟩
    fun A B r => ?_
  · exact form.ne_univ hu (laws.unique red r normal (head_whnf laws.shape _))
  · exact form.ne_typeConst hc (laws.unique red r normal (hc.whnf laws))
  · exact form.ne_pi (laws.unique red r normal (pi_whnf laws.shape _ _))
  · exact form.ne_sigma (laws.unique red r normal (sigma_whnf laws.shape _ _))

/-- A type stuck on the daimon is a leaf. -/
theorem Shape.of_daimonic {X w : Tm Head n} {P : Pack V n} (interp : SInterp V l below ξ X P)
    (red : WhRed V.rules V.roles X w) (daimonic : Daimonic V.roles V.star w) :
    Shape V (SInterp V l below) .total ξ X X := by
  have normal := laws.daimonic_whnf daimonic
  have total : ∀ a b, P.rel a b := by
    rw [interp.eq_total_of_daimonic laws red daimonic]
    exact fun _ _ => trivial
  have former := laws.daimonic_not_former daimonic
  refine .leaf ⟨⟨P, interp, total⟩, fun u r _ => ?_, fun c hc r => ?_, fun A B r => ?_⟩
    fun A B r => ?_
  · exact former.1 u (laws.unique red r normal (head_whnf laws.shape _))
  · exact laws.daimonic_ne_typeConst daimonic hc (laws.unique red r normal (hc.whnf laws))
  · exact former.2.1 A B (laws.unique red r normal (pi_whnf laws.shape _ _))
  · exact former.2.2.1 A B (laws.unique red r normal (sigma_whnf laws.shape _ _))

/-- A decoding `holds c` is a leaf. -/
theorem Shape.holds {c : Tm Head n} {P : Pack V n}
    (interp : SInterp V l below ξ (.app (.const V.holds) c) P) :
    Shape V (SInterp V l below) .total ξ (.app (.const V.holds) c) (.app (.const V.holds) c) :=
  Shape.of_methodForm laws interp .refl (.inr (.inr (.inl ⟨c, rfl⟩)))

end Leaves

/-! ## Carriers -/

/-- **An interpretable carrier, read as a type, is of one shape with itself**:
the codes and the numbers by their constants, a rigid base type as a leaf, and
a function carrier by the clause of dependent function types, componentwise. -/
theorem carrier_shape (laws : V.Laws) {l : L} {below : L → IPack V} :
    ∀ {k : Kind} {K : Carrier k}, K.Interpretable V.toModel → ∀ {n : Nat}
      (ξ : World V.reading n),
      Shape V (SInterp V l below) .pair ξ (liftClosed (K.term V.toModel))
        (liftClosed (K.term V.toModel))
  | _, _, .prop, _, _ => .const (.inl rfl) .refl .refl
  | _, _, .num, _, _ => .const (.inr ⟨_, laws.num_role⟩) .refl .refl
  | _, _, @Consistency.Carrier.Interpretable.rigid _ _ _ _ T role notProp notHolds, _, ξ =>
      have leaf : Shape V (SInterp V l below) .total ξ (.const T) (.const T) :=
        Shape.of_methodForm laws (carrier_interp laws (.rigid role notProp notHolds) ξ) .refl
          (.inr (.inr (.inr ⟨T, [], rfl, role, notProp, notHolds⟩)))
      .total leaf leaf
  | _, _, @Consistency.Carrier.Interpretable.arr _ _ _ _ _ _ K K' dom cod, _, ξ => by
      change Shape V (SInterp V l below) .pair ξ
        (liftClosed (.pi (K.term V.toModel) (Presentation.rename wk (K'.term V.toModel))))
        (liftClosed (.pi (K.term V.toModel) (Presentation.rename wk (K'.term V.toModel))))
      rw [Consistency.liftClosed_arrow]
      refine .pi .refl .refl ?_ ?_ ?_ ?_
      · intro m ξ' ρ _
        rw [rename_liftClosed]
        exact ⟨_, _, carrier_interp laws dom ξ', carrier_interp laws dom ξ', rfl⟩
      · intro m ξ' ρ _
        rw [rename_liftClosed]
        exact carrier_shape laws dom ξ'
      · intro m ξ' ρ _ P _ a b _
        simp only [rename_liftClosed, inst0, subst_liftClosed]
        exact ⟨_, _, carrier_interp laws cod ξ', carrier_interp laws cod ξ', rfl⟩
      · intro m ξ' ρ _ P _ a b _
        simp only [rename_liftClosed, inst0, subst_liftClosed]
        exact carrier_shape laws cod ξ'

/-! ## Decodings -/

section Decodings

variable (laws : V.Laws) {D : Decoders Head} (decodes : Consistency.Decodes V.toModel D)
  {l : L} {below : L → IPack V} {n : Nat} {ξ : World V.reading n}
include laws decodes

/-- **A code and its decoding have one shape**, for every decoder rule. The
decoding of an implication, `Π (holds p) (holds q)`, and of a quantifier,
`Π (x : A). holds (f x)`, are dependent function types into leaves over a
domain of one shape with itself, so they are hereditarily total, as is `holds`
of their code; the decoding of an equation, `Id A x y`, is a leaf. -/
theorem decoder_shape {x y : Tm Head n} (step : DecoderStep D x y) {P₁ P₂ : Pack V n}
    (hx : SInterp V l below ξ x P₁) (hy : SInterp V l below ξ y P₂) :
    Shape V (SInterp V l below) .pair ξ x y := by
  cases step with
  | imp p q =>
      rw [decodes.holds, decodes.imp] at hx ⊢
      rw [decodes.holds] at hy
      obtain ⟨Q, rfl, iQ⟩ := hy.pi_inv laws .refl
      refine .total (Shape.holds laws hx) (.totalPi .refl ⟨_, hy⟩ (fun {_ _ ρ} w => ?_)
        (fun {_ _ _} w {P} hP {a} ha => ?_))
      · have leaf := Shape.of_methodForm laws (iQ.dom w) .refl
          (.inr (.inr (.inl ⟨Presentation.rename ρ p, rfl⟩)))
        exact .total leaf leaf
      · obtain rfl := hP.deterministic laws (iQ.dom w)
        exact Shape.of_methodForm laws (iQ.cod w ha) .refl (.inr (.inr (.inl ⟨_, rfl⟩)))
  | all carrier f =>
      obtain ⟨_, C, -, hC, rfl⟩ := decodes.all carrier
      rw [decodes.holds] at hx hy ⊢
      obtain ⟨Q, rfl, iQ⟩ := hy.pi_inv laws .refl
      refine .total (Shape.holds laws hx) (.totalPi .refl ⟨_, hy⟩ (fun {_ ξ' _} _ => ?_)
        (fun {_ _ _} w {P} hP {a} ha => ?_))
      · rw [rename_liftClosed]
        exact carrier_shape laws hC ξ'
      · obtain rfl := hP.deterministic laws (iQ.dom w)
        exact Shape.of_methodForm laws (iQ.cod w ha) .refl (.inr (.inr (.inl ⟨_, rfl⟩)))
  | eq carrier a b =>
      obtain ⟨_, C, -, hC, rfl⟩ := decodes.eq carrier
      rw [decodes.holds] at hx ⊢
      exact .total (Shape.holds laws hx)
        (Shape.of_methodForm laws hy .refl (.inr (.inl ⟨_, _, _, rfl⟩)))

/-- **Decoder coherence in the universe relation.** A code interpreted at a
level and its decoding are related by the universe relation over that level's
interpretation, for every decoder rule: at every world reached by a morphism
they have one pack and one shape. -/
theorem decoder_related {x y : Tm Head n} (step : DecoderStep D x y) {P : Pack V n}
    (hx : SInterp V l below ξ x P) : (universePack V (SInterp V l below) ξ).rel x y :=
  fun {_ _ ρ} w => by
    obtain ⟨P', hx', -⟩ := hx.rename laws w
    have step' := step.rename ρ
    have hy' := decoder_interp laws decodes step' hx'
    exact ⟨P', hx', hy', decoder_shape laws decodes step' hx' hy'⟩

end Decodings

/-! ## Controls -/

/-- A type of one shape with a decoding is hereditarily total. -/
theorem Shape.total_of_holds_left (laws : V.Laws) {I : IPack V} {n : Nat}
    {ξ : World V.reading n} {c X : Tm Head n}
    (d : Shape V I .pair ξ (.app (.const V.holds) c) X) : Shape V I .total ξ X X := by
  have normal := laws.values.whnf_holds c
  cases d with
  | total _ right => exact right
  | univ red => cases whRed_of_whnf normal red
  | const _ red => cases whRed_of_whnf normal red
  | pi red => cases whRed_of_whnf normal red
  | sigma red => cases whRed_of_whnf normal red

/-- **No decoding is of one shape with a universe**, over any interpretation: a
type of one shape with a decoding is hereditarily total, and no universe is. So
the universe relation never relates a code's decoding to a universe. -/
theorem Shape.holds_not_univ (laws : V.Laws) {I : IPack V} {n : Nat} {ξ : World V.reading n}
    {c : Tm Head n} {u : Head} (hu : V.rules.isUniverse u) :
    ¬ Shape V I .pair ξ (.app (.const V.holds) c) (.head u) := fun d =>
  (d.total_of_holds_left laws).total_not_head laws .refl hu

/-- **The carrier `num → num` is of one shape with itself by the clause of
dependent function types, not as a hereditarily total type**: at the valid
argument `⋆` its codomain is the numbers, a type constant. So `carrier_shape`
exercises the clause at which the transport compares domains. -/
theorem numArrow_shape (laws : V.Laws) {l : L} {below : L → IPack V} {n : Nat}
    (ξ : World V.reading n) :
    Shape V (SInterp V l below) .pair ξ (.pi (.const V.num) (.const V.num))
        (.pi (.const V.num) (.const V.num)) ∧
      ¬ Shape V (SInterp V l below) .total ξ (.pi (.const V.num) (.const V.num))
        (.pi (.const V.num) (.const V.num)) := by
  refine ⟨carrier_shape laws (K := .arr .num .num) (.arr .num .num) ξ, fun t => ?_⟩
  have parts := t.total_pi laws .refl
  have num : SInterp V l below ξ (Presentation.rename idRen (.const V.num)) (numIndPack V n) :=
    carrier_interp laws .num ξ
  exact (parts.codShape (Morph.id ξ) num (a := .const V.star)
    (.star .refl .star .refl .star)).total_not_const laws (.inr ⟨_, laws.num_role⟩) .refl

section Pairs

variable {l : L} {below : L → IPack V} {n : Nat}

/-- `Σ num num` is interpreted by the pack of pairs of numbers. -/
theorem interp_numPair (laws : V.Laws) (ξ : World V.reading n) :
    SInterp V l below ξ (.sigma (.const V.num) (.const V.num))
      (PiPack.arrow ξ (fun {m} _ => numIndPack V m) (fun {m} _ => numIndPack V m)).sigmaPack :=
  SInterp.sigma .refl _ (fun {_ _ _} _ => SInterp.num laws .refl)
    (fun {_ _ _} _ {_} _ => SInterp.num laws .refl) (fun {_ _ _} _ {_ _} _ _ _ => rfl)

/-- **`Σ num num` is of one shape with itself** by the clause of dependent pair
types: its domains and its codomains are the numbers. -/
theorem shape_numPair (laws : V.Laws) (ξ : World V.reading n) :
    Shape V (SInterp V l below) .pair ξ (.sigma (.const V.num) (.const V.num))
      (.sigma (.const V.num) (.const V.num)) :=
  .sigma .refl .refl ⟨_, _, SInterp.num laws .refl, SInterp.num laws .refl, rfl⟩
    (.const (.inr ⟨_, laws.num_role⟩) .refl .refl)
    (fun {_} _ {_ _} _ => ⟨_, _, SInterp.num laws .refl, SInterp.num laws .refl, rfl⟩)
    (fun {_} _ {_ _} _ => .const (.inr ⟨_, laws.num_role⟩) .refl .refl)

/-- The pair type `Σ (holds p) (holds q)` of two codes with meanings `X` and `Y`
is interpreted by the pack of pairs of the two proof packs. -/
theorem interp_holdsPair {ξ : World V.reading n} {p q : Tm Head n} {X Y : V.alg.Cand}
    (hp : Truth V.reading ξ p X) (hq : Truth V.reading ξ q Y) :
    SInterp V l below ξ (.sigma (.app (.const V.holds) p)
        (.app (.const V.holds) (Presentation.rename wk q)))
      (PiPack.arrow ξ (fun {m} _ => holdsPack V m X) (fun {m} _ => holdsPack V m Y)).sigmaPack :=
  SInterp.sigma .refl _ (fun {_ _ _} w => SInterp.holds .refl (hp.rename w))
    (fun {_ _ ρ} w {a} _ => by
      change SInterp V l below _ (.app (.const V.holds)
        (inst0 a (Presentation.rename (liftRen ρ) (Presentation.rename wk q)))) _
      rw [rename_liftRen_wk, inst0_rename_wk]
      exact SInterp.holds .refl (hq.rename w))
    (fun {_ _ _} _ {_ _} _ _ _ => rfl)

/-- **`Σ (holds p) (holds q)` is a hereditarily total dependent pair type**: a
pair of leaves. -/
theorem shape_holdsPair (laws : V.Laws) {ξ : World V.reading n} {p q : Tm Head n}
    {X Y : V.alg.Cand} (hp : Truth V.reading ξ p X) (hq : Truth V.reading ξ q Y) :
    Shape V (SInterp V l below) .total ξ (.sigma (.app (.const V.holds) p)
        (.app (.const V.holds) (Presentation.rename wk q)))
      (.sigma (.app (.const V.holds) p) (.app (.const V.holds) (Presentation.rename wk q))) :=
  .totalSigma .refl ⟨_, interp_holdsPair hp hq⟩ (Shape.holds laws (SInterp.holds .refl hp))
    fun {_} _ {a} _ => by
      change Shape V (SInterp V l below) .total ξ
        (.app (.const V.holds) (inst0 a (Presentation.rename wk q)))
        (.app (.const V.holds) (inst0 a (Presentation.rename wk q)))
      rw [inst0_rename_wk]
      exact Shape.holds laws (SInterp.holds .refl hq)

end Pairs

end ValueSide
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
