import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.Model
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueModel
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Coherence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Controls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Algorithmic

/-!
# The conversion model of the executable package

The executable package without codes (`rules`) is a realizer side of the
conversion model: its generic equality, typed equality or the conversion
algorithm, has its laws, and the facts about weak-head forms of its types come
from the one-sided normalization model, whose declared constants are semantic
(`rulesSide`, `rulesAlgorithmicSide`). With the value side of the transport value
model (`tmodelC`) and its daimon it is a lawful conversion model (`nmodel`,
`nmodel_laws`); the laws do not depend on the realizer side.

The interpretation of the conversion model, read at this model:

* **numbers**: the realizer side's numbers are the value side's, so a number of
  a shape is realized by the constructor candidates of the shape, with typed
  equality and with the conversion algorithm alike (`nmodel_num_real`). The
  value `zero` is realized by `zero` at `num` (`zero_realizes_zero`), and not by
  `zero` with `suc zero` (`zero_not_realizes_suc`);
* **universes**: the lowest universe is interpreted at level one by its universe
  pack, and at level zero by none (`U0_interp`, `U0_not_interp_zero`); the
  values of the pack are realized by the types, and the type of numbers realizes
  itself as a value of the lowest universe (`U0_realizes_num`);
* **identity types**: `Id num 0 0` is realized by `refl 0`
  (`idZeroZero_real`); `Id num 0 1`, whose endpoints are unrelated, is realized
  by the identity candidate of a false proposition, which relates no
  reflexivity proof (`idZeroOne_not_real`);
* **the daimon**: it is a valid value of the numbers, and every variable of the
  numbers realizes it (`star_reflects`); it is a value of the lowest universe,
  while the numeral `zero`, which no clause of the interpretation reads, is not
  (`zero_not_interp`, `U0_star_not_zero`);
* **decoder coherence**: on the value side, `holds (imp ⋆ ⋆)` and its decoding
  are related in the universe relation, one pack and one shape at every world
  (`holdsImp_star_related`), while `holds (imp ⋆ ⋆)` and a universe are not
  (`holdsImp_star_not_univ`). On the realizer side, at a dependent function
  type the function space relates the identity function (`idNum_arrow`), while
  at a type variable, which reaches no dependent function type, it relates only
  terms reaching neutral terms (`arrow_at_variable`): the realizers of a code's
  meaning read the decoding only through a step reaching its former.

Controls for the refinement of the realizers of universes and codes, at this
realizer side:

* the types relate `num` at the lowest universe (positive), which `bot` does not
  relate, since `num` is no neutral term; `top` relates the identity function at
  `Π num num`, which the types do not relate (negative);
* the constructed terms relate `zero` at `num` (positive), which `bot` does not
  relate; they do not relate the identity function (negative).

So both refinements lie strictly between `bot` and `top`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Impredicative.Conversion
open Presentation.TypedEquality.Impredicative.Consistency (World Truth)
open Presentation.TypedEquality.Impredicative.Realizability (Daimonic HasShape)
open Package (U0 numT)

namespace CodeModel
namespace ConvRules

/-! ## The realizer sides and the model -/

/-- **The executable package as a realizer side**, with typed equality: the facts
about weak-head forms of its types come from the one-sided model. -/
def rulesSide (valuation : Nat → Nat) : RealizerSide Tower.Head ℕ where
  toSetting := setting valuation
  laws := laws valuation
  reduce := declarative_convTm_reduce
  facts := facts

/-- **The executable package as a realizer side with the conversion algorithm**
as its generic equality. -/
def rulesAlgorithmicSide : RealizerSide Tower.Head ℕ where
  toSetting := algorithmicSetting (setting fun _ => 0)
  laws := algorithmicSetting_laws (S := setting fun _ => 0) (laws _) (constants _) roots heads
    algebra
  reduce := algorithmic_convTm_reduce (S := setting fun _ => 0)
  facts := facts

/-- **The conversion model of the executable package**: the value side of the
transport value model, its daimon, and a realizer side. -/
def nmodel (v : Nat → Nat) (side : RealizerSide Tower.Head ℕ) : NModel Tower.Head ℕ where
  toModel := tmodelC v
  star := starN
  side := side

/-- **The conversion model of the executable package is lawful**, over every
realizer side. -/
theorem nmodel_laws (v : Nat → Nat) (side : RealizerSide Tower.Head ℕ) :
    (nmodel v side).Laws where
  values := tmodelC_laws v
  star := tmodelRoles_star
  starNotProp := by change starN ≠ propN; decide
  starNotHolds := by change starN ≠ holdsN; decide
  declared := tmodelConstructorsDeclared

/-- The realizer side of the executable package has the value side's numbers. -/
theorem rulesSide_num (v : Nat → Nat) :
    (rulesSide v).roles numN = .inductive [(zeroN, []), (sucN, [.recursive])] :=
  setting_roles_num v

/-- So does the realizer side with the conversion algorithm. -/
theorem rulesAlgorithmicSide_num :
    rulesAlgorithmicSide.roles numN = .inductive [(zeroN, []), (sucN, [.recursive])] :=
  setting_roles_num fun _ => 0

/-! ## Typings in the realizer side -/

section Typings

variable {n : Nat} {Γ : Tower.Ctx n}

theorem rules_numT_typed : Typed rules Γ numT U0 :=
  Derivable.mono (stage_sub_rules _) (numT_typed (names := [numN]) (List.mem_cons_self ..))

theorem rules_zero_typed : Typed rules Γ (.const zeroN) numT :=
  Derivable.mono (stage_sub_rules _)
    (zero_typed (names := [numN, zeroN]) (List.mem_cons_self ..)
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

theorem rules_numArrow_typed : Typed rules Γ (.pi numT numT) U0 :=
  Derivable.mono (stage_sub_rules _)
    (piT (allowed := allowedIn [numN]) (numT_typed (List.mem_cons_self ..))
      (numT_typed (List.mem_cons_self ..)))

/-- The identity function of the numbers. -/
theorem rules_idNum_typed : Typed rules Γ (.lam (.var 0)) (.pi numT numT) :=
  .lamIntro rules_numArrow_typed (LevelTower.IsUniverse.sort _) (Derivable.var 0)

end Typings

/-! ## The numbers -/

/-- **A number of a shape is realized by the constructor candidates of the
shape** in the conversion model of the executable package, over every realizer
side with the value side's numbers: typed equality and the conversion algorithm
alike. -/
theorem nmodel_num_real (v : Nat → Nat) {side : RealizerSide Tower.Head ℕ}
    (role : side.roles numN = .inductive [(zeroN, []), (sucN, [.recursive])]) {l n : Nat}
    {ξ : World (nmodel v side).reading n} {X : Tower.Tm n} {P : NPack (nmodel v side) n}
    (interp : NInterp (nmodel v side) l ξ X P)
    (red : WhRed (tmodelC v).rules (tmodelC v).roles X (.const numN)) {a : Tower.Tm n}
    {s : StrongNormalization.NumShape} (shape : HasShape (tmodelC v).toSetting starN a s)
    {m : Nat} (Δ : Tower.Ctx m) (A t t' : Tower.Tm m) :
    (P.real a).rel Δ A t t' ↔ NumShapeRel side numN zeroN sucN s Δ A t t' :=
  NInterp.num_real (nmodel_laws v side) interp red role shape Δ A t t'

/-- The numbers are interpreted at every level by their inductive pack. -/
theorem nmodel_num_interp (v : Nat → Nat) (l : Nat) {n : Nat}
    (ξ : World (nmodel v (rulesSide v)).reading n) :
    NInterp (nmodel v (rulesSide v)) l ξ numT
      (ValueSide.numIndPack (nmodel v (rulesSide v)).value n) :=
  ValueSide.InterpAt.num (nmodel_laws v _).value l .refl

/-- **The value `zero` is realized by `zero` at `num`.** -/
theorem zero_realizes_zero (v : Nat → Nat) :
    ((ValueSide.numIndPack (nmodel v (rulesSide v)).value 0).real (.const zeroN)).rel .nil numT
      (.const zeroN) (.const zeroN) := by
  have hz : Typed rules (.nil : Tower.Ctx 0) (.const zeroN) numT := rules_zero_typed
  exact (nmodel_num_real v (rulesSide_num v) (nmodel_num_interp v 0 World.closed) .refl
    (.zero .refl) .nil numT _ _).mpr
      (.inr ⟨RedTy.refl ⟨_, LevelTower.IsUniverse.sort _, rules_numT_typed⟩, .refl hz, .refl hz,
        .refl hz⟩)

/-- **The value `zero` is not realized by `zero` with `suc zero`**: `suc zero` is
a constructor spine, which reaches neither `zero` nor a neutral term. -/
theorem zero_not_realizes_suc (v : Nat → Nat) :
    ¬ ((ValueSide.numIndPack (nmodel v (rulesSide v)).value 0).real (.const zeroN)).rel .nil
      numT (.const zeroN) (.app (.const sucN) (.const zeroN)) := by
  intro h
  have ctor : (rulesSide v).roles sucN = .constructor 1 := roles_suc
  have normal : Whnf rules roles (.app (.const sucN) (.const zeroN) : Tower.Tm 0) :=
    ctorSpine_whnf (T := rulesSide v) ctor [.const zeroN]
  rcases (nmodel_num_real v (rulesSide_num v) (nmodel_num_interp v 0 World.closed) .refl
    (.zero .refl) .nil numT _ _).mp h with ne | ⟨-, -, r', -⟩
  · exact ctorSpine_not_neutral (T := rulesSide v) ctor [.const zeroN]
      (ne.right_whnf (.refl ne.typed.2) normal)
  · have e := WhRed.eq_of_whnf normal r'.red
    cases e

/-! ## Universes -/

/-- **The type of numbers realizes itself as a value of the lowest universe**, in
the universe pack of the interpretation at level zero. -/
theorem U0_realizes_num (v : Nat → Nat) (ξ : World (nmodel v (rulesSide v)).reading 0) :
    ((ValueSide.universePack (nmodel v (rulesSide v)).value
        (NInterp (nmodel v (rulesSide v)) 0) ξ).real numT).rel .nil U0 numT numT := by
  have typed : Typed rules (.nil : Tower.Ctx 0) numT U0 := rules_numT_typed
  exact ⟨⟨typed, typed, .refl typed⟩,
    ⟨numT, .refl typed, .inr (.inr (.inr (.inr (.inr ⟨numN, _, roles_num, rfl⟩))))⟩,
    ⟨numT, .refl typed, .inr (.inr (.inr (.inr (.inr ⟨numN, _, roles_num, rfl⟩))))⟩⟩

/-! ## The daimon -/

/-- **The daimon is a valid value of the numbers, and every variable of the
numbers realizes it.** -/
theorem star_reflects (v : Nat → Nat) (l : Nat) {n : Nat}
    (ξ : World (nmodel v (rulesSide v)).reading n) :
    NPack.Related (ValueSide.numIndPack (nmodel v (rulesSide v)).value n) (.const starN)
      (.const starN) (.snoc .nil numT) numT (.var 0) (.var 0) :=
  NInterp.reflect_var (nmodel_laws v _) (nmodel_num_interp v l ξ) 0 (Derivable.var 0)

/-! ## Decoder coherence on the value side -/

/-- The daimon is a neutral code with the neutral meaning. -/
theorem star_truth (v : Nat → Nat) {n : Nat} (ξ : World (nmodel v (rulesSide v)).reading n) :
    Truth (nmodel v (rulesSide v)).reading ξ (.const starN) (ECand.top (rulesSide v)) :=
  .neutral .refl .star

/-- **`holds (imp ⋆ ⋆)` and its decoding are related in the universe relation**:
at every world reached by a morphism they have one pack and one shape. -/
theorem holdsImp_star_related (v : Nat → Nat) (l : Nat) {n : Nat}
    (ξ : World (nmodel v (rulesSide v)).reading n) :
    (ValueSide.universePack (nmodel v (rulesSide v)).value (NInterp (nmodel v (rulesSide v)) l)
      ξ).rel (.app (.const holdsN) (.app (.app (.const impN) (.const starN)) (.const starN)))
      (.pi (.app (.const holdsN) (.const starN))
        (.app (.const holdsN) (Presentation.rename wk (.const starN)))) := by
  have hx : NInterp (nmodel v (rulesSide v)) l ξ
      (.app (.const holdsN) (.app (.app (.const impN) (.const starN)) (.const starN)))
      (ValueSide.holdsPack _ n
        ((ecandAlgebra (rulesSide v)).arrow (ECand.top _) (ECand.top _))) :=
    ValueSide.SInterp.holds .refl (.imp .refl (star_truth v ξ) (star_truth v ξ))
  intro m ξ' ρ w
  exact NInterp.decoder_related (nmodel_laws v _) (tprogramCodes_read v).decodes
    (.imp (D := programCodes.decoders) (.const starN) (.const starN)) hx w

/-! ## Controls: the refined realizers of universes and codes -/

section Controls

variable (v : Nat → Nat)

/-- The types relate `num` at the lowest universe. -/
theorem types_num : (ECand.types (rulesSide v)).rel .nil U0 numT numT :=
  U0_realizes_num v World.closed

/-- `bot` does not relate `num`: it is no neutral term. -/
theorem bot_not_num : ¬ (ECand.bot (rulesSide v)).rel .nil U0 numT numT := by
  rintro ⟨w, -, r, -, nw, -⟩
  have normal : Whnf rules roles (numT : Tower.Tm 0) := inductive_whnf (setting v).shape roles_num
  obtain rfl := WhRed.eq_of_whnf normal r.red
  exact nw.ne_inductive (rulesSide_num v) rfl

/-- `top` relates the identity function of the numbers to itself. -/
theorem top_idNum : (ECand.top (rulesSide v)).rel .nil (.pi numT numT) (.lam (.var 0))
    (.lam (.var 0)) :=
  ⟨rules_idNum_typed, rules_idNum_typed, .refl rules_idNum_typed⟩

omit v in
/-- The identity function reaches only itself, a weak-head normal λ. -/
theorem idNum_reaches {B w : Tower.Tm 0} (r : RedTm rules roles .nil (.lam (.var 0)) w B) :
    w = .lam (.var 0) :=
  WhRed.eq_of_whnf (lam_whnf (setting fun _ => 0).shape (.var 0)) r.red

/-- **The types do not relate the identity function**: it reaches no type form. -/
theorem types_not_idNum : ¬ (ECand.types (rulesSide v)).rel .nil (.pi numT numT)
    (.lam (.var 0)) (.lam (.var 0)) := by
  rintro ⟨-, ⟨w, r, form⟩, -⟩
  obtain rfl := idNum_reaches r
  rcases form with ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, e⟩ | neutral |
    ⟨_, _, _, e⟩
  · cases e
  · cases e
  · cases e
  · cases e
  · exact neutral.ne_lam rfl
  · cases e

/-- The constructed terms relate `zero` at `num`. -/
theorem constructed_zero : (ECand.constructed (rulesSide v)).rel .nil numT (.const zeroN)
    (.const zeroN) := by
  have hz : Typed rules (.nil : Tower.Ctx 0) (.const zeroN) numT := rules_zero_typed
  exact ⟨⟨hz, hz, .refl hz⟩, ⟨_, .refl hz, .inl ⟨zeroN, 0, [], roles_zero, rfl, rfl⟩⟩,
    ⟨_, .refl hz, .inl ⟨zeroN, 0, [], roles_zero, rfl, rfl⟩⟩⟩

/-- `bot` does not relate `zero`: it is a constructor, no neutral term. -/
theorem bot_not_zero :
    ¬ (ECand.bot (rulesSide v)).rel .nil numT (.const zeroN) (.const zeroN) := by
  intro ne
  have ctor : (rulesSide v).roles zeroN = .constructor 0 := roles_zero
  exact ctorSpine_not_neutral (T := rulesSide v) ctor []
    (NeRel.left_whnf ne (.refl ne.typed.1) (ctorSpine_whnf (T := rulesSide v) ctor []))

/-- **The constructed terms do not relate the identity function**: it reaches no
constructor spine and no neutral term. -/
theorem constructed_not_idNum : ¬ (ECand.constructed (rulesSide v)).rel .nil (.pi numT numT)
    (.lam (.var 0)) (.lam (.var 0)) := by
  rintro ⟨-, ⟨w, r, form⟩, -⟩
  obtain rfl := idNum_reaches r
  rcases form with ⟨k, a, args, -, -, e⟩ | neutral
  · exact appSpine_const_ne_lam' e.symm
  · exact neutral.ne_lam rfl

end Controls

/-! ## Controls: the interpretation, identity types, the daimon, decoder coherence -/

section InterpControls

variable (v : Nat → Nat)

/-- **The lowest universe is interpreted at level one** by its universe pack over
the interpretation at level zero. -/
theorem U0_interp {n : Nat} (ξ : World (nmodel v (rulesSide v)).reading n) :
    NInterp (nmodel v (rulesSide v)) 1 ξ U0
      (ValueSide.universePack (nmodel v (rulesSide v)).value
        (NInterp (nmodel v (rulesSide v)) 0) ξ) :=
  ValueSide.InterpAt.sort (LevelTower.IsUniverse.sort _) Nat.zero_lt_one ξ

/-- **The lowest universe is interpreted by no pack at level zero**: a universe
is interpreted only above its level. -/
theorem U0_not_interp_zero {n : Nat} (ξ : World (nmodel v (rulesSide v)).reading n)
    (P : NPack (nmodel v (rulesSide v)) n) : ¬ NInterp (nmodel v (rulesSide v)) 0 ξ U0 P := by
  intro interp
  exact Nat.not_lt_zero _
    (ValueSide.InterpAt.univ_inv (nmodel_laws v _).value interp .refl (LevelTower.IsUniverse.sort _)).1

/-- **A numeral is interpreted by no pack**: `zero` is a weak-head normal
constructor, and no clause of the interpretation reads a constructor. -/
theorem zero_not_interp {l n : Nat} (ξ : World (nmodel v (rulesSide v)).reading n)
    (P : NPack (nmodel v (rulesSide v)) n) :
    ¬ NInterp (nmodel v (rulesSide v)) l ξ (.const zeroN) P := by
  have normal : Whnf (tmodelC v).rules (tmodelC v).roles (.const zeroN : Tower.Tm n) :=
    (tmodelC_laws v).truth.whnf_zero
  have ctor : (tmodelC v).roles zeroN = .constructor 0 := tmodelRoles_zero
  intro interp
  cases interp with
  | sort _ _ red => cases ValueSide.whRed_of_whnf normal red
  | ground _ red => cases ValueSide.whRed_of_whnf normal red
  | pi red => cases ValueSide.whRed_of_whnf normal red
  | sigma red => cases ValueSide.whRed_of_whnf normal red
  | ident red => cases ValueSide.whRed_of_whnf normal red
  | ind red role =>
      cases ValueSide.whRed_of_whnf normal red
      cases role.symm.trans ctor
  | prop red =>
      have e := ValueSide.whRed_of_whnf normal red
      exact absurd (Tm.const.inj e) (show propN ≠ zeroN by decide)
  | holds red => cases ValueSide.whRed_of_whnf normal red
  | @rigid _ _ _ T args red role =>
      obtain ⟨rfl, -⟩ :=
        Consistency.appSpine_const_eq_const (ValueSide.whRed_of_whnf normal red)
      cases role.symm.trans ctor
  | daimon red daimonic =>
      obtain rfl := ValueSide.whRed_of_whnf normal red
      exact ValueSide.Model.Laws.daimonic_ne_constSpine (V := (nmodel v (rulesSide v)).value)
        (args := []) daimonic (show zeroN ≠ starN by decide)
        (fun _ _ h => by cases h.symm.trans ctor) rfl

/-- **The daimon is a value of the lowest universe, and a numeral is not.** -/
theorem U0_star_not_zero {n : Nat} (ξ : World (nmodel v (rulesSide v)).reading n) :
    (ValueSide.universePack (nmodel v (rulesSide v)).value (NInterp (nmodel v (rulesSide v)) 0)
        ξ).Val (.const starN) ∧
      ¬ (ValueSide.universePack (nmodel v (rulesSide v)).value (NInterp (nmodel v (rulesSide v)) 0)
        ξ).Val (.const zeroN) := by
  refine ⟨ValueSide.InterpAt.star_val (nmodel_laws v _).value (U0_interp v ξ), fun h => ?_⟩
  obtain ⟨P, interp, -, -⟩ := h (Consistency.Morph.id ξ)
  exact zero_not_interp v ξ P interp

/-- The proofs of `Id num 0 0` in context: typings in the realizer side. -/
theorem rules_idZero_typed :
    Typed rules (.nil : Tower.Ctx 0) (.id numT (.const zeroN) (.const zeroN)) U0 :=
  .idForm rules_numT_typed (LevelTower.IsUniverse.sort _) rules_zero_typed rules_zero_typed

/-- **An identity type with related endpoints is realized by reflexivity**: the
proofs of `Id num 0 0` are realized by `refl 0`. -/
theorem idZeroZero_real (t : Tower.Tm 0) :
    ((ValueSide.identPack (ValueSide.numIndPack (nmodel v (rulesSide v)).value 0) (.const zeroN)
      (.const zeroN)).real t).rel .nil (.id numT (.const zeroN) (.const zeroN))
        (.refl (.const zeroN)) (.refl (.const zeroN)) := by
  have hr : Typed rules (.nil : Tower.Ctx 0) (.refl (.const zeroN))
      (.id numT (.const zeroN) (.const zeroN)) := .reflIntro rules_zero_typed
  exact .inr ⟨⟨_, _, _, RedTy.refl ⟨_, LevelTower.IsUniverse.sort _, rules_idZero_typed⟩⟩,
    ⟨_, .refl hr⟩, ⟨_, .refl hr⟩, .refl hr,
    ValueSide.numIndPack_rel.mpr ⟨.zero, .zero .refl, .zero .refl⟩⟩

/-- **An identity type with unrelated endpoints is not realized by reflexivity**:
the proofs of `Id num 0 1` are realized by the identity candidate of a false
proposition, which relates no reflexivity proof. -/
theorem idZeroOne_not_real (t : Tower.Tm 0) :
    ¬ ((ValueSide.identPack (ValueSide.numIndPack (nmodel v (rulesSide v)).value 0) (.const zeroN)
      (.app (.const sucN) (.const zeroN))).real t).rel .nil (.id numT (.const zeroN) (.const zeroN))
        (.refl (.const zeroN)) (.refl (.const zeroN)) := by
  have hr : Typed rules (.nil : Tower.Ctx 0) (.refl (.const zeroN))
      (.id numT (.const zeroN) (.const zeroN)) := .reflIntro rules_zero_typed
  rintro (ne | ⟨-, -, -, -, related⟩)
  · exact (ne.left_whnf (.refl hr) (refl_whnf (setting v).shape _)).ne_refl rfl
  · obtain ⟨s, h₀, h₁⟩ := ValueSide.numIndPack_rel.mp related
    have laws := (nmodel_laws v (rulesSide v)).value
    have e₀ := HasShape.deterministic laws.values.truth laws.star h₀ (.zero .refl)
    subst e₀
    have e₁ := HasShape.deterministic laws.values.truth laws.star h₁ (.suc .refl (.zero .refl))
    cases e₁

/-- **Decoder coherence does not relate a decoding to a universe**: `holds (imp ⋆ ⋆)`
and the lowest universe are not related in the universe relation, since no
decoding is of one shape with a universe. -/
theorem holdsImp_star_not_univ (l : Nat) {n : Nat} (ξ : World (nmodel v (rulesSide v)).reading n) :
    ¬ (ValueSide.universePack (nmodel v (rulesSide v)).value (NInterp (nmodel v (rulesSide v)) l)
      ξ).rel (.app (.const holdsN) (.app (.app (.const impN) (.const starN)) (.const starN)))
        U0 := by
  intro h
  obtain ⟨P, -, -, shape⟩ := h (Consistency.Morph.id ξ)
  rw [rename_id, rename_id] at shape
  exact ValueSide.Shape.holds_not_univ (nmodel_laws v _).value (LevelTower.IsUniverse.sort _) shape

/-- **At a dependent function type, the function space of the realizer side
relates the identity function**, for every candidate. -/
theorem idNum_arrow (X : ECand (rulesSide v)) :
    ((ecandAlgebra (rulesSide v)).arrow X X).rel .nil (.pi numT (Presentation.rename wk numT))
      (.lam (.var 0)) (.lam (.var 0)) :=
  lam_var_arrow X (LevelTower.IsUniverse.sort _) rules_numT_typed

/-- **At a type variable the function space is `bot`**: a type variable reduces to
no dependent function type, so without a decoding step reaching one, the
realizers of an implication relate only terms reaching neutral terms. -/
theorem arrow_at_variable (X Y : ECand (rulesSide v)) {t t' : Tower.Tm 1} :
    ((ecandAlgebra (rulesSide v)).arrow X Y).rel (.snoc .nil U0) (.var 0) t t' ↔
      (ECand.bot (rulesSide v)).rel (.snoc .nil U0) (.var 0) t t' :=
  ECand.piOver_rel_of_not_pi fun D C h => by
    cases WhRed.eq_of_whnf ((Neutral.var (roles := roles) 0).whnf (setting v).shape) h.red

end InterpControls

end ConvRules
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
