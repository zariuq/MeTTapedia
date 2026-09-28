import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Constructions
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Reading
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.InterpLaws

/-!
# The realizers of meanings, and the equality reading

The value side realizes the meanings of carriers over any realizer algebra
(`RealizerAlgebra.Real`). At the algebra of equality candidates:

* a code is realized by the constructed terms: the typed terms that `E` relates
  and that reach a constructor applied to its arguments or a neutral term;
* a point of a rigid type is realized by `top`, the typed terms that `E`
  relates;
* a number of shape `s` is realized by the constructor candidates of the
  numbers. These are the realizers of the shapes of numbers (`ecand_numReal`,
  `ecand_real_num`): terms reducing, at the type of numbers, to `zero`, to `suc`
  applied to a realizer of the predecessor shape, or to neutral terms;
* a function is realized by Girard's clause over the meanings of its domain.

The equality reading is the candidate reading over this algebra
(`equalityReading`). It has the laws of a reading (`equalityReading_laws`). At a
realizer type reducing to a dependent function type, its quantification over a
carrier is Girard's clause over the meanings of the carrier
(`equalityReading_allMeaning_pi`), and its implication is the function space of
candidates (`equalityReading_impMeaning_pi`).

A conversion model reads a package with the consistency model's reduction and
universe levels, a daimon, and a realizer side. Its value model is the value
side over the algebra of equality candidates (`NModel.value`), and it has the
value side's laws (`NModel.Laws.value`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Conversion

open Normalization
open UniverseLevel (LevelOrder)
open Consistency (Kind Carrier Reading DataEq dataValue)
open Realizability (HasShape)
open StrongNormalization (NumShape)
open ValueSide (RealizerAlgebra algebraReading)

variable {Head L : Type} [LevelOrder L] {T : RealizerSide Head L}

/-! ## The realizers of numbers -/

variable (T) in
/-- The realizers of a number of shape `s`, read shape by shape. At every
realizer type they relate the terms reducing to neutral terms that `E`
compares. At a realizer type reducing to the numbers `num` they also relate,
at shape zero, terms reducing to `zero`, and at shape `suc s`, terms reducing to
`suc` applied to arguments related at `num` by the realizers of `s`, in both
cases related by `E`. -/
def NumShapeRel (num zero suc : DeclName) :
    NumShape → ∀ {m : Nat}, Ctx Head m → Tm Head m → Tm Head m → Tm Head m → Prop
  | .zero, _, Δ, A, t, t' => NeRel T Δ A t t' ∨
      (RedTy T.R T.roles Δ A (.const num) ∧ RedTm T.R T.roles Δ t (.const zero) A ∧
        RedTm T.R T.roles Δ t' (.const zero) A ∧ T.E.convTm Δ t t' A)
  | .suc s, _, Δ, A, t, t' => NeRel T Δ A t t' ∨
      (RedTy T.R T.roles Δ A (.const num) ∧ ∃ a a',
        RedTm T.R T.roles Δ t (.app (.const suc) a) A ∧
        RedTm T.R T.roles Δ t' (.app (.const suc) a') A ∧ T.E.convTm Δ t t' A ∧
        NumShapeRel num zero suc s Δ (.const num) a a')
  | .star, _, Δ, A, t, t' => NeRel T Δ A t t'

/-- **The constructor candidates at the numbers are the realizers of the shapes
of numbers**, for numbers declared as the inductive type with the constructors
`zero`, without fields, and `suc`, with one recursive field. -/
theorem ecand_numReal {num zero suc : DeclName}
    (role : T.roles num = .inductive [(zero, []), (suc, [.recursive])]) :
    ∀ (s : NumShape) {m : Nat} (Δ : Ctx Head m) (A t t' : Tm Head m),
      ((ecandAlgebra T).numReal num zero suc s).rel Δ A t t' ↔
        NumShapeRel T num zero suc s Δ A t t' := by
  intro s
  induction s with
  | zero =>
      intro m Δ A t t'
      refine or_congr Iff.rfl ⟨?_, ?_⟩
      · rintro ⟨cs, fs, as, as', -, -, hA, r, r', cv, fields⟩
        cases fields
        exact ⟨hA, r, r', cv⟩
      · rintro ⟨hA, r, r', cv⟩
        exact ⟨_, [], [], [], role, List.mem_cons_self .., hA, r, r', cv, .nil⟩
  | suc s ih =>
      intro m Δ A t t'
      refine or_congr Iff.rfl ⟨?_, ?_⟩
      · rintro ⟨cs, fs, as, as', role', mem, hA, r, r', cv, fields⟩
        obtain rfl := Role.inductive.inj (role.symm.trans role')
        rcases fields with _ | ⟨hx, rest⟩
        cases rest
        rcases List.mem_cons.mp mem with e | mem
        · exact absurd (Prod.mk.inj e).2 (List.cons_ne_nil _ _)
        · obtain rfl := List.head_eq_of_cons_eq (Prod.mk.inj (List.mem_singleton.mp mem)).2
          exact ⟨hA, _, _, r, r', cv, (ih Δ _ _ _).mp hx⟩
      · rintro ⟨hA, a, a', r, r', cv, shape⟩
        exact ⟨_, [.recursive], [a], [a'], role,
          List.mem_cons_of_mem _ (List.mem_singleton_self _), hA, r, r', cv,
          .cons ((ih Δ _ _ _).mpr shape) .nil⟩
  | star =>
      intro m Δ A t t'
      exact Iff.rfl

/-- **The realizers of a number are those of its shape**: the realizers of the
value of a term of the numbers of shape `s` relate exactly what `NumShapeRel`
relates at `s`, when the realizer side's numbers have the value side's
constructors. -/
theorem ecand_real_num {S : Consistency.Setting Head} {star num : DeclName} (laws : S.Laws)
    (rigid : S.roles star = .rigid)
    (role : T.roles num = .inductive [(S.zero, []), (S.suc, [.recursive])]) {n : Nat}
    {a : Tm Head n} (rel : DataEq (S.shapes star) .num a a) {s : NumShape}
    (shape : HasShape S star a s) {m : Nat} (Δ : Ctx Head m) (A t t' : Tm Head m) :
    ((ecandAlgebra T).Real S star num .num
        (dataValue (P := (ecandAlgebra T).Cand) (S.shapes star) .num a rel)).rel Δ A t t' ↔
      NumShapeRel T num S.zero S.suc s Δ A t t' := by
  change ((ecandAlgebra T).numValReal S star num
    (dataValue (P := (ecandAlgebra T).Cand) (S.shapes star) .num a rel)).rel Δ A t t' ↔ _
  rw [(ecandAlgebra_laws T).numValReal_dataValue laws rigid num rel shape]
  exact ecand_numReal role s Δ A t t'

/-! ## Codes and rigid types -/

/-- A code is realized by the constructed terms. -/
theorem ecand_real_prop (S : Consistency.Setting Head) (star num : DeclName) (v : ECand T) :
    (ecandAlgebra T).Real S star num .prop v = ECand.constructed T :=
  rfl

/-- A point of a rigid type is realized by `top`. -/
theorem ecand_real_rigid (S : Consistency.Setting Head) (star num I : DeclName) (v : Unit) :
    (ecandAlgebra T).Real S star num (.rigid I) v = ECand.top T :=
  rfl

/-! ## The equality reading -/

/-- **The equality reading**: the candidate reading over the realizer algebra of
equality candidates. -/
abbrev equalityReading (S : Consistency.Setting Head) (star num : DeclName)
    (T : RealizerSide Head L) : Reading Head :=
  algebraReading S star num (ecandAlgebra T)

/-- **The laws of the equality reading.** -/
theorem equalityReading_laws {S : Consistency.Setting Head} {star : DeclName} (num : DeclName)
    (T : RealizerSide Head L) (laws : S.Laws) (rigid : S.roles star = .rigid) :
    (equalityReading S star num T).Laws :=
  ValueSide.algebraReading_laws laws rigid (ecandAlgebra_laws T)

/-- **Quantification in the equality reading is Girard's clause.** At a realizer
type reducing to `Π D C`, the realizers of a quantification over the carrier `K`
of the family `φ` are the terms that reach weak-head normal functions and that
`E` relates, whose applications, after every renaming into a formed context, at
every meaning `v` of `K` and all arguments related by the realizers of `v`, are
related by `φ v` at the codomain instantiated at the argument. -/
theorem equalityReading_allMeaning_pi (S : Consistency.Setting Head) (star num : DeclName)
    {k : Kind} (K : Carrier k) (φ : K.Val (S.shapes star) (ECand T) → ECand T) {m : Nat}
    {Δ : Ctx Head m} {A t t' D : Tm Head m} {C : Tm Head (m + 1)}
    (hA : RedTy T.R T.roles Δ A (.pi D C)) :
    ((equalityReading S star num T).allMeaning K φ).rel Δ A t t' ↔
      FunNf T Δ A t ∧ FunNf T Δ A t' ∧ T.E.convTm Δ t t' A ∧
        ∀ (v : K.Val (S.shapes star) (ECand T)) {k' : Nat} {Θ : Ctx Head k'} {ρ : Ren m k'},
          CtxRen Δ Θ ρ → CtxFormed T.R Θ → ∀ {s s' : Tm Head k'},
            ((ecandAlgebra T).Real S star num K v).rel Θ (Presentation.rename ρ D) s s' →
            (φ v).rel Θ (inst0 s (Presentation.rename (liftRen ρ) C))
              (.app (Presentation.rename ρ t) s) (.app (Presentation.rename ρ t') s') := by
  refine (ECand.piOver_rel_pi (d := (ecandAlgebra T).Real S star num K) (c := φ) hA).trans ?_
  constructor
  · rintro ⟨f, f', cv, app⟩
    refine ⟨f, f', cv, ?_⟩
    intro v k' Θ ρ ren formed s s' hs
    exact app v ⟨ren, formed⟩ hs
  · rintro ⟨f, f', cv, app⟩
    refine ⟨f, f', cv, fun v => ?_⟩
    intro k' Θ ρ world s s' hs
    exact app v world.1 world.2 hs

/-- **Implication in the equality reading is the function space.** At a
realizer type reducing to `Π D C`, the realizers of an implication from `X` to
`Y` are the terms that reach weak-head normal functions and that `E` relates,
whose applications, after every renaming into a formed context, at arguments
related by `X`, are related by `Y` at the codomain instantiated at the
argument. -/
theorem equalityReading_impMeaning_pi (S : Consistency.Setting Head) (star num : DeclName)
    (X Y : ECand T) {m : Nat} {Δ : Ctx Head m} {A t t' D : Tm Head m} {C : Tm Head (m + 1)}
    (hA : RedTy T.R T.roles Δ A (.pi D C)) :
    ((equalityReading S star num T).impMeaning X Y).rel Δ A t t' ↔
      FunNf T Δ A t ∧ FunNf T Δ A t' ∧ T.E.convTm Δ t t' A ∧
        ∀ {k' : Nat} {Θ : Ctx Head k'} {ρ : Ren m k'}, CtxRen Δ Θ ρ → CtxFormed T.R Θ →
          ∀ {s s' : Tm Head k'}, X.rel Θ (Presentation.rename ρ D) s s' →
            Y.rel Θ (inst0 s (Presentation.rename (liftRen ρ) C))
              (.app (Presentation.rename ρ t) s) (.app (Presentation.rename ρ t') s') := by
  refine (ECand.piOver_rel_pi (d := fun _ : Unit => X) (c := fun _ => Y) hA).trans ?_
  constructor
  · rintro ⟨f, f', cv, app⟩
    refine ⟨f, f', cv, ?_⟩
    intro k' Θ ρ ren formed s s' hs
    exact app () ⟨ren, formed⟩ hs
  · rintro ⟨f, f', cv, app⟩
    refine ⟨f, f', cv, fun _ => ?_⟩
    intro k' Θ ρ world s s' hs
    exact app world.1 world.2 hs

/-! ## The conversion model -/

/-- The conversion model: the consistency model's reading of a package, with
universe levels in a level order `L`, a daimon, and a realizer side. -/
structure NModel (Head L : Type) [LevelOrder L] extends Consistency.Model Head L where
  star : DeclName
  side : RealizerSide Head L

namespace NModel

variable (M : NModel Head L)

/-- The value model of the conversion model: its values are realized by the
equality candidates of the realizer side. -/
def value : ValueSide.Model Head L where
  toModel := M.toModel
  star := M.star
  alg := ecandAlgebra M.side

/-- The reading of codes of the conversion model is the equality reading. -/
theorem value_reading : M.value.reading = equalityReading M.toSetting M.star M.num M.side :=
  rfl

/-- The laws of the conversion model: those of the consistency model, the
daimon rigid and distinct from the type of codes and from the decoder, and the
listed constructors of inductive types declared as constructors. -/
structure Laws : Prop where
  values : M.toModel.Laws
  star : M.roles M.star = .rigid
  starNotProp : M.star ≠ M.prop
  starNotHolds : M.star ≠ M.holds
  declared : ConstructorsDeclared M.roles

variable {M}

/-- **The laws of the value model of the conversion model**: the algebra of
equality candidates has the laws of a realizer algebra. -/
theorem Laws.value (laws : M.Laws) : M.value.Laws :=
  ⟨laws.values, laws.star, laws.starNotProp, laws.starNotHolds, ecandAlgebra_laws M.side,
    laws.declared⟩

/-- The laws of the reading of codes of the conversion model. -/
theorem Laws.reading (laws : M.Laws) :
    (equalityReading M.toSetting M.star M.num M.side).Laws :=
  ValueSide.Model.Laws.reading laws.value

end NModel

end Conversion
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
