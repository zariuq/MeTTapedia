import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Reading
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Carriers

/-!
# The interpretation of the conversion model

The value model of the conversion model is the value side over the algebra of
equality candidates (`NModel.value`). Its packs, its interpretation of types at a
level and its denotations are the value side's at that value model (`NPack`,
`NInterp`, `DenN`). A pack relates values and gives each value its realizers: an
equality candidate, which relates terms of the realizer side at every realizer
type.

Read clause by clause, the interpretation realizes

* a type, as a value of a universe below the level, by the types: the terms
  reaching the weak-head form of a type, related by `E` (`NInterp.univ_real`);
* a value of a head that is no universe, of a rigid spine or of a daimonic type
  by `top` (`NInterp.ground_real`, `NInterp.rigid_real`, `NInterp.daimon_real`);
* a function by Girard's clause over its valid arguments at every world reached
  by a morphism: at a realizer type reducing to `Π D C`, the terms reaching
  weak-head normal functions, related by `E`, whose applications to arguments
  realizing a valid argument realize the result (`PiPack.real_rel_pi`);
* a pair with a valid first projection by the pairs of realizers of its
  projections (`PiPack.pairReal_rel`, `PiPack.pairReal_rel_sigma`);
* a proof of an identity type by the identity candidate of the relation of its
  endpoints (`NInterp.id_real`);
* a number, when the realizer side has the value side's numbers, by the
  constructor candidates of its shape: terms reaching `zero`, `suc` of a
  realizer of the predecessor's shape, or neutral terms (`NInterp.num_real`);
* a code by the constructed terms: the terms reaching a constructor applied to
  its arguments or a neutral term (`NInterp.prop_real`);
* a proof of the decoding `holds c` of a code `c` meaning `X` by `X` itself
  (`NInterp.holds_real`).

Nothing of model S is copied: every statement is the value side's, read at the
value model of the conversion model.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Conversion

open Normalization
open UniverseLevel (LevelOrder)
open Consistency (Reading World Morph Truth)
open Realizability (Daimonic HasShape)
open StrongNormalization (NumShape)

variable {Head L : Type} [LevelOrder L]

/-! ## Packs, the interpretation and denotations -/

/-- The reading of codes of the conversion model: the equality reading. -/
abbrev NModel.reading (M : NModel Head L) : Reading Head := M.value.reading

/-- The packs of the conversion model: a value relation, and the realizers of
each value, an equality candidate. -/
abbrev NPack (M : NModel Head L) (n : Nat) : Type := ValueSide.Pack M.value n

/-- **The interpretation of types at a level** in the conversion model: the value
side's interpretation at the value model of the conversion model. -/
abbrev NInterp (M : NModel Head L) (l : L) : ValueSide.IPack M.value :=
  ValueSide.InterpAt M.value l

/-- The denotation of a type in the conversion model: its pack at some level. -/
abbrev DenN (M : NModel Head L) : ValueSide.IPack M.value := ValueSide.DenS M.value

variable {M : NModel Head L}

/-! ## The realizers of the packs of the clauses -/

section Packs

variable {n : Nat}

/-- The types of a universe are realized by the types. -/
theorem universePack_real (I : ValueSide.IPack M.value) (ξ : World M.reading n)
    (A : Tm Head n) : (ValueSide.universePack M.value I ξ).real A = ECand.types M.side :=
  rfl

/-- The values of a type whose values are all related are realized by `top`. -/
theorem total_real (a : Tm Head n) : (ValueSide.Pack.total M.value n).real a = ECand.top M.side :=
  rfl

/-- The codes are realized by the constructed terms. -/
theorem propPack_real (ξ : World M.reading n) (c : Tm Head n) :
    (ValueSide.propPack M.value ξ).real c = ECand.constructed M.side :=
  rfl

/-- The proofs of a decoding of a code meaning `X` are realized by `X`. -/
theorem holdsPack_real (X : ECand M.side) (t : Tm Head n) :
    (ValueSide.holdsPack M.value n X).real t = X :=
  rfl

/-- The proofs of an identity type are realized by the identity candidate of the
relation of its endpoints. -/
theorem identPack_real (R : NPack M n) (lhs rhs t : Tm Head n) :
    (ValueSide.identPack R lhs rhs).real t = ECand.ident M.side (R.rel lhs rhs) :=
  rfl

end Packs

/-! ## Functions and pairs -/

namespace PiPack

variable {n : Nat} {ξ : World M.reading n} (Q : ValueSide.PiPack M.value ξ)

/-- The realizers of a function are Girard's clause over its valid arguments at
every world reached by a morphism. -/
theorem real_eq (f : Tm Head n) :
    Q.real f = ECand.piOver (fun a : Q.Arg => (Q.dom a.morph).real a.arg)
      (fun a => (Q.cod a.morph a.valid).real (.app (Presentation.rename a.ren f) a.arg)) :=
  rfl

/-- **The realizers of a function**, at a realizer type reducing to a dependent
function type `Π D C`: the terms reaching weak-head normal functions, related by
`E`, whose applications, after every renaming into a formed context, to
arguments realizing a valid argument at a world reached by a morphism, realize
the result. -/
theorem real_rel_pi (f : Tm Head n) {m : Nat} {Δ : Ctx Head m} {A t t' D : Tm Head m}
    {C : Tm Head (m + 1)} (hA : RedTy M.side.R M.side.roles Δ A (.pi D C)) :
    (Q.real f).rel Δ A t t' ↔ FunNf M.side Δ A t ∧ FunNf M.side Δ A t' ∧
      M.side.E.convTm Δ t t' A ∧
      ∀ {k : Nat} {ξ' : World M.reading k} {ρ : Ren n k} (w : Morph ξ ξ' ρ) {a : Tm Head k}
        (ha : (Q.dom w).Val a),
        AppClause ((Q.dom w).real a) ((Q.cod w ha).real (.app (Presentation.rename ρ f) a))
          Δ D C t t' := by
  rw [real_eq]
  refine (ECand.piOver_rel_pi hA).trans ⟨?_, ?_⟩
  · rintro ⟨fn, fn', cv, app⟩
    exact ⟨fn, fn', cv, fun w a ha => app ⟨_, _, _, w, a, ha⟩⟩
  · rintro ⟨fn, fn', cv, app⟩
    exact ⟨fn, fn', cv, fun i => app i.morph i.valid⟩

/-- The realizers of a pair are the meet, over the validity of its first
projection, of the pairs of realizers of its projections. -/
theorem pairReal_eq (p : Tm Head n) :
    Q.pairReal p = ECand.inter fun hp : PLift ((Q.dom (Morph.id ξ)).Val (.fst p)) =>
      ECand.sigmaOver ((Q.dom (Morph.id ξ)).real (.fst p))
        ((Q.cod (Morph.id ξ) hp.down).real (.snd p)) :=
  rfl

/-- **The realizers of a pair**: the terms `top` relates that, when the first
projection of the pair is valid, are pairs of realizers of its projections. -/
theorem pairReal_rel (p : Tm Head n) {m : Nat} {Δ : Ctx Head m} {A t t' : Tm Head m} :
    (Q.pairReal p).rel Δ A t t' ↔ (ECand.top M.side).rel Δ A t t' ∧
      ∀ hp : (Q.dom (Morph.id ξ)).Val (.fst p),
        (ECand.sigmaOver ((Q.dom (Morph.id ξ)).real (.fst p))
          ((Q.cod (Morph.id ξ) hp).real (.snd p))).rel Δ A t t' :=
  ⟨fun h => ⟨h.1, fun hp => h.2 ⟨hp⟩⟩, fun h => ⟨h.1, fun hp => h.2 hp.down⟩⟩

/-- The realizers of a pair with a valid first projection, at a realizer type
reducing to a dependent pair type `Σ D C`: the terms reaching weak-head normal
pairs, related by `E`, whose projections, after every renaming into a formed
context, realize the projections of the pair. -/
theorem pairReal_rel_sigma (p : Tm Head n) (hp : (Q.dom (Morph.id ξ)).Val (.fst p)) {m : Nat}
    {Δ : Ctx Head m} {A t t' D : Tm Head m} {C : Tm Head (m + 1)}
    (hA : RedTy M.side.R M.side.roles Δ A (.sigma D C)) :
    (Q.pairReal p).rel Δ A t t' ↔ PairNf M.side Δ A t ∧ PairNf M.side Δ A t' ∧
      M.side.E.convTm Δ t t' A ∧
      ProjClause ((Q.dom (Morph.id ξ)).real (.fst p)) ((Q.cod (Morph.id ξ) hp).real (.snd p))
        Δ D C t t' := by
  rw [pairReal_rel]
  constructor
  · rintro ⟨-, h⟩
    exact (ECand.sigmaOver_rel_sigma hA).mp (h hp)
  · intro h
    have related := (ECand.sigmaOver_rel_sigma hA).mpr h
    refine ⟨ECand.le_top _ related, fun hp' => ?_⟩
    exact related

end PiPack

/-! ## The clauses of the interpretation -/

section Clauses

variable (laws : M.Laws) {l : L} {n : Nat} {ξ : World M.reading n} {X : Tm Head n}
  {P : NPack M n}
include laws

/-- **A type reducing to a universe below the level is realized by the types.** -/
theorem NInterp.univ_real (interp : NInterp M l ξ X P) {u : Head}
    (red : WhRed M.rules M.roles X (.head u)) (hu : M.rules.isUniverse u) (a : Tm Head n) :
    P.real a = ECand.types M.side := by
  obtain ⟨-, rfl⟩ := ValueSide.InterpAt.univ_inv laws.value interp red hu
  rfl

/-- A head that is no universe is realized by `top`. -/
theorem NInterp.ground_real (interp : NInterp M l ξ X P) {h : Head}
    (red : WhRed M.rules M.roles X (.head h)) (hh : ¬ M.rules.isUniverse h) (a : Tm Head n) :
    P.real a = ECand.top M.side := by
  rcases ValueSide.SInterp.head_inv laws.value interp red with ⟨hu, -⟩ | ⟨-, rfl⟩
  · exact absurd hu hh
  · rfl

/-- A rigid spine that is not the type of codes or a decoding is realized by
`top`. -/
theorem NInterp.rigid_real (interp : NInterp M l ξ X P) {T : DeclName} {args : List (Tm Head n)}
    (red : WhRed M.rules M.roles X (appSpine (.const T) args)) (role : M.roles T = .rigid)
    (notProp : T ≠ M.prop) (notHolds : T ≠ M.holds) (a : Tm Head n) :
    P.real a = ECand.top M.side := by
  rw [ValueSide.SInterp.deterministic laws.value interp
    (.rigid (V := M.value) red role notProp notHolds)]
  rfl

/-- A daimonic type is realized by `top`. -/
theorem NInterp.daimon_real (interp : NInterp M l ξ X P) {u : Tm Head n}
    (red : WhRed M.rules M.roles X u) (daimonic : Daimonic M.roles M.star u) (a : Tm Head n) :
    P.real a = ECand.top M.side := by
  rw [ValueSide.SInterp.eq_total_of_daimonic laws.value interp red daimonic]
  rfl

/-- **The codes are realized by the constructed terms.** -/
theorem NInterp.prop_real (interp : NInterp M l ξ X P)
    (red : WhRed M.rules M.roles X (.const M.prop)) (c : Tm Head n) :
    P.real c = ECand.constructed M.side := by
  rw [ValueSide.SInterp.deterministic laws.value interp (.prop (V := M.value) red)]
  rfl

/-- **A decoding of a code is realized by the meaning of the code.** -/
theorem NInterp.holds_real (interp : NInterp M l ξ X P) {c : Tm Head n}
    (red : WhRed M.rules M.roles X (.app (.const M.holds) c)) :
    ∃ Y : ECand M.side, Truth M.reading ξ c Y ∧ ∀ t, P.real t = Y := by
  obtain ⟨Y, truth, rfl⟩ := ValueSide.SInterp.holds_inv laws.value interp red
  exact ⟨Y, truth, fun _ => rfl⟩

/-- **An identity type is realized by the identity candidate of the relation of
its endpoints** in the pack of its carrier. -/
theorem NInterp.id_real (interp : NInterp M l ξ X P) {A a b : Tm Head n}
    (red : WhRed M.rules M.roles X (.id A a b)) :
    ∃ R : NPack M n, NInterp M l ξ A R ∧ R.Val a ∧ R.Val b ∧
      ∀ t, P.real t = ECand.ident M.side (R.rel a b) := by
  obtain ⟨R, rfl, tyInterp, ha, hb⟩ := ValueSide.SInterp.id_inv laws.value interp red
  exact ⟨R, tyInterp, ha, hb, fun _ => rfl⟩

/-- **A number of a shape is realized by the constructor candidates of the
shape**, when the realizer side's numbers are the value side's: terms reaching
`zero` at shape zero, terms reaching `suc` of a realizer of the predecessor's
shape at a successor shape, and at every shape terms reaching neutral terms that
`E` compares. -/
theorem NInterp.num_real (interp : NInterp M l ξ X P)
    (red : WhRed M.rules M.roles X (.const M.num))
    (role : M.side.roles M.num = .inductive [(M.zero, []), (M.suc, [.recursive])])
    {a : Tm Head n} {s : NumShape} (shape : HasShape M.toSetting M.star a s) {m : Nat}
    (Δ : Ctx Head m) (A t t' : Tm Head m) :
    (P.real a).rel Δ A t t' ↔ NumShapeRel M.side M.num M.zero M.suc s Δ A t t' := by
  rw [ValueSide.SInterp.deterministic laws.value interp
    (ValueSide.InterpAt.num laws.value l red)]
  rw [ValueSide.numIndPack_real_of_shape laws.value shape]
  exact ecand_numReal role s Δ A t t'

end Clauses

end Conversion
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
