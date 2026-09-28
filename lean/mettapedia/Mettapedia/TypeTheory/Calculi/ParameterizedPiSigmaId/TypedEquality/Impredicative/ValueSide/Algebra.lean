import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Daimon

/-!
# Realizer algebras and the candidate reading over them

The value side of the normalization model reads the realizers of its values
in a *realizer algebra*: a type of candidates with the constructions the
interpretation of types uses, and nothing more.

* `top`, `univ` and `codes` realize the values of a type whose values are all
  related, of a universe, and of the type of codes;
* `meet` is the meet of a family of candidates over any index type;
* `piOver d c` is Girard's clause over an index: the terms that send, at every
  index `i`, every realizer in `d i` to a realizer in `c i`; with one index it
  is the function space `arrow`;
* `sigmaOver` realizes pairs, and `ident P` identity proofs whose endpoints are
  related exactly when `P` holds;
* `ctorReal T k Xs` realizes a value of the inductive type `T` built by the
  constructor `k` from fields realized by `Xs`, and `stuckReal T` a value of `T`
  stuck on the daimon.

The laws the generic layer uses are equalities: the meet of a nonempty
constant family is its value, and meets and Girard's clause depend only on
the set of candidates, or pairs of candidates, they range over. Membership and
inclusion are no part of the interface.

Codes are read over any realizer algebra: implication means the function
space, a quantifier Girard's clause over the meanings of its carrier, an
equation the identity candidate of the equality of the two meanings, and a
daimonic code `top`. A meaning of a carrier is realized as in the Kripke model:
a code by `codes`, a point of a rigid type by `top`, a number by the meet of the
realizers of the shapes of its representatives, and a function by Girard's
clause over the meanings of its domain.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ValueSide

open Normalization
open Consistency (Kind Carrier Q Realizer Reading)
open Realizability (Daimonic HasShape appGen appData)
open StrongNormalization (NumShape)

/-- The realizers of the values of the normalization model: candidates with the
constructions of the interpretation. -/
structure RealizerAlgebra (Head : Type) where
  /-- The candidates. -/
  Cand : Type
  /-- The realizers of a value of a type whose values are all related. -/
  top : Cand
  /-- The realizers of a type, as a value of a universe. -/
  univ : Cand
  /-- The realizers of a code. -/
  codes : Cand
  /-- The meet of a family of candidates. -/
  meet : ∀ {ι : Type}, (ι → Cand) → Cand
  /-- Girard's clause over an index: every realizer of `d i` is sent into `c i`. -/
  piOver : ∀ {ι : Type}, (ι → Cand) → (ι → Cand) → Cand
  /-- Pairs whose projections realize the two candidates. -/
  sigmaOver : Cand → Cand → Cand
  /-- Identity proofs whose endpoints are related exactly when the proposition
  holds. -/
  ident : Prop → Cand
  /-- A value of an inductive type built by a constructor from realized fields. -/
  ctorReal : DeclName → DeclName → List Cand → Cand
  /-- A value of an inductive type stuck on the daimon. -/
  stuckReal : DeclName → Cand

variable {Head : Type}

namespace RealizerAlgebra

variable (A : RealizerAlgebra Head)

/-- The function space: Girard's clause over one index. -/
def arrow (X Y : A.Cand) : A.Cand :=
  A.piOver (fun _ : Unit => X) (fun _ => Y)

/-- The laws of a realizer algebra: the meet of a nonempty constant family is
its value, and meets and Girard's clause are determined by what they range
over. -/
structure Laws : Prop where
  meet_const : ∀ {ι : Type} (f : ι → A.Cand) (x : A.Cand), (∀ i, f i = x) → Nonempty ι →
    A.meet f = x
  meet_congr : ∀ {ι κ : Type} (f : ι → A.Cand) (g : κ → A.Cand),
    (∀ i, ∃ j, f i = g j) → (∀ j, ∃ i, f i = g j) → A.meet f = A.meet g
  piOver_congr : ∀ {ι κ : Type} (d c : ι → A.Cand) (d' c' : κ → A.Cand),
    (∀ i, ∃ j, d i = d' j ∧ c i = c' j) → (∀ j, ∃ i, d i = d' j ∧ c i = c' j) →
    A.piOver d c = A.piOver d' c'

/-! ## Realizers of the meanings of carriers -/

/-- The realizers of a number of each shape, at the numbers `num` with
constructors `zero` and `suc`. -/
def numReal (num zero suc : DeclName) : NumShape → A.Cand
  | .zero => A.ctorReal num zero []
  | .suc s => A.ctorReal num suc [numReal num zero suc s]
  | .star => A.stuckReal num

/-- The realizers of a value of the numbers: the meet of the realizers of the
shapes of its representatives. -/
def numValReal (S : Consistency.Setting Head) (star num : DeclName) (v : Q (S.shapes star) .num) :
    A.Cand :=
  A.meet fun i : {s : NumShape // ∃ r : Realizer (S := S.shapes star) .num,
      Quot.mk _ r = v ∧ HasShape S star r.1 s} => A.numReal num S.zero S.suc i.1

/-- The realizers of the meanings of each carrier: `codes` at `prop`, `top` at a
rigid type, the realizers of the value at the numbers, and at a function
Girard's clause over the meanings of the domain. -/
def Real (S : Consistency.Setting Head) (star num : DeclName) :
    {k : Kind} → (K : Carrier k) → K.Val (S.shapes star) A.Cand → A.Cand
  | _, .prop, _ => A.codes
  | _, .rigid _, _ => A.top
  | _, .num, v => A.numValReal S star num v
  | _, @Carrier.arr _ .gen K K', φ =>
      A.piOver (Real S star num K) fun v => Real S star num K' (φ v)
  | _, @Carrier.arr .gen .data K K', F =>
      A.piOver (Real S star num K) fun _ => Real S star num K' (appGen F)
  | _, @Carrier.arr .data .data K K', F =>
      A.piOver (Real S star num K) fun a => Real S star num K' (appData F a)

end RealizerAlgebra

/-! ## The reading -/

/-- The candidate reading over a realizer algebra, for the setting `S`, the
daimon `star` and the numbers `num`: implication means the function space, a
quantifier Girard's clause over the meanings of its carrier, an equation the
identity candidate of the equality of the meanings, a daimonic code `top`, and
the meet of a family its meet. -/
def algebraReading (S : Consistency.Setting Head) (star num : DeclName) (A : RealizerAlgebra Head) :
    Reading Head where
  toDataSetting := S.shapes star
  P := A.Cand
  impMeaning := A.arrow
  allMeaning := fun K φ => A.piOver (A.Real S star num K) φ
  eqMeaning := fun _ v w => A.ident (v = w)
  neutral := Daimonic S.roles star
  neutral_subst := fun σ daimonic => daimonic.subst σ
  neutralMeaning := A.top
  meet := A.meet
  top := A.top

end ValueSide
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
