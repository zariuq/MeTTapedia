import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Daimon

/-!
# The candidate reading

The normalization model reads a code by a Kripke candidate: the set of terms,
in every scope, that realize proofs of it. Realizers are terms of a rule
package under its own reduction, the *realizer side*. Its root steps occur at
constant spines of exact arity and reflect renaming, and its decoder's steps
are among them.

* Implication means the Kripke function space of the two candidates.
* A quantifier at a carrier means Girard's clause: the terms that send every
  realizer of every meaning of the carrier, after any renaming, into the
  meaning of the family at that meaning.
* An equation means the identity candidate of the equality of the two
  meanings: strongly normalizing terms that reduce to reflexivity only when the
  meanings are equal.
* Daimonic codes mean the strongly normalizing terms, and the meet of a family
  of candidates is their intersection.

Girard's clause needs the realizers of each meaning of each carrier:

* a code is realized by the terms whose decoding is strongly normalizing;
* a point of a rigid type by every strongly normalizing term;
* a number by the realizers of the shape of its representatives;
* a function by the terms that send, after any renaming, every realizer of
  every meaning of the domain to a realizer of the image of that meaning.

Every carrier has a meaning, the daimon at the data carriers, so the
realizers of a function are strongly normalizing.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Realizability

open Normalization
open Consistency
open StrongNormalization

variable {Head : Type}

/-! ## The realizer side -/

/-- The realizer side of the normalization model: a rule package with roles,
decoders and numerals. Its root steps occur at constant spines of exact arity
and reflect renaming, the decoder computes at the code, and the decoder's
steps are steps of the package. -/
structure Realizers (Head : Type) where
  rules : Rules Head
  roles : Roles Head
  decoders : Decoders Head
  zero : DeclName
  suc : DeclName
  shape : RootShape rules roles
  reflects : RootReflectsRename rules.computation
  decoderRoles : DecoderRoles roles decoders
  numerals : NumeralRoles roles zero suc
  decodes : ∀ {n : Nat} {l r : Tm Head n}, DecoderStep decoders l r →
    rules.computation.step l r

namespace Realizers

variable (T : Realizers Head)

/-- The Kripke candidates of the realizer side. -/
abbrev Cand : Type := KCand T.rules T.roles

/-- The strongly normalizing terms. -/
abbrev sn : T.Cand := KCand.sn' T.reflects

/-- The realizers of codes: terms whose decoding is strongly normalizing. -/
abbrev codes : T.Cand := CodeReal T.shape T.reflects T.decoderRoles

end Realizers

/-! ## Realizers of the meanings of carriers -/

section Realizers

variable (S : Consistency.Setting Head) (star : DeclName) (T : Realizers Head)

/-- The realizers of a number: the realizers of the shape of its
representatives. -/
def numReal (v : Q (S.shapes star) .num) : T.Cand :=
  KCand.inter T.reflects fun i : {s : NumShape // ∃ r : Realizer (S := S.shapes star) .num,
      Quot.mk _ r = v ∧ HasShape S star r.1 s} => NumReal T.reflects T.numerals i.1

/-- The realizers of the meanings of each carrier: at `prop` the realizers of
codes, at a rigid type the strongly normalizing terms, at the numbers the
realizers of the shape of the number, and at a function the terms that send,
after any renaming, every realizer of every meaning of the domain to a
realizer of the image of that meaning. -/
def Real : {k : Kind} → (A : Carrier k) → A.Val (S.shapes star) T.Cand → T.Cand
  | _, .prop, _ => T.codes
  | _, .rigid _, _ => T.sn
  | _, .num, v => numReal S star T v
  | _, @Carrier.arr _ .gen A B, φ =>
      KCand.pi T.shape T.reflects (point S star T.sn A) (Real A) fun v => Real B (φ v)
  | _, @Carrier.arr .gen .data A B, F =>
      KCand.pi T.shape T.reflects (point S star T.sn A) (Real A) fun _ => Real B (appGen F)
  | _, @Carrier.arr .data .data A B, F =>
      KCand.pi T.shape T.reflects (point S star T.sn A) (Real A) fun a =>
        Real B (appData F a)

/-- Girard's clause: the terms that send, after any renaming, every realizer of
every meaning of the carrier into the family's candidate at that meaning. -/
def Girard {k : Kind} (A : Carrier k) (φ : A.Val (S.shapes star) T.Cand → T.Cand) :
    T.Cand :=
  KCand.pi T.shape T.reflects (point S star T.sn A) (Real S star T A) φ

theorem mem_girard {k : Kind} (A : Carrier k) (φ : A.Val (S.shapes star) T.Cand → T.Cand)
    {n : Nat} {t : Tm Head n} :
    (Girard S star T A φ).mem t ↔
      ∀ (v : A.Val (S.shapes star) T.Cand) {m : Nat} (ρ : Ren n m) (u : Tm Head m),
        (Real S star T A v).mem u → (φ v).mem (.app (Presentation.rename ρ t) u) :=
  Iff.rfl

/-! ## The reading -/

/-- The candidate reading: codes mean Kripke candidates of realizers,
implication the function space, a quantifier Girard's clause, an equation the
identity candidate of the equality of the meanings, and a daimonic code the
strongly normalizing terms. -/
def candidateReading : Reading Head where
  toDataSetting := S.shapes star
  P := T.Cand
  impMeaning := KCand.arrow T.shape T.reflects
  allMeaning := fun A φ => Girard S star T A φ
  eqMeaning := fun _ v w => IdCand T.reflects (v = w)
  neutral := Daimonic S.roles star
  neutral_subst := fun σ daimonic => daimonic.subst σ
  neutralMeaning := T.sn
  meet := fun F => KCand.inter T.reflects F
  top := T.sn

variable {S star}

/-- The laws of the candidate reading: those of the setting with the daimon
rigid. -/
theorem candidateReading_laws (laws : S.Laws) (rigid : S.roles star = .rigid) :
    (candidateReading S star T).Laws where
  toDataLaws := laws.shapes rigid
  neutral_whnf := fun daimonic => (daimonic.neutral rigid).whnf laws.shape
  neutral_ne_imp := fun {_ _ p q} daimonic e => by
    have role : S.roles S.imp = .constructor 2 := laws.imp
    rcases Daimonic.constSpine (c := S.imp) (args := [p, q]) daimonic e with
      same | ⟨_, _, computes⟩
    · rw [same, rigid] at role
      cases role
    · rw [role] at computes
      cases computes
  neutral_ne_all := fun {_ _ f a _} daimonic carrier e => by
    have role : S.roles a = .constructor 1 := laws.all carrier
    rcases Daimonic.constSpine (c := a) (args := [f]) daimonic e with same | ⟨_, _, computes⟩
    · rw [same, rigid] at role
      cases role
    · rw [role] at computes
      cases computes
  neutral_ne_eq := fun {_ _ x y e' _} daimonic carrier e => by
    have role : S.roles e' = .constructor 2 := laws.eq carrier
    rcases Daimonic.constSpine (c := e') (args := [x, y]) daimonic e with
      same | ⟨_, _, computes⟩
    · rw [same, rigid] at role
      cases role
    · rw [role] at computes
      cases computes
  neutral_ne_var := fun daimonic => daimonic.ne_varSpine
  meet_const := fun f x all nonempty => by
    obtain ⟨i⟩ := nonempty
    refine KCand.ext fun t => ⟨fun h => ?_, fun h => ⟨x.sn h, fun j => ?_⟩⟩
    · have hi := h.2 i
      rwa [all i] at hi
    · rw [all j]
      exact h

end Realizers

end Realizability
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
