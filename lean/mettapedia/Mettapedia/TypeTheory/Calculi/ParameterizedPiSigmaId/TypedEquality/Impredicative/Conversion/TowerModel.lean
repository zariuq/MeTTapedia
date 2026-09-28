import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Coherence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Controls

/-!
# The conversion model of the universe tower

The universe tower `U₀ : U₁ : …` is a realizer side whose facts about weak-head
forms of types come from the one-sided model (`Tower.side`). With a value side
over the tower's rules, which compute nothing, reading codes of implication and
of a quantifier over codes, a type of numbers with constructors `zero` and
`suc`, and a fresh rigid daimon, it is a lawful conversion model (`Tower.model`,
`Tower.model_laws`). The interpretation of the conversion model, read there:

* the universe `U₀` is interpreted at level one by its universe pack, and at
  level zero by none (`Tower.U0_interp`, `Tower.U0_not_interp_zero`); its values
  are realized by the types, and `U₀` realizes itself as a value of `U₁` at
  `U₁` (`Tower.U0_types`), which `bot` does not relate (`Tower.U0_not_bot`);
  the identity function of `U₀` is related by `top` but not by the types
  (`Tower.types_not_id`);
* the tower declares no numbers, so a number is realized only by terms reaching
  neutral terms: its realizers are `bot` (`Tower.num_real_bot`);
* the daimon is a valid value of every interpreted type, and each variable
  realizes it (`Tower.star_reflects`);
* `holds (imp ⋆ ⋆)` and its decoding are related in the universe relation at
  every level (`Tower.holdsImp_related`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Conversion

open Normalization
open Consistency (Carrier World Truth Morph)
open Realizability (Daimonic HasShape)

namespace Tower

/-! ## The value side -/

/-- The type of numbers of the value side. -/
def numName : DeclName := `Conversion.Tower.num

/-- The constructor `zero` of the numbers. -/
def zeroName : DeclName := `Conversion.Tower.zero

/-- The constructor `suc` of the numbers. -/
def sucName : DeclName := `Conversion.Tower.suc

/-- The implication of codes. -/
def impName : DeclName := `Conversion.Tower.imp

/-- The quantifier over codes. -/
def allName : DeclName := `Conversion.Tower.all

/-- The type of codes. -/
def propName : DeclName := `Conversion.Tower.prop

/-- The decoder of codes. -/
def holdsName : DeclName := `Conversion.Tower.holds

/-- The daimon. -/
def daimonName : DeclName := `Conversion.Tower.daimon

/-- The roles of the value side: implication and the quantifier are
constructors, the numbers are an inductive type with constructors `zero` and
`suc`, and every other name is rigid. -/
def valueRoles : Roles Nat := fun name =>
  if name = impName then .constructor 2
  else if name = allName then .constructor 1
  else if name = numName then .inductive [(zeroName, []), (sucName, [.recursive])]
  else if name = zeroName then .constructor 0
  else if name = sucName then .constructor 1
  else .rigid

/-- The quantifier ranges over the carrier of codes. -/
def allCarrier (name : DeclName) : Option (Σ k, Carrier k) :=
  if name = allName then some ⟨.gen, .prop⟩ else none

theorem allCarrier_some {a : DeclName} {A : Σ k, Carrier k} (found : allCarrier a = some A) :
    a = allName ∧ A = ⟨.gen, .prop⟩ := by
  unfold allCarrier at found
  by_cases e : a = allName
  · rw [if_pos e] at found
    exact ⟨e, (Option.some.inj found).symm⟩
  · rw [if_neg e] at found
    cases found

/-- The value side: the tower's rules, which compute nothing, read with codes and
numbers. -/
def valueModel : Consistency.Model Nat Nat where
  rules := rules
  roles := valueRoles
  zero := zeroName
  suc := sucName
  imp := impName
  allCarrier := allCarrier
  eqCarrier := fun _ => none
  num := numName
  prop := propName
  holds := holdsName
  levels := levels

theorem valueModel_laws : valueModel.Laws where
  truth :=
    { shape :=
        { spine := fun step => (nomatch step), deterministic := fun step _ => (nomatch step) }
      zero := rfl
      suc := rfl
      imp := rfl
      all := fun found => by
        obtain ⟨rfl, -⟩ := allCarrier_some found
        rfl
      eq := fun found => by cases found
      impNotEq := rfl }
  num := rfl
  prop := rfl
  holds := rfl

/-- The only inductive type of the value side is the numbers. -/
theorem valueRoles_inductive {T : DeclName} {cs : List (DeclName × List (Field Nat))}
    (role : valueRoles T = .inductive cs) :
    T = numName ∧ cs = [(zeroName, []), (sucName, [.recursive])] := by
  unfold valueRoles at role
  by_cases hi : T = impName
  · rw [if_pos hi] at role
    cases role
  rw [if_neg hi] at role
  by_cases ha : T = allName
  · rw [if_pos ha] at role
    cases role
  rw [if_neg ha] at role
  by_cases hn : T = numName
  · rw [if_pos hn] at role
    exact ⟨hn, (Role.inductive.inj role).symm⟩
  rw [if_neg hn] at role
  by_cases hz : T = zeroName
  · rw [if_pos hz] at role
    cases role
  rw [if_neg hz] at role
  by_cases hs : T = sucName
  · rw [if_pos hs] at role
    cases role
  rw [if_neg hs] at role
  cases role

/-- The constructors the numbers list are declared as constructors. -/
theorem valueRoles_declared : ConstructorsDeclared valueRoles where
  arity := by
    intro T cs k fields role mem
    obtain ⟨rfl, rfl⟩ := valueRoles_inductive role
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · rfl
  distinct := by
    intro T cs role
    obtain ⟨rfl, rfl⟩ := valueRoles_inductive role
    decide

/-! ## The model -/

/-- **The conversion model of the universe tower**: the value side, its daimon,
and the tower as its realizer side. -/
def model : NModel Nat Nat where
  toModel := valueModel
  star := daimonName
  side := side

/-- **The conversion model of the universe tower is lawful.** -/
theorem model_laws : model.Laws where
  values := valueModel_laws
  star := rfl
  starNotProp := by decide
  starNotHolds := by decide
  declared := valueRoles_declared

/-- The decoders of the value side's codes. -/
def decoders : Decoders Nat where
  holds := holdsName
  imp := impName
  allCarrier := fun a => if a = allName then some (.const propName) else none
  eqCarrier := fun _ => none

/-- The decoders decode the value side's codes. -/
theorem decodes : Consistency.Decodes model.toModel decoders where
  holds := rfl
  imp := rfl
  all := fun {a} {T} found => by
    change (if a = allName then some (.const propName) else none) = some T at found
    by_cases e : a = allName
    · rw [if_pos e] at found
      subst e
      obtain rfl := (Option.some.inj found).symm
      exact ⟨.gen, .prop, rfl, .prop, rfl⟩
    · rw [if_neg e] at found
      cases found
  eq := fun found => by cases found

/-! ## Universes -/

/-- **`U₀` is interpreted at level one** by its universe pack over the
interpretation at level zero. -/
theorem U0_interp {n : Nat} (ξ : World model.reading n) :
    NInterp model 1 ξ (.head 0) (ValueSide.universePack model.value (NInterp model 0) ξ) :=
  ValueSide.InterpAt.sort (V := model.value) (u := 0) trivial Nat.zero_lt_one ξ

/-- **`U₀` is interpreted by no pack at level zero.** -/
theorem U0_not_interp_zero {n : Nat} (ξ : World model.reading n) (P : NPack model n) :
    ¬ NInterp model 0 ξ (.head 0) P := fun interp =>
  Nat.not_lt_zero _
    (ValueSide.InterpAt.univ_inv model_laws.value interp .refl (u := 0) trivial).1

/-- **`U₀` realizes itself as a value of `U₁`**, at the realizer type `U₁`. -/
theorem U0_types :
    ((ValueSide.universePack model.value (NInterp model 1) World.closed).real (.head 0)).rel
      .nil (.head 1) (.head 0) (.head 0) := by
  have typed : Typed rules (.nil : Ctx Nat 0) (.head 0) (.head 1) := .headType rfl
  exact ⟨⟨typed, typed, .refl typed⟩, ⟨_, .refl typed, .inl ⟨0, rfl⟩⟩,
    ⟨_, .refl typed, .inl ⟨0, rfl⟩⟩⟩

/-- **`bot` does not relate `U₀`**: a universe is no neutral term. -/
theorem U0_not_bot : ¬ (ECand.bot side).rel .nil (.head 1) (.head 0) (.head 0) := by
  rintro ⟨w, -, r, -, nw, -⟩
  obtain rfl := WhRed.eq_of_whnf (S := side.toSetting) (head_whnf shape 0) r.red
  exact nw.not_former.1 0 rfl

/-- The identity function of `U₀`. -/
theorem id_typed : Typed rules (.nil : Ctx Nat 0) (.lam (.var 0)) (.pi (.head 0) (.head 0)) :=
  .lamIntro (.piForm (.headType rfl) trivial (.headType rfl) trivial rfl) trivial (Derivable.var 0)

/-- **`top` relates the identity function of `U₀`, and the types do not**: it
reaches no weak-head form of a type. -/
theorem types_not_id :
    (ECand.top side).rel .nil (.pi (.head 0) (.head 0)) (.lam (.var 0)) (.lam (.var 0)) ∧
      ¬ (ECand.types side).rel .nil (.pi (.head 0) (.head 0)) (.lam (.var 0)) (.lam (.var 0)) := by
  refine ⟨⟨id_typed, id_typed, .refl id_typed⟩, ?_⟩
  rintro ⟨-, ⟨w, r, form⟩, -⟩
  obtain rfl := WhRed.eq_of_whnf (S := side.toSetting) (lam_whnf shape (.var 0)) r.red
  rcases form with ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, e⟩ | neutral |
    ⟨_, _, _, e⟩
  · cases e
  · cases e
  · cases e
  · cases e
  · exact neutral.ne_lam rfl
  · cases e

/-! ## Numbers -/

/-- **The tower declares no numbers, so a number is realized by `bot`**: its
realizers relate only terms reaching neutral terms. -/
theorem num_real_bot {n : Nat} {a : Tm Nat n} {s : StrongNormalization.NumShape}
    (shape : HasShape model.toSetting model.star a s) {m : Nat} (Δ : Ctx Nat m)
    (A t t' : Tm Nat m) :
    ((ValueSide.numIndPack model.value n).real a).rel Δ A t t' ↔
      (ECand.bot side).rel Δ A t t' := by
  have e : ((ValueSide.numIndPack model.value n).real a : ECand side) =
      ((ecandAlgebra side).numReal numName zeroName sucName s : ECand side) :=
    ValueSide.numIndPack_real_of_shape model_laws.value shape
  rw [e]
  cases s with
  | zero => exact ⟨fun h => h.elim id fun ⟨_, _, _, _, role, _⟩ => (nomatch role), .inl⟩
  | suc s => exact ⟨fun h => h.elim id fun ⟨_, _, _, _, role, _⟩ => (nomatch role), .inl⟩
  | star => exact Iff.rfl

/-! ## The daimon -/

/-- **The daimon is a valid value of every interpreted type, and each variable
realizes it.** -/
theorem star_reflects {l n : Nat} {ξ : World model.reading n} {A : Tm Nat n} {P : NPack model n}
    (interp : NInterp model l ξ A P) {m : Nat} {Δ : Ctx Nat m} {B : Tm Nat m} (i : Fin m)
    (typing : Typed rules Δ (.var i) B) :
    P.Val (.const daimonName) ∧
      P.Related (.const daimonName) (.const daimonName) Δ B (.var i) (.var i) :=
  ⟨(NInterp.reflect model_laws interp).1, NInterp.reflect_var model_laws interp i typing⟩

/-! ## Decoder coherence -/

/-- The daimon is a neutral code with the neutral meaning. -/
theorem star_truth {n : Nat} (ξ : World model.reading n) :
    Truth model.reading ξ (.const daimonName) (ECand.top side) :=
  .neutral .refl .star

/-- **`holds (imp ⋆ ⋆)` and its decoding are related in the universe relation**
at every level: one pack and one shape at every world reached by a morphism. -/
theorem holdsImp_related (l : Nat) {n : Nat} (ξ : World model.reading n) :
    (ValueSide.universePack model.value (NInterp model l) ξ).rel
      (.app (.const holdsName)
        (.app (.app (.const impName) (.const daimonName)) (.const daimonName)))
      (.pi (.app (.const holdsName) (.const daimonName))
        (.app (.const holdsName) (Presentation.rename wk (.const daimonName)))) := by
  have hx : NInterp model l ξ
      (.app (.const holdsName)
        (.app (.app (.const impName) (.const daimonName)) (.const daimonName)))
      (ValueSide.holdsPack _ n ((ecandAlgebra side).arrow (ECand.top side) (ECand.top side))) :=
    ValueSide.SInterp.holds .refl (.imp .refl (star_truth ξ) (star_truth ξ))
  intro m ξ' ρ w
  exact NInterp.decoder_related model_laws decodes
    (.imp (D := decoders) (.const daimonName) (.const daimonName)) hx w

end Tower

end Conversion
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
