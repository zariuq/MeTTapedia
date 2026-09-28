import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.DecoderComputation

/-!
# The package of proposition codes

The impredicative proposition family of the native proof packages, over any
universe structure with a designated universe of proofs `U`:

* a type `prop` of codes in `U`;
* the decoder `holds : prop → U`;
* implication `imp : prop → prop → prop`;
* a quantifier `all@A : (A → prop) → prop` for each admitted closed carrier
  `A`, which may be `prop` itself;
* under the identity reading, an equation code `eq@A : A → A → prop` for each
  admitted closed carrier.

The admitted instances are given by tables from names to carriers, so a
package may admit infinitely many, for instance one at every simple type.

Codes decode by `decoderComputation`. The package extends a base package (the
tower with its declared data, recursors and definitions) whose declarations
do not use the code constants.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative

open Normalization

/-- The names of a package of proposition codes, with the closed carriers of
its quantifier and equation instances. -/
structure Codes (Head : Type) where
  /-- The universe of proof types, where `prop` lives and `holds` lands. -/
  proofs : Head
  prop : DeclName
  holds : DeclName
  imp : DeclName
  quantifiers : DeclName → Option (Tm Head 0)
  equations : DeclName → Option (Tm Head 0)
  identity : Bool

namespace Codes

variable {Head : Type} (K : Codes Head)

/-- The type of codes, in any context. -/
abbrev propT {n : Nat} : Tm Head n := .const K.prop

/-- The decoder applied to a code. -/
abbrev holdsOf {n : Nat} (c : Tm Head n) : Tm Head n := .app (.const K.holds) c

/-- Implication of two codes. -/
abbrev impOf {n : Nat} (p q : Tm Head n) : Tm Head n := .app (.app (.const K.imp) p) q

def holdsType : Tm Head 0 := .pi K.propT (.head K.proofs)

def impType : Tm Head 0 := .pi K.propT (.pi K.propT K.propT)

/-- The type of the quantifier over a closed carrier `A`: `(A → prop) → prop`. -/
def allType (A : Tm Head 0) : Tm Head 0 := .pi (.pi A K.propT) K.propT

/-- The type of the equation code at a closed carrier `A`: `A → A → prop`. -/
def eqType (A : Tm Head 0) : Tm Head 0 := .pi A (.pi (Presentation.rename wk A) K.propT)

/-- The equation instances that decode: all of them under the identity
reading, none otherwise. -/
def equationCarrier (e : DeclName) : Option (Tm Head 0) :=
  if K.identity then K.equations e else none

/-- The declared type of a code constant. -/
def codeType (c : DeclName) : Option (Tm Head 0) :=
  if c = K.prop then some (.head K.proofs)
  else if c = K.holds then some K.holdsType
  else if c = K.imp then some K.impType
  else match K.quantifiers c with
    | some A => some (K.allType A)
    | none => (K.equationCarrier c).map K.eqType

/-- The decoders of the package. -/
def decoders : Decoders Head where
  holds := K.holds
  imp := K.imp
  allCarrier := K.quantifiers
  eqCarrier := K.equationCarrier

/-- The base package extended by the code constants and their decoding. -/
def extend (base : Rules Head) : Rules Head :=
  { base with
    constantType := fun c => (K.codeType c).orElse fun _ => base.constantType c
    computation := RootComputation.union base.computation (decoderComputation K.decoders) }

theorem extend_decoder_step (base : Rules Head) {n : Nat} {l r : Tm Head n}
    (step : DecoderStep K.decoders l r) : (K.extend base).computation.step l r :=
  .inr step

theorem extend_base_step (base : Rules Head) {n : Nat} {l r : Tm Head n}
    (step : base.computation.step l r) : (K.extend base).computation.step l r :=
  .inl step

@[simp] theorem codeType_prop : K.codeType K.prop = some (.head K.proofs) := by
  simp [codeType]

theorem codeType_holds (distinct : K.holds ≠ K.prop) : K.codeType K.holds = some K.holdsType := by
  simp [codeType, distinct]

theorem codeType_imp (distinct : K.imp ≠ K.prop ∧ K.imp ≠ K.holds) :
    K.codeType K.imp = some K.impType := by
  simp [codeType, distinct.1, distinct.2]

theorem codeType_all {a : DeclName} {A : Tm Head 0}
    (distinct : a ≠ K.prop ∧ a ≠ K.holds ∧ a ≠ K.imp) (carrier : K.quantifiers a = some A) :
    K.codeType a = some (K.allType A) := by
  simp [codeType, distinct.1, distinct.2.1, distinct.2.2, carrier]

theorem extend_constantType_of_code (base : Rules Head) {c : DeclName} {T : Tm Head 0}
    (code : K.codeType c = some T) : (K.extend base).constantType c = some T := by
  simp [extend, code, Option.orElse]

/-! ## Root shape of an extended package -/

section Shape

variable {base : Rules Head} {baseRoles roles : Roles Head}

/-- Roles that keep every role of the base that is not rigid. -/
def RolesKeep (baseRoles roles : Roles Head) : Prop :=
  ∀ {c : DeclName} {role : Role Head}, baseRoles c = role → role ≠ .rigid → roles c = role

theorem canonical_of_keep (keep : RolesKeep baseRoles roles) {n : Nat} {a : Tm Head n}
    (canonical : Canonical baseRoles a) : Canonical roles a := by
  rcases canonical with refl | ⟨k, arity, args, role, rfl⟩
  · exact .inl refl
  · exact .inr ⟨k, arity, args, keep role nofun, rfl⟩

/-- A package extended by codes, with roles that keep the base's non-rigid
roles and give the decoder and the codes their decoding roles, has root shape
when the base does, inspects only constructor forms, and has a rigid decoder.

The base must inspect only constructor forms: a head-form inspection accepts
spines of rigid constants, and the extension gives the rigid decoder a
computing role, so such an acceptance is not kept
(`HeadFormControls.rootShape_not_kept`). -/
theorem extend_rootShape (shape : RootShape base baseRoles)
    (onlyConstructors : ∀ {c : DeclName} {arity : Nat} {inspect : InspectTree},
      baseRoles c = .computes arity inspect → inspect.OnlyConstructors)
    (keep : RolesKeep baseRoles roles) (holdsRigid : baseRoles K.holds = .rigid)
    (decoderRoles : DecoderRoles roles K.decoders)
    (impNotEquation : K.decoders.eqCarrier K.decoders.imp = none) :
    RootShape (K.extend base) roles := by
  have baseSpine : SpineShaped roles base.computation := by
    intro n t u step
    obtain ⟨c, arity, scrutinee, args, role, rfl, length, accepts⟩ := shape.spine step
    exact ⟨c, arity, scrutinee, args, keep role nofun, rfl, length,
      accepts.of_constructors (fun constructor => keep constructor nofun) (onlyConstructors role)⟩
  have notDecoding : ∀ {n : Nat} {t u u' : Tm Head n}, base.computation.step t u →
      DecoderStep K.decoders t u' → False := by
    intro n t u u' step decoding
    obtain ⟨c, arity, scrutinee, args, role, rfl, -⟩ := shape.spine step
    obtain ⟨args', same⟩ := decoderComputation_headed K.decoders decoding
    obtain ⟨rfl, -⟩ := appSpine_const_injective same
    exact nomatch holdsRigid.symm.trans role
  refine ⟨fun step => ?_, fun step step' => ?_⟩
  · rcases step with step | step
    · exact baseSpine step
    · exact decoderComputation_spine decoderRoles step
  · rcases step with step | step <;> rcases step' with step' | step'
    · exact shape.deterministic step step'
    · exact (notDecoding step step').elim
    · exact (notDecoding step' step).elim
    · exact decoderComputation_deterministic impNotEquation step' step

end Shape

end Codes

end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
