import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeRelatorCompatibility

/-!
# Constructorwise denotation of the declared native HOL fragment

The judgments below interpret existing scoped native terms, inspecting their
variables, declarations, applications, lambdas and simple-type Pi codes. They
do not decode a native term into a source HOL term. Source representation is
connected to this independently specified judgment by a theorem.
Denotation is coherent at a fixed typed context and type, even when the raw
syntax admits different hidden application-domain typings.

The supplied Henkin model interprets the retained HOL declarations. This is a
fragment interpretation, not an interpretation of arbitrary native universes,
dependent products, identity elimination, native lists or wire data. It does
not identify HOL satisfaction with a dependent proof inhabitant. Scopes and
supported HOL types are unrestricted; native universe levels are not collapsed
into a two-level model.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace NativeHOLFragmentDenotation

open Presentation Presentation.FormationSensitive
open FormationSensitiveHOLInterface FormationSensitiveHOLUniformList
open Mettapedia.Logic HOL.UniformListInduction

universe w

/-- The actual native type constructors of the interpreted simple fragment.
The Pi codomain has its real extended native scope. -/
inductive TypeMeaning : {n : Nat} → Tower.Tm n → HOL.Ty BaseSort → Prop where
  | proposition {n : Nat} : TypeMeaning (n := n) (.const `HOLUniformList.prop) .prop
  | base {n : Nat} (sort : BaseSort) : TypeMeaning (n := n) (.const (baseName sort)) (.base sort)
  | pi {n : Nat} {domain : Tower.Tm n} {codomain : Tower.Tm (n + 1)}
      {a b : HOL.Ty BaseSort} :
      TypeMeaning domain a → TypeMeaning codomain b →
        TypeMeaning (.pi domain codomain) (.arr a b)

theorem typeAt_meaning (n : Nat) (type : HOL.Ty BaseSort) :
    TypeMeaning (typeAt types n type) type := by
  induction type generalizing n with
  | prop => exact .proposition
  | base sort => exact .base sort
  | arr a b ia ib => exact .pi (ia n) (ib (n + 1))

theorem TypeMeaning.code {n : Nat} {raw : Tower.Tm n} {type : HOL.Ty BaseSort}
    (meaning : TypeMeaning raw type) : raw = typeAt types n type := by
  induction meaning with
  | proposition => rfl
  | base sort => rfl
  | pi _ _ ia ib => simp only [typeAt, ia, ib]

theorem typeAt_injective (n : Nat) : Function.Injective (typeAt types n) := by
  intro left
  induction left generalizing n with
  | prop =>
      intro right same
      cases right with
      | prop => rfl
      | base sort => cases sort <;>
          simp [typeAt, types, liftClosed, Presentation.rename, baseName] at same
      | arr a b => cases same
  | base sort =>
      intro right same
      cases right with
      | prop => cases sort <;>
          simp [typeAt, types, liftClosed, Presentation.rename, baseName] at same
      | base other => cases sort <;> cases other <;>
          simp_all [typeAt, types, liftClosed, Presentation.rename, baseName]
      | arr a b => cases same
  | arr a b ia ib =>
      intro right same
      cases right with
      | prop => cases same
      | base sort => cases same
      | arr c d =>
          have parts := Tm.pi.inj same
          exact congrArg₂ HOL.Ty.arr (ia n parts.1) (ib (n + 1) parts.2)

theorem TypeMeaning.deterministic {n : Nat} {raw : Tower.Tm n}
    {left right : HOL.Ty BaseSort}
    (first : TypeMeaning raw left) (second : TypeMeaning raw right) : left = right :=
  typeAt_injective n (first.code.symm.trans second.code)

theorem TypeMeaning.rename {n m : Nat} {raw : Tower.Tm n} {type : HOL.Ty BaseSort}
    (meaning : TypeMeaning raw type) (rho : Ren n m) :
    TypeMeaning (Presentation.rename rho raw) type := by
  rw [meaning.code, typeAt_rename]
  exact typeAt_meaning m type

theorem TypeMeaning.substitute {n m : Nat} {raw : Tower.Tm n} {type : HOL.Ty BaseSort}
    (meaning : TypeMeaning raw type) (sigma : Sub Tower.Head n m) :
    TypeMeaning (Presentation.subst sigma raw) type := by
  rw [meaning.code, typeAt_subst]
  exact typeAt_meaning m type

theorem TypeMeaning.formed {n : Nat} {raw : Tower.Tm n} {type : HOL.Ty BaseSort}
    (meaning : TypeMeaning raw type) (gamma : Tower.Ctx n) :
    Typing HOLNativeRelatorCompatibility.rules gamma raw (sortTm Tower.zero) := by
  rw [meaning.code]
  exact HOLNativeRelatorCompatibility.hol_typing (simple_type_formed type gamma)

/-- A compositional semantic judgment on the actual native term. Its value is
a function of the existing typed valuation, so binding is explicit. The two
polymorphic logical declarations are interpreted only after their actual
native type argument has a `TypeMeaning` derivation. -/
inductive Denotes (model : HOL.HenkinModel.{0, 0, w} BaseSort Symbol) :
    {gamma : HOL.Ctx BaseSort} → {type : HOL.Ty BaseSort} → Tower.Tm gamma.length →
      (model.Valuation gamma → HOL.Ty.denote model.Carrier type) → Prop where
  | index {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
      (index : HOL.Var gamma type) :
      Denotes model (.var (variableIndex index)) (fun valuation => valuation index)
  | constant {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
      (symbol : Symbol type) :
      Denotes model (gamma := gamma) (.const (symbolName symbol)) (fun _ => model.constDen symbol)
  | implication {gamma : HOL.Ctx BaseSort} :
      Denotes model (gamma := gamma) (type := .arr .prop (.arr .prop .prop))
        (.const `HOLUniformList.implication) (fun _ p q => ULift.up (p.down → q.down))
  | universal {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
      {rawType : Tower.Tm gamma.length} (formed : TypeMeaning rawType type) :
      Denotes model (type := .arr (.arr type .prop) .prop)
        (.app (.const `HOLUniformList.universal) rawType)
        (fun _ predicate => ULift.up (∀ x, model.adm type x → (predicate x).down))
  | equality {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
      {rawType : Tower.Tm gamma.length} (formed : TypeMeaning rawType type) :
      Denotes model (type := .arr type (.arr type .prop))
        (.app (.const `HOLUniformList.equality) rawType)
        (fun _ left right => ULift.up (model.Eqv type left right))
  | application {gamma : HOL.Ctx BaseSort} {a b : HOL.Ty BaseSort}
      {function argument : Tower.Tm gamma.length}
      {functionMeaning : model.Valuation gamma → HOL.Ty.denote model.Carrier (.arr a b)}
      {argumentMeaning : model.Valuation gamma → HOL.Ty.denote model.Carrier a} :
      Denotes model function functionMeaning → Denotes model argument argumentMeaning →
        Denotes model (.app function argument)
          (fun valuation => functionMeaning valuation (argumentMeaning valuation))
  | abstraction {gamma : HOL.Ctx BaseSort} {a b : HOL.Ty BaseSort}
      {body : Tower.Tm (gamma.length + 1)}
      {bodyMeaning : model.Valuation (a :: gamma) → HOL.Ty.denote model.Carrier b} :
      Denotes model (gamma := a :: gamma) body bodyMeaning →
        Denotes model (type := .arr a b) (.lam body)
          (fun valuation x => bodyMeaning (model.extend valuation x))

variable {model : HOL.HenkinModel.{0, 0, w} BaseSort Symbol}

/-- Every constructed native value is the value of some intrinsic HOL term.
This is derived from the native semantic judgment, not used to define it.
Logical declaration heads have eta-expanded source witnesses; their native
representation need not equal the original raw declaration application. -/
theorem Denotes.source_denotation {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
    {raw : Tower.Tm gamma.length}
    {value : model.Valuation gamma → HOL.Ty.denote model.Carrier type}
    (meaning : Denotes model raw value) :
    ∃ term : HOL.Term Symbol gamma type, ∀ valuation, value valuation = model.denote term valuation := by
  induction meaning with
  | index index => exact ⟨.var index, fun _ => rfl⟩
  | constant symbol => exact ⟨.const symbol, fun _ => rfl⟩
  | implication =>
      exact ⟨.lam (.lam (.imp (.var (.vs .vz)) (.var .vz))), fun _ => rfl⟩
  | universal _ =>
      exact ⟨.lam (.all (.app (.var (.vs .vz)) (.var .vz))), fun _ => rfl⟩
  | equality _ =>
      exact ⟨.lam (.lam (.eq (.var (.vs .vz)) (.var .vz))), fun _ => rfl⟩
  | application _ _ functionInduction argumentInduction =>
      obtain ⟨function, functionMeaning⟩ := functionInduction
      obtain ⟨argument, argumentMeaning⟩ := argumentInduction
      refine ⟨.app function argument, ?_⟩
      intro valuation
      simp only [HOL.HenkinModel.denote, HOL.PreModel.denote,
        functionMeaning valuation, argumentMeaning valuation]
  | abstraction _ bodyInduction =>
      obtain ⟨body, bodyMeaning⟩ := bodyInduction
      refine ⟨.lam body, ?_⟩
      intro valuation
      funext x
      exact bodyMeaning (model.extend valuation x)

/-- Henkin closure, without full domains, makes every interpreted native
value admissible whenever its actual ambient valuation is admissible. -/
theorem Denotes.admissible {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
    {raw : Tower.Tm gamma.length}
    {value : model.Valuation gamma → HOL.Ty.denote model.Carrier type}
    (meaning : Denotes model raw value) {valuation : model.Valuation gamma}
    (admissible : model.ValuationAdmissible valuation) :
    model.adm type (value valuation) := by
  obtain ⟨term, valueEquation⟩ := meaning.source_denotation
  rw [valueEquation valuation]
  exact model.denote_admissible admissible term

/-- Componentwise interpretations of an actual native substitution ensure
that its semantic environment preserves admissible valuations. -/
theorem interpreted_environment_admissible {gamma delta : HOL.Ctx BaseSort}
    (sigma : Sub Tower.Head gamma.length delta.length)
    (environment : model.Valuation delta → model.Valuation gamma)
    (components : ∀ {type} (index : HOL.Var gamma type),
      Denotes model (sigma (variableIndex index)) (fun valuation => environment valuation index))
    {valuation : model.Valuation delta} (admissible : model.ValuationAdmissible valuation) :
    model.ValuationAdmissible (environment valuation) := by
  intro type index
  exact (components index).admissible admissible

theorem Denotes.typed {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
    {raw : Tower.Tm gamma.length}
    {value : model.Valuation gamma → HOL.Ty.denote model.Carrier type}
    (meaning : Denotes model raw value) :
    Typing FormationSensitiveHOLUniformList.rules (context types gamma) raw
      (typeAt types gamma.length type) := by
  induction meaning with
  | index index =>
      simpa only [context_lookup] using
        Typing.var (R := FormationSensitiveHOLUniformList.rules)
          (Γ := context types _) (variableIndex index)
  | constant symbol =>
      simpa only [FormationSensitiveHOLUniformList.rules, signature,
        liftClosed, Presentation.rename, typeAt_rename] using
        closed_typed (signature.constant_typed symbol) (context types _)
  | implication =>
      simpa only [FormationSensitiveHOLUniformList.rules, signature,
        liftClosed, Presentation.rename, typeAt_rename] using
        closed_typed signature.implication_typed (context types _)
  | @universal gamma type rawType formed =>
      rw [formed.code]
      simpa only [FormationSensitiveHOLUniformList.universal,
        liftClosed, Presentation.rename, typeAt_rename] using
        closed_typed (universal_typed type) (context types gamma)
  | @equality gamma type rawType formed =>
      rw [formed.code]
      simpa only [FormationSensitiveHOLUniformList.equality,
        liftClosed, Presentation.rename, typeAt_rename] using
        closed_typed (equality_typed type) (context types gamma)
  | application _ _ functionTyped argumentTyped =>
      simpa only [inst0, typeAt_subst] using Typing.appElim functionTyped argumentTyped
  | @abstraction gamma a b body bodyMeaning _ bodyTyped =>
      exact .lamIntro (simple_type_formed (.arr a b) (context types gamma))
        (.sort Tower.zero) bodyTyped

/-- Semantic construction independently entails actual formation-sensitive
admission in the same HOL/wire/List/J rule package. -/
theorem Denotes.admitted {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
    {raw : Tower.Tm gamma.length}
    {value : model.Valuation gamma → HOL.Ty.denote model.Carrier type}
    (meaning : Denotes model raw value) :
    Judgment HOLNativeRelatorCompatibility.rules (context types gamma) raw
      (typeAt types gamma.length type) :=
  HOLNativeRelatorCompatibility.hol_judgment
    ⟨context_formed signature gamma, meaning.typed⟩

/-- Actual native renaming precomposes the interpretation with the matching
typed valuation map, including beneath native lambdas. -/
theorem Denotes.rename {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
    {raw : Tower.Tm gamma.length}
    {value : model.Valuation gamma → HOL.Ty.denote model.Carrier type}
    (meaning : Denotes model raw value) {delta : HOL.Ctx BaseSort}
    (rho : HOL.Rename BaseSort gamma delta) (rawRenaming : Ren gamma.length delta.length)
    (compatible : ∀ {a} (index : HOL.Var gamma a),
      variableIndex (rho index) = rawRenaming (variableIndex index)) :
    Denotes model (Presentation.rename rawRenaming raw)
      (fun valuation => value (HOL.Soundness.renameVal model rho valuation)) := by
  induction meaning generalizing delta with
  | index index =>
      simpa only [Presentation.rename, ← compatible index, HOL.Soundness.renameVal] using
        Denotes.index (model := model) (rho index)
  | constant symbol => exact .constant symbol
  | implication => exact .implication
  | universal formed => exact .universal (formed.rename rawRenaming)
  | equality formed => exact .equality (formed.rename rawRenaming)
  | application _ _ functionInduction argumentInduction =>
      exact .application (functionInduction rho rawRenaming compatible)
        (argumentInduction rho rawRenaming compatible)
  | @abstraction gamma a b body bodyMeaning _ inductionHypothesis =>
      have lifted : ∀ {type} (index : HOL.Var (a :: gamma) type),
          variableIndex (HOL.Rename.lift rho index) =
            liftRen rawRenaming (variableIndex index) := by
        intro type index
        cases index with
        | vz => rfl
        | vs prior => simpa only [HOL.Rename.lift, variableIndex, liftRen,
            Fin.cases_succ] using congrArg Fin.succ (compatible prior)
      have interpreted := Denotes.abstraction
        (inductionHypothesis (HOL.Rename.lift rho) (liftRen rawRenaming) lifted)
      simpa only [Presentation.rename, HOL.Soundness.renameVal_lift] using interpreted

/-- Extend a semantic environment transformation by retaining the newest
variable and applying the old transformation to the remaining valuation. -/
def liftEnvironment {gamma delta : HOL.Ctx BaseSort} {a : HOL.Ty BaseSort}
    (environment : model.Valuation delta → model.Valuation gamma)
    (valuation : model.Valuation (a :: delta)) : model.Valuation (a :: gamma) :=
  model.extend (environment (HOL.Soundness.renameVal model HOL.Rename.weaken valuation))
    (valuation .vz)

theorem liftEnvironment_extend {gamma delta : HOL.Ctx BaseSort} {a : HOL.Ty BaseSort}
    (environment : model.Valuation delta → model.Valuation gamma)
    (valuation : model.Valuation delta) (x : HOL.Ty.denote model.Carrier a) :
    (liftEnvironment environment (model.extend valuation x) : model.Valuation (a :: gamma)) =
      (model.extend (environment valuation) x : model.Valuation (a :: gamma)) := by
  simp only [liftEnvironment, HOL.Soundness.renameVal_weaken_extend,
    HOL.HenkinModel.extend, HOL.PreModel.extend]

theorem lifted_components {gamma delta : HOL.Ctx BaseSort} {a : HOL.Ty BaseSort}
    (sigma : Sub Tower.Head gamma.length delta.length)
    (environment : model.Valuation delta → model.Valuation gamma)
    (components : ∀ {type} (index : HOL.Var gamma type),
      Denotes model (sigma (variableIndex index)) (fun valuation => environment valuation index)) :
    ∀ {type} (index : HOL.Var (a :: gamma) type),
      Denotes model (gamma := a :: delta) (liftSub sigma (variableIndex index))
        (fun valuation => liftEnvironment environment valuation index) := by
  intro type index
  cases index with
  | vz => exact .index .vz
  | vs prior =>
      simpa only [variableIndex, liftSub, Fin.cases_succ, liftEnvironment,
        HOL.HenkinModel.extend, HOL.PreModel.extend] using
        (components prior).rename (HOL.Rename.weaken (σ := a)) wk (fun _ => rfl)

/-- Native substitution is semantic environment substitution. The premise
interprets the actual native substitution components; it does not require a
source HOL substitution or a source-representation witness. -/
theorem Denotes.substitute {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
    {raw : Tower.Tm gamma.length}
    {value : model.Valuation gamma → HOL.Ty.denote model.Carrier type}
    (meaning : Denotes model raw value) {delta : HOL.Ctx BaseSort}
    (sigma : Sub Tower.Head gamma.length delta.length)
    (environment : model.Valuation delta → model.Valuation gamma)
    (components : ∀ {a} (index : HOL.Var gamma a),
      Denotes model (sigma (variableIndex index)) (fun valuation => environment valuation index)) :
    Denotes model (Presentation.subst sigma raw) (fun valuation => value (environment valuation)) := by
  induction meaning generalizing delta with
  | index index => exact components index
  | constant symbol => exact .constant symbol
  | implication => exact .implication
  | universal formed => exact .universal (formed.substitute sigma)
  | equality formed => exact .equality (formed.substitute sigma)
  | application _ _ functionInduction argumentInduction =>
      exact .application (functionInduction sigma environment components)
        (argumentInduction sigma environment components)
  | @abstraction gamma a b body bodyMeaning _ inductionHypothesis =>
      have interpreted := Denotes.abstraction
        (inductionHypothesis (delta := a :: delta) (liftSub sigma) (liftEnvironment environment)
          (lifted_components sigma environment components))
      simpa only [Presentation.subst, liftEnvironment_extend] using interpreted

/-- The ordinary native `inst0` operation computes the denotation of a body
in the valuation extended by its actual interpreted argument. -/
theorem Denotes.instantiate {gamma : HOL.Ctx BaseSort} {a b : HOL.Ty BaseSort}
    {body : Tower.Tm (gamma.length + 1)} {argument : Tower.Tm gamma.length}
    {bodyValue : model.Valuation (a :: gamma) → HOL.Ty.denote model.Carrier b}
    {argumentValue : model.Valuation gamma → HOL.Ty.denote model.Carrier a}
    (bodyMeaning : Denotes model (gamma := a :: gamma) body bodyValue)
    (argumentMeaning : Denotes model argument argumentValue) :
    Denotes model (inst0 argument body)
      (fun valuation => bodyValue (model.extend valuation (argumentValue valuation))) := by
  apply bodyMeaning.substitute (delta := gamma) (subst0 argument)
    (fun valuation => model.extend valuation (argumentValue valuation))
  intro type index
  cases index with
  | vz => exact argumentMeaning
  | vs prior => exact .index prior

/-- A real native beta step, source admission and target admission share one
denotation. The separate coherence theorem also identifies other denotations
of these terms at the same typed context and type. -/
theorem native_beta_square {gamma : HOL.Ctx BaseSort} {a b : HOL.Ty BaseSort}
    {body : Tower.Tm (gamma.length + 1)} {argument : Tower.Tm gamma.length}
    {bodyValue : model.Valuation (a :: gamma) → HOL.Ty.denote model.Carrier b}
    {argumentValue : model.Valuation gamma → HOL.Ty.denote model.Carrier a}
    (bodyMeaning : Denotes model (gamma := a :: gamma) body bodyValue)
    (argumentMeaning : Denotes model argument argumentValue) :
    Step HOLNativeRelatorCompatibility.rules.headEq (.app (.lam body) argument)
        (inst0 argument body) HOLNativeRelatorCompatibility.rules.computation ∧
      Denotes model (.app (.lam body) argument)
        (fun valuation => bodyValue (model.extend valuation (argumentValue valuation))) ∧
      Denotes model (inst0 argument body)
        (fun valuation => bodyValue (model.extend valuation (argumentValue valuation))) ∧
      Judgment HOLNativeRelatorCompatibility.rules (context types gamma)
        (inst0 argument body) (typeAt types gamma.length b) :=
  ⟨.betaPi body argument, .application (.abstraction bodyMeaning) argumentMeaning,
    bodyMeaning.instantiate argumentMeaning, (bodyMeaning.instantiate argumentMeaning).admitted⟩

private theorem application_result {n : Nat} {function argument : Option (Tower.Tm n)}
    {result : Tower.Tm n} :
    (do let f ← function; let a ← argument; pure (Tm.app f a)) = some result ↔
      ∃ f a, function = some f ∧ argument = some a ∧ result = .app f a := by
  cases function <;> cases argument <;> simp [eq_comm]

/-- Representation connects to constructorwise native semantics by induction
on the actual source syntax. The native judgment itself has no source-term
or source-representation premise. -/
theorem representation_square {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
    (term : HOL.Term Symbol gamma type) {raw : Tower.Tm gamma.length}
    (represented : represent signature term = some raw) :
    Denotes model raw (fun valuation => model.denote term valuation) := by
  induction term with
  | var index =>
      cases Option.some.inj represented
      exact .index index
  | const symbol =>
      cases Option.some.inj represented
      exact .constant symbol
  | app function argument functionInduction argumentInduction =>
      obtain ⟨f, a, hf, ha, rfl⟩ := application_result.mp represented
      exact .application (functionInduction hf) (argumentInduction ha)
  | lam body inductionHypothesis =>
      obtain ⟨bodyCode, bodyRepresented, rfl⟩ := Option.map_eq_some_iff.mp represented
      exact .abstraction (inductionHypothesis bodyRepresented)
  | imp premise conclusion premiseInduction conclusionInduction =>
      obtain ⟨function, conclusionCode, functionRepresented, conclusionRepresented, rfl⟩ :=
        application_result.mp represented
      obtain ⟨head, premiseCode, headRepresented, premiseRepresented, rfl⟩ :=
        application_result.mp functionRepresented
      cases Option.some.inj headRepresented
      exact .application (a := .prop) (b := .prop)
        (.application (a := .prop) (b := .arr .prop .prop)
          (Denotes.implication (model := model)) (premiseInduction premiseRepresented))
        (conclusionInduction conclusionRepresented)
  | @all type gamma body inductionHypothesis =>
      obtain ⟨head, argument, headRepresented, argumentRepresented, rfl⟩ :=
        application_result.mp represented
      cases Option.some.inj headRepresented
      obtain ⟨bodyCode, bodyRepresented, rfl⟩ := Option.map_eq_some_iff.mp argumentRepresented
      have meaning := Denotes.application (a := .arr type .prop) (b := .prop)
        (Denotes.universal (model := model)
        (gamma := gamma) (typeAt_meaning gamma.length type))
        (Denotes.abstraction (inductionHypothesis bodyRepresented))
      simpa only [signature, FormationSensitiveHOLUniformList.universal,
        liftClosed, Presentation.rename, typeAt_rename, HOL.propTy,
        HOL.HenkinModel.denote, HOL.PreModel.denote] using meaning
  | @eq gamma type left right leftInduction rightInduction =>
      obtain ⟨function, rightCode, functionRepresented, rightRepresented, rfl⟩ :=
        application_result.mp represented
      obtain ⟨head, leftCode, headRepresented, leftRepresented, rfl⟩ :=
        application_result.mp functionRepresented
      cases Option.some.inj headRepresented
      have meaning := Denotes.application (a := type) (b := .prop)
        (Denotes.application (a := type) (b := .arr type .prop)
        (Denotes.equality (model := model) (gamma := gamma) (typeAt_meaning gamma.length type))
        (leftInduction leftRepresented)) (rightInduction rightRepresented)
      simpa only [signature, FormationSensitiveHOLUniformList.equality,
        liftClosed, Presentation.rename, typeAt_rename, HOL.propTy,
        HOL.HenkinModel.denote, HOL.PreModel.denote] using meaning
  | top | bot | «and» | «or» | «not» | ex => cases represented

/-- The three sides use actual source renaming, actual native renaming and
the same valuation transformation. -/
theorem representation_renaming_square {gamma delta : HOL.Ctx BaseSort}
    {type : HOL.Ty BaseSort} (term : HOL.Term Symbol gamma type)
    {raw : Tower.Tm gamma.length} (represented : represent signature term = some raw)
    (rho : HOL.Rename BaseSort gamma delta) (rawRenaming : Ren gamma.length delta.length)
    (compatible : ∀ {a} (index : HOL.Var gamma a),
      variableIndex (rho index) = rawRenaming (variableIndex index)) :
    represent signature (HOL.rename rho term) = some (Presentation.rename rawRenaming raw) ∧
      Denotes model (Presentation.rename rawRenaming raw)
        (fun valuation => model.denote term (HOL.Soundness.renameVal model rho valuation)) := by
  refine ⟨?_, (representation_square term represented).rename rho rawRenaming compatible⟩
  rw [represent_rename signature rho rawRenaming compatible, represented, Option.map_some]

/-- A represented source substitution and independently interpreted native
components meet at the real capture-avoiding native substitution operation. -/
theorem representation_substitution_square {gamma delta : HOL.Ctx BaseSort}
    {type : HOL.Ty BaseSort} (term : HOL.Term Symbol gamma type)
    {raw : Tower.Tm gamma.length} (represented : represent signature term = some raw)
    (sigma : HOL.Subst Symbol gamma delta)
    (rawSubstitution : Sub Tower.Head gamma.length delta.length)
    (compatible : ∀ {a} (index : HOL.Var gamma a),
      represent signature (sigma index) = some (rawSubstitution (variableIndex index))) :
    represent signature (HOL.subst sigma term) = some (Presentation.subst rawSubstitution raw) ∧
      Denotes model (Presentation.subst rawSubstitution raw)
        (fun valuation => model.denote term (HOL.Soundness.substVal model sigma valuation)) := by
  refine ⟨?_, (representation_square term represented).substitute rawSubstitution
    (HOL.Soundness.substVal model sigma)
      (fun index => representation_square (sigma index) (compatible index))⟩
  rw [represent_subst signature sigma rawSubstitution compatible, represented, Option.map_some]

/-! ## No invented declarations or unsupported type arguments -/

theorem Denotes.constant_origin {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
    {name : DeclName} {value : model.Valuation gamma → HOL.Ty.denote model.Carrier type}
    (meaning : Denotes model (.const name) value) :
    name = `HOLUniformList.implication ∨
      ∃ a, ∃ symbol : Symbol a, name = symbolName symbol := by
  cases meaning with
  | constant symbol => exact .inr ⟨_, symbol, rfl⟩
  | implication => exact .inl rfl

theorem missing_declaration_not_interpreted {gamma : HOL.Ctx BaseSort}
    {type : HOL.Ty BaseSort}
    (value : model.Valuation gamma → HOL.Ty.denote model.Carrier type) :
    ¬ Denotes model (.const `HOLUniformList.missingEquality) value := by
  intro meaning
  rcases meaning.constant_origin with impossible | ⟨a, symbol, impossible⟩
  · cases (by decide : (`HOLUniformList.missingEquality : DeclName) ≠
      `HOLUniformList.implication) impossible
  · cases symbol <;> simp [symbolName] at impossible

theorem unapplied_universal_not_interpreted {gamma : HOL.Ctx BaseSort}
    {type : HOL.Ty BaseSort}
    (value : model.Valuation gamma → HOL.Ty.denote model.Carrier type) :
    ¬ Denotes model (.const `HOLUniformList.universal) value := by
  intro meaning
  rcases meaning.constant_origin with impossible | ⟨a, symbol, impossible⟩
  · cases (by decide : (`HOLUniformList.universal : DeclName) ≠
      `HOLUniformList.implication) impossible
  · cases symbol <;> simp [symbolName] at impossible

/-- Supplying a native universe in place of a supported HOL type code cannot
acquire a universal-operator interpretation through an application rule. -/
theorem universe_argument_rejected {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
    (level : LevelExpr Nat)
    (value : model.Valuation gamma → HOL.Ty.denote model.Carrier type) :
    ¬ Denotes model (.app (.const `HOLUniformList.universal) (sortTm level)) value := by
  intro meaning
  generalize headEquation : (`HOLUniformList.universal : DeclName) = head at meaning
  cases meaning with
  | universal formed => cases formed
  | equality formed => cases formed
  | application function argument =>
      subst head
      exact unapplied_universal_not_interpreted _ function

/-- Every native level still has its genuine native successor formation,
while none is silently treated as one of the fragment's simple HOL codes. -/
theorem native_universes_outside_fragment {n : Nat} (gamma : Tower.Ctx n) (level : LevelExpr Nat) :
    Typing HOLNativeRelatorCompatibility.rules gamma (sortTm level) (sortTm (.succ level)) ∧
      ∀ type, ¬ TypeMeaning (n := n) (sortTm level) type := by
  refine ⟨.headType (.sort level), ?_⟩
  intro type impossible
  cases impossible

theorem native_identity_not_interpreted {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
    (carrier left right : Tower.Tm gamma.length)
    (value : model.Valuation gamma → HOL.Ty.denote model.Carrier type) :
    ¬ Denotes model (.id carrier left right) value := by
  intro impossible
  cases impossible

/-! ## Coherence without uniqueness of hidden application types -/

/-- Actual fragment syntax agrees while its ambient scope may differ. This
relation compares variable positions and native constructors, not typing
derivations or semantic values. -/
private inductive SameFragmentSyntax : {n m : Nat} → Tower.Tm n → Tower.Tm m → Prop where
  | index {n m : Nat} {left : Fin n} {right : Fin m} :
      left.val = right.val → SameFragmentSyntax (.var left) (.var right)
  | constant {n m : Nat} (name : DeclName) :
      SameFragmentSyntax (n := n) (m := m) (.const name) (.const name)
  | pi {n m : Nat} {a : Tower.Tm n} {b : Tower.Tm (n + 1)}
      {c : Tower.Tm m} {d : Tower.Tm (m + 1)} :
      SameFragmentSyntax a c → SameFragmentSyntax b d → SameFragmentSyntax (.pi a b) (.pi c d)
  | abstraction {n m : Nat} {left : Tower.Tm (n + 1)} {right : Tower.Tm (m + 1)} :
      SameFragmentSyntax left right → SameFragmentSyntax (.lam left) (.lam right)
  | application {n m : Nat} {f a : Tower.Tm n} {g b : Tower.Tm m} :
      SameFragmentSyntax f g → SameFragmentSyntax a b → SameFragmentSyntax (.app f a) (.app g b)

private theorem SameFragmentSyntax.names {n m : Nat} {left right : DeclName}
    (same : SameFragmentSyntax (n := n) (m := m) (.const left) (.const right)) : left = right := by
  cases same
  rfl

private theorem SameFragmentSyntax.constant_target {n m : Nat} {name : DeclName} {raw : Tower.Tm m}
    (same : SameFragmentSyntax (n := n) (.const name) raw) : raw = .const name := by
  cases same
  rfl

private theorem SameFragmentSyntax.constant_source {n m : Nat} {name : DeclName} {raw : Tower.Tm n}
    (same : SameFragmentSyntax (m := m) raw (.const name)) : raw = .const name := by
  cases same
  rfl

private theorem SameFragmentSyntax.app_parts {n m : Nat} {f a : Tower.Tm n} {g b : Tower.Tm m}
    (same : SameFragmentSyntax (.app f a) (.app g b)) :
    SameFragmentSyntax f g ∧ SameFragmentSyntax a b := by
  cases same with
  | application functions arguments => exact ⟨functions, arguments⟩

private theorem TypeMeaning.syntax {n : Nat} {raw : Tower.Tm n} {type : HOL.Ty BaseSort}
    (meaning : TypeMeaning raw type) : SameFragmentSyntax raw raw := by
  induction meaning with
  | proposition => exact .constant _
  | base sort => exact .constant _
  | pi _ _ domain codomain => exact .pi domain codomain

private theorem TypeMeaning.type_eq_of_syntax {n m : Nat} {left : Tower.Tm n} {right : Tower.Tm m}
    {a b : HOL.Ty BaseSort} (first : TypeMeaning left a) (second : TypeMeaning right b)
    (same : SameFragmentSyntax left right) : a = b := by
  induction first generalizing m b with
  | proposition =>
      cases second with
      | proposition => rfl
      | base sort =>
          have names := same.names
          cases sort <;> simp [baseName] at names
      | pi _ _ => cases same
  | base sort =>
      cases second with
      | proposition =>
          have names := same.names
          cases sort <;> simp [baseName] at names
      | base other =>
          have names := same.names
          cases sort <;> cases other <;> simp_all [baseName]
      | pi _ _ => cases same
  | pi _ _ domainInduction codomainInduction =>
      cases second with
      | proposition => cases same
      | base sort => cases same
      | pi domain codomain =>
          cases same with
          | pi domains codomains =>
              exact congrArg₂ HOL.Ty.arr (domainInduction domain domains)
                (codomainInduction codomain codomains)

/-- Cross-type logical relations compare arrow values on related arguments.
At every fixed type the relation is exactly ordinary value equality. -/
private def Related (model : HOL.HenkinModel.{0, 0, w} BaseSort Symbol) :
    (a b : HOL.Ty BaseSort) → HOL.Ty.denote model.Carrier a → HOL.Ty.denote model.Carrier b → Prop
  | .arr a b, .arr c d, left, right =>
      ∀ x y, Related model a c x y → Related model b d (left x) (right y)
  | _, _, left, right => HEq left right

private theorem related_same_type (type : HOL.Ty BaseSort)
    (left right : HOL.Ty.denote model.Carrier type) :
    Related model type type left right ↔ left = right := by
  induction type with
  | prop => exact heq_iff_eq
  | base sort => exact heq_iff_eq
  | arr a b domain codomain =>
      constructor
      · intro related
        funext x
        exact (codomain _ _).mp (related x x ((domain _ _).mpr rfl))
      · rintro rfl x y related
        have same := (domain x y).mp related
        subst y
        exact (codomain _ _).mpr rfl

private def RelatedValuations {gamma delta : HOL.Ctx BaseSort}
    (left : model.Valuation gamma) (right : model.Valuation delta) : Prop :=
  ∀ {a b} (i : HOL.Var gamma a) (j : HOL.Var delta b),
    (variableIndex i).val = (variableIndex j).val → Related model a b (left i) (right j)

private theorem variable_type_and_heq {gamma : HOL.Ctx BaseSort} {a b : HOL.Ty BaseSort}
    (left : HOL.Var gamma a) (right : HOL.Var gamma b)
    (same : (variableIndex left).val = (variableIndex right).val) : a = b ∧ HEq left right := by
  induction left generalizing b with
  | vz =>
      cases right with
      | vz => exact ⟨rfl, HEq.rfl⟩
      | vs prior => simp [variableIndex] at same
  | vs prior inductionHypothesis =>
      cases right with
      | vz => simp [variableIndex] at same
      | vs other =>
          obtain ⟨rfl, sameVariables⟩ := inductionHypothesis other (Nat.succ.inj same)
          cases sameVariables
          exact ⟨rfl, HEq.rfl⟩

private theorem related_valuation_refl {gamma : HOL.Ctx BaseSort}
    (valuation : model.Valuation gamma) : RelatedValuations valuation valuation := by
  intro a b left right same
  obtain ⟨rfl, sameVariables⟩ := variable_type_and_heq left right same
  cases sameVariables
  exact (related_same_type _ _ _).mpr rfl

private theorem RelatedValuations.extend {gamma delta : HOL.Ctx BaseSort} {a b : HOL.Ty BaseSort}
    {left : model.Valuation gamma} {right : model.Valuation delta}
    (related : RelatedValuations left right)
    {x : HOL.Ty.denote model.Carrier a} {y : HOL.Ty.denote model.Carrier b}
    (arguments : Related model a b x y) :
    RelatedValuations (model.extend left x) (model.extend right y) := by
  intro c d i j same
  cases i with
  | vz =>
      cases j with
      | vz => exact arguments
      | vs prior => simp [variableIndex] at same
  | vs prior =>
      cases j with
      | vz => simp [variableIndex] at same
      | vs other => exact related prior other (Nat.succ.inj same)

private theorem symbol_type_and_heq {a b : HOL.Ty BaseSort} (left : Symbol a) (right : Symbol b)
    (same : symbolName left = symbolName right) : a = b ∧ HEq left right := by
  cases left <;> cases right <;> simp_all [symbolName]

private theorem unapplied_equality_not_interpreted {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
    (value : model.Valuation gamma → HOL.Ty.denote model.Carrier type) :
    ¬ Denotes model (.const `HOLUniformList.equality) value := by
  intro meaning
  rcases meaning.constant_origin with impossible | ⟨a, symbol, impossible⟩
  · cases (by decide : (`HOLUniformList.equality : DeclName) ≠
      `HOLUniformList.implication) impossible
  · cases symbol <;> simp [symbolName] at impossible

private theorem Denotes.syntax {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
    {raw : Tower.Tm gamma.length}
    {value : model.Valuation gamma → HOL.Ty.denote model.Carrier type}
    (meaning : Denotes model raw value) : SameFragmentSyntax raw raw := by
  induction meaning with
  | index index => exact .index rfl
  | constant symbol => exact .constant _
  | implication => exact .constant _
  | universal formed => exact .application (.constant _) formed.syntax
  | equality formed => exact .application (.constant _) formed.syntax
  | application _ _ function argument => exact .application function argument
  | abstraction _ body => exact .abstraction body

private theorem denotations_related {gamma : HOL.Ctx BaseSort} {a : HOL.Ty BaseSort}
    {left : Tower.Tm gamma.length}
    {leftValue : model.Valuation gamma → HOL.Ty.denote model.Carrier a}
    (first : Denotes model left leftValue) {delta : HOL.Ctx BaseSort} {b : HOL.Ty BaseSort}
    {right : Tower.Tm delta.length}
    {rightValue : model.Valuation delta → HOL.Ty.denote model.Carrier b}
    (second : Denotes model right rightValue) (same : SameFragmentSyntax left right)
    (leftValuation : model.Valuation gamma) (rightValuation : model.Valuation delta)
    (environments : RelatedValuations leftValuation rightValuation) :
    Related model a b (leftValue leftValuation) (rightValue rightValuation) := by
  induction first generalizing delta b with
  | index index =>
      cases second with
      | index other =>
          cases same with
          | index positions => exact environments index other positions
      | constant | implication | universal | equality | application | abstraction => cases same
  | constant symbol =>
      cases second with
      | constant other =>
          obtain ⟨rfl, sameSymbols⟩ := symbol_type_and_heq symbol other same.names
          cases sameSymbols
          exact (related_same_type _ _ _).mpr rfl
      | implication =>
          have names := same.names
          cases symbol <;> simp [symbolName] at names
      | index | universal | equality | application | abstraction => cases same
  | implication =>
      cases second with
      | constant other =>
          have names := same.names
          cases other <;> simp [symbolName] at names
      | implication => exact (related_same_type _ _ _).mpr rfl
      | index | universal | equality | application | abstraction => cases same
  | universal formed =>
      cases second with
      | universal other =>
          have typesEqual := formed.type_eq_of_syntax other same.app_parts.2
          cases typesEqual
          exact (related_same_type _ _ _).mpr rfl
      | equality other =>
          have names := same.app_parts.1.names
          exact False.elim ((by decide : (`HOLUniformList.universal : DeclName) ≠
            `HOLUniformList.equality) names)
      | application function argument =>
          rw [same.app_parts.1.constant_target] at function
          exact False.elim (unapplied_universal_not_interpreted _ function)
      | index | constant | implication | abstraction => cases same
  | equality formed =>
      cases second with
      | equality other =>
          have typesEqual := formed.type_eq_of_syntax other same.app_parts.2
          cases typesEqual
          exact (related_same_type _ _ _).mpr rfl
      | universal other =>
          have names := same.app_parts.1.names
          exact False.elim ((by decide : (`HOLUniformList.equality : DeclName) ≠
            `HOLUniformList.universal) names)
      | application function argument =>
          rw [same.app_parts.1.constant_target] at function
          exact False.elim (unapplied_equality_not_interpreted _ function)
      | index | constant | implication | abstraction => cases same
  | application function argument functionInduction argumentInduction =>
      cases second with
      | application otherFunction otherArgument =>
          exact (functionInduction otherFunction same.app_parts.1
            leftValuation rightValuation environments) _ _
              (argumentInduction otherArgument same.app_parts.2
                leftValuation rightValuation environments)
      | universal other =>
          rw [same.app_parts.1.constant_source] at function
          exact False.elim (unapplied_universal_not_interpreted _ function)
      | equality other =>
          rw [same.app_parts.1.constant_source] at function
          exact False.elim (unapplied_equality_not_interpreted _ function)
      | index | constant | implication | abstraction => cases same
  | abstraction body bodyInduction =>
      cases second with
      | abstraction other =>
          cases same with
          | abstraction bodies =>
              intro x y relatedArguments
              exact bodyInduction other bodies (model.extend leftValuation x)
                (model.extend rightValuation y) (environments.extend relatedArguments)
      | index | constant | implication | universal | equality | application => cases same

/-- Independently constructed denotations of the same actual native term
agree at a fixed typed context and type. Hidden application domains need not
be equal: the proof compares them through a cross-type logical relation. No
normalization, full-domain or valuation-admissibility assumption is needed. -/
theorem Denotes.coherent {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
    {raw : Tower.Tm gamma.length}
    {left right : model.Valuation gamma → HOL.Ty.denote model.Carrier type}
    (first : Denotes model raw left) (second : Denotes model raw right)
    (valuation : model.Valuation gamma) : left valuation = right valuation :=
  (related_same_type type _ _).mp
    (denotations_related first second first.syntax valuation valuation (related_valuation_refl valuation))

/-- On the actual representation image, the source value is the unique
native value, not merely one available interpretation. -/
theorem represented_denotation_iff {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
    (term : HOL.Term Symbol gamma type) {raw : Tower.Tm gamma.length}
    (represented : represent signature term = some raw)
    (value : model.Valuation gamma → HOL.Ty.denote model.Carrier type) :
    Denotes model raw value ↔ ∀ valuation, value valuation = model.denote term valuation := by
  constructor
  · intro meaning valuation
    exact meaning.coherent (representation_square term represented) valuation
  · intro agrees
    have same : value = fun valuation => model.denote term valuation := funext agrees
    rw [same]
    exact representation_square term represented

/-- The same raw function and argument admit two genuinely different hidden
application domains. Coherence must therefore not rely on uniqueness of such
domains, even when either application has the fixed result type `count`. -/
theorem hidden_application_domains (gamma : HOL.Ctx BaseSort) :
    Denotes model (gamma := gamma) (type := .arr (.arr count count) count)
        (.lam (.const `HOLUniformList.zero)) (fun _ _ => model.constDen Symbol.zero) ∧
      Denotes model (gamma := gamma) (type := .arr (.arr mapping mapping) count)
        (.lam (.const `HOLUniformList.zero)) (fun _ _ => model.constDen Symbol.zero) ∧
      Denotes model (gamma := gamma) (type := .arr count count)
        (.lam (.var 0)) (fun _ x => x) ∧
      Denotes model (gamma := gamma) (type := .arr mapping mapping)
        (.lam (.var 0)) (fun _ x => x) ∧
      (HOL.Ty.arr count count : HOL.Ty BaseSort) ≠ .arr mapping mapping :=
  ⟨.abstraction (.constant Symbol.zero), .abstraction (.constant Symbol.zero),
    .abstraction (model := model) (gamma := gamma) (a := count) (b := count) (.index .vz),
    .abstraction (model := model) (gamma := gamma) (a := mapping) (b := mapping) (.index .vz),
    by simp [count, mapping]⟩

/-! ## Actual higher-order native formula and model discrimination -/

/-- The explicit value of the displayed native map-length formula, using
the supplied declarations' carriers and operations. No source term occurs
in this value definition. -/
def mapLengthValue (model : HOL.HenkinModel.{0, 0, w} BaseSort Symbol)
    (gamma : HOL.Ctx BaseSort) : model.Valuation gamma → HOL.Ty.denote model.Carrier .prop :=
  fun _ => ULift.up (∀ function, model.adm mapping function →
    ∀ sequence, model.adm HOL.UniformListInduction.sequence sequence →
      model.Eqv count (model.constDen Symbol.length (model.constDen Symbol.map function sequence))
        (model.constDen Symbol.length sequence))

theorem mapLength_native_meaning (gamma : HOL.Ctx BaseSort) :
    Denotes model (rawMapLength : Tower.Tm gamma.length) (mapLengthValue model gamma) := by
  change Denotes model (rawMapLength : Tower.Tm gamma.length)
    (fun valuation => mapLengthValue model gamma valuation)
  simpa only [HOL.propTy, mapLengthValue, mapLength, preservesLength, HOL.UniformListInduction.length,
    HOL.UniformListInduction.map, HOL.HenkinModel.denote, HOL.PreModel.denote,
    HOL.HenkinModel.extend, HOL.PreModel.extend] using
    representation_square (model := model) (mapLength (Γ := gamma)) (mapLength_represented gamma)

/-- The existing standard list operations satisfy the actual native readout
for every ambient valuation, including arbitrary function arguments. -/
theorem standard_mapLength_value (gamma : HOL.Ctx BaseSort)
    (valuation : StandardListModel.model.Valuation gamma) :
    (mapLengthValue StandardListModel.model gamma valuation).down := by
  intro function _ sequence _
  change (ULift.up ((sequence.down.map (fun x : Bool => (function (ULift.up x)).down)).length) :
      StandardListModel.LiftedCount) = ULift.up sequence.down.length
  simp only [List.length_map]

/-- The junk sequence gives a concrete different value to the same native
formula. This says nothing about a model of the full induction theory. -/
theorem junk_mapLength_value (gamma : HOL.Ctx BaseSort)
    (valuation : JunkModel.model.Valuation gamma) :
    ¬ (mapLengthValue JunkModel.model gamma valuation).down := by
  intro valid
  have impossible := valid (fun x => x) trivial ⟨true⟩ trivial
  change (ULift.up false : JunkModel.LiftedBool) = ULift.up true at impossible
  exact Bool.false_ne_true (congrArg ULift.down impossible)

theorem standard_native_mapLength (gamma : HOL.Ctx BaseSort) :
    Denotes StandardListModel.model (rawMapLength : Tower.Tm gamma.length)
        (mapLengthValue StandardListModel.model gamma) ∧
      ∀ valuation, (mapLengthValue StandardListModel.model gamma valuation).down :=
  ⟨mapLength_native_meaning gamma, standard_mapLength_value gamma⟩

theorem junk_native_mapLength (gamma : HOL.Ctx BaseSort) :
    Denotes JunkModel.model (rawMapLength : Tower.Tm gamma.length)
        (mapLengthValue JunkModel.model gamma) ∧
      (∀ valuation, ¬ (mapLengthValue JunkModel.model gamma valuation).down) ∧
      (∀ formula ∈ equations (Γ := []), JunkModel.model.models formula) ∧
      ¬ JunkModel.model.models inductionPrinciple :=
  ⟨mapLength_native_meaning gamma, junk_mapLength_value gamma,
    JunkModel.equations_valid, JunkModel.induction_invalid⟩

/-- Every represented full-theory premise is interpreted and true under the
standard model. Truth still forms a proposition, not its native inhabitant. -/
theorem standard_theory_native_semantics (formula : HOL.ClosedFormula Symbol)
    (member : formula ∈ theory) {raw : Tower.Tm 0}
    (represented : represent signature formula = some raw) :
    Denotes StandardListModel.model (gamma := []) raw
        (fun valuation => StandardListModel.model.denote formula valuation) ∧
      StandardListModel.model.models formula :=
  ⟨representation_square formula represented, StandardListModel.theory_valid formula member⟩

/-- The actual function-valued identity substitution passes under the
sequence binder and through the declared equality. The proof uses native
semantic substitution, not a source-term decoder. -/
theorem function_substitution_meaning :
    Denotes model (gamma := []) (type := predicate) (inst0 rawMappingIdentity rawLengthPredicate)
      (fun _ sequence => ULift.up
        (model.Eqv count (model.constDen Symbol.length
          (model.constDen Symbol.map (fun x => x) sequence)) (model.constDen Symbol.length sequence))) := by
  have body := representation_square (model := model)
    (lengthPredicate (.var .vz : Expr [mapping] mapping)) lengthPredicate_represented
  have argument := representation_square (model := model) mappingIdentity mappingIdentity_represented
  convert body.instantiate argument using 1
  rfl

theorem function_substitution_native_admission :
    Judgment HOLNativeRelatorCompatibility.rules .nil
      (inst0 rawMappingIdentity rawLengthPredicate) (typeAt types 0 predicate) :=
  (function_substitution_meaning (model := StandardListModel.model)).admitted

/-- Coherence rules out inventing a false value for the standard-model native
formula, rather than merely exhibiting one true interpretation. -/
theorem standard_mapLength_false_value_rejected :
    ¬ Denotes StandardListModel.model (gamma := []) (type := .prop) rawMapLength
      (fun _ => ULift.up False) := by
  intro invented
  let valuation : StandardListModel.model.Valuation [] := fun index => nomatch index
  have agrees := (mapLength_native_meaning (model := StandardListModel.model) []).coherent
    invented valuation
  have valid := standard_mapLength_value [] valuation
  exact (congrArg ULift.down agrees).mp valid

/-- The equations-only junk model cannot assign a true value to this native
formula. Its failure of induction remains a separate established control. -/
theorem junk_mapLength_true_value_rejected :
    ¬ Denotes JunkModel.model (gamma := []) (type := .prop) rawMapLength
      (fun _ => ULift.up True) := by
  intro invented
  let valuation : JunkModel.model.Valuation [] := fun index => nomatch index
  have agrees := (mapLength_native_meaning (model := JunkModel.model) []).coherent invented valuation
  exact junk_mapLength_value [] valuation ((congrArg ULift.down agrees).mpr trivial)

#print axioms typeAt_meaning
#print axioms TypeMeaning.code
#print axioms typeAt_injective
#print axioms TypeMeaning.deterministic
#print axioms TypeMeaning.rename
#print axioms TypeMeaning.substitute
#print axioms TypeMeaning.formed
#print axioms Denotes.source_denotation
#print axioms Denotes.admissible
#print axioms interpreted_environment_admissible
#print axioms Denotes.typed
#print axioms Denotes.admitted
#print axioms Denotes.rename
#print axioms liftEnvironment_extend
#print axioms lifted_components
#print axioms Denotes.substitute
#print axioms Denotes.instantiate
#print axioms native_beta_square
#print axioms application_result
#print axioms representation_square
#print axioms representation_renaming_square
#print axioms representation_substitution_square
#print axioms Denotes.constant_origin
#print axioms missing_declaration_not_interpreted
#print axioms unapplied_universal_not_interpreted
#print axioms universe_argument_rejected
#print axioms native_universes_outside_fragment
#print axioms native_identity_not_interpreted
#print axioms SameFragmentSyntax.names
#print axioms SameFragmentSyntax.constant_target
#print axioms SameFragmentSyntax.constant_source
#print axioms SameFragmentSyntax.app_parts
#print axioms TypeMeaning.syntax
#print axioms TypeMeaning.type_eq_of_syntax
#print axioms related_same_type
#print axioms variable_type_and_heq
#print axioms related_valuation_refl
#print axioms RelatedValuations.extend
#print axioms symbol_type_and_heq
#print axioms unapplied_equality_not_interpreted
#print axioms Denotes.syntax
#print axioms denotations_related
#print axioms Denotes.coherent
#print axioms represented_denotation_iff
#print axioms hidden_application_domains
#print axioms mapLength_native_meaning
#print axioms standard_mapLength_value
#print axioms junk_mapLength_value
#print axioms standard_native_mapLength
#print axioms junk_native_mapLength
#print axioms standard_theory_native_semantics
#print axioms function_substitution_meaning
#print axioms function_substitution_native_admission
#print axioms standard_mapLength_false_value_rejected
#print axioms junk_mapLength_true_value_rejected

end NativeHOLFragmentDenotation
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
