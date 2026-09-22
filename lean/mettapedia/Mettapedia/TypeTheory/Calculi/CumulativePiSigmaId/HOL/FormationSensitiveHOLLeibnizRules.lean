import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLLeibnizInterface

/-!
# Native introduction and use of HOL predicate equality

These rules construct ordinary native lambdas and applications over the
existing proof decoder. Their equality premise is a proof of the displayed
predicate formula, not a new opaque equality constant or native identity.
Formation of each formula and dependent product is checked independently.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLLeibnizRules

open Presentation Presentation.FormationSensitive
open FormationSensitiveHOLInterface Mettapedia.Logic HOL.UniformListInduction
open FormationSensitiveHOLUniformList (types rawAll rawImp)
open FormationSensitiveHOLProofFamily (proof)
open FormationSensitiveHOLLeibnizInterface (rawLeibniz)

abbrev rules := FormationSensitiveHOLProofFamily.rules

def predicateContext {n : Nat} (context : Tower.Ctx n) (type : HOL.Ty BaseSort) : Tower.Ctx (n + 1) :=
  .snoc context (typeAt types n (.arr type .prop))

def atPredicate {n : Nat} (value : Tower.Tm n) : Tower.Tm (n + 1) :=
  .app (.var 0) (rename wk value)

theorem application_typed {n : Nat} {context : Tower.Ctx n} {a b : HOL.Ty BaseSort}
    {f x : Tower.Tm n} (function : Typing rules context f (typeAt types n (.arr a b)))
    (argument : Typing rules context x (typeAt types n a)) :
    Typing rules context (.app f x) (typeAt types n b) := by
  simpa only [inst0, typeAt_subst] using Typing.appElim function argument

theorem predicate_application_typed {n : Nat} {context : Tower.Ctx n} {a : HOL.Ty BaseSort}
    {predicate x : Tower.Tm n}
    (predicateTyped : Typing rules context predicate (typeAt types n (.arr a .prop)))
    (argument : Typing rules context x (typeAt types n a)) :
    Typing rules context (.app predicate x) (.const `HOLUniformList.prop) :=
  application_typed predicateTyped argument

theorem atPredicate_typed {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty BaseSort}
    {value : Tower.Tm n} (typed : Typing rules context value (typeAt types n type)) :
    Typing rules (predicateContext context type) (atPredicate value) (.const `HOLUniformList.prop) := by
  have predicateTyped : Typing rules (predicateContext context type) (.var 0)
      (typeAt types (n + 1) (.arr type .prop)) := by
    simpa only [predicateContext, Ctx.lookup_snoc_zero, typeAt_rename] using
      (Typing.var (R := rules) (Γ := predicateContext context type) 0)
  have valueTyped : Typing rules (predicateContext context type) (rename wk value)
      (typeAt types (n + 1) type) := by
    simpa only [typeAt_rename, predicateContext] using
      typed.weaken (extension := typeAt types n (.arr type .prop))
  exact predicate_application_typed predicateTyped valueTyped

theorem body_typed {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty BaseSort}
    {x y : Tower.Tm n} (hx : Typing rules context x (typeAt types n type))
    (hy : Typing rules context y (typeAt types n type)) :
    Typing rules (predicateContext context type) (rawImp (atPredicate x) (atPredicate y))
      (.const `HOLUniformList.prop) :=
  FormationSensitiveHOLProofFamily.implication_proposition (atPredicate_typed hx) (atPredicate_typed hy)

theorem rawLeibniz_typed {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty BaseSort}
    {x y : Tower.Tm n} (hx : Typing rules context x (typeAt types n type))
    (hy : Typing rules context y (typeAt types n type)) :
    Typing rules context (rawLeibniz type x y) (.const `HOLUniformList.prop) := by
  have typed := FormationSensitiveHOLProofFamily.universal_lambda_proposition
    (FormationSensitiveHOLProofFamily.simple_type_formed (.arr type .prop) context)
    (body_typed hx hy)
  simpa only [rawLeibniz, atPredicate, rawAll, FormationSensitiveHOLUniformList.universal,
    FormationSensitiveHOLProofFamily.universalProposition, liftClosed, rename, typeAt_rename] using typed

/-- A checked body depending on an arbitrary HOL predicate and an input
proof constructs predicate equality by two ordinary native lambdas. -/
theorem introduction {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty BaseSort}
    {x y : Tower.Tm n} {body : Tower.Tm (n + 2)}
    (hx : Typing rules context x (typeAt types n type))
    (hy : Typing rules context y (typeAt types n type))
    (bodyTyped : Typing rules
      (.snoc (predicateContext context type) (proof (atPredicate x)))
      body (rename wk (proof (atPredicate y)))) :
    Typing rules context (.lam (.lam body)) (proof (rawLeibniz type x y)) := by
  have implication := FormationSensitiveHOLProofFamily.implication_intro
    (atPredicate_typed hx) (atPredicate_typed hy) bodyTyped
  have universal := FormationSensitiveHOLProofFamily.universal_intro
    (FormationSensitiveHOLProofFamily.simple_type_formed (.arr type .prop) context)
    (body_typed hx hy) implication
  simpa only [rawLeibniz, atPredicate, rawAll, FormationSensitiveHOLUniformList.universal,
    FormationSensitiveHOLProofFamily.universalProposition, liftClosed, rename, typeAt_rename] using universal

/-- Predicate instantiation is ordinary application of the given proof. -/
theorem specialize {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty BaseSort}
    {x y h predicate : Tower.Tm n}
    (hx : Typing rules context x (typeAt types n type))
    (hy : Typing rules context y (typeAt types n type))
    (comparison : Typing rules context h (proof (rawLeibniz type x y)))
    (predicateTyped : Typing rules context predicate (typeAt types n (.arr type .prop))) :
    Typing rules context (.app h predicate)
      (proof (rawImp (.app predicate x) (.app predicate y))) := by
  have comparison' : Typing rules context h
      (proof (FormationSensitiveHOLProofFamily.universalProposition
        (typeAt types n (.arr type .prop)) (.lam (rawImp (atPredicate x) (atPredicate y))))) := by
    simpa only [rawLeibniz, atPredicate, rawAll, FormationSensitiveHOLUniformList.universal,
      FormationSensitiveHOLProofFamily.universalProposition, liftClosed, rename, typeAt_rename] using comparison
  have universal := FormationSensitiveHOLProofFamily.universal_elim
    (FormationSensitiveHOLProofFamily.simple_type_formed (.arr type .prop) context)
    (body_typed hx hy) comparison' predicateTyped
  have instantiate (value : Tower.Tm n) : inst0 predicate (atPredicate value) = .app predicate value := by
    have weakened : subst (subst0 predicate) (rename wk value) = value := inst0_rename_wk predicate value
    simp only [atPredicate, inst0, subst, subst0, Fin.cases_zero, weakened]
  have instantiateBody : inst0 predicate (rawImp (atPredicate x) (atPredicate y)) =
      rawImp (.app predicate x) (.app predicate y) := by
    change rawImp (inst0 predicate (atPredicate x)) (inst0 predicate (atPredicate y)) = _
    rw [instantiate, instantiate]
  simpa only [instantiateBody] using universal

/-- Reuse is the application `(h P) hx`, with no equality axiom or search. -/
theorem elimination {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty BaseSort}
    {x y h predicate input : Tower.Tm n}
    (hx : Typing rules context x (typeAt types n type))
    (hy : Typing rules context y (typeAt types n type))
    (comparison : Typing rules context h (proof (rawLeibniz type x y)))
    (predicateTyped : Typing rules context predicate (typeAt types n (.arr type .prop)))
    (inputTyped : Typing rules context input (proof (.app predicate x))) :
    Typing rules context (.app (.app h predicate) input) (proof (.app predicate y)) := by
  exact FormationSensitiveHOLProofFamily.implication_elim
    (predicate_application_typed predicateTyped hx)
    (predicate_application_typed predicateTyped hy)
    (specialize hx hy comparison predicateTyped) inputTyped

theorem reflexivity {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty BaseSort}
    {x : Tower.Tm n} (hx : Typing rules context x (typeAt types n type)) :
    Typing rules context (.lam (.lam (.var 0))) (proof (rawLeibniz type x x)) :=
  introduction hx hx (.var 0)

/-- Reflexive transport returns the original witness by two beta steps. -/
theorem reflexivity_computation {n : Nat} (predicate input : Tower.Tm n) :
    Conv rules.headEq (.app (.app (.lam (.lam (.var 0))) predicate) input)
      input rules.computation := by
  have first : Conv rules.headEq (.app (.lam (.lam (.var 0))) predicate)
      (.lam (.var 0)) rules.computation :=
    .rel _ _ (.betaPi (.lam (.var 0)) predicate)
  exact .trans _ _ _ (Conv.congApp first (.refl _)) (.rel _ _ (.betaPi (.var 0) input))

theorem reflexivity_reuses_input {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty BaseSort}
    {x predicate input : Tower.Tm n}
    (hx : Typing rules context x (typeAt types n type))
    (predicateTyped : Typing rules context predicate (typeAt types n (.arr type .prop)))
    (inputTyped : Typing rules context input (proof (.app predicate x))) :
    Typing rules context (.app (.app (.lam (.lam (.var 0))) predicate) input)
        (proof (.app predicate x)) ∧
      Conv rules.headEq (.app (.app (.lam (.lam (.var 0))) predicate) input)
        input rules.computation :=
  ⟨elimination hx hx (reflexivity hx) predicateTyped inputTyped,
    reflexivity_computation predicate input⟩

namespace Controls

/-- The equality carrier can itself be a function type. This closed proof
uses a real native lambda inhabitant, not an assumed equality certificate. -/
theorem function_reflexivity :
    Judgment rules .nil (.lam (.lam (.var 0)))
      (proof (rawLeibniz mapping (.lam (.var 0)) (.lam (.var 0)))) := by
  refine ⟨.nil, reflexivity ?_⟩
  apply FormationSensitiveHOLProofFamily.include_typed
  exact represent_typed FormationSensitiveHOLLeibnizInterface.signature
    (FormationSensitiveHOLUniformList.mappingIdentity) rfl

/-- Existing primitive equality still has no decoder root. The alternative
presentation gains its eliminator through lambdas and the old two roots. -/
theorem primitive_equality_undecoded (target : Tower.Tm 0) :
    ¬ FormationSensitiveHOLProofFamily.DecoderStep
      (proof (FormationSensitiveHOLUniformList.rawEq sequence
        (.const `HOLUniformList.nil) (.const `HOLUniformList.nil))) target :=
  FormationSensitiveHOLProofFamily.equality_has_no_decoder_step _ _ _ _

end Controls

#print axioms rawLeibniz_typed
#print axioms introduction
#print axioms specialize
#print axioms elimination
#print axioms reflexivity
#print axioms reflexivity_reuses_input
#print axioms Controls.function_reflexivity
#print axioms Controls.primitive_equality_undecoded

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLLeibnizRules
