import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLLeibnizRules

/-!
# Constructive native equality operations

Symmetry, transitivity and application congruence are ordinary terms built
from the actual predicate equality proof. Beta conversion opens each chosen
predicate. No new equality rule, proof constant or native identity equation
is added to the presentation.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLLeibnizDerived

open Presentation Presentation.FormationSensitive
open FormationSensitiveHOLInterface Mettapedia.Logic HOL.UniformListInduction
open FormationSensitiveHOLUniformList (types rawImp)
open FormationSensitiveHOLProofFamily (proof)
open FormationSensitiveHOLLeibnizInterface (rawLeibniz rawLeibniz_subst)
open FormationSensitiveHOLLeibnizRules

def reflTerm {n : Nat} : Tower.Tm n := .lam (.lam (.var 0))

def symmetry {n : Nat} (type : HOL.Ty BaseSort) (x h : Tower.Tm n) : Tower.Tm n :=
  .app (.app h (.lam (rawLeibniz type (.var 0) (rename wk x)))) reflTerm

def transitivity {n : Nat} (type : HOL.Ty BaseSort) (x h k : Tower.Tm n) : Tower.Tm n :=
  .app (.app k (.lam (rawLeibniz type (rename wk x) (.var 0)))) h

def congruence {n : Nat} (result : HOL.Ty BaseSort) (f x h : Tower.Tm n) : Tower.Tm n :=
  .app (.app h (.lam (rawLeibniz result (rename wk (.app f x))
    (.app (rename wk f) (.var 0))))) reflTerm

def functionCongruence {n : Nat} (result : HOL.Ty BaseSort) (f x h : Tower.Tm n) : Tower.Tm n :=
  .app (.app h (.lam (rawLeibniz result (rename wk (.app f x))
    (.app (.var 0) (rename wk x))))) reflTerm

def propForward {n : Nat} (h : Tower.Tm n) : Tower.Tm n := .app h (.lam (.var 0))

@[simp] theorem reflTerm_subst {n m : Nat} (sigma : Sub Tower.Head n m) :
    subst sigma reflTerm = reflTerm := rfl

@[simp] theorem symmetry_subst {n m : Nat} (sigma : Sub Tower.Head n m)
    (type : HOL.Ty BaseSort) (x h : Tower.Tm n) :
    subst sigma (symmetry type x h) = symmetry type (subst sigma x) (subst sigma h) := by
  simp [symmetry, subst, rawLeibniz_subst, liftSub, reflTerm]

@[simp] theorem transitivity_subst {n m : Nat} (sigma : Sub Tower.Head n m)
    (type : HOL.Ty BaseSort) (x h k : Tower.Tm n) :
    subst sigma (transitivity type x h k) =
      transitivity type (subst sigma x) (subst sigma h) (subst sigma k) := by
  simp [transitivity, subst, rawLeibniz_subst, liftSub]

@[simp] theorem congruence_subst {n m : Nat} (sigma : Sub Tower.Head n m)
    (type : HOL.Ty BaseSort) (f x h : Tower.Tm n) :
    subst sigma (congruence type f x h) =
      congruence type (subst sigma f) (subst sigma x) (subst sigma h) := by
  simp [congruence, subst, rawLeibniz_subst, liftSub, reflTerm]

@[simp] theorem functionCongruence_subst {n m : Nat} (sigma : Sub Tower.Head n m)
    (type : HOL.Ty BaseSort) (f x h : Tower.Tm n) :
    subst sigma (functionCongruence type f x h) =
      functionCongruence type (subst sigma f) (subst sigma x) (subst sigma h) := by
  simp [functionCongruence, subst, rawLeibniz_subst, liftSub, reflTerm]

@[simp] theorem propForward_subst {n m : Nat} (sigma : Sub Tower.Head n m)
    (h : Tower.Tm n) : subst sigma (propForward h) = propForward (subst sigma h) := rfl

@[simp] theorem subst0_weaken {n : Nat} (argument term : Tower.Tm n) :
    subst (subst0 argument) (rename wk term) = term := inst0_rename_wk argument term

theorem variable_zero {n : Nat} (context : Tower.Ctx n) (type : HOL.Ty BaseSort) :
    Typing rules (.snoc context (typeAt types n type)) (.var 0)
      (typeAt types (n + 1) type) := by
  simpa only [Ctx.lookup_snoc_zero, typeAt_rename] using
    (Typing.var (R := rules) (Γ := .snoc context (typeAt types n type)) 0)

theorem weaken_typed {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty BaseSort}
    {term : Tower.Tm n} (typed : Typing rules context term (typeAt types n type))
    (extension : Tower.Tm n) :
    Typing rules (.snoc context extension) (rename wk term) (typeAt types (n + 1) type) := by
  simpa only [typeAt_rename] using typed.weaken (extension := extension)

theorem predicate_lambda {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty BaseSort}
    {body : Tower.Tm (n + 1)}
    (typed : Typing rules (.snoc context (typeAt types n type)) body (.const `HOLUniformList.prop)) :
    Typing rules context (.lam body) (typeAt types n (.arr type .prop)) :=
  .lamIntro (FormationSensitiveHOLProofFamily.pi_zero
    (FormationSensitiveHOLProofFamily.simple_type_formed type context)
    (FormationSensitiveHOLProofFamily.proposition_formed _)) (.sort Tower.zero) typed

theorem beta_conversion {n : Nat} (body : Tower.Tm (n + 1)) (argument : Tower.Tm n) :
    Conv rules.headEq (.app (.lam body) argument) (inst0 argument body) rules.computation :=
  .rel _ _ (.betaPi body argument)

/-- The supplied equality chooses an actual lambda predicate. Its beta
computations are checked at both the input and output proof families. -/
theorem eliminate_lambda {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty BaseSort}
    {x y h input : Tower.Tm n} {body : Tower.Tm (n + 1)}
    (hx : Typing rules context x (typeAt types n type))
    (hy : Typing rules context y (typeAt types n type))
    (comparison : Typing rules context h (proof (rawLeibniz type x y)))
    (bodyTyped : Typing rules (.snoc context (typeAt types n type)) body (.const `HOLUniformList.prop))
    (inputTyped : Typing rules context input (proof (inst0 x body))) :
    Typing rules context (.app (.app h (.lam body)) input) (proof (inst0 y body)) := by
  have predicate := predicate_lambda bodyTyped
  have adjusted := Typing.conv inputTyped
    (FormationSensitiveHOLProofFamily.proof_formed (predicate_application_typed predicate hx))
    (.sort Tower.zero) (Conv.congApp (.refl _) (.symm _ _ (beta_conversion body x)))
  have application := elimination hx hy comparison predicate adjusted
  have target := bodyTyped.instantiate hy
  exact .conv application (FormationSensitiveHOLProofFamily.proof_formed target)
    (.sort Tower.zero) (Conv.congApp (.refl _) (beta_conversion body y))

theorem symmetry_typed {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty BaseSort}
    {x y h : Tower.Tm n}
    (hx : Typing rules context x (typeAt types n type))
    (hy : Typing rules context y (typeAt types n type))
    (comparison : Typing rules context h (proof (rawLeibniz type x y))) :
    Typing rules context (symmetry type x h) (proof (rawLeibniz type y x)) := by
  have body := rawLeibniz_typed (variable_zero context type)
    (weaken_typed hx (typeAt types n type))
  have initial := reflexivity hx
  have result := eliminate_lambda hx hy comparison body
    (input := reflTerm) (by simpa [inst0, rawLeibniz_subst, reflTerm] using initial)
  simpa only [symmetry, inst0, FormationSensitiveHOLLeibnizInterface.rawLeibniz_subst,
    subst, subst0_weaken, subst0, Fin.cases_zero] using result

theorem transitivity_typed {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty BaseSort}
    {x y z h k : Tower.Tm n}
    (hx : Typing rules context x (typeAt types n type))
    (hy : Typing rules context y (typeAt types n type))
    (hz : Typing rules context z (typeAt types n type))
    (first : Typing rules context h (proof (rawLeibniz type x y)))
    (second : Typing rules context k (proof (rawLeibniz type y z))) :
    Typing rules context (transitivity type x h k) (proof (rawLeibniz type x z)) := by
  have body := rawLeibniz_typed (weaken_typed hx (typeAt types n type))
    (variable_zero context type)
  have result := eliminate_lambda hy hz second body
    (input := h) (by simpa [inst0, rawLeibniz_subst] using first)
  simpa only [transitivity, inst0, FormationSensitiveHOLLeibnizInterface.rawLeibniz_subst,
    subst, subst0_weaken, subst0, Fin.cases_zero] using result

theorem congruence_typed {n : Nat} {context : Tower.Ctx n} {a b : HOL.Ty BaseSort}
    {f x y h : Tower.Tm n}
    (hf : Typing rules context f (typeAt types n (.arr a b)))
    (hx : Typing rules context x (typeAt types n a))
    (hy : Typing rules context y (typeAt types n a))
    (comparison : Typing rules context h (proof (rawLeibniz a x y))) :
    Typing rules context (congruence b f x h) (proof (rawLeibniz b (.app f x) (.app f y))) := by
  have application := application_typed hf hx
  have body := rawLeibniz_typed (weaken_typed application (typeAt types n a))
    (application_typed (weaken_typed hf (typeAt types n a)) (variable_zero context a))
  have result := eliminate_lambda hx hy comparison body (input := reflTerm)
    (by simpa [inst0, rawLeibniz_subst, reflTerm, subst, subst0] using reflexivity application)
  simpa only [congruence, inst0, rawLeibniz_subst, subst, subst0_weaken,
    subst0, Fin.cases_zero] using result

theorem functionCongruence_typed {n : Nat} {context : Tower.Ctx n} {a b : HOL.Ty BaseSort}
    {f g x h : Tower.Tm n}
    (hf : Typing rules context f (typeAt types n (.arr a b)))
    (hg : Typing rules context g (typeAt types n (.arr a b)))
    (hx : Typing rules context x (typeAt types n a))
    (comparison : Typing rules context h (proof (rawLeibniz (.arr a b) f g))) :
    Typing rules context (functionCongruence b f x h)
      (proof (rawLeibniz b (.app f x) (.app g x))) := by
  have application := application_typed hf hx
  have body := rawLeibniz_typed (weaken_typed application (typeAt types n (.arr a b)))
    (application_typed (variable_zero context (.arr a b))
      (weaken_typed hx (typeAt types n (.arr a b))))
  have result := eliminate_lambda hf hg comparison body (input := reflTerm)
    (by simpa [inst0, rawLeibniz_subst, reflTerm, subst, subst0] using reflexivity application)
  simpa only [functionCongruence, inst0, rawLeibniz_subst, subst, subst0_weaken,
    subst0, Fin.cases_zero] using result

theorem propForward_typed {n : Nat} {context : Tower.Ctx n} {p q h : Tower.Tm n}
    (hp : Typing rules context p (.const `HOLUniformList.prop))
    (hq : Typing rules context q (.const `HOLUniformList.prop))
    (comparison : Typing rules context h (proof (rawLeibniz .prop p q))) :
    Typing rules context (propForward h) (proof (rawImp p q)) := by
  have predicate := predicate_lambda (variable_zero context .prop)
  have result := specialize hp hq comparison predicate
  have beta (term : Tower.Tm n) : Conv rules.headEq (.app (.lam (.var 0)) term) term
      rules.computation := by
    simpa only [inst0, subst, subst0, Fin.cases_zero] using beta_conversion (.var 0) term
  have implication : Conv rules.headEq
      (rawImp (.app (.lam (.var 0)) p) (.app (.lam (.var 0)) q)) (rawImp p q)
      rules.computation := Conv.congApp (Conv.congApp (.refl _) (beta p)) (beta q)
  exact .conv result
    (FormationSensitiveHOLProofFamily.proof_formed
      (FormationSensitiveHOLProofFamily.implication_proposition hp hq))
    (.sort Tower.zero) (Conv.congApp (.refl _) implication)

theorem propBackward_typed {n : Nat} {context : Tower.Ctx n} {p q h : Tower.Tm n}
    (hp : Typing rules context p (.const `HOLUniformList.prop))
    (hq : Typing rules context q (.const `HOLUniformList.prop))
    (comparison : Typing rules context h (proof (rawLeibniz .prop p q))) :
    Typing rules context (propForward (symmetry .prop p h)) (proof (rawImp q p)) :=
  propForward_typed hq hp (symmetry_typed hp hq comparison)

#print axioms symmetry_typed
#print axioms transitivity_typed
#print axioms congruence_typed
#print axioms functionCongruence_typed
#print axioms propForward_typed
#print axioms propBackward_typed

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLLeibnizDerived
