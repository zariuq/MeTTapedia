import Mettapedia.Logic.HOL.HOLLightBooleanDefinitions
import Mettapedia.Logic.HOL.HOLLightBooleanProofs
import Mettapedia.Logic.HOL.ContextualConversionFree

/-!
# Contextual laws for the HOL Light Boolean bodies

Closed-body application commutes with renaming and substitution. The retained
negation beta step and quantifier congruence work at arbitrary contexts and
simple carriers, independently of any datatype signature or source cache.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.HOLLightBooleanConversions

open ContextualTrinity

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
variable {Γ Ξ : Ctx Base} {domain codomain : Ty Base}

theorem rename_applyClosed (mapping : Rename Base Γ Ξ)
    (function : ClosedTerm Const (domain ⇒ codomain)) (argument : Term Const Γ domain) :
    rename mapping (HOLLightBooleanDefinitions.applyClosed function argument) =
      HOLLightBooleanDefinitions.applyClosed function (rename mapping argument) := by
  simp only [HOLLightBooleanDefinitions.applyClosed, rename, rename_weakenCtx]

theorem subst_applyClosed (mapping : Subst Const Γ Ξ)
    (function : ClosedTerm Const (domain ⇒ codomain)) (argument : Term Const Γ domain) :
    subst mapping (HOLLightBooleanDefinitions.applyClosed function argument) =
      HOLLightBooleanDefinitions.applyClosed function (subst mapping argument) := by
  simp only [HOLLightBooleanDefinitions.applyClosed, subst, subst_weakenCtx]

theorem rename_imp (mapping : Rename Base Γ Ξ) (first second : Formula Const Γ) :
    rename mapping (HOLLightBooleanDefinitions.imp first second) =
      HOLLightBooleanDefinitions.imp (rename mapping first) (rename mapping second) := by
  simp only [HOLLightBooleanDefinitions.imp, rename, rename_applyClosed]

theorem subst_imp (mapping : Subst Const Γ Ξ) (first second : Formula Const Γ) :
    subst mapping (HOLLightBooleanDefinitions.imp first second) =
      HOLLightBooleanDefinitions.imp (subst mapping first) (subst mapping second) := by
  simp only [HOLLightBooleanDefinitions.imp, subst, subst_applyClosed]

theorem weaken_negation (context : Ctx Base) :
    weakenCtx context (HOLLightBooleanDefinitions.negation (Const := Const)) =
      .lam (HOLLightBooleanDefinitions.imp (.var .vz)
        (weakenCtx (.prop :: context) HOLLightBooleanDefinitions.falsity)) := by
  induction context with
  | nil => rfl
  | cons domain context ih =>
      change weaken (weakenCtx context HOLLightBooleanDefinitions.negation) = _
      rw [ih]
      simp only [weaken, rename, rename_imp, Rename.lift, rename_weakenCtx]

def negationStep (argument : Formula Const Γ) :
    BetaStep (HOLLightBooleanDefinitions.applyClosed HOLLightBooleanDefinitions.negation argument)
      (HOLLightBooleanDefinitions.imp argument (weakenCtx Γ HOLLightBooleanDefinitions.falsity)) := by
  let body : Formula Const (.prop :: Γ) :=
    HOLLightBooleanDefinitions.imp (.var .vz) (weakenCtx _ HOLLightBooleanDefinitions.falsity)
  have source : HOLLightBooleanDefinitions.applyClosed HOLLightBooleanDefinitions.negation argument =
      .app (.lam body) argument := by
    simp only [HOLLightBooleanDefinitions.applyClosed, weaken_negation, body]
  have target : instantiate argument body =
      HOLLightBooleanDefinitions.imp argument (weakenCtx Γ HOLLightBooleanDefinitions.falsity) := by
    simp only [body, instantiate, subst_imp, subst, Subst.single, subst_weakenCtx]
  rw [source, ← target]
  exact .beta body argument

def allStep {first second : Formula Const (domain :: Γ)} (step : BetaStep first second) :
    BetaStep (HOLLightBooleanDefinitions.all first) (HOLLightBooleanDefinitions.all second) :=
  .appArg (weakenCtx Γ (HOLLightBooleanDefinitions.universal domain)) (.lam step)

def transport {assumptions : List (Formula Const Γ)} {first second : Formula Const Γ}
    (equality : ProofSyntax Const assumptions (.eq first second))
    (premise : ProofSyntax Const assumptions first) : ProofSyntax Const assumptions second :=
  .impE (.eqPropEL equality) premise

theorem transport_free {assumptions : List (Formula Const Γ)} {first second : Formula Const Γ}
    (equality : ProofSyntax Const assumptions (.eq first second))
    (premise : ProofSyntax Const assumptions first)
    (equalityFree : equality.FunctionExtensionalityFree) (premiseFree : premise.FunctionExtensionalityFree) :
    (transport equality premise).FunctionExtensionalityFree := ⟨equalityFree, premiseFree⟩

theorem expand_weakenCtx (context : Ctx Base) {type : Ty Base} (term : ClosedTerm Const type) :
    ImpredicativeConnectives.expand (weakenCtx context term) =
      weakenCtx context (ImpredicativeConnectives.expand term) := by
  induction context with
  | nil => rfl
  | cons domain context ih =>
      simp only [weakenCtx_cons, weaken, ImpredicativeConnectives.expand_rename, ih]

theorem expand_applyClosed (function : ClosedTerm Const (domain ⇒ codomain))
    (argument : Term Const Γ domain) :
    ImpredicativeConnectives.expand (HOLLightBooleanDefinitions.applyClosed function argument) =
      HOLLightBooleanDefinitions.applyClosed (ImpredicativeConnectives.expand function)
        (ImpredicativeConnectives.expand argument) := by
  simp only [HOLLightBooleanDefinitions.applyClosed, ImpredicativeConnectives.expand, expand_weakenCtx]

theorem expand_imp (first second : Formula Const Γ) :
    ImpredicativeConnectives.expand (HOLLightBooleanDefinitions.imp first second) =
      HOLLightBooleanDefinitions.imp (ImpredicativeConnectives.expand first)
        (ImpredicativeConnectives.expand second) := by
  simp only [HOLLightBooleanDefinitions.imp, ImpredicativeConnectives.expand, expand_applyClosed]
  rfl

theorem expand_all (body : Formula Const (domain :: Γ)) :
    ImpredicativeConnectives.expand (HOLLightBooleanDefinitions.all body) =
      HOLLightBooleanDefinitions.all (ImpredicativeConnectives.expand body) := by
  simp only [HOLLightBooleanDefinitions.all, expand_applyClosed, ImpredicativeConnectives.expand]
  rfl

theorem expand_falsity :
    ImpredicativeConnectives.expand (HOLLightBooleanDefinitions.falsity (Const := Const)) =
      HOLLightBooleanDefinitions.falsity := rfl

theorem sourceConjunctionBeta_free {assumptions : List (Formula Const Γ)}
    (first second : Formula Const Γ) :
    (HOLLightBooleanProofs.sourceConjunctionBeta first second (Δ := assumptions)).FunctionExtensionalityFree := by
  simp [HOLLightBooleanProofs.sourceConjunctionBeta, ProofSyntax.FunctionExtensionalityFree]
  refine (ProofSyntax.functionExtensionalityFree_of_heq rfl ?_ (cast_heq _ _)).mpr ?_
  · rw [← rename_weakenCtx (Γ' := []) (Δ' := Γ) (fun {_} index => nomatch index)
      (HOLLightBooleanDefinitions.conjunction (Const := Const))]
    rfl
  · simp [ProofSyntax.FunctionExtensionalityFree]

def conjunctionEquation {assumptions : List (Formula Const Γ)} (first second : Formula Const Γ) :
    ProofSyntax Const assumptions (.eq (HOLLightBooleanDefinitions.conj first second) (.and first second)) :=
  .eqTrans (HOLLightBooleanProofs.sourceConjunctionBeta first second)
    (HOLLightBooleanProofs.conjunctionEquation first second)

theorem conjunctionEquation_free {assumptions : List (Formula Const Γ)} (first second : Formula Const Γ) :
    (conjunctionEquation first second (assumptions := assumptions)).FunctionExtensionalityFree :=
  ⟨sourceConjunctionBeta_free first second, HOLLightBooleanProofs.conjunctionEquation_free first second⟩

def conjunctionMap {assumptions : List (Formula Const Γ)} {first first' second second' : Formula Const Γ}
    (firstEq : ProofSyntax Const assumptions (.eq first first'))
    (secondEq : ProofSyntax Const assumptions (.eq second second')) :
    ProofSyntax Const assumptions
      (.eq (HOLLightBooleanDefinitions.conj first second) (.and first' second')) :=
  .eqTrans (conjunctionEquation first second) (ProofSyntax.andCongr firstEq secondEq)

theorem conjunctionMap_free {assumptions : List (Formula Const Γ)}
    {first first' second second' : Formula Const Γ}
    (firstEq : ProofSyntax Const assumptions (.eq first first'))
    (secondEq : ProofSyntax Const assumptions (.eq second second'))
    (firstFree : firstEq.FunctionExtensionalityFree) (secondFree : secondEq.FunctionExtensionalityFree) :
    (conjunctionMap firstEq secondEq).FunctionExtensionalityFree := by
  exact ⟨conjunctionEquation_free _ _, (ProofSyntax.andCongr_free _ _).mpr ⟨firstFree, secondFree⟩⟩

def implicationCongruence {assumptions : List (Formula Const Γ)}
    {first first' second second' : Formula Const Γ}
    (firstEq : ProofSyntax Const assumptions (.eq first first'))
    (secondEq : ProofSyntax Const assumptions (.eq second second')) :
    ProofSyntax Const assumptions
      (.eq (HOLLightBooleanDefinitions.imp first second) (HOLLightBooleanDefinitions.imp first' second')) :=
  ProofSyntax.appCongr (.eqAppArg (weakenCtx Γ HOLLightBooleanDefinitions.implication) firstEq) secondEq

theorem implicationCongruence_free {assumptions : List (Formula Const Γ)}
    {first first' second second' : Formula Const Γ}
    (firstEq : ProofSyntax Const assumptions (.eq first first'))
    (secondEq : ProofSyntax Const assumptions (.eq second second'))
    (firstFree : firstEq.FunctionExtensionalityFree) (secondFree : secondEq.FunctionExtensionalityFree) :
    (implicationCongruence firstEq secondEq).FunctionExtensionalityFree :=
  (ProofSyntax.appCongr_free _ _).mpr ⟨firstFree, secondFree⟩

def allCongruence {assumptions : List (Formula Const Γ)} {first second : Formula Const (domain :: Γ)}
    (equation : ProofSyntax Const (weakenHyps assumptions) (.eq first second)) :
    ProofSyntax Const assumptions (.eq (HOLLightBooleanDefinitions.all first) (HOLLightBooleanDefinitions.all second)) :=
  .eqAppArg (weakenCtx Γ (HOLLightBooleanDefinitions.universal domain)) (.eqLam equation)

theorem allCongruence_free {assumptions : List (Formula Const Γ)} {first second : Formula Const (domain :: Γ)}
    (equation : ProofSyntax Const (weakenHyps assumptions) (.eq first second))
    (free : equation.FunctionExtensionalityFree) : (allCongruence equation).FunctionExtensionalityFree := free

#print axioms negationStep
#print axioms transport_free
#print axioms expand_all
#print axioms sourceConjunctionBeta_free
#print axioms conjunctionMap_free
#print axioms allCongruence_free

end Mettapedia.Logic.HOL.HOLLightBooleanConversions
