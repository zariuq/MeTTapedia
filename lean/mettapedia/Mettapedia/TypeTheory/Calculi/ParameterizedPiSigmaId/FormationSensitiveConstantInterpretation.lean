import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConstantExpansion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRegularity

/-!
# Typed interpretation of declared constants by closed terms

A declaration interpretation is a translation between rule presentations, not
an equation identifying a source constant with its chosen image. Its primitive
obligations are closed typing for each declared image, preservation of universe
rules, and conversion of the images of source root computations. The resulting
theorems transport actual formation-sensitive derivations, formed telescopes,
and typed substitutions through simultaneous constant expansion.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ConstantExpansion

open FormationSensitive

variable {Head : Type} {n m : Nat}

def expandCtx (bodies : Bodies Head) {n : Nat} : Ctx Head n → Ctx Head n
  | .nil => .nil
  | .snoc Γ A => .snoc (expandCtx bodies Γ) (expand bodies A)

@[simp] theorem expandCtx_lookup (bodies : Bodies Head) (Γ : Ctx Head n)
    (index : Fin n) :
    Ctx.lookup (expandCtx bodies Γ) index = expand bodies (Ctx.lookup Γ index) := by
  induction Γ with
  | nil => exact Fin.elim0 index
  | snoc Γ A ih =>
      refine Fin.cases ?_ ?_ index
      · exact (expand_rename bodies wk A).symm
      · intro prior
        simp only [expandCtx, Ctx.lookup_snoc_succ, ih, expand_rename]

/-- Local evidence for interpreting primitive declarations and rules. The
conclusions about arbitrary derivations below are not fields of this record. -/
structure TypedInterpretation (source target : Rules Head) (bodies : Bodies Head) : Prop where
  headTyping : ∀ {h u}, source.headTyping h u → target.headTyping h u
  isUniverse : ∀ {u}, source.isUniverse u → target.isUniverse u
  join : ∀ {u v w}, source.join u v w → target.join u v w
  cumulative : ∀ {u v}, source.cumulative u v → target.cumulative u v
  headEq : source.headEq = target.headEq
  constant : ∀ {name type}, source.constantType name = some type →
    Typing target .nil (bodies name) (expand bodies type)
  root : ∀ {k : Nat} {left right : Tm Head k}, source.computation.step left right →
    Conv target.headEq (expand bodies left) (expand bodies right) target.computation

namespace TypedInterpretation

variable {source target : Rules Head} {bodies : Bodies Head}

theorem conversion (interpretation : TypedInterpretation source target bodies)
    {left right : Tm Head n} (converted : Conv source.headEq left right source.computation) :
    Conv target.headEq (expand bodies left) (expand bodies right) target.computation := by
  rw [interpretation.headEq] at converted
  exact conv_expand bodies interpretation.root converted

/-- Every source typing constructor, including formation-sensitive conversion,
is transported through the chosen declaration interpretation. -/
theorem typing (interpretation : TypedInterpretation source target bodies)
    {Γ : Ctx Head n} {term type : Tm Head n} (typed : Typing source Γ term type) :
    Typing target (expandCtx bodies Γ) (expand bodies term) (expand bodies type) := by
  induction typed with
  | headType head => exact .headType (interpretation.headTyping head)
  | var index =>
      simpa only [expand, expandCtx_lookup] using
        (Typing.var (R := target) (Γ := expandCtx bodies _) index)
  | @const k Γ name type u known _ _ _ =>
      have lifted := (interpretation.constant known).renameTyping
        (Δ := expandCtx bodies Γ) (ρ := Fin.elim0) (fun index => Fin.elim0 index)
      simpa only [expand, expand_liftClosed, liftClosed, expand_rename] using lifted
  | piForm _ universeA _ universeB joined ihA ihB =>
      exact .piForm ihA (interpretation.isUniverse universeA) ihB
        (interpretation.isUniverse universeB) (interpretation.join joined)
  | sigmaForm _ universeA _ universeB joined ihA ihB =>
      exact .sigmaForm ihA (interpretation.isUniverse universeA) ihB
        (interpretation.isUniverse universeB) (interpretation.join joined)
  | lamIntro _ universeWitness _ ihPi ihBody =>
      exact .lamIntro ihPi (interpretation.isUniverse universeWitness) ihBody
  | appElim _ _ ihFunction ihArgument =>
      simpa only [expand, expand_inst0] using Typing.appElim ihFunction ihArgument
  | pairIntro _ universeWitness _ _ ihSigma ihFirst ihSecond =>
      rw [expand_inst0] at ihSecond
      exact .pairIntro ihSigma (interpretation.isUniverse universeWitness) ihFirst ihSecond
  | fstElim _ ihPair => exact .fstElim ihPair
  | sndElim _ ihPair =>
      simpa only [expand, expand_inst0] using Typing.sndElim ihPair
  | idForm _ universeWitness _ _ ihA ihLeft ihRight =>
      exact .idForm ihA (interpretation.isUniverse universeWitness) ihLeft ihRight
  | reflIntro _ ihTerm => exact .reflIntro ihTerm
  | cumul _ order ihTerm => exact .cumul ihTerm (interpretation.cumulative order)
  | conv _ _ universeWitness converted ihTerm ihTarget =>
      exact .conv ihTerm ihTarget (interpretation.isUniverse universeWitness)
        (interpretation.conversion converted)

theorem context (interpretation : TypedInterpretation source target bodies)
    {Γ : Ctx Head n} (formed : ContextFormation source Γ) :
    ContextFormation target (expandCtx bodies Γ) := by
  induction formed with
  | nil => exact .nil
  | snoc _ typed universeWitness ih =>
      exact .snoc ih (interpretation.typing typed) (interpretation.isUniverse universeWitness)

theorem judgment (interpretation : TypedInterpretation source target bodies)
    {Γ : Ctx Head n} {term type : Tm Head n} (judged : Judgment source Γ term type) :
    Judgment target (expandCtx bodies Γ) (expand bodies term) (expand bodies type) :=
  ⟨interpretation.context judged.context, interpretation.typing judged.typing⟩

/-- Context substitutions are interpreted componentwise, on the same map as
the terms and telescope entries they act on. -/
theorem contextMorphism (interpretation : TypedInterpretation source target bodies)
    {Γ : Ctx Head n} {Δ : Ctx Head m} {sigma : Sub Head n m}
    (typed : FormationSensitive.CtxMor source Γ Δ sigma) :
    FormationSensitive.CtxMor target (expandCtx bodies Γ) (expandCtx bodies Δ)
      (fun index => expand bodies (sigma index)) := by
  intro index
  simpa only [expand_subst, expandCtx_lookup] using interpretation.typing (typed index)

/-- Interpretation and proof reuse by simultaneous substitution form a
commuting square with complete formed-context judgments at the target. -/
theorem substituted_judgment (interpretation : TypedInterpretation source target bodies)
    {Γ : Ctx Head n} {Δ : Ctx Head m} {term type : Tm Head n} {sigma : Sub Head n m}
    (judged : Judgment source Γ term type) (formed : ContextFormation source Δ)
    (typed : FormationSensitive.CtxMor source Γ Δ sigma) :
    Judgment target (expandCtx bodies Δ)
      (subst (fun index => expand bodies (sigma index)) (expand bodies term))
      (subst (fun index => expand bodies (sigma index)) (expand bodies type)) :=
  (interpretation.judgment judged).substitute (interpretation.context formed)
    (interpretation.contextMorphism typed)

end TypedInterpretation

#print axioms expandCtx_lookup
#print axioms TypedInterpretation.conversion
#print axioms TypedInterpretation.typing
#print axioms TypedInterpretation.context
#print axioms TypedInterpretation.judgment
#print axioms TypedInterpretation.contextMorphism
#print axioms TypedInterpretation.substituted_judgment

end ConstantExpansion
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
