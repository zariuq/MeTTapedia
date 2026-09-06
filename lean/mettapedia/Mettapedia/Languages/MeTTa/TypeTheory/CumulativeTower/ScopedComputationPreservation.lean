import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedComputationTyping
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ScopedComputationSemantics

/-!
# Result preservation for independently typed scoped computations

Source computations contain raw terms and operation names. Typing, direct
world semantics and contextual handlers are independent constructions. A
primitive result contract suffices to prove native result typing for every
well-typed computation, under every refined native value environment.

Dependent sequencing preserves the selected argument in a native Sigma pair;
the continuation is checked in its extended context. The result theorem is
not extracted from a proof-carrying answer subtype. Exact handler realization
transfers it to the existing contextual interpreter. Neither theorem asserts
progress for primitives, normalization of native terms, or preservation for
an unimplemented full CBPV or call-by-need calculus.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace ScopedComputation

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers

universe uState uIntent

variable {Head Operation : Type} {State : Type uState} {Intent : Type uIntent}
  {n m : Nat} {R : Rules Head} {signature : OperationSignature Head Operation}
  {Γ : Ctx Head n} {Δ : Ctx Head m}

/-- The primitive's independently authored result family holds for its
actual world results. An empty result list is not a proof of progress. -/
def PrimitivePreserves (R : Rules Head) (signature : OperationSignature Head Operation)
    (Δ : Ctx Head m)
    (primitive : Operation → Tm Head m → State → BranchTrace →
      List (WorldResult State (Tm Head m) Intent)) : Prop :=
  ∀ operation argument state branch output,
    OperationFormation R signature operation →
    FormationSensitive.Typing R Δ argument (liftClosed (signature.input operation)) →
    output ∈ primitive operation argument state branch →
    FormationSensitive.Typing R Δ output.answer (signature.result operation argument)

/-- Every direct result of independently admitted source code has its
substituted native type. Both source binders extend the typed environment
with the actual answer of the first computation. -/
theorem Typing.worlds_preserve {code : Code Head Operation n} {A : Tm Head n}
    (typing : Typing R signature Γ code A) :
    ∀ {m : Nat} {Δ : Ctx Head m}
      {primitive : Operation → Tm Head m → State → BranchTrace →
        List (WorldResult State (Tm Head m) Intent)}
      {environment : Sub Head n m} {state : State} {branch : BranchTrace}
      {output : WorldResult State (Tm Head m) Intent},
      FormationSensitive.CtxMor R Γ Δ environment →
      PrimitivePreserves R signature Δ primitive →
      output ∈ Code.worlds primitive environment code state branch →
      FormationSensitive.Typing R Δ output.answer (subst environment A) := by
  induction typing with
  | returnValue admitted =>
      intro m Δ primitive environment state branch output typed sound returned
      simp only [Code.worlds, List.mem_singleton] at returned
      subst output
      exact admitted.substitute typed
  | sequence _ _ _ _ _ _ ihFirst ihBody =>
      intro m Δ primitive environment state branch output typed sound returned
      obtain ⟨prior, priorMem, suffixMem⟩ := List.mem_flatMap.mp returned
      obtain ⟨later, laterMem, rfl⟩ := List.mem_map.mp suffixMem
      have firstTyped := ihFirst typed sound priorMem
      have laterTyped := ihBody (extendEnvironment typed firstTyped) sound laterMem
      simpa only [subst_consSub_rename_wk] using laterTyped
  | sequenceSigma formed universeWitness _ _ ihFirst ihBody =>
      intro m Δ primitive environment state branch output typed sound returned
      obtain ⟨prior, priorMem, suffixMem⟩ := List.mem_flatMap.mp returned
      obtain ⟨later, laterMem, rfl⟩ := List.mem_map.mp suffixMem
      have firstTyped := ihFirst typed sound priorMem
      have laterTyped := ihBody (extendEnvironment typed firstTyped) sound laterMem
      apply FormationSensitive.Typing.pairIntro (formed.substitute typed)
        universeWitness firstTyped
      simpa only [subst_consSub] using laterTyped
  | choose _ _ ihLeft ihRight =>
      intro m Δ primitive environment state branch output typed sound returned
      rcases List.mem_append.mp returned with left | right
      · exact ihLeft typed sound left
      · exact ihRight typed sound right
  | call declared admitted =>
      intro m Δ primitive environment state branch output typed sound returned
      have argument := admitted.substitute typed
      rw [subst_liftClosed] at argument
      simpa only [OperationSignature.substitute_result] using
        sound _ _ state branch output declared argument returned
  | conv _ formed universeWitness conversion ih =>
      intro m Δ primitive environment state branch output typed sound returned
      exact .conv (ih typed sound returned) (formed.substitute typed)
        universeWitness (conversion.substitute environment)

/-- Exact primitive realization carries the source result theorem to the
existing handler. States, branch traces and intent lists remain in the
membership witness rather than being discarded before qualification. -/
theorem Typing.interpret_preserve {code : Code Head Operation n} {A : Tm Head n}
    (typing : Typing R signature Γ code A)
    (handler : Operation → Tm Head m → Program State (Tm Head m) Intent)
    (primitive : Operation → Tm Head m → State → BranchTrace →
      List (WorldResult State (Tm Head m) Intent))
    (realizes : ∀ operation argument state branch,
      runWorldsAt (handler operation argument) state branch =
        primitive operation argument state branch)
    {environment : Sub Head n m} (typed : FormationSensitive.CtxMor R Γ Δ environment)
    (sound : PrimitivePreserves R signature Δ primitive)
    {state : State} {branch : BranchTrace}
    {output : WorldResult State (Tm Head m) Intent}
    (returned : output ∈ runWorldsAt (Code.interpret handler environment code) state branch) :
    FormationSensitive.Typing R Δ output.answer (subst environment A) := by
  rw [Code.interpret_worlds handler primitive realizes] at returned
  exact typing.worlds_preserve typed sound returned

/-- A formed target context upgrades result typing to the complete existing
native logical judgment. -/
theorem Judgment.interpret_preserve {code : Code Head Operation n} {A : Tm Head n}
    (judgment : Judgment R signature Γ code A)
    (handler : Operation → Tm Head m → Program State (Tm Head m) Intent)
    (primitive : Operation → Tm Head m → State → BranchTrace →
      List (WorldResult State (Tm Head m) Intent))
    (realizes : ∀ operation argument state branch,
      runWorldsAt (handler operation argument) state branch =
        primitive operation argument state branch)
    {environment : Sub Head n m} (target : FormationSensitive.ContextFormation R Δ)
    (typed : FormationSensitive.CtxMor R Γ Δ environment)
    (sound : PrimitivePreserves R signature Δ primitive)
    {state : State} {branch : BranchTrace}
    {output : WorldResult State (Tm Head m) Intent}
    (returned : output ∈ runWorldsAt (Code.interpret handler environment code) state branch) :
    FormationSensitive.Judgment R Δ output.answer (subst environment A) :=
  ⟨target, judgment.typing.interpret_preserve handler primitive realizes typed sound returned⟩

#print axioms extendEnvironment
#print axioms Typing.substitute
#print axioms Typing.rename
#print axioms Typing.instantiate
#print axioms Judgment.substitute
#print axioms Typing.worlds_preserve
#print axioms Typing.interpret_preserve
#print axioms Judgment.interpret_preserve

end ScopedComputation
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
