import Mettapedia.OSLF.Syntax.BindingPatternRendering
import Mettapedia.OSLF.Syntax.LambdaScopedAuthoringComparison

/-!
# The authored lambda rendering preserves contextual substitution

The generic binding-rendering theorem is instantiated with the actual `App`
and `Lam` pattern constructors. The comparison with the existing authored
encoder is proved recursively, so the resulting substitution theorem concerns
the encoder used by the scoped LamCong declaration, not a parallel syntax.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaPatternRendering

open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.LambdaScopedAuthoringComparison
open Mettapedia.OSLF.Binding.PatternRendering
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution

/-- Both authored lambda constructors commute with index shifting and
capture-avoiding raw-pattern substitution. -/
def rendering : Rendering sig where
  operation := fun op args => match op with
    | .app => .apply "App" args
    | .lam => .apply "Lam" args
  shift := by
    intro s op args cutoff amount
    cases op <;> rfl
  bind := by
    intro s op args assignment
    cases op <;> rfl

theorem rendering_scoped : ScopePreserving rendering := by
  intro s op args depth h
  cases op <;> exact h

theorem wrapBinders_eq (binders : List Srt) (body : Pattern) :
    PatternRendering.wrapBinders binders body =
      LambdaScopedAuthoringComparison.wrapBinders binders body := rfl

mutual
/-- The generic rendering is definitionally aligned with the actual authored
lambda encoder at every variable and constructor. -/
theorem encodeTerm_eq : ∀ {Γ : Ctx sig} {s : Srt}
    (term : Term sig Γ s),
    PatternRendering.encodeTerm rendering term =
      LambdaScopedAuthoringComparison.encodeTerm term
  | _, _, .var _ => rfl
  | _, _, .op op args => by
      have h := encodeArgs_eq args
      cases op with
      | app =>
          change Pattern.apply "App" (PatternRendering.encodeArgs rendering args) =
            Pattern.apply "App" (LambdaScopedAuthoringComparison.encodeArgs args)
          exact congrArg (Pattern.apply "App") h
      | lam =>
          change Pattern.apply "Lam" (PatternRendering.encodeArgs rendering args) =
            Pattern.apply "Lam" (LambdaScopedAuthoringComparison.encodeArgs args)
          exact congrArg (Pattern.apply "Lam") h

/-- The comparison includes the complete argument vector and its binder
wrappers. -/
theorem encodeArgs_eq : ∀ {arity : List (List Srt × Srt)}
    {Γ : Ctx sig} (args : Args sig arity Γ),
    PatternRendering.encodeArgs rendering args =
      LambdaScopedAuthoringComparison.encodeArgs args
  | _, _, .nil => rfl
  | _, _, .cons (bs := bs) head tail => by
      simp only [PatternRendering.encodeArgs,
        LambdaScopedAuthoringComparison.encodeArgs,
        encodeTerm_eq head, encodeArgs_eq tail]
      exact congrArg (fun body => body ::
        LambdaScopedAuthoringComparison.encodeArgs tail)
        (wrapBinders_eq bs (LambdaScopedAuthoringComparison.encodeTerm head))
end

/-- The actual authored encoder never emits an escaping de Bruijn index from
an intrinsically scoped lambda term. -/
theorem encodeTerm_scoped {Γ : Ctx sig} {s : Srt}
    (term : Term sig Γ s) :
    (LambdaScopedAuthoringComparison.encodeTerm term).isWellScopedAt
      Γ.length = true := by
  rw [← encodeTerm_eq]
  exact PatternRendering.encodeTerm_wellScoped rendering rendering_scoped term

/-- The real authored lambda encoder respects every intrinsic simultaneous
substitution, including substitutions beneath a lambda binder. -/
theorem encodeTerm_bind {Γ Δ : Ctx sig} (sigma : Sub sig Γ Δ)
    {s : Srt} (term : Term sig Γ s) :
    LambdaScopedAuthoringComparison.encodeTerm (bind sigma term) =
      substitute (PatternRendering.encodeSub rendering sigma)
        (LambdaScopedAuthoringComparison.encodeTerm term) := by
  rw [← encodeTerm_eq, ← encodeTerm_eq]
  exact PatternRendering.encodeTerm_bind rendering sigma term

/-- The same comparison holds for every argument vector, including all
declared binder lists. -/
theorem encodeArgs_bind {arity : List (List Srt × Srt)}
    {Γ Δ : Ctx sig} (sigma : Sub sig Γ Δ)
    (args : Args sig arity Γ) :
    LambdaScopedAuthoringComparison.encodeArgs (bindArgs sigma args) =
      substituteList (PatternRendering.encodeSub rendering sigma)
        (LambdaScopedAuthoringComparison.encodeArgs args) := by
  rw [← encodeArgs_eq, ← encodeArgs_eq]
  exact PatternRendering.encodeArgs_bind rendering sigma args

/-- Eliminating the newest intrinsic variable is represented by the existing
single-variable pattern assignment on every declared source variable. -/
theorem encoded_extend {Γ : Ctx sig} (argument : Term sig Γ .term) :
    EncodedAssignment rendering (extend argument)
      (single (LambdaScopedAuthoringComparison.encodeTerm argument)) := by
  intro s v
  cases v with
  | zero =>
      change LambdaScopedAuthoringComparison.encodeTerm argument =
        PatternRendering.encodeTerm rendering argument
      exact (encodeTerm_eq argument).symm
  | succ w => rfl

/-- The beta contractum in every ambient context is exactly canonical
binder elimination of the encoded body and argument. -/
theorem encode_inst {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term)
    (argument : Term sig Γ .term) :
    LambdaScopedAuthoringComparison.encodeTerm (inst body argument) =
      instantiateBVar (LambdaScopedAuthoringComparison.encodeTerm argument)
        (LambdaScopedAuthoringComparison.encodeTerm body) := by
  calc
    LambdaScopedAuthoringComparison.encodeTerm (inst body argument) =
        PatternRendering.encodeTerm rendering (bind (extend argument) body) :=
      (encodeTerm_eq _).symm
    _ = substitute
          (single (LambdaScopedAuthoringComparison.encodeTerm argument))
          (PatternRendering.encodeTerm rendering body) :=
      PatternRendering.encodeTerm_bind_of_assignment rendering
        (extend argument) _ (encoded_extend argument) body
    _ = instantiateBVar
          (LambdaScopedAuthoringComparison.encodeTerm argument)
          (LambdaScopedAuthoringComparison.encodeTerm body) := by
      rw [encodeTerm_eq,
        substitute_single_eq_instantiateBVar]

/-- Every intrinsic beta instance is rendered with the authored `App` and
`Lam` source and the actual binder-eliminated target. -/
theorem encode_beta_endpoints {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term)
    (argument : Term sig Γ .term) :
    LambdaScopedAuthoringComparison.encodeTerm (appT (lamT body) argument) =
        .apply "App"
          [.apply "Lam"
            [.lambda none (LambdaScopedAuthoringComparison.encodeTerm body)],
           LambdaScopedAuthoringComparison.encodeTerm argument] ∧
      LambdaScopedAuthoringComparison.encodeTerm (inst body argument) =
        instantiateBVar
          (LambdaScopedAuthoringComparison.encodeTerm argument)
          (LambdaScopedAuthoringComparison.encodeTerm body) := by
  exact ⟨rfl, encode_inst body argument⟩

/-- An enclosing binder and an ambient variable have distinct indices after
lowering; substituting the ambient one does not capture it. -/
def openLamUsesAmbient : Term sig [.term] .term :=
  lamT (.var (.succ .zero))

def duplicateAmbient : Sub sig [.term] [.term]
  | _, .zero => appT (.var .zero) (.var .zero)

theorem openLam_substitution_preserves_binder :
    substitute (PatternRendering.encodeSub rendering duplicateAmbient)
      (LambdaScopedAuthoringComparison.encodeTerm openLamUsesAmbient) =
        .apply "Lam" [.lambda none (.apply "App" [.bvar 1, .bvar 1])] := by
  rw [← encodeTerm_bind]
  rfl

theorem captured_openLam_result_is_wrong :
    substitute (PatternRendering.encodeSub rendering duplicateAmbient)
      (LambdaScopedAuthoringComparison.encodeTerm openLamUsesAmbient) ≠
        .apply "Lam" [.lambda none (.apply "App" [.bvar 0, .bvar 0])] := by
  rw [openLam_substitution_preserves_binder]
  decide +kernel

#print axioms encodeTerm_bind
#print axioms encodeArgs_bind
#print axioms encode_inst

end Mettapedia.OSLF.Binding.LambdaPatternRendering
