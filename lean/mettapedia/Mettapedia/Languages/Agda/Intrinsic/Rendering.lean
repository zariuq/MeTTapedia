import Mettapedia.Languages.Agda.Intrinsic.Syntax
import Mettapedia.OSLF.Syntax.BindingPatternRendering

/-!
# Structural lowering to the generic execution carrier

Binder wrappers come from the signature's arities. The substitution square
below concerns the executor's actual pattern substitution, including open
contexts and substitution beneath arbitrary binders. This is a syntax
refinement, not a claim that an Agda source parser has been verified.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Intrinsic.Rendering

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.PatternRendering
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution

def label : {s : Srt} → Op s → String
  | _, .pi => "Pi"
  | _, .lam => "Lam"
  | _, .app => "App"
  | _, .ann => "Ann"
  | _, .sigma => "Sigma"
  | _, .pair => "Pair"
  | _, .fst => "Fst"
  | _, .snd => "Snd"
  | _, .nat => "Nat"
  | _, .zero => "Zero"
  | _, .suc => "Suc"
  | _, .natSuc => "NatSuc"
  | _, .natrec => "NatRec"
  | _, .unit => "Unit"
  | _, .star => "Star"
  | _, .empty => "Empty"
  | _, .univ level => "Set:" ++ toString level
  | _, .global name => "Global:" ++ toString name

def rendering : PatternRendering.Rendering sig where
  operation := fun op args => .apply (label op) args
  shift := by intros; rfl
  bind := by intros; rfl

theorem rendering_scoped : ScopePreserving rendering := by
  intro s op args depth h
  exact h

def encode {Γ : Ctx sig} (term : Tm Γ) : Pattern :=
  PatternRendering.encodeTerm rendering term

theorem encode_scoped {Γ : Ctx sig} (term : Tm Γ) :
    (encode term).isWellScopedAt Γ.length = true :=
  PatternRendering.encodeTerm_wellScoped rendering rendering_scoped term

theorem encode_substitute {Γ Δ : Ctx sig} (σ : Sub sig Γ Δ) (term : Tm Γ) :
    encode (bind σ term) =
      substitute (encodeSub rendering σ) (encode term) :=
  PatternRendering.encodeTerm_bind rendering σ term

theorem encoded_extend {Γ : Ctx sig} (argument : Tm Γ) :
    EncodedAssignment rendering (extend argument) (single (encode argument)) := by
  intro s v
  cases v <;> rfl

/-- Intrinsic binder elimination and the executor's binder elimination agree
for all bodies and arguments, not just for closed test terms. -/
theorem encode_inst {Γ : Ctx sig}
    (body : Tm (.term :: Γ)) (argument : Tm Γ) :
    encode (inst body argument) =
      instantiateBVar (encode argument) (encode body) := by
  change PatternRendering.encodeTerm rendering (bind (extend argument) body) = _
  rw [PatternRendering.encodeTerm_bind_of_assignment rendering
    (extend argument) _ (encoded_extend argument) body]
  exact substitute_single_eq_instantiateBVar _ _

theorem encode_beta_endpoints {Γ : Ctx sig}
    (body : Tm (.term :: Γ)) (argument : Tm Γ) :
    encode (app (lam body) argument) =
      .apply "App" [.apply "Lam" [.lambda none (encode body)], encode argument] ∧
    encode (inst body argument) =
      instantiateBVar (encode argument) (encode body) :=
  ⟨rfl, encode_inst body argument⟩

/-- A free occurrence remains outside the inner binder after beta. -/
theorem open_beta_keeps_ambient :
    instantiateBVar (.bvar 0)
      (encode (lam (.var (.succ .zero)) : Tm [.term, .term])) =
      .apply "Lam" [.lambda none (.bvar 1)] := by
  change instantiateBVar (encode (.var .zero : Tm [.term])) _ = _
  rw [← encode_inst]
  rfl

theorem captured_output_is_different :
    instantiateBVar (.bvar 0)
      (encode (lam (.var (.succ .zero)) : Tm [.term, .term])) ≠
      .apply "Lam" [.lambda none (.bvar 0)] := by
  rw [open_beta_keeps_ambient]
  decide +kernel

end Mettapedia.Languages.Agda.Intrinsic.Rendering
