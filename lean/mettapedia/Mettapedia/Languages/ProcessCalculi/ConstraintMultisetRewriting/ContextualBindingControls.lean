import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBinding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFreshening
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameControls
import Mettapedia.OSLF.Syntax.BindingSignatureABT

/-!
# Contextual binding and fresh activation controls

The identity supply has arbitrarily many keys at every finite arity.
Controls include symbolic principal answers, an occurrence refusal that must
not be mistaken for inconsistency, declared capture through arguments,
rejected nullary capture, and private versus captured activation identities.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBinding.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

abbrev base := ContextualFrame.Controls.signature

def declaration (identity : Nat × Nat) : MetaArity base :=
  (List.replicate identity.1 (), ())

abbrev extended := signature base declaration
def fId : Nat × Nat := (2, 0)
def gId : Nat × Nat := (2, 1)
def nullaryId : Nat × Nat := (0, 0)

def pair {Γ : Ctx base} (left right : Term extended Γ ()) : Term extended Γ () :=
  .op (.inl .pair) (.cons left (.cons right .nil))

def gCall {Γ : Ctx base} (first second : Term extended Γ ()) : Term extended Γ () :=
  .op (.inr (.mk gId)) (.cons first (.cons second .nil))

def body : Term extended [(), ()] () :=
  pair (.var .zero) (gCall (.var (.succ .zero)) (.var .zero))

theorem binding_with_unresolved_hole_is_principal :
    (ContextualFamilies.action declaration [(), ()] ()).Principal
      [(generator declaration fId, body)] (answer fId body) :=
  principal fId body (by decide)

theorem executable_binding_accepts_the_symbolic_body :
    solve? fId body = some (answer fId body) := rfl

theorem executable_binding_refuses_the_reflexive_case :
    solve? fId (generator declaration fId) = none := rfl

/-- A solver branch's refusal is not a negative unification verdict. -/
theorem the_reflexive_case_is_consistent :
    (ContextualFamilies.action declaration [(), ()] ()).Consistent
      [(generator declaration fId, generator declaration fId)] := by
  refine ⟨generator declaration, ?_⟩
  intro equation member
  have same := List.mem_singleton.mp member
  subst equation
  rfl

def repeatedCall : Term extended [()] () :=
  .op (.inr (.mk fId)) (.cons (.var .zero) (.cons (.var .zero) .nil))

theorem principal_binding_applies_to_a_repeated_spine :
    instantiate (answer fId body) repeatedCall = pair (.var .zero) (gCall (.var .zero) (.var .zero)) := rfl

def lambdaCall : Term extended [] () :=
  .op (.inl .lam) (.cons repeatedCall .nil)

theorem declared_binder_argument_is_preserved :
    instantiate (answer fId body) lambdaCall =
      Term.op (S := extended) (.inl .lam)
        (.cons (pair (.var .zero) (gCall (.var .zero) (.var .zero))) .nil) := rfl

private theorem closed_bind_ne_variable {T : Signature} {Γ : Ctx T} {sort : T.Srt}
    (term : Term T [] sort) (environment : Sub T [] Γ) (position : Var Γ sort) :
    Mettapedia.OSLF.Binding.bind environment term ≠ Term.var position := by
  cases term with
  | var impossible => cases impossible
  | op _ _ => intro same; cases same

theorem nullary_binding_cannot_capture_the_surrounding_binder :
    ¬ (ContextualFamilies.action declaration [()] ()).Consistent
      [(Term.op (.inr (.mk nullaryId)) .nil, Term.var .zero)] := by
  rintro ⟨assignment, solved⟩
  have same := solved (Term.op (.inr (.mk nullaryId)) .nil, Term.var .zero) (by simp)
  change Mettapedia.OSLF.Binding.bind
    (argsToSub (S := extended) (bs := []) (Γ := [()]) .nil) (assignment nullaryId) = Term.var .zero at same
  exact closed_bind_ne_variable (assignment nullaryId) _ _ same

theorem every_binding_result_has_the_common_ABT_scope
    (assignment : Assignment declaration declaration) :
    Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.Term.supportedAt 0
      (CommonABT.lower (instantiate assignment lambdaCall)) = true :=
  CommonABT.lower_scoped (S := extended) (instantiate assignment lambdaCall)

def uniform (_ : Nat) : MetaArity base := ([(), ()], ())

def privateSchema : Term (signature base (ContextualFreshening.declarations uniform uniform)) [(), ()] () :=
  generator (ContextualFreshening.declarations uniform uniform) (.inl 7)

def capturedSchema : Term (signature base (ContextualFreshening.declarations uniform uniform)) [(), ()] () :=
  generator (ContextualFreshening.declarations uniform uniform) (.inr 7)

theorem distinct_activations_have_distinct_private_identities :
    ContextualFreshening.termAt uniform uniform 0 privateSchema ≠
      ContextualFreshening.termAt uniform uniform 1 privateSchema := by
  intro same
  have seen := congrArg (support (S := base)) same
  change [Sum.inl (Mettapedia.Logic.LP.ScopedVar.at 0 7)] =
    [Sum.inl (Mettapedia.Logic.LP.ScopedVar.at 1 7)] at seen
  have seen := (List.cons.inj seen).1
  have scopes := congrArg Mettapedia.Logic.LP.ScopedVar.scope (Sum.inl.inj seen)
  change 0 = 1 at scopes
  cases scopes

theorem explicit_captures_keep_the_same_identity :
    ContextualFreshening.termAt uniform uniform 0 capturedSchema =
      ContextualFreshening.termAt uniform uniform 1 capturedSchema := by
  rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBinding.Controls
