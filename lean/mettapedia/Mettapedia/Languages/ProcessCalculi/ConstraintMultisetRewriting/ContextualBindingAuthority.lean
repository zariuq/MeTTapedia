import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BindingAuthority
import Mettapedia.OSLF.Syntax.ContextualFamilySupport
import Mettapedia.OSLF.Syntax.ContextualFamilyComposition
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectionViewControls

/-!
# Contextual binding authority follows the resolved metavariable support

The later assignment must explicitly fix every protected component in the
resolved observation. This is an authorization obligation, not a consequence
of physical formation or a freshness ledger. The law includes argument
spines and object binders through the existing support congruence theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BindingAuthority

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V W : Type} {source : V → MetaArity S} {target : W → MetaArity S}

theorem contextual_resolved_observation_unchanged (rigid : W → Prop)
    (incoming : Assignment source target) (later : Assignment target target)
    {Γ : Ctx S} {sort : S.Srt} (observed : Term (signature S source) Γ sort)
    (laterFixes : ∀ name, rigid name → later name = generator target name)
    (protectedSupport : ∀ name ∈ support (instantiate incoming observed), rigid name) :
    instantiate (Assignment.compose later incoming) observed = instantiate incoming observed := by
  rw [Assignment.instantiate_compose]
  exact (instantiate_congr later (generator target) (instantiate incoming observed)
    (fun name member => laterFixes name (protectedSupport name member))).trans (instantiate_identity _)

namespace ContextualControls

set_option backward.isDefEq.respectTransparency.types false

open ContextualSelectionViews.Controls (base atom)

abbrev declarations (_ : Nat) : MetaArity base := ([], ())
def observed : Term (signature base declarations) [] () := generator declarations 0

def incoming : Assignment declarations declarations := fun name =>
  if name = 0 then generator declarations 1 else generator declarations name

def later : Assignment declarations declarations := fun name =>
  if name = 1 then atom declarations else generator declarations name

def protectedRoot (name : Nat) : Prop := name = 0

theorem later_fixes_root : ∀ name, protectedRoot name → later name = generator declarations name := by
  intro name same
  change name = 0 at same
  subst name
  rfl

theorem root_alias_resolves_to_dependency : instantiate incoming observed = generator declarations 1 := by
  rw [observed, instantiate_generator]
  rfl

theorem dependency_binding_changes_observation :
    instantiate (Assignment.compose later incoming) observed = atom declarations := by
  rw [Assignment.instantiate_compose, root_alias_resolves_to_dependency, instantiate_generator]
  rfl

theorem fixing_only_the_root_does_not_preserve_the_value :
    instantiate (Assignment.compose later incoming) observed ≠ instantiate incoming observed := by
  rw [dependency_binding_changes_observation, root_alias_resolves_to_dependency]
  intro same
  have operators := (Term.op.inj same).1
  cases operators

theorem the_missing_resolved_support_is_explicit :
    ¬ ∀ name ∈ support (instantiate incoming observed), protectedRoot name := by
  intro closed
  have impossible := closed 1 (by rw [root_alias_resolves_to_dependency, support_generator]; simp)
  exact Nat.noConfusion impossible

abbrev spineDeclarations : Nat → MetaArity base
  | 0 => ([()], ())
  | _ + 1 => ([], ())

def spineObserved : Term (signature base spineDeclarations) [] () :=
  .op (.inl .lam) (.cons
    (.op (S := signature base spineDeclarations) (Γ := [()]) (.inr (.mk 0)) (.cons
      (.op (S := signature base spineDeclarations) (Γ := [()]) (.inl .pair)
        (.cons (.var .zero) (.cons
          (.op (S := signature base spineDeclarations) (Γ := [()]) (.inr (.mk 1)) .nil) .nil))) .nil)) .nil)

def spineResolved : Term (signature base spineDeclarations) [] () :=
  .op (.inl .lam) (.cons
    (.op (S := signature base spineDeclarations) (Γ := [()]) (.inr (.mk 0)) (.cons
      (.op (S := signature base spineDeclarations) (Γ := [()]) (.inl .pair)
        (.cons (.var .zero) (.cons
          (.op (S := signature base spineDeclarations) (Γ := [()]) (.inr (.mk 2)) .nil) .nil))) .nil)) .nil)

def spineIncoming : Assignment spineDeclarations spineDeclarations
  | 0 => generator spineDeclarations 0
  | 1 => generator spineDeclarations 2
  | name + 2 => generator spineDeclarations (name + 2)

def spineLater : Assignment spineDeclarations spineDeclarations
  | 0 => generator spineDeclarations 0
  | 1 => atom spineDeclarations
  | name + 2 => generator spineDeclarations (name + 2)

def protectedSpine (name : Nat) : Prop := name = 0 ∨ name = 2

theorem spine_resolves_under_the_object_binder : instantiate spineIncoming spineObserved = spineResolved := rfl

theorem resolved_support_includes_the_argument_dependency : support spineResolved = [0, 2] := rfl

theorem spine_later_fixes_resolved_support :
    ∀ name, protectedSpine name → spineLater name = generator spineDeclarations name := by
  intro name protectedHere
  rcases protectedHere with rfl | rfl <;> rfl

theorem later_binding_is_nonidentity : spineLater 1 ≠ generator spineDeclarations 1 := by
  intro same
  have operators := (Term.op.inj same).1
  cases operators

theorem binder_and_compound_spine_remain_unchanged :
    instantiate (Assignment.compose spineLater spineIncoming) spineObserved =
      instantiate spineIncoming spineObserved := by
  apply contextual_resolved_observation_unchanged protectedSpine spineIncoming spineLater spineObserved
    spine_later_fixes_resolved_support
  intro name member
  rw [spine_resolves_under_the_object_binder, resolved_support_includes_the_argument_dependency] at member
  simpa [protectedSpine] using member

end ContextualControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BindingAuthority
