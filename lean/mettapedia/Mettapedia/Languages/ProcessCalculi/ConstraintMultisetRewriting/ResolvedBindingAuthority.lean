import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingAuthority
import Mettapedia.Logic.LP.UnificationIdempotence

/-!
# Binding authority on resolved observations

Permission to refine a caller's bindings must follow the dependencies of the
current observation. Fixing only its original variable identity is insufficient.
For first-order syntax, fixing the resolved support is necessary and sufficient.
For contextual metavariables, it is a sufficient compositional condition.

The incoming substitution denotes the current interpretation. A triangular
runtime table needs full dereferencing before this interface applies; one
application of that raw table is not full resolution. The idempotence lemma
states an explicit sufficient boundary. These laws do not assert that native
publication already checks binding authority.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResolvedBindingAuthority

open Mettapedia.Logic.LP

universe u v

section FirstOrder

variable {signature : LPSignature.{u, u, v, u}} [DecidableEq signature.vars]

theorem observation_unchanged_iff (incoming later : Subst signature) (observed : Term signature) :
    (later.comp incoming).applyTerm observed = incoming.applyTerm observed ↔
      ∀ name ∈ (incoming.applyTerm observed).freeVars, later name = .var name := by
  rw [Subst.applyTerm_comp]
  exact ⟨Subst.var_fixed_of_applyTerm_eq_self, Subst.applyTerm_eq_self⟩

/-- Every dependency of each protected current value is fixed. -/
def Protects (protectedRoots : signature.vars → Prop) (incoming later : Subst signature) : Prop :=
  ∀ root, protectedRoots root →
    ∀ name ∈ (incoming.applyTerm (.var root)).freeVars, later name = .var name

theorem Protects.preserves {protectedRoots : signature.vars → Prop} {incoming later : Subst signature}
    (authorized : Protects protectedRoots incoming later) (root : signature.vars) (isProtected : protectedRoots root) :
    (later.comp incoming).applyTerm (.var root) = incoming.applyTerm (.var root) :=
  (observation_unchanged_iff incoming later (.var root)).mpr (authorized root isProtected)

theorem protects_iff_preserves (protectedRoots : signature.vars → Prop) (incoming later : Subst signature) :
    Protects protectedRoots incoming later ↔
      ∀ root, protectedRoots root →
        (later.comp incoming).applyTerm (.var root) = incoming.applyTerm (.var root) :=
  ⟨fun authorized root isProtected => authorized.preserves root isProtected,
    fun preserved root isProtected =>
      (observation_unchanged_iff incoming later (.var root)).mp (preserved root isProtected)⟩

theorem Protects.identity (protectedRoots : signature.vars → Prop) (incoming : Subst signature) :
    Protects protectedRoots incoming (Subst.id signature) := by
  intro root isProtected name member
  rfl

/-- Authority for the second step is checked against the first step's result. -/
theorem Protects.compose {protectedRoots : signature.vars → Prop} {incoming first second : Subst signature}
    (firstAuthorized : Protects protectedRoots incoming first)
    (secondAuthorized : Protects protectedRoots (first.comp incoming) second) :
    Protects protectedRoots incoming (second.comp first) := by
  intro root isProtected name member
  have fixedFirst := firstAuthorized root isProtected name member
  have fixedSecond := secondAuthorized root isProtected name (by
    rw [firstAuthorized.preserves root isProtected]
    exact member)
  change second.applyTerm (first name) = .var name
  rw [fixedFirst]
  exact fixedSecond

theorem Protects.restrict {protectedRoots smaller : signature.vars → Prop}
    {incoming later : Subst signature} (authorized : Protects protectedRoots incoming later)
    (subset : ∀ name, smaller name → protectedRoots name) : Protects smaller incoming later :=
  fun root isProtected => authorized root (subset root isProtected)

/-- An idempotent interpretation is already fully resolved. Repeatedly applying
the authorized composite to the observation cannot reveal a deeper change. -/
theorem idempotent_resolution_unchanged (protectedRoots : signature.vars → Prop)
    (incoming : Subst signature) (idempotent : incoming.Absorbs incoming)
    (later : ProtectedParameters.Assignment protectedRoots) (observed : Term signature)
    (supportProtected : ∀ name ∈ (incoming.applyTerm observed).freeVars, protectedRoots name) :
    (later.val.comp incoming).applyTerm ((later.val.comp incoming).applyTerm observed) =
      incoming.applyTerm observed := by
  rw [BindingAuthority.resolved_observation_unchanged protectedRoots incoming later observed supportProtected,
    Subst.applyTerm_comp, idempotent.applyTerm]
  exact ProtectedParameters.supported_term_fixed protectedRoots later (incoming.applyTerm observed) supportProtected

end FirstOrder

namespace Contextual

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V W : Type}
  {source : V → MetaArity S} {target : W → MetaArity S}

/-- Contextual support fixation is sufficient; argument specialization makes
its first-order necessity theorem invalid for higher-arity metavariables. -/
def Protects (protectedRoots : V → Prop) (incoming : Assignment source target)
    (later : Assignment target target) : Prop :=
  ∀ root, protectedRoots root → ∀ name ∈ support (incoming root),
    later name = generator target name

theorem Protects.preserves {protectedRoots : V → Prop} {incoming : Assignment source target}
    {later : Assignment target target} (authorized : Protects protectedRoots incoming later)
    (root : V) (isProtected : protectedRoots root) :
    Assignment.compose later incoming root = incoming root := by
  exact (instantiate_congr later (generator target) (incoming root)
    (fun name member => authorized root isProtected name member)).trans (instantiate_identity _)

theorem Protects.identity (protectedRoots : V → Prop) (incoming : Assignment source target) :
    Protects protectedRoots incoming (generator target) := by
  intro root isProtected name member
  rfl

theorem Protects.compose {protectedRoots : V → Prop} {incoming : Assignment source target}
    {first second : Assignment target target}
    (firstAuthorized : Protects protectedRoots incoming first)
    (secondAuthorized : Protects protectedRoots (Assignment.compose first incoming) second) :
    Protects protectedRoots incoming (Assignment.compose second first) := by
  intro root isProtected name member
  have firstFixed := firstAuthorized root isProtected name member
  have secondFixed := secondAuthorized root isProtected name (by
    rw [firstAuthorized.preserves root isProtected]
    exact member)
  change instantiate second (first name) = generator target name
  rw [firstFixed, instantiate_generator]
  exact secondFixed

end Contextual

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResolvedBindingAuthority
