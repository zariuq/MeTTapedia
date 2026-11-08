import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStoredRows
import Mettapedia.OSLF.Syntax.ContextualFamilyReindex

/-!
# Local instantiation of stored schemas in a nonbinding guard

A shared row is compared under the supplied assignment. A schema may instantiate
its private locals in a later declaration family. The supplied model's names
enter that family by an injective, arity-preserving renaming; captured values
are fixed through that renaming. Local witnesses create no caller binding.

Allowing the later frame avoids requiring bodies for unused or erased local
declarations in a possibly smaller model frame. All terms remain the existing
intrinsically scoped binding terms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardMatching

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {Local Shared Next Future Later : Type}
  (locals : Local → MetaArity S)
  {captures : Shared → MetaArity S} {next : Next → MetaArity S}
  {future : Future → MetaArity S} {later : Later → MetaArity S}

structure Extension (declaration : Next → MetaArity S) where
  Names : Type
  declarations : Names → MetaArity S
  name : Next → Names
  injective : Function.Injective name
  preserves : ∀ identity, declarations (name identity) = declaration identity

def Extension.assignment (extension : Extension next) : Assignment next extension.declarations :=
  reindex extension.name extension.preserves

def Extension.identity (declaration : Next → MetaArity S) : Extension declaration :=
  ⟨Next, declaration, id, Function.injective_id, fun _ => rfl⟩

def Extension.withLocals (locals : Local → MetaArity S) (declaration : Next → MetaArity S) :
    Extension declaration :=
  ⟨Local ⊕ Next, ContextualSelectionViews.source locals declaration, Sum.inr,
    Sum.inr_injective, fun _ => rfl⟩

def instanceAssignment (localBodies : Assignment locals future)
    (embedding : Assignment next future) (candidate : Assignment captures next) :
    Assignment (ContextualSelectionViews.source locals captures) future
  | .inl identity => localBodies identity
  | .inr identity => instantiate embedding (candidate identity)

theorem instance_fixes_captures (localBodies : Assignment locals future)
    (embedding : Assignment next future) (candidate : Assignment captures next) (identity : Shared) :
    instanceAssignment locals localBodies embedding candidate (.inr identity) =
      instantiate embedding (candidate identity) := rfl

def Matches (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (pattern : Term (signature S next) Γ sort) : ContextualStoredRows.Row locals captures Γ sort → Prop
  | .shared value => pattern = instantiate candidate value
  | .schema body => ∃ extension : Extension next, ∃ localBodies : Assignment locals extension.declarations,
      instantiate (instanceAssignment locals localBodies extension.assignment candidate) body =
        instantiate extension.assignment pattern

theorem shared_matches_iff (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (pattern : Term (signature S next) Γ sort) (value : Term (signature S captures) Γ sort) :
    Matches locals candidate pattern (.shared value) ↔ pattern = instantiate candidate value := Iff.rfl

theorem instance_on_shared_value (localBodies : Assignment locals future)
    (embedding : Assignment next future) (candidate : Assignment captures next)
    {Γ : Ctx S} {sort : S.Srt} (value : Term (signature S captures) Γ sort) :
    instantiate (instanceAssignment locals localBodies embedding candidate)
        (instantiate (ContextualSelectionViews.capturedSource locals captures) value) =
      instantiate embedding (instantiate candidate value) := by
  rw [instantiate_comp, instantiate_comp]
  congr 1
  funext identity
  exact instantiate_generator (instanceAssignment locals localBodies embedding candidate) (.inr identity)

theorem instance_after_capture_transport (localBodies : Assignment locals future)
    (embedding : Assignment next future) (candidate : Assignment later next)
    (change : Assignment captures later) :
    Assignment.compose (instanceAssignment locals localBodies embedding candidate)
        (ContextualStoredRows.liftCaptures locals change) =
      instanceAssignment locals localBodies embedding (Assignment.compose candidate change) := by
  funext identity
  cases identity with
  | inl identity => exact instantiate_generator (instanceAssignment locals localBodies embedding candidate) (.inl identity)
  | inr identity => exact instance_on_shared_value locals localBodies embedding candidate (change identity)

theorem instantiated_transported_body (localBodies : Assignment locals future)
    (embedding : Assignment next future) (candidate : Assignment later next)
    (change : Assignment captures later) {Γ : Ctx S} {sort : S.Srt}
    (body : Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort) :
    instantiate (instanceAssignment locals localBodies embedding candidate)
        (instantiate (ContextualStoredRows.liftCaptures locals change) body) =
      instantiate (instanceAssignment locals localBodies embedding (Assignment.compose candidate change)) body := by
  rw [instantiate_comp]
  exact congrArg (fun assignment => instantiate assignment body)
    (instance_after_capture_transport locals localBodies embedding candidate change)

theorem matches_after_capture_transport (change : Assignment captures later)
    (candidate : Assignment later next) {Γ : Ctx S} {sort : S.Srt}
    (pattern : Term (signature S next) Γ sort) (row : ContextualStoredRows.Row locals captures Γ sort) :
    Matches locals candidate pattern (row.map locals change) ↔
      Matches locals (Assignment.compose candidate change) pattern row := by
  cases row with
  | shared value => simp only [ContextualStoredRows.Row.map, Matches, Assignment.instantiate_compose]
  | schema body =>
      constructor
      · rintro ⟨extension, localBodies, same⟩
        refine ⟨extension, localBodies, ?_⟩
        exact (instantiated_transported_body locals localBodies extension.assignment candidate change body).symm.trans same
      · rintro ⟨extension, localBodies, same⟩
        refine ⟨extension, localBodies, ?_⟩
        exact (instantiated_transported_body locals localBodies extension.assignment candidate change body).trans same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardMatching
