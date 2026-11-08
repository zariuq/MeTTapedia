import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchematicStorage
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExtensionSplitting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualComputedFreshFrame
import Mettapedia.OSLF.Syntax.ContextualRigidTerms

/-!
# Reusable publication after actual contextual solving

A reusable atom preserves the substitution already computed by the firing.
Its remaining variables become private to each later use. The returned
declaration family supplies those variables, including new helper arities.
The old private family is extended explicitly, without assuming that a later
model already has an inhabitant at every new arity.

The publication theorem compares schema matching with an independent source
relation: instances of the original template under solutions of the original
equation problem. Unfinished solver queues are not discarded.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublication

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching

variable {S : Signature} {Local V Shared Next : Type}
    (locals : Local → MetaArity S) (declaration : V → MetaArity S)
    {captures : Shared → MetaArity S} {next : Next → MetaArity S}

abbrev privateFamily : Local ⊕ V → MetaArity S := Sum.elim locals declaration

def newPrivate : Assignment declaration (privateFamily locals declaration) :=
  fun identity => generator (privateFamily locals declaration) (.inr identity)

def oldPrivate : Assignment locals (privateFamily locals declaration) :=
  fun identity => generator (privateFamily locals declaration) (.inl identity)

def ordinary {Γ : Ctx S} {sort : S.Srt} (value : Term (signature S declaration) Γ sort) :
    ContextualStoredRows.Row (privateFamily locals declaration) captures Γ sort :=
  ContextualStoredRows.store (privateFamily locals declaration) captures
    (instantiate (newPrivate locals declaration) value)

def Instances {Γ : Ctx S} {sort : S.Srt} (value : Term (signature S declaration) Γ sort)
    (next : Next → MetaArity S) (pattern : Term (signature S next) Γ sort) : Prop :=
  ∃ extension : Extension next, ∃ images : Assignment declaration extension.declarations,
    instantiate images value = instantiate extension.assignment pattern

theorem instantiate_store {Future : Type} {future : Future → MetaArity S}
    (images : Assignment locals future) (embedding : Assignment next future)
    (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (value : Term (signature S locals) Γ sort) :
    instantiate (instanceAssignment locals images embedding candidate)
      (instantiate (ContextualStoredRows.privateSource locals captures) value) = instantiate images value := by
  rw [instantiate_comp]
  apply congrArg (fun assignment => instantiate assignment value)
  funext identity
  exact instantiate_generator (instanceAssignment locals images embedding candidate) (.inl identity)

theorem instantiate_newPrivate {Future : Type} {future : Future → MetaArity S}
    (images : Assignment (privateFamily locals declaration) future)
    {Γ : Ctx S} {sort : S.Srt} (value : Term (signature S declaration) Γ sort) :
    instantiate images (instantiate (newPrivate locals declaration) value) =
      instantiate (fun identity => images (.inr identity)) value := by
  rw [instantiate_comp]
  apply congrArg (fun assignment => instantiate assignment value)
  funext identity
  exact instantiate_generator images (.inr identity)

/-- Extra unused private arities get fresh formal generators in a genuine
extension. They need no arbitrary terms in the model's original family. -/
theorem ordinary_matches_iff (candidate : Assignment captures next)
    {Γ : Ctx S} {sort : S.Srt} (value : Term (signature S declaration) Γ sort)
    (pattern : Term (signature S next) Γ sort) :
    Matches (privateFamily locals declaration) candidate pattern (ordinary locals declaration value) ↔
      Instances declaration value next pattern := by
  constructor
  · rintro ⟨extension,images,same⟩
    refine ⟨extension,fun identity => images (.inr identity),?_⟩
    change instantiate (instanceAssignment (privateFamily locals declaration) images extension.assignment candidate)
      (instantiate (ContextualStoredRows.privateSource (privateFamily locals declaration) captures)
        (instantiate (newPrivate locals declaration) value)) = _ at same
    rw [instantiate_store,instantiate_newPrivate] at same
    exact same
  · rintro ⟨extension,images,same⟩
    let added := Extension.withLocals locals extension.declarations
    let images' : Assignment (privateFamily locals declaration) added.declarations
      | .inl identity => generator added.declarations (.inl identity)
      | .inr identity => instantiate added.assignment (images identity)
    refine ⟨extension.trans added,images',?_⟩
    change instantiate (instanceAssignment (privateFamily locals declaration) images'
      (extension.trans added).assignment candidate)
        (instantiate (ContextualStoredRows.privateSource (privateFamily locals declaration) captures)
          (instantiate (newPrivate locals declaration) value)) = _
    erw [instantiate_store,instantiate_newPrivate,Extension.trans_assignment]
    have mapped := congrArg (instantiate added.assignment) same
    exact (Assignment.instantiate_compose added.assignment images value).trans
      (mapped.trans (Assignment.instantiate_compose added.assignment extension.assignment pattern).symm)

theorem ordinary_is_independent_of_caller {Other : Type} {other : Other → MetaArity S}
    (first : Assignment captures next) (second : Assignment other next)
    {Γ : Ctx S} {sort : S.Srt} (value : Term (signature S declaration) Γ sort)
    (pattern : Term (signature S next) Γ sort) :
    Matches (privateFamily locals declaration) first pattern
        (ordinary locals declaration value : ContextualStoredRows.Row _ captures Γ sort) ↔
      Matches (privateFamily locals declaration) second pattern
        (ordinary locals declaration value : ContextualStoredRows.Row _ other Γ sort) :=
  (ordinary_matches_iff locals declaration first value pattern).trans
    (ordinary_matches_iff locals declaration second value pattern).symm

/-- Values without contextual unknowns have the same matching observations
under either storage kind. This is a semantic erasure law, not a cost claim. -/
theorem rigid_publication_matches_shared (candidate : Assignment captures next)
    {Γ : Ctx S} {sort : S.Srt} (value : Term S Γ sort) (pattern : Term (signature S next) Γ sort) :
    Matches (privateFamily locals declaration) candidate pattern
        (ordinary locals declaration (Rigid.includeTerm declaration value)) ↔
      Matches locals candidate pattern (.shared (Rigid.includeTerm captures value)) := by
  rw [ordinary_matches_iff]
  change Instances declaration (Rigid.includeTerm declaration value) next pattern ↔
    pattern = instantiate candidate (Rigid.includeTerm captures value)
  rw [Rigid.instantiate_include]
  constructor
  · rintro ⟨extension,images,same⟩
    rw [Rigid.instantiate_include] at same
    apply extension.instantiate_injective
    exact same.symm.trans (Rigid.instantiate_include extension.assignment value).symm
  · intro same
    subst pattern
    let extension := Extension.withLocals declaration next
    refine ⟨extension,fun identity => generator extension.declarations (.inl identity),?_⟩
    exact (Rigid.instantiate_include
      (fun identity => generator (ContextualSelectionViews.source declaration next) (.inl identity)) value).trans
        (Rigid.instantiate_include extension.assignment value).symm

variable {locals declaration}
    {Original : Type} {source : Original → MetaArity S}

/-- Source meaning at publication: an original joint solution supplies the
template value. This relation mentions no chosen solver representation. -/
def SourceInstances (problem : ContextualResidual.Problem source)
    {Γ : Ctx S} {sort : S.Srt} (template : Term (signature S source) Γ sort)
    (next : Next → MetaArity S) (pattern : Term (signature S next) Γ sort) : Prop :=
  ∃ extension : Extension next, ∃ candidate : Assignment source extension.declarations,
    ContextualResidual.Models candidate problem ∧
      instantiate candidate template = instantiate extension.assignment pattern

theorem completed_instances_iff {problem : ContextualResidual.Problem source}
    (update : ContextualFrameUpdate.Update problem) (finished : update.remaining = [])
    {Γ : Ctx S} {sort : S.Srt} (template : Term (signature S source) Γ sort)
    (next : Next → MetaArity S) (pattern : Term (signature S next) Γ sort) :
    Instances update.declaration (instantiate update.answer template) next pattern ↔
      SourceInstances problem template next pattern := by
  constructor
  · rintro ⟨extension,images,same⟩
    refine ⟨extension,Assignment.compose images update.answer,?_,?_⟩
    · exact update.valid.sound extension.declarations images (by simp [finished,ContextualResidual.Models])
    · exact (Assignment.instantiate_compose images update.answer template).trans same
  · rintro ⟨extension,candidate,model,same⟩
    obtain ⟨images,_,components⟩ := update.factors extension.declarations candidate model
    exact ⟨extension,images,(ContextualFrameUnifier.factor_terms candidate update.answer images components template).symm.trans same⟩

theorem completed_ordinary_matches_iff (locals : Local → MetaArity S)
    {problem : ContextualResidual.Problem source} (update : ContextualFrameUpdate.Update problem)
    (finished : update.remaining = []) (candidate : Assignment captures next)
    {Γ : Ctx S} {sort : S.Srt} (template : Term (signature S source) Γ sort)
    (pattern : Term (signature S next) Γ sort) :
    Matches (privateFamily locals update.declaration) candidate pattern
      (ordinary locals update.declaration (instantiate update.answer template)) ↔
        SourceInstances problem template next pattern :=
  (ordinary_matches_iff locals update.declaration candidate _ pattern).trans
    (completed_instances_iff update finished template next pattern)

/-- Different completed solver representations produce the same reusable
row instances, including different helper families. -/
theorem completed_publications_agree (locals : Local → MetaArity S)
    {problem : ContextualResidual.Problem source}
    (first second : ContextualFrameUpdate.Update problem)
    (firstFinished : first.remaining = []) (secondFinished : second.remaining = [])
    (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (template : Term (signature S source) Γ sort) (pattern : Term (signature S next) Γ sort) :
    Matches (privateFamily locals first.declaration) candidate pattern
        (ordinary locals first.declaration (instantiate first.answer template)) ↔
      Matches (privateFamily locals second.declaration) candidate pattern
        (ordinary locals second.declaration (instantiate second.answer template)) :=
  (completed_ordinary_matches_iff locals first firstFinished candidate template pattern).trans
    (completed_ordinary_matches_iff locals second secondFinished candidate template pattern).symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublication
