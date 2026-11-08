import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardSemantics

/-!
# Existing rows survive extension of the private declaration bank

New reusable outputs may contain helper arities returned by the actual
solver. The private bank therefore extends from old locals to old locals
plus returned declarations. Reindexing old templates changes neither their
capture identities nor their schema-instance and physical-count semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublication

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching

universe u
variable {S : Signature} {Local V Shared Next : Type} {O : Type u}
    (locals : Local → MetaArity S) (declaration : V → MetaArity S)
    {captures : Shared → MetaArity S} {next : Next → MetaArity S}

def includePrivate : Assignment (ContextualSelectionViews.source locals captures)
    (ContextualSelectionViews.source (privateFamily locals declaration) captures)
  | .inl identity => generator (ContextualSelectionViews.source (privateFamily locals declaration) captures)
      (.inl (.inl identity))
  | .inr identity => generator (ContextualSelectionViews.source (privateFamily locals declaration) captures)
      (.inr identity)

def extendPrivate {Γ : Ctx S} {sort : S.Srt} :
    ContextualStoredRows.Row locals captures Γ sort →
      ContextualStoredRows.Row (privateFamily locals declaration) captures Γ sort
  | .schema body => .schema (instantiate (includePrivate locals declaration) body)
  | .shared value => .shared value

theorem instance_includePrivate {Future : Type} {future : Future → MetaArity S}
    (images : Assignment (privateFamily locals declaration) future)
    (embedding : Assignment next future) (candidate : Assignment captures next) :
    Assignment.compose (instanceAssignment (privateFamily locals declaration) images embedding candidate)
        (includePrivate locals declaration) =
      instanceAssignment locals (fun identity => images (.inl identity)) embedding candidate := by
  funext identity
  cases identity <;> exact instantiate_generator _ _

theorem extended_instance {Future : Type} {future : Future → MetaArity S}
    (images : Assignment (privateFamily locals declaration) future)
    (embedding : Assignment next future) (candidate : Assignment captures next)
    {Γ : Ctx S} {sort : S.Srt}
    (body : Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort) :
    instantiate (instanceAssignment (privateFamily locals declaration) images embedding candidate)
        (instantiate (includePrivate locals declaration) body) =
      instantiate (instanceAssignment locals (fun identity => images (.inl identity)) embedding candidate) body := by
  rw [← Assignment.instantiate_compose,instance_includePrivate]

theorem extendPrivate_matches_iff (candidate : Assignment captures next)
    {Γ : Ctx S} {sort : S.Srt} (pattern : Term (signature S next) Γ sort)
    (row : ContextualStoredRows.Row locals captures Γ sort) :
    Matches (privateFamily locals declaration) candidate pattern (extendPrivate locals declaration row) ↔
      Matches locals candidate pattern row := by
  cases row with
  | shared value => rfl
  | schema body =>
      constructor
      · rintro ⟨extension,images,same⟩
        refine ⟨extension,fun identity => images (.inl identity),?_⟩
        exact (extended_instance locals declaration images extension.assignment candidate body).symm.trans same
      · rintro ⟨extension,images,same⟩
        let added := Extension.withLocals declaration extension.declarations
        let images' : Assignment (privateFamily locals declaration) added.declarations
          | .inl identity => instantiate added.assignment (images identity)
          | .inr identity => generator added.declarations (.inl identity)
        refine ⟨extension.trans added,images',?_⟩
        change instantiate (instanceAssignment (privateFamily locals declaration) images'
            (extension.trans added).assignment candidate)
          (instantiate (includePrivate locals declaration) body) = _
        erw [extended_instance,Extension.trans_assignment]
        have mapped := congrArg (instantiate added.assignment) same
        have sameAssignments :
            (fun identity => instantiate added.assignment
              (instanceAssignment locals images extension.assignment candidate identity)) =
            instanceAssignment locals (fun identity => images' (.inl identity))
              (Assignment.compose added.assignment extension.assignment) candidate := by
          funext identity
          cases identity with
          | inl identity => rfl
          | inr identity => exact instantiate_comp extension.assignment added.assignment (candidate identity)
        have left := (instantiate_comp (instanceAssignment locals images extension.assignment candidate)
          added.assignment body).trans
            (congrArg (fun assignment => instantiate assignment body) sameAssignments)
        exact left.symm.trans
          (mapped.trans (Assignment.instantiate_compose added.assignment extension.assignment pattern).symm)

theorem region_extendPrivate (candidate : Assignment captures next)
    {Γ : Ctx S} {sort : S.Srt} (pattern : Term (signature S captures) Γ sort)
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O) :
    ContextualGuardSemantics.region (privateFamily locals declaration) candidate
        (fun occurrence => extendPrivate locals declaration (rows occurrence)) world pattern =
      ContextualGuardSemantics.region locals candidate rows world pattern := by
  classical
  apply Finset.ext
  intro occurrence
  simp only [ContextualGuardSemantics.mem_region,extendPrivate_matches_iff]

theorem holds_extendPrivate (candidate : Assignment captures next)
    {Γ : Ctx S} {sort : S.Srt} (check : Check (Term (signature S captures) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O) :
    ContextualGuardSemantics.Holds (privateFamily locals declaration) candidate
        (fun occurrence => extendPrivate locals declaration (rows occurrence)) world check ↔
      ContextualGuardSemantics.Holds locals candidate rows world check := by
  cases check with
  | equal _ _ => rfl
  | absent pattern => simp only [ContextualGuardSemantics.Holds,extendPrivate_matches_iff]
  | count pattern number => simp only [ContextualGuardSemantics.Holds,region_extendPrivate]

theorem ask_extendPrivate {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (check : Check (Term (signature S captures) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O) :
    ContextualGuardSemantics.Ask (privateFamily locals declaration) problem
        (fun occurrence => extendPrivate locals declaration (rows occurrence)) world check ↔
      ContextualGuardSemantics.Ask locals problem rows world check := by
  constructor <;> intro asked Future future candidate model
  · exact (holds_extendPrivate locals declaration candidate check rows world).mp (asked Future future candidate model)
  · exact (holds_extendPrivate locals declaration candidate check rows world).mpr (asked Future future candidate model)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublication
