import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionPaths
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExtensionAsks
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExtensionModels

/-!
# Actual contextual paths conservatively transport retained prefix snapshots

Each actual edge includes captured names and the computed helper frame.
Their injective composition transports the complete original inventory,
without its future equations or physical effects. Original all-future asks
reflect on that explicit prefix snapshot, not on the final mutated world.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecution

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching ContextualWorldScopeLedger ContextualScopeSupport

variable {S : Signature} {Local O : Type} (locals : Local → MetaArity S)
  {Γ : Ctx S} {sort : S.Srt}

namespace Endpoint

variable {locals}

def namesEquiv {first second : Endpoint locals O Γ sort} (same : first = second) : first.Names ≃ second.Names :=
  Equiv.cast (congrArg Endpoint.Names same)

theorem namesEquiv_preserves {first second : Endpoint locals O Γ sort} (same : first = second) (name : first.Names) :
    second.declarations (namesEquiv same name) = first.declarations name := by
  cases same
  rfl

theorem namesEquiv_scopes {first second : Endpoint locals O Γ sort} (same : first = second) (name : first.Names) :
    second.scopes (namesEquiv same name) = first.scopes name := by
  cases same
  rfl

end Endpoint

variable [DecidableEq O] [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

namespace Firing

variable {locals} {before after : Endpoint locals O Γ sort}

def captureName (firing : Firing locals before after) (name : before.Names) : after.Names :=
  Endpoint.namesEquiv firing.destination.symm (.inl (.inr name))

theorem captureName_injective (firing : Firing locals before after) : Function.Injective firing.captureName := by
  intro first second same
  have old := (Endpoint.namesEquiv firing.destination.symm).injective same
  exact Sum.inr.inj (Sum.inl.inj old)

theorem captureName_preserves (firing : Firing locals before after) (name : before.Names) :
    after.declarations (firing.captureName name) = before.declarations name :=
  Endpoint.namesEquiv_preserves firing.destination.symm (.inl (.inr name))

theorem captureName_scopes (firing : Firing locals before after) (name : before.Names) :
    after.scopes (firing.captureName name) = before.scopes name :=
  Endpoint.namesEquiv_scopes firing.destination.symm (.inl (.inr name))

def captureExtension (firing : Firing locals before after) : Extension before.declarations where
  Names := after.Names
  declarations := after.declarations
  name := firing.captureName
  injective := firing.captureName_injective
  preserves := firing.captureName_preserves

end Firing

variable {locals}

def namesAlong {source : Endpoint locals O Γ sort} : {target : Endpoint locals O Γ sort} →
    Quiver.Path source target → source.Names → target.Names
  | _, .nil => id
  | _, .cons past edge => edge.captureName ∘ namesAlong past

theorem namesAlong_injective {source target : Endpoint locals O Γ sort} (path : Quiver.Path source target) :
    Function.Injective (namesAlong path) := by
  induction path with
  | nil => exact Function.injective_id
  | cons past edge earlier => exact edge.captureName_injective.comp earlier

theorem namesAlong_preserves {source target : Endpoint locals O Γ sort} (path : Quiver.Path source target)
    (name : source.Names) : target.declarations (namesAlong path name) = source.declarations name := by
  induction path with
  | nil => rfl
  | cons past edge earlier => exact (edge.captureName_preserves _).trans earlier

theorem namesAlong_scopes {source target : Endpoint locals O Γ sort} (path : Quiver.Path source target)
    (name : source.Names) : target.scopes (namesAlong path name) = source.scopes name := by
  induction path with
  | nil => rfl
  | cons past edge earlier => exact (edge.captureName_scopes _).trans earlier

def pathExtension {source target : Endpoint locals O Γ sort} (path : Quiver.Path source target) :
    Extension source.declarations where
  Names := target.Names
  declarations := target.declarations
  name := namesAlong path
  injective := namesAlong_injective path
  preserves := namesAlong_preserves path

def pathAssignment {source target : Endpoint locals O Γ sort} (path : Quiver.Path source target) :
    Assignment source.declarations target.declarations := (pathExtension path).assignment

theorem namesAlong_comp {source middle target : Endpoint locals O Γ sort}
    (first : Quiver.Path source middle) (second : Quiver.Path middle target) :
    namesAlong (first.comp second) = namesAlong second ∘ namesAlong first := by
  induction second with
  | nil => rfl
  | cons past edge earlier =>
      funext name
      change edge.captureName (namesAlong (first.comp past) name) =
        edge.captureName (namesAlong past (namesAlong first name))
      rw [earlier]
      rfl

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
private theorem reindex_congr {V W : Type} {source : V → MetaArity S} {target : W → MetaArity S}
    {first second : V → W} (same : first = second)
    (firstPreserves : ∀ name, target (first name) = source name)
    (secondPreserves : ∀ name, target (second name) = source name) :
    reindex first firstPreserves = reindex second secondPreserves := by
  cases same
  rfl

theorem pathAssignment_comp {source middle target : Endpoint locals O Γ sort}
    (first : Quiver.Path source middle) (second : Quiver.Path middle target) :
    pathAssignment (first.comp second) = Assignment.compose (pathAssignment second) (pathAssignment first) := by
  unfold pathAssignment pathExtension Extension.assignment
  rw [reindex_compose]
  exact reindex_congr (namesAlong_comp first second) _ _

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
private theorem term_castMetaBody {V : Type} {declaration : V → MetaArity S} (scopes : V → Finset Nat)
    {first second : MetaArity S} (same : first = second)
    (value : Term (signature S declaration) first.1 first.2) :
    term scopes (castMetaBody (V := signature S declaration) same value) = term scopes value := by
  cases same
  rfl

theorem pathAssignment_respects_scopes {source target : Endpoint locals O Γ sort} (path : Quiver.Path source target) :
    Respects source.scopes target.scopes (pathAssignment path) := by
  intro name
  unfold Covered pathAssignment pathExtension Extension.assignment reindex
  rw [term_castMetaBody, term_generator, namesAlong_scopes]

def prefixSnapshot {source target : Endpoint locals O Γ sort} (path : Quiver.Path source target) :
    Inventory locals target.declarations (O := O) Γ sort :=
  mapInventory locals source.declarations (pathAssignment path) source.inventory

omit [DecidableEq O] [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
private theorem mapInventory_compose {V W X : Type} {source : V → MetaArity S}
    {middle : W → MetaArity S} {target : X → MetaArity S}
    (first : Assignment source middle) (second : Assignment middle target)
    (original : Inventory locals source (O := O) Γ sort) :
    mapInventory locals middle second (mapInventory locals source first original) =
      mapInventory locals source (Assignment.compose second first) original := by
  cases original
  simp only [mapInventory, ContextualFrameUnifier.mapProblem, List.map_map, Function.comp_def,
    ← Assignment.instantiate_compose, instantiateObservation_comp,
    ContextualStoredRows.Row.map_compose, ContextualStoredRows.liftCaptures_compose]

theorem prefixSnapshot_comp {source middle target : Endpoint locals O Γ sort}
    (first : Quiver.Path source middle) (second : Quiver.Path middle target) :
    prefixSnapshot (first.comp second) =
      mapInventory locals middle.declarations (pathAssignment second) (prefixSnapshot first) := by
  unfold prefixSnapshot
  rw [pathAssignment_comp]
  exact (mapInventory_compose (pathAssignment first) (pathAssignment second) source.inventory).symm

theorem prefixSnapshot_present {source target : Endpoint locals O Γ sort} (path : Quiver.Path source target) :
    (prefixSnapshot path).configuration.present = source.inventory.configuration.present := rfl

theorem prefixSnapshot_covered {source target : Endpoint locals O Γ sort} (path : Quiver.Path source target) :
    CoveredWorld locals target.declarations target.scopes source.occupied (prefixSnapshot path) :=
  mapInventory_covered locals source.declarations source.scopes target.scopes (pathAssignment path)
    (pathAssignment_respects_scopes path) source.inventory source.covered

theorem ask_prefixSnapshot_iff {source target : Endpoint locals O Γ sort} (path : Quiver.Path source target)
    (check : Check (Term (signature S source.declarations) Γ sort)) :
    ContextualGuardSemantics.Ask locals (prefixSnapshot path).configuration.equations
        (prefixSnapshot path).rows (prefixSnapshot path).configuration.present
        (check.map (instantiate (pathAssignment path))) ↔
      ContextualGuardSemantics.Ask locals source.inventory.configuration.equations source.inventory.rows
        source.inventory.configuration.present check :=
  ContextualGuardSemantics.Ask.extension_iff locals (pathExtension path)
    source.inventory.configuration.equations source.inventory.rows source.inventory.configuration.present check

theorem exists_prefixSnapshot_model_iff {source target : Endpoint locals O Γ sort} (path : Quiver.Path source target) :
    (∃ (Future : Type) (future : Future → MetaArity S) (candidate : Assignment target.declarations future),
      ContextualFrameUnifier.Models candidate (prefixSnapshot path).configuration.equations) ↔
    ∃ (Future : Type) (future : Future → MetaArity S) (candidate : Assignment source.declarations future),
      ContextualFrameUnifier.Models candidate source.inventory.configuration.equations :=
  (pathExtension path).exists_model_iff source.inventory.configuration.equations

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecution
