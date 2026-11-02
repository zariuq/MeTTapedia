import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUnusedConjunctive

/-!
# Joined source queries retain exact ports through capture transport

Mapping a pattern list changes its declaration family, not its port count
or physical choices. The explicit inverse port maps keep repeated physical
reads and the shared query assignment unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveQueries

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualGuardMatching

universe u
variable {S : Signature} {Query Local Shared Later Next : Type} {O : Type u}
  (queries : Query → MetaArity S) (locals : Local → MetaArity S)
  {captures : Shared → MetaArity S} {later : Later → MetaArity S} {next : Next → MetaArity S}

def mapPatterns (change : Assignment captures later) {Γ : Ctx S} {sort : S.Srt}
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort)) :
    List (Term (signature S (queryFamily queries later)) Γ sort) :=
  patterns.map (instantiate (ContextualStoredRows.liftCaptures queries change))

def sourcePort (change : Assignment captures later) {Γ : Ctx S} {sort : S.Srt}
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (port : Fin (mapPatterns queries change patterns).length) : Fin patterns.length :=
  ⟨port.val, by simpa only [mapPatterns, List.length_map] using port.isLt⟩

def targetPort (change : Assignment captures later) {Γ : Ctx S} {sort : S.Srt}
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (port : Fin patterns.length) : Fin (mapPatterns queries change patterns).length :=
  ⟨port.val, by simpa only [mapPatterns, List.length_map] using port.isLt⟩

@[simp] theorem source_target (change : Assignment captures later) {Γ : Ctx S} {sort : S.Srt}
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort)) (port : Fin patterns.length) :
    sourcePort queries change patterns (targetPort queries change patterns port) = port := rfl

@[simp] theorem target_source (change : Assignment captures later) {Γ : Ctx S} {sort : S.Srt}
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (port : Fin (mapPatterns queries change patterns).length) :
    targetPort queries change patterns (sourcePort queries change patterns port) = port := rfl

@[simp] theorem rowScope_targetPort (change : Assignment captures later) {Γ : Ctx S} {sort : S.Srt}
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort)) (port : Fin patterns.length) :
    rowScope (targetPort queries change patterns port) = rowScope port := rfl

@[simp] theorem rowScope_sourcePort (change : Assignment captures later) {Γ : Ctx S} {sort : S.Srt}
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (port : Fin (mapPatterns queries change patterns).length) :
    rowScope (sourcePort queries change patterns port) = rowScope port := rfl

theorem mapPatterns_get (change : Assignment captures later) {Γ : Ctx S} {sort : S.Srt}
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (port : Fin (mapPatterns queries change patterns).length) :
    (mapPatterns queries change patterns).get port =
      instantiate (ContextualStoredRows.liftCaptures queries change)
        (patterns.get (sourcePort queries change patterns port)) := by
  exact List.getElem_map (instantiate (ContextualStoredRows.liftCaptures queries change))
    (l := patterns) (i := port.val) (h := port.isLt)

def mapChoice (change : Assignment captures later) {Γ : Ctx S} {sort : S.Srt}
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (chosen : Fin patterns.length → O) : Fin (mapPatterns queries change patterns).length → O :=
  fun port => chosen (sourcePort queries change patterns port)

def restoreChoice (change : Assignment captures later) {Γ : Ctx S} {sort : S.Srt}
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (chosen : Fin (mapPatterns queries change patterns).length → O) : Fin patterns.length → O :=
  fun port => chosen (targetPort queries change patterns port)

@[simp] theorem map_restore_choice (change : Assignment captures later) {Γ : Ctx S} {sort : S.Srt}
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (chosen : Fin (mapPatterns queries change patterns).length → O) :
    mapChoice queries change patterns (restoreChoice queries change patterns chosen) = chosen := by
  funext port
  exact congrArg chosen (target_source queries change patterns port)

@[simp] theorem restore_map_choice (change : Assignment captures later) {Γ : Ctx S} {sort : S.Srt}
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (chosen : Fin patterns.length → O) :
    restoreChoice queries change patterns (mapChoice queries change patterns chosen) = chosen := by
  funext port
  exact congrArg chosen (source_target queries change patterns port)

theorem matches_after_capture_transport (change : Assignment captures later)
    (candidate : Assignment later next) {Γ : Ctx S} {sort : S.Srt}
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (chosen : Fin patterns.length → O) :
    Matches queries locals later candidate (mapPatterns queries change patterns)
        (fun occurrence => (rows occurrence).map locals change) (mapChoice queries change patterns chosen) ↔
      Matches queries locals captures (Assignment.compose candidate change) patterns rows chosen := by
  constructor
  · rintro ⟨extension, queryBodies, rowBodies, agrees⟩
    refine ⟨extension, queryBodies, rowBodies, ?_⟩
    intro port
    have matched := agrees (targetPort queries change patterns port)
    simpa only [mapChoice, source_target, rowScope_targetPort, mapPatterns_get,
      ContextualStoredRows.asTemplate_map,
      ContextualGuardMatching.instantiated_transported_body locals
        (fun name => rowBodies (ScopedVar.at (rowScope port) name)) extension.assignment candidate change
          (ContextualStoredRows.asTemplate locals captures (rows (chosen port))),
      ContextualGuardMatching.instantiated_transported_body queries queryBodies extension.assignment candidate change
        (patterns.get port)] using matched
  · rintro ⟨extension, queryBodies, rowBodies, agrees⟩
    refine ⟨extension, queryBodies, rowBodies, ?_⟩
    intro port
    have matched := agrees (sourcePort queries change patterns port)
    simpa only [mapChoice, rowScope_sourcePort, mapPatterns_get,
      ContextualStoredRows.asTemplate_map,
      ContextualGuardMatching.instantiated_transported_body locals
        (fun name => rowBodies (ScopedVar.at (rowScope port) name)) extension.assignment candidate change
          (ContextualStoredRows.asTemplate locals captures (rows (chosen (sourcePort queries change patterns port)))),
      ContextualGuardMatching.instantiated_transported_body queries queryBodies extension.assignment candidate change
        (patterns.get (sourcePort queries change patterns port))] using matched

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveQueries
