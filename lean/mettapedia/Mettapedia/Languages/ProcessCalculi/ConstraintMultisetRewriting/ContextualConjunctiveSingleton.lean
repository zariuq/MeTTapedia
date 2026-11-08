import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardRefutation

/-!
# A capture-only singleton query is exactly the existing absence ask

The comparison is at the all-future guard contract. A singleton witness may
extend its supplied model; the original ask applies to that same extended
model. No false reflection from a larger pointwise model into a smaller
declaration family, or globally inhabited declaration carrier, is needed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveSingleton

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualGuardMatching

universe u
variable {S : Signature} {Local Shared Next : Type} {O : Type u}
  (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
  {next : Next → MetaArity S}

def noQueries : Empty → MetaArity S := fun impossible => nomatch impossible

def pattern {Γ : Ctx S} {sort : S.Srt} (value : Term (signature S captures) Γ sort) :=
  instantiate (ContextualSelectionViews.capturedSource (noQueries (S := S)) captures) value

theorem old_match_gives_singleton (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (value : Term (signature S captures) Γ sort) (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (occurrence : O) (matched : ContextualGuardMatching.Matches locals candidate (instantiate candidate value) (rows occurrence)) :
    ContextualConjunctiveQueries.Matches noQueries locals captures candidate [pattern captures value] rows (fun _ => occurrence) := by
  let queryBodies : {Future : Type} → (future : Future → MetaArity S) → Assignment (noQueries (S := S)) future :=
    fun _ impossible => nomatch impossible
  cases rowCase : rows occurrence with
  | schema body =>
      rw [rowCase] at matched
      change ContextualGuardMatching.Matches locals candidate (instantiate candidate value) (.schema body) at matched
      obtain ⟨extension, bodies, same⟩ := matched
      refine ⟨extension, queryBodies extension.declarations, (fun name : ScopedVar Local => bodies name.name), ?_⟩
      intro port
      have only : port = 0 := Fin.ext (by change port.val = 0; have bound : port.val < 1 := port.isLt; omega)
      subst port
      rw [rowCase]
      exact same.trans (instance_on_shared_value noQueries (queryBodies extension.declarations)
        extension.assignment candidate value).symm
  | shared body =>
      rw [rowCase] at matched
      change instantiate candidate value = instantiate candidate body at matched
      let extension := Extension.withLocals locals next
      let bodies : Assignment (ContextualConjunctiveQueries.rowLocals locals) extension.declarations :=
        fun name => generator extension.declarations (.inl name.name)
      refine ⟨extension, queryBodies extension.declarations, bodies, ?_⟩
      intro port
      have only : port = 0 := Fin.ext (by change port.val = 0; have bound : port.val < 1 := port.isLt; omega)
      subst port
      rw [rowCase]
      exact (instance_on_shared_value locals (fun name => bodies (ScopedVar.at 2 name)) extension.assignment candidate body).trans
        ((congrArg (instantiate extension.assignment) matched.symm).trans
          (instance_on_shared_value noQueries (queryBodies extension.declarations) extension.assignment candidate value).symm)

theorem ask_iff_existing_absence {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (value : Term (signature S captures) Γ sort)
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O) :
    ContextualConjunctiveAbsence.Ask noQueries locals captures problem [pattern captures value] rows world ↔
      ContextualGuardSemantics.Ask locals problem rows world (.absent value) := by
  constructor
  · intro absent Next next candidate solved occurrence present matched
    exact absent Next next candidate solved (fun _ => occurrence) (fun _ => present)
      (old_match_gives_singleton locals captures candidate value rows occurrence matched)
  · intro absent Next next candidate solved chosen present matched
    obtain ⟨extension, queryBodies, rowBodies, agrees⟩ := matched
    let changed := Assignment.compose extension.assignment candidate
    have changedModels := ContextualFrameUnifier.models_compose solved extension.assignment
    have same := agrees 0
    have patternLaw := instance_on_shared_value noQueries queryBodies extension.assignment candidate value
    have samePattern :
        instantiate (instanceAssignment noQueries queryBodies extension.assignment candidate) (pattern captures value) =
          instantiate changed value := patternLaw.trans (Assignment.instantiate_compose extension.assignment candidate value).symm
    apply absent extension.Names extension.declarations changed changedModels (chosen 0) (present 0)
    cases rowCase : rows (chosen 0) with
    | schema body =>
        let bodies : Assignment locals extension.declarations :=
          fun name => rowBodies (ScopedVar.at 2 name)
        have instanceSame : instanceAssignment locals bodies (generator extension.declarations) changed =
            instanceAssignment locals bodies extension.assignment candidate := by
          funext name
          cases name with
          | inl name => rfl
          | inr name => exact instantiate_identity _
        refine ⟨Extension.identity extension.declarations, bodies, ?_⟩
        change instantiate (instanceAssignment locals bodies (generator extension.declarations) changed) body =
          instantiate (generator extension.declarations) (instantiate changed value)
        rw [instanceSame, instantiate_identity]
        change instantiate (instanceAssignment locals bodies extension.assignment candidate)
          (ContextualStoredRows.asTemplate locals captures (rows (chosen 0))) = _ at same
        rw [rowCase] at same
        exact same.trans samePattern
    | shared body =>
        have valueLaw := instance_on_shared_value locals (fun name => rowBodies (ScopedVar.at 2 name))
          extension.assignment candidate body
        rw [rowCase] at same
        exact (Assignment.instantiate_compose extension.assignment candidate value).trans
          (patternLaw.symm.trans (same.symm.trans
            (valueLaw.trans (Assignment.instantiate_compose extension.assignment candidate body).symm)))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveSingleton
