import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUpdate
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentTypedInversion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentProjectionInversion

/-!
# A computed flexible-variable elimination rule with typed eta

The left side is compared with the newest metavariable by the actual typed
eta converter. Direct checked recovery is retained; if it does not finish,
the independently typed right side is normalized and recovery is retried.
Both paths establish typed equality with the original endpoint.
Successful reconstruction supplies the answer;
the entire residual queue is then instantiated and scanned. Every successful
result carries both solution reconstruction and factorization.

The operation accepts eta-expanded function heads and arbitrary dependent
declared types. It is one driver rule, not a complete pattern-selection or
pruning algorithm. A failed bounded check returns no update, not a refutation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentFlex

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentTypedInversion ContextualDependentUpdate

variable {Head : Type} {rules : Rules Head}

def withoutNewest (Γ : Context rules) (type : TypeOver Γ) : Inclusion Γ (extend Γ type) where
  forward := wk
  injective := Fin.succ_injective Γ.arity
  typed := (projectionHom Γ type).typed

theorem withoutNewest_hom (Γ : Context rules) (type : TypeOver Γ) :
    (withoutNewest Γ type).hom = projectionHom Γ type := by
  apply Hom.ext
  rfl

def equation {Γ : Context rules} {type : TypeOver Γ}
    (left right : Term (extend Γ type) (type.reindex (projectionHom Γ type))) :
    Equation (TotalTerm (extend Γ type)) :=
  (⟨_, left⟩, ⟨_, right⟩)

variable {L : Type} [UniverseLevel.LevelOrder L] (levels : LevelModel rules L)

theorem recovered_equivalent {Γ : Context rules} {type : TypeOver Γ}
    (left right : Term (extend Γ type) (type.reindex (projectionHom Γ type)))
    (leftIsVariable : (frames levels).E (⟨_, left⟩ : TotalTerm _) (Elimination.last Γ type))
    (body : Term Γ type)
    (rightRecovered : (frames levels).E
      (TotalTerm.reindex (⟨type, body⟩ : TotalTerm Γ) (projectionHom Γ type))
      (⟨_, right⟩ : TotalTerm (extend Γ type)))
    (rest : EquationStore (TotalTerm (extend Γ type))) :
    (frames levels).Equivalent (equation left right :: rest)
      (Elimination.definition Γ body :: rest) := by
  intro Δ solution
  have first := (frames levels).preserves solution leftIsVariable
  have second := (frames levels).preserves solution rightRecovered
  simp only [Frames.Models, List.mem_cons, forall_eq_or_imp]
  apply and_congr_left
  intro _
  constructor
  · intro solved
    exact ((frames levels).equivalence Δ).trans (((frames levels).equivalence Δ).symm first)
      (((frames levels).equivalence Δ).trans solved (((frames levels).equivalence Δ).symm second))
  · intro solved
    exact ((frames levels).equivalence Δ).trans first
      (((frames levels).equivalence Δ).trans solved second)

variable {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
variable (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

/-- Preserve direct recovery, including inputs whose values need not be
normalized. Only an unfinished direct attempt tries the normalized route. -/
def recoverRight (fuel : Nat) {Γ : Context S.R} {type : TypeOver Γ}
    (right : Term (extend Γ type) (type.reindex (projectionHom Γ type))) :
    Option (ContextualDependentProjectionInversion.Recovery S.levels (projectionHom Γ type) type
      (⟨_, right⟩ : TotalTerm (extend Γ type))) :=
  match recover facts roots heads algebra declared choices reducer fuel (withoutNewest Γ type) type right.code with
  | some recovered => some ⟨recovered.body, by
      refine ⟨(type.reindex (projectionHom Γ type)).isType.refl, ?_⟩
      change Equal S.R (extend Γ type).raw (subst projection recovered.body.code) right.code
        (type.reindex (projectionHom Γ type)).code
      rw [subst_projection]
      rw [show rename wk recovered.body.code = right.code from recovered.recovers]
      exact .refl right.typed⟩
  | none => do
      let recovered ← ContextualDependentProjectionInversion.recover facts roots heads algebra declared choices reducer fuel
        (withoutNewest Γ type) (𝟙 (extend Γ type)) (𝟙 (extend Γ type)) type (⟨_, right⟩ : TotalTerm _)
      return ⟨recovered.body, by
        rcases recovered with ⟨body, same⟩
        simpa only [Category.id_comp, withoutNewest_hom] using same⟩

theorem recoverRight_preserves_direct {fuel : Nat} {Γ : Context S.R} {type : TypeOver Γ}
    (right : Term (extend Γ type) (type.reindex (projectionHom Γ type)))
    (recovered : Recovery (withoutNewest Γ type) type right.code)
    (accepted : recover facts roots heads algebra declared choices reducer fuel
      (withoutNewest Γ type) type right.code = some recovered) :
    (recoverRight facts roots heads algebra declared choices reducer fuel right).map (fun answer => answer.body) =
      some recovered.body := by
  simp only [recoverRight, accepted, Option.map_some]

def solveNewest (fuel : Nat) {Γ : Context S.R} {type : TypeOver Γ}
    (left right : Term (extend Γ type) (type.reindex (projectionHom Γ type)))
    (rest : EquationStore (TotalTerm (extend Γ type))) :
    Option (Update S.levels (equation left right :: rest)) := do
  let leftIsVariable ← Conversion.compare facts roots heads algebra reducer fuel
    (⟨_, left⟩ : TotalTerm _) (Elimination.last Γ type)
  let recovered ← recoverRight facts roots heads algebra declared choices reducer fuel right
  let eliminated := (ContextualDependentUpdate.definition S.levels recovered.body rest).rephrase
    (recovered_equivalent S.levels left right leftIsVariable.down recovered.body recovered.solves rest)
  return eliminated.then
    (conversion facts roots heads algebra reducer fuel eliminated.remaining)

/-- An unsuccessful bounded attempt retains the complete original store.
This operation never treats failure to reconstruct as a refutation. -/
def stepNewest (fuel : Nat) {Γ : Context S.R} {type : TypeOver Γ}
    (left right : Term (extend Γ type) (type.reindex (projectionHom Γ type)))
    (rest : EquationStore (TotalTerm (extend Γ type))) :
    Update S.levels (equation left right :: rest) :=
  (solveNewest facts roots heads algebra declared choices reducer fuel left right rest).getD
    (Update.pending S.levels (equation left right :: rest))

end ContextualDependentFlex
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
