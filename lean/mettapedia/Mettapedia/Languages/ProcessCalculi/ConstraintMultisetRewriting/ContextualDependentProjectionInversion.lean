import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentTypedInversion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaConversion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSigma

/-!
# Checked inversion through dependent projections

A typed expansion exposes projected variables before ordinary variable
inversion. The actual reducer and checker construct a proposed body in the
selected context. A final typed conversion check compares its reindexing
with the original target, including its annotation. Thus an unsuccessful
bounded attempt is not a refutation, and successful recovery remains valid
at every later frame. This is recovery, not a principality theorem for an
arbitrary unification problem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentProjectionInversion

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentTypedInversion

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
variable (levels : LevelModel rules L)

structure Recovery {source target : Context rules} (arguments : target ⟶ source)
    (type : TypeOver source) (original : TotalTerm target) where
  body : Term source type
  solves : (frames levels).E (TotalTerm.reindex ⟨type, body⟩ arguments) original

namespace Recovery

theorem at_future {source target future : Context rules} {arguments : target ⟶ source}
    {type : TypeOver source} {original : TotalTerm target}
    (recovered : Recovery levels arguments type original) (later : future ⟶ target) :
    (frames levels).E (TotalTerm.reindex ⟨type, recovered.body⟩ (later ≫ arguments))
      (original.reindex later) := by
  let value : TotalTerm source := ⟨type, recovered.body⟩
  have same := (frames levels).preserves later recovered.solves
  change (frames levels).E ((value.reindex arguments).reindex later)
    (original.reindex later) at same
  change (frames levels).E (value.reindex (later ≫ arguments)) (original.reindex later)
  rw [reindex_comp]
  exact same

end Recovery

variable {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
variable (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

/-- Expansion and restoration are actual typed substitutions. The final
check certifies recovery even if a caller supplies an unsuitable expansion;
no inverse law or successful comparison is an input to this algorithm. -/
def recover (fuel : Nat) {source expanded target : Context S.R}
    (selection : Inclusion source expanded) (expand : expanded ⟶ target)
    (restore : target ⟶ expanded) (type : TypeOver source) (original : TotalTerm target) :
    Option (Recovery S.levels (restore ≫ selection.hom) type original) := do
  let normal ← reducer fuel (original.reindex expand).2.code
  let proposed ← ContextualDependentTypedInversion.recover facts roots heads algebra declared choices reducer fuel
    selection type normal.val
  let checked ← Conversion.compare facts roots heads algebra reducer fuel
    (TotalTerm.reindex ⟨type, proposed.body⟩ (restore ≫ selection.hom)) original
  return ⟨proposed.body, checked.down⟩

/-- The dependent Sigma maps supply the intended expansion/restoration
pair. Their inverse laws are proved by the shared splitting owner. -/
def recoverSigma (fuel : Nat) {Γ source : Context S.R} (shape : ContextualDependentSigma.Shape Γ)
    (selection : Inclusion source shape.split) (type : TypeOver source)
    (original : TotalTerm shape.packed) :
    Option (Recovery S.levels (shape.unpack ≫ selection.hom) type original) :=
  recover facts roots heads algebra declared choices reducer fuel
    selection shape.pack shape.unpack type original

end ContextualDependentProjectionInversion
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
