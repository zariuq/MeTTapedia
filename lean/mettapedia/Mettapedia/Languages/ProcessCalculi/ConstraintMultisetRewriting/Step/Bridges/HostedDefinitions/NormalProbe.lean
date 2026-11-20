import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.GroundCall

/-!
# Pattern-only source probes for the normal-form profile

A probe retains an equation's actual pattern and fresh site, wraps its call
under a distinct literal head, and returns a fixed held marker on a match.
No reduction helper runs in the probe. Matching the wrapped terms has exactly
the original solvability condition, including the actual branch constraints.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalProbe

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration

def probeTag : String := "hd-normal-probe"
def markerTag : String := "hd-redex-found"

def wrap {X : Type} {declaration : X → MetaArity MSig}
    (datum : Term (signature MSig declaration) [] ()) : Term (signature MSig declaration) [] () :=
  Toolkit.tupleAt [Toolkit.symAt probeTag, datum]

def marker {X : Type} (declaration : X → MetaArity MSig) : Term (signature MSig declaration) [] () :=
  Toolkit.symAt markerTag

theorem wrap_eq_iff {X : Type} {declaration : X → MetaArity MSig}
    (first second : Term (signature MSig declaration) [] ()) :
    wrap first = wrap second ↔ first = second :=
  ⟨fun same => (Toolkit.tuple2_inj same).2, congrArg wrap⟩

theorem instantiate_wrap {X Y : Type} {source : X → MetaArity MSig} {target : Y → MetaArity MSig}
    (assignment : Assignment source target) (datum : Term (signature MSig source) [] ()) :
    instantiate assignment (wrap datum) = wrap (instantiate assignment datum) := by
  unfold wrap
  rw [RuleBuilder.instantiate_tuple]
  rfl

theorem solvable_iff {κ : Keys MSig} (K : List (Constraint κ [] ())) (left right : Data κ [] ()) :
    Solvable (K ++ [(wrap left, wrap right)]) ↔ Solvable (K ++ [(left, right)]) := by
  constructor
  · rintro ⟨X, target, assignment, solved⟩
    obtain ⟨old, wrapped⟩ := (models_append _ _ _).mp solved
    have same := (models_singleton _ _).mp wrapped
    dsimp only at same
    rw [instantiate_wrap, instantiate_wrap] at same
    exact ⟨X, target, assignment, (models_append _ _ _).mpr
      ⟨old, (models_singleton _ _).mpr ((wrap_eq_iff _ _).mp same)⟩⟩
  · rintro ⟨X, target, assignment, solved⟩
    obtain ⟨old, matched⟩ := (models_append _ _ _).mp solved
    have same := (models_singleton _ _).mp matched
    refine ⟨X, target, assignment, (models_append _ _ _).mpr ⟨old, ?_⟩⟩
    apply (models_singleton _ _).mpr
    dsimp only
    rw [instantiate_wrap, instantiate_wrap, same]

def equation {κ : Keys MSig} {Ty : Type} (original : SourceLanguage.Equation κ [] () Ty) :
    SourceLanguage.Equation κ [] () Ty :=
  ⟨original.site, wrap original.lhs, .ret (marker (fam κ))⟩

theorem copied_match_iff {κ : Keys MSig} {Ty : Type}
    (original : SourceLanguage.Equation κ [] () Ty) (scope : Nat)
    (K : List (Constraint κ [] ())) (call : Data κ [] ()) :
    Solvable (K ++ [(instantiate (copyAt κ scope) (equation original).lhs, wrap call)]) ↔
      Solvable (K ++ [(instantiate (copyAt κ scope) original.lhs, call)]) := by
  change Solvable (K ++ [(instantiate (copyAt κ scope) (wrap original.lhs), wrap call)]) ↔ _
  rw [instantiate_wrap]
  exact solvable_iff K _ call

theorem marker_ne_wrapped {X : Type} (declaration : X → MetaArity MSig)
    (datum : Term (signature MSig declaration) [] ()) : marker declaration ≠ wrap datum := by
  intro same
  cases same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalProbe

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalProbe.copied_match_iff
