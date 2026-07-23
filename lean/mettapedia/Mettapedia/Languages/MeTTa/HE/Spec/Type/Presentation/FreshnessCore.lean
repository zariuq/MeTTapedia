import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation

/-!
# Primitive freshness vocabulary for type presentations

This module contains only the finite-support predicates shared by the exact
type-service carrier and the stronger presentation-preservation theory.  It
deliberately depends only on the base presentation layer, so higher semantic
interfaces can state one separation contract without creating an import
cycle or depending on a concrete fresh-name generator.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Freshness

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation

/-- Every variable occurring in one atom avoids a finite name scope. -/
def AtomAvoids (atom : Atom) (forbidden : List String) : Prop :=
  ∀ name, name ∈ TypeSubst.typeVars atom → name ∉ forbidden

/-- Every variable occurring in a list of atoms avoids a finite name scope. -/
def AtomsAvoid (atoms : List Atom)
    (forbidden : List String) : Prop :=
  ∀ name, name ∈ TypeSubst.typeVarsList atoms → name ∉ forbidden

/-- Two independently freshened atom families have disjoint variable
supports.  This is the common semantic vocabulary for argument-family,
operator/argument-cell, cross-history, and localized-signature separation;
the concrete generators remain confined to realization theorems. -/
def FreshFamiliesSeparated (left right : List Atom) : Prop :=
  AtomsAvoid left (TypeSubst.typeVarsList right)

/-- Fresh-family separation is symmetric even though its definition uses
the existing one-sided `AtomsAvoid` vocabulary. -/
theorem FreshFamiliesSeparated.symm
    {left right : List Atom}
    (separated : FreshFamiliesSeparated left right) :
    FreshFamiliesSeparated right left := by
  intro name rightMember leftMember
  exact separated name leftMember rightMember

/-- Disjoint singleton variable families are a positive boundary example. -/
theorem freshFamiliesSeparated_distinct_variables :
    FreshFamiliesSeparated [.var "left"] [.var "right"] := by
  simp [FreshFamiliesSeparated, AtomsAvoid, TypeSubst.typeVarsList,
    TypeSubst.typeVars]

/-- Reusing one private variable across independently freshened families is
rejected. -/
theorem freshFamiliesSeparated_rejects_shared_variable :
    ¬FreshFamiliesSeparated [.var "shared"] [.var "shared"] := by
  simp [FreshFamiliesSeparated, AtomsAvoid, TypeSubst.typeVarsList,
    TypeSubst.typeVars]

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Freshness
