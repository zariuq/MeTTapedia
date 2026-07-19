/-
# LF kernel profiles as PTS data

The product rules below are extracted from the running MeTTa kernels rather
than chosen for convenience.

* The registered basic `KWCheck` route reaches
  `MettaKernel/kernel/kernel_signature_lf_v0.metta:106-110`: it admits
  `(type,type,type)` and `(type,kind,kind)` only.
* The indexed kernel implements the additional Type-parameter cases at
  `MettaKernel/kernel/kernel_signature_lf_indexed_v0.metta:99-108`:
  `(kind,type,kind)` and `(kind,kind,kind)`.
* Both kernels implement `Type : Kind` and reject `Kind` as a top sort
  (`kernel_signature_lf_v0.metta:112-113` and
  `kernel_signature_lf_indexed_v0.metta:110-111`).

This module makes that difference an explicit point in a profile lattice.
-/

import Mettapedia.GSLT.LanguageDef.LF

namespace Mettapedia.GSLT.LanguageDef.LFProfile

open Mettapedia.GSLT.LanguageDef.LF

/-- One PTS product triple `(domain sort, codomain sort, result sort)`. -/
structure ProductRule where
  domain : Srt
  codomain : Srt
  result : Srt
  deriving DecidableEq, Repr

/-- The kernel-selectable part of the LF statics. -/
structure Profile where
  sortAxiom : Srt → Option Srt
  products : List ProductRule

def typeAxiom : Srt → Option Srt
  | .type => some .kind
  | .kind => none

def typeTypeType : ProductRule := ⟨.type, .type, .type⟩
def typeKindKind : ProductRule := ⟨.type, .kind, .kind⟩
def kindTypeKind : ProductRule := ⟨.kind, .type, .kind⟩
def kindKindKind : ProductRule := ⟨.kind, .kind, .kind⟩

/-- Exact profile of the kernel behind the registered basic `KWCheck` bridge. -/
def basic : Profile where
  sortAxiom := typeAxiom
  products := [typeTypeType, typeKindKind]

/-- Exact PTS profile implemented by the indexed kernel. -/
def indexed : Profile where
  sortAxiom := typeAxiom
  products := [typeTypeType, typeKindKind, kindTypeKind, kindKindKind]

/-- Pointwise inclusion of axioms and product rules. -/
def Subsumed (first second : Profile) : Prop :=
  (∀ source target, first.sortAxiom source = some target →
    second.sortAxiom source = some target) ∧
  ∀ rule, rule ∈ first.products → rule ∈ second.products

infix:50 " ⊑ " => Subsumed

theorem Subsumed.refl (profile : Profile) : profile ⊑ profile := by
  constructor
  · intro source target haxiom
    exact haxiom
  · intro rule hrule
    exact hrule

theorem Subsumed.trans {first second third : Profile}
    (hfirst : first ⊑ second) (hsecond : second ⊑ third) :
    first ⊑ third := by
  constructor
  · intro source target haxiom
    exact hsecond.1 source target (hfirst.1 source target haxiom)
  · intro rule hrule
    exact hsecond.2 rule (hfirst.2 rule hrule)

/-- T1: every basic product/axiom is present unchanged in the indexed profile. -/
theorem basic_subsumed_indexed : basic ⊑ indexed := by
  constructor
  · intro source target haxiom
    exact haxiom
  · intro rule hrule
    simp [basic] at hrule
    rcases hrule with rfl | rfl <;> simp [indexed]

/-! A small shared formation judgment makes profile monotonicity substantive. -/

/-- Nat-interned PTS formation skeleton; atoms stand for context/signature heads. -/
inductive SortExpr where
  | sort : Srt → SortExpr
  | atom : Nat → Srt → SortExpr
  | pi : SortExpr → SortExpr → SortExpr
  deriving DecidableEq, Repr

/-- Profile-parametric PTS formation. -/
inductive Forms (profile : Profile) : SortExpr → Srt → Prop where
  | sort {source target} :
      profile.sortAxiom source = some target →
      Forms profile (.sort source) target
  | atom (name : Nat) (sort : Srt) :
      Forms profile (.atom name sort) sort
  | pi {domain codomain domainSort codomainSort resultSort} :
      Forms profile domain domainSort →
      Forms profile codomain codomainSort →
      (⟨domainSort, codomainSort, resultSort⟩ : ProductRule) ∈
        profile.products →
      Forms profile (.pi domain codomain) resultSort

/-- Formation derivations transport monotonically along the profile lattice. -/
theorem Forms.mono {first second : Profile} (hprofiles : first ⊑ second)
    {expression : SortExpr} {sort : Srt}
    (hforms : Forms first expression sort) : Forms second expression sort := by
  induction hforms with
  | sort haxiom => exact .sort (hprofiles.1 _ _ haxiom)
  | atom name sort => exact .atom name sort
  | pi hdomain hcodomain hrule ihDomain ihCodomain =>
      exact .pi ihDomain ihCodomain (hprofiles.2 _ hrule)

/-- Corollary in the exact form needed by later profile-parametric judgments. -/
theorem basic_forms_embed {expression : SortExpr} {sort : Srt}
    (hforms : Forms basic expression sort) : Forms indexed expression sort :=
  hforms.mono basic_subsumed_indexed

def objectArrow : SortExpr :=
  .pi (.atom 0 .type) (.atom 1 .type)

/-- A product between ordinary object types belongs to both profiles. -/
theorem objectArrow_basic : Forms basic objectArrow .type := by
  exact .pi (.atom 0 .type) (.atom 1 .type) (by simp [basic, typeTypeType])

def typeParameterProduct : SortExpr :=
  .pi (.sort .type) (.sort .type)

/-- Positive fixture: the indexed profile admits `Π (α : Type). Type`. -/
theorem typeParameterProduct_indexed :
    Forms indexed typeParameterProduct .kind := by
  exact .pi (.sort rfl) (.sort rfl) (by simp [indexed, kindKindKind])

/-- Negative fixture: the registered basic profile cannot form that product. -/
theorem typeParameterProduct_not_basic :
    ¬ Forms basic typeParameterProduct .kind := by
  intro hforms
  cases hforms with
  | pi hdomain hcodomain hrule =>
      cases hdomain with
      | sort hdomainSort =>
          simp [basic, typeAxiom] at hdomainSort
          cases hcodomain with
          | sort hcodomainSort =>
              simp [basic, typeAxiom] at hcodomainSort
              cases hdomainSort
              cases hcodomainSort
              simp [basic, typeTypeType, typeKindKind] at hrule

#print axioms basic_subsumed_indexed
#print axioms Forms.mono
#print axioms typeParameterProduct_indexed
#print axioms typeParameterProduct_not_basic

end Mettapedia.GSLT.LanguageDef.LFProfile
