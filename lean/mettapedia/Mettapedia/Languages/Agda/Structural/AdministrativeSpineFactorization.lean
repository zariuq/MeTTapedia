import Mettapedia.Languages.Agda.Structural.AdministrativeStatics

/-!
# Factoring spine actions through conversions

These views are folds over actual action trees. They split append at its
retained intermediate type, compose an empty prefix with an arbitrary suffix,
and move a suffix beneath a leading argument. Input and output conversions
are retained and moved to the corresponding side of the composition. No
formation of an arbitrary proposed input type is inferred.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory
open Statics (RawTm RawTy RawContext)

structure AppendFactors {n : Nat} (Γ : RawContext n) (A : RawTy n)
    (es fs : Spine (scope n)) (B : RawTy n) where
  middle : RawTy n
  first : Action Γ A es middle
  second : Action Γ middle fs B

structure ActionFactors {n : Nat} (Γ : RawContext n) (A : RawTy n)
    (spine : Spine (scope n)) (B : RawTy n) where
  append : ∀ es fs, spine = Structural.append es fs → AppendFactors Γ A es fs B
  nil : spine = Structural.nil → ∀ {fs : Spine (scope n)} {C : RawTy n},
    Action Γ B fs C → Action Γ A fs C
  cons : ∀ u es, spine = Structural.cons (apply u) es →
    ∀ {fs : Spine (scope n)} {C : RawTy n}, Action Γ B fs C →
      Action Γ A (Structural.cons (apply u) (Structural.append es fs)) C

def Factorization : Judgment → Type
  | .spineAction Γ A es B => ActionFactors Γ A es B
  | _ => PUnit

theorem cons_apply_injective {n : Nat} {u v : RawTm n} {es fs : Spine (scope n)}
    (same : Structural.cons (apply u) es = Structural.cons (apply v) fs) : u = v ∧ es = fs := by
  cases same
  exact ⟨rfl, rfl⟩

def factorizationRule {j : Judgment} (shape : RuleShape j)
    (children : Evidence Derivation (premises shape))
    (ih : Evidence Factorization (premises shape)) : Factorization j := by
  cases shape with
  | prior shape =>
      have children := priorPremiseEvidence children
      have ih := priorPremiseEvidence ih
      cases shape with
      | core | elimination => exact ⟨⟩
      | nil Γ A =>
        exact ⟨(fun _ _ same => by cases same), (by intro _ _ _ tail; exact tail),
          fun _ _ same => by cases same⟩
      | cons Γ A B u es C =>
        simp only [SpineStatics.premises] at children ih
        refine ⟨(fun _ _ same => by cases same), (fun same => by cases same), ?_⟩
        intro v first same tail D suffix
        obtain ⟨rfl, rfl⟩ := cons_apply_injective same
        exact Derivation.cons (children 0) (Derivation.append (children 1) suffix)
      | append Γ A es B fs C =>
        simp only [SpineStatics.premises] at children ih
        refine ⟨?_, (fun same => by cases same), (fun _ _ same => by cases same)⟩
        intro first second same
        cases same
        exact ⟨B, children 0, children 1⟩
      | inputConversion Γ A' A es B =>
        simp only [SpineStatics.premises] at children ih
        refine ⟨?_, ?_, ?_⟩
        · intro first second same
          let factors := (ih 1).append first second same
          exact ⟨factors.middle, Derivation.inputConversion (children 0) factors.first, factors.second⟩
        · intro same fs C suffix
          exact Derivation.inputConversion (children 0) ((ih 1).nil same suffix)
        · intro u first same fs C suffix
          exact Derivation.inputConversion (children 0) ((ih 1).cons u first same suffix)
      | outputConversion Γ A es B B' =>
        simp only [SpineStatics.premises] at children ih
        refine ⟨?_, ?_, ?_⟩
        · intro first second same
          let factors := (ih 0).append first second same
          exact ⟨factors.middle, factors.first, Derivation.outputConversion factors.second (children 1)⟩
        · intro same fs C suffix
          exact (ih 0).nil same (Derivation.inputConversion (children 1) suffix)
        · intro u first same fs C suffix
          exact (ih 0).cons u first same (Derivation.inputConversion (children 1) suffix)
  | spineRefl | spineSymm | spineTrans | spineCons | spineAppend | spineInputConversion
    | spineOutputConversion | appendEmpty | appendCons | eliminationCongruence
    | emptyElimination | nestedElimination => exact ⟨⟩

noncomputable def Derivation.factorization {j : Judgment} (tree : Derivation j) : Factorization j :=
  IndexedPolynomial.Fix.eliminate presentation.polynomial
    (fun _ j _ => Factorization j)
    (fun _ _ shape children ih => factorizationRule shape children ih) () j tree

noncomputable def Action.splitAppend {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    {es fs : Spine (scope n)} (tree : Action Γ A (Structural.append es fs) B) :
    AppendFactors Γ A es fs B := tree.factorization.append es fs rfl

noncomputable def Action.dropEmptyAppend {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    {es : Spine (scope n)} (tree : Action Γ A (Structural.append Structural.nil es) B) : Action Γ A es B :=
  let factors := tree.splitAppend
  factors.first.factorization.nil rfl factors.second

noncomputable def Action.distributeAppend {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    {u : RawTm n} {es fs : Spine (scope n)}
    (tree : Action Γ A (Structural.append (Structural.cons (apply u) es) fs) B) :
    Action Γ A (Structural.cons (apply u) (Structural.append es fs)) B :=
  let factors := tree.splitAppend
  factors.first.factorization.cons u es rfl factors.second

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics
