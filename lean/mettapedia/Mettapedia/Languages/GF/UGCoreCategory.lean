import Mettapedia.Languages.GF.UGCoreSelected
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Categorical Packaging of the Selected UG Core

Objects are surjective interfaces `AbstractNode -> carrier` that preserve a
selected invariant signature. Morphisms commute with the abstract-tree
injections. In this category, the selected-core quotient is terminal.
-/

namespace Mettapedia.Languages.GF.UGCoreCategory

open CategoryTheory
open Mettapedia.Languages.GF
open Mettapedia.Languages.GF.Abstract
open Mettapedia.Languages.GF.UGCoreSelected

universe u

/-- A surjective interface that preserves a selected invariant signature. -/
structure SelectedCoreObj (sig : UGSignature) where
  carrier : Type u
  inject : AbstractNode → carrier
  surj : Function.Surjective inject
  preserves : SignaturePreservingInterface sig carrier
  inject_eq_observe : preserves.observe = inject

attribute [simp] SelectedCoreObj.inject_eq_observe

/-- Morphisms commute with the abstract-tree injections. -/
structure SelectedCoreHom {sig : UGSignature} (A B : SelectedCoreObj sig) where
  map : A.carrier → B.carrier
  comm : ∀ t, map (A.inject t) = B.inject t

@[ext] theorem SelectedCoreHom.ext {sig : UGSignature}
    {A B : SelectedCoreObj sig} {f g : SelectedCoreHom A B}
    (h : ∀ t, f.map (A.inject t) = g.map (A.inject t)) :
    f = g := by
  cases f with
  | mk fmap fcomm =>
    cases g with
    | mk gmap gcomm =>
      have hfun : fmap = gmap := by
        funext x
        rcases A.surj x with ⟨t, rfl⟩
        exact h t
      subst hfun
      have hproof : fcomm = gcomm := Subsingleton.elim _ _
      cases hproof
      rfl

instance selectedCoreCategoryStruct {sig : UGSignature} :
    CategoryTheory.CategoryStruct (SelectedCoreObj sig) where
  Hom A B := SelectedCoreHom A B
  id A :=
    { map := id
      comm := by intro t; rfl }
  comp f g :=
    { map := g.map ∘ f.map
      comm := by
        intro t
        rw [Function.comp, f.comm t, g.comm t] }

instance selectedCoreCategory {sig : UGSignature} :
    CategoryTheory.Category (SelectedCoreObj sig) where
  id_comp := by
    intro A B f
    apply SelectedCoreHom.ext
    intro t
    rfl
  comp_id := by
    intro A B f
    apply SelectedCoreHom.ext
    intro t
    rfl
  assoc := by
    intro A B C D f g h
    apply SelectedCoreHom.ext
    intro t
    rfl

/-- The selected-core quotient itself as a categorical object. -/
noncomputable def selectedCoreObject (sig : UGSignature) : SelectedCoreObj sig where
  carrier := Quotient (ugCoreSetoid sig)
  inject := Quotient.mk (ugCoreSetoid sig)
  surj := by
    intro q
    refine Quotient.inductionOn q ?_
    intro t
    exact ⟨t, rfl⟩
  preserves :=
    { observe := Quotient.mk (ugCoreSetoid sig)
      recover := by
        intro ℓ
        refine ⟨sig.observeOnCore ℓ, ?_⟩
        intro t
        rfl }
  inject_eq_observe := rfl

/-- Canonical factorization of any object through the selected-core quotient. -/
noncomputable def SelectedCoreObj.toSelectedCore {sig : UGSignature}
    (A : SelectedCoreObj sig) : A ⟶ selectedCoreObject sig where
  map := fun x => Quotient.mk (ugCoreSetoid sig) (Classical.choose (A.surj x))
  comm := by
    intro t
    apply Quotient.sound
    have hEq : A.inject (Classical.choose (A.surj (A.inject t))) = A.inject t :=
      Classical.choose_spec (A.surj (A.inject t))
    have hObs :
        A.preserves.observe (Classical.choose (A.surj (A.inject t))) =
          A.preserves.observe t := by
      simpa [A.inject_eq_observe] using hEq
    exact A.preserves.obsEq_implies_coreEq hObs

/-- The canonical factorization into the selected core is unique. -/
theorem SelectedCoreObj.toSelectedCore_unique {sig : UGSignature}
    (A : SelectedCoreObj sig) (f : A ⟶ selectedCoreObject sig) :
    f = A.toSelectedCore := by
  apply SelectedCoreHom.ext
  intro t
  rw [f.comm t, A.toSelectedCore.comm t]

noncomputable instance uniqueToSelectedCore {sig : UGSignature}
    (A : SelectedCoreObj sig) : Unique (A ⟶ selectedCoreObject sig) where
  default := A.toSelectedCore
  uniq f := A.toSelectedCore_unique f

/-- The selected-core quotient is terminal in the category of surjective
selected-signature-preserving interfaces. -/
noncomputable def selectedCore_isTerminal (sig : UGSignature) :
    CategoryTheory.Limits.IsTerminal (selectedCoreObject sig) :=
  CategoryTheory.Limits.IsTerminal.ofUnique _

section EnglishCzech

open Mettapedia.Languages.GF.OSLFBridge
open Mettapedia.Languages.GF.WorldModelSemantics
open Mettapedia.Languages.GF.OSLFToNTT
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.QuantifiedFormula2
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModel

variable {State : Type u} [EvidenceType State] [BinaryWorldModel State Mettapedia.OSLF.MeTTaIL.Syntax.Pattern]

/-- The English/Czech selected core admits the same terminal-object packaging. -/
noncomputable def englishCzechSelectedCore_isTerminal
    (W : State)
    (Isem : String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop) (φsem : OSLFFormula)
    (Rnt : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop) (Int : QEvidenceAtomSem)
    (Dom : Domain2) (envScope : VarEnv2)
    (x y : String) (hne : x ≠ y)
    (φscope : QFormula2) (X : Mettapedia.CategoryTheory.PLNInstance.PLNObj)
    (env₁ env₂ : VarEnv2) (φclosed : QFormula2) (hcl : closedQF2 φclosed) :
    CategoryTheory.Limits.IsTerminal
      (selectedCoreObject
        (englishCzechSelectedSignature
          W Isem φsem Rnt Int Dom envScope x y hne φscope X env₁ env₂ φclosed hcl)) :=
  selectedCore_isTerminal _

end EnglishCzech

end Mettapedia.Languages.GF.UGCoreCategory
