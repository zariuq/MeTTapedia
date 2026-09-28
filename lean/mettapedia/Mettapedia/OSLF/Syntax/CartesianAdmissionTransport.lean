import Mettapedia.OSLF.Syntax.AdmittedJudgmentRulePresentation

/-!
# Cartesian transport of all-node admission

A translation of indexed rule constructors preserves every recursive
premise address. If each translated constructor conclusion is admitted,
induction on complete trees transports admission at every node.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CartesianAdmissionTransport

open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding.IndexedRulePolynomialMorphisms
open Mettapedia.OSLF.Binding.AdmittedJudgmentRulePresentation

universe uBase uIndex uOtherIndex uShape uPosition uOtherShape uOtherPosition

variable {Base : Type uBase}
variable {I : Base → Type uIndex} {J : Base → Type uOtherIndex}
variable {P : IndexedPolynomial.{uBase, uIndex, uShape, uPosition} Base I}
variable {Q : IndexedPolynomial.{uBase, uOtherIndex, uOtherShape, uOtherPosition} Base J}

private theorem allNodes_cast (Admit : ∀ b, J b → Prop)
    (b : Base) {i j : J b} (same : i = j) (tree : Q.Fix b i) :
    AllNodesAdmitted
      (⟨fun b => J b, Q⟩ :
        Mettapedia.OSLF.Binding.IndexedRulePresentationCategory.Presentation Base)
      Admit b j (same ▸ tree) ↔
    AllNodesAdmitted
      (⟨fun b => J b, Q⟩ :
        Mettapedia.OSLF.Binding.IndexedRulePresentationCategory.Presentation Base)
      Admit b i tree := by
  cases same
  rfl

/-- A cartesian map carries node-wise admission if every translated source
constructor has an admitted conclusion. The condition applies to shapes,
not all source indices: an uninhabited judgment need not be admitted. -/
theorem mapFix_allNodesAdmitted
    {f : ∀ b, I b → J b} (h : Hom P Q f)
    (Admit : ∀ b, J b → Prop)
    (accepted : ∀ b i (_shape : P.Shape b i), Admit b (f b i)) :
    ∀ b i (tree : P.Fix b i),
      AllNodesAdmitted
        (⟨fun b => J b, Q⟩ :
          Mettapedia.OSLF.Binding.IndexedRulePresentationCategory.Presentation Base)
        Admit b (f b i) (h.mapFix b i tree) := by
  refine IndexedPolynomial.Fix.eliminate P
    (fun b i tree => AllNodesAdmitted
      (⟨fun b => J b, Q⟩ :
        Mettapedia.OSLF.Binding.IndexedRulePresentationCategory.Presentation Base)
      Admit b (f b i) (h.mapFix b i tree)) ?_
  intro b i shape children ih
  apply (allNodesAdmitted_roll
    (⟨fun b => J b, Q⟩ :
      Mettapedia.OSLF.Binding.IndexedRulePresentationCategory.Presentation Base)
    Admit b (f b i) (h.onShape b i shape)
    (fun position => (h.onNext b i shape position).symm ▸
      h.mapFix b _ (children ((h.onPosition b i shape) position)))).mpr
  refine ⟨accepted b i shape, ?_⟩
  intro position
  have child := ih ((h.onPosition b i shape) position)
  exact (allNodes_cast Admit b
    (h.onNext b i shape position).symm
    (h.mapFix b _ (children ((h.onPosition b i shape) position)))).mpr child

#print axioms mapFix_allNodesAdmitted

end Mettapedia.OSLF.Binding.CartesianAdmissionTransport

namespace Mettapedia.OSLF.Binding.CartesianAdmissionTransport.Control

open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding.AdmittedJudgmentRulePresentation

/-- A two-node tree whose root is admitted but whose sole child is not. -/
private def rules : IndexedPolynomial Unit (fun _ => Bool) where
  Shape := fun _ _ => Unit
  Position := fun {_} {index} _ => if index then Unit else Empty
  next := fun _ _ => false

private def presentation :
    IndexedRulePresentationCategory.Presentation Unit where
  Judgment := fun _ => Bool
  rules := rules

private def leaf : rules.Fix () false :=
  .roll () (fun position => nomatch position)

private def root : rules.Fix () true :=
  .roll () (fun _ => leaf)

/-- Root admission by itself does not supply all-node admission. -/
theorem admitted_root_insufficient :
    (true : Bool) = true ∧
      ¬ AllNodesAdmitted presentation (fun _ index => index = true)
        () true root := by
  refine ⟨rfl, ?_⟩
  intro admitted
  have children := (allNodesAdmitted_roll presentation
    (fun _ index => index = true) () true ()
    (fun _ => leaf)).mp admitted |>.2
  have child := children ()
  have impossible := (allNodesAdmitted_roll presentation
    (fun _ index => index = true) () false ()
    (fun position => nomatch position)).mp child |>.1
  cases impossible

#print axioms admitted_root_insufficient

end Mettapedia.OSLF.Binding.CartesianAdmissionTransport.Control
