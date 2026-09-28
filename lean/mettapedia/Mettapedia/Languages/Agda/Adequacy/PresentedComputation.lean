import Mettapedia.Languages.Agda.Adequacy.Controls
import Mettapedia.Languages.Agda.Structural.PresentationSoundness
import Mettapedia.Languages.Agda.Structural.PresentationCompleteness
import Mettapedia.Languages.Agda.Structural.PresentationCorrespondence
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalPaths

/-!
# Source computation as paths in the actual rule presentation

The independently specified finite application and substitution derivations
produce paths whose edges are firing trees of the authored 29-rule table.
This combines the source simulation with the structural presentation maps.
It retains ordered edges, rather than replacing a computation by endpoint
reachability. It does not establish termination or source elaboration.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Adequacy

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Structural (sig scope)

abbrev PresentedPath {Γ : Ctx sig} {s : Structural.Srt}
    (source target : Term sig Γ s) :=
  @Quiver.Path (Term sig Γ s)
    (derivationQuiver Structural.Authored.computationRules Structural.Authored.algebra Γ s)
    source target

local instance {Γ : Ctx sig} {s : Structural.Srt} : Quiver (Term sig Γ s) :=
  derivationQuiver Structural.Authored.computationRules Structural.Authored.algebra Γ s

/-- Translate every ordered structural step into an actual firing tree. -/
def presentPath {Γ : Ctx sig} {s : Structural.Srt}
    {source target : Term sig Γ s} (path : Path source target) : PresentedPath source target :=
  path.toQuiver (fun term => term) Structural.stepToTree

/-- Interpret every presented edge by table soundness, preserving its position. -/
def interpretPath {Γ : Ctx sig} {s : Structural.Srt}
    {source target : Term sig Γ s} (path : PresentedPath source target) : Path source target :=
  match path with
  | .nil => .refl _
  | .cons history last => (interpretPath history).trans (.single (Structural.treeToStep last))

theorem presentPath_length {Γ : Ctx sig} {s : Structural.Srt}
    {source target : Term sig Γ s} (path : Path source target) :
    (presentPath path).length = path.length :=
  path.toQuiver_length (fun term => term) Structural.stepToTree

theorem presentPath_trans {Γ : Ctx sig} {s : Structural.Srt}
    {source middle target : Term sig Γ s}
    (left : Path source middle) (right : Path middle target) :
    presentPath (left.trans right) = (presentPath left).comp (presentPath right) :=
  left.toQuiver_trans (fun term => term) Structural.stepToTree right

theorem interpretPath_length {Γ : Ctx sig} {s : Structural.Srt}
    {source target : Term sig Γ s} (path : PresentedPath source target) :
    (interpretPath path).length = path.length := by
  induction path with
  | nil => rfl
  | cons history last ih =>
      exact (CompatibleDerivations.Path.length_trans (R := @Structural.Root)
        (interpretPath history) (.single (Structural.treeToStep last))).trans
        (congrArg (· + 1) ih)

theorem interpretPath_comp {Γ : Ctx sig} {s : Structural.Srt}
    {source middle target : Term sig Γ s}
    (left : PresentedPath source middle) (right : PresentedPath middle target) :
    interpretPath (left.comp right) = (interpretPath left).trans (interpretPath right) := by
  induction right with
  | nil => exact (CompatibleDerivations.Path.trans_refl (interpretPath left)).symm
  | cons history last ih =>
      change (interpretPath (left.comp history)).trans (.single (Structural.treeToStep last)) = _
      exact (congrArg (fun path => path.trans (.single (Structural.treeToStep last))) ih).trans
        (CompatibleDerivations.Path.trans_assoc _ _ _)

/-- Translating a structural computation out and back preserves every step. -/
theorem interpretPath_presentPath {Γ : Ctx sig} {s : Structural.Srt}
    {source target : Term sig Γ s} (path : Path source target) :
    interpretPath (presentPath path) = path := by
  induction path with
  | refl _ => rfl
  | cons step rest ih =>
      calc
        interpretPath (presentPath (.cons step rest)) =
            (interpretPath (Quiver.Hom.toPath (Structural.stepToTree step))).trans
              (interpretPath (presentPath rest)) := interpretPath_comp _ _
        _ = (CompatibleDerivations.Path.single step).trans rest :=
          congrArg₂ CompatibleDerivations.Path.trans
            (congrArg CompatibleDerivations.Path.single
              (Structural.treeToStep_stepToTree step)) ih
        _ = .cons step rest := rfl

/-- Interpreting and rebuilding a firing history preserves its actual trees. -/
theorem presentPath_interpretPath {Γ : Ctx sig} {s : Structural.Srt}
    {source target : Term sig Γ s} (path : PresentedPath source target) :
    presentPath (interpretPath path) = path := by
  induction path with
  | nil => rfl
  | cons history last ih =>
      calc
        presentPath (interpretPath (history.cons last)) =
            (presentPath (interpretPath history)).comp
              (presentPath (.single (Structural.treeToStep last))) := presentPath_trans _ _
        _ = history.comp (Quiver.Hom.toPath last) :=
          congrArg₂ Quiver.Path.comp ih
            (congrArg Quiver.Hom.toPath (Structural.stepToTree_treeToStep last))
        _ = history.cons last := rfl

/-- The free paths agree as proof objects, beyond endpoint reachability. -/
def presentedPathEquiv {Γ : Ctx sig} {s : Structural.Srt}
    (source target : Term sig Γ s) : Path source target ≃ PresentedPath source target where
  toFun := presentPath
  invFun := interpretPath
  left_inv := interpretPath_presentPath
  right_inv := presentPath_interpretPath

/-- Every finite reference application is realized inside the rule polynomial. -/
def presentedApply {n : Nat} {term result : Specification.Term n}
    {spine : Specification.Spine n} (derivation : Specification.Apply term spine result) :
    PresentedPath (Structural.eliminate (embedTerm term) (embedSpine spine)) (embedTerm result) :=
  presentPath (realizeApply derivation)

/-- Hereditary reference substitution is represented by explicit rule firings. -/
def presentedSubstitute {n m : Nat} {σ : Specification.Substitution n m}
    {term : Specification.Term n} {result : Specification.Term m}
    (derivation : Specification.Substitute σ term result) :
    PresentedPath (bind (embedSub σ) (embedTerm term)) (embedTerm result) :=
  presentPath (realizeSubstitute derivation)

/-- The identity application takes beta and empty-spine elimination steps. -/
theorem presented_identity_length (argument : Specification.Term 0) :
    (presentedApply (Specification.Examples.identity_apply argument)).length = 2 := by
  rw [presentedApply, presentPath_length]
  rfl

/-- Capture avoidance reaches the uncaptured target through authored firings. -/
def presented_capture :
    PresentedPath
      (Structural.eliminate (Structural.lam (Structural.lam (.var (.succ .zero))))
        (Structural.cons (Structural.apply (.var .zero)) Structural.nil))
      (Structural.lam (.var (.succ .zero)) : Structural.Tm [.term]) :=
  presentPath Controls.capturePath

/-- A variable has no nonempty history in the authored presentation. -/
theorem variable_path_length_zero {Γ : Ctx sig} {s : Structural.Srt}
    (index : Var Γ s) {target : Term sig Γ s}
    (path : PresentedPath (.var index) target) : path.length = 0 := by
  let structural := interpretPath path
  have zero : structural.length = 0 := by
    cases structural with
    | refl _ => rfl
    | cons step _ => exact False.elim ((Structural.variable_inert index _).false step)
  exact (interpretPath_length path).symm.trans zero

#print axioms presentedApply
#print axioms presentedSubstitute
#print axioms presentedPathEquiv
#print axioms presented_identity_length
#print axioms variable_path_length_zero

end Mettapedia.Languages.Agda.Adequacy
