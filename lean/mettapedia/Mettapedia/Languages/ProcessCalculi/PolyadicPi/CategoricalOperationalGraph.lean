import Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredClassified
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalModelPresheaf
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafEventPowers
import Mettapedia.CategoryTheory.InternalCategoryPathMaps

/-!
# Retained COMM evidence over the actual pi equation clone

The event object contains the independently authored local firing trees,
including active parallel and private-scope descent. Its endpoints lie in
the same represented program object as the complete native function bodies.
The free path category retains individual firings; its endpoint image and
the raw runtime comparison are separate readouts.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.CategoricalOperational

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open IntrinsicScopedConditionalPresheaf
open IntrinsicScopedOperationalPresheafEvents
open IntrinsicScopedLocalPolynomial (Tree)
open AuthoredPositionedRulePolynomial (Judgment)

abbrev algebra := AuthoredClassified.algebra
abbrev Base := IntrinsicScopedConditionalPresheaf.Base algebra
abbrev Ambient := Base ⥤ Type

/-- The existing genuine tree substitution model, with every rule position. -/
abbrev model := IntrinsicScopedAuthoredClassifiedInstance.treeModel
  AuthoredOperationalProfile.rules algebra

/-- Complete retained evidence of the process sort. -/
abbrev edges : Ambient := sortEvents model.toAction .pr

abbrev processes : Ambient := programs algebra .pr

def source : edges ⟶ processes :=
  IntrinsicScopedOperationalPresheafEventPowers.source model.toAction .pr

def target : edges ⟶ processes :=
  IntrinsicScopedOperationalPresheafEventPowers.target model.toAction .pr

/-- Every event contains both complete endpoint classes and its supplied tree. -/
def atEquiv (world : Base) : edges.obj world ≃
    Σ pair : algebra.substitution.Carrier world.unop.context .pr ×
      algebra.substitution.Carrier world.unop.context .pr,
      Tree AuthoredOperationalProfile.rules algebra
        ⟨world.unop.context, .pr, pair⟩ where
  toFun event := event.2 ▸ event.1.2
  invFun supplied := ⟨⟨.pr, supplied.1, supplied.2⟩, rfl⟩
  left_inv event := by
    rcases event with ⟨⟨sort, pair, evidence⟩, same⟩
    cases same
    rfl
  right_inv supplied := rfl

theorem source_readout (world : Base) (event : edges.obj world) :
    programsAtEquiv algebra .pr world (source.app world event) =
      (atEquiv world event).1.1 := by
  rcases event with ⟨⟨sort, pair, evidence⟩, same⟩
  cases same
  rfl

theorem target_readout (world : Base) (event : edges.obj world) :
    programsAtEquiv algebra .pr world (target.app world event) =
      (atEquiv world event).1.2 := by
  rcases event with ⟨⟨sort, pair, evidence⟩, same⟩
  cases same
  rfl

/-- The complete event graph is on the actual equation-clone base. -/
def graph : Mettapedia.CategoryTheory.InternalGraph Ambient :=
  ⟨processes, edges, source, target⟩

/-- Its arrows are retained finite paths of actual authored firings. -/
def internalCategory : Mettapedia.CategoryTheory.InternalCategory Ambient :=
  Mettapedia.CategoryTheory.InternalCategoryPathDiagram.category graph

/-- Reading a retained event at its supplied world gives an actual runtime
step modulo the independently checked structural equations. -/
theorem runtime (world : Base) (event : edges.obj world) :
    StepModulo (Quotient.out ((atEquiv world event).1.1))
      (Quotient.out ((atEquiv world event).1.2)) :=
  AuthoredClassified.quotientTree_sound _ (atEquiv world event).2

/-- Whole endpoint readouts commute with every clone substitution. -/
theorem source_substitution {world future : Base} (change : world ⟶ future)
    (event : edges.obj world) :
    source.app future (edges.map change event) =
      processes.map change (source.app world event) :=
  source.naturality_apply change event

theorem target_substitution {world future : Base} (change : world ⟶ future)
    (event : edges.obj world) :
    target.app future (edges.map change event) =
      processes.map change (target.app world event) :=
  target.naturality_apply change event

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.CategoricalOperational
