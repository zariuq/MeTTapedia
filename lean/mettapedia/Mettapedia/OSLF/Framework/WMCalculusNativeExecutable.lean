import Mettapedia.OSLF.Framework.WMCalculusContextClosure
import Mettapedia.OSLF.NativeTypes.Executable.ExploredCompiled
import Mettapedia.OSLF.MeTTaIL.StructuralDescentPlan

/-!
# WM calculus on the compiled native explorer

Compile the authored WM rules, including recursive congruence, with explicit
typed handles and a relation-provider snapshot. The complete search retains
guard premises and explores cycles instead of treating commutativity as a
normalization procedure. A settled exploration supports future modal
mu-calculus queries; exhausted work yields unknown.

Provider rows are operational inputs. Their truth in a particular world-model
interpretation is a separate obligation of that interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusNativeExecutable

open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.NativeTypes.Executable.Explored.Compiled
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Mettapedia.Logic.ModalMuCalculus

/-- Recursive descent comes from the authored congruence premises. -/
def permissions : Permissions where
  sites := .rootOnly
  equationIndices := some []
  includeDerivedEquations := false

def snapshot (vertex : WMExtVertex) (handles : List (String × TypeExpr))
    (provider : GeneralPremise.ProviderSnapshot) : Snapshot where
  language := wmExtVertexLanguageDefWithCong vertex
  freeTypes := handles
  provider := provider

def compile (vertex : WMExtVertex) (handles : List (String × TypeExpr))
    (provider : GeneralPremise.ProviderSnapshot) : Plan :=
  StructuralDescent.Plan.compile (snapshot vertex handles provider) permissions

theorem compile_equations (vertex : WMExtVertex) (handles : List (String × TypeExpr))
    (provider : GeneralPremise.ProviderSnapshot) :
    (compile vertex handles provider).equations = [] := by
  unfold compile StructuralDescent.Plan.compile
  rw [StructuralDescent.Plan.equations_preserved]
  rfl

inductive Issue where
  | admission (obligations : List Obligation)
  | sourceSort
  deriving DecidableEq, Repr

/-- Boolean observations of raw WM terms, interpreted on the compiled steps.
Admission and source typing failures are distinct from a negative answer. -/
def ask (vertex : WMExtVertex) (handles : List (String × TypeExpr))
    (provider : GeneralPremise.ProviderSnapshot) (sort : TypeExpr)
    (source : Pattern) {n : Nat} (atoms : Fin n → Pattern → Bool)
    (formula : Formula Traversal n) (work budget : Nat) : Except Issue Verdict :=
  let plan := compile vertex handles provider
  if plan.complete then
    if Mettapedia.GSLT.LanguageDef.WellSorted.checkHasType
        plan.snapshot.language plan.snapshot.free [] source sort then
      .ok (verdict plan [] sort id source work formula
        (equationFreeAtoms (bound := []) (expected := sort)
          (compile_equations vertex handles provider) atoms) budget)
    else .error .sourceSort
  else .error (.admission plan.obligations)

private theorem ask_ok {vertex : WMExtVertex} {handles : List (String × TypeExpr)}
    {provider : GeneralPremise.ProviderSnapshot} {sort : TypeExpr}
    {source : Pattern} {n : Nat} {atoms : Fin n → Pattern → Bool}
    {formula : Formula Traversal n} {work budget : Nat} {result : Verdict}
    (answer : ask vertex handles provider sort source atoms formula work budget = .ok result) :
    verdict (compile vertex handles provider) [] sort id source work formula
      (equationFreeAtoms (bound := []) (expected := sort)
        (compile_equations vertex handles provider) atoms) budget = result := by
  unfold ask at answer
  dsimp only at answer
  split at answer
  · split at answer
    · exact Except.ok.inj answer
    · cases answer
  · cases answer

/-- A returned verdict never silently drops unadmitted authored rules. -/
theorem ask_admitted {vertex : WMExtVertex} {handles : List (String × TypeExpr)}
    {provider : GeneralPremise.ProviderSnapshot} {sort : TypeExpr}
    {source : Pattern} {n : Nat} {atoms : Fin n → Pattern → Bool}
    {formula : Formula Traversal n} {work budget : Nat} {result : Verdict}
    (answer : ask vertex handles provider sort source atoms formula work budget = .ok result) :
    (compile vertex handles provider).complete = true := by
  unfold ask at answer
  dsimp only at answer
  split at answer
  · assumption
  · cases answer

/-- Positive answers denote the future property of the compiled WM relation. -/
theorem ask_proved (vertex : WMExtVertex) (handles : List (String × TypeExpr))
    (provider : GeneralPremise.ProviderSnapshot) (sort : TypeExpr)
    (source : Pattern) {n : Nat} (atoms : Fin n → Pattern → Bool)
    (formula : Formula Traversal n) (work budget : Nat)
    (answer : ask vertex handles provider sort source atoms formula work budget = .ok .proved) :
    satisfies (transitionSystem (GSLTTypeSynthesis.gsltSpan
      (theory (compile vertex handles provider) [] sort)))
      (equationFreeAtoms (bound := []) (expected := sort) (compile_equations vertex handles provider) atoms).meaning formula source := by
  exact verdict_proved (plan := compile vertex handles provider) (bound := []) (expected := sort)
    (by rw [Complete.Predecessors.equationsChecked, compile_equations]; rfl)
    (Abstraction.plain _ _ _) trivial (ask_ok answer)

theorem ask_refuted (vertex : WMExtVertex) (handles : List (String × TypeExpr))
    (provider : GeneralPremise.ProviderSnapshot) (sort : TypeExpr)
    (source : Pattern) {n : Nat} (atoms : Fin n → Pattern → Bool)
    (formula : Formula Traversal n) (work budget : Nat)
    (answer : ask vertex handles provider sort source atoms formula work budget = .ok .refuted) :
    ¬ satisfies (transitionSystem (GSLTTypeSynthesis.gsltSpan
      (theory (compile vertex handles provider) [] sort)))
      (equationFreeAtoms (bound := []) (expected := sort) (compile_equations vertex handles provider) atoms).meaning formula source := by
  exact verdict_refuted (plan := compile vertex handles provider) (bound := []) (expected := sort)
    (by rw [Complete.Predecessors.equationsChecked, compile_equations]; rfl)
    (Abstraction.plain _ _ _) trivial (ask_ok answer)

end Mettapedia.OSLF.Framework.WMCalculusNativeExecutable
