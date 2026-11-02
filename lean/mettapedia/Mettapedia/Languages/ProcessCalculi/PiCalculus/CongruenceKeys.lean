import Mettapedia.Languages.ProcessCalculi.PiCalculus.CongruenceToolkit
import Mettapedia.Languages.ProcessCalculi.PiCalculus.BindingAgreement

/-!
# Locally nameless keys of π processes

The locally nameless translation `piToPattern` forgets the spelling of bound names and flattens parallel composition.
Processes with the same translation are structurally congruent (`congruent_of_piToPattern_eq`): their parallel
components correspond one to one (`piComponents_piToPattern`, `congruent_parList_parts`), and at a binder both bodies
renamed to a common fresh name have the same translation, so α-conversion relates them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open PiCalcInstance (piToPattern piComponents piPar piPar_components piToPattern_open_close_substitute)

/-- **The parallel components of a process**, flattened. -/
def parts : Process → List Process
  | .par left right => parts left ++ parts right
  | process => [process]

theorem piComponents_piToPattern : ∀ process : Process,
    piComponents (piToPattern process) = (parts process).map piToPattern
  | .par left right => by
    rw [piToPattern, piPar_components, piComponents_piToPattern left, piComponents_piToPattern right]
    simp [piComponents, parts]
  | .nil => rfl
  | .input _ _ _ => rfl
  | .output _ _ => rfl
  | .nu _ _ => rfl
  | .replicate _ _ _ => rfl

theorem congruent_parList_parts : ∀ process : Process, Congruent process (parList (parts process))
  | .par left right =>
    (Congruent.par (congruent_parList_parts left) (congruent_parList_parts right)).trans (parList_append _ _).symm
  | .nil => (Congruent.nilRight _).symm
  | .input _ _ _ => (Congruent.nilRight _).symm
  | .output _ _ => (Congruent.nilRight _).symm
  | .nu _ _ => (Congruent.nilRight _).symm
  | .replicate _ _ _ => (Congruent.nilRight _).symm

theorem nodeCount_le_of_mem_parts : ∀ {process part : Process}, part ∈ parts process → part.nodeCount ≤ process.nodeCount
  | .par left right, part, member => by
    simp only [parts, List.mem_append] at member
    simp only [Process.nodeCount]
    rcases member with inLeft | inRight
    · have := nodeCount_le_of_mem_parts inLeft; omega
    · have := nodeCount_le_of_mem_parts inRight; omega
  | .nil, _, member | .input _ _ _, _, member | .output _ _, _, member | .nu _ _, _, member
  | .replicate _ _ _, _, member => by
    obtain rfl := List.mem_singleton.mp member
    exact le_rfl

theorem forall₂_of_map_eq {α β : Type} (f : α → β) :
    ∀ {first second : List α}, first.map f = second.map f → List.Forall₂ (fun a b => f a = f b) first second
  | [], [], _ => .nil
  | [], _ :: _, same => by simp at same
  | _ :: _, [], same => by simp at same
  | _ :: _, _ :: _, same => by
    simp only [List.map_cons, List.cons.injEq] at same
    exact .cons same.1 (forall₂_of_map_eq f same.2)

theorem forall₂_imp_of_mem {α β : Type} {relation other : α → β → Prop} :
    ∀ {first : List α} {second : List β}, List.Forall₂ relation first second →
      (∀ a ∈ first, ∀ b, relation a b → other a b) → List.Forall₂ other first second
  | [], [], .nil, _ => .nil
  | _ :: _, _ :: _, .cons head rest, implies =>
    .cons (implies _ List.mem_cons_self _ head)
      (forall₂_imp_of_mem rest fun a member => implies a (List.mem_cons_of_mem _ member))

/-- A common fresh name for two binders. -/
theorem exists_fresh (avoid : Finset Name) : ∃ name, name ∉ avoid := ⟨_, Mettapedia.FreshString.fresh_not_mem avoid⟩

/-- **Processes with the same locally nameless translation are structurally congruent.** -/
theorem congruent_of_piToPattern_eq : ∀ (size : ℕ) (first second : Process), first.nodeCount ≤ size →
    piToPattern first = piToPattern second → Congruent first second
  | 0, first, _, small, _ => by cases first <;> simp [Process.nodeCount] at small
  | size + 1, first, second, small, same => by
    cases first with
    | par left right =>
      cases second
      case par left' right' =>
        have components := congrArg piComponents same
        rw [piComponents_piToPattern, piComponents_piToPattern] at components
        have pointwise := forall₂_of_map_eq piToPattern components
        have congruentParts : List.Forall₂ Congruent (parts (left ||| right)) (parts (left' ||| right')) := by
          refine forall₂_imp_of_mem pointwise fun part member part' partSame => ?_
          refine congruent_of_piToPattern_eq size part part' ?_ partSame
          have bound := nodeCount_le_of_mem_parts member
          simp only [parts, List.mem_append] at member
          simp only [Process.nodeCount] at small
          rcases member with inLeft | inRight
          · have := nodeCount_le_of_mem_parts inLeft; omega
          · have := nodeCount_le_of_mem_parts inRight; omega
        exact (congruent_parList_parts _).trans ((parList_forall₂ congruentParts).trans (congruent_parList_parts _).symm)
      all_goals simp [piToPattern, piPar_components] at same
    | nil => cases second <;> simp [piToPattern, piPar_components] at same; exact Congruent.refl _
    | output x z =>
      cases second <;> simp [piToPattern, piPar_components] at same
      obtain ⟨rfl, rfl⟩ := same
      exact Congruent.refl _
    | input x y body =>
      cases second
      case input x' w body' =>
        simp only [piToPattern, Pattern.apply.injEq, List.cons.injEq, Pattern.fvar.injEq, Pattern.lambda.injEq,
          true_and, and_true] at same
        obtain ⟨rfl, closed⟩ := same
        obtain ⟨fresh, freshNot⟩ := exists_fresh (body.freeNames ∪ body'.freeNames ∪ {y, w})
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at freshNot
        obtain ⟨⟨notBody, notBody'⟩, notY, notW⟩ := freshNot
        have renamed : piToPattern (body.substitute y fresh) = piToPattern (body'.substitute w fresh) := by
          rw [← piToPattern_open_close_substitute, ← piToPattern_open_close_substitute, closed]
        simp only [Process.nodeCount] at small
        have inner := congruent_of_piToPattern_eq size _ _ (by rw [nodeCount_substitute]; omega) renamed
        refine Congruent.trans ⟨.alpha_input x y fresh body notBody notY⟩ ?_
        refine Congruent.trans (inner.map fun inner => .input_cong _ _ _ _ inner) ?_
        exact Congruent.symm ⟨.alpha_input x w fresh body' notBody' notW⟩
      all_goals simp [piToPattern, piPar_components] at same
    | replicate x y body =>
      cases second
      case replicate x' w body' =>
        simp only [piToPattern, Pattern.apply.injEq, List.cons.injEq, Pattern.fvar.injEq, Pattern.lambda.injEq,
          true_and, and_true] at same
        obtain ⟨rfl, closed⟩ := same
        obtain ⟨fresh, freshNot⟩ := exists_fresh (body.freeNames ∪ body'.freeNames ∪ {y, w})
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at freshNot
        obtain ⟨⟨notBody, notBody'⟩, notY, notW⟩ := freshNot
        have renamed : piToPattern (body.substitute y fresh) = piToPattern (body'.substitute w fresh) := by
          rw [← piToPattern_open_close_substitute, ← piToPattern_open_close_substitute, closed]
        simp only [Process.nodeCount] at small
        have inner := congruent_of_piToPattern_eq size _ _ (by rw [nodeCount_substitute]; omega) renamed
        refine Congruent.trans ⟨.alpha_replicate x y fresh body notBody notY⟩ ?_
        refine Congruent.trans (inner.map fun inner => .replicate_cong _ _ _ _ inner) ?_
        exact Congruent.symm ⟨.alpha_replicate x w fresh body' notBody' notW⟩
      all_goals simp [piToPattern, piPar_components] at same
    | nu y body =>
      cases second
      case nu w body' =>
        simp only [piToPattern, Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq, true_and,
          and_true] at same
        obtain ⟨fresh, freshNot⟩ := exists_fresh (body.freeNames ∪ body'.freeNames ∪ {y, w})
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at freshNot
        obtain ⟨⟨notBody, notBody'⟩, notY, notW⟩ := freshNot
        have renamed : piToPattern (body.substitute y fresh) = piToPattern (body'.substitute w fresh) := by
          rw [← piToPattern_open_close_substitute, ← piToPattern_open_close_substitute, same]
        simp only [Process.nodeCount] at small
        have inner := congruent_of_piToPattern_eq size _ _ (by rw [nodeCount_substitute]; omega) renamed
        refine Congruent.trans ⟨.alpha_nu y fresh body notBody⟩ ?_
        refine Congruent.trans (Congruent.nu fresh inner) ?_
        exact Congruent.symm ⟨.alpha_nu w fresh body' notBody'⟩
      all_goals simp [piToPattern, piPar_components] at same

end Mettapedia.Languages.ProcessCalculi.PiCalculus
