import Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintPresentation

/-!
# Constraint models through actual branch unification

The source model is the existing destination equation judgment. The runtime
side uses the actual solved substitution, including first-match lookup.
These laws relate all source models, not just one chosen answer valuation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintPresentation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open EagerDFS

theorem resolve_expression (bindings : Subst) (items : List Atom) :
    Unifying.resolve bindings (.expression items) = .expression (items.map (Unifying.resolve bindings)) := by
  calc
    Unifying.resolve bindings (.expression items) = Destination.read (environment bindings) (.expression items) :=
      (read_environment _ _).symm
    _ = .expression (items.map (Destination.read (environment bindings))) := read_expression _ _
    _ = .expression (items.map (Unifying.resolve bindings)) := by
      apply congrArg Atom.expression
      apply List.map_congr_left
      intro item present
      exact read_environment bindings item

theorem read_single_binding (model : Destination.Environment) (name : String) (value : Atom)
    (sameValue : Destination.read model (.var name) = Destination.read model value) (term : Atom) :
    Destination.read model (Unifying.resolve [(name,value)] term) = Destination.read model term := by
  cases term with
  | symbol => rfl
  | grounded => rfl
  | var other =>
      by_cases same : name = other
      · subst other
        simpa only [Unifying.resolve,applySubst,Subst.lookup,List.find?_cons,beq_self_eq_true,
          ↓reduceIte,Option.map_some,Prod.snd,Option.getD_some] using sameValue.symm
      · simp [Unifying.resolve,applySubst,Subst.lookup,same]
  | expression items =>
      rw [resolve_expression,read_expression,read_expression]
      simp only [Atom.expression.injEq,List.map_map]
      apply List.map_congr_left
      intro item present
      exact read_single_binding model name value sameValue item
termination_by sizeOf term
decreasing_by
  simp_wf
  exact Nat.lt_trans (List.sizeOf_lt_of_mem present) (by omega)

theorem bindVar_keeps_model (model : Destination.Environment) (bindings : Subst) (name : String) (value : Atom)
    (old : Destination.Solves model (presentation bindings)) (free : Subst.lookup bindings name = none)
    (sameValue : Destination.read model (.var name) = Destination.read model value) :
    Destination.Solves model (presentation (Unifying.bindVar bindings name value)) := by
  apply (solves_iff_absorbs _ _).mpr
  intro term
  rw [Unifying.resolve_bindVar free,read_single_binding model name value sameValue]
  exact absorbs_of_solves model bindings old term

theorem refines_keeps_earlier_models (model : Destination.Environment) (earlier later : Subst)
    (refined : Unifying.Refines earlier later)
    (current : Destination.Solves model (presentation later)) :
    Destination.Solves model (presentation earlier) := by
  apply (solves_iff_absorbs _ _).mpr
  intro term
  calc
    Destination.read model (Unifying.resolve earlier term) =
        Destination.read model (Unifying.resolve later (Unifying.resolve earlier term)) :=
      (absorbs_of_solves model later current _).symm
    _ = Destination.read model (Unifying.resolve later term) := congrArg _ (refined term)
    _ = Destination.read model term := absorbs_of_solves model later current term

theorem successful_model_implies_source_equation (fuel : Nat) (bindings bound : Subst) (left right : Atom)
    (valid : Unifying.Idempotent bindings)
    (unified : Unifying.unifyTerms fuel bindings left right = .ok bound)
    (model : Destination.Environment) (current : Destination.Solves model (presentation bound)) :
    Destination.Solves model (presentation bindings) ∧ Destination.read model left = Destination.read model right := by
  obtain ⟨afterValid,refined,equal⟩ := Unifying.unifyTerms_sound fuel bindings bound left right valid unified
  refine ⟨refines_keeps_earlier_models model bindings bound refined current,?_⟩
  calc
    Destination.read model left = Destination.read model (Unifying.resolve bound left) :=
      (absorbs_of_solves model bound current _).symm
    _ = Destination.read model (Unifying.resolve bound right) := congrArg _ equal
    _ = Destination.read model right := absorbs_of_solves model bound current _

theorem unifyLists_keeps_model (unifier : Subst → Atom → Atom → Unifying.Unified)
    (validAfter : ∀ bindings bound left right, Unifying.Idempotent bindings →
      unifier bindings left right = .ok bound → Unifying.Idempotent bound)
    (keeps : ∀ bindings bound left right, Unifying.Idempotent bindings →
      unifier bindings left right = .ok bound → ∀ model,
        Destination.Solves model (presentation bindings) → Destination.read model left = Destination.read model right →
          Destination.Solves model (presentation bound)) :
    ∀ (left right : List Atom) (bindings bound : Subst), Unifying.Idempotent bindings →
      Unifying.unifyLists unifier bindings left right = .ok bound → ∀ model,
        Destination.Solves model (presentation bindings) → left.map (Destination.read model) = right.map (Destination.read model) →
          Destination.Solves model (presentation bound) := by
  intro left
  induction left with
  | nil =>
      intro right bindings bound valid unified model old equal
      cases right with
      | nil => cases unified; exact old
      | cons => cases unified
  | cons first rest ih =>
      intro right bindings bound valid unified model old equal
      cases right with
      | nil => cases unified
      | cons other others =>
          simp only [List.map_cons,List.cons.injEq] at equal
          cases head : unifier bindings first other with
          | clash => simp [Unifying.unifyLists,head] at unified
          | exhausted => simp [Unifying.unifyLists,head] at unified
          | ok middle =>
              rw [Unifying.unifyLists,head,Unifying.Unified.ok_andThen] at unified
              exact ih others middle bound (validAfter bindings middle first other valid head) unified model
                (keeps bindings middle first other valid head model old equal.1) equal.2

theorem unifyTerms_keeps_model (fuel : Nat) :
    ∀ (bindings bound : Subst) (left right : Atom), Unifying.Idempotent bindings →
      Unifying.unifyTerms fuel bindings left right = .ok bound → ∀ model,
        Destination.Solves model (presentation bindings) → Destination.read model left = Destination.read model right →
          Destination.Solves model (presentation bound) := by
  induction fuel with
  | zero => intro bindings bound left right valid unified; cases unified
  | succ fuel ih =>
      intro bindings bound left right valid unified model old equal
      have resolvedEqual : Destination.read model (Unifying.resolve bindings left) =
          Destination.read model (Unifying.resolve bindings right) :=
        (absorbs_of_solves model bindings old left).trans
          (equal.trans (absorbs_of_solves model bindings old right).symm)
      have bindLeft : ∀ name term, Unifying.resolve bindings left = .var name →
          Unifying.resolve bindings right = term →
          Destination.Solves model (presentation (Unifying.bindVar bindings name term)) := by
        intro name term leftView rightView
        have unbound := Unifying.unbound_resolve valid left
        have free : Subst.lookup bindings name = none := by
          apply unbound name
          rw [leftView]
          simp [Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars]
        exact bindVar_keeps_model model bindings name term old free (by simpa only [leftView,rightView] using resolvedEqual)
      have bindRight : ∀ name term, Unifying.resolve bindings right = .var name →
          Unifying.resolve bindings left = term →
          Destination.Solves model (presentation (Unifying.bindVar bindings name term)) := by
        intro name term rightView leftView
        have unbound := Unifying.unbound_resolve valid right
        have free : Subst.lookup bindings name = none := by
          apply unbound name
          rw [rightView]
          simp [Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars]
        exact bindVar_keeps_model model bindings name term old free (by simpa only [leftView,rightView] using resolvedEqual.symm)
      unfold Unifying.unifyTerms at unified
      generalize leftView : Unifying.resolve bindings left = resolvedLeft at unified
      generalize rightView : Unifying.resolve bindings right = resolvedRight at unified
      cases resolvedLeft with
      | var name =>
          cases resolvedRight with
          | var other =>
              simp only at unified
              split at unified
              · cases unified; exact old
              · cases unified; exact bindLeft name (.var other) leftView rightView
          | symbol name' =>
              simp only at unified
              split at unified
              · cases unified
              · cases unified; exact bindLeft name (.symbol name') leftView rightView
          | grounded value =>
              simp only at unified
              split at unified
              · cases unified
              · cases unified; exact bindLeft name (.grounded value) leftView rightView
          | expression items =>
              simp only at unified
              split at unified
              · cases unified
              · cases unified; exact bindLeft name (.expression items) leftView rightView
      | symbol name =>
          cases resolvedRight with
          | var other =>
              simp only at unified
              split at unified
              · cases unified
              · cases unified; exact bindRight other (.symbol name) rightView leftView
          | symbol other =>
              simp only at unified
              split at unified
              · cases unified; exact old
              · cases unified
          | grounded => simp only at unified; cases unified
          | expression => simp only at unified; cases unified
      | grounded value =>
          cases resolvedRight with
          | var other =>
              simp only at unified
              split at unified
              · cases unified
              · cases unified; exact bindRight other (.grounded value) rightView leftView
          | symbol => simp only at unified; cases unified
          | grounded other =>
              simp only at unified
              split at unified
              · cases unified; exact old
              · cases unified
          | expression => simp only at unified; cases unified
      | expression items =>
          cases resolvedRight with
          | var other =>
              simp only at unified
              split at unified
              · cases unified
              · cases unified; exact bindRight other (.expression items) rightView leftView
          | symbol => simp only at unified; cases unified
          | grounded => simp only at unified; cases unified
          | expression others =>
              simp only at unified
              have equalItems : items.map (Destination.read model) = others.map (Destination.read model) := by
                simpa only [leftView,rightView,read_expression,Atom.expression.injEq] using resolvedEqual
              exact unifyLists_keeps_model (Unifying.unifyTerms fuel)
                (fun bindings bound left right valid native => (Unifying.unifyTerms_sound fuel bindings bound left right valid native).1)
                ih items others bindings bound valid unified model old equalItems

theorem successful_models_iff (fuel : Nat) (bindings bound : Subst) (left right : Atom)
    (valid : Unifying.Idempotent bindings)
    (unified : Unifying.unifyTerms fuel bindings left right = .ok bound) (model : Destination.Environment) :
    Destination.Solves model (presentation bound) ↔
      Destination.Solves model (presentation bindings) ∧ Destination.read model left = Destination.read model right :=
  ⟨successful_model_implies_source_equation fuel bindings bound left right valid unified model,
   fun conditions => unifyTerms_keeps_model fuel bindings bound left right valid unified model conditions.1 conditions.2⟩

end Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintPresentation
