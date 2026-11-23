import Mettapedia.Languages.OpenTheory.FunctionRecognition

/-!
# Canonical term typing

Successful checking determines exact application and abstraction types and
bounds every de Bruijn index by the context and binder depth.
-/

namespace Mettapedia.Languages.OpenTheory.DBTerm

theorem inferType_app_eq_some_iff {context : List Ty} {function argument : DBTerm}
    {ty : Ty} :
    (DBTerm.app function argument).inferType context = some ty ↔
      ∃ domain, function.inferType context = some (.function domain ty) ∧
        argument.inferType context = some domain := by
  constructor
  · intro h
    simp only [DBTerm.inferType.eq_4, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨functionTy, hfunction, argumentTy, hargument, ⟨domain, codomain⟩,
      hdest, hresult⟩ := h
    split at hresult
    · rename_i hsame
      cases hresult
      have hdomain := (Ty.same_eq_true_iff _ _).mp hsame
      subst hdomain
      rw [Ty.eq_function_of_destFunction? hdest] at hfunction
      exact ⟨domain, hfunction, hargument⟩
    · contradiction
  · rintro ⟨domain, hfunction, hargument⟩
    simp only [DBTerm.inferType.eq_4, Option.bind_eq_bind, Option.bind_eq_some_iff]
    refine ⟨_, hfunction, _, hargument, (domain, ty), Ty.destFunction?_function _ _, ?_⟩
    simp [(Ty.same_eq_true_iff domain domain).mpr rfl]

theorem inferType_abs_eq_some_iff {context : List Ty} {domain : Ty} {body : DBTerm}
    {ty : Ty} :
    (DBTerm.abs domain body).inferType context = some ty ↔
      ∃ codomain, body.inferType (domain :: context) = some codomain ∧
        ty = .function domain codomain := by
  simp only [DBTerm.inferType.eq_5]
  cases body.inferType (domain :: context) with
  | none => simp
  | some codomain =>
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some,
        Option.some.injEq]
      constructor
      · intro h
        exact ⟨codomain, rfl, h.symm⟩
      · rintro ⟨codomain', hcodomain, rfl⟩
        cases hcodomain
        rfl

/-- Every loose bound index is below the given binder depth. -/
def LooseBelow : Nat → DBTerm → Prop
  | depth, .bound index => index < depth
  | depth, .app function argument =>
      LooseBelow depth function ∧ LooseBelow depth argument
  | depth, .abs _ body => LooseBelow (depth + 1) body
  | _, .const _ _ => True
  | _, .free _ => True

theorem looseBelow_of_inferType :
    ∀ {context : List Ty} {term : DBTerm} {ty : Ty},
      term.inferType context = some ty → term.LooseBelow context.length
  | _, .const _ _, _, _ => trivial
  | _, .free _, _, _ => trivial
  | context, .bound index, ty, h => by
      simp only [DBTerm.inferType.eq_3] at h
      exact (List.getElem?_eq_some_iff.mp h).1
  | _, .app function argument, _, h => by
      obtain ⟨domain, hfunction, hargument⟩ := inferType_app_eq_some_iff.mp h
      exact ⟨looseBelow_of_inferType hfunction, looseBelow_of_inferType hargument⟩
  | _, .abs domain body, _, h => by
      obtain ⟨codomain, hbody, _⟩ := inferType_abs_eq_some_iff.mp h
      exact looseBelow_of_inferType (term := body) hbody

end Mettapedia.Languages.OpenTheory.DBTerm
