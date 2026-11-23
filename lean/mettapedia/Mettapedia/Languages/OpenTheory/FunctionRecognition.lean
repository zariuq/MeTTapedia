import Mettapedia.Languages.OpenTheory.Syntax

/-!
# Exact function-carrier recognition

The existing recognizer checks the operator's complete provenance and its
two arguments. Successful recognition therefore determines the actual type,
rather than merely a printed operator name.
-/

namespace Mettapedia.Languages.OpenTheory.Ty

theorem destFunction?_eq_some_iff (type domain codomain : Ty) :
    type.destFunction? = some (domain, codomain) ↔ type = .function domain codomain := by
  constructor
  · intro recognized
    cases type with
    | var name => simp [destFunction?] at recognized
    | op operator arguments =>
        cases arguments with
        | nil => simp [destFunction?] at recognized
        | cons first rest =>
            cases rest with
            | nil => simp [destFunction?] at recognized
            | cons second remaining =>
                cases remaining with
                | cons third tail => simp [destFunction?] at recognized
                | nil =>
                    simp only [destFunction?] at recognized
                    split at recognized
                    · rename_i same
                      have operatorSame := (TypeOp.same_eq_true_iff _ _).mp same
                      have components := Option.some.inj recognized
                      cases components
                      simp [function, operatorSame]
                    · contradiction
  · intro same
    rw [same]
    exact destFunction?_function domain codomain

theorem eq_function_of_destFunction? {ty domain codomain : Ty}
    (h : ty.destFunction? = some (domain, codomain)) :
    ty = .function domain codomain := by
  cases ty with
  | var name => simp [destFunction?] at h
  | op operator arguments =>
      match arguments, h with
      | [first, second], h =>
          simp only [destFunction?] at h
          split at h
          · rename_i same
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have := (TypeOp.same_eq_true_iff _ _).mp same
            subst this
            rfl
          · contradiction

theorem function_inj {domain codomain domain' codomain' : Ty}
    (h : Ty.function domain codomain = Ty.function domain' codomain') :
    domain = domain' ∧ codomain = codomain' := by
  simp only [Ty.function, Ty.op.injEq, List.cons.injEq] at h
  exact ⟨h.2.1, h.2.2.1⟩

end Mettapedia.Languages.OpenTheory.Ty
