import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveRegularity

/-!
# Context conversion through a checked identity substitution

Changing the newest binder to a convertible type transports the entire
formation-sensitive body derivation. The map is the existing identity
substitution, checked against the two actual telescopes. No syntax rewriting
or type erasure is used.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation

variable {Head : Type} {n : Nat}

/-- Changing the argument used to open a dependent body changes its result
by conversion, including when the argument occurs beneath further binders. -/
theorem Conv.inst0Argument {headEq : Head → Head → Prop}
    {root : RootComputation Head} {left right : Tm Head n}
    (conversion : Conv headEq left right root) (body : Tm Head (n + 1)) :
    Conv headEq (inst0 left body) (inst0 right body) root := by
  apply Conv.substitutePointwise (term := body)
  intro index
  refine Fin.cases ?_ ?_ index
  · exact conversion
  · intro prior
    exact .refl _

namespace FormationSensitive

variable {R : Rules Head}

/-- The newest variable at the new binder type is converted back to the
formed old type; older variables keep their original lookup types. -/
theorem CtxMor.convertNewest {Γ : Ctx Head n} {old new : Tm Head n} {u : Head}
    (formed : Typing R Γ old (.head u)) (universeWitness : R.isUniverse u)
    (conversion : Conv R.headEq old new R.computation) :
    CtxMor R (.snoc Γ old) (.snoc Γ new) ids := by
  intro index
  rw [subst_ids]
  refine Fin.cases ?_ ?_ index
  · change Typing R (.snoc Γ new) (.var 0) (rename wk old)
    have oldFormed : Typing R (.snoc Γ new) (rename wk old) (.head u) := by
      simpa only [rename] using formed.weaken (extension := new)
    have reversed : Conv R.headEq new old R.computation := .symm _ _ conversion
    exact .conv (.var 0) oldFormed universeWitness
      (reversed.renameTerms wk)
  · intro prior
    exact .var (Fin.succ prior)

/-- The entire dependent body derivation survives changing a binder to a
convertible type, by the already proved simultaneous substitution theorem. -/
theorem Typing.convertNewest {Γ : Ctx Head n} {old new : Tm Head n} {u : Head}
    {term type : Tm Head (n + 1)}
    (typing : Typing R (.snoc Γ old) term type)
    (formed : Typing R Γ old (.head u)) (universeWitness : R.isUniverse u)
    (conversion : Conv R.headEq old new R.computation) :
    Typing R (.snoc Γ new) term type := by
  simpa only [subst_ids] using
    typing.substitute (CtxMor.convertNewest formed universeWitness conversion)

/-- Restore an original displayed result type using its independently
proved regularity, not an unchecked conversion target. -/
theorem Typing.withResultOf {Γ : Ctx Head n} {original replacement A B : Tm Head n}
    (typed : Typing R Γ replacement B) (source : Typing R Γ original A)
    (universes : UniverseRegularity R) (context : ContextFormation R Γ)
    (conversion : Conv R.headEq B A R.computation) :
    Typing R Γ replacement A := by
  obtain ⟨u, universeWitness, formed⟩ := source.regularity universes context
  exact .conv typed formed universeWitness conversion

#print axioms CtxMor.convertNewest
#print axioms Typing.convertNewest
#print axioms Typing.withResultOf

end FormationSensitive
#print axioms Conv.inst0Argument
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
