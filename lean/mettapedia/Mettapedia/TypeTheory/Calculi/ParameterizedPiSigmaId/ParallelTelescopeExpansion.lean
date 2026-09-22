import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRegularity

/-!
# Expanding simultaneous domain declarations into a dependent telescope

Every domain in a group is read in the same preceding context. Placing its
j-th entry into an ordinary telescope crosses j new binders, so the domain
is renamed by that context extension. This is the existing scoped syntax
and renaming action, not a second context carrier or typing judgment.

The construction covers arbitrary group sizes and independently supplied
domains. Formation and preservation are derived from structural weakening;
head interpretation commutes with expansion. The negative control isolates
the unshifted-domain mistake even when all annotations share one type.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ParallelTelescopeExpansion

variable {Head Head' : Type} {n : Nat}

/-- Old variables move past all newly introduced group entries. -/
def inclusion (n count : Nat) : Ren n (n + count) := fun index =>
  ⟨index.val + count, Nat.add_lt_add_right index.isLt count⟩

theorem inclusion_zero : inclusion n 0 = idRen := by
  funext index
  apply Fin.ext
  rfl

theorem inclusion_succ (count : Nat) :
    inclusion n (count + 1) = wk ∘ inclusion n count := by
  funext index
  apply Fin.ext
  rfl

/-- Expand the first count entries in their written order. Sibling
annotations remain terms of the original context, not later contexts. -/
def expand (context : Ctx Head n) :
    {count : Nat} → (Fin count → Tm Head n) → Ctx Head (n + count)
  | 0, _ => context
  | count + 1, domains =>
      .snoc (expand context (fun index => domains index.castSucc))
        (rename (inclusion n count) (domains (Fin.last count)))

/-- The actual expanded context preserves all original scoped derivations. -/
theorem typing_preserved {R : Rules Head} {context : Ctx Head n}
    {term type : Tm Head n} (typed : FormationSensitive.Typing R context term type)
    {count : Nat} (domains : Fin count → Tm Head n) :
    FormationSensitive.Typing R (expand context domains)
      (rename (inclusion n count) term) (rename (inclusion n count) type) := by
  induction count with
  | zero => simpa only [expand, inclusion_zero, rename_id] using typed
  | succ count inductionHypothesis =>
      have earlier := inductionHypothesis (fun index => domains index.castSucc)
      have weakened := earlier.weaken
        (extension := rename (inclusion n count) (domains (Fin.last count)))
      simpa only [expand, inclusion_succ, rename_comp, Function.comp_def] using weakened

/-- Finite groups of formed domains produce an actually formed telescope. -/
theorem formed {R : Rules Head} {context : Ctx Head n}
    (contextFormed : FormationSensitive.ContextFormation R context)
    {count : Nat} (domains : Fin count → Tm Head n)
    (domainsFormed : ∀ index, ∃ level,
      R.isUniverse level ∧
        FormationSensitive.Typing R context (domains index) (.head level)) :
    FormationSensitive.ContextFormation R (expand context domains) := by
  induction count with
  | zero => exact contextFormed
  | succ count inductionHypothesis =>
      have earlier := inductionHypothesis (fun index => domains index.castSucc)
        (fun index => domainsFormed index.castSucc)
      obtain ⟨level, isUniverse, domainTyped⟩ := domainsFormed (Fin.last count)
      apply FormationSensitive.ContextFormation.snoc earlier
        (u := level) _ isUniverse
      simpa only [rename] using
        typing_preserved domainTyped (fun index => domains index.castSucc)

/-- An old variable still denotes the same original context entry. -/
theorem old_lookup (context : Ctx Head n) {count : Nat}
    (domains : Fin count → Tm Head n) (index : Fin n) :
    Ctx.lookup (expand context domains) (inclusion n count index) =
      rename (inclusion n count) (Ctx.lookup context index) := by
  induction count with
  | zero => simp only [expand, inclusion_zero, idRen, rename_id]
  | succ count inductionHypothesis =>
      rw [inclusion_succ]
      simp only [expand, Function.comp_apply, wk, Ctx.lookup, Fin.cases_succ]
      rw [inductionHypothesis]
      exact rename_comp _ _ _

/-- Mapping the installed head interpretation commutes with this expansion. -/
theorem mapHead (map : Head → Head') (context : Ctx Head n) {count : Nat}
    (domains : Fin count → Tm Head n) :
    (expand context domains).mapHead map =
      expand (context.mapHead map) (fun index => (domains index).mapHead map) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp only [expand, Ctx.mapHead, Tm.mapHead_rename, inductionHypothesis]

/-- Sharing the annotation does not mean sharing its unchanged index. -/
theorem shared_domain_still_moves (domain : Tm Head 0) :
    expand (.snoc .nil domain) (fun _ : Fin 2 => (.var 0 : Tm Head 1)) =
      .snoc (.snoc (.snoc .nil domain) (.var 0)) (.var 1) := rfl

theorem unshifted_shared_domain_is_different (domain : Tm Head 0) :
    expand (.snoc .nil domain) (fun _ : Fin 2 => (.var 0 : Tm Head 1)) ≠
      .snoc (.snoc (.snoc .nil domain) (.var 0)) (.var 0) := by
  intro same
  cases same

#print axioms typing_preserved
#print axioms formed
#print axioms old_lookup
#print axioms mapHead
#print axioms unshifted_shared_domain_is_different

end ParallelTelescopeExpansion
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
