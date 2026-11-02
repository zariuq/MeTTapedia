import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutationPair

/-!
# Scope ownership under the actual producer-block exchange

Both real executions allocate the same ledger. The two live local blocks
are exchanged; helper copies stay in their original helper regions. The
whole-name scope equation additionally requires the incoming declarations'
scope sets to be bounded by the incoming ledger.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualScopeSupport ContextualFreshFrameScopeLedger ContextualActivationScopes
open ContextualExecutionCommutationNames

def localLedger (occupied : Finset Nat) := occupied ∪ Finset.Ico (start occupied) (start occupied + 1)
def firstScope (occupied : Finset Nat) := start occupied
def secondScope (occupied : Finset Nat) := start (Producer.nextLedger occupied)
def swapScopes (occupied : Finset Nat) : Equiv.Perm Nat := Equiv.swap (firstScope occupied) (secondScope occupied)

theorem first_mem_local (occupied : Finset Nat) : firstScope occupied ∈ localLedger occupied := by
  apply Finset.mem_union_right
  simp [firstScope]

theorem first_lt_helper (occupied : Finset Nat) :
    firstScope occupied < helperScope (localLedger occupied) :=
  occupied_lt_start _ (first_mem_local occupied)

theorem helper_lt_second (occupied : Finset Nat) :
    helperScope (localLedger occupied) < secondScope occupied :=
  occupied_lt_start _ (helper_scope_retained _)

theorem scope_order (occupied : Finset Nat) : firstScope occupied < secondScope occupied :=
  (first_lt_helper occupied).trans (helper_lt_second occupied)

theorem swap_fixes_initial_scope (occupied : Finset Nat) (name : Nat) (present : name ∈ occupied) :
    swapScopes occupied name = name := by
  have below := occupied_lt_start occupied present
  have order := scope_order occupied
  apply Equiv.swap_apply_of_ne_of_ne <;> dsimp [firstScope, secondScope] at * <;> omega

theorem swap_fixes_first_helper (occupied : Finset Nat) :
    swapScopes occupied (helperScope (localLedger occupied)) = helperScope (localLedger occupied) := by
  apply Equiv.swap_apply_of_ne_of_ne
  · exact (first_lt_helper occupied).ne'
  · exact (helper_lt_second occupied).ne

theorem swap_fixes_second_helper (occupied : Finset Nat) :
    swapScopes occupied (helperScope (localLedger (Producer.nextLedger occupied))) =
      helperScope (localLedger (Producer.nextLedger occupied)) := by
  have later := first_lt_helper (Producer.nextLedger occupied)
  have order := scope_order occupied
  apply Equiv.swap_apply_of_ne_of_ne <;> dsimp [firstScope, secondScope] at * <;> omega

theorem swap_preserves_initial_set (occupied values : Finset Nat) (bounded : values ⊆ occupied) :
    values.image (swapScopes occupied) = values := by
  ext name
  constructor
  · intro present
    obtain ⟨old, member, rfl⟩ := Finset.mem_image.mp present
    rw [swap_fixes_initial_scope occupied old (bounded member)]
    exact member
  · intro present
    exact Finset.mem_image.mpr ⟨name, present, swap_fixes_initial_scope occupied name (bounded present)⟩

theorem swap_preserves_final_ledger (occupied : Finset Nat) :
    (Producer.nextLedger (Producer.nextLedger occupied)).image (swapScopes occupied) =
      Producer.nextLedger (Producer.nextLedger occupied) := by
  have firstPresent : firstScope occupied ∈ Producer.nextLedger (Producer.nextLedger occupied) :=
    (ContextualFreshFrameScopeLedger.old_scopes_retained _) (Finset.mem_union_left _
      ((ContextualFreshFrameScopeLedger.old_scopes_retained _) (first_mem_local occupied)))
  have secondPresent : secondScope occupied ∈ Producer.nextLedger (Producer.nextLedger occupied) :=
    (ContextualFreshFrameScopeLedger.old_scopes_retained _) (first_mem_local (Producer.nextLedger occupied))
  have maps : ∀ name ∈ Producer.nextLedger (Producer.nextLedger occupied),
      swapScopes occupied name ∈ Producer.nextLedger (Producer.nextLedger occupied) := by
    intro name member
    by_cases first : name = firstScope occupied
    · subst name
      simpa [swapScopes] using secondPresent
    by_cases second : name = secondScope occupied
    · subst name
      simpa [swapScopes] using firstPresent
    rw [show swapScopes occupied name = name from Equiv.swap_apply_of_ne_of_ne first second]
    exact member
  ext name
  constructor
  · intro present
    obtain ⟨old, member, rfl⟩ := Finset.mem_image.mp present
    exact maps old member
  · intro present
    refine Finset.mem_image.mpr ⟨swapScopes occupied name, maps name present, ?_⟩
    simp [swapScopes]

def nextScopes {Local V : Type} (scopes : V → Finset Nat) (occupied : Finset Nat) : Names Local V → Finset Nat :=
  frameScopes (activeScopes scopes) (helperScope (localLedger occupied))

def twiceScopes {Local V : Type} (scopes : V → Finset Nat) (occupied : Finset Nat) :
    Twice (Local := Local) (V := V) → Finset Nat :=
  nextScopes (nextScopes scopes occupied) (Producer.nextLedger occupied)

theorem scope_exchange {Local V : Type} (scopes : V → Finset Nat) (occupied : Finset Nat)
    (bounded : ∀ name, scopes name ⊆ occupied) (name : Twice (Local := Local) (V := V)) :
    twiceScopes scopes occupied (exchange (swapScopes occupied) name) =
      (twiceScopes scopes occupied name).image (swapScopes occupied) := by
  cases name with
  | inr helper =>
      cases helper with
      | inl _ =>
          simp only [twiceScopes, nextScopes, frameScopes, exchange, Finset.image_singleton,
            swap_fixes_second_helper]
      | inr impossible => exact nomatch impossible
  | inl active =>
      cases active with
      | inl name =>
          simp [twiceScopes, nextScopes, frameScopes, activeScopes, exchange, earlier, scopeMap, swapScopes]
      | inr previous =>
          cases previous with
          | inr helper =>
              cases helper with
              | inl _ =>
                  change {helperScope (localLedger occupied)} =
                    ({helperScope (localLedger occupied)} : Finset Nat).image (swapScopes occupied)
                  simp only [Finset.image_singleton, swap_fixes_first_helper]
              | inr impossible => exact nomatch impossible
          | inl active =>
              cases active with
              | inl name =>
                  simp [twiceScopes, nextScopes, frameScopes, activeScopes, exchange, later, scopeMap]
              | inr name => exact (swap_preserves_initial_set occupied _ (bounded name)).symm

variable {S : Signature} {Local O : Type} {locals : Local → MetaArity S}
  [DecidableEq O] [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
  {Γ : Ctx S} {sort : S.Srt} {before : ContextualExecution.Endpoint locals O Γ sort}

theorem actual_two_target_scopes (first second : Producer before)
    (empty : before.inventory.configuration.equations = [])
    (separate : Disjoint second.made.toFinset first.made.toFinset) :
    (first.twoTarget second empty separate).scopes = twiceScopes before.scopes before.occupied := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionCommutation
