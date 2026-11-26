import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.PartialSubstitution
import Mathlib.Data.Finset.Sort


/-!
# Packing the free support of scoped syntax

The raw renaming observer depends exactly on the free coordinates of the
term. Reindexing a checked partial substitution preserves its readout,
including absence. These laws give an executable, minimal presentation
of a raw term by its packed syntax and the increasing map of used slots.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

private theorem lifted_agreement_iff {n m : Nat} (ρ σ : Ren n m) (used : Set (Fin (n + 1))) :
    (∀ i ∈ used, liftRen ρ i = liftRen σ i) ↔
      ∀ i, Fin.succ i ∈ used → ρ i = σ i := by
  constructor
  · intro h i hi
    have equal : Fin.succ (ρ i) = Fin.succ (σ i) := h (Fin.succ i) hi
    exact Fin.succ_inj.mp equal
  · intro h i
    refine Fin.cases ?_ (fun j hj => ?_) i
    · intro _
      rfl
    · exact congrArg Fin.succ (h j hj)

/-- A syntactic readout under a renaming observes exactly its free variables. -/
theorem rename_eq_iff_agree_freeVariables {Head : Type} {n m : Nat}
    (term : Tm Head n) (ρ σ : Ren n m) :
    rename ρ term = rename σ term ↔ ∀ i ∈ term.freeVariables, ρ i = σ i := by
  induction term generalizing m with
  | var i => simp [rename, Tm.freeVariables, Set.mem_singleton_iff]
  | const c | head c => simp [rename, Tm.freeVariables]
  | pi A B ha hb | sigma A B ha hb =>
      simp [rename, Tm.freeVariables, ha, hb, lifted_agreement_iff, or_imp, forall_and]
  | id A x y ha hx hy =>
      simp [rename, Tm.freeVariables, ha, hx, hy, or_imp, forall_and, and_assoc]
  | lam body ih => simp [rename, Tm.freeVariables, ih, lifted_agreement_iff]
  | app f a hf ha | pair f a hf ha =>
      simp [rename, Tm.freeVariables, hf, ha, or_imp, forall_and]
  | fst p ih | snd p ih | refl p ih => simp [rename, Tm.freeVariables, ih]

/-- The free-variable set is the least set of slots that determines renaming
readout. Two target slots suffice to detect a missing free variable. -/
theorem rename_observes_support_iff {Head : Type} {n : Nat}
    (term : Tm Head n) (support : Set (Fin n)) :
    (∀ ρ σ : Ren n 2, (∀ i ∈ support, ρ i = σ i) → rename ρ term = rename σ term) ↔
      term.freeVariables ⊆ support := by
  constructor
  · intro h i used
    by_contra absent
    let ρ : Ren n 2 := fun _ => 0
    let σ : Ren n 2 := fun j => if j = i then 1 else 0
    have agree : ∀ j ∈ support, ρ j = σ j := by
      intro j member
      have not_i : j ≠ i := fun same => absent (same ▸ member)
      simp [ρ, σ, not_i]
    have observed := (rename_eq_iff_agree_freeVariables term ρ σ).mp (h ρ σ agree) i used
    change (0 : Fin 2) = (if i = i then 1 else 0) at observed
    rw [if_pos rfl] at observed
    exact (by decide : (0 : Fin 2) ≠ 1) observed
  · intro h ρ σ agree
    exact (rename_eq_iff_agree_freeVariables term ρ σ).mpr fun i used => agree i (h used)

variable {Head : Type} {n m k : Nat}

private theorem liftPartialSub_map_rename (environment : PartialSub Head n m) (ρ : Ren m k) :
    liftPartialSub (fun i => (environment i).map (rename ρ)) =
      fun i => (liftPartialSub environment i).map (rename (liftRen ρ)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [liftPartialSub, Fin.cases_succ, Option.map_map]
    congr 1
    funext term
    simp only [Function.comp_apply, rename_comp]
    rfl

/-- Changing the output scope commutes with checked substitution, including
the failure case of a missing entry. -/
theorem substPartial_map_rename (term : Tm Head n) (environment : PartialSub Head n m)
    (ρ : Ren m k) : (substPartial environment term).map (rename ρ) =
      substPartial (fun i => (environment i).map (rename ρ)) term := by
  induction term generalizing m k with
  | var i => rfl
  | const c => rfl
  | head h => rfl
  | pi a b ha hb | sigma a b ha hb =>
      simp only [substPartial, liftPartialSub_map_rename, ← ha, ← hb, Option.bind_eq_bind,
        Option.map_bind, Option.bind_map, Function.comp_def, Option.pure_def, Option.map_some, rename]
  | id a x y ha hx hy =>
      simp only [substPartial, ← ha, ← hx, ← hy, Option.bind_eq_bind, Option.map_bind, Option.bind_map,
        Function.comp_def, Option.pure_def, Option.map_some, rename]
  | lam body ih =>
      simp only [substPartial, liftPartialSub_map_rename, ← ih, Option.map_map,
        Function.comp_def, rename]
  | app f a hf ha | pair f a hf ha =>
      simp only [substPartial, ← hf, ← ha, Option.bind_eq_bind, Option.map_bind, Option.bind_map,
        Function.comp_def, Option.pure_def, Option.map_some, rename]
  | fst t ih | snd t ih | refl t ih =>
      simp only [substPartial, ← ih, Option.map_map, Function.comp_def, rename]

/-- The original coordinates in increasing order. -/
def Tm.supportSlots (term : Tm Head n) : Fin term.support.card ↪o Fin n :=
  term.support.orderEmbOfFin rfl

private def supportEnvironment (term : Tm Head n) : PartialSub Head n term.support.card :=
  fun i => if used : i ∈ term.support then
    some (.var ((term.support.orderIsoOfFin rfl).symm ⟨i, used⟩)) else none

private theorem supportEnvironment_defined (term : Tm Head n) :
    (substPartial (supportEnvironment term) term).isSome = true := by
  apply (substPartial_defined _ _).mpr
  intro i used
  simp [supportEnvironment, used]

/-- Rescope a term to just its free coordinates. The checked partial
substitution also covers closed terms, whose packed scope is empty. -/
def Tm.packSupport (term : Tm Head n) : Tm Head term.support.card :=
  (substPartial (supportEnvironment term) term).get (supportEnvironment_defined term)

@[simp] theorem Tm.rename_packSupport (term : Tm Head n) :
    rename term.supportSlots term.packSupport = term := by
  have decoded := substPartial_eq term
    (partialEnv := fun i => (supportEnvironment term i).map (rename term.supportSlots))
    (environment := ids) (by
      intro i used
      simp only [supportEnvironment, dif_pos used, Option.map_some, rename, ids,
        supportSlots, ← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply])
  rw [← substPartial_map_rename, subst_ids] at decoded
  obtain ⟨body, found⟩ := Option.isSome_iff_exists.mp (supportEnvironment_defined term)
  rw [found, Option.map_some, Option.some.injEq] at decoded
  unfold packSupport
  rw [Option.get_of_eq_some _ found, decoded]

/-- No smaller ambient scope can generate this raw term by renaming. This
includes images of maps that duplicate or reorder coordinates. -/
theorem Tm.support_card_le_of_rename (term : Tm Head n) (e : Ren m n)
    (body : Tm Head m) (image : rename e body = term) : term.support.card ≤ m := by
  have within : term.freeVariables ⊆ Set.range e := by
    apply (rename_observes_support_iff term _).mp
    intro ρ σ agree
    rw [← image, rename_comp, rename_comp]
    congr 1
    funext index
    exact agree (e index) ⟨index, rfl⟩
  have subset : term.support ⊆ Finset.univ.image e := by
    intro i used
    obtain ⟨j, rfl⟩ := within ((Tm.mem_support term i).mp used)
    exact Finset.mem_image_of_mem e (Finset.mem_univ j)
  exact (Finset.card_le_card subset).trans (Finset.card_image_le.trans_eq (by simp))

section Controls

private def boundAndFree : Tm Unit 2 :=
  .lam (.pair (.var 0) (.var (Fin.succ 1)))

example (ρ σ : Ren 2 2) (agree : ρ 1 = σ 1) :
    rename ρ boundAndFree = rename σ boundAndFree := by
  apply (rename_eq_iff_agree_freeVariables boundAndFree ρ σ).mpr
  intro i used
  have lifted : i.succ = (1 : Fin 2).succ := by
    simpa only [boundAndFree, Tm.freeVariables, Set.mem_ofPred_eq, Set.mem_union,
      Set.mem_singleton_iff, Fin.succ_ne_zero, false_or] using used
  exact (Fin.succ_inj.mp lifted) ▸ agree

example : rename idRen boundAndFree ≠ rename (fun _ => 0) boundAndFree := by
  intro equal
  have agreed := (rename_eq_iff_agree_freeVariables boundAndFree idRen _).mp equal
  have used : (1 : Fin 2) ∈ boundAndFree.freeVariables := by
    simp [boundAndFree, Tm.freeVariables]
  exact (by decide : (1 : Fin 2) ≠ 0) (agreed 1 used)

example : boundAndFree.packSupport = .lam (.pair (.var 0) (.var 1)) := by
  let packed : Tm Unit 1 := boundAndFree.packSupport
  have decoded := congrArg (rename (fun _ : Fin 2 => (0 : Fin 1))) boundAndFree.rename_packSupport
  rw [rename_comp] at decoded
  change rename (fun _ : Fin 1 => (0 : Fin 1)) packed =
    (.lam (.pair (.var 0) (.var 1)) : Tm Unit 1) at decoded
  have identity : (fun _ : Fin 1 => (0 : Fin 1)) = idRen := Subsingleton.elim _ _
  rw [identity, rename_id] at decoded
  exact decoded

example :
    ((.lam (.var 0) : Tm Unit 4).packSupport : Tm Unit 0) = .lam (.var 0) := by decide

example (body : Tm Unit 0) (e : Ren 0 2) : rename e body ≠ boundAndFree := by
  intro same
  have minimum := boundAndFree.support_card_le_of_rename e body same
  have width : boundAndFree.support.card = 1 := by decide
  exact (by decide : ¬ (1 ≤ 0)) (width ▸ minimum)

end Controls

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
