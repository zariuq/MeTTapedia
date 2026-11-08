import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDynamicFragment

/-!
# Stability of Miller occurrences under pattern instantiation

A **pattern instantiation** `σ` solves one flexible variable `F` by `λ z̄. u`, where the body `u` is
normal, has Miller occurrences (its outer variables flexible, its binders rigid), and reaches its
outer variables through an injective renaming into flexible variables; every other variable is
renamed injectively, respecting the marking.

**Stability**: on a normal term with Miller occurrences in which `F` is always applied to exactly
`|z̄|` arguments, `σ` followed by normalization gives a normal term with Miller occurrences. The
normal form is reached explicitly: every occurrence `F ȳ` collapses to the renaming `u[ȳ/z̄]`, and
every other spine is renamed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentDynamicFragment

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ExecutableReduction ContextualDependentExecutableJoin
open ContextualDependentGeneralPattern (liftFlexible)

variable {Head : Type}

/-! ## Binders and markings -/

theorem rename_lamsVar {n m : Nat} (ρ : Ren n m) :
    ∀ (count : Nat) (body : Tm Head (n + count)),
      rename ρ (lamsVar count body) = lamsVar count (rename (liftRenK count ρ) body)
  | 0, _ => rfl
  | count + 1, body => rename_lamsVar ρ count (.lam body)

theorem liftRenK_comp {n m k : Nat} (ρ : Ren m k) (τ : Ren n m) :
    ∀ (count : Nat) (index : Fin (n + count)),
      liftRenK count ρ (liftRenK count τ index) = liftRenK count (fun j => ρ (τ j)) index
  | 0, _ => rfl
  | count + 1, index => by
      refine Fin.cases ?_ (fun prior => ?_) index
      · rfl
      · change Fin.succ (liftRenK count ρ (liftRenK count τ prior)) = Fin.succ (liftRenK count (fun j => ρ (τ j)) prior)
        rw [liftRenK_comp ρ τ count prior]

/-- The marking of a solution body: outer variables flexible, `count` binders rigid. -/
def bodyFlexible {o : Nat} : (count : Nat) → Fin (o + count) → Bool
  | 0 => fun _ => true
  | count + 1 => liftFlexible (bodyFlexible count)

theorem combined_respects {n m : Nat} {outer : Ren m n} {flexible' : Fin n → Bool}
    (outerFlexible : ∀ j, flexible' (outer j) = true) :
    ∀ (arguments : List (Fin n)), (∀ argument ∈ arguments, flexible' argument = false) →
      ∀ index, flexible' (combined outer arguments index) = bodyFlexible arguments.length index
  | [], _, index => outerFlexible index
  | argument :: rest, rigid, index => by
      refine Fin.cases ?_ (fun prior => ?_) index
      · exact rigid argument List.mem_cons_self
      · exact combined_respects outerFlexible rest (fun other member => rigid other (List.mem_cons_of_mem _ member)) prior

/-! ## Pattern instantiations -/

/-- **A pattern instantiation** of `target` by `λ z̄. body`, renaming every other variable. -/
structure Instantiation (R : Rules Head) {n m : Nat} (flexible : Fin n → Bool) (flexible' : Fin m → Bool)
    (σ : Sub Head n m) : Type where
  target : Fin n
  arity : Nat
  flexibleTarget : flexible target = true
  rename : (i : Fin n) → i ≠ target → Fin m
  injective : ∀ i j (hi : i ≠ target) (hj : j ≠ target), rename i hi = rename j hj → i = j
  respects : ∀ i (hi : i ≠ target), flexible' (rename i hi) = flexible i
  others : ∀ i (hi : i ≠ target), σ i = .var (rename i hi)
  outerArity : Nat
  outer : Ren outerArity m
  outerInjective : Function.Injective outer
  outerFlexible : ∀ j, flexible' (outer j) = true
  body : Tm Head (outerArity + arity)
  solution : σ target = lamsVar arity (Presentation.rename (liftRenK arity outer) body)
  bodyMiller : miller (bodyFlexible arity) body = true
  bodyNormal : Normal R body

variable {R : Rules Head}

/-- A pattern instantiation under one more binder. -/
def Instantiation.lift {n m : Nat} {flexible : Fin n → Bool} {flexible' : Fin m → Bool} {σ : Sub Head n m}
    (inst : Instantiation R flexible flexible' σ) :
    Instantiation R (liftFlexible flexible) (liftFlexible flexible') (liftSub σ) where
  target := inst.target.succ
  arity := inst.arity
  flexibleTarget := inst.flexibleTarget
  rename i := Fin.cases (motive := fun i => i ≠ inst.target.succ → Fin (m + 1)) (fun _ => 0)
    (fun j hj => (inst.rename j (fun h => hj (congrArg Fin.succ h))).succ) i
  injective := by
    intro i j hi hj same
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩ <;> rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · rfl
    · exact absurd same (Fin.succ_ne_zero _).symm
    · exact absurd same (Fin.succ_ne_zero _)
    · exact congrArg Fin.succ (inst.injective i j _ _ (Fin.succ_injective _ same))
  respects := by
    intro i hi
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · rfl
    · exact inst.respects i _
  others := by
    intro i hi
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · rfl
    · change Presentation.rename wk (σ i) = _
      rw [inst.others i (fun h => hi (congrArg Fin.succ h))]
      rfl
  outerArity := inst.outerArity
  outer := fun j => (inst.outer j).succ
  outerInjective := fun _ _ same => inst.outerInjective (Fin.succ_injective _ same)
  outerFlexible := fun j => inst.outerFlexible j
  body := inst.body
  solution := by
    change Presentation.rename wk (σ inst.target) = _
    rw [inst.solution, rename_lamsVar, rename_comp]
    congr 1
    exact rename_ext (fun index => liftRenK_comp wk inst.outer inst.arity index) inst.body
  bodyMiller := inst.bodyMiller
  bodyNormal := inst.bodyNormal

/-- Substituting a variable spine whose arguments go to the given variables. -/
theorem subst_appsVar_pmap {n m : Nat} (σ : Sub Head n m) (head : Tm Head n) {P : Fin n → Prop}
    (g : (i : Fin n) → P i → Fin m) (sends : ∀ i (hi : P i), σ i = .var (g i hi)) :
    ∀ (arguments : List (Fin n)) (holds : ∀ a ∈ arguments, P a),
      subst σ (appsVar head arguments) = appsVar (subst σ head) (arguments.pmap g holds)
  | [], _ => rfl
  | argument :: rest, holds => by
      simp only [appsVar, subst, List.pmap]
      rw [subst_appsVar_pmap σ head g sends rest, sends]

/-! ## Arities of a pattern instantiation -/

/-- Arities under `count` rigid binders. -/
def liftArityK {o : Nat} : (count : Nat) → (Fin o → Nat) → Fin (o + count) → Nat
  | 0, arity => arity
  | count + 1, arity => liftArity (liftArityK count arity)

theorem combined_arities {n m : Nat} {outer : Ren m n} {arity' : Fin n → Nat} :
    ∀ (arguments : List (Fin n)) (index : Fin (m + arguments.length)), bodyFlexible arguments.length index = true →
      arity' (combined outer arguments index) = liftArityK arguments.length (fun j => arity' (outer j)) index
  | [], _, _ => rfl
  | argument :: rest, index, flexibleIndex => by
      rcases Fin.eq_zero_or_eq_succ index with rfl | ⟨prior, rfl⟩
      · cases flexibleIndex
      · exact combined_arities rest prior flexibleIndex

/-- **Arities of a pattern instantiation**: the instantiated variable's arity is its number of
binders, renamed flexible variables keep their arities, and the solution body has the arities of
the flexible variables it reaches. -/
structure Arities {n m : Nat} {flexible : Fin n → Bool} {flexible' : Fin m → Bool} {σ : Sub Head n m}
    (inst : Instantiation R flexible flexible' σ) (arity : Fin n → Nat) (arity' : Fin m → Nat) : Prop where
  target : arity inst.target = inst.arity
  rename : ∀ i (hi : i ≠ inst.target), flexible i = true → arity' (inst.rename i hi) = arity i
  body : arities (bodyFlexible inst.arity) (liftArityK inst.arity fun j => arity' (inst.outer j)) inst.body = true

theorem Arities.lift {n m : Nat} {flexible : Fin n → Bool} {flexible' : Fin m → Bool} {σ : Sub Head n m}
    {inst : Instantiation R flexible flexible' σ} {arity : Fin n → Nat} {arity' : Fin m → Nat}
    (known : Arities inst arity arity') : Arities inst.lift (liftArity arity) (liftArity arity') where
  target := known.target
  rename := by
    intro i hi flexibleI
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · cases flexibleI
    · exact known.rename i (fun h => hi (congrArg Fin.succ h)) flexibleI
  body := known.body

/-! ## Stability -/

/-- What stability gives for one term: a normal reduct with Miller occurrences and the arities, a
rigid spine head kept rigid, and no new introduction except where a flexible spine collapsed. -/
abbrev Stable {n m : Nat} (flexible : Fin n → Bool) (flexible' : Fin m → Bool) (arity' : Fin m → Nat)
    (σ : Sub Head n m) (t : Tm Head n) : Prop :=
  ∃ t', Star (R := R) (subst σ t) t' ∧ Normal R t' ∧ miller flexible' t' = true ∧ arities flexible' arity' t' = true ∧
    (flexHead flexible (spineHead t) = false → flexHead flexible' (spineHead t') = false) ∧
    (isLam t' = true → isLam t = true ∨ flexHead flexible (spineHead t) = true) ∧
    (isPair t' = true → isPair t = true ∨ flexHead flexible (spineHead t) = true)

variable (empty : R.computation = RootComputation.empty)
include empty

/-- A flexible spine, instantiated. -/
theorem stable_spine {n m : Nat} {flexible : Fin n → Bool} {flexible' : Fin m → Bool} {σ : Sub Head n m}
    (inst : Instantiation R flexible flexible' σ) {arity : Fin n → Nat} {arity' : Fin m → Nat}
    (known : Arities inst arity arity') {head : Fin n} {arguments : List (Fin n)}
    (flexibleHead : flexible head = true) (rigid : ∀ argument ∈ arguments, flexible argument = false)
    (distinct : arguments.Nodup) (lengthOf : arguments.length = arity head) :
    Stable (R := R) flexible flexible' arity' σ (appsVar (.var head) arguments) := by
  have avoid : ∀ argument ∈ arguments, argument ≠ inst.target := fun argument member same => by
    have := rigid argument member
    rw [same, inst.flexibleTarget] at this
    cases this
  let images := arguments.pmap inst.rename avoid
  have renamedRigid : ∀ argument ∈ images, flexible' argument = false := by
    intro renamed member
    obtain ⟨argument, inArguments, rfl⟩ := List.mem_pmap.mp member
    rw [inst.respects argument]
    exact rigid argument inArguments
  have renamedDistinct : images.Nodup :=
    distinct.pmap fun i hi j hj same => inst.injective i j hi hj same
  have imagesLength : images.length = arguments.length := List.length_pmap
  have substituted : subst σ (appsVar (.var head) arguments) = appsVar (σ head) images :=
    subst_appsVar_pmap σ (.var head) inst.rename inst.others arguments avoid
  have spineFlexible : flexHead flexible (spineHead (appsVar (Head := Head) (.var head) arguments)) = true := by
    rw [spineHead_appsVar]
    exact flexibleHead
  by_cases isTarget : head = inst.target
  · subst isTarget
    have bodyArities := known.body
    have arityTarget := known.target
    have solution := inst.solution
    have outerInjective := inst.outerInjective
    have outerFlexible := inst.outerFlexible
    have bodyMiller := inst.bodyMiller
    have bodyNormal := inst.bodyNormal
    generalize inst.body = body at bodyArities solution bodyMiller bodyNormal
    generalize inst.outer = outer at bodyArities solution outerInjective outerFlexible
    generalize inst.outerArity = outerArity at body outer
    have lengths : images.length = inst.arity := by rw [imagesLength, lengthOf, arityTarget]
    generalize inst.arity = count at lengths body bodyArities solution bodyMiller bodyNormal
    subst lengths
    refine ⟨Presentation.rename (combined outer images) body, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [substituted, solution]
      exact collapse_rename outer images body
    · exact (ContextualDependentNormalizing.normal_rename_iff empty _ body).mpr bodyNormal
    · exact miller_rename body (combined_injective outerInjective _ renamedDistinct
        (fun argument member index same => by
          have := renamedRigid argument member
          rw [← same, outerFlexible] at this
          cases this))
        (combined_respects outerFlexible _ renamedRigid) bodyMiller
    · exact arities_rename body (combined_respects outerFlexible _ renamedRigid)
        (fun index flexibleIndex => combined_arities _ index flexibleIndex) bodyArities
    · intro rigidSpine
      rw [spineFlexible] at rigidSpine
      cases rigidSpine
    · intro _
      exact .inr spineFlexible
    · intro _
      exact .inr spineFlexible
  · have renamedHead : σ head = .var (inst.rename head isTarget) := inst.others head isTarget
    have renamedFlexible : flexible' (inst.rename head isTarget) = true := by
      rw [inst.respects head isTarget]; exact flexibleHead
    refine ⟨appsVar (.var (inst.rename head isTarget)) images, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [substituted, renamedHead]
    · exact normal_appsVar empty _ _
    · exact miller_appsVar renamedFlexible _ renamedRigid renamedDistinct
    · exact arities_appsVar renamedFlexible _
        (by rw [imagesLength, lengthOf, known.rename head isTarget flexibleHead])
    · intro rigidSpine
      rw [spineFlexible] at rigidSpine
      cases rigidSpine
    · intro _
      exact .inr spineFlexible
    · intro _
      exact .inr spineFlexible

/-- **Stability of the fragment's occurrence conditions under a pattern instantiation followed by
normalization**: Miller occurrences and arities are kept, and the normal form is reached. -/
theorem stable : ∀ {n : Nat} (t : Tm Head n) {m : Nat} {flexible : Fin n → Bool} {flexible' : Fin m → Bool}
    {σ : Sub Head n m} (inst : Instantiation R flexible flexible' σ) {arity : Fin n → Nat} {arity' : Fin m → Nat},
    Arities inst arity arity' →
    miller flexible t = true → arities flexible arity t = true → Normal R t →
      Stable (R := R) flexible flexible' arity' σ t
  | _, .var i, _, flexible, flexible', σ, inst, arity, arity', known, _, holdsArity, _ => by
      simp only [arities, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at holdsArity
      by_cases isTarget : i = inst.target
      · subst isTarget
        have zero : arity inst.target = 0 := by
          rcases holdsArity with rigid | zero
          · rw [inst.flexibleTarget] at rigid; cases rigid
          · exact zero
        exact stable_spine empty inst known (arguments := []) inst.flexibleTarget
          (fun _ member => absurd member List.not_mem_nil) List.nodup_nil zero.symm
      · refine ⟨.var (inst.rename i isTarget), ?_, normal_var empty _, rfl, ?_, ?_, ?_, ?_⟩
        · change Star (R := R) (σ i) _
          rw [inst.others i isTarget]
        · simp only [arities, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq]
          rw [inst.respects i isTarget]
          rcases holdsArity with rigid | zero
          · exact .inl rigid
          · cases flexibleVariable : flexible i
            · exact .inl rfl
            · exact .inr (by rw [known.rename i isTarget flexibleVariable]; exact zero)
        · intro rigidHead
          change flexible' (inst.rename i isTarget) = false
          rw [inst.respects i isTarget]
          exact rigidHead
        · intro impossible; cases impossible
        · intro impossible; cases impossible
  | _, .const c, _, _, _, _, _, _, _, _, _, _, _ =>
      ⟨.const c, .refl, normal_const empty c, rfl, rfl, fun _ => rfl, fun impossible => (by cases impossible),
        fun impossible => (by cases impossible)⟩
  | _, .head h, _, _, _, _, _, _, _, _, _, _, _ =>
      ⟨.head h, .refl, normal_head empty h, rfl, rfl, fun _ => rfl, fun impossible => (by cases impossible),
        fun impossible => (by cases impossible)⟩
  | _, .pi A B, _, _, _, _, inst, _, _, known, holds, holdsArity, normal => by
      simp only [miller, Bool.and_eq_true] at holds
      simp only [arities, Bool.and_eq_true] at holdsArity
      obtain ⟨normalA, normalB⟩ := (normal_pi_iff empty).mp normal
      obtain ⟨A', sA, nA, mA, aA, -⟩ := stable A inst known holds.1 holdsArity.1 normalA
      obtain ⟨B', sB, nB, mB, aB, -⟩ := stable B inst.lift known.lift holds.2 holdsArity.2 normalB
      refine ⟨.pi A' B', star_pi sA sB, (normal_pi_iff empty).mpr ⟨nA, nB⟩, ?_, ?_, fun _ => rfl,
        fun impossible => (by cases impossible), fun impossible => (by cases impossible)⟩
      · simp only [miller, Bool.and_eq_true]
        exact ⟨mA, mB⟩
      · simp only [arities, Bool.and_eq_true]
        exact ⟨aA, aB⟩
  | _, .sigma A B, _, _, _, _, inst, _, _, known, holds, holdsArity, normal => by
      simp only [miller, Bool.and_eq_true] at holds
      simp only [arities, Bool.and_eq_true] at holdsArity
      obtain ⟨normalA, normalB⟩ := (normal_sigma_iff empty).mp normal
      obtain ⟨A', sA, nA, mA, aA, -⟩ := stable A inst known holds.1 holdsArity.1 normalA
      obtain ⟨B', sB, nB, mB, aB, -⟩ := stable B inst.lift known.lift holds.2 holdsArity.2 normalB
      refine ⟨.sigma A' B', star_sigma sA sB, (normal_sigma_iff empty).mpr ⟨nA, nB⟩, ?_, ?_, fun _ => rfl,
        fun impossible => (by cases impossible), fun impossible => (by cases impossible)⟩
      · simp only [miller, Bool.and_eq_true]
        exact ⟨mA, mB⟩
      · simp only [arities, Bool.and_eq_true]
        exact ⟨aA, aB⟩
  | _, .id A a b, _, _, _, _, inst, _, _, known, holds, holdsArity, normal => by
      simp only [miller, Bool.and_eq_true] at holds
      simp only [arities, Bool.and_eq_true] at holdsArity
      obtain ⟨normalA, normala, normalb⟩ := (normal_id_iff empty).mp normal
      obtain ⟨A', sA, nA, mA, aA, -⟩ := stable A inst known holds.1.1 holdsArity.1.1 normalA
      obtain ⟨a', sa, na, ma, aa, -⟩ := stable a inst known holds.1.2 holdsArity.1.2 normala
      obtain ⟨b', sb, nb, mb, ab, -⟩ := stable b inst known holds.2 holdsArity.2 normalb
      refine ⟨.id A' a' b', star_id sA sa sb, (normal_id_iff empty).mpr ⟨nA, na, nb⟩, ?_, ?_, fun _ => rfl,
        fun impossible => (by cases impossible), fun impossible => (by cases impossible)⟩
      · simp only [miller, Bool.and_eq_true]
        exact ⟨⟨mA, ma⟩, mb⟩
      · simp only [arities, Bool.and_eq_true]
        exact ⟨⟨aA, aa⟩, ab⟩
  | _, .lam body, _, _, _, _, inst, _, _, known, holds, holdsArity, normal => by
      simp only [miller] at holds
      simp only [arities] at holdsArity
      obtain ⟨body', s, nb, mb, ab, -⟩ := stable body inst.lift known.lift holds holdsArity ((normal_lam_iff empty).mp normal)
      exact ⟨.lam body', star_lam s, (normal_lam_iff empty).mpr nb, mb, ab, fun _ => rfl,
        fun _ => .inl rfl, fun impossible => (by cases impossible)⟩
  | _, .pair a b, _, _, _, _, inst, _, _, known, holds, holdsArity, normal => by
      simp only [miller, Bool.and_eq_true] at holds
      simp only [arities, Bool.and_eq_true] at holdsArity
      obtain ⟨normala, normalb⟩ := (normal_pair_iff empty).mp normal
      obtain ⟨a', sa, na, ma, aa, -⟩ := stable a inst known holds.1 holdsArity.1 normala
      obtain ⟨b', sb, nb, mb, ab, -⟩ := stable b inst known holds.2 holdsArity.2 normalb
      refine ⟨.pair a' b', star_pair sa sb, (normal_pair_iff empty).mpr ⟨na, nb⟩, ?_, ?_, fun _ => rfl,
        fun impossible => (by cases impossible), fun _ => .inl rfl⟩
      · simp only [miller, Bool.and_eq_true]
        exact ⟨ma, mb⟩
      · simp only [arities, Bool.and_eq_true]
        exact ⟨aa, ab⟩
  | _, .refl a, _, _, _, _, inst, _, _, known, holds, holdsArity, normal => by
      simp only [miller] at holds
      simp only [arities] at holdsArity
      obtain ⟨a', sa, na, ma, aa, -⟩ := stable a inst known holds holdsArity ((normal_refl_iff empty).mp normal)
      exact ⟨.refl a', star_refl sa, (normal_refl_iff empty).mpr na, ma, aa, fun _ => rfl,
        fun impossible => (by cases impossible), fun impossible => (by cases impossible)⟩
  | _, .fst p, _, flexible, flexible', _, inst, _, _, known, holds, holdsArity, normal => by
      simp only [miller, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at holds
      simp only [arities] at holdsArity
      obtain ⟨notPair, normalp⟩ := (normal_fst_iff empty).mp normal
      obtain ⟨p', sp, np, mp, ap, rigidKept, -, pairs⟩ := stable p inst known holds.2 holdsArity normalp
      have notPair' : isPair p' = false := by
        cases pair : isPair p' with
        | false => rfl
        | true =>
            rcases pairs pair with bad | bad
            · rw [notPair] at bad; cases bad
            · rw [holds.1] at bad; cases bad
      refine ⟨.fst p', star_fst sp, (normal_fst_iff empty).mpr ⟨notPair', np⟩, ?_, ap, fun _ => rfl,
        fun impossible => (by cases impossible), fun impossible => (by cases impossible)⟩
      simp only [miller, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
      exact ⟨rigidKept holds.1, mp⟩
  | _, .snd p, _, flexible, flexible', _, inst, _, _, known, holds, holdsArity, normal => by
      simp only [miller, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at holds
      simp only [arities] at holdsArity
      obtain ⟨notPair, normalp⟩ := (normal_snd_iff empty).mp normal
      obtain ⟨p', sp, np, mp, ap, rigidKept, -, pairs⟩ := stable p inst known holds.2 holdsArity normalp
      have notPair' : isPair p' = false := by
        cases pair : isPair p' with
        | false => rfl
        | true =>
            rcases pairs pair with bad | bad
            · rw [notPair] at bad; cases bad
            · rw [holds.1] at bad; cases bad
      refine ⟨.snd p', star_snd sp, (normal_snd_iff empty).mpr ⟨notPair', np⟩, ?_, ap, fun _ => rfl,
        fun impossible => (by cases impossible), fun impossible => (by cases impossible)⟩
      simp only [miller, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
      exact ⟨rigidKept holds.1, mp⟩
  | _, .app f a, _, flexible, flexible', σ, inst, arity, arity', known, holds, holdsArity, normal => by
      by_cases flexibleSpine : flexHead flexible (spineHead f) = true
      · simp only [miller, flexibleSpine, if_true] at holds
        unfold millerSpine at holds
        cases read : readSpine (Tm.app f a) with
        | none => rw [read] at holds; cases holds
        | some found =>
            obtain ⟨head, arguments⟩ := found
            rw [read] at holds
            simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
              decide_eq_true_eq] at holds
            obtain ⟨⟨flexibleHead, rigid⟩, distinct⟩ := holds
            have shape := readSpine_spec read
            rw [shape] at holdsArity ⊢
            exact stable_spine empty inst known flexibleHead rigid distinct
              (arities_appsVar_length flexibleHead arguments holdsArity)
      · have rigidSpine : flexHead flexible (spineHead f) = false := by
          cases h : flexHead flexible (spineHead f)
          · rfl
          · exact absurd h flexibleSpine
        simp only [miller, rigidSpine, Bool.false_eq_true, if_false, Bool.and_eq_true] at holds
        simp only [arities, rigidSpine, Bool.false_eq_true, if_false, Bool.and_eq_true] at holdsArity
        obtain ⟨notLam, normalf, normala⟩ := (normal_app_iff empty).mp normal
        obtain ⟨f', sf, nf, mf, af, rigidKept, lams, -⟩ := stable f inst known holds.1 holdsArity.1 normalf
        obtain ⟨a', sa, na, ma, aa, -⟩ := stable a inst known holds.2 holdsArity.2 normala
        have notLam' : isLam f' = false := by
          cases lam : isLam f' with
          | false => rfl
          | true =>
              rcases lams lam with bad | bad
              · rw [notLam] at bad; cases bad
              · rw [rigidSpine] at bad; cases bad
        refine ⟨.app f' a', star_app sf sa, (normal_app_iff empty).mpr ⟨notLam', nf, na⟩, ?_, ?_, ?_,
          fun impossible => (by cases impossible), fun impossible => (by cases impossible)⟩
        · simp only [miller, rigidKept rigidSpine, Bool.false_eq_true, if_false, Bool.and_eq_true]
          exact ⟨mf, ma⟩
        · simp only [arities, rigidKept rigidSpine, Bool.false_eq_true, if_false, Bool.and_eq_true]
          exact ⟨af, aa⟩
        · intro _
          exact rigidKept rigidSpine

end ContextualDependentDynamicFragment
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
