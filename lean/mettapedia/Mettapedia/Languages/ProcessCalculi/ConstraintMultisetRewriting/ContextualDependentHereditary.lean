import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDynamicFragmentStore

/-!
# Hereditary substitution of pattern answers on Miller normal forms

A **pattern answer** solves one metavariable `F` by a normal term `v` with Miller occurrences whose free variables
are all metavariables: `F := v`, with `v = λ z̄. u` for a pattern solution `u`. Its leading abstractions are not
fixed: the answer may have more or fewer of them than an occurrence of `F` has arguments.

**Hereditary substitution** of the answer into a normal term `t` with Miller occurrences replaces each occurrence
`F y₁ … yⱼ` (distinct rigid locals) by `v y₁ … yⱼ` and contracts the redexes this creates. Since the arguments are
variables, each contraction is a renaming: `v`'s leading abstractions are consumed by the arguments one at a time,
and what remains is applied to the arguments left over (`collapse_miller`). No other redex is created, so the result
is the normal form of the substitution (`stableMiller`):

* it is a reduct of `t` instantiated (`Star`), and normal, hence the normal form by confluence;
* it has Miller occurrences: an occurrence applied to more arguments than `v` has abstractions becomes a flexible
  spine of `v` applied to further distinct locals, still a Miller spine, or a rigid spine applied to locals.

No arity is read: the theorem holds for occurrences applied to fewer, exactly, or more arguments than `F`'s
declared arity. This is the occurrence condition of the stratified Miller class
(`ContextualDependentShortClosure.StratifiedMiller`). R86's exact-arity stability
(`ContextualDependentDynamicFragment.stable`) is the case where every occurrence has as many arguments as the
answer has abstractions (`Instantiation.toPattern`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentHereditary

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ExecutableReduction ContextualDependentExecutableJoin ContextualDependentDynamicFragment
open ContextualDependentGeneralPattern (liftFlexible)

variable {Head : Type}

/-! ## Forward spines -/

/-- `appsFwd t [y₁, …, yₖ] = t y₁ … yₖ`: a head applied to variables, first argument first. -/
def appsFwd {n : Nat} (head : Tm Head n) : List (Fin n) → Tm Head n
  | [] => head
  | argument :: rest => appsFwd (.app head (.var argument)) rest

theorem appsFwd_append_single {n : Nat} (argument : Fin n) :
    ∀ (arguments : List (Fin n)) (head : Tm Head n),
      appsFwd head (arguments ++ [argument]) = .app (appsFwd head arguments) (.var argument)
  | [], _ => rfl
  | first :: rest, head => appsFwd_append_single argument rest (.app head (.var first))

/-- The spines of `appsVar`, innermost argument first, are the forward spines of the reversed list. -/
theorem appsVar_eq_appsFwd {n : Nat} (head : Tm Head n) :
    ∀ arguments : List (Fin n), appsVar head arguments = appsFwd head arguments.reverse
  | [] => rfl
  | argument :: rest => by
      rw [List.reverse_cons, appsFwd_append_single, ← appsVar_eq_appsFwd head rest]
      rfl

theorem appsFwd_appsVar {n : Nat} (head : Tm Head n) :
    ∀ (more arguments : List (Fin n)), appsFwd (appsVar head arguments) more = appsVar head (more.reverse ++ arguments)
  | [], _ => rfl
  | argument :: rest, arguments => by
      change appsFwd (appsVar head (argument :: arguments)) rest = _
      rw [appsFwd_appsVar head rest (argument :: arguments), List.reverse_cons, List.append_assoc]
      rfl

theorem spineHead_appsFwd {n : Nat} : ∀ (more : List (Fin n)) (head : Tm Head n),
    spineHead (appsFwd head more) = spineHead head
  | [], _ => rfl
  | argument :: rest, head => by
      rw [appsFwd, spineHead_appsFwd rest]
      rfl

theorem isLam_appsFwd {n : Nat} : ∀ (argument : Fin n) (rest : List (Fin n)) (head : Tm Head n),
    isLam (appsFwd head (argument :: rest)) = false
  | _, [], _ => rfl
  | argument, next :: rest, head => isLam_appsFwd next rest (.app head (.var argument))

theorem isPair_appsFwd {n : Nat} : ∀ (argument : Fin n) (rest : List (Fin n)) (head : Tm Head n),
    isPair (appsFwd head (argument :: rest)) = false
  | _, [], _ => rfl
  | argument, next :: rest, head => isPair_appsFwd next rest (.app head (.var argument))

variable {R : Rules Head}

theorem star_appsFwd {n : Nat} : ∀ (more : List (Fin n)) {head head' : Tm Head n},
    Star (R := R) head head' → Star (R := R) (appsFwd head more) (appsFwd head' more)
  | [], _, _, steps => steps
  | _ :: rest, _, _, steps => star_appsFwd rest (star_app steps .refl)

theorem miller_appsFwd_rigid {n : Nat} {flexible : Fin n → Bool} :
    ∀ (more : List (Fin n)) {head : Tm Head n}, miller flexible head = true →
      flexHead flexible (spineHead head) = false → miller flexible (appsFwd head more) = true
  | [], _, holds, _ => holds
  | argument :: rest, head, holds, rigidHead => by
      refine miller_appsFwd_rigid rest ?_ rigidHead
      simp only [miller, rigidHead, Bool.false_eq_true, if_false, Bool.and_eq_true]
      exact ⟨holds, trivial⟩

theorem isLam_rename {n m : Nat} (ρ : Ren n m) : ∀ t : Tm Head n, isLam (Presentation.rename ρ t) = isLam t
  | .var _ | .const _ | .head _ | .pi _ _ | .sigma _ _ | .id _ _ _ | .lam _ | .app _ _ | .pair _ _ | .fst _ | .snd _
  | .refl _ => rfl

theorem not_lam_of_isLam {n : Nat} : ∀ {t : Tm Head n}, isLam t = false → ∀ body, t ≠ .lam body
  | .var _, _, _, h | .const _, _, _, h | .head _, _, _, h | .pi _ _, _, _, h | .sigma _ _, _, _, h
  | .id _ _ _, _, _, h | .app _ _, _, _, h | .pair _ _, _, _, h | .fst _, _, _, h | .snd _, _, _, h
  | .refl _, _, _, h => by cases h
  | .lam _, notLam, _, _ => by cases notLam

theorem cons_injective {o m : Nat} {ρ : Ren o m} (injective : Function.Injective ρ) {y : Fin m}
    (avoids : ∀ i, ρ i ≠ y) : Function.Injective (Fin.cases y ρ : Fin (o + 1) → Fin m) := by
  intro first second same
  rcases Fin.eq_zero_or_eq_succ first with rfl | ⟨first, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ second with rfl | ⟨second, rfl⟩
  · rfl
  · exact absurd same.symm (avoids second)
  · exact absurd same (avoids first)
  · exact congrArg Fin.succ (injective same)

/-- Contracting an abstraction, renamed, against a variable is a renaming of its body. -/
theorem inst0_var_rename_liftRen {o m : Nat} (ρ : Ren o m) (y : Fin m) (body : Tm Head (o + 1)) :
    inst0 (.var y) (Presentation.rename (liftRen ρ) body) = Presentation.rename (Fin.cases y ρ) body := by
  unfold inst0
  rw [subst_rename, ← subst_renSub]
  refine subst_ext (fun index => ?_) body
  refine Fin.cases ?_ (fun prior => ?_) index
  · rfl
  · rfl

variable (empty : R.computation = RootComputation.empty)
include empty

theorem normal_appsFwd {n : Nat} : ∀ (more : List (Fin n)) {head : Tm Head n}, Normal R head → isLam head = false →
    Normal R (appsFwd head more)
  | [], _, normal, _ => normal
  | argument :: rest, _, normal, notLam =>
      normal_appsFwd rest ((normal_app_iff empty).mpr ⟨notLam, normal, normal_var empty argument⟩) rfl

/-! ## Contracting an answer against variables -/

/-- **An answer applied to distinct rigid variables contracts to a Miller normal form.** A normal term `v` with Miller
occurrences, renamed injectively into flexible variables and its own rigid binders, applied to distinct rigid
variables outside the renaming's image, reduces to a normal term with Miller occurrences: each leading abstraction of
`v` takes one argument, by a renaming, and the arguments left over are appended to what remains. -/
theorem collapse_miller {m : Nat} {flexible' : Fin m → Bool} :
    ∀ (more : List (Fin m)) {o : Nat} (v : Tm Head o) (mark : Fin o → Bool) (ρ : Ren o m),
      Normal R v → miller mark v = true → Function.Injective ρ → (∀ i, flexible' (ρ i) = mark i) →
      (∀ y ∈ more, flexible' y = false) → more.Nodup → (∀ y ∈ more, ∀ i, ρ i ≠ y) →
      ∃ t', Star (R := R) (appsFwd (Presentation.rename ρ v) more) t' ∧ Normal R t' ∧ miller flexible' t' = true
  | [], _, v, _, ρ, normal, holds, injective, respects, _, _, _ =>
      ⟨Presentation.rename ρ v, .refl, (ContextualDependentNormalizing.normal_rename_iff empty ρ v).mpr normal,
        miller_rename v injective respects holds⟩
  | y :: rest, o, v, mark, ρ, normal, holds, injective, respects, rigid, distinct, avoids => by
      by_cases abstraction : ∃ body, v = .lam body
      · obtain ⟨body, rfl⟩ := abstraction
        have fresh : ∀ i, ρ i ≠ y := avoids y List.mem_cons_self
        have restRigid : ∀ other ∈ rest, flexible' other = false :=
          fun other member => rigid other (List.mem_cons_of_mem _ member)
        have restDistinct := (List.nodup_cons.mp distinct).2
        have restAvoids : ∀ other ∈ rest, ∀ i, (Fin.cases y ρ : Fin (o + 1) → Fin m) i ≠ other := by
          intro other member i
          refine Fin.cases ?_ (fun prior => ?_) i
          · intro same
            change y = other at same
            exact (List.nodup_cons.mp distinct).1 (by rw [same]; exact member)
          · exact avoids other (List.mem_cons_of_mem _ member) prior
        have consRespects : ∀ i, flexible' ((Fin.cases y ρ : Fin (o + 1) → Fin m) i) = liftFlexible mark i := by
          intro i
          refine Fin.cases ?_ (fun prior => ?_) i
          · exact rigid y List.mem_cons_self
          · exact respects prior
        simp only [miller] at holds
        obtain ⟨t', steps, normal', holds'⟩ := collapse_miller rest body (liftFlexible mark) (Fin.cases y ρ)
          ((normal_lam_iff empty).mp normal) holds (cons_injective injective fresh) consRespects restRigid
          restDistinct restAvoids
        refine ⟨t', ?_, normal', holds'⟩
        have contracted : Star (R := R) (.app (.lam (Presentation.rename (liftRen ρ) body)) (.var y))
            (Presentation.rename (Fin.cases y ρ) body) := by
          rw [← inst0_var_rename_liftRen]
          exact Relation.ReflTransGen.single (.betaPi _ _)
        exact (star_appsFwd rest contracted).trans steps
      · have notLam : isLam v = false := by
          cases v with
          | lam body => exact absurd ⟨body, rfl⟩ abstraction
          | var _ | const _ | head _ | pi _ _ | sigma _ _ | id _ _ _ | app _ _ | pair _ _ | fst _ | snd _
          | refl _ => rfl
        refine ⟨appsFwd (Presentation.rename ρ v) (y :: rest), .refl,
          normal_appsFwd empty _ ((ContextualDependentNormalizing.normal_rename_iff empty ρ v).mpr normal)
            (by rw [isLam_rename]; exact notLam), ?_⟩
        rcases side_shape v holds with spine | rigidHead
        · unfold millerSpine at spine
          cases read : readSpine v with
          | none => rw [read] at spine; cases spine
          | some found =>
              obtain ⟨head, arguments⟩ := found
              rw [read] at spine
              simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
                decide_eq_true_eq] at spine
              obtain ⟨⟨flexibleHead, argumentsRigid⟩, argumentsDistinct⟩ := spine
              rw [readSpine_spec read, rename_appsVar, appsFwd_appsVar]
              refine miller_appsVar (by rw [respects]; exact flexibleHead) _ ?_ ?_
              · intro other member
                rcases List.mem_append.mp member with early | late
                · exact rigid other (List.mem_reverse.mp early)
                · obtain ⟨argument, inArguments, rfl⟩ := List.mem_map.mp late
                  rw [respects]
                  exact argumentsRigid argument inArguments
              · refine List.nodup_append.mpr ⟨List.nodup_reverse.mpr distinct, argumentsDistinct.map injective, ?_⟩
                intro first early second late same
                obtain ⟨argument, _, rfl⟩ := List.mem_map.mp late
                exact avoids first (List.mem_reverse.mp early) argument same.symm
        · refine miller_appsFwd_rigid _ (miller_rename v injective respects holds) ?_
          rw [spineHead_rename, flexHead_rename ρ respects]
          exact rigidHead

/-! ## Pattern answers -/

/-- **A pattern answer** for `target`: a normal term with Miller occurrences whose free variables are all
metavariables, reached through an injective renaming into flexible variables; every other variable is renamed
injectively, respecting the marking. -/
structure PatternAnswer (R : Rules Head) {n m : Nat} (flexible : Fin n → Bool) (flexible' : Fin m → Bool)
    (σ : Sub Head n m) : Type where
  target : Fin n
  flexibleTarget : flexible target = true
  rename : (i : Fin n) → i ≠ target → Fin m
  injective : ∀ i j (hi : i ≠ target) (hj : j ≠ target), rename i hi = rename j hj → i = j
  respects : ∀ i (hi : i ≠ target), flexible' (rename i hi) = flexible i
  others : ∀ i (hi : i ≠ target), σ i = .var (rename i hi)
  outerArity : Nat
  outer : Ren outerArity m
  outerInjective : Function.Injective outer
  outerFlexible : ∀ j, flexible' (outer j) = true
  value : Tm Head outerArity
  solution : σ target = Presentation.rename outer value
  valueMiller : miller (fun _ => true) value = true
  valueNormal : Normal R value

omit empty in
/-- A pattern answer under one more binder. -/
def PatternAnswer.lift {n m : Nat} {flexible : Fin n → Bool} {flexible' : Fin m → Bool} {σ : Sub Head n m}
    (answer : PatternAnswer R flexible flexible' σ) :
    PatternAnswer R (liftFlexible flexible) (liftFlexible flexible') (liftSub σ) where
  target := answer.target.succ
  flexibleTarget := answer.flexibleTarget
  rename i := Fin.cases (motive := fun i => i ≠ answer.target.succ → Fin (m + 1)) (fun _ => 0)
    (fun j hj => (answer.rename j (fun h => hj (congrArg Fin.succ h))).succ) i
  injective := by
    intro i j hi hj same
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩ <;> rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · rfl
    · exact absurd same (Fin.succ_ne_zero _).symm
    · exact absurd same (Fin.succ_ne_zero _)
    · exact congrArg Fin.succ (answer.injective i j _ _ (Fin.succ_injective _ same))
  respects := by
    intro i hi
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · rfl
    · exact answer.respects i _
  others := by
    intro i hi
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · rfl
    · change Presentation.rename wk (σ i) = _
      rw [answer.others i (fun h => hi (congrArg Fin.succ h))]
      rfl
  outerArity := answer.outerArity
  outer := fun j => (answer.outer j).succ
  outerInjective := fun _ _ same => answer.outerInjective (Fin.succ_injective _ same)
  outerFlexible := fun j => answer.outerFlexible j
  value := answer.value
  solution := by
    change Presentation.rename wk (σ answer.target) = _
    rw [answer.solution, rename_comp]
    rfl
  valueMiller := answer.valueMiller
  valueNormal := answer.valueNormal

omit empty in
/-- The Miller occurrences of an abstraction are those of its body, with the binders rigid. -/
theorem miller_lamsVar {o : Nat} : ∀ (count : Nat) (body : Tm Head (o + count)),
    miller (fun _ => true) (lamsVar count body) = miller (bodyFlexible count) body
  | 0, _ => rfl
  | count + 1, body => miller_lamsVar count (.lam body)

theorem normal_lamsVar {o : Nat} : ∀ (count : Nat) (body : Tm Head (o + count)), Normal R body →
    Normal R (lamsVar count body)
  | 0, _, normal => normal
  | count + 1, _, normal => normal_lamsVar count _ ((normal_lam_iff empty).mpr normal)

/-- **R86's pattern instantiations are pattern answers**: the answer is the abstraction of the solution body. -/
def Instantiation.toPattern {n m : Nat} {flexible : Fin n → Bool} {flexible' : Fin m → Bool} {σ : Sub Head n m}
    (inst : Instantiation R flexible flexible' σ) : PatternAnswer R flexible flexible' σ where
  target := inst.target
  flexibleTarget := inst.flexibleTarget
  rename := inst.rename
  injective := inst.injective
  respects := inst.respects
  others := inst.others
  outerArity := inst.outerArity
  outer := inst.outer
  outerInjective := inst.outerInjective
  outerFlexible := inst.outerFlexible
  value := lamsVar inst.arity inst.body
  solution := by rw [inst.solution, rename_lamsVar]
  valueMiller := by rw [miller_lamsVar]; exact inst.bodyMiller
  valueNormal := normal_lamsVar empty inst.arity inst.body inst.bodyNormal

/-! ## Stability with any number of arguments -/

omit empty in
/-- What hereditary substitution gives for one term: a normal reduct of the instance with Miller occurrences, a rigid
spine head kept rigid, and no new introduction except where an occurrence of the answered metavariable contracted. -/
abbrev StableMiller {n m : Nat} (flexible : Fin n → Bool) (flexible' : Fin m → Bool) (σ : Sub Head n m)
    (t : Tm Head n) : Prop :=
  ∃ t', Star (R := R) (subst σ t) t' ∧ Normal R t' ∧ miller flexible' t' = true ∧
    (flexHead flexible (spineHead t) = false → flexHead flexible' (spineHead t') = false) ∧
    (isLam t' = true → isLam t = true ∨ flexHead flexible (spineHead t) = true) ∧
    (isPair t' = true → isPair t = true ∨ flexHead flexible (spineHead t) = true)

/-- A flexible spine applied to distinct rigid variables, hereditarily substituted. -/
theorem stableMiller_spine {n m : Nat} {flexible : Fin n → Bool} {flexible' : Fin m → Bool} {σ : Sub Head n m}
    (answer : PatternAnswer R flexible flexible' σ) {head : Fin n} {arguments : List (Fin n)}
    (flexibleHead : flexible head = true) (rigid : ∀ argument ∈ arguments, flexible argument = false)
    (distinct : arguments.Nodup) :
    StableMiller (R := R) flexible flexible' σ (appsVar (.var head) arguments) := by
  have avoid : ∀ argument ∈ arguments, argument ≠ answer.target := fun argument member same => by
    have := rigid argument member
    rw [same, answer.flexibleTarget] at this
    cases this
  let images := arguments.pmap answer.rename avoid
  have renamedRigid : ∀ argument ∈ images, flexible' argument = false := by
    intro renamed member
    obtain ⟨argument, inArguments, rfl⟩ := List.mem_pmap.mp member
    rw [answer.respects argument]
    exact rigid argument inArguments
  have renamedDistinct : images.Nodup :=
    distinct.pmap fun i hi j hj same => answer.injective i j hi hj same
  have substituted : subst σ (appsVar (.var head) arguments) = appsVar (σ head) images :=
    subst_appsVar_pmap σ (.var head) answer.rename answer.others arguments avoid
  have spineFlexible : flexHead flexible (spineHead (appsVar (Head := Head) (.var head) arguments)) = true := by
    rw [spineHead_appsVar]
    exact flexibleHead
  by_cases isTarget : head = answer.target
  · subst isTarget
    obtain ⟨t', steps, normal', holds'⟩ := collapse_miller empty images.reverse answer.value (fun _ => true)
      answer.outer answer.valueNormal answer.valueMiller answer.outerInjective answer.outerFlexible
      (fun other member => renamedRigid other (List.mem_reverse.mp member))
      (List.nodup_reverse.mpr renamedDistinct)
      (fun other member index same => by
        have := renamedRigid other (List.mem_reverse.mp member)
        rw [← same, answer.outerFlexible] at this
        cases this)
    refine ⟨t', ?_, normal', holds', ?_, fun _ => .inr spineFlexible, fun _ => .inr spineFlexible⟩
    · rw [substituted, answer.solution, appsVar_eq_appsFwd]
      exact steps
    · intro rigidSpine
      rw [spineFlexible] at rigidSpine
      cases rigidSpine
  · have renamedHead : σ head = .var (answer.rename head isTarget) := answer.others head isTarget
    have renamedFlexible : flexible' (answer.rename head isTarget) = true := by
      rw [answer.respects head isTarget]; exact flexibleHead
    refine ⟨appsVar (.var (answer.rename head isTarget)) images, ?_, normal_appsVar empty _ _,
      miller_appsVar renamedFlexible _ renamedRigid renamedDistinct, ?_, fun _ => .inr spineFlexible,
      fun _ => .inr spineFlexible⟩
    · rw [substituted, renamedHead]
    · intro rigidSpine
      rw [spineFlexible] at rigidSpine
      cases rigidSpine

/-- **Hereditary substitution of a pattern answer** into a normal term with Miller occurrences: the instance
reduces to a normal term with Miller occurrences, whatever the number of arguments of each occurrence of the answered
metavariable. -/
theorem stableMiller : ∀ {n : Nat} (t : Tm Head n) {m : Nat} {flexible : Fin n → Bool} {flexible' : Fin m → Bool}
    {σ : Sub Head n m}, PatternAnswer R flexible flexible' σ →
    miller flexible t = true → Normal R t → StableMiller (R := R) flexible flexible' σ t
  | _, .var i, _, flexible, flexible', σ, answer, _, _ => by
      by_cases isTarget : i = answer.target
      · subst isTarget
        exact stableMiller_spine empty answer (arguments := []) answer.flexibleTarget
          (fun _ member => absurd member List.not_mem_nil) List.nodup_nil
      · refine ⟨.var (answer.rename i isTarget), ?_, normal_var empty _, rfl, ?_, ?_, ?_⟩
        · change Star (R := R) (σ i) _
          rw [answer.others i isTarget]
        · intro rigidHead
          change flexible' (answer.rename i isTarget) = false
          rw [answer.respects i isTarget]
          exact rigidHead
        · intro impossible; cases impossible
        · intro impossible; cases impossible
  | _, .const c, _, _, _, _, _, _, _ =>
      ⟨.const c, .refl, normal_const empty c, rfl, fun _ => rfl, fun impossible => (by cases impossible),
        fun impossible => (by cases impossible)⟩
  | _, .head h, _, _, _, _, _, _, _ =>
      ⟨.head h, .refl, normal_head empty h, rfl, fun _ => rfl, fun impossible => (by cases impossible),
        fun impossible => (by cases impossible)⟩
  | _, .pi A B, _, _, _, _, answer, holds, normal => by
      simp only [miller, Bool.and_eq_true] at holds
      obtain ⟨normalA, normalB⟩ := (normal_pi_iff empty).mp normal
      obtain ⟨A', sA, nA, mA, -⟩ := stableMiller A answer holds.1 normalA
      obtain ⟨B', sB, nB, mB, -⟩ := stableMiller B answer.lift holds.2 normalB
      refine ⟨.pi A' B', star_pi sA sB, (normal_pi_iff empty).mpr ⟨nA, nB⟩, ?_, fun _ => rfl,
        fun impossible => (by cases impossible), fun impossible => (by cases impossible)⟩
      simp only [miller, Bool.and_eq_true]
      exact ⟨mA, mB⟩
  | _, .sigma A B, _, _, _, _, answer, holds, normal => by
      simp only [miller, Bool.and_eq_true] at holds
      obtain ⟨normalA, normalB⟩ := (normal_sigma_iff empty).mp normal
      obtain ⟨A', sA, nA, mA, -⟩ := stableMiller A answer holds.1 normalA
      obtain ⟨B', sB, nB, mB, -⟩ := stableMiller B answer.lift holds.2 normalB
      refine ⟨.sigma A' B', star_sigma sA sB, (normal_sigma_iff empty).mpr ⟨nA, nB⟩, ?_, fun _ => rfl,
        fun impossible => (by cases impossible), fun impossible => (by cases impossible)⟩
      simp only [miller, Bool.and_eq_true]
      exact ⟨mA, mB⟩
  | _, .id A a b, _, _, _, _, answer, holds, normal => by
      simp only [miller, Bool.and_eq_true] at holds
      obtain ⟨normalA, normala, normalb⟩ := (normal_id_iff empty).mp normal
      obtain ⟨A', sA, nA, mA, -⟩ := stableMiller A answer holds.1.1 normalA
      obtain ⟨a', sa, na, ma, -⟩ := stableMiller a answer holds.1.2 normala
      obtain ⟨b', sb, nb, mb, -⟩ := stableMiller b answer holds.2 normalb
      refine ⟨.id A' a' b', star_id sA sa sb, (normal_id_iff empty).mpr ⟨nA, na, nb⟩, ?_, fun _ => rfl,
        fun impossible => (by cases impossible), fun impossible => (by cases impossible)⟩
      simp only [miller, Bool.and_eq_true]
      exact ⟨⟨mA, ma⟩, mb⟩
  | _, .lam body, _, _, _, _, answer, holds, normal => by
      simp only [miller] at holds
      obtain ⟨body', s, nb, mb, -⟩ := stableMiller body answer.lift holds ((normal_lam_iff empty).mp normal)
      exact ⟨.lam body', star_lam s, (normal_lam_iff empty).mpr nb, mb, fun _ => rfl,
        fun _ => .inl rfl, fun impossible => (by cases impossible)⟩
  | _, .pair a b, _, _, _, _, answer, holds, normal => by
      simp only [miller, Bool.and_eq_true] at holds
      obtain ⟨normala, normalb⟩ := (normal_pair_iff empty).mp normal
      obtain ⟨a', sa, na, ma, -⟩ := stableMiller a answer holds.1 normala
      obtain ⟨b', sb, nb, mb, -⟩ := stableMiller b answer holds.2 normalb
      refine ⟨.pair a' b', star_pair sa sb, (normal_pair_iff empty).mpr ⟨na, nb⟩, ?_, fun _ => rfl,
        fun impossible => (by cases impossible), fun _ => .inl rfl⟩
      simp only [miller, Bool.and_eq_true]
      exact ⟨ma, mb⟩
  | _, .refl a, _, _, _, _, answer, holds, normal => by
      simp only [miller] at holds
      obtain ⟨a', sa, na, ma, -⟩ := stableMiller a answer holds ((normal_refl_iff empty).mp normal)
      exact ⟨.refl a', star_refl sa, (normal_refl_iff empty).mpr na, ma, fun _ => rfl,
        fun impossible => (by cases impossible), fun impossible => (by cases impossible)⟩
  | _, .fst p, _, flexible, flexible', _, answer, holds, normal => by
      simp only [miller, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at holds
      obtain ⟨notPair, normalp⟩ := (normal_fst_iff empty).mp normal
      obtain ⟨p', sp, np, mp, rigidKept, -, pairs⟩ := stableMiller p answer holds.2 normalp
      have notPair' : isPair p' = false := by
        cases pair : isPair p' with
        | false => rfl
        | true =>
            rcases pairs pair with bad | bad
            · rw [notPair] at bad; cases bad
            · rw [holds.1] at bad; cases bad
      refine ⟨.fst p', star_fst sp, (normal_fst_iff empty).mpr ⟨notPair', np⟩, ?_, fun _ => rfl,
        fun impossible => (by cases impossible), fun impossible => (by cases impossible)⟩
      simp only [miller, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
      exact ⟨rigidKept holds.1, mp⟩
  | _, .snd p, _, flexible, flexible', _, answer, holds, normal => by
      simp only [miller, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at holds
      obtain ⟨notPair, normalp⟩ := (normal_snd_iff empty).mp normal
      obtain ⟨p', sp, np, mp, rigidKept, -, pairs⟩ := stableMiller p answer holds.2 normalp
      have notPair' : isPair p' = false := by
        cases pair : isPair p' with
        | false => rfl
        | true =>
            rcases pairs pair with bad | bad
            · rw [notPair] at bad; cases bad
            · rw [holds.1] at bad; cases bad
      refine ⟨.snd p', star_snd sp, (normal_snd_iff empty).mpr ⟨notPair', np⟩, ?_, fun _ => rfl,
        fun impossible => (by cases impossible), fun impossible => (by cases impossible)⟩
      simp only [miller, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
      exact ⟨rigidKept holds.1, mp⟩
  | _, .app f a, _, flexible, flexible', σ, answer, holds, normal => by
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
            rw [readSpine_spec read]
            exact stableMiller_spine empty answer flexibleHead rigid distinct
      · have rigidSpine : flexHead flexible (spineHead f) = false := by
          cases h : flexHead flexible (spineHead f)
          · rfl
          · exact absurd h flexibleSpine
        simp only [miller, rigidSpine, Bool.false_eq_true, if_false, Bool.and_eq_true] at holds
        obtain ⟨notLam, normalf, normala⟩ := (normal_app_iff empty).mp normal
        obtain ⟨f', sf, nf, mf, rigidKept, lams, -⟩ := stableMiller f answer holds.1 normalf
        obtain ⟨a', sa, na, ma, -⟩ := stableMiller a answer holds.2 normala
        have notLam' : isLam f' = false := by
          cases lam : isLam f' with
          | false => rfl
          | true =>
              rcases lams lam with bad | bad
              · rw [notLam] at bad; cases bad
              · rw [rigidSpine] at bad; cases bad
        refine ⟨.app f' a', star_app sf sa, (normal_app_iff empty).mpr ⟨notLam', nf, na⟩, ?_, ?_,
          fun impossible => (by cases impossible), fun impossible => (by cases impossible)⟩
        · simp only [miller, rigidKept rigidSpine, Bool.false_eq_true, if_false, Bool.and_eq_true]
          exact ⟨mf, ma⟩
        · intro _
          exact rigidKept rigidSpine

end ContextualDependentHereditary
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
