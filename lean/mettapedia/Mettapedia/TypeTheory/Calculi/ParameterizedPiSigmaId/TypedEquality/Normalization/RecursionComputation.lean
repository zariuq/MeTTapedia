import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.DefinitionConsequences

/-!
# The equations of a recursive definition as a root computation

The equations of a definition by structural recursion,
`f x₀ ⋯ x_{s-1} (k a₁ ⋯ aₐ) y₁ ⋯ y_d ⟶ rhs_k`, form a root computation closed
under renaming and substitution. Its steps occur at full applications of `f`
whose scrutinee is a constructor form, and they are deterministic when the
constructors have distinct names.

Root computations combine: the union of the root computations of distinct
computing constants is a root computation, deterministic when each part is.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open TelescopeAbstraction (closeType applyClosed applyClosed_subst)

variable {Head : Type}

/-! ## Substituting the pattern's substitutions -/

theorem subst_extendSub_comp {n m k : Nat} (τ : Sub Head m k) (ρ : Sub Head n m)
    (values : Nat → Tm Head m) :
    ∀ (b : Nat), (fun ι => Presentation.subst τ (extendSub ρ values b ι)) =
      extendSub (fun i => Presentation.subst τ (ρ i))
        (fun l => Presentation.subst τ (values l)) b
  | 0 => rfl
  | b + 1 => by
      funext ι
      refine Fin.cases ?_ (fun i => ?_) ι
      · rfl
      · show Presentation.subst τ (extendSub ρ values b i) = extendSub _ _ b i
        exact congrFun (subst_extendSub_comp τ ρ values b) i

theorem getD_map_subst {n m : Nat} (τ : Sub Head n m) :
    ∀ (as : List (Tm Head n)) (l : Nat),
      (as.map (Presentation.subst τ)).getD l defaultTm =
        Presentation.subst τ (as.getD l defaultTm)
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: as, l + 1 => getD_map_subst τ as l

theorem subst_matchSub {m k s a : Nat} (τ : Sub Head m k) (as : List (Tm Head m)) :
    ∀ (d : Nat) (σ : Sub Head (s + 1 + d) m),
      (fun ι => Presentation.subst τ (matchSub s a as d σ ι)) =
        matchSub s a (as.map (Presentation.subst τ)) d (fun i => Presentation.subst τ (σ i))
  | 0, σ => by
      show (fun ι => Presentation.subst τ
        (extendSub (tailSub σ) (fun l => as.getD l defaultTm) a ι)) = _
      rw [subst_extendSub_comp]
      exact congrArg (fun values => extendSub (fun i => Presentation.subst τ (tailSub σ i)) values a)
        (funext fun l => (getD_map_subst τ as l).symm)
  | d + 1, σ => by
      funext ι
      refine Fin.cases ?_ (fun i => ?_) ι
      · rfl
      · show Presentation.subst τ (matchSub s a as d (tailSub σ) i) =
          matchSub s a (as.map (Presentation.subst τ)) d
            (tailSub fun i => Presentation.subst τ (σ i)) i
        exact congrFun (subst_matchSub τ as d (tailSub σ)) i

theorem subst_replaceScrut {m k s : Nat} (τ : Sub Head m k) (x : Tm Head m) :
    ∀ (d : Nat) (σ : Sub Head (s + 1 + d) m),
      (fun ι => Presentation.subst τ (replaceScrut s x d σ ι)) =
        replaceScrut s (Presentation.subst τ x) d (fun i => Presentation.subst τ (σ i))
  | 0, _ => by
      funext ι
      refine Fin.cases ?_ (fun i => ?_) ι
      · rfl
      · rfl
  | d + 1, σ => by
      funext ι
      refine Fin.cases ?_ (fun i => ?_) ι
      · rfl
      · show Presentation.subst τ (replaceScrut s x d (tailSub σ) i) =
          replaceScrut s (Presentation.subst τ x) d (tailSub fun i => Presentation.subst τ (σ i)) i
        exact congrFun (subst_replaceScrut τ x d (tailSub σ)) i

/-- The arguments of an application to a telescope determine the
substitution. -/
theorem telescopeArgs_injective (e : (i : Nat) → Tm Head i) {m : Nat} :
    ∀ (n : Nat) {σ σ' : Sub Head n m},
      telescopeArgs (ofEntries e n) σ = telescopeArgs (ofEntries e n) σ' → σ = σ'
  | 0, _, _, _ => funext fun i => Fin.elim0 i
  | n + 1, σ, σ', h => by
      rw [telescopeArgs_ofEntries_succ, telescopeArgs_ofEntries_succ] at h
      obtain ⟨h₁, h₂⟩ := List.append_inj' h rfl
      have e₁ := telescopeArgs_injective e n h₁
      have e₂ : σ 0 = σ' 0 := (List.cons.inj h₂).1
      calc σ = consSub (σ 0) (tailSub σ) := (consSub_eta σ).symm
        _ = consSub (σ' 0) (tailSub σ') := by rw [e₁, e₂]
        _ = σ' := consSub_eta σ'

/-! ## The equations -/

/-- An equation of the definition of `f`, by structural recursion on its
argument at position `s`, applied at a constructor form. -/
def RecursionStep (f : DeclName) (ctors : List (DeclName × List (Field Head)))
    (e : (i : Nat) → Tm Head i) (s d : Nat)
    (body : (k : DeclName) → (fields : List (Field Head)) →
      Tm Head (s + fields.length + d + (recPositions fields).length)) {n : Nat}
    (l r : Tm Head n) : Prop :=
  ∃ (k : DeclName) (fields : List (Field Head)) (σ : Sub Head (s + 1 + d) n)
    (as : List (Tm Head n)), (k, fields) ∈ ctors ∧ as.length = fields.length ∧
    l = applyClosed (ofEntries e (s + 1 + d)) (replaceScrut s (appSpine (.const k) as) d σ)
      (.const f) ∧
    r = Presentation.subst (matchSub s fields.length as d σ)
      (Presentation.subst (hypSub f e s d fields) (body k fields))

section Steps

variable {f : DeclName} {ctors : List (DeclName × List (Field Head))} {e : (i : Nat) → Tm Head i}
  {s d : Nat}
  {body : (k : DeclName) → (fields : List (Field Head)) →
    Tm Head (s + fields.length + d + (recPositions fields).length)}

theorem RecursionStep.substitute {n m : Nat} (τ : Sub Head n m) {l r : Tm Head n}
    (step : RecursionStep f ctors e s d body l r) :
    RecursionStep f ctors e s d body (Presentation.subst τ l) (Presentation.subst τ r) := by
  obtain ⟨k, fields, σ, as, mem, has, rfl, rfl⟩ := step
  refine ⟨k, fields, fun i => Presentation.subst τ (σ i), as.map (Presentation.subst τ), mem,
    by rw [List.length_map, has], ?_, ?_⟩
  · rw [applyClosed_subst]
    have h := subst_replaceScrut τ (appSpine (.const k) as) d σ
    rw [subst_appSpine] at h
    exact congrArg (fun σ' => applyClosed (ofEntries e (s + 1 + d)) σ' (.const f)) h
  · rw [subst_comp]
    exact congrArg (fun σ' => Presentation.subst σ'
      (Presentation.subst (hypSub f e s d fields) (body k fields))) (subst_matchSub τ as d σ)

theorem RecursionStep.rename {n m : Nat} (ρ : Ren n m) {l r : Tm Head n}
    (step : RecursionStep f ctors e s d body l r) :
    RecursionStep f ctors e s d body (Presentation.rename ρ l) (Presentation.rename ρ r) := by
  rw [← subst_renSub, ← subst_renSub]
  exact step.substitute (renSub ρ)

/-- A step occurs at a full application of `f` whose scrutinee is a
constructor form. -/
theorem RecursionStep.spine {roles : Roles Head} {T : DeclName}
    (role : roles T = .inductive ctors) (declared : ConstructorsDeclared roles)
    (fRole : roles f = .computes (s + 1 + d) (.split s .constructor fun _ => .leaf)) {n : Nat} {l r : Tm Head n}
    (step : RecursionStep f ctors e s d body l r) :
    ∃ c arity scrutinee args, roles c = .computes arity scrutinee ∧
      l = appSpine (.const c) args ∧ args.length = arity ∧ scrutinee.Accepts roles args := by
  obtain ⟨k, fields, σ, as, mem, _, rfl, rfl⟩ := step
  refine ⟨f, s + 1 + d, _, _, fRole, applyClosed_split e d _ _, ?_, ?_⟩
  · rw [List.length_append, List.length_cons, telescopeArgs_length, suffixArgs_length]
    omega
  · refine InspectTree.accepts_single.mpr
      ⟨appSpine (.const k) as, ?_, .inr ⟨k, _, as, declared.arity role mem, rfl⟩⟩
    rw [List.getElem?_append_right (Nat.le_of_eq (telescopeArgs_length _ _)), telescopeArgs_length,
      Nat.sub_self, List.getElem?_cons_zero, scrutOf_replaceScrut]

/-- The equations are deterministic. -/
theorem RecursionStep.deterministic {roles : Roles Head} {T : DeclName}
    (role : roles T = .inductive ctors) (declared : ConstructorsDeclared roles) {n : Nat}
    {l r r' : Tm Head n} (step : RecursionStep f ctors e s d body l r)
    (step' : RecursionStep f ctors e s d body l r') : r' = r := by
  obtain ⟨k, fields, σ, as, mem, _, rfl, rfl⟩ := step
  obtain ⟨k', fields', σ', as', mem', _, same, rfl⟩ := step'
  rw [applyClosed_eq_appSpine, applyClosed_eq_appSpine] at same
  obtain ⟨_, args⟩ := appSpine_const_injective same
  have subs := telescopeArgs_injective e (s + 1 + d) args
  have scrut := congrArg (scrutOf s d) subs
  rw [scrutOf_replaceScrut, scrutOf_replaceScrut] at scrut
  obtain ⟨hk, has⟩ := appSpine_const_injective scrut
  subst hk has
  have hf := declared.fields_unique role mem mem'
  subst hf
  have matched : matchSub s fields.length as d σ' = matchSub s fields.length as d σ := by
    rw [← matchSub_replaceScrut as (appSpine (.const k) as) d σ', ← subs, matchSub_replaceScrut]
  rw [matched]

end Steps

/-- The equations of the definition of `f` by structural recursion, as a root
computation. -/
def recursionComputation (f : DeclName) (ctors : List (DeclName × List (Field Head)))
    (e : (i : Nat) → Tm Head i) (s d : Nat)
    (body : (k : DeclName) → (fields : List (Field Head)) →
      Tm Head (s + fields.length + d + (recPositions fields).length)) :
    RootComputation Head where
  step := RecursionStep f ctors e s d body
  rename := by
    intro n m ρ l r step
    exact step.rename ρ
  substitute := by
    intro n m σ l r step
    exact step.substitute σ

/-! ## Unions of root computations -/

/-- The union of two root computations. -/
def RootComputation.union (first second : RootComputation Head) : RootComputation Head where
  step := fun l r => first.step l r ∨ second.step l r
  rename := by
    intro n m ρ l r step
    exact step.elim (fun h => .inl (first.rename ρ h)) (fun h => .inr (second.rename ρ h))
  substitute := by
    intro n m σ l r step
    exact step.elim (fun h => .inl (first.substitute σ h)) (fun h => .inr (second.substitute σ h))

/-- The union of two deterministic root computations whose steps rewrite
applications of distinct constants is deterministic. -/
theorem RootComputation.union_deterministic {first second : RootComputation Head}
    {c c' : DeclName} (distinct : c ≠ c')
    (head : ∀ {n : Nat} {l r : Tm Head n}, first.step l r → ∃ args, l = appSpine (.const c) args)
    (head' : ∀ {n : Nat} {l r : Tm Head n}, second.step l r →
      ∃ args, l = appSpine (.const c') args)
    (deterministic : ∀ {n : Nat} {l r r' : Tm Head n}, first.step l r → first.step l r' → r' = r)
    (deterministic' : ∀ {n : Nat} {l r r' : Tm Head n}, second.step l r → second.step l r' →
      r' = r) {n : Nat} {l r r' : Tm Head n} (step : (RootComputation.union first second).step l r)
    (step' : (RootComputation.union first second).step l r') : r' = r := by
  rcases step with h | h <;> rcases step' with h' | h'
  · exact deterministic h h'
  · obtain ⟨args, rfl⟩ := head h
    obtain ⟨args', same⟩ := head' h'
    exact absurd (appSpine_const_injective same).1 distinct
  · obtain ⟨args, rfl⟩ := head' h
    obtain ⟨args', same⟩ := head h'
    exact absurd (appSpine_const_injective same).1 distinct.symm
  · exact deterministic' h h'

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
