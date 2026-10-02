import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.DefinitionConsequences

/-!
# The equations of a recursive definition as a root computation

The equations of a definition by structural recursion,
`f x₀ ⋯ x_{s-1} (k a₁ ⋯ aₐ) y₁ ⋯ y_d ⟶ rhs_k`, form a root computation closed
under renaming and substitution. Its steps occur at full applications of `f`
whose scrutinee is a constructor form, and they are deterministic when the
constructors have distinct names.

The left side of an equation is an instance of itself: matching the pattern of
a constructor at its own fields (`patternFields`) gives the identity
substitution (`matchSub_pattern`).

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

/-! ## The pattern at its own fields -/

/-- There is one field variable for each field. -/
theorem length_fieldVars (s : Nat) : ∀ a : Nat, (fieldVars (Head := Head) s a).length = a
  | 0 => rfl
  | a + 1 => by simp [fieldVars, length_fieldVars s a]

/-- The field variables, oldest first. -/
theorem fieldVars_getD (s : Nat) :
    ∀ (a l : Nat) (hl : l < a),
      (fieldVars (Head := Head) s a).getD l defaultTm = .var ⟨a - 1 - l, by omega⟩
  | 0, _, hl => absurd hl (Nat.not_lt_zero _)
  | a + 1, l, hl => by
      rw [List.getD_eq_getElem?_getD]
      simp only [fieldVars]
      rcases Nat.lt_or_ge l a with h | h
      · rw [List.getElem?_append_left (by simp [length_fieldVars s a, h]), List.getElem?_map]
        have ih := fieldVars_getD s a l h
        rw [List.getD_eq_getElem?_getD] at ih
        have hsome : (fieldVars (Head := Head) s a)[l]? = some (.var ⟨a - 1 - l, by omega⟩) := by
          rw [List.getElem?_eq_getElem (by simp [length_fieldVars s a, h])] at ih ⊢
          simp only [Option.getD_some] at ih
          rw [ih]
        rw [hsome]
        simp only [Option.map_some, Option.getD_some, Presentation.rename, wk, Tm.var.injEq]
        ext
        simp only [Fin.val_succ]
        omega
      · have hl' : l = a := by omega
        subst hl'
        rw [List.getElem?_append_right (by simp [length_fieldVars s l])]
        simp [length_fieldVars s l]

/-- An extended substitution below the extension reads the extension. -/
theorem extendSub_lt {n m : Nat} (ρ : Sub Head n m) (values : Nat → Tm Head m) :
    ∀ (b i : Nat) (hi : i < b), extendSub ρ values b ⟨i, by omega⟩ = values (b - 1 - i)
  | 0, _, hi => absurd hi (Nat.not_lt_zero _)
  | b + 1, 0, _ => by simp [extendSub]
  | b + 1, i + 1, hi => by
      show extendSub ρ values b ⟨i, by omega⟩ = _
      rw [extendSub_lt ρ values b i (by omega)]
      congr 1
      omega

/-- The fields of the pattern of a constructor, in the context of an equation. -/
def patternFields (s a : Nat) : (d : Nat) → List (Tm Head (s + a + d))
  | 0 => fieldVars s a
  | d + 1 => (patternFields s a d).map (Presentation.rename wk)

/-- The pattern of a constructor has one field term for each field. -/
theorem length_patternFields (s a : Nat) :
    ∀ d : Nat, (patternFields (Head := Head) s a d).length = a
  | 0 => length_fieldVars s a
  | d + 1 => by simp [patternFields, length_patternFields s a d]

/-- **The match of the pattern at its own fields is the identity.** -/
theorem matchSub_pattern (s a : Nat) (k : DeclName) :
    ∀ d : Nat, matchSub s a (patternFields (Head := Head) s a d) d (patternSub s a d k) = ids
  | 0 => by
      funext ι
      show extendSub (fun i : Fin s => (.var ⟨i.val + a, by omega⟩ : Tm Head (s + a)))
        (fun l => (fieldVars s a).getD l defaultTm) a ι = .var ι
      rcases Nat.lt_or_ge ι.val a with h | h
      · have e : ι = ⟨ι.val, by omega⟩ := rfl
        rw [e, extendSub_lt _ _ a ι.val h, fieldVars_getD s a _ (by omega)]
        congr 1
        ext
        simp only
        omega
      · have e : ι = ⟨(⟨ι.val - a, by omega⟩ : Fin s).val + a, by omega⟩ :=
          Fin.ext (by simp only; omega)
        rw [e, extendSub_ge]
  | d + 1 => by
      funext ι
      refine Fin.cases ?_ (fun j => ?_) ι
      · rfl
      · show matchSub s a (patternFields s a (d + 1)) d
            (fun i => Presentation.rename wk (patternSub s a d k i)) j = .var j.succ
        have hfun : (Presentation.subst (renSub wk) :
            Tm Head (s + a + d) → Tm Head (s + a + d + 1)) = Presentation.rename wk :=
          funext (subst_renSub wk)
        have nat := subst_matchSub (Head := Head) (s := s) (a := a) (renSub wk)
          (patternFields s a d) d (patternSub s a d k)
        rw [hfun, matchSub_pattern s a k d] at nat
        rw [show patternFields (Head := Head) s a (d + 1) =
          (patternFields s a d).map (Presentation.rename wk) from rfl, ← nat]
        rfl

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
