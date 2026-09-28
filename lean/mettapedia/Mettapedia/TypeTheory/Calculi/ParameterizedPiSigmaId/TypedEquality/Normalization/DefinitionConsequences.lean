import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.RecursiveDefinitions

/-!
# The equations of definitions preserve typing

For a rule package with the facts about the weak-head forms of its types, the
equation of a definition by one equation, and each equation of a definition by structural recursion,
preserve typing: in a typed application that the equation rewrites, the
right-hand side has the application's type. Together with the corresponding
results for the recursor and the identity eliminator, these are the
root-preservation obligations of the constants of the admissible class.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open TelescopeAbstraction (closeType applyClosed applyClosed_subst liftClosed_zero)

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

theorem forall₂_getD {α β : Type} {R : α → β → Prop} (da : α) (db : β) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ i, i < l₁.length →
      R (l₁.getD i da) (l₂.getD i db)
  | [], [], .nil, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _ :: _, .cons hab _, 0, _ => hab
  | _ :: _, _ :: _, .cons _ rest, i + 1, h =>
      forall₂_getD da db rest i (Nat.lt_of_succ_lt_succ h)

/-- The match does not read the scrutinee. -/
theorem matchSub_replaceScrut {m s a : Nat} (as : List (Tm Head m)) (x : Tm Head m) :
    ∀ (d : Nat) (σ : Sub Head (s + 1 + d) m),
      matchSub s a as d (replaceScrut s x d σ) = matchSub s a as d σ
  | 0, _ => rfl
  | d + 1, σ => by
      show consSub (σ 0) (matchSub s a as d (replaceScrut s x d (tailSub σ))) =
        consSub (σ 0) (matchSub s a as d (tailSub σ))
      rw [matchSub_replaceScrut as x d (tailSub σ)]

/-! ## Typed substitutions of pattern contexts -/

section Typings

variable {R : Rules Head}

theorem SubstMor.prefixSub (e : (i : Nat) → Tm Head i) {s m : Nat} {Δ : Ctx Head m} :
    ∀ (d : Nat) {σ : Sub Head (s + 1 + d) m}, SubstMor R (ofEntries e (s + 1 + d)) Δ σ →
      SubstMor R (ofEntries e s) Δ (prefixSub s d σ)
  | 0, _, typed => SubstMor.tail typed
  | d + 1, _, typed => SubstMor.prefixSub e d (SubstMor.tail typed)

theorem SubstMor.scrut (e : (i : Nat) → Tm Head i) {s m : Nat} {Δ : Ctx Head m} :
    ∀ (d : Nat) {σ : Sub Head (s + 1 + d) m}, SubstMor R (ofEntries e (s + 1 + d)) Δ σ →
      Typed R Δ (scrutOf s d σ) (Presentation.subst (Normalization.prefixSub s d σ) (e s))
  | 0, _, typed => SubstMor.head typed
  | d + 1, _, typed => SubstMor.scrut e d (SubstMor.tail typed)

theorem SubstMor.fields {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} (T : DeclName)
    (fields : List (Field Head)) {as : List (Tm Head m)}
    (typed : ∀ l, l < fields.length →
      Typed R Δ (as.getD l defaultTm) (liftClosed ((fields.getD l .recursive).type T)))
    {ρ : Sub Head n m} (base : SubstMor R Γ Δ ρ) :
    ∀ (b : Nat), b ≤ fields.length →
      SubstMor R (extendEntries Γ (fun l => liftClosed ((fields.getD l .recursive).type T)) b) Δ
        (extendSub ρ (fun l => as.getD l defaultTm) b)
  | 0, _ => base
  | b + 1, hb => by
      refine SubstMor.cons (SubstMor.fields T fields typed base b (by omega)) ?_
      rw [subst_liftClosed]
      exact typed b (by omega)

theorem SubstMor.hyps {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} (X : Nat → Tm Head n)
    {τ : Sub Head n m} {vals : Nat → Tm Head m} (base : SubstMor R Γ Δ τ) :
    ∀ (b : Nat), (∀ j, j < b → Typed R Δ (vals j) (Presentation.subst τ (X j))) →
      SubstMor R (extendEntries Γ (fun j => Presentation.rename (wkN j) (X j)) b) Δ
        (extendSub τ vals b)
  | 0, _ => base
  | b + 1, typed => by
      refine SubstMor.cons (SubstMor.hyps X base b (fun j hj => typed j (by omega))) ?_
      rw [subst_extendSub_wkN]
      exact typed b (by omega)

/-- The match of a typed constructor form is a typed substitution of the
pattern context. -/
theorem SubstMor.pattern (e : (i : Nat) → Tm Head i) {s m : Nat} {Δ : Ctx Head m}
    {T k : DeclName} (fields : List (Field Head)) {as : List (Tm Head m)}
    (typed : ∀ l, l < fields.length →
      Typed R Δ (as.getD l defaultTm) (liftClosed ((fields.getD l .recursive).type T)))
    (length : as.length = fields.length) :
    ∀ (d : Nat) {τ : Sub Head (s + 1 + d) m}, SubstMor R (ofEntries e (s + 1 + d)) Δ τ →
      scrutOf s d τ = appSpine (.const k) as →
      SubstMor R (patternCtx T k e s d fields) Δ (matchSub s fields.length as d τ)
  | 0, _, base, _ =>
      SubstMor.fields T fields typed (SubstMor.prefixSub e 0 base) fields.length (Nat.le_refl _)
  | d + 1, τ, base, h => by
      refine SubstMor.cons (SubstMor.pattern e fields typed length d (SubstMor.tail base) h) ?_
      have entry : ∀ σ : Sub Head (s + 1 + d) m, scrutOf s d σ = appSpine (.const k) as →
          Presentation.subst (matchSub s fields.length as d σ)
            (Presentation.subst (liftSubN (patSub s fields.length k) d) (e (s + 1 + d))) =
          Presentation.subst σ (e (s + 1 + d)) := by
        intro σ hσ
        rw [subst_comp]
        have key : (fun ι => Presentation.subst (matchSub s fields.length as d σ)
              (liftSubN (patSub s fields.length k) d ι)) =
            replaceScrut s (appSpine (.const k) as) d σ :=
          funext fun ι => subst_matchSub_patternSub k as length d σ ι
        rw [key, ← hσ, replaceScrut_self]
      rw [entry _ h]
      exact SubstMor.head base

end Typings

/-! ## Preservation -/

section Preservation

variable {S₀ : Setting Head L} (facts : FormFacts S.R S.roles)
include facts

/-- The equation of a definition by one equation preserves typing, in every
package containing the declaring one. -/
theorem DeclaresDefinition.rule_preserves {R₀ : Rules Head} {f : DeclName} {k : Nat}
    {Θ : Ctx Head k} {C rhs : Tm Head k} (decl : DeclaresDefinition S₀ R₀ f Θ C rhs)
    (sub : RulesSub S₀.R S.R) {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    (σ : Sub Head k n) {A : Tm Head n} (typing : Typed S.R Γ (applyClosed Θ σ (.const f)) A) :
    Typed S.R Γ (Presentation.subst σ rhs) A := by
  obtain ⟨mor, _, le⟩ := Typed.telescope_inv facts formed Θ C (sub.constantType decl.declared)
    typing
  exact Typed.subsume (Typed.substitute (Derivable.mono (decl.sub₀.trans sub) decl.body) mor) le

variable {R₀ : Rules Head} {f T : DeclName} {ctors : List (DeclName × List (Field Head))}
  {e : (i : Nat) → Tm Head i} {s d : Nat} {C : Tm Head (s + 1 + d)}
  {body : (k : DeclName) → (fields : List (Field Head)) →
    Tm Head (s + fields.length + d + (recPositions fields).length)}
  (decl : DeclaresRecursion S₀ R₀ f T ctors e s d C body)
  {R₀' R₁' R₂' : Rules Head} {u : Head} {rec : DeclName} {v : Head}
  (ind : DeclaresInductive S₀ R₀' R₁' R₂' T u ctors rec v) (sub : RulesSub S₀.R S.R)
include decl ind sub

/-- An equation of a definition by structural recursion preserves typing, in
every package containing the declaring one: in a typed application to a
constructor form, the right-hand side, with the recursive calls substituted, has
the application's type. -/
theorem DeclaresRecursion.rule_preserves {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {k : DeclName} {fields : List (Field Head)} (mem : (k, fields) ∈ ctors)
    (σ : Sub Head (s + 1 + d) n) (as : List (Tm Head n)) (has : as.length = fields.length)
    {A : Tm Head n}
    (typing : Typed S.R Γ (applyClosed (ofEntries e (s + 1 + d))
      (replaceScrut s (appSpine (.const k) as) d σ) (.const f)) A) :
    Typed S.R Γ (Presentation.subst (matchSub s fields.length as d σ)
      (Presentation.subst (hypSub f e s d fields) (body k fields))) A := by
  obtain ⟨mor, _, le⟩ := Typed.telescope_inv facts formed (ofEntries e (s + 1 + d)) C
    (sub.constantType decl.declared) typing
  /- The scrutinee is the constructor form, of the inductive type. -/
  have tScrut : Typed S.R Γ (appSpine (.const k) as) (.const T) := by
    have h := SubstMor.scrut e d mor
    rw [scrutOf_replaceScrut, prefixSub_replaceScrut, subst_scrutinee e decl.scrutinee] at h
    exact h
  /- The arguments for the fields are typed at the field types. -/
  have argsK : telescopeArgs (ofEntries (ctorEntry T fields) fields.length)
      (argsSub fields.length as) = as :=
    telescopeArgs_argsSub _ _ _ has
  have typingK : Typed S.R Γ (applyClosed (ctorTele T fields) (argsSub fields.length as)
      (.const k)) (.const T) := by
    rw [applyClosed_eq_appSpine]
    show Typed S.R Γ (appSpine (.const k) (telescopeArgs (ofEntries (ctorEntry T fields)
      fields.length) (argsSub fields.length as))) (.const T)
    rw [argsK]
    exact tScrut
  obtain ⟨morK, _, _⟩ := Typed.telescope_inv facts formed (ctorTele T fields)
    (.const T) (sub.constantType (ind.ctorDeclared mem)) typingK
  have fieldsTyped := fields_of_substMor (R := S.R) fields.length (Nat.le_refl _) morK
  rw [List.take_length, argsK] at fieldsTyped
  have fieldTyped : ∀ l, l < fields.length →
      Typed S.R Γ (as.getD l defaultTm) (liftClosed ((fields.getD l .recursive).type T)) :=
    fun l hl => forall₂_getD .recursive defaultTm fieldsTyped l hl
  /- The variables of the equation's context. -/
  have morP := SubstMor.pattern e fields fieldTyped has d mor (scrutOf_replaceScrut _ d σ)
  rw [matchSub_replaceScrut] at morP
  have morPrefix : SubstMor S.R (ofEntries e s) Γ (prefixSub s d σ) := by
    have h := SubstMor.prefixSub e d mor
    rwa [prefixSub_replaceScrut] at h
  /- The recursive calls, at the types of the hypotheses. -/
  have typingF : Typed S.R Γ (.const f)
      (liftClosed (closeType (ofEntries e (s + 1)) (piRange e (s + 1) d C))) := by
    rw [← closeType_ofEntries_add]
    exact Derivable.mono sub decl.typing
  have calls : ∀ j, j < (recPositions fields).length →
      Typed S.R Γ (Presentation.subst (matchSub s fields.length as d σ)
          (recCall f e s fields.length d ((recPositions fields).getD j 0)))
        (Presentation.subst (matchSub s fields.length as d σ)
          (recCallType e s fields.length d ((recPositions fields).getD j 0) C)) := by
    intro j hj
    obtain ⟨hl, hrec⟩ := recPositions_spec fields j hj
    rw [getD_of_lt 0 hj, subst_recCall f e _ σ hl, subst_recCallType e _ σ C hl]
    have ha := fieldTyped _ hl
    rw [hrec] at ha
    have morσ₀ : SubstMor S.R (ofEntries e (s + 1)) Γ
        (consSub (as.getD (recPositions fields)[j] defaultTm) (prefixSub s d σ)) := by
      refine SubstMor.cons (A := e s) morPrefix ?_
      rw [subst_scrutinee e decl.scrutinee]
      exact ha
    exact Typed.telescope_apply morσ₀ typingF
  have morH := SubstMor.hyps
    (fun j => recCallType e s fields.length d ((recPositions fields).getD j 0) C) morP
    (recPositions fields).length calls
  /- The right-hand side, at the type of the application. -/
  have result := Typed.substitute (Derivable.mono (decl.sub₀.trans sub) (decl.bodyTyped mem)) morH
  have tyEq : Presentation.subst (extendSub (matchSub s fields.length as d σ)
        (fun j => Presentation.subst (matchSub s fields.length as d σ)
          (recCall f e s fields.length d ((recPositions fields).getD j 0)))
        (recPositions fields).length)
      (Presentation.rename (wkN (recPositions fields).length)
        (Presentation.subst (patternSub s fields.length d k) C)) =
      Presentation.subst (replaceScrut s (appSpine (.const k) as) d σ) C := by
    rw [subst_extendSub_wkN, subst_comp]
    exact congrArg (fun τ => Presentation.subst τ C)
      (funext fun ι => subst_matchSub_patternSub k as has d σ ι)
  rw [tyEq] at result
  rw [subst_hypSub]
  exact Typed.subsume result le

end Preservation

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
