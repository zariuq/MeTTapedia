import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.RecursionComputation

/-!
# Root computations of declared constants

Each declared constant with computation contributes a root computation whose
steps rewrite full applications of that constant: a definition by one equation
unfolds, the eliminator returns its method at reflexivity, a recursor and a
definition by structural recursion compute at constructor forms. The steps of
each occur at spines of its constant, with a canonical scrutinee where it has
one, and are deterministic.

Root computations of distinct constants combine into one. Its steps are those
of the listed computations; it is closed under renaming and substitution; its
steps occur at spines of the listed constants; and it is deterministic when
each listed computation is.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open TelescopeAbstraction (closeType applyClosed applyClosed_subst)

variable {Head : Type}

/-- The arguments of an application to a telescope determine the
substitution. -/
theorem telescopeArgs_inj {m : Nat} :
    ∀ {n : Nat} (Θ : Ctx Head n) {σ σ' : Sub Head n m},
      telescopeArgs Θ σ = telescopeArgs Θ σ' → σ = σ'
  | _, .nil, _, _, _ => funext fun i => Fin.elim0 i
  | _, .snoc Θ _, σ, σ', h => by
      obtain ⟨h₁, h₂⟩ := List.append_inj' h rfl
      have e₁ := telescopeArgs_inj Θ h₁
      have e₂ : σ 0 = σ' 0 := (List.cons.inj h₂).1
      calc σ = consSub (σ 0) (tailSub σ) := (consSub_eta σ).symm
        _ = consSub (σ' 0) (tailSub σ') := by rw [e₁, e₂]
        _ = σ' := consSub_eta σ'

/-- The steps of a root computation occur at spines of computing constants of
exact arity, whose inspected values have the shapes their skeleton requires. -/
def SpineShaped (roles : Roles Head) (computation : RootComputation Head) : Prop :=
  ∀ ⦃n : Nat⦄ ⦃t u : Tm Head n⦄, computation.step t u →
    ∃ c arity inspect args, roles c = .computes arity inspect ∧
      t = appSpine (.const c) args ∧ args.length = arity ∧ inspect.Accepts roles args

/-- The steps of a root computation rewrite applications of the constant `c`. -/
def HeadedBy (c : DeclName) (computation : RootComputation Head) : Prop :=
  ∀ ⦃n : Nat⦄ ⦃t u : Tm Head n⦄, computation.step t u → ∃ args, t = appSpine (.const c) args

/-- A deterministic root computation. -/
def Deterministic (computation : RootComputation Head) : Prop :=
  ∀ ⦃n : Nat⦄ ⦃t u u' : Tm Head n⦄, computation.step t u → computation.step t u' → u' = u

/-! ## Definitions by one equation -/

/-- The equation `f x₁ ⋯ x_k ⟶ rhs` of a definition by one equation. -/
def DefinitionStep (f : DeclName) {k : Nat} (Θ : Ctx Head k) (rhs : Tm Head k) {n : Nat}
    (l r : Tm Head n) : Prop :=
  ∃ σ : Sub Head k n, l = applyClosed Θ σ (.const f) ∧ r = Presentation.subst σ rhs

section Definition

variable {f : DeclName} {k : Nat} {Θ : Ctx Head k} {rhs : Tm Head k}

theorem DefinitionStep.substitute {n m : Nat} (τ : Sub Head n m) {l r : Tm Head n}
    (step : DefinitionStep f Θ rhs l r) :
    DefinitionStep f Θ rhs (Presentation.subst τ l) (Presentation.subst τ r) := by
  obtain ⟨σ, rfl, rfl⟩ := step
  refine ⟨fun i => Presentation.subst τ (σ i), ?_, ?_⟩
  · rw [applyClosed_subst]
    rfl
  · rw [subst_comp]

theorem DefinitionStep.rename {n m : Nat} (ρ : Ren n m) {l r : Tm Head n}
    (step : DefinitionStep f Θ rhs l r) :
    DefinitionStep f Θ rhs (Presentation.rename ρ l) (Presentation.rename ρ r) := by
  rw [← subst_renSub, ← subst_renSub]
  exact step.substitute (renSub ρ)

end Definition

/-- The equation of a definition by one equation, as a root computation. -/
def definitionComputation (f : DeclName) {k : Nat} (Θ : Ctx Head k) (rhs : Tm Head k) :
    RootComputation Head where
  step := DefinitionStep f Θ rhs
  rename := by
    intro n m ρ l r step
    exact step.rename ρ
  substitute := by
    intro n m σ l r step
    exact step.substitute σ

theorem definitionComputation_spine {roles : Roles Head} {f : DeclName} {k : Nat}
    {Θ : Ctx Head k} {rhs : Tm Head k} (role : roles f = .computes k .leaf) :
    SpineShaped roles (definitionComputation f Θ rhs) := by
  intro n t u step
  obtain ⟨σ, rfl, rfl⟩ := step
  exact ⟨f, k, .leaf, telescopeArgs Θ σ, role, applyClosed_eq_appSpine Θ σ _,
    telescopeArgs_length Θ σ, .leaf _⟩

theorem definitionComputation_headed {f : DeclName} {k : Nat} {Θ : Ctx Head k}
    {rhs : Tm Head k} : HeadedBy f (definitionComputation f Θ rhs) := by
  intro n t u step
  obtain ⟨σ, rfl, rfl⟩ := step
  exact ⟨_, applyClosed_eq_appSpine Θ σ _⟩

theorem definitionComputation_deterministic {f : DeclName} {k : Nat} {Θ : Ctx Head k}
    {rhs : Tm Head k} : Deterministic (definitionComputation f Θ rhs) := by
  intro n t u u' step step'
  obtain ⟨σ, rfl, rfl⟩ := step
  obtain ⟨σ', same, rfl⟩ := step'
  rw [applyClosed_eq_appSpine, applyClosed_eq_appSpine] at same
  rw [telescopeArgs_inj Θ (appSpine_const_injective same).2]

/-! ## The identity eliminator -/

/-- The eliminator's linear rule: at reflexivity, the method. -/
def eliminatorComputation (J : DeclName) : RootComputation Head where
  step := fun {n} l r => ∃ a₀ a₁ a₂ a₃ a₄ a₅ : Tm Head n,
    l = appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, .refl a₅] ∧ r = a₃
  rename := by
    intro n m ρ l r step
    obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, e₁, e₂⟩ := step
    subst e₁
    exact ⟨Presentation.rename ρ a₀, Presentation.rename ρ a₁, Presentation.rename ρ a₂,
      Presentation.rename ρ a₃, Presentation.rename ρ a₄, Presentation.rename ρ a₅,
      by rw [rename_appSpine]; rfl, by rw [e₂]⟩
  substitute := by
    intro n m σ l r step
    obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, e₁, e₂⟩ := step
    subst e₁
    exact ⟨Presentation.subst σ a₀, Presentation.subst σ a₁, Presentation.subst σ a₂,
      Presentation.subst σ a₃, Presentation.subst σ a₄, Presentation.subst σ a₅,
      by rw [subst_appSpine]; rfl, by rw [e₂]⟩

theorem eliminatorComputation_spine {roles : Roles Head} {J : DeclName}
    (role : roles J = .computes 6 (.split 5 .constructor fun _ => .leaf)) : SpineShaped roles (eliminatorComputation J) := by
  intro n t u step
  obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, e₁, _⟩ := step
  subst e₁
  exact ⟨J, 6, _, [a₀, a₁, a₂, a₃, a₄, .refl a₅], role, rfl, rfl,
    InspectTree.accepts_single.mpr ⟨_, rfl, .inl ⟨a₅, rfl⟩⟩⟩

theorem eliminatorComputation_headed {J : DeclName} :
    HeadedBy J (eliminatorComputation (Head := Head) J) := by
  intro n t u step
  obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, e₁, _⟩ := step
  exact ⟨_, e₁⟩

theorem eliminatorComputation_deterministic {J : DeclName} :
    Deterministic (eliminatorComputation (Head := Head) J) := by
  intro n t u u' step step'
  obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, e₁, e₂⟩ := step
  obtain ⟨b₀, b₁, b₂, b₃, b₄, b₅, e₃, e₄⟩ := step'
  rw [e₁] at e₃
  obtain ⟨_, args⟩ := appSpine_const_injective e₃
  simp only [List.cons.injEq] at args
  rw [e₂, e₄]
  exact args.2.2.2.1.symm

/-! ## Recursors and recursive definitions -/

theorem iotaComputation_headed {rec : DeclName} {ctors : List (DeclName × List (Field Head))} :
    HeadedBy rec (iotaComputation rec ctors) := by
  intro n t u step
  obtain ⟨p, ms, _, k, _, args, _, _, _, _, _, rfl, rfl⟩ := step
  exact ⟨_, rfl⟩

theorem recursionComputation_headed {f : DeclName} {ctors : List (DeclName × List (Field Head))}
    {e : (i : Nat) → Tm Head i} {s d : Nat}
    {body : (k : DeclName) → (fields : List (Field Head)) →
      Tm Head (s + fields.length + d + (recPositions fields).length)} :
    HeadedBy f (recursionComputation f ctors e s d body) := by
  intro n t u step
  obtain ⟨_, _, σ, _, _, _, rfl, rfl⟩ := step
  exact ⟨_, applyClosed_eq_appSpine _ _ _⟩

/-! ## Combining the computations of distinct constants -/

/-- The union of the root computations of the listed constants. -/
def RootComputation.unionAll : List (DeclName × RootComputation Head) → RootComputation Head
  | [] => RootComputation.empty
  | entry :: rest => RootComputation.union entry.2 (RootComputation.unionAll rest)

/-- A step of the union is a step of one of the listed computations. -/
theorem RootComputation.unionAll_step :
    ∀ {cs : List (DeclName × RootComputation Head)} {n : Nat} {t u : Tm Head n},
      (RootComputation.unionAll cs).step t u → ∃ entry ∈ cs, entry.2.step t u
  | [], _, _, _, step => nomatch step
  | entry :: rest, _, _, _, step => by
      rcases step with h | h
      · exact ⟨entry, List.mem_cons_self .., h⟩
      · obtain ⟨entry', mem, h'⟩ := RootComputation.unionAll_step h
        exact ⟨entry', List.mem_cons_of_mem _ mem, h'⟩

/-- A step of a listed computation is a step of the union. -/
theorem RootComputation.step_unionAll :
    ∀ {cs : List (DeclName × RootComputation Head)} {entry : DeclName × RootComputation Head},
      entry ∈ cs → ∀ {n : Nat} {t u : Tm Head n}, entry.2.step t u →
        (RootComputation.unionAll cs).step t u
  | [], _, mem, _, _, _, _ => nomatch mem
  | head :: rest, entry, mem, _, _, _, h => by
      rcases List.mem_cons.mp mem with rfl | mem'
      · exact .inl h
      · exact .inr (RootComputation.step_unionAll mem' h)

theorem RootComputation.unionAll_spine {roles : Roles Head}
    {cs : List (DeclName × RootComputation Head)}
    (spine : ∀ entry ∈ cs, SpineShaped roles entry.2) :
    SpineShaped roles (RootComputation.unionAll cs) := by
  intro n t u step
  obtain ⟨entry, mem, h⟩ := RootComputation.unionAll_step step
  exact spine entry mem h

/-- The union of deterministic computations of distinct constants is
deterministic. -/
theorem RootComputation.unionAll_deterministic {cs : List (DeclName × RootComputation Head)}
    (distinct : (cs.map Prod.fst).Nodup) (headed : ∀ entry ∈ cs, HeadedBy entry.1 entry.2)
    (deterministic : ∀ entry ∈ cs, Deterministic entry.2) :
    Deterministic (RootComputation.unionAll cs) := by
  induction cs with
  | nil =>
      intro n t u u' step
      cases step
  | cons entry rest ih =>
      intro n t u u' step step'
      rw [List.map_cons, List.nodup_cons] at distinct
      have headedHere : HeadedBy entry.1 entry.2 := headed entry (List.mem_cons_self ..)
      have restDeterministic := ih distinct.2
        (fun e mem => headed e (List.mem_cons_of_mem _ mem))
        (fun e mem => deterministic e (List.mem_cons_of_mem _ mem))
      have clash : ∀ {v v' : Tm Head n}, entry.2.step t v →
          (RootComputation.unionAll rest).step t v' → False := by
        intro v v' h h'
        obtain ⟨args, rfl⟩ := headedHere h
        obtain ⟨other, mem, h''⟩ := RootComputation.unionAll_step h'
        obtain ⟨args', same⟩ := headed other (List.mem_cons_of_mem _ mem) h''
        have names := (appSpine_const_injective same).1
        exact distinct.1 (names ▸ List.mem_map_of_mem mem)
      rcases step with h | h <;> rcases step' with h' | h'
      · exact deterministic entry (List.mem_cons_self ..) h h'
      · exact (clash h h').elim
      · exact (clash h' h).elim
      · exact restDeterministic h h'

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
