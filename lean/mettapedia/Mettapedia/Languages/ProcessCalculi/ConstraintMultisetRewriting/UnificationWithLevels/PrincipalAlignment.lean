import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Dispatch
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.SymbolicLevels

/-!
# Alignment with the core's principal answers

The core states principality as `Frames.Principal` and, relative to a set of terms, as
`Frames.FactorsOn` (`Step/Dispatch`). Its principal answer gives factorization without uniqueness.
Here the outcomes of exact runs are stated in exactly those terms.

* **Solved is `Principal`, and `FactorsOn` over all terms**: `exact_nil_iff_principal` and
  `exact_nil_iff_factorsOn_univ`.
* **Postponed still factors**: the answer of any exact run factors every solution of the store on
  every set of terms (`Exact.factorsOn`). It is principal as soon as the identity solves the
  residual (`Exact.principal_of_id`), and, for an epimorphic answer, exactly then
  (`Exact.principal_iff_of_epi`).
* **Initial is `Principal` with a unique factor** (`initialSolution_iff`). Where the core's
  `Principal.unique` gives mutual factorization of two principal answers, an initial one makes the
  round trip the identity (`InitialSolution.retract`).
* **The constrained version for level variables.** A residual made of level constraints only
  makes the answer `Principal` at every valuation that satisfies them, and leaves the store
  unsolvable at every other (`exact_levels_principal`, `exact_levels_unsolvable`). For the cross
  store, the store with its pending constraint `b ≤ a` goes along the answer `U : Sort b ⟶ Sort a`
  to the pending constraint alone, exactly, at every valuation satisfying the cumulativity
  constraint (`Cross.constrained_exact`). In the core's terms (`Cross.constrained_principal`): the
  answer `FactorsOn` the constrained store over all terms at every such valuation, it is
  `Principal` for it exactly where the pending constraint holds, it is then `Principal` for the cross
  store itself, and where the pending constraint fails no answer is `Principal` for the cross store.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

open Interface

universe uO uT uH

section General

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} {X : Frames Tm Hom}

/-- **Solved, in the core's relative terms.** -/
theorem exact_nil_iff_factorsOn_univ {a m : Obj} {S : EquationStore (Tm a)} {σ : Hom a m} :
    Exact X S σ [] ↔ X.Models σ S ∧ X.FactorsOn S σ Set.univ :=
  exact_nil_iff_principal.trans Frames.principal_iff_factorsOn_univ

/-- **The answer of any exact run factors every solution, on every set of terms.** -/
theorem Exact.factorsOn {a m : Obj} {S : EquationStore (Tm a)} {σ : Hom a m}
    {R : EquationStore (Tm m)} (exact : Exact X S σ R) (T : Set (Tm a)) : X.FactorsOn S σ T := by
  intro b f solved
  obtain ⟨g, fg, _⟩ := (exact b f).mp solved
  exact ⟨g, fun t _ => fg t⟩

/-- A postponed answer is principal as soon as the identity solves the residual. -/
theorem Exact.principal_of_id {a m : Obj} {S : EquationStore (Tm a)} {σ : Hom a m}
    {R : EquationStore (Tm m)} (exact : Exact X S σ R) (idSolves : X.Models (X.id m) R) :
    X.Principal S σ :=
  Frames.principal_iff_factorsOn_univ.mpr
    ⟨(exact m σ).mpr ⟨X.id m, agree_id_comp σ, idSolves⟩, exact.factorsOn Set.univ⟩

/-- For an epimorphic answer, exactly then. -/
theorem Exact.principal_iff_of_epi {a m : Obj} {S : EquationStore (Tm a)} {σ : Hom a m}
    {R : EquationStore (Tm m)} (exact : Exact X S σ R) (epi : EpiOnTerms X σ) :
    X.Principal S σ ↔ X.Models (X.id m) R := by
  constructor
  · intro principal
    obtain ⟨g, σg, solvedG⟩ := (exact m σ).mp principal.sound
    have agree : Agree X g (X.id m) := epi g (X.id m) fun t => by
      have h := σg t
      rw [X.act_comp] at h
      rw [X.act_id]
      exact (X.equivalence m).symm h
    exact (models_of_agree agree R).mp solvedG
  · exact exact.principal_of_id

/-- **Initial is `Principal` with a unique factor.** -/
theorem initialSolution_iff {a m : Obj} {S : EquationStore (Tm a)} {σ : Hom a m} :
    InitialSolution X S σ ↔ X.Principal S σ ∧
      ∀ (b : Obj) (f : Hom a b) (g h : Hom m b),
        Agree X f (X.comp g σ) → Agree X f (X.comp h σ) → Agree X g h :=
  ⟨fun initial => ⟨⟨initial.solves, initial.factor⟩, initial.unique⟩,
    fun ⟨principal, unique⟩ => ⟨principal.sound, principal.factors, unique⟩⟩

/-- **Mutual factorization becomes a retraction**: for an initial answer and any principal one,
the factors of the core's `Principal.unique` compose to the identity on the initial answer's
frame. -/
theorem InitialSolution.retract {a m₁ m₂ : Obj} {S : EquationStore (Tm a)} {one : Hom a m₁}
    {two : Hom a m₂} (initial : InitialSolution X S one) (second : X.Principal S two) :
    ∃ (r : Hom m₁ m₂) (r' : Hom m₂ m₁), Agree X two (X.comp r one) ∧
      Agree X one (X.comp r' two) ∧ Agree X (X.comp r' r) (X.id m₁) := by
  obtain ⟨r, h₁⟩ := initial.factor m₂ two second.sound
  obtain ⟨r', h₂⟩ := second.factors m₁ one initial.solves
  have h₂' : Agree X one (X.comp r' two) := h₂
  refine ⟨r, r', h₁, h₂', ?_⟩
  apply initial.unique m₁ one
  · exact (h₂'.trans (h₁.comp_left r')).trans (agree_assoc one r r')
  · exact agree_id_comp one

end General

/-! ## The constrained version for level variables -/

namespace CumulativeCodes

variable {v : Nat → Nat}

/-- **A residual of level constraints only**: the answer is principal wherever they hold. -/
theorem exact_levels_principal {Δ m : Ctx} {S : EquationStore (Term Δ)} {σ : Assign v Δ m}
    {C : LevelStore} (exact : Exact (frames v) S σ (withLevels [] C)) (sat : C.Satisfies v) :
    (frames v).Principal S σ :=
  exact.principal_of_id ((models_withLevels _ [] C).mpr ⟨Frames.models_nil _, sat⟩)

/-- **And the store is unsolvable wherever they fail.** -/
theorem exact_levels_unsolvable {Δ m : Ctx} {S : EquationStore (Term Δ)} {σ : Assign v Δ m}
    {C : LevelStore} (exact : Exact (frames v) S σ (withLevels [] C)) (unsat : ¬ C.Satisfies v) :
    ¬ (frames v).Solvable S := by
  rw [exact.solvable_iff]
  rintro ⟨Γ, g, solved⟩
  exact unsat ((models_withLevels g [] C).mp solved).2

namespace Cross

/-- **The constrained answer as an exact transition**: at every valuation satisfying the cumulativity
constraint, the cross store with its pending constraint goes along the answer to the pending
constraint alone. -/
theorem constrained_exact (v : Nat → Nat) (sat : levels.Satisfies v) :
    Exact (frames v) (withLevels store [pending]) (answer v (le_of_satisfies sat))
      (withLevels [] [pending]) := by
  intro Γ f
  rw [models_withLevels]
  constructor
  · rintro ⟨solved, pend⟩
    have ge : pending.Holds v := pend pending (List.mem_singleton_self _)
    obtain ⟨g, fg⟩ := (answer_principal (le_of_satisfies sat) ge).factors Γ f solved
    refine ⟨g, fg, ?_⟩
    rw [models_withLevels]
    exact ⟨Frames.models_nil _, pend⟩
  · rintro ⟨g, fg, solvedG⟩
    rw [models_withLevels] at solvedG
    exact ⟨(models_of_agree fg store).mpr (Frames.models_comp (answer_solves _) g), solvedG.2⟩

/-- **The constrained principal answer, in the core's terms.** At every valuation satisfying the
cumulativity constraint `a ≤ b`: the answer factors every solution of the store with its pending
constraint over all terms; it is principal for that store exactly where the pending constraint
`b ≤ a` holds; it is then principal for the cross store itself; and where the pending constraint
fails, no answer is principal for the cross store. -/
theorem constrained_principal (v : Nat → Nat) (sat : levels.Satisfies v) :
    (frames v).FactorsOn (withLevels store [pending]) (answer v (le_of_satisfies sat)) Set.univ ∧
      ((frames v).Principal (withLevels store [pending]) (answer v (le_of_satisfies sat)) ↔
        pending.Holds v) ∧
      (pending.Holds v → (frames v).Principal store (answer v (le_of_satisfies sat))) ∧
      (¬ pending.Holds v → ∀ (Γ : Ctx) (σ : Assign v ctx Γ), ¬ (frames v).Principal store σ) := by
  refine ⟨(constrained_exact v sat).factorsOn Set.univ, ⟨fun principal => ?_, fun ge => ?_⟩,
    fun ge => answer_principal _ ge, fun fails Γ σ principal => fails ?_⟩
  · exact ((models_withLevels _ store [pending]).mp principal.sound).2 pending
      (List.mem_singleton_self _)
  · refine exact_levels_principal (constrained_exact v sat) fun c hc => ?_
    rw [List.mem_singleton] at hc
    subst hc
    exact ge
  · exact (principal_iff (le_of_satisfies sat)).mp ⟨Γ, σ, principal⟩

end Cross

end CumulativeCodes

#print axioms exact_nil_iff_factorsOn_univ
#print axioms Exact.factorsOn
#print axioms Exact.principal_of_id
#print axioms Exact.principal_iff_of_epi
#print axioms initialSolution_iff
#print axioms InitialSolution.retract
#print axioms CumulativeCodes.exact_levels_principal
#print axioms CumulativeCodes.exact_levels_unsolvable
#print axioms CumulativeCodes.Cross.constrained_exact
#print axioms CumulativeCodes.Cross.constrained_principal

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
