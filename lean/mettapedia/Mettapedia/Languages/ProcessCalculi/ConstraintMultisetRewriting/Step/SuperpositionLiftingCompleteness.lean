import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SuperpositionLiftingOverlap
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SuperpositionLiftingRedundancy

/-!
# Refutational completeness of non-ground superposition

## Non-ground inferences

`NInference ord side main μ concl`: superposition (positive or negative, by the sign of the main
literal), equality resolution and equality factoring, each with its told unification, a most general
unifier `μ`, and its side conditions at `μ`. These are the inferences the firings of
`SuperpositionFiring` make. The premises of an inference **from a set `N`** are reorientations of
copies of clauses of `N` by injective renamings, the two premises of a superposition renamed apart
(`Copies`). Renaming apart needs two injective renamings with disjoint images (`VariableSupply`); the
natural numbers have them (`variableSupply_nat`).

## Saturation lifts to the ground instances

`NSaturated ord N`: every inference from `N` is redundant (`RedundantNInference`). By the lifting
lemma and the variable-overlap redundancy (`lift_binary`, `lift_unary`), every ground inference among
ground instances of `N` is redundant (`ground_redundant`). Therefore:

* **(a)** the ground instances of a saturated set are saturated (`NSaturated.saturated`), and a
  saturated set without the empty clause has a model of all its ground instances
  (`NSaturated.satisfiable`), through `satisfiable` (the candidate model);
* **(b)** a fair derivation (`NDerivation`, `NFair`: every inference between copies of persistent
  clauses eventually becomes redundant, for instance by being made, `RedundantNInference.of_mem`)
  from a start whose ground instances are unsatisfiable derives the empty clause
  (`NDerivation.complete`). The argument goes through the irredundant ground instances of all sets of
  the derivation: each comes from a persistent clause (`NDerivation.persists`), and they form a
  saturated set whose candidate model satisfies every ground instance that ever appeared. Every
  derived clause follows from the start (`NDerivation.models`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition

open Mettapedia.Logic.LP
open Resolution (A)

variable {sig : LPSignature}

/-! ## Non-ground inferences, copies and renaming apart -/

section Inferences

/-- **The non-ground inferences** with their most general unifier: `NInference ord side main μ concl`. -/
inductive NInference (ord : StableOrder sig) :
    Option (NClause sig) → NClause sig → Subst sig → NClause sig → Prop
  /-- Superposition of `l ≈ r ∨ D'` into `L ∨ C'` at `L.lhs = c[u]`. -/
  | sup (D' C' : NClause sig) (L : NLit sig) (c : FirstOrderRewriting.Context sig) (u l r : Term sig)
      (μ : Subst sig) (atPosition : L.lhs = c.fill u) (principal : (A sig).Principal [(l, u)] μ)
      (conditions : supConditions ord u l r D' L C' μ) :
      NInference ord (some (posLit l r :: D')) (L :: C') μ ((supConclusion c r D' L C').subst μ)
  /-- Equality resolution on `L ∨ C'`. -/
  | eqRes (L : NLit sig) (C' : NClause sig) (μ : Subst sig)
      (principal : (A sig).Principal [(L.lhs, L.rhs)] μ) (conditions : eqResConditions ord L C' μ) :
      NInference ord none (L :: C') μ (C'.subst μ)
  /-- Equality factoring on `L ∨ L' ∨ C'`. -/
  | eqFact (L L' : NLit sig) (C' : NClause sig) (μ : Subst sig)
      (principal : (A sig).Principal [(L.lhs, L'.lhs)] μ) (conditions : eqFactConditions ord L L' C' μ) :
      NInference ord none (L :: L' :: C') μ ((eqFactConclusion L L' C').subst μ)

/-- **A copy of a clause** by a renaming of its variables. -/
def NClause.rename (π : sig.vars → sig.vars) (C : NClause sig) : NClause sig :=
  C.subst fun v => .var (π v)

theorem NClause.rename_id (C : NClause sig) : C.rename id = C :=
  FixesClause.subst_eq fun L _ => ⟨Subst.applyTerm_id L.lhs, Subst.applyTerm_id L.rhs⟩

/-- **The premises are copies of clauses of `N`**: reorientations of renamings of clauses of `N` by
injective renamings, the side premise renamed apart from the main one. -/
def Copies (N : Set (NClause sig)) (side : Option (NClause sig)) (main : NClause sig) : Prop :=
  ∃ C ∈ N, ∃ π : sig.vars → sig.vars, Function.Injective π ∧ Reorient main (C.rename π) ∧
    ∀ D' ∈ side, ∃ D ∈ N, ∃ π' : sig.vars → sig.vars, Function.Injective π' ∧ (∀ v w, π' v ≠ π w) ∧
      Reorient D' (D.rename π')

/-- **Enough variables to rename two clauses apart**: two injective renamings with disjoint images. -/
def VariableSupply (sig : LPSignature) : Prop :=
  ∃ π₁ π₂ : sig.vars → sig.vars, Function.Injective π₁ ∧ Function.Injective π₂ ∧ ∀ v w, π₁ v ≠ π₂ w

/-- Variables in bijection with the natural numbers are enough: even and odd. -/
theorem variableSupply_of_equiv (e : sig.vars ≃ ℕ) : VariableSupply sig :=
  ⟨fun v => e.symm (2 * e v), fun v => e.symm (2 * e v + 1),
    fun a b same => e.injective (by have h := e.symm.injective same; omega),
    fun a b same => e.injective (by have h := e.symm.injective same; omega),
    fun v w same => by have h := e.symm.injective same; omega⟩

/-- **Standardizing apart**: groundings of two copies renamed apart are one grounding. -/
theorem standardize {π₁ π₂ : sig.vars → sig.vars} (inj₁ : Function.Injective π₁)
    (inj₂ : Function.Injective π₂) (apart : ∀ v w, π₁ v ≠ π₂ w) (g₁ g₂ : Grounding sig) :
    ∃ θ : Grounding sig, (∀ v, θ (π₁ v) = g₁ v) ∧ ∀ v, θ (π₂ v) = g₂ v := by
  classical
  refine ⟨fun w => if h : ∃ v, π₁ v = w then g₁ h.choose else
    if h' : ∃ v, π₂ v = w then g₂ h'.choose else g₁ w, fun v => ?_, fun v => ?_⟩
  · have h : ∃ v', π₁ v' = π₁ v := ⟨v, rfl⟩
    show (if h : ∃ v', π₁ v' = π₁ v then g₁ h.choose else
      if h' : ∃ v', π₂ v' = π₁ v then g₂ h'.choose else g₁ (π₁ v)) = g₁ v
    rw [dif_pos h]
    exact congrArg g₁ (inj₁ h.choose_spec)
  · have h : ¬ ∃ v', π₁ v' = π₂ v := fun ⟨v', e⟩ => apart v' v e
    have h' : ∃ v', π₂ v' = π₂ v := ⟨v, rfl⟩
    show (if h : ∃ v', π₁ v' = π₂ v then g₁ h.choose else
      if h' : ∃ v', π₂ v' = π₂ v then g₂ h'.choose else g₁ (π₂ v)) = g₂ v
    rw [dif_neg h, dif_pos h']
    exact congrArg g₂ (inj₂ h'.choose_spec)

end Inferences

/-! ## Every ground inference among instances is redundant when every inference lifts redundantly -/

section Saturation

variable [LinearOrder (GroundTerm sig)]

theorem NClause.ground_rename (θ : Grounding sig) (π : sig.vars → sig.vars) (C : NClause sig) :
    NClause.ground θ (C.rename π) = NClause.ground (fun v => θ (π v)) C :=
  NClause.ground_subst θ (fun v => .var (π v)) C

/-- **Saturation up to redundancy**: every inference from copies of clauses of `N` is redundant with
respect to the ground instances of `N`. -/
def NSaturated (ord : StableOrder sig) (N : Set (NClause sig)) : Prop :=
  ∀ side main μ concl, NInference ord side main μ concl → Copies N side main →
    RedundantNInference (groundInstances N) side main μ concl

variable [GroundSimplification sig] [DecidableEq sig.vars] [DecidableEq sig.constants]
  [DecidableEq sig.functionSymbols]

/-- **Lifted redundancy gives ground redundancy.** If every inference from copies of clauses of `P` is
redundant with respect to `T`, and `T` holds the ground instances of `P`, then every ground inference
among ground instances of `P` is redundant with respect to `T`: it lifts, or it is a superposition at
or below a variable. -/
theorem ground_redundant (ord : GroundedOrder sig) (supply : VariableSupply sig) {P : Set (NClause sig)}
    {T : Set (Clause (GroundTerm sig))} (instancesIn : groundInstances P ⊆ T)
    (lifted : ∀ side main μ concl, NInference ord.toStableOrder side main μ concl → Copies P side main →
      RedundantNInference T side main μ concl)
    {side : Option (Clause (GroundTerm sig))} {main concl : Clause (GroundTerm sig)}
    (inference : Inference side main concl) (sides : ∀ D ∈ side, D ∈ groundInstances P)
    (mainIn : main ∈ groundInstances P) : RedundantInference T main concl := by
  obtain ⟨C, CP, gC, rfl⟩ := mainIn
  cases side with
  | none =>
      rcases lift_unary ord gC inference rfl rfl with lifts | lifts
      · refine lifts.elim fun lift => ?_
        have ι := NInference.eqRes lift.L lift.C' lift.μ lift.principal lift.conditions
        have copies : Copies P none (lift.L :: lift.C') :=
          ⟨C, CP, id, Function.injective_id, by rw [NClause.rename_id]; exact lift.main_reorient,
            fun _ h => by cases h⟩
        have mainSame : NClause.ground lift.ν (NClause.subst lift.μ (lift.L :: lift.C')) = NClause.ground gC C := by
          rw [NClause.ground_subst, lift.factors]
          exact lift.main_reorient.ground gC
        have conclSame : NClause.ground lift.ν (lift.C'.subst lift.μ) = concl := by
          rw [NClause.ground_subst, lift.factors]
          exact lift.conclusion
        have red := lifted _ _ _ _ ι copies lift.ν (by rw [mainSame, conclSame]; exact inference)
        rwa [mainSame, conclSame] at red
      · refine lifts.elim fun lift => ?_
        have ι := NInference.eqFact lift.L lift.L' lift.C' lift.μ lift.principal lift.conditions
        have copies : Copies P none (lift.L :: lift.L' :: lift.C') :=
          ⟨C, CP, id, Function.injective_id, by rw [NClause.rename_id]; exact lift.main_reorient,
            fun _ h => by cases h⟩
        have mainSame : NClause.ground lift.ν (NClause.subst lift.μ (lift.L :: lift.L' :: lift.C')) =
            NClause.ground gC C := by
          rw [NClause.ground_subst, lift.factors]
          exact lift.main_reorient.ground gC
        have conclSame : NClause.ground lift.ν ((eqFactConclusion lift.L lift.L' lift.C').subst lift.μ) =
            concl := by
          rw [NClause.ground_subst, lift.factors]
          exact lift.conclusion
        have red := lifted _ _ _ _ ι copies lift.ν (by rw [mainSame, conclSame]; exact inference)
        rwa [mainSame, conclSame] at red
  | some Dg =>
      obtain ⟨D, DP, gD, rfl⟩ := sides _ rfl
      obtain ⟨π₁, π₂, inj₁, inj₂, apart⟩ := supply
      obtain ⟨θ, onD, onC⟩ := standardize inj₁ inj₂ apart gD gC
      have groundD : NClause.ground θ (D.rename π₁) = NClause.ground gD D := by
        rw [NClause.ground_rename]
        exact congrArg (NClause.ground · D) (funext onD)
      have groundC : NClause.ground θ (C.rename π₂) = NClause.ground gC C := by
        rw [NClause.ground_rename]
        exact congrArg (NClause.ground · C) (funext onC)
      rcases lift_binary ord θ inference (by rw [groundD]) groundC.symm with lifts | overlap
      · refine lifts.elim fun lift => ?_
        have ι := NInference.sup lift.D' lift.C' lift.L lift.c lift.u lift.l lift.r lift.μ lift.at_position
          lift.principal lift.conditions
        have copies : Copies P (some (posLit lift.l lift.r :: lift.D')) (lift.L :: lift.C') :=
          ⟨C, CP, π₂, inj₂, lift.main_reorient, fun X member => by
            rw [Option.mem_def, Option.some.injEq] at member
            subst member
            exact ⟨D, DP, π₁, inj₁, apart, lift.side_reorient⟩⟩
        have sideSame : NClause.ground lift.ν (NClause.subst lift.μ (posLit lift.l lift.r :: lift.D')) =
            NClause.ground gD D := by
          rw [NClause.ground_subst, lift.factors, lift.side_reorient.ground θ, groundD]
        have mainSame : NClause.ground lift.ν (NClause.subst lift.μ (lift.L :: lift.C')) = NClause.ground gC C := by
          rw [NClause.ground_subst, lift.factors, lift.main_reorient.ground θ, groundC]
        have conclSame : NClause.ground lift.ν
            ((supConclusion lift.c lift.r lift.D' lift.L lift.C').subst lift.μ) = concl := by
          rw [NClause.ground_subst, lift.factors]
          exact lift.conclusion
        have red := lifted _ _ _ _ ι copies lift.ν (by
          show Inference (some (NClause.ground lift.ν (NClause.subst lift.μ (posLit lift.l lift.r :: lift.D')))) _ _
          rw [sideSame, mainSame, conclSame]
          exact inference)
        rwa [mainSame, conclSame] at red
      · have red := overlap T (by rw [groundD]; exact instancesIn ⟨D, DP, gD, rfl⟩)
          (fun θ' => by
            rw [NClause.ground_rename]
            exact instancesIn ⟨C, CP, _, rfl⟩)
        rwa [groundC] at red

/-- **(a) The ground instances of a saturated set are saturated.** -/
theorem NSaturated.saturated (ord : GroundedOrder sig) (supply : VariableSupply sig)
    {N : Set (NClause sig)} (saturated : NSaturated ord.toStableOrder N) : Saturated (groundInstances N) :=
  fun _ _ _ inference sides mainIn =>
    ground_redundant ord supply (fun _ member => member) saturated inference sides mainIn

variable [WellFoundedLT (GroundTerm sig)]

/-- **(a) A saturated set without the empty clause has a model of all its ground instances.** -/
theorem NSaturated.satisfiable (ord : GroundedOrder sig) (supply : VariableSupply sig)
    {N : Set (NClause sig)} (saturated : NSaturated ord.toStableOrder N) (noEmpty : [] ∉ N) :
    ∃ I : Congruence sig, ∀ C ∈ N, ∀ θ : Grounding sig, Models I.rel (NClause.ground θ C) := by
  obtain ⟨I, holds⟩ := Superposition.satisfiable (saturated.saturated ord supply)
    fun ⟨C, member, θ, zero⟩ => noEmpty ((NClause.ground_eq_zero_iff θ C).mp zero ▸ member)
  exact ⟨I, fun C member θ => holds _ ⟨C, member, θ, rfl⟩⟩

end Saturation

/-! ## Fair derivations -/

section Derivations

variable [LinearOrder (GroundTerm sig)]

/-- **A non-ground derivation**: every ground instance of a new clause follows from the previous set,
and every removed clause is redundant with respect to the next set. -/
structure NDerivation (N : ℕ → Set (NClause sig)) : Prop where
  sound : ∀ i, ∀ C ∈ N (i + 1), C ∉ N i → ∀ θ : Grounding sig,
    Entails (groundInstances (N i)) (NClause.ground θ C)
  removes : ∀ i, ∀ C ∈ N i, C ∉ N (i + 1) → NRedundant (N (i + 1)) C

/-- **The persistent clauses.** -/
def nlimit (N : ℕ → Set (NClause sig)) : Set (NClause sig) := {C | ∃ i, ∀ j, i ≤ j → C ∈ N j}

/-- The ground instances of every set of the derivation. -/
def nunion (N : ℕ → Set (NClause sig)) : Set (Clause (GroundTerm sig)) :=
  {G | ∃ i, G ∈ groundInstances (N i)}

/-- **Fairness**: every inference between copies of persistent clauses eventually becomes redundant. -/
def NFair (ord : StableOrder sig) (N : ℕ → Set (NClause sig)) : Prop :=
  ∀ side main μ concl, NInference ord side main μ concl → Copies (nlimit N) side main →
    ∃ i, RedundantNInference (groundInstances (N i)) side main μ concl

variable {N : ℕ → Set (NClause sig)}

/-- **Every derived clause follows from the start.** -/
theorem NDerivation.models (derivation : NDerivation N) (I : Congruence sig)
    (initial : ∀ C ∈ N 0, ∀ θ : Grounding sig, Models I.rel (NClause.ground θ C)) :
    ∀ i, ∀ C ∈ N i, ∀ θ : Grounding sig, Models I.rel (NClause.ground θ C)
  | 0 => initial
  | i + 1 => fun C member θ => by
      by_cases old : C ∈ N i
      · exact derivation.models I initial i C old θ
      · refine derivation.sound i C member old θ I fun G inside => ?_
        obtain ⟨D, inD, θ', same⟩ := inside
        exact same ▸ derivation.models I initial i D inD θ'

/-- **A clause with an irredundant instance persists.** -/
theorem NDerivation.persists (derivation : NDerivation N) {i : ℕ} {C : NClause sig} (member : C ∈ N i)
    {θ : Grounding sig} (irredundant : ¬ Redundant (nunion N) (NClause.ground θ C)) : C ∈ nlimit N := by
  refine ⟨i, fun j le => ?_⟩
  induction le with
  | refl => exact member
  | @step m _ ih =>
      by_contra gone
      exact irredundant (Redundant.mono (fun G inside => (⟨m + 1, inside⟩ : G ∈ nunion N))
        (derivation.removes m C ih gone θ))

variable [GroundSimplification sig] [WellFoundedLT (GroundTerm sig)] [DecidableEq sig.vars]
  [DecidableEq sig.constants] [DecidableEq sig.functionSymbols]

/-- **(b) Refutational completeness of non-ground superposition**: a fair derivation from a start whose
ground instances are unsatisfiable derives the empty clause. -/
theorem NDerivation.complete (ord : GroundedOrder sig) (supply : VariableSupply sig)
    (derivation : NDerivation N) (fair : NFair ord.toStableOrder N)
    (unsatisfiable : ¬ ∃ I : Congruence sig, ∀ C ∈ N 0, ∀ θ : Grounding sig, Models I.rel (NClause.ground θ C)) :
    ∃ i, [] ∈ N i := by
  by_contra never
  push Not at never
  have persistent : ∀ G ∈ irredundant (nunion N), G ∈ groundInstances (nlimit N) := by
    rintro G ⟨⟨i, C, member, θ, rfl⟩, notRedundant⟩
    exact ⟨C, derivation.persists member notRedundant, θ, rfl⟩
  have saturated : Saturated (irredundant (nunion N)) := by
    intro side main concl inference sides mainIn
    have redundant : RedundantInference (nunion N) main concl :=
      ground_redundant ord supply (P := nlimit N) (T := nunion N)
        (fun G inside => by
          obtain ⟨C, ⟨i, stays⟩, θ, same⟩ := inside
          exact (⟨i, C, stays i le_rfl, θ, same⟩ : G ∈ nunion N))
        (fun side main μ concl ι copies => by
          obtain ⟨i, redundant⟩ := fair side main μ concl ι copies
          exact RedundantNInference.mono (fun G inside => (⟨i, inside⟩ : G ∈ nunion N)) redundant)
        inference (fun D member => persistent D (sides D member)) (persistent main mainIn)
    exact redundantInference_diff redundant
  have noEmpty : (0 : Clause (GroundTerm sig)) ∉ irredundant (nunion N) := by
    rintro ⟨⟨i, C, member, θ, zero⟩, -⟩
    exact never i ((NClause.ground_eq_zero_iff θ C).mp zero ▸ member)
  obtain ⟨I, holds⟩ := Superposition.satisfiable saturated noEmpty
  have all : ∀ G ∈ nunion N, Models I.rel G := by
    intro G
    refine clauseLT_wf.induction (C := fun G => G ∈ nunion N → Models I.rel G) G fun G ih member => ?_
    by_cases redundant : Redundant (nunion N) G
    · exact redundant I fun D ⟨inUnion, lt⟩ => ih D lt inUnion
    · exact holds G ⟨member, redundant⟩
  exact unsatisfiable ⟨I, fun C member θ => all _ ⟨0, C, member, θ, rfl⟩⟩

end Derivations

#print axioms NClause.rename_id
#print axioms variableSupply_of_equiv
#print axioms standardize
#print axioms NClause.ground_rename
#print axioms ground_redundant
#print axioms NSaturated.saturated
#print axioms NSaturated.satisfiable
#print axioms NDerivation.models
#print axioms NDerivation.persists
#print axioms NDerivation.complete

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition
