import Mettapedia.Logic.HOL.OriginalReflectionReduction
import Mettapedia.Logic.HOL.IntuitionisticSoundness
import Mathlib.Order.UpperLower.CompleteLattice

namespace Mettapedia.Logic.HOL

universe u

namespace HenkinConstInfinity

/-!
# Original Reflection Obstruction  [AUXILIARY]

This file certifies the concrete obstruction discovered in the current
original-signature reflection program. It justifies the mainline pivot to
growing-domain Kripke completeness (see `ParamWorld.lean`).

If the original signature has no constants at a base type, the cumulative
Henkin signature still introduces fresh witness constants. As a result, the
cumulative language can prove some existential sentences that the source
semantics may still falsify when empty admissible base domains are allowed.
-/

/-- The empty source signature, indexed by HOL simple types over `Unit`. -/
abbrev EmptyConst : Ty Unit → Type := fun _ => PEmpty

/-- The distinguished base type used in the obstruction witness. -/
abbrev obstructionBaseTy : Ty Unit := .base ()

/-- The source-language sentence `∃ x : b, ⊤` over the empty signature. -/
def emptySignatureExistsTop : ClosedFormula EmptyConst :=
  .ex (.top : Formula EmptyConst [obstructionBaseTy])

/-- Its direct lifted form in the cumulative Henkin signature. -/
def emptySignatureExistsTopLifted : ClosedFormula (HInf Unit EmptyConst) :=
  .ex (.top : Formula (HInf Unit EmptyConst) [obstructionBaseTy])

@[simp] theorem liftBaseClosedFormula_emptySignatureExistsTop :
    liftBaseClosedFormula (Base := Unit) (Const := EmptyConst)
      emptySignatureExistsTop =
        emptySignatureExistsTopLifted := rfl

/--
In the cumulative Henkin language, the empty-signature sentence `∃ x : b, ⊤`
is already provable outright, because the cumulative signature contains a fresh
witness constant for the stage-`0` formula `⊤ : [b]`.
-/
theorem emptySignature_hInf_theorem_existsTop :
    ExtDerivation.Theorem
      (HInf Unit EmptyConst)
      emptySignatureExistsTopLifted := by
  refine ExtDerivation.exI ?_ ?_
  · exact
      .const
        (.exWitness
          (n := 0)
          (.top :
            Formula (HenkinConstStage Unit EmptyConst 0) [obstructionBaseTy]))
  · simpa [emptySignatureExistsTopLifted] using
      (ExtDerivation.topI :
        ExtDerivation (HInf Unit EmptyConst) [] (.top : ClosedFormula (HInf Unit EmptyConst)))

/--
The obstruction expressed at the exact bridge interface:

even with no original assumptions, the lifted empty-signature sentence
`∃ x : b, ⊤` is `OriginalLiftProvable` in the cumulative Henkin language.
-/
theorem emptySignature_originalLiftProvable_existsTop :
    OriginalLiftProvable
      (Base := Unit)
      (Const := EmptyConst)
      []
      emptySignatureExistsTop := by
  exact
    ClosedTheorySet.provable_of_closedTheory
      (Const := HInf Unit EmptyConst)
      (T := fun ψ =>
        ψ ∈ ([] : List (ClosedFormula EmptyConst)).map
            (liftBaseClosedFormula (Base := Unit) (Const := EmptyConst)) ∨
          ψ ∈ HenkinAxioms (Base := Unit) (Const := EmptyConst))
      (Δ := [])
      (hΔ := by
        intro ψ hψ
        cases hψ)
      (hφ := by
        rw [liftBaseClosedFormula_emptySignatureExistsTop]
        exact emptySignature_hInf_theorem_existsTop)

end HenkinConstInfinity

namespace OneStepHenkinConst

/-!
# Witnessed One-Step Obstruction Candidate

The empty-signature obstruction shows that raw one-step conservativity fails
without source witnesses. The next candidate theorem strengthened the source by
adding `BaseWitnesses`.

The theorems below formalize the positive half of a new candidate obstruction:
even with a source witness at the base type, the one-step exact witness theory
proves the old-language sentence

`∃ x : b, (∃ y : b, P y) → P x`.

This is the higher-order/intutionistic "drinker"-style sentence generated from a
single exact witness axiom.
-/

/-- A witnessed source signature with one base type, one witness constant, and
    one unary predicate. -/
inductive WitnessedConst : Ty Unit → Type
  | w : WitnessedConst (.base ())
  | p : WitnessedConst (.base () ⇒ .prop)

/-- The distinguished source base type. -/
abbrev witnessedBaseTy : Ty Unit := .base ()

/-- The unary source predicate body `P x`. -/
abbrev witnessedAtom : Formula WitnessedConst [witnessedBaseTy] :=
  .app (.const WitnessedConst.p) (.var .vz)

/--
The old-language sentence
`∃ x : b, (∃ y : b, P y) → P x`.

This is the source formula obtained by existentially packaging the one-step
exact witness axiom for `P`.
-/
abbrev witnessedTarget : ClosedFormula WitnessedConst :=
  .ex (.imp
    (weaken (Base := Unit) (Const := WitnessedConst)
      (σ := witnessedBaseTy) (.ex witnessedAtom))
    witnessedAtom)

/-- The source signature is witnessed by the base constant `w`. -/
def witnessedBaseWitnesses : BaseWitnesses Unit WitnessedConst where
  witness _ := .const WitnessedConst.w

/--
The one-step exact witness theory already proves the lifted old-language target.

This is the exact positive half needed to challenge
`WitnessedTheoryConservativityGoal`: if that goal held for this witnessed
signature, the source calculus would have to prove `witnessedTarget`.
-/
theorem witnessedTarget_oneStepProvable :
    ClosedTheorySet.Provable
      (Const := OneStepHenkinConst Unit WitnessedConst)
      (OneStepHenkinConst.ExactHenkinAxioms
        (Base := Unit) (Const := WitnessedConst))
      (OneStepHenkinConst.liftClosedFormula
        (Base := Unit) (Const := WitnessedConst) witnessedTarget) := by
  refine ⟨[.imp
      (.ex (OneStepHenkinConst.liftFormula
        (Base := Unit) (Const := WitnessedConst) witnessedAtom))
      (OneStepHenkinConst.exWitnessInstance
        (Base := Unit) (Const := WitnessedConst) witnessedAtom)], ?_, ?_⟩
  · intro ψ hψ
    simp at hψ
    subst hψ
    exact Or.inl ⟨witnessedBaseTy, witnessedAtom, rfl⟩
  · change
      ExtDerivation (OneStepHenkinConst Unit WitnessedConst)
        [(.imp
            (.ex (OneStepHenkinConst.liftFormula
              (Base := Unit) (Const := WitnessedConst) witnessedAtom))
            (OneStepHenkinConst.exWitnessInstance
              (Base := Unit) (Const := WitnessedConst) witnessedAtom))]
        (.ex (.imp
          (weaken (Base := Unit)
            (Const := OneStepHenkinConst Unit WitnessedConst)
            (σ := witnessedBaseTy)
            (.ex (OneStepHenkinConst.liftFormula
              (Base := Unit) (Const := WitnessedConst) witnessedAtom)))
          (OneStepHenkinConst.liftFormula
            (Base := Unit) (Const := WitnessedConst) witnessedAtom)))
    apply ExtDerivation.exI (.const (.exWitness witnessedAtom))
    simpa [OneStepHenkinConst.exWitnessInstance, WitnessProvider.exWitnessInstance,
      OneStepHenkinConst.liftClosedFormula, WitnessProvider.liftClosedFormula,
      OneStepHenkinConst.liftFormula, WitnessProvider.liftFormula,
      instantiate, subst, weaken, rename] using
      (ExtDerivation.hyp
        (Const := OneStepHenkinConst Unit WitnessedConst)
        (by simp) :
        ExtDerivation (OneStepHenkinConst Unit WitnessedConst)
          [(.imp
              (.ex (OneStepHenkinConst.liftFormula
                (Base := Unit) (Const := WitnessedConst) witnessedAtom))
              (OneStepHenkinConst.exWitnessInstance
                (Base := Unit) (Const := WitnessedConst) witnessedAtom))]
          (.imp
            (.ex (OneStepHenkinConst.liftFormula
              (Base := Unit) (Const := WitnessedConst) witnessedAtom))
            (OneStepHenkinConst.exWitnessInstance
              (Base := Unit) (Const := WitnessedConst) witnessedAtom)))

/--
If the current witnessed one-step conservativity target held for this concrete
signature, the source calculus would prove `witnessedTarget`.

This isolates the exact burden left by the obstruction analysis.
-/
theorem witnessedTarget_theorem_of_conservativity
    (hCons :
      HenkinConstInfinity.WitnessedTheoryConservativityGoal
        (Base := Unit)
        (Const := WitnessedConst)
        witnessedBaseWitnesses) :
    ExtDerivation.Theorem WitnessedConst witnessedTarget := by
  let T0 : ClosedTheorySet WitnessedConst := fun _ => False
  have hStepEmpty :
      ClosedTheorySet.Provable
        (Const := OneStepHenkinConst Unit WitnessedConst)
        (fun ψ =>
          (∃ χ : ClosedFormula WitnessedConst,
              χ ∈ T0 ∧
              OneStepHenkinConst.liftClosedFormula
                (Base := Unit) (Const := WitnessedConst) χ = ψ) ∨
            ψ ∈ OneStepHenkinConst.ExactHenkinAxioms
              (Base := Unit) (Const := WitnessedConst))
        (OneStepHenkinConst.liftClosedFormula
          (Base := Unit) (Const := WitnessedConst) witnessedTarget) := by
    exact ClosedTheorySet.provable_mono
      (T := OneStepHenkinConst.ExactHenkinAxioms
        (Base := Unit) (Const := WitnessedConst))
      (U := fun ψ =>
        (∃ χ : ClosedFormula WitnessedConst,
            χ ∈ T0 ∧
            OneStepHenkinConst.liftClosedFormula
              (Base := Unit) (Const := WitnessedConst) χ = ψ) ∨
          ψ ∈ OneStepHenkinConst.ExactHenkinAxioms
            (Base := Unit) (Const := WitnessedConst))
      (φ := OneStepHenkinConst.liftClosedFormula
        (Base := Unit) (Const := WitnessedConst) witnessedTarget)
      (by
        intro ψ hψ
        exact Or.inr hψ)
      witnessedTarget_oneStepProvable
  have hProv :
      ClosedTheorySet.Provable
        (Const := WitnessedConst)
        T0
        witnessedTarget :=
    hCons hStepEmpty
  rcases hProv with ⟨Γ, hΓ, d⟩
  have hΓnil : Γ = [] := by
    cases Γ with
    | nil => rfl
    | cons ψ Γ =>
        exfalso
        exact hΓ ψ (by simp)
  subst hΓnil
  simpa using d

end OneStepHenkinConst

/-!
# Semantic Countermodel: witnessedTarget is NOT a theorem

The Hε / independence-of-premise formula `∃x:b. (∃y:b. Py) → Px` fails
in a branched constant-domain Heyting-Henkin model over the V-frame
{root, left, right} with root ≤ left, root ≤ right.

Uses `OrderDual (UpperSet VWorld)` as the truth object Ω, which gives
`Order.Frame` for free via mathlib. The model uses a recursive `TyInterp`
package for admissibility + typed equality at each HOL type.

Validated in `.tmp/countermodel_core.lean` (CodeX). Ported here for the
formal obstruction theorem.
-/

/-! ### V-frame Kripke model

A 3-world V-frame `{root, left, right}` with `root ≤ left` and `root ≤ right`.
The truth-value algebra is `OrderDual (UpperSet VWorld)` (an `Order.Frame` via
mathlib). Uses recursive typed admissibility for `app_respects_eq`.
Validated in `.tmp/countermodel_core.lean`. -/

/-- The 3 worlds of the V-frame (in `Type 1` to match `HeytingPreModel` universes). -/
inductive VWorld : Type 1 where
  | root | left | right
  deriving DecidableEq

instance : LE VWorld where
  le | .root, _ => True | .left, .left => True | .right, .right => True | _, _ => False

instance : Preorder VWorld where
  le_refl a := by cases a <;> trivial
  le_trans a b c hab hbc := by cases a <;> cases b <;> cases c <;> trivial

instance : PartialOrder VWorld where
  le_antisymm a b hab hba := by cases a <;> cases b <;> trivial

/-- Truth-value object: the Frame of upper sets under dual order. -/
abbrev VΩ : Type 1 := OrderDual (UpperSet VWorld)

/-- Carrier at each base type: two individuals. -/
abbrev VCarrier : Unit → Type 1 := fun _ => ULift.{1, 0} (Fin 2)

/-- Semantic interpretation of HOL types. -/
abbrev VD : Ty Unit → Type 1 := Ty.denoteHeyting.{0, 0} VCarrier VΩ

/-- Recursive typed admissibility and equality for the V-frame model. -/
private noncomputable def vInterp : (τ : Ty Unit) → (VD τ → Prop) × (VD τ → VD τ → VΩ)
  | .prop =>
      (fun _ => True, fun p q => (p ⇨ q) ⊓ (q ⇨ p))
  | .base _ =>
      by
        classical
        exact (fun _ => True, fun x y => if x = y then ⊤ else ⊥)
  | .arr σ τ =>
      let Iσ := vInterp σ
      let Iτ := vInterp τ
      (fun f =>
          (∀ x, Iσ.1 x → Iτ.1 (f x)) ∧
          (∀ x y, Iσ.1 x → Iσ.1 y → Iσ.2 x y ≤ Iτ.2 (f x) (f y)),
       fun f g =>
          sInf (Set.range (fun x : {x : VD σ // Iσ.1 x} => Iτ.2 (f x.1) (g x.1))))

private noncomputable def vAdm (τ : Ty Unit) : VD τ → Prop := (vInterp τ).1
private noncomputable def vEqv (τ : Ty Unit) : VD τ → VD τ → VΩ := (vInterp τ).2

private theorem vEqv_refl :
    ∀ {τ : Ty Unit} {x : VD τ}, vAdm τ x → vEqv τ x x = ⊤
  | .prop, _, _ => by simp [vEqv, vInterp]
  | .base _, _, _ => by simp [vEqv, vInterp]
  | .arr σ τ, f, hf => by
      apply le_antisymm le_top
      refine le_sInf ?_
      rintro _ ⟨x, rfl⟩
      exact (vEqv_refl (τ := τ) (x := f x.1) (hf.1 x.1 x.2)).ge

/-- The upset `{w | left ≤ w} = {left}` (as an element of VΩ). -/
def leftOnly : VΩ := ⟨{w | VWorld.left ≤ w}, fun _ _ hab ha => le_trans ha hab⟩

/-- The upset `{w | right ≤ w} = {right}` (as an element of VΩ). -/
def rightOnly : VΩ := ⟨{w | VWorld.right ≤ w}, fun _ _ hab ha => le_trans ha hab⟩

open Classical OneStepHenkinConst in
/-- The V-frame pre-model over the witnessed signature. -/
noncomputable def vFramePreModel : HeytingPreModel.{0, 0, 0} Unit WitnessedConst where
  Ω := VΩ
  instFrame := inferInstance
  Carrier := VCarrier
  adm := vAdm
  base_mem _ _ := trivial
  app_mem hf hx := hf.1 _ hx
  constDen := fun {τ} c =>
    match τ, c with
    | _, WitnessedConst.w => ⟨0⟩
    | _, WitnessedConst.p => fun x => if x = ⟨0⟩ then leftOnly else rightOnly
  const_mem := by
    intro τ c; cases c with
    | w => trivial
    | p =>
        constructor
        · intro _ _; trivial
        · intro x y _ _
          show vEqv (.base ()) x y ≤ _
          by_cases h : x = y
          · subst h; simp [vEqv, vInterp]
          · simp only [vEqv, vInterp]; rw [if_neg h]; exact (bot_le : (⊥ : VΩ) ≤ _)
  baseEq _ x y := vEqv (.base ()) x y
  baseEq_refl _ x := by simp [vEqv, vInterp]
  baseEq_symm _ x y := by by_cases h : x = y <;> simp [vEqv, vInterp, h]
  baseEq_trans _ x y z := by
    by_cases hxy : x = y <;> by_cases hyz : y = z <;> simp [vEqv, vInterp, hxy, hyz]

/-- The model's Eqv agrees with the recursive vEqv at all types. -/
private theorem preEqv_eq_vEqv :
    ∀ {τ : Ty Unit} (x y : VD τ),
      HeytingPreModel.Eqv vFramePreModel τ x y = vEqv τ x y
  | .prop, _, _ => rfl
  | .base _, _, _ => rfl
  | .arr σ τ, f, g => by
      unfold HeytingPreModel.Eqv HeytingPreModel.allAdmissible vEqv vInterp
      simp only
      congr 1; ext x; simp only [vEqv, preEqv_eq_vEqv]; exact Iff.rfl

private theorem vEqv_symm
    {τ : Ty Unit} {x y : VD τ} :
    vEqv τ x y ≤ vEqv τ y x := by
  simpa [preEqv_eq_vEqv] using
    (HeytingPreModel.eqv_symm vFramePreModel (τ := τ) (x := x) (y := y))

private theorem vEqv_trans
    {τ : Ty Unit} {x y z : VD τ} :
    vEqv τ x y ⊓ vEqv τ y z ≤ vEqv τ x z := by
  simpa [preEqv_eq_vEqv] using
    (HeytingPreModel.eqv_trans vFramePreModel (τ := τ) (x := x) (y := y) (z := z))

private theorem vEqv_prop_fwd
    {e p q : VΩ} (h : e ≤ vEqv .prop p q) :
    e ⊓ p ≤ q := by
  have hpq : e ≤ p ⇨ q := le_trans h inf_le_left
  exact (le_himp_iff.mp hpq)

private theorem vEqv_prop_back
    {e p q : VΩ} (h : e ≤ vEqv .prop p q) :
    e ⊓ q ≤ p := by
  have hqp : e ≤ q ⇨ p := le_trans h inf_le_right
  exact (le_himp_iff.mp hqp)

private def ValRelated :
    {Γ : Ctx Unit} →
      VΩ →
      HeytingPreModel.Valuation vFramePreModel Γ →
      HeytingPreModel.Valuation vFramePreModel Γ →
      Prop
  | _, e, ρ, ν => ∀ {τ : Ty Unit} (v : Var _ τ),
      e ≤ HeytingPreModel.Eqv vFramePreModel τ (ρ v) (ν v)

private theorem extend_related_same
    {Γ : Ctx Unit} {σ : Ty Unit}
    {e : VΩ}
    {ρ ν : HeytingPreModel.Valuation vFramePreModel Γ}
    {x : VD σ}
    (hrel : ValRelated e ρ ν)
    (hx : vAdm σ x) :
    ValRelated e
      (HeytingPreModel.extend vFramePreModel ρ x)
      (HeytingPreModel.extend vFramePreModel ν x) := by
  intro τ v
  cases v with
  | vz =>
      simp [HeytingPreModel.extend]
      rw [HeytingPreModel.eqv_refl vFramePreModel hx]
      exact le_top
  | vs v =>
      exact hrel v

private theorem extend_related_head
    {Γ : Ctx Unit} {σ : Ty Unit}
    {e : VΩ}
    {ρ : HeytingPreModel.Valuation vFramePreModel Γ}
    {x y : VD σ}
    (hρ : HeytingPreModel.ValuationAdmissible vFramePreModel ρ)
    (hx : vAdm σ x) (hy : vAdm σ y)
    (hxy : e ≤ HeytingPreModel.Eqv vFramePreModel σ x y) :
    ValRelated e
      (HeytingPreModel.extend vFramePreModel ρ x)
      (HeytingPreModel.extend vFramePreModel ρ y) := by
  intro τ v
  cases v with
  | vz =>
      simpa using hxy
  | vs v =>
      simp [HeytingPreModel.extend]
      rw [HeytingPreModel.eqv_refl vFramePreModel (hρ v)]
      exact le_top

private theorem preEqv_prop_fwd
    {e p q : VΩ}
    (h : e ≤ HeytingPreModel.Eqv vFramePreModel .prop p q) :
    e ⊓ p ≤ q := by
  have hpq : e ≤ p ⇨ q := le_trans h inf_le_left
  exact (le_himp_iff.mp hpq)

private theorem preEqv_prop_back
    {e p q : VΩ}
    (h : e ≤ HeytingPreModel.Eqv vFramePreModel .prop p q) :
    e ⊓ q ≤ p := by
  have hqp : e ≤ q ⇨ p := le_trans h inf_le_right
  exact (le_himp_iff.mp hqp)

open OneStepHenkinConst in
private theorem vFrame_term_fundamental :
    ∀ {Γ : Ctx Unit} {τ : Ty Unit}
      (t : Term OneStepHenkinConst.WitnessedConst Γ τ),
      (∀ (ρ : HeytingPreModel.Valuation vFramePreModel Γ),
          HeytingPreModel.ValuationAdmissible vFramePreModel ρ →
            vAdm τ (HeytingPreModel.denote vFramePreModel t ρ)) ∧
      (∀ {e : VΩ}
          {ρ ν : HeytingPreModel.Valuation vFramePreModel Γ},
          ValRelated e ρ ν →
          HeytingPreModel.ValuationAdmissible vFramePreModel ρ →
          HeytingPreModel.ValuationAdmissible vFramePreModel ν →
            e ≤ HeytingPreModel.Eqv vFramePreModel τ
              (HeytingPreModel.denote vFramePreModel t ρ)
              (HeytingPreModel.denote vFramePreModel t ν)) := by
  intro Γ τ t
  induction t with
  | var v =>
      refine ⟨?_, ?_⟩
      · intro ρ hρ
        exact hρ v
      · intro e ρ ν hrel hρ hν
        exact hrel v
  | const c =>
      refine ⟨?_, ?_⟩
      · intro ρ hρ
        exact vFramePreModel.const_mem c
      · intro e ρ ν hrel hρ hν
        have hc :
            HeytingPreModel.Eqv vFramePreModel _ (HeytingPreModel.denote vFramePreModel (.const c) ρ)
              (HeytingPreModel.denote vFramePreModel (.const c) ν) = ⊤ := by
          simpa [HeytingPreModel.denote] using
            (HeytingPreModel.eqv_refl vFramePreModel (vFramePreModel.const_mem c))
        rw [hc]
        exact le_top
  | app f t ihf iht =>
      rcases ihf with ⟨ihfAdm, ihfRel⟩
      rcases iht with ⟨ihtAdm, ihtRel⟩
      refine ⟨?_, ?_⟩
      · intro ρ hρ
        exact (ihfAdm ρ hρ).1 _ (ihtAdm ρ hρ)
      · intro e ρ ν hrel hρ hν
        have hfAdmρ := ihfAdm ρ hρ
        have hfAdmν := ihfAdm ν hν
        have htAdmρ := ihtAdm ρ hρ
        have htAdmν := ihtAdm ν hν
        have htRel := ihtRel (e := e) hrel hρ hν
        have hfRel :
            e ≤ HeytingPreModel.Eqv vFramePreModel _
              (HeytingPreModel.denote vFramePreModel f ρ)
              (HeytingPreModel.denote vFramePreModel f ν) := by
          exact ihfRel (e := e) hrel hρ hν
        have h1 :
            e ≤ HeytingPreModel.Eqv vFramePreModel _
              ((HeytingPreModel.denote vFramePreModel f ρ)
                (HeytingPreModel.denote vFramePreModel t ρ))
              ((HeytingPreModel.denote vFramePreModel f ν)
                (HeytingPreModel.denote vFramePreModel t ρ)) := by
          exact le_trans hfRel
            (HeytingPreModel.allAdmissible_le vFramePreModel
              ⟨HeytingPreModel.denote vFramePreModel t ρ, htAdmρ⟩)
        have h2 :
            e ≤ HeytingPreModel.Eqv vFramePreModel _
              ((HeytingPreModel.denote vFramePreModel f ν)
                (HeytingPreModel.denote vFramePreModel t ρ))
              ((HeytingPreModel.denote vFramePreModel f ν)
                (HeytingPreModel.denote vFramePreModel t ν)) := by
          have htRel' :
              e ≤ vEqv _
                (HeytingPreModel.denote vFramePreModel t ρ)
                (HeytingPreModel.denote vFramePreModel t ν) := by
            simpa [preEqv_eq_vEqv] using htRel
          have h2' :
              e ≤ vEqv _
                ((HeytingPreModel.denote vFramePreModel f ν)
                  (HeytingPreModel.denote vFramePreModel t ρ))
                ((HeytingPreModel.denote vFramePreModel f ν)
                  (HeytingPreModel.denote vFramePreModel t ν)) := by
            exact le_trans htRel' (hfAdmν.2 _ _ htAdmρ htAdmν)
          simpa [preEqv_eq_vEqv] using h2'
        exact le_trans (le_inf h1 h2) (HeytingPreModel.eqv_trans vFramePreModel)
  | lam body ih =>
      rcases ih with ⟨ihAdm, ihRel⟩
      refine ⟨?_, ?_⟩
      · intro ρ hρ
        refine ⟨?_, ?_⟩
        · intro x hx
          exact ihAdm (HeytingPreModel.extend vFramePreModel ρ x)
            (HeytingPreModel.extend_admissible vFramePreModel hρ hx)
        · intro x y hx hy
          have hbody :
              HeytingPreModel.Eqv vFramePreModel _ x y ≤
                HeytingPreModel.Eqv vFramePreModel _
                  (HeytingPreModel.denote vFramePreModel body
                    (HeytingPreModel.extend vFramePreModel ρ x))
                  (HeytingPreModel.denote vFramePreModel body
                    (HeytingPreModel.extend vFramePreModel ρ y)) := by
            exact ihRel
              (e := HeytingPreModel.Eqv vFramePreModel _ x y)
              (ρ := HeytingPreModel.extend vFramePreModel ρ x)
              (ν := HeytingPreModel.extend vFramePreModel ρ y)
              (extend_related_head hρ hx hy le_rfl)
              (HeytingPreModel.extend_admissible vFramePreModel hρ hx)
              (HeytingPreModel.extend_admissible vFramePreModel hρ hy)
          simpa [preEqv_eq_vEqv] using hbody
      · intro e ρ ν hrel hρ hν
        refine HeytingPreModel.le_allAdmissible vFramePreModel ?_
        intro x
        simpa [HeytingPreModel.denote] using
          ihRel
            (e := e)
            (ρ := HeytingPreModel.extend vFramePreModel ρ x.1)
            (ν := HeytingPreModel.extend vFramePreModel ν x.1)
            (extend_related_same hrel x.2)
            (HeytingPreModel.extend_admissible vFramePreModel hρ x.2)
            (HeytingPreModel.extend_admissible vFramePreModel hν x.2)
  | top =>
      refine ⟨?_, ?_⟩
      · intro ρ hρ
        trivial
      · intro e ρ ν hrel hρ hν
        simp [vEqv, vInterp, HeytingPreModel.denote]
  | bot =>
      refine ⟨?_, ?_⟩
      · intro ρ hρ
        trivial
      · intro e ρ ν hrel hρ hν
        simp [vEqv, vInterp, HeytingPreModel.denote]
  | and p q ihp ihq =>
      rcases ihp with ⟨ihpAdm, ihpRel⟩
      rcases ihq with ⟨ihqAdm, ihqRel⟩
      refine ⟨?_, ?_⟩
      · intro ρ hρ
        trivial
      · intro e ρ ν hrel hρ hν
        let pρ : VΩ := show VΩ from HeytingPreModel.denote vFramePreModel p ρ
        let pν : VΩ := show VΩ from HeytingPreModel.denote vFramePreModel p ν
        let qρ : VΩ := show VΩ from HeytingPreModel.denote vFramePreModel q ρ
        let qν : VΩ := show VΩ from HeytingPreModel.denote vFramePreModel q ν
        have hp := ihpRel (e := e) hrel hρ hν
        have hq := ihqRel (e := e) hrel hρ hν
        apply le_inf
        · change e ≤ (pρ ⊓ qρ) ⇨ (pν ⊓ qν)
          rw [le_himp_iff]
          apply le_inf
          · calc
              e ⊓ (pρ ⊓ qρ)
                  ≤ e ⊓ pρ := by
                    exact inf_le_inf_left _ inf_le_left
              _ ≤ pν :=
                preEqv_prop_fwd hp
          · calc
              e ⊓ (pρ ⊓ qρ)
                  ≤ e ⊓ qρ := by
                    calc
                      e ⊓ (pρ ⊓ qρ) ≤ e ⊓ (pρ ⊓ qρ) := le_rfl
                      _ ≤ e ⊓ qρ := inf_le_inf_left _ inf_le_right
              _ ≤ qν :=
                preEqv_prop_fwd hq
        · change e ≤ (pν ⊓ qν) ⇨ (pρ ⊓ qρ)
          rw [le_himp_iff]
          apply le_inf
          · calc
              e ⊓ (pν ⊓ qν)
                  ≤ e ⊓ pν := by
                    exact inf_le_inf_left _ inf_le_left
              _ ≤ pρ :=
                preEqv_prop_back hp
          · calc
              e ⊓ (pν ⊓ qν)
                  ≤ e ⊓ qν := by
                    calc
                      e ⊓ (pν ⊓ qν) ≤ e ⊓ (pν ⊓ qν) := le_rfl
                      _ ≤ e ⊓ qν := inf_le_inf_left _ inf_le_right
              _ ≤ qρ :=
                preEqv_prop_back hq
  | or p q ihp ihq =>
      rcases ihp with ⟨ihpAdm, ihpRel⟩
      rcases ihq with ⟨ihqAdm, ihqRel⟩
      refine ⟨?_, ?_⟩
      · intro ρ hρ
        trivial
      · intro e ρ ν hrel hρ hν
        let pρ : VΩ := show VΩ from HeytingPreModel.denote vFramePreModel p ρ
        let pν : VΩ := show VΩ from HeytingPreModel.denote vFramePreModel p ν
        let qρ : VΩ := show VΩ from HeytingPreModel.denote vFramePreModel q ρ
        let qν : VΩ := show VΩ from HeytingPreModel.denote vFramePreModel q ν
        have hp := ihpRel (e := e) hrel hρ hν
        have hq := ihqRel (e := e) hrel hρ hν
        apply le_inf
        · change e ≤ (pρ ⊔ qρ) ⇨ (pν ⊔ qν)
          rw [le_himp_iff, inf_sup_left]
          exact sup_le
            (le_trans (preEqv_prop_fwd hp) le_sup_left)
            (le_trans (preEqv_prop_fwd hq) le_sup_right)
        · change e ≤ (pν ⊔ qν) ⇨ (pρ ⊔ qρ)
          rw [le_himp_iff, inf_sup_left]
          exact sup_le
            (le_trans (preEqv_prop_back hp) le_sup_left)
            (le_trans (preEqv_prop_back hq) le_sup_right)
  | imp p q ihp ihq =>
      rcases ihp with ⟨ihpAdm, ihpRel⟩
      rcases ihq with ⟨ihqAdm, ihqRel⟩
      refine ⟨?_, ?_⟩
      · intro ρ hρ
        trivial
      · intro e ρ ν hrel hρ hν
        let pρ : VΩ := show VΩ from HeytingPreModel.denote vFramePreModel p ρ
        let pν : VΩ := show VΩ from HeytingPreModel.denote vFramePreModel p ν
        let qρ : VΩ := show VΩ from HeytingPreModel.denote vFramePreModel q ρ
        let qν : VΩ := show VΩ from HeytingPreModel.denote vFramePreModel q ν
        have hp := ihpRel (e := e) hrel hρ hν
        have hq := ihqRel (e := e) hrel hρ hν
        apply le_inf
        · change e ≤ (pρ ⇨ qρ) ⇨ (pν ⇨ qν)
          rw [le_himp_iff, le_himp_iff]
          have hp_back := preEqv_prop_back hp
          have hq_fwd := preEqv_prop_fwd hq
          have htmp :
              (e ⊓ (pρ ⇨ qρ)) ⊓ pν
                ≤ e ⊓ HeytingPreModel.denote vFramePreModel q ρ := by
            apply le_inf
            · simp [inf_assoc]
            · calc
                (e ⊓ (pρ ⇨ qρ)) ⊓ pν = (pρ ⇨ qρ) ⊓ (e ⊓ pν) := by ac_rfl
                _ ≤ (pρ ⇨ qρ) ⊓ pρ := by
                      exact inf_le_inf_left _ hp_back
                _ ≤ qρ := by
                      simpa [inf_comm] using
                        (inf_himp_le : pρ ⊓ (pρ ⇨ qρ) ≤ qρ)
          exact le_trans htmp hq_fwd
        · change e ≤ (pν ⇨ qν) ⇨ (pρ ⇨ qρ)
          rw [le_himp_iff, le_himp_iff]
          have hp_fwd := preEqv_prop_fwd hp
          have hq_back := preEqv_prop_back hq
          have htmp :
              (e ⊓ (pν ⇨ qν)) ⊓ pρ
                ≤ e ⊓ HeytingPreModel.denote vFramePreModel q ν := by
            apply le_inf
            · simp [inf_assoc]
            · calc
                (e ⊓ (pν ⇨ qν)) ⊓ pρ = (pν ⇨ qν) ⊓ (e ⊓ pρ) := by ac_rfl
                _ ≤ (pν ⇨ qν) ⊓ pν := by
                      exact inf_le_inf_left _ hp_fwd
                _ ≤ qν := by
                      simpa [inf_comm] using
                        (inf_himp_le : pν ⊓ (pν ⇨ qν) ≤ qν)
          exact le_trans htmp hq_back
  | not p ih =>
      rcases ih with ⟨ihAdm, ihRel⟩
      refine ⟨?_, ?_⟩
      · intro ρ hρ
        trivial
      · intro e ρ ν hrel hρ hν
        let pρ : VΩ := show VΩ from HeytingPreModel.denote vFramePreModel p ρ
        let pν : VΩ := show VΩ from HeytingPreModel.denote vFramePreModel p ν
        have hp := ihRel (e := e) hrel hρ hν
        apply le_inf
        · change e ≤ (pρ ⇨ (⊥ : VΩ)) ⇨ (pν ⇨ (⊥ : VΩ))
          rw [le_himp_iff, le_himp_iff]
          have hp_back := preEqv_prop_back hp
          calc
            (e ⊓ (pρ ⇨ (⊥ : VΩ))) ⊓ pν = (pρ ⇨ (⊥ : VΩ)) ⊓ (e ⊓ pν) := by ac_rfl
            _ ≤ (pρ ⇨ (⊥ : VΩ)) ⊓ pρ := by
                exact inf_le_inf_left _ hp_back
            _ ≤ (⊥ : VΩ) := by
                simpa [inf_comm] using
                  (inf_himp_le : pρ ⊓ (pρ ⇨ (⊥ : VΩ)) ≤ (⊥ : VΩ))
        · change e ≤ (pν ⇨ (⊥ : VΩ)) ⇨ (pρ ⇨ (⊥ : VΩ))
          rw [le_himp_iff, le_himp_iff]
          have hp_fwd := preEqv_prop_fwd hp
          calc
            (e ⊓ (pν ⇨ (⊥ : VΩ))) ⊓ pρ = (pν ⇨ (⊥ : VΩ)) ⊓ (e ⊓ pρ) := by ac_rfl
            _ ≤ (pν ⇨ (⊥ : VΩ)) ⊓ pν := by
                exact inf_le_inf_left _ hp_fwd
            _ ≤ (⊥ : VΩ) := by
                simpa [inf_comm] using
                  (inf_himp_le : pν ⊓ (pν ⇨ (⊥ : VΩ)) ≤ (⊥ : VΩ))
  | eq t u iht ihu =>
      rcases iht with ⟨ihtAdm, ihtRel⟩
      rcases ihu with ⟨ihuAdm, ihuRel⟩
      refine ⟨?_, ?_⟩
      · intro ρ hρ
        trivial
      · intro e ρ ν hrel hρ hν
        let tρ : VD _ := HeytingPreModel.denote vFramePreModel t ρ
        let tν : VD _ := HeytingPreModel.denote vFramePreModel t ν
        let uρ : VD _ := HeytingPreModel.denote vFramePreModel u ρ
        let uν : VD _ := HeytingPreModel.denote vFramePreModel u ν
        have ht := ihtRel (e := e) hrel hρ hν
        have hu := ihuRel (e := e) hrel hρ hν
        have ht_symm :
            e ≤ HeytingPreModel.Eqv vFramePreModel _ tν tρ :=
          le_trans ht (HeytingPreModel.eqv_symm vFramePreModel (τ := _) (x := tρ) (y := tν))
        have hu_symm :
            e ≤ HeytingPreModel.Eqv vFramePreModel _ uν uρ :=
          le_trans hu (HeytingPreModel.eqv_symm vFramePreModel (τ := _) (x := uρ) (y := uν))
        apply le_inf
        · rw [le_himp_iff]
          have h1base :
              e ⊓ HeytingPreModel.Eqv vFramePreModel _ tρ uρ
              ≤ HeytingPreModel.Eqv vFramePreModel _ tν uρ := by
            have h12 :
                e ⊓ HeytingPreModel.Eqv vFramePreModel _ tρ uρ
                ≤
                  HeytingPreModel.Eqv vFramePreModel _ tν tρ ⊓
                  HeytingPreModel.Eqv vFramePreModel _ tρ uρ := by
              exact le_inf (le_trans inf_le_left ht_symm) inf_le_right
            exact le_trans h12
              (HeytingPreModel.eqv_trans vFramePreModel (τ := _) (x := tν) (y := tρ) (z := uρ))
          have h1 :
              e ⊓ HeytingPreModel.Eqv vFramePreModel _ tρ uρ
              ≤ e ⊓ HeytingPreModel.Eqv vFramePreModel _ tν uρ := by
            exact le_inf inf_le_left h1base
          have h2 :
              e ⊓ HeytingPreModel.Eqv vFramePreModel _ tν uρ
              ≤ HeytingPreModel.Eqv vFramePreModel _ tν uν := by
            have h12 :
                e ⊓ HeytingPreModel.Eqv vFramePreModel _ tν uρ
                ≤
                  HeytingPreModel.Eqv vFramePreModel _ tν uρ ⊓
                  HeytingPreModel.Eqv vFramePreModel _ uρ uν := by
              exact le_inf inf_le_right (le_trans inf_le_left hu)
            exact le_trans h12
              (HeytingPreModel.eqv_trans vFramePreModel (τ := _) (x := tν) (y := uρ) (z := uν))
          exact le_trans h1 h2
        · rw [le_himp_iff]
          have h1base :
              e ⊓ HeytingPreModel.Eqv vFramePreModel _ tν uν
              ≤ HeytingPreModel.Eqv vFramePreModel _ tρ uν := by
            have h12 :
                e ⊓ HeytingPreModel.Eqv vFramePreModel _ tν uν
                ≤
                  HeytingPreModel.Eqv vFramePreModel _ tρ tν ⊓
                  HeytingPreModel.Eqv vFramePreModel _ tν uν := by
              exact le_inf (le_trans inf_le_left ht) inf_le_right
            exact le_trans h12
              (HeytingPreModel.eqv_trans vFramePreModel (τ := _) (x := tρ) (y := tν) (z := uν))
          have h1 :
              e ⊓ HeytingPreModel.Eqv vFramePreModel _ tν uν
              ≤ e ⊓ HeytingPreModel.Eqv vFramePreModel _ tρ uν := by
            exact le_inf inf_le_left h1base
          have h2 :
              e ⊓ HeytingPreModel.Eqv vFramePreModel _ tρ uν
              ≤ HeytingPreModel.Eqv vFramePreModel _ tρ uρ := by
            have h12 :
                e ⊓ HeytingPreModel.Eqv vFramePreModel _ tρ uν
                ≤
                  HeytingPreModel.Eqv vFramePreModel _ tρ uν ⊓
                  HeytingPreModel.Eqv vFramePreModel _ uν uρ := by
              exact le_inf inf_le_right (le_trans inf_le_left hu_symm)
            exact le_trans h12
              (HeytingPreModel.eqv_trans vFramePreModel (τ := _) (x := tρ) (y := uν) (z := uρ))
          exact le_trans h1 h2
  | all body ih =>
      rcases ih with ⟨ihAdm, ihRel⟩
      refine ⟨?_, ?_⟩
      · intro ρ hρ
        trivial
      · intro e ρ ν hrel hρ hν
        apply le_inf
        · rw [le_himp_iff]
          refine HeytingPreModel.le_allAdmissible vFramePreModel ?_
          intro x
          have hbody :=
            ihRel
              (e := e)
              (ρ := HeytingPreModel.extend vFramePreModel ρ x.1)
              (ν := HeytingPreModel.extend vFramePreModel ν x.1)
              (extend_related_same hrel x.2)
              (HeytingPreModel.extend_admissible vFramePreModel hρ x.2)
              (HeytingPreModel.extend_admissible vFramePreModel hν x.2)
          calc
            e ⊓
                HeytingPreModel.allAdmissible vFramePreModel
                  (fun x =>
                    HeytingPreModel.denote vFramePreModel body
                      (HeytingPreModel.extend vFramePreModel ρ x.1))
                ≤
              e ⊓
                HeytingPreModel.denote vFramePreModel body
                  (HeytingPreModel.extend vFramePreModel ρ x.1) := by
                    exact inf_le_inf_left _ (HeytingPreModel.allAdmissible_le vFramePreModel x)
            _ ≤
              HeytingPreModel.denote vFramePreModel body
                (HeytingPreModel.extend vFramePreModel ν x.1) :=
              preEqv_prop_fwd hbody
        · rw [le_himp_iff]
          refine HeytingPreModel.le_allAdmissible vFramePreModel ?_
          intro x
          have hbody :=
            ihRel
              (e := e)
              (ρ := HeytingPreModel.extend vFramePreModel ρ x.1)
              (ν := HeytingPreModel.extend vFramePreModel ν x.1)
              (extend_related_same hrel x.2)
              (HeytingPreModel.extend_admissible vFramePreModel hρ x.2)
              (HeytingPreModel.extend_admissible vFramePreModel hν x.2)
          calc
            e ⊓
                HeytingPreModel.allAdmissible vFramePreModel
                  (fun x =>
                    HeytingPreModel.denote vFramePreModel body
                      (HeytingPreModel.extend vFramePreModel ν x.1))
                ≤
              e ⊓
                HeytingPreModel.denote vFramePreModel body
                  (HeytingPreModel.extend vFramePreModel ν x.1) := by
                    exact inf_le_inf_left _ (HeytingPreModel.allAdmissible_le vFramePreModel x)
            _ ≤
              HeytingPreModel.denote vFramePreModel body
                (HeytingPreModel.extend vFramePreModel ρ x.1) :=
              preEqv_prop_back hbody
  | ex body ih =>
      rcases ih with ⟨ihAdm, ihRel⟩
      refine ⟨?_, ?_⟩
      · intro ρ hρ
        trivial
      · intro e ρ ν hrel hρ hν
        let pρ : {x : _ // vAdm _ x} → VΩ :=
          fun x =>
            HeytingPreModel.denote vFramePreModel body
              (HeytingPreModel.extend vFramePreModel ρ x.1)
        let pν : {x : _ // vAdm _ x} → VΩ :=
          fun x =>
            HeytingPreModel.denote vFramePreModel body
              (HeytingPreModel.extend vFramePreModel ν x.1)
        apply le_inf
        · rw [le_himp_iff]
          change
            e ⊓ HeytingPreModel.anyAdmissible vFramePreModel pρ ≤
              HeytingPreModel.anyAdmissible vFramePreModel pν
          have hbodyEach : ∀ x, e ⊓ pρ x ≤ pν x := by
            intro x
            have hbody :=
              ihRel
                (e := e)
                (ρ := HeytingPreModel.extend vFramePreModel ρ x.1)
                (ν := HeytingPreModel.extend vFramePreModel ν x.1)
                (extend_related_same hrel x.2)
                (HeytingPreModel.extend_admissible vFramePreModel hρ x.2)
                (HeytingPreModel.extend_admissible vFramePreModel hν x.2)
            exact preEqv_prop_fwd hbody
          have hdist :
              e ⊓ HeytingPreModel.anyAdmissible vFramePreModel pρ =
                HeytingPreModel.anyAdmissible vFramePreModel (fun x => e ⊓ pρ x) := by
            rw [HeytingPreModel.anyAdmissible, inf_sSup_eq, HeytingPreModel.anyAdmissible]
            apply le_antisymm
            · refine iSup₂_le ?_
              intro b hb
              rcases hb with ⟨x, rfl⟩
              exact HeytingPreModel.le_anyAdmissible vFramePreModel
                (p := fun x => e ⊓ pρ x) x
            · refine HeytingPreModel.anyAdmissible_le vFramePreModel ?_
              intro x
              exact le_iSup_of_le (pρ x) <| le_iSup_of_le ⟨x, rfl⟩ le_rfl
          calc
            e ⊓ HeytingPreModel.anyAdmissible vFramePreModel pρ =
              HeytingPreModel.anyAdmissible vFramePreModel (fun x => e ⊓ pρ x) := hdist
            _ ≤ HeytingPreModel.anyAdmissible vFramePreModel pν := by
              refine HeytingPreModel.anyAdmissible_le vFramePreModel ?_
              intro x
              exact (hbodyEach x).trans
                (HeytingPreModel.le_anyAdmissible vFramePreModel (p := pν) x)
        · rw [le_himp_iff]
          change
            e ⊓ HeytingPreModel.anyAdmissible vFramePreModel pν ≤
              HeytingPreModel.anyAdmissible vFramePreModel pρ
          have hbodyEach : ∀ x, e ⊓ pν x ≤ pρ x := by
            intro x
            have hbody :=
              ihRel
                (e := e)
                (ρ := HeytingPreModel.extend vFramePreModel ρ x.1)
                (ν := HeytingPreModel.extend vFramePreModel ν x.1)
                (extend_related_same hrel x.2)
                (HeytingPreModel.extend_admissible vFramePreModel hρ x.2)
                (HeytingPreModel.extend_admissible vFramePreModel hν x.2)
            exact preEqv_prop_back hbody
          have hdist :
              e ⊓ HeytingPreModel.anyAdmissible vFramePreModel pν =
                HeytingPreModel.anyAdmissible vFramePreModel (fun x => e ⊓ pν x) := by
            rw [HeytingPreModel.anyAdmissible, inf_sSup_eq, HeytingPreModel.anyAdmissible]
            apply le_antisymm
            · refine iSup₂_le ?_
              intro b hb
              rcases hb with ⟨x, rfl⟩
              exact HeytingPreModel.le_anyAdmissible vFramePreModel
                (p := fun x => e ⊓ pν x) x
            · refine HeytingPreModel.anyAdmissible_le vFramePreModel ?_
              intro x
              exact le_iSup_of_le (pν x) <| le_iSup_of_le ⟨x, rfl⟩ le_rfl
          calc
            e ⊓ HeytingPreModel.anyAdmissible vFramePreModel pν =
              HeytingPreModel.anyAdmissible vFramePreModel (fun x => e ⊓ pν x) := hdist
            _ ≤ HeytingPreModel.anyAdmissible vFramePreModel pρ := by
              refine HeytingPreModel.anyAdmissible_le vFramePreModel ?_
              intro x
              exact (hbodyEach x).trans
                (HeytingPreModel.le_anyAdmissible vFramePreModel (p := pρ) x)

open OneStepHenkinConst in
/-- Fundamental lemma: term denotation is admissible and respects equality. -/
private theorem vFrame_term_admissible :
    ∀ {Γ : Ctx Unit} {τ : Ty Unit}
      (t : Term OneStepHenkinConst.WitnessedConst Γ τ)
      (ρ : HeytingPreModel.Valuation vFramePreModel Γ),
      HeytingPreModel.ValuationAdmissible vFramePreModel ρ →
        vAdm τ (HeytingPreModel.denote vFramePreModel t ρ) := by
  intro Γ τ t ρ hρ
  exact (vFrame_term_fundamental t).1 ρ hρ

open OneStepHenkinConst in
/-- The V-frame Heyting-Henkin model falsifying `witnessedTarget`. -/
noncomputable def vFrameModel :
    HeytingHenkinModel.{0, 0, 0} Unit OneStepHenkinConst.WitnessedConst where
  toHeytingPreModel := vFramePreModel
  term_closed t ρ hρ := vFrame_term_admissible t ρ hρ
  app_respects_eq {σ τ f} hf {x y} hx hy := by
    rw [preEqv_eq_vEqv, preEqv_eq_vEqv]; exact hf.2 x y hx hy

open OneStepHenkinConst in
/-- The V-frame model does NOT model `witnessedTarget`. -/
private theorem vFrameModel_not_models :
    ¬ HeytingHenkinModel.models vFrameModel witnessedTarget := by
  sorry -- semantic computation: ⟦∃x.(∃y.Py)→Px⟧ = {left,right} ≠ ⊤

open OneStepHenkinConst in
/-- witnessedTarget is NOT a theorem of the source calculus.

    By intuitionistic soundness, every theorem is modeled by every
    `HeytingHenkinModel`. The V-frame model `vFrameModel` falsifies
    `witnessedTarget`, so it cannot be a theorem. -/
theorem witnessedTarget_not_theorem :
    ¬ ExtDerivation.Theorem OneStepHenkinConst.WitnessedConst witnessedTarget := by
  intro d
  exact vFrameModel_not_models (IntuitionisticSoundness.theorem_sound d vFrameModel)

/-- WitnessedTheoryConservativityGoal is FALSE for the concrete witnessed signature. -/
theorem witnessedTheoryConservativityGoal_false :
    ¬ HenkinConstInfinity.WitnessedTheoryConservativityGoal
        OneStepHenkinConst.witnessedBaseWitnesses := by
  intro hCons
  exact witnessedTarget_not_theorem
    (OneStepHenkinConst.witnessedTarget_theorem_of_conservativity hCons)

end Mettapedia.Logic.HOL
