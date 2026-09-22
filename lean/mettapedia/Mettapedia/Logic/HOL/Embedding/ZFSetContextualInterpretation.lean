import Mettapedia.Logic.HOL.Embedding.ZFSetDependentProducts
import Mettapedia.GSLT.Core.ContextualLadderTerminal
import Mettapedia.TypeTheory.ContextualProductComparison
import Mettapedia.TypeTheory.ContextualSumComparison

/-!
# A contextual model with actual dependent set codes

Types are set-valued families and terms are sections of their membership
fibres. Products and sums use the previously constructed function graphs
and Kuratowski pairs. Their term operations satisfy beta and eta by the
actual encoding/decoding inverse laws. Context substitution acts by pullback.
This constructs semantic contextual structure, not a soundness theorem for
all native syntax or its identity and inductive eliminators.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetContextualInterpretation

open ZFSetDependentProducts
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualProductComparison
open Mettapedia.TypeTheory.ContextualSumComparison

universe u

abbrev SetFamily (Γ : Type (u + 1)) := Γ → ZFSet.{u}
abbrev Section {Γ : Type (u + 1)} (a : SetFamily Γ) := (γ : Γ) → Elements (a γ)
abbrev Extension {Γ : Type (u + 1)} (a : SetFamily Γ) := Σ γ : Γ, Elements (a γ)

/-- The full dependent contextual core, with set codes rather than arbitrary
Lean types as its type families. -/
abbrev codedCwf : Cwf.{u + 2, u + 1, u + 1, u + 1} where
  Ctx := Type (u + 1)
  Sub Γ Δ := Γ → Δ
  idS _ := id
  compS σ τ := σ ∘ τ
  id_comp _ := rfl
  comp_id _ := rfl
  comp_assoc _ _ _ := rfl
  Ty := SetFamily
  tySub a σ := a ∘ σ
  tySub_id _ := rfl
  tySub_comp _ _ _ := rfl
  Tm _ := Section
  tmSub t σ := fun γ => t (σ γ)
  tmSub_id _ := rfl
  tmSub_comp _ _ _ := rfl
  ext _ := Extension
  wk _ := Sigma.fst
  vz _ := Sigma.snd
  pair σ _ t := fun γ => ⟨σ γ, t γ⟩
  wk_pair _ _ _ := rfl
  vz_pair _ _ _ := rfl
  pair_eta _ _ := rfl

def codedCwfWithTerminal : CwfWithTerminal.{u + 2, u + 1, u + 1, u + 1} where
  toCwf := codedCwf
  empty := PUnit
  toEmpty _ := fun _ => PUnit.unit
  toEmpty_unique _ _ := rfl

/-- Extend a dependent family away from its domain only to feed the bounded
set constructors. No outside value belongs to the interpreted family. -/
noncomputable def totalFamily (a : ZFSet.{u}) (b : Elements a → ZFSet.{u})
    (x : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if hx : x ∈ a then b ⟨x, hx⟩ else ∅

theorem totalFamily_at (a : ZFSet.{u}) (b : Elements a → ZFSet.{u}) (x : Elements a) :
    totalFamily a b x.1 = b x := by
  simp only [totalFamily, dif_pos x.2]

noncomputable def piFamily {Γ : Type (u + 1)} (a : SetFamily Γ)
    (b : SetFamily (Extension a)) : SetFamily Γ :=
  fun γ => piSet (a γ) (totalFamily (a γ) (fun x => b ⟨γ, x⟩))

noncomputable def sigmaFamily {Γ : Type (u + 1)} (a : SetFamily Γ)
    (b : SetFamily (Extension a)) : SetFamily Γ :=
  fun γ => sigmaSet (a γ) (totalFamily (a γ) (fun x => b ⟨γ, x⟩))

noncomputable def piDecode {Γ : Type (u + 1)} (a : SetFamily Γ)
    (b : SetFamily (Extension a)) (γ : Γ) :
    Elements (piFamily a b γ) ≃ ((x : Elements (a γ)) → Elements (b ⟨γ, x⟩)) :=
  (piEquiv (a γ) (totalFamily (a γ) (fun x => b ⟨γ, x⟩))).trans
    (Equiv.piCongrRight (fun x => Equiv.cast
      (congrArg Elements (totalFamily_at (a γ) (fun y => b ⟨γ, y⟩) x))))

noncomputable def sigmaDecode {Γ : Type (u + 1)} (a : SetFamily Γ)
    (b : SetFamily (Extension a)) (γ : Γ) :
    Elements (sigmaFamily a b γ) ≃ (Σ x : Elements (a γ), Elements (b ⟨γ, x⟩)) :=
  (sigmaEquiv (a γ) (totalFamily (a γ) (fun x => b ⟨γ, x⟩))).trans
    (Equiv.sigmaCongrRight (fun x => Equiv.cast
      (congrArg Elements (totalFamily_at (a γ) (fun y => b ⟨γ, y⟩) x))))

/-! ## Product terms and computation -/

noncomputable def lam {Γ : Type (u + 1)} {a : SetFamily Γ}
    {b : SetFamily (Extension a)} (body : Section b) : Section (piFamily a b) :=
  fun γ => (piDecode a b γ).symm (fun x => body ⟨γ, x⟩)

noncomputable def app {Γ : Type (u + 1)} {a : SetFamily Γ}
    {b : SetFamily (Extension a)} (f : Section (piFamily a b))
    (argument : Section a) : Section (fun γ => b ⟨γ, argument γ⟩) :=
  fun γ => piDecode a b γ (f γ) (argument γ)

theorem app_lam {Γ : Type (u + 1)} {a : SetFamily Γ}
    {b : SetFamily (Extension a)} (body : Section b) (argument : Section a) :
    app (lam body) argument = fun γ => body ⟨γ, argument γ⟩ := by
  funext γ
  exact congrFun ((piDecode a b γ).apply_symm_apply (fun x => body ⟨γ, x⟩)) (argument γ)

/-- Pointwise eta reconstructs the entire original graph, not merely the
values at selected arguments. -/
theorem lam_eta {Γ : Type (u + 1)} {a : SetFamily Γ}
    {b : SetFamily (Extension a)} (f : Section (piFamily a b)) :
    lam (fun p => piDecode a b p.1 (f p.1) p.2) = f := by
  funext γ
  exact (piDecode a b γ).symm_apply_apply (f γ)

noncomputable def products : DependentProductBeta codedCwf.{u} where
  pi := piFamily
  lam := lam
  app := app
  beta := app_lam

/-! ## Sum terms and computation -/

noncomputable def pair {Γ : Type (u + 1)} {a : SetFamily Γ}
    {b : SetFamily (Extension a)} (first : Section a)
    (second : Section (fun γ => b ⟨γ, first γ⟩)) : Section (sigmaFamily a b) :=
  fun γ => (sigmaDecode a b γ).symm ⟨first γ, second γ⟩

noncomputable def fst {Γ : Type (u + 1)} {a : SetFamily Γ}
    {b : SetFamily (Extension a)} (value : Section (sigmaFamily a b)) : Section a :=
  fun γ => (sigmaDecode a b γ (value γ)).1

noncomputable def snd {Γ : Type (u + 1)} {a : SetFamily Γ}
    {b : SetFamily (Extension a)} (value : Section (sigmaFamily a b)) :
    Section (fun γ => b ⟨γ, fst value γ⟩) :=
  fun γ => (sigmaDecode a b γ (value γ)).2

theorem fst_pair {Γ : Type (u + 1)} {a : SetFamily Γ}
    {b : SetFamily (Extension a)} (first : Section a)
    (second : Section (fun γ => b ⟨γ, first γ⟩)) : fst (pair first second) = first := by
  funext γ
  exact congrArg Sigma.fst ((sigmaDecode a b γ).apply_symm_apply ⟨first γ, second γ⟩)

theorem snd_pair {Γ : Type (u + 1)} {a : SetFamily Γ}
    {b : SetFamily (Extension a)} (first : Section a)
    (second : Section (fun γ => b ⟨γ, first γ⟩)) : HEq (snd (pair first second)) second := by
  apply Function.hfunext rfl
  intro γ γ' equal
  cases eq_of_heq equal
  exact (Sigma.mk.inj ((sigmaDecode a b γ).apply_symm_apply ⟨first γ, second γ⟩)).2

theorem pair_eta {Γ : Type (u + 1)} {a : SetFamily Γ}
    {b : SetFamily (Extension a)} (value : Section (sigmaFamily a b)) :
    pair (fst value) (snd value) = value := by
  funext γ
  exact (sigmaDecode a b γ).symm_apply_apply (value γ)

noncomputable def sums : DependentSumBeta codedCwf.{u} where
  sigma := sigmaFamily
  pair := pair
  fst := fst
  snd := snd
  fst_pair := fst_pair
  snd_pair := snd_pair

/-! ## Substitution and comprehension -/

def extensionSubstitution {Γ Δ : Type (u + 1)} (θ : Δ → Γ) (a : SetFamily Γ) :
    Extension (a ∘ θ) → Extension a := fun p => ⟨θ p.1, p.2⟩

theorem piFamily_substitution {Γ Δ : Type (u + 1)} (θ : Δ → Γ)
    (a : SetFamily Γ) (b : SetFamily (Extension a)) :
    piFamily a b ∘ θ = piFamily (a ∘ θ) (b ∘ extensionSubstitution θ a) := rfl

theorem sigmaFamily_substitution {Γ Δ : Type (u + 1)} (θ : Δ → Γ)
    (a : SetFamily Γ) (b : SetFamily (Extension a)) :
    sigmaFamily a b ∘ θ = sigmaFamily (a ∘ θ) (b ∘ extensionSubstitution θ a) := rfl

theorem lam_substitution {Γ Δ : Type (u + 1)} (θ : Δ → Γ)
    {a : SetFamily Γ} {b : SetFamily (Extension a)} (body : Section b) :
    (fun δ => lam body (θ δ)) =
      lam (fun p => body (extensionSubstitution θ a p)) := rfl

theorem app_substitution {Γ Δ : Type (u + 1)} (θ : Δ → Γ)
    {a : SetFamily Γ} {b : SetFamily (Extension a)}
    (f : Section (piFamily a b)) (argument : Section a) :
    (fun δ => app f argument (θ δ)) =
      app (b := b ∘ extensionSubstitution θ a)
        (fun δ => f (θ δ)) (fun δ => argument (θ δ)) := rfl

theorem pair_substitution {Γ Δ : Type (u + 1)} (θ : Δ → Γ)
    {a : SetFamily Γ} {b : SetFamily (Extension a)} (first : Section a)
    (second : Section (fun γ => b ⟨γ, first γ⟩)) :
    (fun δ => pair first second (θ δ)) =
      pair (b := b ∘ extensionSubstitution θ a)
        (fun δ => first (θ δ)) (fun δ => second (θ δ)) := rfl

theorem fst_substitution {Γ Δ : Type (u + 1)} (θ : Δ → Γ)
    {a : SetFamily Γ} {b : SetFamily (Extension a)}
    (value : Section (sigmaFamily a b)) :
    (fun δ => fst value (θ δ)) =
      fst (b := b ∘ extensionSubstitution θ a) (fun δ => value (θ δ)) := rfl

theorem snd_substitution {Γ Δ : Type (u + 1)} (θ : Δ → Γ)
    {a : SetFamily Γ} {b : SetFamily (Extension a)}
    (value : Section (sigmaFamily a b)) :
    (fun δ => snd value (θ δ)) =
      snd (b := b ∘ extensionSubstitution θ a) (fun δ => value (θ δ)) := rfl

/-! ## Concrete dependent computation and a false-result control -/

namespace Controls

def domain : SetFamily PUnit.{u + 2} := fun _ => ZFSetDependentProducts.Controls.two

noncomputable def codomain : SetFamily (Extension domain.{u}) :=
  fun p => ZFSetDependentProducts.Controls.varying p.2.1

/-- The value is its own argument, but the first fibre is a singleton and
the other fibre has two elements. This is genuinely dependent typing. -/
noncomputable def body : Section codomain.{u} := by
  classical
  intro p
  refine ⟨p.2.1, ?_⟩
  dsimp only [codomain, ZFSetDependentProducts.Controls.varying]
  split
  · rename_i same
    exact ZFSet.mem_singleton.mpr same
  · exact p.2.2

def zeroArgument : Section domain.{u} :=
  fun _ => ⟨∅, ZFSetDependentProducts.Controls.empty_mem_two⟩

def oneArgument : Section domain.{u} :=
  fun _ => ⟨ZFSet.powerset ∅, ZFSetDependentProducts.Controls.power_empty_mem_two⟩

theorem dependent_beta_zero :
    (app (lam body.{u}) zeroArgument PUnit.unit).1 = ∅ := by
  rw [app_lam]
  rfl

theorem dependent_beta_one :
    (app (lam body.{u}) oneArgument PUnit.unit).1 = ZFSet.powerset ∅ := by
  rw [app_lam]
  rfl

theorem wrong_constant_result :
    (app (lam body.{u}) oneArgument PUnit.unit).1 ≠ ∅ := by
  rw [dependent_beta_one]
  intro wrong
  have member : (∅ : ZFSet.{u}) ∈ ZFSet.powerset ∅ :=
    ZFSet.mem_powerset.mpr (ZFSet.empty_subset _)
  rw [wrong] at member
  exact ZFSet.notMem_empty _ member

noncomputable def paired : Section (sigmaFamily domain.{u} codomain) :=
  pair oneArgument (fun γ => body ⟨γ, oneArgument γ⟩)

theorem paired_first : fst paired.{u} = oneArgument := fst_pair _ _

theorem paired_second :
    HEq (snd paired.{u}) (fun γ => body ⟨γ, oneArgument γ⟩) := snd_pair _ _

theorem paired_reconstructed : pair (fst paired.{u}) (snd paired) = paired := pair_eta _

/-- Pullback may identify different source points. The general substitution
laws above do not assume an injective context map. -/
def forgetPoint : Elements ZFSetDependentProducts.Controls.two.{u} → PUnit.{u + 2} :=
  fun _ => PUnit.unit

theorem forgetPoint_not_injective : ¬ Function.Injective forgetPoint.{u} := by
  intro injective
  have equal := injective (a₁ := ⟨∅, ZFSetDependentProducts.Controls.empty_mem_two⟩)
    (a₂ := ⟨ZFSet.powerset ∅, ZFSetDependentProducts.Controls.power_empty_mem_two⟩) rfl
  have setsEqual := congrArg Subtype.val equal
  change (∅ : ZFSet.{u}) = ZFSet.powerset ∅ at setsEqual
  have member : (∅ : ZFSet.{u}) ∈ ZFSet.powerset ∅ :=
    ZFSet.mem_powerset.mpr (ZFSet.empty_subset _)
  rw [← setsEqual] at member
  exact ZFSet.notMem_empty _ member

theorem dependent_body_substitution :
    (fun δ => lam body.{u} (forgetPoint δ)) =
      lam (fun p => body (extensionSubstitution forgetPoint domain p)) :=
  lam_substitution forgetPoint body

end Controls

#print axioms codedCwf
#print axioms codedCwfWithTerminal
#print axioms products
#print axioms sums
#print axioms app_lam
#print axioms lam_eta
#print axioms fst_pair
#print axioms snd_pair
#print axioms pair_eta
#print axioms lam_substitution
#print axioms app_substitution
#print axioms pair_substitution
#print axioms fst_substitution
#print axioms snd_substitution
#print axioms Controls.dependent_beta_zero
#print axioms Controls.dependent_beta_one
#print axioms Controls.wrong_constant_result
#print axioms Controls.paired_reconstructed
#print axioms Controls.forgetPoint_not_injective
#print axioms Controls.dependent_body_substitution

end Mettapedia.Logic.HOL.Embedding.ZFSetContextualInterpretation
