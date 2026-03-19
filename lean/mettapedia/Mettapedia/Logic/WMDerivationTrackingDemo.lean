import Mettapedia.Logic.LP.Provenance
import Mettapedia.Logic.PLNProvenanceWMSupportBridge
import Mettapedia.Logic.PLNScopedTrackedWhichState
import Mettapedia.Logic.PLNProvenanceInference
import Provenance.Semirings.Which

/-!
# End-to-End Derivation Tracking Demo

A worked example: provenance flow from LP rules through the actual `T_P_K_LP`
operator with `Which`, into WM extraction, and then into scoped forgetting.

## Design note

`T_P_K_LP` injects plain semiring `1` for EDB facts. For the `Which` semiring,
that means `wset ∅`, which does **not** carry source labels like `{o₁}` and
`{o₂}`. So the example uses a *seeded provenance closure*
`seed + T_P_K_LP ...` rather than raw iteration from the empty K-relation.
This keeps the example honest with the current code while still exercising
the actual LP provenance operator on every derived consequence.
-/

namespace Mettapedia.Logic.WMDerivationTrackingDemo

open Mettapedia.Logic
open Mettapedia.Logic.LP
open Mettapedia.Logic.PLNWorldModelGeneric

/-! ## 1. Signature and atoms -/

inductive MapleCourtRel
  | pipeLeak
  | showerRunning
  | wallHumidity
  | bathroomHumidity
  | moldRisk
  deriving DecidableEq, Fintype

abbrev MapleCourtConst := Unit
abbrev MapleCourtVar := Unit

def mapleCourtSig : LPSignature where
  constants := MapleCourtConst
  vars := MapleCourtVar
  relationSymbols := MapleCourtRel
  relationArity := fun _ => 1
  functionSymbols := PEmpty
  functionArity := PEmpty.elim

instance : IsEmpty mapleCourtSig.functionSymbols := inferInstanceAs (IsEmpty PEmpty)
instance : DecidableEq mapleCourtSig.constants := inferInstanceAs (DecidableEq Unit)
instance : DecidableEq mapleCourtSig.vars := inferInstanceAs (DecidableEq Unit)
instance : DecidableEq mapleCourtSig.relationSymbols := inferInstanceAs (DecidableEq MapleCourtRel)
instance : Fintype mapleCourtSig.constants := inferInstanceAs (Fintype Unit)
instance : Fintype mapleCourtSig.vars := inferInstanceAs (Fintype Unit)

def unit1 : GroundTerm mapleCourtSig := .const ()
def x : Term mapleCourtSig := .var ()

def unaryAtom (r : MapleCourtRel) (t : Term mapleCourtSig) : Atom mapleCourtSig where
  symbol := r; args := fun _ => t

def unaryGroundAtom (r : MapleCourtRel) : GroundAtom mapleCourtSig :=
  GroundAtom.ofFinArgs r (fun _ => ())

def pipeLeakX : Atom mapleCourtSig := unaryAtom .pipeLeak x
def showerRunningX : Atom mapleCourtSig := unaryAtom .showerRunning x
def wallHumidityX : Atom mapleCourtSig := unaryAtom .wallHumidity x
def bathroomHumidityX : Atom mapleCourtSig := unaryAtom .bathroomHumidity x
def moldRiskX : Atom mapleCourtSig := unaryAtom .moldRisk x

def pipeLeak₁ : GroundAtom mapleCourtSig := unaryGroundAtom .pipeLeak
def showerRunning₁ : GroundAtom mapleCourtSig := unaryGroundAtom .showerRunning
def wallHumidity₁ : GroundAtom mapleCourtSig := unaryGroundAtom .wallHumidity
def bathroomHumidity₁ : GroundAtom mapleCourtSig := unaryGroundAtom .bathroomHumidity
def moldRisk₁ : GroundAtom mapleCourtSig := unaryGroundAtom .moldRisk

/-! ## 2. LP program (3 rules, no EDB facts) -/

def rulePipeLeakToWallHumidity : Clause mapleCourtSig where
  head := wallHumidityX; body := [pipeLeakX]

def ruleShowerToBathroomHumidity : Clause mapleCourtSig where
  head := bathroomHumidityX; body := [showerRunningX]

def ruleWallToMoldRisk : Clause mapleCourtSig where
  head := moldRiskX; body := [wallHumidityX]

def mapleCourtProg : Program mapleCourtSig :=
  [rulePipeLeakToWallHumidity, ruleShowerToBathroomHumidity, ruleWallToMoldRisk]

-- No EDB facts — observations enter as labelled seeds via T_P_K_LP_seeded

/-! ## 3. Observation seeds -/

def oPipe : Fin 2 := 0
def oShower : Fin 2 := 1
def srcPipe : Finset (Fin 2) := {oPipe}
def srcShower : Finset (Fin 2) := {oShower}
def pipeProv : Which (Fin 2) := Which.wset srcPipe
def showerProv : Which (Fin 2) := Which.wset srcShower

def seedOf (fact : GroundAtom mapleCourtSig) (src : Finset (Fin 2)) :
    KRelation mapleCourtSig (Which (Fin 2)) :=
  fun a => if a = fact then Which.wset src else 0

def pipeSeed : KRelation mapleCourtSig (Which (Fin 2)) := seedOf pipeLeak₁ srcPipe
def showerSeed : KRelation mapleCourtSig (Which (Fin 2)) := seedOf showerRunning₁ srcShower

@[simp] theorem pipeSeed_pipeLeak : pipeSeed pipeLeak₁ = pipeProv := by
  simp [pipeSeed, seedOf, pipeProv]
@[simp] theorem pipeSeed_showerRunning : pipeSeed showerRunning₁ = 0 := by
  simp only [pipeSeed, seedOf]; exact if_neg (by decide)
@[simp] theorem pipeSeed_wallHumidity : pipeSeed wallHumidity₁ = 0 := by
  simp only [pipeSeed, seedOf]; exact if_neg (by decide)
@[simp] theorem pipeSeed_bathroomHumidity : pipeSeed bathroomHumidity₁ = 0 := by
  simp only [pipeSeed, seedOf]; exact if_neg (by decide)
@[simp] theorem pipeSeed_moldRisk : pipeSeed moldRisk₁ = 0 := by
  simp only [pipeSeed, seedOf]; exact if_neg (by decide)

@[simp] theorem showerSeed_pipeLeak : showerSeed pipeLeak₁ = 0 := by
  simp only [showerSeed, seedOf]; exact if_neg (by decide)
@[simp] theorem showerSeed_showerRunning : showerSeed showerRunning₁ = showerProv := by
  simp [showerSeed, seedOf, showerProv]
@[simp] theorem showerSeed_wallHumidity : showerSeed wallHumidity₁ = 0 := by
  simp only [showerSeed, seedOf]; exact if_neg (by decide)
@[simp] theorem showerSeed_bathroomHumidity : showerSeed bathroomHumidity₁ = 0 := by
  simp only [showerSeed, seedOf]; exact if_neg (by decide)
@[simp] theorem showerSeed_moldRisk : showerSeed moldRisk₁ = 0 := by
  simp only [showerSeed, seedOf]; exact if_neg (by decide)

/-! ## 4. Unique grounding -/

instance : Unique (Grounding mapleCourtSig) where
  default := fun _ => unit1
  uniq g := by
    funext v; cases v
    cases h : g () with
    | const c => cases c; rfl
    | app f ts => cases f

@[simp] theorem default_grounds_unary_atom (r : MapleCourtRel) :
    (default : Grounding mapleCourtSig).groundAtom (unaryAtom r x) = unaryGroundAtom r := rfl

/-! ## 5. T_P_K_LP_seeded one-step equations

The seeded operator `T_P_K_LP_seeded` directly takes labelled observations as a
`KRelation`-valued seed, avoiding the Boolean-EDB workaround. For the Maple Court
program, with only one grounding, `Fintype.sum_unique` collapses the sum. -/

private theorem T_P_K_LP_seeded_core
    (seed I : KRelation mapleCourtSig (Which (Fin 2)))
    (a : GroundAtom mapleCourtSig) :
    T_P_K_LP_seeded (Which (Fin 2)) mapleCourtProg seed I a =
      seed a +
      ((if (default : Grounding mapleCourtSig).groundAtom wallHumidityX = a then
        I ((default : Grounding mapleCourtSig).groundAtom pipeLeakX) else 0) +
      ((if (default : Grounding mapleCourtSig).groundAtom bathroomHumidityX = a then
        I ((default : Grounding mapleCourtSig).groundAtom showerRunningX) else 0) +
      (if (default : Grounding mapleCourtSig).groundAtom moldRiskX = a then
        I ((default : Grounding mapleCourtSig).groundAtom wallHumidityX) else 0))) := by
  classical
  unfold T_P_K_LP_seeded mapleCourtProg
  rw [Fintype.sum_unique]
  simp only [List.map, List.sum_cons, List.sum_nil, add_zero,
    rulePipeLeakToWallHumidity, ruleShowerToBathroomHumidity, ruleWallToMoldRisk,
    Clause.mk, List.prod_cons, List.prod_nil, mul_one]

theorem T_P_K_LP_seeded_pipeLeak
    (seed I : KRelation mapleCourtSig (Which (Fin 2))) :
    T_P_K_LP_seeded (Which (Fin 2)) mapleCourtProg seed I pipeLeak₁ = seed pipeLeak₁ := by
  rw [T_P_K_LP_seeded_core]
  simp only [default_grounds_unary_atom, wallHumidityX, pipeLeakX, bathroomHumidityX,
    showerRunningX, moldRiskX, pipeLeak₁, unaryGroundAtom]
  have h1 : wallHumidity₁ ≠ pipeLeak₁ := by decide
  have h2 : bathroomHumidity₁ ≠ pipeLeak₁ := by decide
  have h3 : moldRisk₁ ≠ pipeLeak₁ := by decide
  simp only [wallHumidity₁, bathroomHumidity₁, moldRisk₁, pipeLeak₁, unaryGroundAtom] at h1 h2 h3
  simp [h1, h2, h3]

theorem T_P_K_LP_seeded_showerRunning
    (seed I : KRelation mapleCourtSig (Which (Fin 2))) :
    T_P_K_LP_seeded (Which (Fin 2)) mapleCourtProg seed I showerRunning₁ =
      seed showerRunning₁ := by
  rw [T_P_K_LP_seeded_core]
  simp only [default_grounds_unary_atom, wallHumidityX, pipeLeakX, bathroomHumidityX,
    showerRunningX, moldRiskX, showerRunning₁, unaryGroundAtom]
  have h1 : wallHumidity₁ ≠ showerRunning₁ := by decide
  have h2 : bathroomHumidity₁ ≠ showerRunning₁ := by decide
  have h3 : moldRisk₁ ≠ showerRunning₁ := by decide
  simp only [wallHumidity₁, bathroomHumidity₁, moldRisk₁, showerRunning₁, unaryGroundAtom] at h1 h2 h3
  simp [h1, h2, h3]

theorem T_P_K_LP_seeded_wallHumidity
    (seed I : KRelation mapleCourtSig (Which (Fin 2))) :
    T_P_K_LP_seeded (Which (Fin 2)) mapleCourtProg seed I wallHumidity₁ =
      seed wallHumidity₁ + I pipeLeak₁ := by
  rw [T_P_K_LP_seeded_core]
  simp only [default_grounds_unary_atom, wallHumidityX, pipeLeakX, bathroomHumidityX,
    showerRunningX, moldRiskX, wallHumidity₁, pipeLeak₁, unaryGroundAtom]
  have h1 : bathroomHumidity₁ ≠ wallHumidity₁ := by decide
  have h2 : moldRisk₁ ≠ wallHumidity₁ := by decide
  simp only [bathroomHumidity₁, moldRisk₁, wallHumidity₁, unaryGroundAtom] at h1 h2
  simp [h1, h2]

theorem T_P_K_LP_seeded_bathroomHumidity
    (seed I : KRelation mapleCourtSig (Which (Fin 2))) :
    T_P_K_LP_seeded (Which (Fin 2)) mapleCourtProg seed I bathroomHumidity₁ =
      seed bathroomHumidity₁ + I showerRunning₁ := by
  rw [T_P_K_LP_seeded_core]
  simp only [default_grounds_unary_atom, wallHumidityX, pipeLeakX, bathroomHumidityX,
    showerRunningX, moldRiskX, bathroomHumidity₁, showerRunning₁, unaryGroundAtom]
  have h1 : wallHumidity₁ ≠ bathroomHumidity₁ := by decide
  have h2 : moldRisk₁ ≠ bathroomHumidity₁ := by decide
  simp only [wallHumidity₁, moldRisk₁, bathroomHumidity₁, unaryGroundAtom] at h1 h2
  simp [h1, h2]

theorem T_P_K_LP_seeded_moldRisk
    (seed I : KRelation mapleCourtSig (Which (Fin 2))) :
    T_P_K_LP_seeded (Which (Fin 2)) mapleCourtProg seed I moldRisk₁ =
      seed moldRisk₁ + I wallHumidity₁ := by
  rw [T_P_K_LP_seeded_core]
  simp only [default_grounds_unary_atom, wallHumidityX, pipeLeakX, bathroomHumidityX,
    showerRunningX, moldRiskX, moldRisk₁, wallHumidity₁, unaryGroundAtom]
  have h1 : wallHumidity₁ ≠ moldRisk₁ := by decide
  have h2 : bathroomHumidity₁ ≠ moldRisk₁ := by decide
  simp only [wallHumidity₁, bathroomHumidity₁, moldRisk₁, unaryGroundAtom] at h1 h2
  simp [h1, h2]

/-! ## 6. Two-round seeded closure via T_P_K_LP_seeded -/

/-- Two rounds of `T_P_K_LP_seeded`: enough for the longest chain
    PipeLeak → WallHumidity → MoldRisk. -/
noncomputable def closure2 (seed : KRelation mapleCourtSig (Which (Fin 2))) :=
  T_P_K_LP_seeded (Which (Fin 2)) mapleCourtProg seed
    (T_P_K_LP_seeded (Which (Fin 2)) mapleCourtProg seed seed)

noncomputable def pipeClosure := closure2 pipeSeed
noncomputable def showerClosure := closure2 showerSeed

/-! ## 7. Branch-local provenance results -/

/-- Reduction lemma: `closure2 seed a` expands to seed + IDB(seed + IDB(seed)). -/
private theorem closure_apply (seed : KRelation mapleCourtSig (Which (Fin 2)))
    (a : GroundAtom mapleCourtSig) :
    closure2 seed a =
      seed a + (∑ g : Grounding mapleCourtSig,
        (mapleCourtProg.map (fun r =>
          if g.groundAtom r.head = a then
            (r.body.map (fun b =>
              T_P_K_LP_seeded (Which (Fin 2)) mapleCourtProg seed seed (g.groundAtom b))).prod
          else 0)).sum) := rfl

theorem pipeClosure_pipeLeak : pipeClosure pipeLeak₁ = pipeProv := by
  simp only [pipeClosure, closure2, T_P_K_LP_seeded_pipeLeak]; simp

theorem pipeClosure_wallHumidity : pipeClosure wallHumidity₁ = pipeProv := by
  simp only [pipeClosure, closure2, T_P_K_LP_seeded_wallHumidity, T_P_K_LP_seeded_pipeLeak]
  simp

theorem pipeClosure_moldRisk : pipeClosure moldRisk₁ = pipeProv := by
  simp only [pipeClosure, closure2, T_P_K_LP_seeded_moldRisk, T_P_K_LP_seeded_wallHumidity,
    T_P_K_LP_seeded_pipeLeak]; simp

theorem pipeClosure_bathroomHumidity_zero : pipeClosure bathroomHumidity₁ = 0 := by
  simp only [pipeClosure, closure2, T_P_K_LP_seeded_bathroomHumidity,
    T_P_K_LP_seeded_showerRunning]; simp

theorem showerClosure_showerRunning : showerClosure showerRunning₁ = showerProv := by
  simp only [showerClosure, closure2, T_P_K_LP_seeded_showerRunning]; simp

theorem showerClosure_bathroomHumidity : showerClosure bathroomHumidity₁ = showerProv := by
  simp only [showerClosure, closure2, T_P_K_LP_seeded_bathroomHumidity,
    T_P_K_LP_seeded_showerRunning]; simp

theorem showerClosure_wallHumidity_zero : showerClosure wallHumidity₁ = 0 := by
  simp only [showerClosure, closure2, T_P_K_LP_seeded_wallHumidity, T_P_K_LP_seeded_pipeLeak]
  simp

theorem showerClosure_moldRisk_zero : showerClosure moldRisk₁ = 0 := by
  simp only [showerClosure, closure2, T_P_K_LP_seeded_moldRisk, T_P_K_LP_seeded_wallHumidity,
    T_P_K_LP_seeded_pipeLeak]; simp

/-! ## 8. Full state and WM extraction -/

noncomputable def fullState : KRelation mapleCourtSig (Which (Fin 2)) :=
  pipeClosure + showerClosure

private theorem fullState_apply (a : GroundAtom mapleCourtSig) :
    fullState a = pipeClosure a + showerClosure a := rfl

theorem fullState_moldRisk : fullState moldRisk₁ = pipeProv := by
  rw [fullState_apply, pipeClosure_moldRisk, showerClosure_moldRisk_zero]; simp [add_zero]

theorem fullState_bathroomHumidity : fullState bathroomHumidity₁ = showerProv := by
  rw [fullState_apply, pipeClosure_bathroomHumidity_zero, showerClosure_bathroomHumidity]
  simp [add_zero]

theorem extract_fullState_moldRisk :
    AdditiveWorldModel.extract
      (State := KRelation mapleCourtSig (Which (Fin 2)))
      (Query := GroundAtom mapleCourtSig)
      (Ev := Which (Fin 2))
      fullState moldRisk₁ = pipeProv := by
  simpa using fullState_moldRisk

theorem extract_fullState_bathroomHumidity :
    AdditiveWorldModel.extract
      (State := KRelation mapleCourtSig (Which (Fin 2)))
      (Query := GroundAtom mapleCourtSig)
      (Ev := Which (Fin 2))
      fullState bathroomHumidity₁ = showerProv := by
  simpa using fullState_bathroomHumidity

/-! ## 9. Scoped tracked state -/

def sPipe : Fin 2 := 0
def sShower : Fin 2 := 1
def scopePipe : Finset (Fin 2) := {sPipe}
def scopeShower : Finset (Fin 2) := {sShower}

noncomputable def scopedPipe : ScopedTrackedWhichState mapleCourtSig 2 2 :=
  toScopedTrackedWhichState (σ := mapleCourtSig) (n := 2) (m := 2) sPipe pipeClosure

noncomputable def scopedShower : ScopedTrackedWhichState mapleCourtSig 2 2 :=
  toScopedTrackedWhichState (σ := mapleCourtSig) (n := 2) (m := 2) sShower showerClosure

noncomputable def scopedFull : ScopedTrackedWhichState mapleCourtSig 2 2 :=
  scopedPipe + scopedShower

theorem scopedTrackedEvidence_toScopedTrackedWhichState_eq
    (s : Fin 2) (I : KRelation mapleCourtSig (Which (Fin 2)))
    (q : GroundAtom mapleCourtSig) :
    scopedTrackedEvidence
      (toScopedTrackedWhichState (σ := mapleCourtSig) (n := 2) (m := 2) s I) q = I q := by
  cases hI : I q with
  | wbot =>
      show scopedTrackedEvidence
        (toScopedTrackedWhichState (σ := mapleCourtSig) (n := 2) (m := 2) s I) q = 0
      unfold scopedTrackedEvidence scopedTrackedUnionSupport toScopedTrackedWhichState
      simp [hI]
  | wset support =>
      have hs : scopedTrackedUnionSupport
            (toScopedTrackedWhichState (σ := mapleCourtSig) (n := 2) (m := 2) s I) q ≠ ∅ := by
        unfold scopedTrackedUnionSupport toScopedTrackedWhichState; simp [hI]
      rw [scopedTrackedEvidence_eq_wset_of_support_ne_empty _ _ hs]
      unfold scopedTrackedPayloadSupport scopedTrackedUnionSupport toScopedTrackedWhichState
      simp [hI]; ext x; simp [Finset.mem_biUnion, Finset.mem_image]
      constructor
      · rintro ⟨a, (⟨hm, rfl⟩ | ⟨hm, rfl⟩), hxa⟩ <;> simp_all
      · intro hx; exact ⟨some x, by fin_cases x <;> simp_all, by simp⟩

theorem scopeClean_other_singleton (s t : Fin 2) (hst : t ≠ s)
    (I : KRelation mapleCourtSig (Which (Fin 2))) :
    ScopeClean
      (toScopedTrackedWhichState (σ := mapleCourtSig) (n := 2) (m := 2) t I)
      ({s} : Finset (Fin 2)) := by
  intro q chunk hchunk
  unfold toScopedTrackedWhichState at hchunk
  cases hI : I q with
  | wbot => simp [hI] at hchunk
  | wset support => simp [hI] at hchunk; rcases hchunk with rfl; simp [hst]

/-! ## 10. Scoped forgetting -/

theorem forget_pipe_scope :
    forgetScopedByScope scopePipe scopedFull = scopedShower := by
  show forgetScopedByScope {sPipe}
    (toScopedTrackedWhichState sPipe pipeClosure + toScopedTrackedWhichState sShower showerClosure) =
    toScopedTrackedWhichState sShower showerClosure
  rw [add_comm]
  exact forgetScopedByScope_exactInverse_of_supported_of_clean
    (hclean := scopeClean_other_singleton sPipe sShower (by decide) showerClosure)
    (hsupp := toScopedTrackedWhichState_supportedInSingleton
      (σ := mapleCourtSig) (n := 2) (m := 2) (s := sPipe) pipeClosure)

theorem forget_pipe_scope_moldRisk_zero :
    scopedTrackedEvidence (forgetScopedByScope scopePipe scopedFull) moldRisk₁ = 0 := by
  simp only [forget_pipe_scope, scopedShower]; rw [scopedTrackedEvidence_toScopedTrackedWhichState_eq]
  exact showerClosure_moldRisk_zero

theorem forget_pipe_scope_bathroomHumidity :
    scopedTrackedEvidence (forgetScopedByScope scopePipe scopedFull) bathroomHumidity₁ =
      showerProv := by
  simp only [forget_pipe_scope, scopedShower]; rw [scopedTrackedEvidence_toScopedTrackedWhichState_eq]
  exact showerClosure_bathroomHumidity

theorem forget_shower_scope :
    forgetScopedByScope scopeShower scopedFull = scopedPipe := by
  show forgetScopedByScope {sShower}
    (toScopedTrackedWhichState sPipe pipeClosure + toScopedTrackedWhichState sShower showerClosure) =
    toScopedTrackedWhichState sPipe pipeClosure
  exact forgetScopedByScope_exactInverse_of_supported_of_clean
    (hclean := scopeClean_other_singleton sShower sPipe (by decide) pipeClosure)
    (hsupp := toScopedTrackedWhichState_supportedInSingleton
      (σ := mapleCourtSig) (n := 2) (m := 2) (s := sShower) showerClosure)

theorem forget_shower_scope_bathroomHumidity_zero :
    scopedTrackedEvidence (forgetScopedByScope scopeShower scopedFull) bathroomHumidity₁ = 0 := by
  simp only [forget_shower_scope, scopedPipe]; rw [scopedTrackedEvidence_toScopedTrackedWhichState_eq]
  exact pipeClosure_bathroomHumidity_zero

theorem forget_shower_scope_moldRisk :
    scopedTrackedEvidence (forgetScopedByScope scopeShower scopedFull) moldRisk₁ = pipeProv := by
  simp only [forget_shower_scope, scopedPipe]; rw [scopedTrackedEvidence_toScopedTrackedWhichState_eq]
  exact pipeClosure_moldRisk

/-! ## 11. Conservation -/

noncomputable def scopedRemember (s : Fin 2)
    (I : KRelation mapleCourtSig (Which (Fin 2)))
    (W : ScopedTrackedWhichState mapleCourtSig 2 2) :
    ScopedTrackedWhichState mapleCourtSig 2 2 :=
  W + toScopedTrackedWhichState (σ := mapleCourtSig) (n := 2) (m := 2) s I

theorem forget_after_remember_pipe_is_id :
    forgetScopedByScope scopePipe
      (scopedRemember sPipe pipeClosure scopedShower) = scopedShower := by
  show forgetScopedByScope {sPipe}
    (toScopedTrackedWhichState sShower showerClosure +
     toScopedTrackedWhichState sPipe pipeClosure) =
    toScopedTrackedWhichState sShower showerClosure
  exact forgetScopedByScope_exactInverse_of_supported_of_clean
    (hclean := scopeClean_other_singleton sPipe sShower (by decide) showerClosure)
    (hsupp := toScopedTrackedWhichState_supportedInSingleton
      (σ := mapleCourtSig) (n := 2) (m := 2) (s := sPipe) pipeClosure)

theorem forget_after_remember_shower_is_id :
    forgetScopedByScope scopeShower
      (scopedRemember sShower showerClosure scopedPipe) = scopedPipe := by
  show forgetScopedByScope {sShower}
    (toScopedTrackedWhichState sPipe pipeClosure +
     toScopedTrackedWhichState sShower showerClosure) =
    toScopedTrackedWhichState sPipe pipeClosure
  exact forgetScopedByScope_exactInverse_of_supported_of_clean
    (hclean := scopeClean_other_singleton sShower sPipe (by decide) pipeClosure)
    (hsupp := toScopedTrackedWhichState_supportedInSingleton
      (σ := mapleCourtSig) (n := 2) (m := 2) (s := sShower) showerClosure)

/-! ## 12. End-to-end summary -/

theorem end_to_end_summary :
    fullState moldRisk₁ = pipeProv ∧
    fullState bathroomHumidity₁ = showerProv ∧
    scopedTrackedEvidence (forgetScopedByScope scopePipe scopedFull) moldRisk₁ = 0 ∧
    scopedTrackedEvidence (forgetScopedByScope scopePipe scopedFull) bathroomHumidity₁ = showerProv ∧
    scopedTrackedEvidence (forgetScopedByScope scopeShower scopedFull) bathroomHumidity₁ = 0 ∧
    scopedTrackedEvidence (forgetScopedByScope scopeShower scopedFull) moldRisk₁ = pipeProv :=
  ⟨fullState_moldRisk, fullState_bathroomHumidity,
    forget_pipe_scope_moldRisk_zero, forget_pipe_scope_bathroomHumidity,
    forget_shower_scope_bathroomHumidity_zero, forget_shower_scope_moldRisk⟩

end Mettapedia.Logic.WMDerivationTrackingDemo
