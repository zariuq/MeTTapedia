import Mettapedia.Logic.LP.Provenance
import Mettapedia.Logic.LP.FunctionFree
import Mettapedia.Logic.PLNProvenanceWMSupportBridge
import Mettapedia.Logic.PLNScopedTrackedWhichState
import Provenance.Semirings.Which

/-!
# End-to-End Derivation Tracking Demo

A worked example for the gap described in `TASK_DERIVATION_TRACKING.md`:

1. start from a tiny Maple Court humidity chain,
2. propagate observation provenance through `T_P_K_LP` with `Which`,
3. read the result through the `KRelation -> AdditiveWorldModel` bridge,
4. embed the per-observation closures into a scoped tracked WM state,
5. forget one scope and recover the surviving evidence exactly.

## Two small, fully explicit specializations

### Ground specialization
The intended running example is the unary chain

- `PipeLeak(unit1)`
- `ShowerRunning(unit1)`
- `PipeLeak(x) -> WallHumidity(x)`
- `ShowerRunning(x) -> BathroomHumidity(x)`
- `WallHumidity(x) -> MoldRisk(x)`

For proof compactness, we specialize to the single resident unit `unit1`
and work propositionally with the five ground atoms

- `PipeLeak₁`
- `ShowerRunning₁`
- `WallHumidity₁`
- `BathroomHumidity₁`
- `MoldRisk₁`.

This is extensionally the same one-unit Maple Court chain.

### Seeded provenance step
The current `T_P_K_LP` injects raw database facts with annotation `1`.
That is perfect for generic semiring lifting, but it does *not* by itself assign
observation-specific `Which` labels to extensional facts.

So the demo uses the smallest honest wrapper:

`seededStep seed I := seed + T_P_K_LP Which ruleKB I`

where `seed` is the observation-labelled `KRelation` carrying
`{o₁}` for `PipeLeak₁` and/or `{o₂}` for `ShowerRunning₁`.

All actual rule propagation still happens through `T_P_K_LP`.

### Example-level remembering
The uploaded bundle proves the exact inverse theorem for
`toScopedTrackedWhichState`, but it does not define a named
`scopedRemember`.  This file therefore defines the tiny example-level wrapper

`rememberInScope s I W := W + toScopedTrackedWhichState s I`.

Then forgetting that scope is proved to recover the base state exactly.
-/

namespace Mettapedia.Logic.PLNDerivationTrackingDemoPropositional

open Mettapedia.Logic
open Mettapedia.Logic.LP
open Mettapedia.Logic.PLNWorldModelGeneric

/-! ## 1. The ground Maple Court signature -/

/-- The five ground predicates of the single-unit Maple Court chain. -/
inductive DemoRel
  | pipeLeak₁
  | showerRunning₁
  | wallHumidity₁
  | bathroomHumidity₁
  | moldRisk₁
  deriving DecidableEq, Fintype, Repr

/-- A function-free propositional LP signature. -/
abbrev DemoSig : LPSignature where
  constants := PUnit
  vars := PEmpty
  relationSymbols := DemoRel
  relationArity := fun _ => 0
  functionSymbols := PEmpty
  functionArity := PEmpty.elim

/-- Nullary atom constructor. -/
def atom₀ (r : DemoRel) : Atom DemoSig where
  symbol := r
  args := fun i => Fin.elim0 i

/-- Nullary ground atom constructor. -/
def gatom₀ (r : DemoRel) : GroundAtom DemoSig where
  symbol := r
  args := fun i => Fin.elim0 i

/-- Every ground atom in the demo is determined by its relation symbol. -/
theorem groundAtom_eq_gatom₀ (q : GroundAtom DemoSig) : q = gatom₀ q.symbol := by
  cases q with
  | mk r args =>
      congr
      funext i
      exact Fin.elim0 i

@[simp] theorem groundAtom_symbol_gatom₀ (r : DemoRel) :
    (gatom₀ r).symbol = r := rfl

/-! ## 2. The rule KB -/

/-- `PipeLeak₁ -> WallHumidity₁`. -/
def wallRule : Clause DemoSig where
  head := atom₀ .wallHumidity₁
  body := [atom₀ .pipeLeak₁]

/-- `ShowerRunning₁ -> BathroomHumidity₁`. -/
def bathroomRule : Clause DemoSig where
  head := atom₀ .bathroomHumidity₁
  body := [atom₀ .showerRunning₁]

/-- `WallHumidity₁ -> MoldRisk₁`. -/
def moldRule : Clause DemoSig where
  head := atom₀ .moldRisk₁
  body := [atom₀ .wallHumidity₁]

/-- Rules only; the observation-labelled seeds are injected separately. -/
def ruleKB : FinKnowledgeBase DemoSig where
  prog := [wallRule, bathroomRule, moldRule]
  db := ∅

/-! ## 3. Observation labels and provenance seeds -/

abbrev ObsIx := Fin 2
abbrev DemoKState := KRelation DemoSig (Which ObsIx)
abbrev DemoScopedState := ScopedTrackedWhichState DemoSig 2 2

def o₁ : ObsIx := ⟨0, by decide⟩
def o₂ : ObsIx := ⟨1, by decide⟩

def s₁ : Fin 2 := ⟨0, by decide⟩
def s₂ : Fin 2 := ⟨1, by decide⟩

def ev₁ : Which ObsIx := Which.wset {o₁}
def ev₂ : Which ObsIx := Which.wset {o₂}

def pipeSeed : DemoKState :=
  fun q => if q = gatom₀ .pipeLeak₁ then ev₁ else 0

def showerSeed : DemoKState :=
  fun q => if q = gatom₀ .showerRunning₁ then ev₂ else 0

def bothSeed : DemoKState := pipeSeed + showerSeed

/-- The smallest honest wrapper around `T_P_K_LP`: keep the labelled seed,
then let `T_P_K_LP` perform one round of rule propagation. -/
noncomputable def seededStep (seed : DemoKState) (I : DemoKState) : DemoKState :=
  seed + T_P_K_LP (σ := DemoSig) (Which ObsIx) ruleKB I

/-- The unique grounding of the propositional demo. -/
def g⋆ : Grounding DemoSig := fun v => PEmpty.elim v

theorem grounding_univ_singleton :
    (Finset.univ : Finset (Grounding DemoSig)) = {g⋆} := by
  ext g
  simp [g⋆]
  constructor
  · intro _
    funext v
    exact PEmpty.elim v
  · intro _
    simp

@[simp] theorem groundAtom_atom₀ (g : Grounding DemoSig) (r : DemoRel) :
    g.groundAtom (atom₀ r) = gatom₀ r := by
  rfl

/-- One-step evaluation of the demo rule KB at each named atom. -/
theorem seededStep_apply_named
    (seed I : DemoKState) (r : DemoRel) :
    seededStep seed I (gatom₀ r) =
      seed (gatom₀ r) +
        match r with
        | .pipeLeak₁ => 0
        | .showerRunning₁ => 0
        | .wallHumidity₁ => I (gatom₀ .pipeLeak₁)
        | .bathroomHumidity₁ => I (gatom₀ .showerRunning₁)
        | .moldRisk₁ => I (gatom₀ .wallHumidity₁) := by
  cases r <;>
    simp [seededStep, T_P_K_LP, ruleKB, wallRule, bathroomRule, moldRule,
      grounding_univ_singleton, atom₀, gatom₀]

/-! ## 4. Explicit closures computed by the seeded operator -/

/-- Closure generated by the leak observation alone. -/
def pipeClosure : DemoKState :=
  fun q =>
    if q = gatom₀ .pipeLeak₁ then ev₁
    else if q = gatom₀ .wallHumidity₁ then ev₁
    else if q = gatom₀ .moldRisk₁ then ev₁
    else 0

/-- Closure generated by the shower observation alone. -/
def showerClosure : DemoKState :=
  fun q =>
    if q = gatom₀ .showerRunning₁ then ev₂
    else if q = gatom₀ .bathroomHumidity₁ then ev₂
    else 0

/-- Combined closure.  No body in the program mixes the two observations, so the
joint state is just the additive merge of the two single-source closures. -/
def fullClosure : DemoKState := pipeClosure + showerClosure

/-- Two seeded rounds compute the leak-only closure exactly. -/
theorem pipeClosure_from_two_steps :
    seededStep pipeSeed (seededStep pipeSeed pipeSeed) = pipeClosure := by
  funext q
  cases q with
  | mk r args =>
      have hargs : args = (fun i => Fin.elim0 i) := by
        funext i
        exact Fin.elim0 i
      subst hargs
      cases r <;>
        simp [pipeClosure, pipeSeed, ev₁, seededStep_apply_named, gatom₀,
          o₁, o₂]

/-- Two seeded rounds compute the shower-only closure exactly. -/
theorem showerClosure_from_two_steps :
    seededStep showerSeed (seededStep showerSeed showerSeed) = showerClosure := by
  funext q
  cases q with
  | mk r args =>
      have hargs : args = (fun i => Fin.elim0 i) := by
        funext i
        exact Fin.elim0 i
      subst hargs
      cases r <;>
        simp [showerClosure, showerSeed, ev₂, seededStep_apply_named, gatom₀,
          o₁, o₂]

/-- Two seeded rounds compute the combined closure exactly. -/
theorem fullClosure_from_two_steps :
    seededStep bothSeed (seededStep bothSeed bothSeed) = fullClosure := by
  funext q
  cases q with
  | mk r args =>
      have hargs : args = (fun i => Fin.elim0 i) := by
        funext i
        exact Fin.elim0 i
      subst hargs
      cases r <;>
        simp [fullClosure, pipeClosure, showerClosure, bothSeed, pipeSeed, showerSeed,
          ev₁, ev₂, seededStep_apply_named, gatom₀, o₁, o₂, add_comm, add_left_comm,
          add_assoc]

/-- The two-round combined closure is already a fixpoint of the seeded operator. -/
theorem fullClosure_fixpoint :
    seededStep bothSeed fullClosure = fullClosure := by
  funext q
  cases q with
  | mk r args =>
      have hargs : args = (fun i => Fin.elim0 i) := by
        funext i
        exact Fin.elim0 i
      subst hargs
      cases r <;>
        simp [fullClosure, pipeClosure, showerClosure, bothSeed, pipeSeed, showerSeed,
          ev₁, ev₂, seededStep_apply_named, gatom₀, o₁, o₂, add_comm, add_left_comm,
          add_assoc]

/-! ## 5. Stage-2 query theorems: provenance visible on derived facts -/

theorem fullClosure_moldRisk :
    fullClosure (gatom₀ .moldRisk₁) = ev₁ := by
  simp [fullClosure, pipeClosure, showerClosure, ev₁]

theorem fullClosure_bathroomHumidity :
    fullClosure (gatom₀ .bathroomHumidity₁) = ev₂ := by
  simp [fullClosure, pipeClosure, showerClosure, ev₂]

/-! ## 6. Stage-3 bridge: `KRelation` is already an `AdditiveWorldModel` -/

theorem extract_fullClosure_moldRisk :
    AdditiveWorldModel.extract
      (State := DemoKState) (Query := GroundAtom DemoSig) (Ev := Which ObsIx)
      fullClosure (gatom₀ .moldRisk₁) = ev₁ := by
  simpa [fullClosure, pipeClosure, showerClosure, ev₁]


theorem extract_fullClosure_bathroomHumidity :
    AdditiveWorldModel.extract
      (State := DemoKState) (Query := GroundAtom DemoSig) (Ev := Which ObsIx)
      fullClosure (gatom₀ .bathroomHumidity₁) = ev₂ := by
  simpa [fullClosure, pipeClosure, showerClosure, ev₂]

/-! ## 7. Scoped tracked WM state -/

def pipeScoped : DemoScopedState :=
  toScopedTrackedWhichState (σ := DemoSig) (n := 2) (m := 2) s₁ pipeClosure


def showerScoped : DemoScopedState :=
  toScopedTrackedWhichState (σ := DemoSig) (n := 2) (m := 2) s₂ showerClosure

/-- The full scoped WM state is the sum of the two scoped observation closures. -/
def fullScoped : DemoScopedState := showerScoped + pipeScoped

/-- Extraction from one scope-labelled tracked state recovers the underlying
`Which` K-relation exactly. -/
theorem extract_toScopedTrackedWhichState
    (s : Fin 2) (I : DemoKState) (q : GroundAtom DemoSig) :
    AdditiveWorldModel.extract
      (State := DemoScopedState) (Query := GroundAtom DemoSig) (Ev := Which ObsIx)
      (toScopedTrackedWhichState (σ := DemoSig) (n := 2) (m := 2) s I) q = I q := by
  cases hI : I q with
  | wbot =>
      show scopedTrackedEvidence
        (toScopedTrackedWhichState (σ := DemoSig) (n := 2) (m := 2) s I) q = 0
      unfold scopedTrackedEvidence scopedTrackedUnionSupport toScopedTrackedWhichState
      simp [hI]
  | wset support =>
      have hs :
          scopedTrackedUnionSupport
            (toScopedTrackedWhichState (σ := DemoSig) (n := 2) (m := 2) s I) q ≠ ∅ := by
        unfold scopedTrackedUnionSupport toScopedTrackedWhichState
        simp [hI]
      show scopedTrackedEvidence
          (toScopedTrackedWhichState (σ := DemoSig) (n := 2) (m := 2) s I) q = Which.wset support
      rw [scopedTrackedEvidence_eq_wset_of_support_ne_empty _ _ hs]
      unfold scopedTrackedPayloadSupport scopedTrackedUnionSupport toScopedTrackedWhichState
      ext i
      simp [hI]

/-- The scoped tracked state exposes the same evidence as the bridged `KRelation`. -/
theorem extract_fullScoped_eq_fullClosure (q : GroundAtom DemoSig) :
    AdditiveWorldModel.extract
      (State := DemoScopedState) (Query := GroundAtom DemoSig) (Ev := Which ObsIx)
      fullScoped q =
    AdditiveWorldModel.extract
      (State := DemoKState) (Query := GroundAtom DemoSig) (Ev := Which ObsIx)
      fullClosure q := by
  unfold fullScoped fullClosure
  rw [AdditiveWorldModel.extract_add'
      (State := DemoScopedState) (Query := GroundAtom DemoSig) (Ev := Which ObsIx)
      showerScoped pipeScoped q]
  rw [extract_toScopedTrackedWhichState, extract_toScopedTrackedWhichState]
  simp [add_comm, add_left_comm, add_assoc]

theorem extract_fullScoped_moldRisk :
    AdditiveWorldModel.extract
      (State := DemoScopedState) (Query := GroundAtom DemoSig) (Ev := Which ObsIx)
      fullScoped (gatom₀ .moldRisk₁) = ev₁ := by
  have h := extract_fullScoped_eq_fullClosure (gatom₀ .moldRisk₁)
  simpa using h.trans extract_fullClosure_moldRisk


theorem extract_fullScoped_bathroomHumidity :
    AdditiveWorldModel.extract
      (State := DemoScopedState) (Query := GroundAtom DemoSig) (Ev := Which ObsIx)
      fullScoped (gatom₀ .bathroomHumidity₁) = ev₂ := by
  have h := extract_fullScoped_eq_fullClosure (gatom₀ .bathroomHumidity₁)
  simpa using h.trans extract_fullClosure_bathroomHumidity

/-! ## 8. Scope cleanliness lemmas -/

theorem toScoped_scopeClean_of_ne
    (s t : Fin 2) (h : t ≠ s) (I : DemoKState) :
    ScopeClean
      (toScopedTrackedWhichState (σ := DemoSig) (n := 2) (m := 2) t I)
      ({s} : Finset (Fin 2)) := by
  intro q chunk hchunk
  unfold toScopedTrackedWhichState at hchunk
  cases hI : I q with
  | wbot =>
      simp [hI] at hchunk
  | wset support =>
      simp [hI] at hchunk
      rcases hchunk with rfl
      simp [h]


theorem showerScoped_clean_s₁ : ScopeClean showerScoped ({s₁} : Finset (Fin 2)) := by
  exact toScoped_scopeClean_of_ne s₁ s₂ (by decide) showerClosure


theorem pipeScoped_clean_s₂ : ScopeClean pipeScoped ({s₂} : Finset (Fin 2)) := by
  exact toScoped_scopeClean_of_ne s₂ s₁ (by decide) pipeClosure

/-! ## 9. Stage-4 forgetting -/

/-- Forgeting the leak scope removes the leak-derived chain and keeps the shower chain. -/
theorem forget_s₁_exact :
    forgetScopedByScope ({s₁} : Finset (Fin 2)) fullScoped = showerScoped := by
  unfold fullScoped pipeScoped
  exact toScopedTrackedWhichState_forget_exactInverse_of_clean
    (σ := DemoSig) (n := 2) (m := 2) s₁ pipeClosure showerScoped showerScoped_clean_s₁

/-- Forgetting the shower scope removes the shower-derived chain and keeps the leak chain. -/
theorem forget_s₂_exact :
    forgetScopedByScope ({s₂} : Finset (Fin 2)) fullScoped = pipeScoped := by
  have h :=
    toScopedTrackedWhichState_forget_exactInverse_of_clean
      (σ := DemoSig) (n := 2) (m := 2) s₂ showerClosure pipeScoped pipeScoped_clean_s₂
  simpa [fullScoped, pipeScoped, showerScoped, add_comm, add_left_comm, add_assoc] using h

/-- Forgetting `o₁` kills `MoldRisk₁`. -/
theorem forget_o₁_extract_moldRisk :
    AdditiveWorldModel.extract
      (State := DemoScopedState) (Query := GroundAtom DemoSig) (Ev := Which ObsIx)
      (forgetScopedByScope ({s₁} : Finset (Fin 2)) fullScoped)
      (gatom₀ .moldRisk₁) = 0 := by
  rw [forget_s₁_exact]
  simpa [showerClosure] using
    (extract_toScopedTrackedWhichState s₂ showerClosure (gatom₀ .moldRisk₁))

/-- Forgetting `o₁` preserves `BathroomHumidity₁`. -/
theorem forget_o₁_extract_bathroomHumidity :
    AdditiveWorldModel.extract
      (State := DemoScopedState) (Query := GroundAtom DemoSig) (Ev := Which ObsIx)
      (forgetScopedByScope ({s₁} : Finset (Fin 2)) fullScoped)
      (gatom₀ .bathroomHumidity₁) = ev₂ := by
  rw [forget_s₁_exact]
  simpa [showerClosure, ev₂] using
    (extract_toScopedTrackedWhichState s₂ showerClosure (gatom₀ .bathroomHumidity₁))

/-- Forgetting `o₂` kills `BathroomHumidity₁`. -/
theorem forget_o₂_extract_bathroomHumidity :
    AdditiveWorldModel.extract
      (State := DemoScopedState) (Query := GroundAtom DemoSig) (Ev := Which ObsIx)
      (forgetScopedByScope ({s₂} : Finset (Fin 2)) fullScoped)
      (gatom₀ .bathroomHumidity₁) = 0 := by
  rw [forget_s₂_exact]
  simpa [pipeClosure] using
    (extract_toScopedTrackedWhichState s₁ pipeClosure (gatom₀ .bathroomHumidity₁))

/-- Forgetting `o₂` preserves `MoldRisk₁`. -/
theorem forget_o₂_extract_moldRisk :
    AdditiveWorldModel.extract
      (State := DemoScopedState) (Query := GroundAtom DemoSig) (Ev := Which ObsIx)
      (forgetScopedByScope ({s₂} : Finset (Fin 2)) fullScoped)
      (gatom₀ .moldRisk₁) = ev₁ := by
  rw [forget_s₂_exact]
  simpa [pipeClosure, ev₁] using
    (extract_toScopedTrackedWhichState s₁ pipeClosure (gatom₀ .moldRisk₁))

/-! ## 10. Stage-5 conservation: forgetting after remembering is identity -/

/-- Example-level remembering wrapper: add one scope-labelled closure. -/
def rememberInScope (s : Fin 2) (I : DemoKState) (W : DemoScopedState) : DemoScopedState :=
  W + toScopedTrackedWhichState (σ := DemoSig) (n := 2) (m := 2) s I

/-- Remember the leak closure in scope `s₁`, then forget `s₁`: identity on the shower base state. -/
theorem forget_remember_s₁_identity :
    forgetScopedByScope ({s₁} : Finset (Fin 2))
      (rememberInScope s₁ pipeClosure showerScoped) = showerScoped := by
  unfold rememberInScope
  exact toScopedTrackedWhichState_forget_exactInverse_of_clean
    (σ := DemoSig) (n := 2) (m := 2) s₁ pipeClosure showerScoped showerScoped_clean_s₁

/-- Remember the shower closure in scope `s₂`, then forget `s₂`: identity on the leak base state. -/
theorem forget_remember_s₂_identity :
    forgetScopedByScope ({s₂} : Finset (Fin 2))
      (rememberInScope s₂ showerClosure pipeScoped) = pipeScoped := by
  unfold rememberInScope
  exact toScopedTrackedWhichState_forget_exactInverse_of_clean
    (σ := DemoSig) (n := 2) (m := 2) s₂ showerClosure pipeScoped pipeScoped_clean_s₂

end Mettapedia.Logic.PLNDerivationTrackingDemoPropositional
