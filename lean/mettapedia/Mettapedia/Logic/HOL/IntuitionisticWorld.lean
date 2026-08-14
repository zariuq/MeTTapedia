import Mettapedia.Logic.HOL.WitnessedWorld

/-!
# Intuitionistic canonical worlds

The classical `ClosedTheorySet.World` includes a same-world `all_counterexample`
field.  For the EM-free route we keep the constructive core only: deductive
closure, consistency, disjunction primeness, and Henkin witnesses for
existentials.  Universal counterexamples are instead produced by passing to a
prime extension that omits a fresh instance.
-/

namespace Mettapedia.Logic.HOL

open Mettapedia.Logic.HOL.WithParams

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

namespace ClosedTheorySet

/-- The EM-free canonical-theory state used as a world in the future Kripke
semantics: prime, deductively closed, consistent, and existentially witnessed. -/
structure IntuitionisticWorld (Const : Ty Base → Type v) where
  carrier : ClosedTheorySet Const
  closed : DeductivelyClosed (Const := Const) carrier
  consistent : Consistent (Const := Const) carrier
  prime_or :
    ∀ {φ ψ : ClosedFormula Const},
      (.or φ ψ : ClosedFormula Const) ∈ carrier → φ ∈ carrier ∨ ψ ∈ carrier
  exists_witness :
    ∀ {σ : Ty Base} {φ : Formula Const [σ]},
      (.ex φ : ClosedFormula Const) ∈ carrier →
        ∃ t : ClosedTerm Const σ, instantiate (Base := Base) t φ ∈ carrier

namespace IntuitionisticWorld

variable {W : IntuitionisticWorld Const}

theorem mem_of_provable {φ : ClosedFormula Const}
    (h : Provable (Const := Const) W.carrier φ) :
    φ ∈ W.carrier :=
  W.closed h

theorem top_mem : (.top : ClosedFormula Const) ∈ W.carrier :=
  mem_of_provable (W := W) (provable_top (Const := Const) W.carrier)

theorem mp {φ ψ : ClosedFormula Const}
    (hImp : (.imp φ ψ : ClosedFormula Const) ∈ W.carrier)
    (hφ : φ ∈ W.carrier) :
    ψ ∈ W.carrier := by
  apply mem_of_provable (W := W)
  exact provable_mp (Const := Const)
    (provable_of_mem (Const := Const) hImp)
    (provable_of_mem (Const := Const) hφ)

theorem bot_not_mem : (.bot : ClosedFormula Const) ∉ W.carrier := by
  intro hbot
  exact W.consistent (provable_of_mem (Const := Const) hbot)

/-- Any theory included in an intuitionistic world is consistent. -/
theorem consistent_of_subset {T : ClosedTheorySet Const}
    (hSub : ∀ {φ : ClosedFormula Const}, φ ∈ T → φ ∈ W.carrier) :
    Consistent (Const := Const) T := by
  intro hbot
  exact W.consistent
    (provable_mono (Const := Const) (T := T) (U := W.carrier)
      (by intro φ hφ; exact hSub hφ) hbot)

end IntuitionisticWorld

theorem noConstOccurrence_self_const_false {σ : Ty Base} (c : Const σ) :
    ¬ NoConstOccurrence c (.const c : ClosedTerm Const σ) := by
  intro h
  cases h with
  | const_diff_type hne _ => exact hne rfl
  | const_same_ne _ hne => exact hne rfl

theorem noConstOccurrence_eq_self_const_false {σ : Ty Base} (c : Const σ) :
    ¬ NoConstOccurrence c
      (.eq (.const c : ClosedTerm Const σ) (.const c) : ClosedFormula Const) := by
  intro h
  cases h with
  | eq hleft _ => exact noConstOccurrence_self_const_false c hleft

/-- Parameter indices from layers strictly below `ℓ`, expressed through
`Nat.pair`. -/
def ParamBelowLayer (ℓ p : Nat) : Prop :=
  ∃ m k, p = Nat.pair m k ∧ m < ℓ

/-- Original constants plus parameters restricted to layers below `ℓ`. -/
abbrev LevelParams (Const : Ty Base → Type v) (ℓ : Nat) (σ : Ty Base) : Type v :=
  Const σ ⊕ {p : Nat // ParamBelowLayer ℓ p}

namespace LevelParams

/-- Embed a level-restricted signature into the global parameter signature. -/
@[reducible] def toWithParams {ℓ : Nat} {σ : Ty Base} :
    LevelParams Const ℓ σ → WithParams Const σ
  | Sum.inl c => inj c
  | Sum.inr p => param σ p.1

theorem param_pair_not_below {ℓ m k : Nat} (hm : ℓ ≤ m) :
    ¬ ParamBelowLayer ℓ (Nat.pair m k) := by
  intro h
  rcases h with ⟨m', k', hp, hm'⟩
  have hmm' : m = m' := (Nat.pair_eq_pair.mp hp).1
  exact (not_lt_of_ge hm) (by simpa [hmm'] using hm')

/-- Monotone inclusion of lower-level parameter signatures. -/
@[reducible] def castLe {ℓ ℓ' : Nat} (hℓ : ℓ ≤ ℓ') {σ : Ty Base} :
    LevelParams Const ℓ σ → LevelParams Const ℓ' σ
  | Sum.inl c => Sum.inl c
  | Sum.inr p =>
      Sum.inr ⟨p.1, by
        rcases p.2 with ⟨m, k, hp, hm⟩
        exact ⟨m, k, hp, lt_of_lt_of_le hm hℓ⟩⟩

/-- Successor-level inclusion of a level-restricted signature. -/
@[reducible] def castSucc {ℓ : Nat} {σ : Ty Base} :
    LevelParams Const ℓ σ → LevelParams Const (ℓ + 1) σ :=
  castLe (Const := Const) (Nat.le_succ ℓ)

/-- Lifting a level-restricted constant and then embedding globally is the same
global constant. -/
theorem toWithParams_castLe {ℓ ℓ' : Nat} (hℓ : ℓ ≤ ℓ')
    {σ : Ty Base} (c : LevelParams Const ℓ σ) :
    toWithParams (castLe (Const := Const) hℓ c) = toWithParams c := by
  cases c with
  | inl c => rfl
  | inr p => rfl

/-- Lifting a level-restricted term and then embedding globally is the same as
embedding it globally directly. -/
theorem mapConst_toWithParams_castLe {ℓ ℓ' : Nat} (hℓ : ℓ ≤ ℓ')
    {Γ : Ctx Base} {τ : Ty Base} (t : Term (LevelParams Const ℓ) Γ τ) :
    mapConst (fun {_} c => toWithParams c)
        (mapConst (fun {_} c => castLe (Const := Const) hℓ c) t) =
      mapConst (fun {_} c => toWithParams c) t := by
  rw [mapConst_comp]
  exact mapConst_ext
    (Const := LevelParams Const ℓ)
    (Const' := WithParams Const)
    (fun c => toWithParams_castLe (Const := Const) hℓ c)
    t

/-- Mapping a level-restricted term into `WithParams` cannot introduce a
parameter from any future layer. -/
theorem noConstOccurrence_toWithParams_of_future
    {ℓ m k : Nat} (hm : ℓ ≤ m) (σ : Ty Base) :
    ∀ {Γ : Ctx Base} {τ : Ty Base} (t : Term (LevelParams Const ℓ) Γ τ),
      NoConstOccurrence (param σ (Nat.pair m k) : WithParams Const σ)
        (mapConst (fun {_} c => toWithParams c) t) := by
  intro Γ τ t
  induction t with
  | var v => exact NoConstOccurrence.var
  | @const τ₁ Γ₁ d =>
      cases d with
      | inl c =>
          by_cases hτ : σ = τ₁
          · subst hτ
            exact NoConstOccurrence.const_same_ne (inj c) (inj_ne_param c (Nat.pair m k))
          · exact NoConstOccurrence.const_diff_type hτ (inj c)
      | inr p =>
          by_cases hτ : σ = τ₁
          · subst hτ
            refine NoConstOccurrence.const_same_ne (param σ p.1) ?_
            intro heq
            have hp : p.1 = Nat.pair m k := param_inj heq
            have hpBelow : ParamBelowLayer ℓ (Nat.pair m k) := by
              simpa [hp] using p.2
            exact param_pair_not_below (ℓ := ℓ) (m := m) (k := k) hm hpBelow
          · exact NoConstOccurrence.const_diff_type hτ (param τ₁ p.1)
  | app f t hf ht => exact NoConstOccurrence.app hf ht
  | lam t ih => exact NoConstOccurrence.lam ih
  | top => exact NoConstOccurrence.top
  | bot => exact NoConstOccurrence.bot
  | and φ ψ hφ hψ => exact NoConstOccurrence.and hφ hψ
  | or φ ψ hφ hψ => exact NoConstOccurrence.or hφ hψ
  | imp φ ψ hφ hψ => exact NoConstOccurrence.imp hφ hψ
  | not φ hφ => exact NoConstOccurrence.not hφ
  | eq t u ht hu => exact NoConstOccurrence.eq ht hu
  | all φ hφ => exact NoConstOccurrence.all hφ
  | ex φ hφ => exact NoConstOccurrence.ex hφ

end LevelParams

/-- A theory uses no parameter from layers `ℓ, ℓ+1, ...`, where layer/index pairs
are encoded by `Nat.pair`. -/
def AvoidsParamLayersFrom (ℓ : Nat) (T : ClosedTheorySet (WithParams Const)) : Prop :=
  ∀ ψ ∈ T, ∀ (σ : Ty Base) (m k : Nat), ℓ ≤ m →
    NoConstOccurrence (param σ (Nat.pair m k)) ψ

/-- Formula-level support condition for the global layered parameter pool. -/
def FormulaAvoidsParamLayersFrom
    (ℓ : Nat) (φ : ClosedFormula (WithParams Const)) : Prop :=
  ∀ (σ : Ty Base) (m k : Nat), ℓ ≤ m →
    NoConstOccurrence (param σ (Nat.pair m k)) φ

/-- A theory uses no parameter from stages `s, s+1, ...` inside a fixed outer
layer `ℓ`.  Stage splitting lets an infinite construction consume stage `s`
while preserving a reserve of later stages below the same outer layer. -/
def AvoidsParamStagesFrom
    (ℓ s : Nat) (T : ClosedTheorySet (WithParams Const)) : Prop :=
  ∀ ψ ∈ T, ∀ (σ : Ty Base) (r k : Nat), s ≤ r →
    NoConstOccurrence (param σ (Nat.pair ℓ (Nat.pair r k))) ψ

/-- Formula-level support condition for future stages inside one parameter
layer. -/
def FormulaAvoidsParamStagesFrom
    (ℓ s : Nat) (φ : ClosedFormula (WithParams Const)) : Prop :=
  ∀ (σ : Ty Base) (r k : Nat), s ≤ r →
    NoConstOccurrence (param σ (Nat.pair ℓ (Nat.pair r k))) φ

/-- If a formula avoids all parameters from layer `ℓ` upward, it also avoids all
parameters from any later layer. -/
theorem FormulaAvoidsParamLayersFrom.mono
    {ℓ m : Nat} (hℓm : ℓ ≤ m) {φ : ClosedFormula (WithParams Const)}
    (hφ : FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ φ) :
    FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) m φ := by
  intro σ r k hmr
  exact hφ σ r k (le_trans hℓm hmr)

/-- Future-stage formula support is monotone in the stage bound. -/
theorem FormulaAvoidsParamStagesFrom.mono
    {ℓ s r : Nat} (hsr : s ≤ r) {φ : ClosedFormula (WithParams Const)}
    (hφ : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ s φ) :
    FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ r φ := by
  intro σ q k hrq
  exact hφ σ q k (le_trans hsr hrq)

/-- If a theory avoids all parameters from layer `ℓ` upward, it also avoids all
parameters from any later layer. -/
theorem AvoidsParamLayersFrom.mono
    {ℓ m : Nat} (hℓm : ℓ ≤ m) {T : ClosedTheorySet (WithParams Const)}
    (hT : AvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ T) :
    AvoidsParamLayersFrom (Base := Base) (Const := Const) m T := by
  intro ψ hψ σ r k hmr
  exact hT ψ hψ σ r k (le_trans hℓm hmr)

/-- Future-stage theory support is monotone in the stage bound. -/
theorem AvoidsParamStagesFrom.mono
    {ℓ s r : Nat} (hsr : s ≤ r) {T : ClosedTheorySet (WithParams Const)}
    (hT : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ s T) :
    AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ r T := by
  intro ψ hψ σ q k hrq
  exact hT ψ hψ σ q k (le_trans hsr hrq)

/-- Inserting a formula with the same future-layer support preserves support of
the raw theory. -/
theorem AvoidsParamLayersFrom.insert
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    {δ : ClosedFormula (WithParams Const)}
    (hT : AvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ T)
    (hδ : FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ δ) :
    AvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ (insert δ T) := by
  intro ψ hψ σ m k hℓm
  rcases Set.mem_insert_iff.mp hψ with rfl | hψT
  · exact hδ σ m k hℓm
  · exact hT ψ hψT σ m k hℓm

/-- Inserting a formula with the same future-stage support preserves
future-stage support of the raw theory. -/
theorem AvoidsParamStagesFrom.insert
    {ℓ s : Nat} {T : ClosedTheorySet (WithParams Const)}
    {δ : ClosedFormula (WithParams Const)}
    (hT : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ s T)
    (hδ : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ s δ) :
    AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ s (insert δ T) := by
  intro ψ hψ σ r k hsr
  rcases Set.mem_insert_iff.mp hψ with rfl | hψT
  · exact hδ σ r k hsr
  · exact hT ψ hψT σ r k hsr

/-- A theory that avoids future stages is fresh for the supply reserved at the
current stage. -/
theorem AvoidsParamStagesFrom.fresh_for_stageSupply
    {ℓ s : Nat} {T : ClosedTheorySet (WithParams Const)}
    (hT : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ s T) :
    ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ ((stageWitnessSupply ℓ s).index k)) ψ := by
  intro ψ hψ σ k
  exact hT ψ hψ σ s k (le_refl s)

/-- A formula that avoids future stages is fresh for the current stage supply. -/
theorem FormulaAvoidsParamStagesFrom.fresh_for_stageSupply
    {ℓ s : Nat} {φ : ClosedFormula (WithParams Const)}
    (hφ : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ s φ) :
    ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ ((stageWitnessSupply ℓ s).index k)) φ := by
  intro σ k
  exact hφ σ s k (le_refl s)

/-- Every closed formula has finite stage support inside a fixed outer layer:
after `maxParam φ`, no parameter from that layer can occur. -/
theorem FormulaAvoidsParamStagesFrom.of_maxParam
    (ℓ : Nat) (φ : ClosedFormula (WithParams Const)) :
    FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (maxParam φ) φ := by
  intro σ r k hφr
  exact noConstOccurrence_param_of_ge (Nat.pair ℓ (Nat.pair r k)) φ
    (le_trans hφr
      (le_trans (Nat.left_le_pair r k) (Nat.right_le_pair ℓ (Nat.pair r k))))

/-- Every closed formula has finite layer support: after `maxParam φ`, no
parameter from that layer or any later layer can occur. -/
theorem FormulaAvoidsParamLayersFrom.of_maxParam
    (φ : ClosedFormula (WithParams Const)) :
    FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) (maxParam φ) φ := by
  intro σ m k hφm
  exact noConstOccurrence_param_of_ge (Nat.pair m k) φ
    (Nat.le_trans hφm (Nat.left_le_pair m k))

/-- Future-layer support implies future-stage support within that layer. -/
theorem AvoidsParamLayersFrom.to_stages
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (hT : AvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ T) :
    AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T := by
  intro ψ hψ σ r k _hr
  exact hT ψ hψ σ ℓ (Nat.pair r k) (le_refl ℓ)

/-- Formula future-layer support implies future-stage support within that layer. -/
theorem FormulaAvoidsParamLayersFrom.to_stages
    {ℓ : Nat} {φ : ClosedFormula (WithParams Const)}
    (hφ : FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ φ) :
    FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 φ := by
  intro σ r k _hr
  exact hφ σ ℓ (Nat.pair r k) (le_refl ℓ)

/-- A canonical world presentation keeps the raw, level-bounded theory separate
from its deductive-closure carrier.  Future Kripke forcing should range over
this presentation rather than over a bare closed carrier, because closed carriers
contain provable formulas mentioning arbitrary future parameters. -/
structure PresentedIntuitionisticWorld (Const : Ty Base → Type v) where
  level : Nat
  raw : ClosedTheorySet (WithParams Const)
  raw_avoids_future :
    AvoidsParamLayersFrom (Base := Base) (Const := Const) level raw
  consistent :
    Consistent (Const := WithParams Const)
      (ClosedTheorySet.provableClosure (Const := WithParams Const) raw)
  prime_or :
    ∀ {φ ψ : ClosedFormula (WithParams Const)},
      (.or φ ψ : ClosedFormula (WithParams Const)) ∈
        ClosedTheorySet.provableClosure (Const := WithParams Const) raw →
        φ ∈ ClosedTheorySet.provableClosure (Const := WithParams Const) raw ∨
          ψ ∈ ClosedTheorySet.provableClosure (Const := WithParams Const) raw
  exists_witness :
    ∀ {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
      (.ex φ : ClosedFormula (WithParams Const)) ∈
        ClosedTheorySet.provableClosure (Const := WithParams Const) raw →
        ∃ t : ClosedTerm (WithParams Const) σ,
          instantiate (Base := Base) t φ ∈
            ClosedTheorySet.provableClosure (Const := WithParams Const) raw

namespace PresentedIntuitionisticWorld

/-- The semantic carrier read from a presented world: the deductive closure of
its raw base. -/
def carrier (W : PresentedIntuitionisticWorld Const) : ClosedTheorySet (WithParams Const) :=
  ClosedTheorySet.provableClosure (Const := WithParams Const) W.raw

theorem closed (W : PresentedIntuitionisticWorld Const) :
    DeductivelyClosed (Const := WithParams Const) W.carrier := by
  exact ClosedTheorySet.provableClosure_deductivelyClosed
    (Const := WithParams Const) W.raw

/-- Forget the raw presentation when only the already-closed intuitionistic-world
interface is needed.  The raw fields should be retained for Kripke successor and
freshness arguments. -/
def toIntuitionisticWorld (W : PresentedIntuitionisticWorld Const) :
    IntuitionisticWorld (WithParams Const) where
  carrier := W.carrier
  closed := W.closed
  consistent := W.consistent
  prime_or := W.prime_or
  exists_witness := W.exists_witness

theorem raw_mem_carrier {W : PresentedIntuitionisticWorld Const}
    {φ : ClosedFormula (WithParams Const)} (hφ : φ ∈ W.raw) :
    φ ∈ W.carrier := by
  exact ClosedTheorySet.subset_provableClosure
    (Const := WithParams Const) W.raw hφ

end PresentedIntuitionisticWorld

/-- Image of a level-restricted closed theory inside the global parameter
signature. -/
def mapLevelTheory (ℓ : Nat) (T : ClosedTheorySet (LevelParams Const ℓ)) :
    ClosedTheorySet (WithParams Const) :=
  {ψ | ∃ φ : ClosedFormula (LevelParams Const ℓ),
    φ ∈ T ∧ mapConst (fun {_} c => LevelParams.toWithParams c) φ = ψ}

/-- Image of a level-restricted theory in a larger level-restricted signature. -/
def castLevelTheory {ℓ ℓ' : Nat} (hℓ : ℓ ≤ ℓ')
    (T : ClosedTheorySet (LevelParams Const ℓ)) :
    ClosedTheorySet (LevelParams Const ℓ') :=
  {ψ | ∃ φ : ClosedFormula (LevelParams Const ℓ),
    φ ∈ T ∧ mapConst (fun {_} c => LevelParams.castLe (Const := Const) hℓ c) φ = ψ}

/-- The global image of a cast level theory is the original global image. -/
theorem mapLevelTheory_castLevelTheory {ℓ ℓ' : Nat} (hℓ : ℓ ≤ ℓ')
    (T : ClosedTheorySet (LevelParams Const ℓ)) :
    mapLevelTheory (Base := Base) (Const := Const) ℓ' (castLevelTheory hℓ T) =
      mapLevelTheory (Base := Base) (Const := Const) ℓ T := by
  ext ψ
  constructor
  · intro hψ
    rcases hψ with ⟨φ', hφ', hφ'ψ⟩
    rcases hφ' with ⟨φ, hφ, hφφ'⟩
    refine ⟨φ, hφ, ?_⟩
    rw [← hφ'ψ, ← hφφ']
    exact (LevelParams.mapConst_toWithParams_castLe (Const := Const) hℓ φ).symm
  · intro hψ
    rcases hψ with ⟨φ, hφ, hφψ⟩
    refine ⟨mapConst (fun {_} c => LevelParams.castLe (Const := Const) hℓ c) φ, ?_, ?_⟩
    · exact ⟨φ, hφ, rfl⟩
    · rw [← hφψ]
      exact LevelParams.mapConst_toWithParams_castLe (Const := Const) hℓ φ

/-- Successor-level image of a level-restricted theory. -/
def castLevelTheorySucc (ℓ : Nat) (T : ClosedTheorySet (LevelParams Const ℓ)) :
    ClosedTheorySet (LevelParams Const (ℓ + 1)) :=
  castLevelTheory (Base := Base) (Const := Const) (Nat.le_succ ℓ) T

/-- Casting a level theory to the successor level leaves its global image
unchanged. -/
theorem mapLevelTheory_castLevelTheorySucc
    (ℓ : Nat) (T : ClosedTheorySet (LevelParams Const ℓ)) :
    mapLevelTheory (Base := Base) (Const := Const) (ℓ + 1)
        (castLevelTheorySucc (Base := Base) (Const := Const) ℓ T) =
      mapLevelTheory (Base := Base) (Const := Const) ℓ T :=
  mapLevelTheory_castLevelTheory (Base := Base) (Const := Const) (Nat.le_succ ℓ) T

/-- Consistency of the global image is invariant under level-theory casting. -/
theorem consistent_mapLevelTheory_castLevelTheory_iff {ℓ ℓ' : Nat} (hℓ : ℓ ≤ ℓ')
    (T : ClosedTheorySet (LevelParams Const ℓ)) :
    Consistent (Const := WithParams Const)
        (mapLevelTheory (Base := Base) (Const := Const) ℓ' (castLevelTheory hℓ T)) ↔
      Consistent (Const := WithParams Const)
        (mapLevelTheory (Base := Base) (Const := Const) ℓ T) := by
  rw [mapLevelTheory_castLevelTheory (Base := Base) (Const := Const) hℓ T]

/-- Successor-level form of global-image consistency invariance. -/
theorem consistent_mapLevelTheory_castLevelTheorySucc_iff
    (ℓ : Nat) (T : ClosedTheorySet (LevelParams Const ℓ)) :
    Consistent (Const := WithParams Const)
        (mapLevelTheory (Base := Base) (Const := Const) (ℓ + 1)
          (castLevelTheorySucc (Base := Base) (Const := Const) ℓ T)) ↔
      Consistent (Const := WithParams Const)
        (mapLevelTheory (Base := Base) (Const := Const) ℓ T) :=
  consistent_mapLevelTheory_castLevelTheory_iff
    (Base := Base) (Const := Const) (Nat.le_succ ℓ) T

/-- Set-level provability is preserved when a level-restricted theory is moved
to a larger level-restricted signature. -/
theorem provable_castLevelTheory {ℓ ℓ' : Nat} (hℓ : ℓ ≤ ℓ')
    {T : ClosedTheorySet (LevelParams Const ℓ)}
    {φ : ClosedFormula (LevelParams Const ℓ)}
    (h : Provable (Const := LevelParams Const ℓ) T φ) :
    Provable (Const := LevelParams Const ℓ') (castLevelTheory hℓ T)
      (mapConst (fun {_} c => LevelParams.castLe (Const := Const) hℓ c) φ) := by
  rcases h with ⟨Γ, hΓ, d⟩
  refine ⟨Γ.map (fun ψ =>
    mapConst (fun {_} c => LevelParams.castLe (Const := Const) hℓ c) ψ), ?_, ?_⟩
  · intro ψ hψ
    rcases List.mem_map.mp hψ with ⟨ξ, hξ, rfl⟩
    exact ⟨ξ, hΓ ξ hξ, rfl⟩
  · simpa [mapClosedFormula] using
      (ExtDerivation.closedTheory_mapConst
        (Base := Base) (Const := LevelParams Const ℓ) (Const' := LevelParams Const ℓ')
        (fun {_} c => LevelParams.castLe (Const := Const) hℓ c) d)

/-- Successor-level form of `provable_castLevelTheory`. -/
theorem provable_castLevelTheorySucc
    {ℓ : Nat} {T : ClosedTheorySet (LevelParams Const ℓ)}
    {φ : ClosedFormula (LevelParams Const ℓ)}
    (h : Provable (Const := LevelParams Const ℓ) T φ) :
    Provable (Const := LevelParams Const (ℓ + 1)) (castLevelTheorySucc ℓ T)
      (mapConst (fun {_} c => LevelParams.castSucc (Const := Const) c) φ) :=
  provable_castLevelTheory (Base := Base) (Const := Const) (Nat.le_succ ℓ) h

/-- The image of a level-`ℓ` theory avoids every parameter from layers
`ℓ, ℓ+1, ...`. -/
theorem mapLevelTheory_avoids_future_layers
    (ℓ : Nat) (T : ClosedTheorySet (LevelParams Const ℓ)) :
    AvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ (mapLevelTheory ℓ T) := by
  intro ψ hψ σ m k hm
  rcases hψ with ⟨φ, _hφ, rfl⟩
  exact LevelParams.noConstOccurrence_toWithParams_of_future
    (Const := Const) hm σ φ

/-- Formulas in a level-`ℓ` theory image are fresh for every parameter in the
level-`ℓ` witness supply. -/
theorem mapLevelTheory_fresh_for_levelSupply
    (ℓ : Nat) (T : ClosedTheorySet (LevelParams Const ℓ)) :
    ∀ ψ ∈ mapLevelTheory (Base := Base) (Const := Const) ℓ T,
      ∀ (σ : Ty Base) (k : Nat),
        NoConstOccurrence (param σ ((levelWitnessSupply ℓ).index k)) ψ := by
  intro ψ hψ σ k
  exact mapLevelTheory_avoids_future_layers
    (Base := Base) (Const := Const) ℓ T ψ hψ σ ℓ k (le_refl ℓ)

/-- Formulas in a level-`ℓ` theory image are fresh for every parameter in any
higher-layer witness supply. -/
theorem mapLevelTheory_fresh_for_higherLevelSupply
    {ℓ m : Nat} (hm : ℓ ≤ m) (T : ClosedTheorySet (LevelParams Const ℓ)) :
    ∀ ψ ∈ mapLevelTheory (Base := Base) (Const := Const) ℓ T,
      ∀ (σ : Ty Base) (k : Nat),
        NoConstOccurrence (param σ ((levelWitnessSupply m).index k)) ψ := by
  intro ψ hψ σ k
  exact mapLevelTheory_avoids_future_layers
    (Base := Base) (Const := Const) ℓ T ψ hψ σ m k hm

/-- Inserting one formula that is fresh for a higher-layer witness supply keeps
the whole theory fresh for that supply. -/
theorem fresh_for_levelSupply_insert
    {T : ClosedTheorySet (WithParams Const)} {θ : ClosedFormula (WithParams Const)}
    {m : Nat}
    (hT : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ ((levelWitnessSupply m).index k)) ψ)
    (hθ : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ ((levelWitnessSupply m).index k)) θ) :
    ∀ ψ ∈ insert θ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ ((levelWitnessSupply m).index k)) ψ := by
  intro ψ hψ σ k
  rcases Set.mem_insert_iff.mp hψ with rfl | hψT
  · exact hθ σ k
  · exact hT ψ hψT σ k

/-- Level-image form of the fair disjunction branch step.  A level-`ℓ` base can
decide one proved disjunction using any reserved layer `m ≥ ℓ`, then close and
witness the chosen branch while preserving omission of `θ`. -/
theorem exists_closed_witnessed_or_branch_levelImage_separating
    {ℓ m : Nat} (hm : ℓ ≤ m)
    {T : ClosedTheorySet (LevelParams Const ℓ)}
    (enum : Nat → Body Const) (hfair : BodyFairAfter (Const := Const) enum)
    {φ ψ θ : ClosedFormula (WithParams Const)}
    (hNot : ¬ Provable (Const := WithParams Const)
      (mapLevelTheory (Base := Base) (Const := Const) ℓ T) θ)
    (hOr : Provable (Const := WithParams Const)
      (mapLevelTheory (Base := Base) (Const := Const) ℓ T) (.or φ ψ))
    (hφ : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ ((levelWitnessSupply m).index k)) φ)
    (hψ : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ ((levelWitnessSupply m).index k)) ψ)
    (hθ : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ ((levelWitnessSupply m).index k)) θ) :
    (∃ U : ClosedTheorySet (WithParams Const),
      (∀ {ξ : ClosedFormula (WithParams Const)},
        ξ ∈ mapLevelTheory (Base := Base) (Const := Const) ℓ T → ξ ∈ U) ∧
      φ ∈ U ∧
      DeductivelyClosed (Const := WithParams Const) U ∧
      Consistent (Const := WithParams Const) U ∧
      (∀ {σ : Ty Base} {χ : Formula (WithParams Const) [σ]},
        (.ex χ : ClosedFormula (WithParams Const)) ∈ U →
          ∃ t : ClosedTerm (WithParams Const) σ, instantiate (Base := Base) t χ ∈ U) ∧
      θ ∉ U) ∨
    (∃ U : ClosedTheorySet (WithParams Const),
      (∀ {ξ : ClosedFormula (WithParams Const)},
        ξ ∈ mapLevelTheory (Base := Base) (Const := Const) ℓ T → ξ ∈ U) ∧
      ψ ∈ U ∧
      DeductivelyClosed (Const := WithParams Const) U ∧
      Consistent (Const := WithParams Const) U ∧
      (∀ {σ : Ty Base} {χ : Formula (WithParams Const) [σ]},
        (.ex χ : ClosedFormula (WithParams Const)) ∈ U →
          ∃ t : ClosedTerm (WithParams Const) σ, instantiate (Base := Base) t χ ∈ U) ∧
      θ ∉ U) := by
  exact exists_closed_witnessed_or_branch_instanceLimit_separating
    (Base := Base) (Const := Const) (levelWitnessSupply m)
    (T₀ := mapLevelTheory (Base := Base) (Const := Const) ℓ T)
    enum hfair hNot hOr
    (mapLevelTheory_fresh_for_higherLevelSupply
      (Base := Base) (Const := Const) hm T)
    hφ hψ hθ

/-- Universal-introduction over a level-image base theory using a current-layer
fresh parameter. -/
theorem provable_all_intro_fresh_of_mapLevelTheory
    (ℓ : Nat) (T : ClosedTheorySet (LevelParams Const ℓ))
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]} (k : Nat)
    (hφfresh :
      NoConstOccurrence (param σ ((levelWitnessSupply ℓ).index k) : WithParams Const σ) φ)
    (hInst : Provable (Const := WithParams Const)
      (mapLevelTheory (Base := Base) (Const := Const) ℓ T)
      (instantiate (Base := Base) (.const (param σ ((levelWitnessSupply ℓ).index k))) φ)) :
    Provable (Const := WithParams Const)
      (mapLevelTheory (Base := Base) (Const := Const) ℓ T) (.all φ) := by
  exact provable_all_intro_fresh
    (Const := WithParams Const) (T := mapLevelTheory (Base := Base) (Const := Const) ℓ T)
    (c := param σ ((levelWitnessSupply ℓ).index k))
    (fun ψ hψ => mapLevelTheory_fresh_for_levelSupply
      (Base := Base) (Const := Const) ℓ T ψ hψ σ k)
    hφfresh hInst

/-- If a full EM-free world extends a level-image base theory and omits `∀x.φ`,
then no current-layer fresh instance of `φ` is provable from that base theory. -/
theorem not_provable_fresh_instance_of_not_all_mem_levelImage
    (ℓ : Nat) {T : ClosedTheorySet (LevelParams Const ℓ)}
    (W : IntuitionisticWorld (WithParams Const))
    (hSub : ∀ {ψ : ClosedFormula (WithParams Const)},
      ψ ∈ mapLevelTheory (Base := Base) (Const := Const) ℓ T → ψ ∈ W.carrier)
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]} (k : Nat)
    (hφfresh :
      NoConstOccurrence (param σ ((levelWitnessSupply ℓ).index k) : WithParams Const σ) φ)
    (hNotAll : (.all φ : ClosedFormula (WithParams Const)) ∉ W.carrier) :
    ¬ Provable (Const := WithParams Const)
      (mapLevelTheory (Base := Base) (Const := Const) ℓ T)
      (instantiate (Base := Base) (.const (param σ ((levelWitnessSupply ℓ).index k))) φ) := by
  intro hInst
  have hAllBase : Provable (Const := WithParams Const)
      (mapLevelTheory (Base := Base) (Const := Const) ℓ T) (.all φ) :=
    provable_all_intro_fresh_of_mapLevelTheory
      (Base := Base) (Const := Const) ℓ T k hφfresh hInst
  have hAllW : Provable (Const := WithParams Const) W.carrier (.all φ) :=
    provable_mono (Const := WithParams Const)
      (T := mapLevelTheory (Base := Base) (Const := Const) ℓ T)
      (U := W.carrier)
      (by intro ψ hψ; exact hSub hψ)
      hAllBase
  exact hNotAll (W.closed hAllW)

/-- Prime separation for the level-image universal case: if a full EM-free world
extends a level-image base but omits `∀x.φ`, then the base has a prime extension
that omits the current-layer fresh instance of `φ`. -/
theorem exists_prime_extension_omitting_fresh_instance_levelImage
    (ℓ : Nat) {T : ClosedTheorySet (LevelParams Const ℓ)}
    (W : IntuitionisticWorld (WithParams Const))
    (hSub : ∀ {ψ : ClosedFormula (WithParams Const)},
      ψ ∈ mapLevelTheory (Base := Base) (Const := Const) ℓ T → ψ ∈ W.carrier)
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]} (k : Nat)
    (hφfresh :
      NoConstOccurrence (param σ ((levelWitnessSupply ℓ).index k) : WithParams Const σ) φ)
    (hNotAll : (.all φ : ClosedFormula (WithParams Const)) ∉ W.carrier) :
    ∃ U : ClosedTheorySet (WithParams Const),
      (∀ {ψ : ClosedFormula (WithParams Const)},
        ψ ∈ mapLevelTheory (Base := Base) (Const := Const) ℓ T → ψ ∈ U) ∧
      DeductivelyClosed (Const := WithParams Const) U ∧
      Consistent (Const := WithParams Const) U ∧
      (∀ {ψ χ : ClosedFormula (WithParams Const)},
        (.or ψ χ : ClosedFormula (WithParams Const)) ∈ U → ψ ∈ U ∨ χ ∈ U) ∧
      instantiate (Base := Base) (.const (param σ ((levelWitnessSupply ℓ).index k))) φ ∉ U := by
  exact exists_prime_extension_separating
    (Const := WithParams Const)
    (T := mapLevelTheory (Base := Base) (Const := Const) ℓ T)
    (φ := instantiate (Base := Base) (.const (param σ ((levelWitnessSupply ℓ).index k))) φ)
    (not_provable_fresh_instance_of_not_all_mem_levelImage
      (Base := Base) (Const := Const) ℓ W hSub k hφfresh hNotAll)

/-- If a full EM-free world extends a level-image base theory and omits
`φ → ψ`, then adding `φ` to that base cannot prove `ψ`. -/
theorem not_provable_of_not_imp_mem_levelImage
    (ℓ : Nat) {T : ClosedTheorySet (LevelParams Const ℓ)}
    (W : IntuitionisticWorld (WithParams Const))
    (hSub : ∀ {χ : ClosedFormula (WithParams Const)},
      χ ∈ mapLevelTheory (Base := Base) (Const := Const) ℓ T → χ ∈ W.carrier)
    {φ ψ : ClosedFormula (WithParams Const)}
    (hNotImp : (.imp φ ψ : ClosedFormula (WithParams Const)) ∉ W.carrier) :
    ¬ Provable (Const := WithParams Const)
      (insert φ (mapLevelTheory (Base := Base) (Const := Const) ℓ T)) ψ := by
  intro hInsert
  have hImpBase : Provable (Const := WithParams Const)
      (mapLevelTheory (Base := Base) (Const := Const) ℓ T) (.imp φ ψ) :=
    provable_imp_of_insert (Const := WithParams Const) hInsert
  have hImpW : Provable (Const := WithParams Const) W.carrier (.imp φ ψ) :=
    provable_mono (Const := WithParams Const)
      (T := mapLevelTheory (Base := Base) (Const := Const) ℓ T)
      (U := W.carrier)
      (by intro χ hχ; exact hSub hχ)
      hImpBase
  exact hNotImp (W.closed hImpW)

/-- Prime separation for the level-image implication case: if a full EM-free
world extends a level-image base but omits `φ → ψ`, then the base plus `φ` has a
prime extension that still omits `ψ`. -/
theorem exists_prime_extension_for_imp_levelImage
    (ℓ : Nat) {T : ClosedTheorySet (LevelParams Const ℓ)}
    (W : IntuitionisticWorld (WithParams Const))
    (hSub : ∀ {χ : ClosedFormula (WithParams Const)},
      χ ∈ mapLevelTheory (Base := Base) (Const := Const) ℓ T → χ ∈ W.carrier)
    {φ ψ : ClosedFormula (WithParams Const)}
    (hNotImp : (.imp φ ψ : ClosedFormula (WithParams Const)) ∉ W.carrier) :
    ∃ U : ClosedTheorySet (WithParams Const),
      (∀ {χ : ClosedFormula (WithParams Const)},
        χ ∈ mapLevelTheory (Base := Base) (Const := Const) ℓ T → χ ∈ U) ∧
      φ ∈ U ∧
      DeductivelyClosed (Const := WithParams Const) U ∧
      Consistent (Const := WithParams Const) U ∧
      (∀ {χ ξ : ClosedFormula (WithParams Const)},
        (.or χ ξ : ClosedFormula (WithParams Const)) ∈ U → χ ∈ U ∨ ξ ∈ U) ∧
      ψ ∉ U := by
  obtain ⟨U, hExt, hClosed, hCons, hPrime, hOmit⟩ :=
    exists_prime_extension_separating
      (Const := WithParams Const)
      (T := insert φ (mapLevelTheory (Base := Base) (Const := Const) ℓ T))
      (φ := ψ)
      (not_provable_of_not_imp_mem_levelImage
        (Base := Base) (Const := Const) ℓ W hSub hNotImp)
  refine ⟨U, ?_, ?_, hClosed, hCons, hPrime, hOmit⟩
  · intro χ hχ
    exact hExt (Set.mem_insert_of_mem φ hχ)
  · exact hExt (Set.mem_insert φ (mapLevelTheory (Base := Base) (Const := Const) ℓ T))

/-- An enumeration of existential bodies avoids every parameter from layers
`ℓ, ℓ+1, ...`. -/
def BodyAvoidsParamLayersFrom (ℓ : Nat) (enum : Nat → Body Const) : Prop :=
  ∀ n, ∀ (σ : Ty Base) (m k : Nat), ℓ ≤ m →
    NoConstOccurrence (param σ (Nat.pair m k)) (enum n).2

/-- An enumeration of existential bodies avoids every parameter from stages
`s, s+1, ...` inside a fixed outer layer `ℓ`. -/
def BodyAvoidsParamStagesFrom (ℓ s : Nat) (enum : Nat → Body Const) : Prop :=
  ∀ n, ∀ (σ : Ty Base) (r k : Nat), s ≤ r →
    NoConstOccurrence (param σ (Nat.pair ℓ (Nat.pair r k))) (enum n).2

/-- Body-enumeration support is monotone in the lower layer bound. -/
theorem BodyAvoidsParamLayersFrom.mono
    {ℓ m : Nat} (hℓm : ℓ ≤ m) {enum : Nat → Body Const}
    (hEnum : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ enum) :
    BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) m enum := by
  intro n σ r k hmr
  exact hEnum n σ r k (le_trans hℓm hmr)

/-- Body-enumeration support is monotone in the future-stage bound. -/
theorem BodyAvoidsParamStagesFrom.mono
    {ℓ s r : Nat} (hsr : s ≤ r) {enum : Nat → Body Const}
    (hEnum : BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ s enum) :
    BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ r enum := by
  intro n σ q k hrq
  exact hEnum n σ q k (le_trans hsr hrq)

/-- A closed disjunction to be decided during raw prime-extension construction. -/
abbrev ClosedFormulaPair (Const : Ty Base → Type v) :=
  ClosedFormula (WithParams Const) × ClosedFormula (WithParams Const)

/-- Fairness for disjunction-decision enumeration: every pair appears again at
or after any finite stage. -/
def FormulaPairFairAfter (enum : Nat → ClosedFormulaPair Const) : Prop :=
  ∀ p : ClosedFormulaPair Const, ∀ N : Nat, ∃ n, N ≤ n ∧ enum n = p

/-- A disjunction-pair enumeration avoids every parameter from layers
`ℓ, ℓ+1, ...`. -/
def FormulaPairAvoidsParamLayersFrom
    (ℓ : Nat) (enum : Nat → ClosedFormulaPair Const) : Prop :=
  ∀ n, ∀ (σ : Ty Base) (m k : Nat), ℓ ≤ m →
    NoConstOccurrence (param σ (Nat.pair m k)) (enum n).1 ∧
      NoConstOccurrence (param σ (Nat.pair m k)) (enum n).2

/-- A disjunction-pair enumeration avoids every parameter from stages
`s, s+1, ...` inside a fixed outer layer `ℓ`. -/
def FormulaPairAvoidsParamStagesFrom
    (ℓ s : Nat) (enum : Nat → ClosedFormulaPair Const) : Prop :=
  ∀ n, ∀ (σ : Ty Base) (r k : Nat), s ≤ r →
    NoConstOccurrence (param σ (Nat.pair ℓ (Nat.pair r k))) (enum n).1 ∧
      NoConstOccurrence (param σ (Nat.pair ℓ (Nat.pair r k))) (enum n).2

/-- One existential body avoids every parameter from stages `s, s+1, ...`
inside a fixed outer layer `ℓ`. -/
def BodyAvoidsParamStagesFromAt (ℓ s : Nat) (body : Body Const) : Prop :=
  ∀ (σ : Ty Base) (r k : Nat), s ≤ r →
    NoConstOccurrence (param σ (Nat.pair ℓ (Nat.pair r k))) body.2

/-- One existential body avoids every parameter from layers `ℓ, ℓ+1, ...`. -/
def BodyAvoidsParamLayersFromAt (ℓ : Nat) (body : Body Const) : Prop :=
  ∀ (σ : Ty Base) (m k : Nat), ℓ ≤ m →
    NoConstOccurrence (param σ (Nat.pair m k)) body.2

/-- One disjunction pair avoids every parameter from stages `s, s+1, ...`
inside a fixed outer layer `ℓ`. -/
def FormulaPairAvoidsParamStagesFromAt
    (ℓ s : Nat) (pair : ClosedFormulaPair Const) : Prop :=
  ∀ (σ : Ty Base) (r k : Nat), s ≤ r →
    NoConstOccurrence (param σ (Nat.pair ℓ (Nat.pair r k))) pair.1 ∧
      NoConstOccurrence (param σ (Nat.pair ℓ (Nat.pair r k))) pair.2

/-- One disjunction pair avoids every parameter from layers `ℓ, ℓ+1, ...`. -/
def FormulaPairAvoidsParamLayersFromAt
    (ℓ : Nat) (pair : ClosedFormulaPair Const) : Prop :=
  ∀ (σ : Ty Base) (m k : Nat), ℓ ≤ m →
    NoConstOccurrence (param σ (Nat.pair m k)) pair.1 ∧
      NoConstOccurrence (param σ (Nat.pair m k)) pair.2

/-- Stage-local fairness for a body enumeration: every body whose support stays
below the next outer layer and below stage `s` appears again after any requested
finite point. -/
def BodyStageFairAfter (ℓ s : Nat) (enum : Nat → Body Const) : Prop :=
  ∀ b : Body Const,
    BodyAvoidsParamLayersFromAt (Base := Base) (Const := Const) (ℓ + 1) b →
    BodyAvoidsParamStagesFromAt (Base := Base) (Const := Const) ℓ s b →
    ∀ N : Nat, ∃ n, N ≤ n ∧ enum n = b

/-- Support-respecting fairness for a disjunction-pair scheduler.  The selected
pair at stage `n` must be fresh for that stage, and every finitely supported
pair appears at some sufficiently late fresh stage. -/
def FormulaPairStageScheduleFair (ℓ : Nat) (enum : Nat → ClosedFormulaPair Const) : Prop :=
  (∀ n, FormulaPairAvoidsParamStagesFromAt (Base := Base) (Const := Const) ℓ n (enum n)) ∧
    (∀ p : ClosedFormulaPair Const, ∀ N : Nat,
      ∃ n, N ≤ n ∧ FormulaPairAvoidsParamStagesFromAt (Base := Base) (Const := Const) ℓ n p ∧
        enum n = p)

/-- Disjunction-pair enumeration support is monotone in the lower layer bound. -/
theorem FormulaPairAvoidsParamLayersFrom.mono
    {ℓ m : Nat} (hℓm : ℓ ≤ m) {enum : Nat → ClosedFormulaPair Const}
    (hEnum : FormulaPairAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ enum) :
    FormulaPairAvoidsParamLayersFrom (Base := Base) (Const := Const) m enum := by
  intro n σ r k hmr
  exact hEnum n σ r k (le_trans hℓm hmr)

/-- Disjunction-pair enumeration support is monotone in the future-stage bound. -/
theorem FormulaPairAvoidsParamStagesFrom.mono
    {ℓ s r : Nat} (hsr : s ≤ r) {enum : Nat → ClosedFormulaPair Const}
    (hEnum : FormulaPairAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ s enum) :
    FormulaPairAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ r enum := by
  intro n σ q k hrq
  exact hEnum n σ q k (le_trans hsr hrq)

/-- Every existential body has finite stage support inside a fixed outer layer. -/
theorem BodyAvoidsParamStagesFromAt.of_maxParam
    (ℓ : Nat) (body : Body Const) :
    BodyAvoidsParamStagesFromAt (Base := Base) (Const := Const) ℓ (maxParam body.2) body := by
  intro σ r k hbodyr
  exact noConstOccurrence_param_of_ge (Nat.pair ℓ (Nat.pair r k)) body.2
    (le_trans hbodyr
      (le_trans (Nat.left_le_pair r k) (Nat.right_le_pair ℓ (Nat.pair r k))))

/-- Every existential body has finite layer support. -/
theorem BodyAvoidsParamLayersFromAt.of_maxParam
    (body : Body Const) :
    BodyAvoidsParamLayersFromAt (Base := Base) (Const := Const) (maxParam body.2) body := by
  intro σ m k hbodym
  exact noConstOccurrence_param_of_ge (Nat.pair m k) body.2
    (Nat.le_trans hbodym (Nat.left_le_pair m k))

/-- Single-body future-layer support follows from a supported body enumeration. -/
theorem BodyAvoidsParamLayersFrom.at
    {ℓ : Nat} {enum : Nat → Body Const}
    (hEnum : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ enum)
    (n : Nat) :
    BodyAvoidsParamLayersFromAt (Base := Base) (Const := Const) ℓ (enum n) := by
  intro σ m k hℓm
  exact hEnum n σ m k hℓm

/-- Every closed disjunction pair has finite stage support inside a fixed outer
layer. -/
theorem FormulaPairAvoidsParamStagesFromAt.of_maxParam
    (ℓ : Nat) (pair : ClosedFormulaPair Const) :
    FormulaPairAvoidsParamStagesFromAt (Base := Base) (Const := Const) ℓ
      (max (maxParam pair.1) (maxParam pair.2)) pair := by
  intro σ r k hpairr
  constructor
  · exact noConstOccurrence_param_of_ge (Nat.pair ℓ (Nat.pair r k)) pair.1
      (le_trans (le_trans (le_max_left (maxParam pair.1) (maxParam pair.2)) hpairr)
        (le_trans (Nat.left_le_pair r k) (Nat.right_le_pair ℓ (Nat.pair r k))))
  · exact noConstOccurrence_param_of_ge (Nat.pair ℓ (Nat.pair r k)) pair.2
      (le_trans (le_trans (le_max_right (maxParam pair.1) (maxParam pair.2)) hpairr)
        (le_trans (Nat.left_le_pair r k) (Nat.right_le_pair ℓ (Nat.pair r k))))

/-- Every closed disjunction pair has finite layer support. -/
theorem FormulaPairAvoidsParamLayersFromAt.of_maxParam
    (pair : ClosedFormulaPair Const) :
    FormulaPairAvoidsParamLayersFromAt (Base := Base) (Const := Const)
      (max (maxParam pair.1) (maxParam pair.2)) pair := by
  intro σ m k hpairm
  constructor
  · exact noConstOccurrence_param_of_ge (Nat.pair m k) pair.1
      (Nat.le_trans (Nat.le_trans (le_max_left (maxParam pair.1) (maxParam pair.2)) hpairm)
        (Nat.left_le_pair m k))
  · exact noConstOccurrence_param_of_ge (Nat.pair m k) pair.2
      (Nat.le_trans (Nat.le_trans (le_max_right (maxParam pair.1) (maxParam pair.2)) hpairm)
        (Nat.left_le_pair m k))

/-- Body finite-support facts are monotone in the future-stage bound. -/
theorem BodyAvoidsParamStagesFromAt.mono
    {ℓ s r : Nat} (hsr : s ≤ r) {body : Body Const}
    (hBody : BodyAvoidsParamStagesFromAt (Base := Base) (Const := Const) ℓ s body) :
    BodyAvoidsParamStagesFromAt (Base := Base) (Const := Const) ℓ r body := by
  intro σ q k hrq
  exact hBody σ q k (le_trans hsr hrq)

/-- Body future-layer support is monotone in the lower layer bound. -/
theorem BodyAvoidsParamLayersFromAt.mono
    {ℓ m : Nat} (hℓm : ℓ ≤ m) {body : Body Const}
    (hBody : BodyAvoidsParamLayersFromAt (Base := Base) (Const := Const) ℓ body) :
    BodyAvoidsParamLayersFromAt (Base := Base) (Const := Const) m body := by
  intro σ r k hmr
  exact hBody σ r k (le_trans hℓm hmr)

/-- Pair future-layer support is monotone in the lower layer bound. -/
theorem FormulaPairAvoidsParamLayersFromAt.mono
    {ℓ m : Nat} (hℓm : ℓ ≤ m) {pair : ClosedFormulaPair Const}
    (hPair : FormulaPairAvoidsParamLayersFromAt (Base := Base) (Const := Const) ℓ pair) :
    FormulaPairAvoidsParamLayersFromAt (Base := Base) (Const := Const) m pair := by
  intro σ r k hmr
  exact hPair σ r k (le_trans hℓm hmr)

/-- Pair finite-support facts are monotone in the future-stage bound. -/
theorem FormulaPairAvoidsParamStagesFromAt.mono
    {ℓ s r : Nat} (hsr : s ≤ r) {pair : ClosedFormulaPair Const}
    (hPair : FormulaPairAvoidsParamStagesFromAt (Base := Base) (Const := Const) ℓ s pair) :
    FormulaPairAvoidsParamStagesFromAt (Base := Base) (Const := Const) ℓ r pair := by
  intro σ q k hrq
  exact hPair σ q k (le_trans hsr hrq)

/-- A level-bounded presented world whose closure readout is prime and
witnessed for formulas supported below its level. -/
structure SupportedPresentedIntuitionisticWorld (Const : Ty Base → Type v) where
  level : Nat
  raw : ClosedTheorySet (WithParams Const)
  raw_avoids_future :
    AvoidsParamLayersFrom (Base := Base) (Const := Const) level raw
  consistent :
    Consistent (Const := WithParams Const)
      (ClosedTheorySet.provableClosure (Const := WithParams Const) raw)
  supported_prime_or :
    ∀ {φ ψ : ClosedFormula (WithParams Const)},
      FormulaPairAvoidsParamLayersFromAt (Base := Base) (Const := Const) level (φ, ψ) →
      (.or φ ψ : ClosedFormula (WithParams Const)) ∈
        ClosedTheorySet.provableClosure (Const := WithParams Const) raw →
        φ ∈ ClosedTheorySet.provableClosure (Const := WithParams Const) raw ∨
          ψ ∈ ClosedTheorySet.provableClosure (Const := WithParams Const) raw
  supported_exists_witness :
    ∀ {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
      BodyAvoidsParamLayersFromAt (Base := Base) (Const := Const) level
        (⟨σ, φ⟩ : Body Const) →
      (.ex φ : ClosedFormula (WithParams Const)) ∈
        ClosedTheorySet.provableClosure (Const := WithParams Const) raw →
        ∃ t : ClosedTerm (WithParams Const) σ,
          instantiate (Base := Base) t φ ∈
            ClosedTheorySet.provableClosure (Const := WithParams Const) raw

namespace SupportedPresentedIntuitionisticWorld

/-- The closed carrier read from a supported presented world. -/
def carrier (W : SupportedPresentedIntuitionisticWorld Const) :
    ClosedTheorySet (WithParams Const) :=
  ClosedTheorySet.provableClosure (Const := WithParams Const) W.raw

theorem closed (W : SupportedPresentedIntuitionisticWorld Const) :
    DeductivelyClosed (Const := WithParams Const) W.carrier := by
  exact ClosedTheorySet.provableClosure_deductivelyClosed
    (Const := WithParams Const) W.raw

theorem raw_mem_carrier {W : SupportedPresentedIntuitionisticWorld Const}
    {φ : ClosedFormula (WithParams Const)} (hφ : φ ∈ W.raw) :
    φ ∈ W.carrier := by
  exact ClosedTheorySet.subset_provableClosure
    (Const := WithParams Const) W.raw hφ

end SupportedPresentedIntuitionisticWorld

/-- A level-bounded presented world whose closure readout is globally
disjunction-prime and existentially witnessed.  This is stronger than
`SupportedPresentedIntuitionisticWorld`: it keeps the raw support presentation
needed for freshness-sensitive successor arguments, while making the local
`∨`/`∃` Kripke clauses available without support side conditions. -/
structure FullPresentedIntuitionisticWorld (Const : Ty Base → Type v) where
  level : Nat
  raw : ClosedTheorySet (WithParams Const)
  raw_avoids_future :
    AvoidsParamLayersFrom (Base := Base) (Const := Const) level raw
  consistent :
    Consistent (Const := WithParams Const)
      (ClosedTheorySet.provableClosure (Const := WithParams Const) raw)
  prime_or :
    ∀ {φ ψ : ClosedFormula (WithParams Const)},
      (.or φ ψ : ClosedFormula (WithParams Const)) ∈
        ClosedTheorySet.provableClosure (Const := WithParams Const) raw →
        φ ∈ ClosedTheorySet.provableClosure (Const := WithParams Const) raw ∨
          ψ ∈ ClosedTheorySet.provableClosure (Const := WithParams Const) raw
  exists_witness :
    ∀ {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
      (.ex φ : ClosedFormula (WithParams Const)) ∈
        ClosedTheorySet.provableClosure (Const := WithParams Const) raw →
        ∃ t : ClosedTerm (WithParams Const) σ,
          instantiate (Base := Base) t φ ∈
            ClosedTheorySet.provableClosure (Const := WithParams Const) raw

namespace FullPresentedIntuitionisticWorld

/-- The closed carrier read from a full presented world. -/
def carrier (W : FullPresentedIntuitionisticWorld Const) :
    ClosedTheorySet (WithParams Const) :=
  ClosedTheorySet.provableClosure (Const := WithParams Const) W.raw

theorem closed (W : FullPresentedIntuitionisticWorld Const) :
    DeductivelyClosed (Const := WithParams Const) W.carrier := by
  exact ClosedTheorySet.provableClosure_deductivelyClosed
    (Const := WithParams Const) W.raw

theorem raw_mem_carrier {W : FullPresentedIntuitionisticWorld Const}
    {φ : ClosedFormula (WithParams Const)} (hφ : φ ∈ W.raw) :
    φ ∈ W.carrier := by
  exact ClosedTheorySet.subset_provableClosure
    (Const := WithParams Const) W.raw hφ

/-- Forget global local clauses, retaining the support-bounded interface. -/
def toSupported (W : FullPresentedIntuitionisticWorld Const) :
    SupportedPresentedIntuitionisticWorld (Base := Base) Const :=
  { level := W.level
    raw := W.raw
    raw_avoids_future := W.raw_avoids_future
    consistent := W.consistent
    supported_prime_or := by
      intro φ ψ _hSupport hOr
      exact W.prime_or hOr
    supported_exists_witness := by
      intro σ φ _hSupport hEx
      exact W.exists_witness hEx }

@[simp] theorem toSupported_level (W : FullPresentedIntuitionisticWorld Const) :
    W.toSupported.level = W.level := rfl

@[simp] theorem toSupported_raw (W : FullPresentedIntuitionisticWorld Const) :
    W.toSupported.raw = W.raw := rfl

@[simp] theorem toSupported_carrier (W : FullPresentedIntuitionisticWorld Const) :
    W.toSupported.carrier = W.carrier := rfl

end FullPresentedIntuitionisticWorld

/-- Single-pair future-layer support follows from a supported pair enumeration. -/
theorem FormulaPairAvoidsParamLayersFrom.at
    {ℓ : Nat} {enum : Nat → ClosedFormulaPair Const}
    (hEnum : FormulaPairAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ enum)
    (n : Nat) :
    FormulaPairAvoidsParamLayersFromAt (Base := Base) (Const := Const) ℓ (enum n) := by
  intro σ m k hℓm
  exact hEnum n σ m k hℓm

/-- Single-pair future-stage support follows from a supported pair enumeration. -/
theorem FormulaPairAvoidsParamStagesFrom.at
    {ℓ s : Nat} {enum : Nat → ClosedFormulaPair Const}
    (hEnum : FormulaPairAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ s enum)
    (n : Nat) :
    FormulaPairAvoidsParamStagesFromAt (Base := Base) (Const := Const) ℓ s (enum n) := by
  intro σ r k hsr
  exact hEnum n σ r k hsr

/-- Component freshness for a disjunction-pair enumeration at a reserved higher
level. -/
theorem formulaPairAvoids_fresh_for_levelSupply
    {ℓ m : Nat} (hm : ℓ ≤ m) {enum : Nat → ClosedFormulaPair Const}
    (hEnum : FormulaPairAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ enum)
    (n : Nat) :
    (∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ ((levelWitnessSupply m).index k)) (enum n).1) ∧
    (∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ ((levelWitnessSupply m).index k)) (enum n).2) := by
  constructor
  · intro σ k
    exact (hEnum n σ m k hm).1
  · intro σ k
    exact (hEnum n σ m k hm).2

/-- Raw disjunction decision over a level-image base.  This is the branch-choice
piece used before closing/witnessing: if the base proves `φ ∨ ψ` while omitting
`θ`, one disjunct can be inserted without deriving `θ`, and the chosen disjunct
retains freshness for a higher reserved supply. -/
theorem exists_raw_or_branch_levelImage_omitting
    {ℓ m : Nat}
    {T : ClosedTheorySet (LevelParams Const ℓ)}
    {φ ψ θ : ClosedFormula (WithParams Const)}
    (hNot : ¬ Provable (Const := WithParams Const)
      (mapLevelTheory (Base := Base) (Const := Const) ℓ T) θ)
    (hOr : Provable (Const := WithParams Const)
      (mapLevelTheory (Base := Base) (Const := Const) ℓ T) (.or φ ψ))
    (hφ : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ ((levelWitnessSupply m).index k)) φ)
    (hψ : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ ((levelWitnessSupply m).index k)) ψ) :
    ∃ δ : ClosedFormula (WithParams Const),
      (δ = φ ∨ δ = ψ) ∧
      ¬ Provable (Const := WithParams Const)
        (insert δ (mapLevelTheory (Base := Base) (Const := Const) ℓ T)) θ ∧
      (∀ (σ : Ty Base) (k : Nat),
        NoConstOccurrence (param σ ((levelWitnessSupply m).index k)) δ) := by
  have hBranch :=
    exists_or_branch_omitting (Const := WithParams Const)
      (T := mapLevelTheory (Base := Base) (Const := Const) ℓ T)
      (φ := φ) (ψ := ψ) (θ := θ) hNot hOr
  rcases hBranch with hLeft | hRight
  · exact ⟨φ, Or.inl rfl, hLeft, hφ⟩
  · exact ⟨ψ, Or.inr rfl, hRight, hψ⟩

/-- Enumeration-indexed raw branch choice, packaged with future-layer freshness
of the enlarged raw base. -/
theorem exists_raw_or_branch_from_enum_levelImage
    {ℓ m : Nat} (hm : ℓ ≤ m)
    {T : ClosedTheorySet (LevelParams Const ℓ)}
    {enum : Nat → ClosedFormulaPair Const}
    (hEnum : FormulaPairAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ enum)
    (n : Nat) {θ : ClosedFormula (WithParams Const)}
    (hNot : ¬ Provable (Const := WithParams Const)
      (mapLevelTheory (Base := Base) (Const := Const) ℓ T) θ)
    (hOr : Provable (Const := WithParams Const)
      (mapLevelTheory (Base := Base) (Const := Const) ℓ T)
      (.or (enum n).1 (enum n).2)) :
    ∃ δ : ClosedFormula (WithParams Const),
      (δ = (enum n).1 ∨ δ = (enum n).2) ∧
      ¬ Provable (Const := WithParams Const)
        (insert δ (mapLevelTheory (Base := Base) (Const := Const) ℓ T)) θ ∧
      (∀ ξ ∈ insert δ (mapLevelTheory (Base := Base) (Const := Const) ℓ T),
        ∀ (σ : Ty Base) (k : Nat),
          NoConstOccurrence (param σ ((levelWitnessSupply m).index k)) ξ) := by
  obtain ⟨hφ, hψ⟩ :=
    formulaPairAvoids_fresh_for_levelSupply
      (Base := Base) (Const := Const) hm hEnum n
  obtain ⟨δ, hδchoice, hδNot, hδfresh⟩ :=
    exists_raw_or_branch_levelImage_omitting
      (Base := Base) (Const := Const)
      (T := T) hNot hOr hφ hψ
  refine ⟨δ, hδchoice, hδNot, ?_⟩
  exact fresh_for_levelSupply_insert
    (Base := Base) (Const := Const)
    (m := m)
    (T := mapLevelTheory (Base := Base) (Const := Const) ℓ T)
    (θ := δ)
    (mapLevelTheory_fresh_for_higherLevelSupply
      (Base := Base) (Const := Const) hm T)
    hδfresh

/-- A parameter from one layer does not occur in a parameter constant from a
different layer. -/
theorem noConstOccurrence_param_pair_ne_const
    {σ ρ : Ty Base} {m ℓ k j : Nat} (hm : m ≠ ℓ) :
    NoConstOccurrence
      (param σ (Nat.pair m k) : WithParams Const σ)
      (.const (param ρ (Nat.pair ℓ j)) : ClosedTerm (WithParams Const) ρ) := by
  by_cases hσρ : σ = ρ
  · subst hσρ
    refine NoConstOccurrence.const_same_ne (param σ (Nat.pair ℓ j)) ?_
    intro heq
    have hp : Nat.pair ℓ j = Nat.pair m k := param_inj heq
    exact hm ((Nat.pair_eq_pair.mp hp).1.symm)
  · exact NoConstOccurrence.const_diff_type hσρ (param ρ (Nat.pair ℓ j))

/-- Instantiating with a parameter from layer `ℓ` preserves absence of a
parameter from a different layer. -/
theorem noConstOccurrence_param_pair_ne_instantiate
    {σ ρ : Ty Base} {m ℓ k j : Nat} {φ : Formula (WithParams Const) [ρ]}
    (hm : m ≠ ℓ)
    (hφ : NoConstOccurrence (param σ (Nat.pair m k) : WithParams Const σ) φ) :
    NoConstOccurrence
      (param σ (Nat.pair m k) : WithParams Const σ)
      (instantiate (Base := Base) (.const (param ρ (Nat.pair ℓ j))) φ) := by
  exact noConstOccurrence_instantiate
    (noConstOccurrence_param_pair_ne_const
      (Const := Const) (σ := σ) (ρ := ρ) (m := m) (ℓ := ℓ) (k := k) (j := j) hm)
    hφ

/-- A parameter from one stage of a fixed outer layer does not occur in a
parameter constant from a different stage of that same layer. -/
theorem noConstOccurrence_param_stage_ne_const
    {σ ρ : Ty Base} {ℓ r s k j : Nat} (hrs : r ≠ s) :
    NoConstOccurrence
      (param σ (Nat.pair ℓ (Nat.pair r k)) : WithParams Const σ)
      (.const (param ρ (Nat.pair ℓ (Nat.pair s j))) : ClosedTerm (WithParams Const) ρ) := by
  by_cases hσρ : σ = ρ
  · subst hσρ
    refine NoConstOccurrence.const_same_ne (param σ (Nat.pair ℓ (Nat.pair s j))) ?_
    intro heq
    have hp : Nat.pair ℓ (Nat.pair s j) = Nat.pair ℓ (Nat.pair r k) := param_inj heq
    have hsreq : s = r := (Nat.pair_eq_pair.mp ((Nat.pair_eq_pair.mp hp).2)).1
    exact hrs hsreq.symm
  · exact NoConstOccurrence.const_diff_type hσρ (param ρ (Nat.pair ℓ (Nat.pair s j)))

/-- Instantiating with a parameter from stage `s` preserves absence of a
parameter from a different stage `r` in the same outer layer. -/
theorem noConstOccurrence_param_stage_ne_instantiate
    {σ ρ : Ty Base} {ℓ r s k j : Nat} {φ : Formula (WithParams Const) [ρ]}
    (hrs : r ≠ s)
    (hφ :
      NoConstOccurrence (param σ (Nat.pair ℓ (Nat.pair r k)) : WithParams Const σ) φ) :
    NoConstOccurrence
      (param σ (Nat.pair ℓ (Nat.pair r k)) : WithParams Const σ)
      (instantiate (Base := Base)
        (.const (param ρ (Nat.pair ℓ (Nat.pair s j))) :
          ClosedTerm (WithParams Const) ρ) φ) := by
  exact noConstOccurrence_instantiate
    (noConstOccurrence_param_stage_ne_const
      (Const := Const) (σ := σ) (ρ := ρ) (ℓ := ℓ) (r := r) (s := s)
      (k := k) (j := j) hrs)
    hφ

/-- A level-`ℓ` witness instance preserves absence of all strictly higher
parameter layers. -/
theorem witnessInstance_levelWitnessSupply_avoids_future_layers
    {ℓ n : Nat} {T : ClosedTheorySet (WithParams Const)} {enum : Nat → Body Const}
    (hEnum : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) enum) :
    ∀ (σ : Ty Base) (m k : Nat), ℓ + 1 ≤ m →
      NoConstOccurrence (param σ (Nat.pair m k) : WithParams Const σ)
        (instantiate (Base := Base)
          (.const (param (enum n).1 ((levelWitnessSupply ℓ).index
            (witnessIndex
              (witnessInstanceChainUsing (levelWitnessSupply ℓ) T enum n) (enum n)))))
          (enum n).2) := by
  intro σ m k hm
  refine noConstOccurrence_param_pair_ne_instantiate
    (Const := Const) (σ := σ) (ρ := (enum n).1) (m := m) (ℓ := ℓ) (k := k)
    (j := witnessIndex
      (witnessInstanceChainUsing (levelWitnessSupply ℓ) T enum n) (enum n))
    ?_ ?_
  · omega
  · exact hEnum n σ m k hm

/-- Every formula in a level-`ℓ` omission-preserving witness-instance chain
avoids strictly higher parameter layers when the base and enumerated bodies do. -/
theorem witnessInstanceChainUsing_levelWitnessSupply_avoids_future_layers
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)} {enum : Nat → Body Const}
    (hEnum : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) enum) :
    ∀ n, ∀ {ψ : ClosedFormula (WithParams Const)},
      ψ ∈ witnessInstanceChainUsing (levelWitnessSupply ℓ) T enum n →
        ∀ (σ : Ty Base) (m k : Nat), ℓ + 1 ≤ m →
          NoConstOccurrence (param σ (Nat.pair m k)) ψ := by
  intro n
  induction n with
  | zero =>
      intro ψ hψ
      simp [witnessInstanceChainUsing] at hψ
  | succ n ih =>
      intro ψ hψ σ m k hm
      classical
      simp only [witnessInstanceChainUsing] at hψ
      by_cases hEx : Provable (Const := WithParams Const)
          (T ∪ {ψ | ψ ∈ witnessInstanceChainUsing (levelWitnessSupply ℓ) T enum n})
          (.ex (enum n).2)
      · simp [hEx] at hψ
        rcases hψ with hhead | htail
        · subst hhead
          exact witnessInstance_levelWitnessSupply_avoids_future_layers
            (Base := Base) (Const := Const) (ℓ := ℓ) (n := n) (T := T)
            (enum := enum) hEnum σ m k hm
        · exact ih htail σ m k hm
      · simp [hEx] at hψ
        exact ih hψ σ m k hm

/-- The level-`ℓ` omission-preserving witness-instance limit of a theory that
avoids all strictly higher layers also avoids those higher layers. -/
theorem witnessInstanceLimitUsing_levelWitnessSupply_avoids_future_layers
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)} {enum : Nat → Body Const}
    (hT : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hEnum : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) enum) :
    AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1)
      (witnessInstanceLimitUsing (levelWitnessSupply ℓ) T enum) := by
  intro ψ hψ σ m k hm
  simp only [witnessInstanceLimitUsing, Set.mem_union, Set.mem_setOf_eq] at hψ
  rcases hψ with hψT | ⟨n, hψn⟩
  · exact hT ψ hψT σ m k hm
  · exact witnessInstanceChainUsing_levelWitnessSupply_avoids_future_layers
      (Base := Base) (Const := Const) (ℓ := ℓ) (T := T) (enum := enum)
      hEnum n hψn σ m k hm

/-- An omission-preserving witness instance inserted at stage `s` of layer `ℓ`
preserves absence of all strictly higher parameter layers. -/
theorem witnessInstance_stageWitnessSupply_avoids_future_layers
    {ℓ s n : Nat} {T : ClosedTheorySet (WithParams Const)} {enum : Nat → Body Const}
    (hEnum : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) enum) :
    ∀ (σ : Ty Base) (m k : Nat), ℓ + 1 ≤ m →
      NoConstOccurrence (param σ (Nat.pair m k) : WithParams Const σ)
        (instantiate (Base := Base)
          (.const (param (enum n).1 ((stageWitnessSupply ℓ s).index
            (witnessIndex
              (witnessInstanceChainUsing (stageWitnessSupply ℓ s) T enum n) (enum n)))))
          (enum n).2) := by
  intro σ m k hm
  refine noConstOccurrence_param_pair_ne_instantiate
    (Const := Const) (σ := σ) (ρ := (enum n).1) (m := m) (ℓ := ℓ) (k := k)
    (j := Nat.pair s
      (witnessIndex
        (witnessInstanceChainUsing (stageWitnessSupply ℓ s) T enum n) (enum n)))
    ?_ ?_
  · omega
  · exact hEnum n σ m k hm

/-- An omission-preserving witness instance inserted at stage `s` of layer `ℓ`
preserves absence of all later stages in that same outer layer. -/
theorem witnessInstance_stageWitnessSupply_avoids_future_stages
    {ℓ s n : Nat} {T : ClosedTheorySet (WithParams Const)} {enum : Nat → Body Const}
    (hEnum : BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1) enum) :
    ∀ (σ : Ty Base) (r k : Nat), s + 1 ≤ r →
      NoConstOccurrence (param σ (Nat.pair ℓ (Nat.pair r k)) : WithParams Const σ)
        (instantiate (Base := Base)
          (.const (param (enum n).1 ((stageWitnessSupply ℓ s).index
            (witnessIndex
              (witnessInstanceChainUsing (stageWitnessSupply ℓ s) T enum n) (enum n)))))
          (enum n).2) := by
  intro σ r k hrs
  refine noConstOccurrence_param_stage_ne_instantiate
    (Const := Const) (σ := σ) (ρ := (enum n).1) (ℓ := ℓ) (r := r) (s := s)
    (k := k)
    (j := witnessIndex
      (witnessInstanceChainUsing (stageWitnessSupply ℓ s) T enum n) (enum n))
    ?_ ?_
  · omega
  · exact hEnum n σ r k hrs

/-- Every formula in a stage-`s` omission-preserving witness-instance chain
avoids strictly higher parameter layers when the base and enumerated bodies do. -/
theorem witnessInstanceChainUsing_stageWitnessSupply_avoids_future_layers
    {ℓ s : Nat} {T : ClosedTheorySet (WithParams Const)} {enum : Nat → Body Const}
    (hEnum : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) enum) :
    ∀ n, ∀ {ψ : ClosedFormula (WithParams Const)},
      ψ ∈ witnessInstanceChainUsing (stageWitnessSupply ℓ s) T enum n →
        ∀ (σ : Ty Base) (m k : Nat), ℓ + 1 ≤ m →
          NoConstOccurrence (param σ (Nat.pair m k)) ψ := by
  intro n
  induction n with
  | zero =>
      intro ψ hψ
      simp [witnessInstanceChainUsing] at hψ
  | succ n ih =>
      intro ψ hψ σ m k hm
      classical
      simp only [witnessInstanceChainUsing] at hψ
      by_cases hEx : Provable (Const := WithParams Const)
          (T ∪ {ψ | ψ ∈ witnessInstanceChainUsing (stageWitnessSupply ℓ s) T enum n})
          (.ex (enum n).2)
      · simp [hEx] at hψ
        rcases hψ with hhead | htail
        · subst hhead
          exact witnessInstance_stageWitnessSupply_avoids_future_layers
            (Base := Base) (Const := Const) (ℓ := ℓ) (s := s) (n := n) (T := T)
            (enum := enum) hEnum σ m k hm
        · exact ih htail σ m k hm
      · simp [hEx] at hψ
        exact ih hψ σ m k hm

/-- Every formula in a stage-`s` omission-preserving witness-instance chain
avoids later stages of the same outer layer when the base and enumerated bodies do. -/
theorem witnessInstanceChainUsing_stageWitnessSupply_avoids_future_stages
    {ℓ s : Nat} {T : ClosedTheorySet (WithParams Const)} {enum : Nat → Body Const}
    (hEnum : BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1) enum) :
    ∀ n, ∀ {ψ : ClosedFormula (WithParams Const)},
      ψ ∈ witnessInstanceChainUsing (stageWitnessSupply ℓ s) T enum n →
        ∀ (σ : Ty Base) (r k : Nat), s + 1 ≤ r →
          NoConstOccurrence (param σ (Nat.pair ℓ (Nat.pair r k))) ψ := by
  intro n
  induction n with
  | zero =>
      intro ψ hψ
      simp [witnessInstanceChainUsing] at hψ
  | succ n ih =>
      intro ψ hψ σ r k hrs
      classical
      simp only [witnessInstanceChainUsing] at hψ
      by_cases hEx : Provable (Const := WithParams Const)
          (T ∪ {ψ | ψ ∈ witnessInstanceChainUsing (stageWitnessSupply ℓ s) T enum n})
          (.ex (enum n).2)
      · simp [hEx] at hψ
        rcases hψ with hhead | htail
        · subst hhead
          exact witnessInstance_stageWitnessSupply_avoids_future_stages
            (Base := Base) (Const := Const) (ℓ := ℓ) (s := s) (n := n) (T := T)
            (enum := enum) hEnum σ r k hrs
        · exact ih htail σ r k hrs
      · simp [hEx] at hψ
        exact ih hψ σ r k hrs

/-- The stage-`s` omission-preserving witness-instance limit of a theory that
avoids higher layers also avoids those higher layers. -/
theorem witnessInstanceLimitUsing_stageWitnessSupply_avoids_future_layers
    {ℓ s : Nat} {T : ClosedTheorySet (WithParams Const)} {enum : Nat → Body Const}
    (hT : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hEnum : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) enum) :
    AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1)
      (witnessInstanceLimitUsing (stageWitnessSupply ℓ s) T enum) := by
  intro ψ hψ σ m k hm
  simp only [witnessInstanceLimitUsing, Set.mem_union, Set.mem_setOf_eq] at hψ
  rcases hψ with hψT | ⟨n, hψn⟩
  · exact hT ψ hψT σ m k hm
  · exact witnessInstanceChainUsing_stageWitnessSupply_avoids_future_layers
      (Base := Base) (Const := Const) (ℓ := ℓ) (s := s) (T := T) (enum := enum)
      hEnum n hψn σ m k hm

/-- The stage-`s` omission-preserving witness-instance limit of a theory that
avoids later stages in the same outer layer also avoids those later stages. -/
theorem witnessInstanceLimitUsing_stageWitnessSupply_avoids_future_stages
    {ℓ s : Nat} {T : ClosedTheorySet (WithParams Const)} {enum : Nat → Body Const}
    (hT : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1) T)
    (hEnum : BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1) enum) :
    AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1)
      (witnessInstanceLimitUsing (stageWitnessSupply ℓ s) T enum) := by
  intro ψ hψ σ r k hrs
  simp only [witnessInstanceLimitUsing, Set.mem_union, Set.mem_setOf_eq] at hψ
  rcases hψ with hψT | ⟨n, hψn⟩
  · exact hT ψ hψT σ r k hrs
  · exact witnessInstanceChainUsing_stageWitnessSupply_avoids_future_stages
      (Base := Base) (Const := Const) (ℓ := ℓ) (s := s) (T := T) (enum := enum)
      hEnum n hψn σ r k hrs

/-- A stage-local variant of the fair witness-instance property.  It only
promises witnesses for bodies covered by the stage-local enumeration, which is
the form needed for fixed-layer Kripke successors. -/
theorem exists_witnessInstanceLimitUsing_of_stageFair
    (supply : WitnessSupply) (T : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) {ℓ s : Nat}
    (hfair : BodyStageFairAfter (Base := Base) (Const := Const) ℓ s enum) :
    ∀ {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
      BodyAvoidsParamLayersFromAt (Base := Base) (Const := Const) (ℓ + 1)
        (⟨σ, φ⟩ : Body Const) →
      BodyAvoidsParamStagesFromAt (Base := Base) (Const := Const) ℓ s
        (⟨σ, φ⟩ : Body Const) →
      Provable (Const := WithParams Const)
        (witnessInstanceLimitUsing supply T enum) (.ex φ) →
      ∃ t : ClosedTerm (WithParams Const) σ,
        instantiate (Base := Base) t φ ∈ witnessInstanceLimitUsing supply T enum := by
  intro σ φ hBodyLayer hBodyStage hEx
  rcases hEx with ⟨Γ, hΓ, d⟩
  obtain ⟨N, hN⟩ := exists_stage_instance_using supply T enum Γ hΓ
  have hExStage : Provable (Const := WithParams Const)
      (witnessInstanceTheoryUsing supply T enum N) (.ex φ) :=
    ⟨Γ, hN, d⟩
  obtain ⟨n, hNn, hn⟩ := hfair ⟨σ, φ⟩ hBodyLayer hBodyStage N
  have hExAtN : Provable (Const := WithParams Const)
      (witnessInstanceTheoryUsing supply T enum n) (.ex φ) :=
    provable_mono (Const := WithParams Const)
      (T := witnessInstanceTheoryUsing supply T enum N)
      (U := witnessInstanceTheoryUsing supply T enum n)
      (by intro ψ hψ; exact witnessInstanceTheoryUsing_mono supply T enum hNn hψ)
      hExStage
  rcases hEnum : enum n with ⟨ρ, χ⟩
  have hEq : ρ = σ ∧ HEq χ φ := by
    simpa [hEnum, Sigma.ext_iff] using hn
  rcases hEq with ⟨hρ, hχ⟩
  subst hρ
  cases hχ
  let k := supply.index (witnessIndex (witnessInstanceChainUsing supply T enum n) ⟨ρ, χ⟩)
  refine ⟨.const (param ρ k), ?_⟩
  refine Set.mem_union_right _ ?_
  refine ⟨n + 1, ?_⟩
  have hExRaw : Provable (Const := WithParams Const)
      (T ∪ {ψ | ψ ∈ witnessInstanceChainUsing supply T enum n}) (.ex χ) := by
    simpa [witnessInstanceTheoryUsing] using hExAtN
  have hExRawEnum : Provable (Const := WithParams Const)
      (T ∪ {ψ | ψ ∈ witnessInstanceChainUsing supply T enum n}) (.ex (enum n).2) := by
    rw [hEnum]
    exact hExRaw
  rw [witnessInstanceChainUsing]
  simp only [hExRawEnum, if_true, List.mem_cons]
  left
  rw [hEnum]

/-- One raw alternating step: decide one enumerated disjunction, then run the
omission-preserving witness-instance saturation at the current layer.  The
result is still raw, extends the old raw base, contains the chosen disjunct,
omits the target, and avoids all parameters from the next layer upward. -/
theorem exists_raw_branch_witnessInstance_step
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const) (n : Nat)
    {θ : ClosedFormula (WithParams Const)}
    (hT : AvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ T)
    (hBody : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hPair : FormulaPairAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ pairEnum)
    (hθ : FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ)
    (hOr : Provable (Const := WithParams Const) T (.or (pairEnum n).1 (pairEnum n).2)) :
    ∃ R : ClosedTheorySet (WithParams Const),
      ∃ δ : ClosedFormula (WithParams Const),
        (δ = (pairEnum n).1 ∨ δ = (pairEnum n).2) ∧
        (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ R) ∧
        δ ∈ R ∧
        ¬ Provable (Const := WithParams Const) R θ ∧
        AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) R ∧
        (∀ {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
          Provable (Const := WithParams Const) R (.ex φ) →
            ∃ t : ClosedTerm (WithParams Const) σ,
              instantiate (Base := Base) t φ ∈ R) := by
  let supply := levelWitnessSupply ℓ
  have hTsupply : ∀ ξ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) ξ := by
    intro ξ hξ σ k
    exact hT ξ hξ σ ℓ k (le_refl ℓ)
  have hLeftFresh : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) (pairEnum n).1 := by
    intro σ k
    exact (hPair n σ ℓ k (le_refl ℓ)).1
  have hRightFresh : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) (pairEnum n).2 := by
    intro σ k
    exact (hPair n σ ℓ k (le_refl ℓ)).2
  obtain ⟨δ, hδchoice, hδNot, _hδSupply⟩ :=
    exists_raw_or_branch_supply_omitting
      (Base := Base) (Const := Const) supply
      (T₀ := T) hNot hOr hTsupply hLeftFresh hRightFresh
  let Tδ : ClosedTheorySet (WithParams Const) := insert δ T
  let R : ClosedTheorySet (WithParams Const) :=
    witnessInstanceLimitUsing supply Tδ bodyEnum
  have hδFuture : FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ δ := by
    rcases hδchoice with rfl | rfl
    · intro σ m k hℓm
      exact (hPair n σ m k hℓm).1
    · intro σ m k hℓm
      exact (hPair n σ m k hℓm).2
  have hTδ : AvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ Tδ :=
    AvoidsParamLayersFrom.insert
      (Base := Base) (Const := Const) hT hδFuture
  have hTδNext : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) Tδ :=
    AvoidsParamLayersFrom.mono
      (Base := Base) (Const := Const) (Nat.le_succ ℓ) hTδ
  have hTδSupply : ∀ ξ ∈ Tδ, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) ξ := by
    intro ξ hξ σ k
    exact hTδ ξ hξ σ ℓ k (le_refl ℓ)
  have hθSupply : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) θ := by
    intro σ k
    exact hθ σ ℓ k (le_refl ℓ)
  have hOmitR : ¬ Provable (Const := WithParams Const) R θ := by
    exact witnessInstanceLimitUsing_omits
      (Base := Base) (Const := Const) supply Tδ bodyEnum hδNot hTδSupply hθSupply
  have hAvoidR : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) R := by
    exact witnessInstanceLimitUsing_levelWitnessSupply_avoids_future_layers
      (Base := Base) (Const := Const) (ℓ := ℓ) (T := Tδ) (enum := bodyEnum)
      hTδNext hBody
  refine ⟨R, δ, hδchoice, ?_, ?_, hOmitR, hAvoidR, ?_⟩
  · intro ψ hψ
    exact subset_witnessInstanceLimitUsing
      (Base := Base) (Const := Const) supply Tδ bodyEnum
      (Set.mem_insert_of_mem δ hψ)
  · exact subset_witnessInstanceLimitUsing
      (Base := Base) (Const := Const) supply Tδ bodyEnum
      (Set.mem_insert δ T)
  · intro σ φ hEx
    exact exists_witnessInstanceLimitUsing
      (Base := Base) (Const := Const) supply Tδ bodyEnum hfair hEx

/-- A raw witness-repair step without a disjunction decision.  This is the
fallback branch of the alternating construction when the currently enumerated
disjunction is not yet derivable from the raw stage. -/
theorem exists_raw_witnessInstance_step
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    {θ : ClosedFormula (WithParams Const)}
    (hT : AvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ T)
    (hBody : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hθ : FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ∃ R : ClosedTheorySet (WithParams Const),
      (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ R) ∧
      ¬ Provable (Const := WithParams Const) R θ ∧
      AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) R ∧
      (∀ {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
        Provable (Const := WithParams Const) R (.ex φ) →
          ∃ t : ClosedTerm (WithParams Const) σ,
            instantiate (Base := Base) t φ ∈ R) := by
  let supply := levelWitnessSupply ℓ
  let R : ClosedTheorySet (WithParams Const) :=
    witnessInstanceLimitUsing supply T bodyEnum
  have hTsupply : ∀ ξ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) ξ := by
    intro ξ hξ σ k
    exact hT ξ hξ σ ℓ k (le_refl ℓ)
  have hθSupply : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) θ := by
    intro σ k
    exact hθ σ ℓ k (le_refl ℓ)
  have hTNext : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T :=
    AvoidsParamLayersFrom.mono
      (Base := Base) (Const := Const) (Nat.le_succ ℓ) hT
  have hOmitR : ¬ Provable (Const := WithParams Const) R θ :=
    witnessInstanceLimitUsing_omits
      (Base := Base) (Const := Const) supply T bodyEnum hNot hTsupply hθSupply
  have hAvoidR : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) R :=
    witnessInstanceLimitUsing_levelWitnessSupply_avoids_future_layers
      (Base := Base) (Const := Const) (ℓ := ℓ) (T := T) (enum := bodyEnum)
      hTNext hBody
  refine ⟨R, ?_, hOmitR, hAvoidR, ?_⟩
  · intro ψ hψ
    exact subset_witnessInstanceLimitUsing
      (Base := Base) (Const := Const) supply T bodyEnum hψ
  · intro σ φ hEx
    exact exists_witnessInstanceLimitUsing
      (Base := Base) (Const := Const) supply T bodyEnum hfair hEx

/-- A raw witness-repair step using only stage `s` inside outer layer `ℓ`.  The
result preserves the finite outer support bound `ℓ + 1` while consuming only the
current stage supply, so it avoids all later stages `s + 1, s + 2, ...`. -/
theorem exists_raw_witnessInstance_stage_step
    {ℓ s : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ s T)
    (hBodyLayer : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hBodyStage : BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1) bodyEnum)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ s θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ∃ R : ClosedTheorySet (WithParams Const),
      (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ R) ∧
      ¬ Provable (Const := WithParams Const) R θ ∧
      AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) R ∧
      AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1) R ∧
      (∀ {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
        Provable (Const := WithParams Const) R (.ex φ) →
          ∃ t : ClosedTerm (WithParams Const) σ,
            instantiate (Base := Base) t φ ∈ R) := by
  let supply := stageWitnessSupply ℓ s
  let R : ClosedTheorySet (WithParams Const) :=
    witnessInstanceLimitUsing supply T bodyEnum
  have hTsupply : ∀ ξ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) ξ := by
    exact AvoidsParamStagesFrom.fresh_for_stageSupply
      (Base := Base) (Const := Const) (ℓ := ℓ) (s := s) hStage
  have hθSupply : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) θ := by
    exact FormulaAvoidsParamStagesFrom.fresh_for_stageSupply
      (Base := Base) (Const := Const) (ℓ := ℓ) (s := s) hθStage
  have hStageNext : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1) T :=
    AvoidsParamStagesFrom.mono
      (Base := Base) (Const := Const) (Nat.le_succ s) hStage
  have hOmitR : ¬ Provable (Const := WithParams Const) R θ :=
    witnessInstanceLimitUsing_omits
      (Base := Base) (Const := Const) supply T bodyEnum hNot hTsupply hθSupply
  have hAvoidLayerR : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) R :=
    witnessInstanceLimitUsing_stageWitnessSupply_avoids_future_layers
      (Base := Base) (Const := Const) (ℓ := ℓ) (s := s) (T := T) (enum := bodyEnum)
      hLayer hBodyLayer
  have hAvoidStageR : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1) R :=
    witnessInstanceLimitUsing_stageWitnessSupply_avoids_future_stages
      (Base := Base) (Const := Const) (ℓ := ℓ) (s := s) (T := T) (enum := bodyEnum)
      hStageNext hBodyStage
  refine ⟨R, ?_, hOmitR, hAvoidLayerR, hAvoidStageR, ?_⟩
  · intro ψ hψ
    exact subset_witnessInstanceLimitUsing
      (Base := Base) (Const := Const) supply T bodyEnum hψ
  · intro σ φ hEx
    exact exists_witnessInstanceLimitUsing
      (Base := Base) (Const := Const) supply T bodyEnum hfair hEx

/-- Stage-local raw witness repair.  Unlike
`exists_raw_witnessInstance_stage_step`, this does not require the stage
enumeration to be fair for every body in the full language; it witnesses exactly
the bodies whose support stays below the next stage. -/
theorem exists_raw_witnessInstance_stage_step_of_stageFair
    {ℓ s : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyStageFairAfter (Base := Base) (Const := Const) ℓ (s + 1) bodyEnum)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ s T)
    (hBodyLayer : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hBodyStage : BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1) bodyEnum)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ s θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ∃ R : ClosedTheorySet (WithParams Const),
      (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ R) ∧
      ¬ Provable (Const := WithParams Const) R θ ∧
      AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) R ∧
      AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1) R ∧
      (∀ {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
        BodyAvoidsParamLayersFromAt (Base := Base) (Const := Const) (ℓ + 1)
          (⟨σ, φ⟩ : Body Const) →
        BodyAvoidsParamStagesFromAt (Base := Base) (Const := Const) ℓ (s + 1)
          (⟨σ, φ⟩ : Body Const) →
        Provable (Const := WithParams Const) R (.ex φ) →
          ∃ t : ClosedTerm (WithParams Const) σ,
            instantiate (Base := Base) t φ ∈ R) := by
  let supply := stageWitnessSupply ℓ s
  let R : ClosedTheorySet (WithParams Const) :=
    witnessInstanceLimitUsing supply T bodyEnum
  have hTsupply : ∀ ξ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) ξ := by
    exact AvoidsParamStagesFrom.fresh_for_stageSupply
      (Base := Base) (Const := Const) (ℓ := ℓ) (s := s) hStage
  have hθSupply : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) θ := by
    exact FormulaAvoidsParamStagesFrom.fresh_for_stageSupply
      (Base := Base) (Const := Const) (ℓ := ℓ) (s := s) hθStage
  have hStageNext : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1) T :=
    AvoidsParamStagesFrom.mono
      (Base := Base) (Const := Const) (Nat.le_succ s) hStage
  have hOmitR : ¬ Provable (Const := WithParams Const) R θ :=
    witnessInstanceLimitUsing_omits
      (Base := Base) (Const := Const) supply T bodyEnum hNot hTsupply hθSupply
  have hAvoidLayerR : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) R :=
    witnessInstanceLimitUsing_stageWitnessSupply_avoids_future_layers
      (Base := Base) (Const := Const) (ℓ := ℓ) (s := s) (T := T) (enum := bodyEnum)
      hLayer hBodyLayer
  have hAvoidStageR : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1) R :=
    witnessInstanceLimitUsing_stageWitnessSupply_avoids_future_stages
      (Base := Base) (Const := Const) (ℓ := ℓ) (s := s) (T := T) (enum := bodyEnum)
      hStageNext hBodyStage
  refine ⟨R, ?_, hOmitR, hAvoidLayerR, hAvoidStageR, ?_⟩
  · intro ψ hψ
    exact subset_witnessInstanceLimitUsing
      (Base := Base) (Const := Const) supply T bodyEnum hψ
  · intro σ φ hBodyLayer hBodyStage hEx
    exact exists_witnessInstanceLimitUsing_of_stageFair
      (Base := Base) (Const := Const) supply T bodyEnum hfair hBodyLayer hBodyStage hEx

/-- A stage-indexed raw branch-and-witness step.  It decides one currently
proved disjunction, inserts an omission-preserving disjunct, then repairs
witnesses using only the same stage supply. -/
theorem exists_raw_branch_witnessInstance_stage_step
    {ℓ s : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const) (n : Nat)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ s T)
    (hBodyLayer : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hBodyStage : BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1) bodyEnum)
    (hPairLayer : FormulaPairAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (ℓ + 1) pairEnum)
    (hPairStage : FormulaPairAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ s pairEnum)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ s θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ)
    (hOr : Provable (Const := WithParams Const) T (.or (pairEnum n).1 (pairEnum n).2)) :
    ∃ R : ClosedTheorySet (WithParams Const),
      ∃ δ : ClosedFormula (WithParams Const),
        (δ = (pairEnum n).1 ∨ δ = (pairEnum n).2) ∧
        (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ R) ∧
        δ ∈ R ∧
        ¬ Provable (Const := WithParams Const) R θ ∧
        AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) R ∧
        AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1) R ∧
        (∀ {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
          Provable (Const := WithParams Const) R (.ex φ) →
            ∃ t : ClosedTerm (WithParams Const) σ,
              instantiate (Base := Base) t φ ∈ R) := by
  let supply := stageWitnessSupply ℓ s
  have hTsupply : ∀ ξ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) ξ := by
    exact AvoidsParamStagesFrom.fresh_for_stageSupply
      (Base := Base) (Const := Const) (ℓ := ℓ) (s := s) hStage
  have hLeftFresh : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) (pairEnum n).1 := by
    intro σ k
    exact (hPairStage n σ s k (le_refl s)).1
  have hRightFresh : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) (pairEnum n).2 := by
    intro σ k
    exact (hPairStage n σ s k (le_refl s)).2
  obtain ⟨δ, hδchoice, hδNot, _hδSupply⟩ :=
    exists_raw_or_branch_supply_omitting
      (Base := Base) (Const := Const) supply
      (T₀ := T) hNot hOr hTsupply hLeftFresh hRightFresh
  let Tδ : ClosedTheorySet (WithParams Const) := insert δ T
  have hδLayer : FormulaAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (ℓ + 1) δ := by
    rcases hδchoice with rfl | rfl
    · intro σ m k hℓm
      exact (hPairLayer n σ m k hℓm).1
    · intro σ m k hℓm
      exact (hPairLayer n σ m k hℓm).2
  have hδStage : FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ s δ := by
    rcases hδchoice with rfl | rfl
    · intro σ r k hsr
      exact (hPairStage n σ r k hsr).1
    · intro σ r k hsr
      exact (hPairStage n σ r k hsr).2
  have hTδLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) Tδ :=
    AvoidsParamLayersFrom.insert
      (Base := Base) (Const := Const) hLayer hδLayer
  have hTδStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ s Tδ :=
    AvoidsParamStagesFrom.insert
      (Base := Base) (Const := Const) hStage hδStage
  obtain ⟨R, hExtTδ, hOmit, hAvoidLayer, hAvoidStage, hWitness⟩ :=
    exists_raw_witnessInstance_stage_step
      (Base := Base) (Const := Const) (ℓ := ℓ) (s := s) (T := Tδ)
      bodyEnum hfair hTδLayer hTδStage hBodyLayer hBodyStage hθStage hδNot
  refine ⟨R, δ, hδchoice, ?_, ?_, hOmit, hAvoidLayer, hAvoidStage, hWitness⟩
  · intro ψ hψ
    exact hExtTδ (Set.mem_insert_of_mem δ hψ)
  · exact hExtTδ (Set.mem_insert δ T)

/-- Stage-local branch-and-witness step with the same local witness guarantee as
`exists_raw_witnessInstance_stage_step_of_stageFair`. -/
theorem exists_raw_branch_witnessInstance_stage_step_of_stageFair
    {ℓ s : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyStageFairAfter (Base := Base) (Const := Const) ℓ (s + 1) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const) (n : Nat)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ s T)
    (hBodyLayer : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hBodyStage : BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1) bodyEnum)
    (hPairLayer : FormulaPairAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (ℓ + 1) pairEnum)
    (hPairStage : FormulaPairAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ s pairEnum)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ s θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ)
    (hOr : Provable (Const := WithParams Const) T (.or (pairEnum n).1 (pairEnum n).2)) :
    ∃ R : ClosedTheorySet (WithParams Const),
      ∃ δ : ClosedFormula (WithParams Const),
        (δ = (pairEnum n).1 ∨ δ = (pairEnum n).2) ∧
        (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ R) ∧
        δ ∈ R ∧
        ¬ Provable (Const := WithParams Const) R θ ∧
        AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) R ∧
        AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1) R ∧
        (∀ {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
          BodyAvoidsParamLayersFromAt (Base := Base) (Const := Const) (ℓ + 1)
            (⟨σ, φ⟩ : Body Const) →
          BodyAvoidsParamStagesFromAt (Base := Base) (Const := Const) ℓ (s + 1)
            (⟨σ, φ⟩ : Body Const) →
          Provable (Const := WithParams Const) R (.ex φ) →
            ∃ t : ClosedTerm (WithParams Const) σ,
              instantiate (Base := Base) t φ ∈ R) := by
  let supply := stageWitnessSupply ℓ s
  have hTsupply : ∀ ξ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) ξ := by
    exact AvoidsParamStagesFrom.fresh_for_stageSupply
      (Base := Base) (Const := Const) (ℓ := ℓ) (s := s) hStage
  have hLeftFresh : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) (pairEnum n).1 := by
    intro σ k
    exact (hPairStage n σ s k (le_refl s)).1
  have hRightFresh : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) (pairEnum n).2 := by
    intro σ k
    exact (hPairStage n σ s k (le_refl s)).2
  obtain ⟨δ, hδchoice, hδNot, _hδSupply⟩ :=
    exists_raw_or_branch_supply_omitting
      (Base := Base) (Const := Const) supply
      (T₀ := T) hNot hOr hTsupply hLeftFresh hRightFresh
  let Tδ : ClosedTheorySet (WithParams Const) := insert δ T
  have hδLayer : FormulaAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (ℓ + 1) δ := by
    rcases hδchoice with rfl | rfl
    · intro σ m k hℓm
      exact (hPairLayer n σ m k hℓm).1
    · intro σ m k hℓm
      exact (hPairLayer n σ m k hℓm).2
  have hδStage : FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ s δ := by
    rcases hδchoice with rfl | rfl
    · intro σ r k hsr
      exact (hPairStage n σ r k hsr).1
    · intro σ r k hsr
      exact (hPairStage n σ r k hsr).2
  have hTδLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) Tδ :=
    AvoidsParamLayersFrom.insert
      (Base := Base) (Const := Const) hLayer hδLayer
  have hTδStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ s Tδ :=
    AvoidsParamStagesFrom.insert
      (Base := Base) (Const := Const) hStage hδStage
  obtain ⟨R, hExtTδ, hOmit, hAvoidLayer, hAvoidStage, hWitness⟩ :=
    exists_raw_witnessInstance_stage_step_of_stageFair
      (Base := Base) (Const := Const) (ℓ := ℓ) (s := s) (T := Tδ)
      bodyEnum hfair hTδLayer hTδStage hBodyLayer hBodyStage hθStage hδNot
  refine ⟨R, δ, hδchoice, ?_, ?_, hOmit, hAvoidLayer, hAvoidStage, hWitness⟩
  · intro ψ hψ
    exact hExtTδ (Set.mem_insert_of_mem δ hψ)
  · exact hExtTδ (Set.mem_insert δ T)

/-- Single-pair form of the stage-local branch-and-witness step. -/
theorem exists_raw_branch_witnessInstance_stage_step_at_of_stageFair
    {ℓ s : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyStageFairAfter (Base := Base) (Const := Const) ℓ (s + 1) bodyEnum)
    (pair : ClosedFormulaPair Const)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ s T)
    (hBodyLayer : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hBodyStage : BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1) bodyEnum)
    (hPairLayer : FormulaPairAvoidsParamLayersFromAt
      (Base := Base) (Const := Const) (ℓ + 1) pair)
    (hPairStage : FormulaPairAvoidsParamStagesFromAt
      (Base := Base) (Const := Const) ℓ s pair)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ s θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ)
    (hOr : Provable (Const := WithParams Const) T (.or pair.1 pair.2)) :
    ∃ R : ClosedTheorySet (WithParams Const),
      ∃ δ : ClosedFormula (WithParams Const),
        (δ = pair.1 ∨ δ = pair.2) ∧
        (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ R) ∧
        δ ∈ R ∧
        ¬ Provable (Const := WithParams Const) R θ ∧
        AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) R ∧
        AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1) R ∧
        (∀ {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
          BodyAvoidsParamLayersFromAt (Base := Base) (Const := Const) (ℓ + 1)
            (⟨σ, φ⟩ : Body Const) →
          BodyAvoidsParamStagesFromAt (Base := Base) (Const := Const) ℓ (s + 1)
            (⟨σ, φ⟩ : Body Const) →
          Provable (Const := WithParams Const) R (.ex φ) →
            ∃ t : ClosedTerm (WithParams Const) σ,
              instantiate (Base := Base) t φ ∈ R) := by
  let supply := stageWitnessSupply ℓ s
  have hTsupply : ∀ ξ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) ξ := by
    exact AvoidsParamStagesFrom.fresh_for_stageSupply
      (Base := Base) (Const := Const) (ℓ := ℓ) (s := s) hStage
  have hLeftFresh : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) pair.1 := by
    intro σ k
    exact (hPairStage σ s k (le_refl s)).1
  have hRightFresh : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) pair.2 := by
    intro σ k
    exact (hPairStage σ s k (le_refl s)).2
  obtain ⟨δ, hδchoice, hδNot, _hδSupply⟩ :=
    exists_raw_or_branch_supply_omitting
      (Base := Base) (Const := Const) supply
      (T₀ := T) hNot hOr hTsupply hLeftFresh hRightFresh
  let Tδ : ClosedTheorySet (WithParams Const) := insert δ T
  have hδLayer : FormulaAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (ℓ + 1) δ := by
    rcases hδchoice with rfl | rfl
    · intro σ m k hℓm
      exact (hPairLayer σ m k hℓm).1
    · intro σ m k hℓm
      exact (hPairLayer σ m k hℓm).2
  have hδStage : FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ s δ := by
    rcases hδchoice with rfl | rfl
    · intro σ r k hsr
      exact (hPairStage σ r k hsr).1
    · intro σ r k hsr
      exact (hPairStage σ r k hsr).2
  have hTδLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) Tδ :=
    AvoidsParamLayersFrom.insert
      (Base := Base) (Const := Const) hLayer hδLayer
  have hTδStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ s Tδ :=
    AvoidsParamStagesFrom.insert
      (Base := Base) (Const := Const) hStage hδStage
  obtain ⟨R, hExtTδ, hOmit, hAvoidLayer, hAvoidStage, hWitness⟩ :=
    exists_raw_witnessInstance_stage_step_of_stageFair
      (Base := Base) (Const := Const) (ℓ := ℓ) (s := s) (T := Tδ)
      bodyEnum hfair hTδLayer hTδStage hBodyLayer hBodyStage hθStage hδNot
  refine ⟨R, δ, hδchoice, ?_, ?_, hOmit, hAvoidLayer, hAvoidStage, hWitness⟩
  · intro ψ hψ
    exact hExtTδ (Set.mem_insert_of_mem δ hψ)
  · exact hExtTδ (Set.mem_insert δ T)

/-- One total stage-indexed raw alternating step.  It repairs witnesses and,
when the current enumerated disjunction is derivable, chooses one disjunct,
while preserving the fixed outer support bound `ℓ + 1` and advancing only the
future-stage bound. -/
theorem exists_raw_alternating_stage_step
    {ℓ s : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const) (n : Nat)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ s T)
    (hBodyLayer : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hBodyStage : BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1) bodyEnum)
    (hPairLayer : FormulaPairAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (ℓ + 1) pairEnum)
    (hPairStage : FormulaPairAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ s pairEnum)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ s θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ∃ R : ClosedTheorySet (WithParams Const),
      (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ R) ∧
      ¬ Provable (Const := WithParams Const) R θ ∧
      AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) R ∧
      AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1) R ∧
      (∀ {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
        Provable (Const := WithParams Const) R (.ex φ) →
          ∃ t : ClosedTerm (WithParams Const) σ,
            instantiate (Base := Base) t φ ∈ R) ∧
      (Provable (Const := WithParams Const) T (.or (pairEnum n).1 (pairEnum n).2) →
        ∃ δ : ClosedFormula (WithParams Const),
          (δ = (pairEnum n).1 ∨ δ = (pairEnum n).2) ∧ δ ∈ R) := by
  classical
  by_cases hOr : Provable (Const := WithParams Const) T (.or (pairEnum n).1 (pairEnum n).2)
  · obtain ⟨R, δ, hδchoice, hExt, hδR, hOmit, hAvoidLayer, hAvoidStage, hWitness⟩ :=
      exists_raw_branch_witnessInstance_stage_step
        (Base := Base) (Const := Const) (ℓ := ℓ) (s := s) (T := T)
        bodyEnum hfair pairEnum n hLayer hStage hBodyLayer hBodyStage
        hPairLayer hPairStage hθStage hNot hOr
    refine ⟨R, hExt, hOmit, hAvoidLayer, hAvoidStage, hWitness, ?_⟩
    intro _h
    exact ⟨δ, hδchoice, hδR⟩
  · obtain ⟨R, hExt, hOmit, hAvoidLayer, hAvoidStage, hWitness⟩ :=
      exists_raw_witnessInstance_stage_step
        (Base := Base) (Const := Const) (ℓ := ℓ) (s := s) (T := T)
        bodyEnum hfair hLayer hStage hBodyLayer hBodyStage hθStage hNot
    refine ⟨R, hExt, hOmit, hAvoidLayer, hAvoidStage, hWitness, ?_⟩
    intro hOr'
    exact False.elim (hOr hOr')

/-- Total stage-indexed raw alternating step with stage-local body fairness. -/
theorem exists_raw_alternating_stage_step_of_stageFair
    {ℓ s : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyStageFairAfter (Base := Base) (Const := Const) ℓ (s + 1) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const) (n : Nat)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ s T)
    (hBodyLayer : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hBodyStage : BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1) bodyEnum)
    (hPairLayer : FormulaPairAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (ℓ + 1) pairEnum)
    (hPairStage : FormulaPairAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ s pairEnum)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ s θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ∃ R : ClosedTheorySet (WithParams Const),
      (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ R) ∧
      ¬ Provable (Const := WithParams Const) R θ ∧
      AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) R ∧
      AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1) R ∧
      (∀ {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
        BodyAvoidsParamLayersFromAt (Base := Base) (Const := Const) (ℓ + 1)
          (⟨σ, φ⟩ : Body Const) →
        BodyAvoidsParamStagesFromAt (Base := Base) (Const := Const) ℓ (s + 1)
          (⟨σ, φ⟩ : Body Const) →
        Provable (Const := WithParams Const) R (.ex φ) →
          ∃ t : ClosedTerm (WithParams Const) σ,
            instantiate (Base := Base) t φ ∈ R) ∧
      (Provable (Const := WithParams Const) T (.or (pairEnum n).1 (pairEnum n).2) →
        ∃ δ : ClosedFormula (WithParams Const),
          (δ = (pairEnum n).1 ∨ δ = (pairEnum n).2) ∧ δ ∈ R) := by
  classical
  by_cases hOr : Provable (Const := WithParams Const) T (.or (pairEnum n).1 (pairEnum n).2)
  · obtain ⟨R, δ, hδchoice, hExt, hδR, hOmit, hAvoidLayer, hAvoidStage, hWitness⟩ :=
      exists_raw_branch_witnessInstance_stage_step_of_stageFair
        (Base := Base) (Const := Const) (ℓ := ℓ) (s := s) (T := T)
        bodyEnum hfair pairEnum n hLayer hStage hBodyLayer hBodyStage
        hPairLayer hPairStage hθStage hNot hOr
    refine ⟨R, hExt, hOmit, hAvoidLayer, hAvoidStage, hWitness, ?_⟩
    intro _h
    exact ⟨δ, hδchoice, hδR⟩
  · obtain ⟨R, hExt, hOmit, hAvoidLayer, hAvoidStage, hWitness⟩ :=
      exists_raw_witnessInstance_stage_step_of_stageFair
        (Base := Base) (Const := Const) (ℓ := ℓ) (s := s) (T := T)
        bodyEnum hfair hLayer hStage hBodyLayer hBodyStage hθStage hNot
    refine ⟨R, hExt, hOmit, hAvoidLayer, hAvoidStage, hWitness, ?_⟩
    intro hOr'
    exact False.elim (hOr hOr')

/-- Single-pair total stage-indexed raw alternating step with stage-local body
fairness. -/
theorem exists_raw_alternating_stage_step_at_of_stageFair
    {ℓ s : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyStageFairAfter (Base := Base) (Const := Const) ℓ (s + 1) bodyEnum)
    (pair : ClosedFormulaPair Const)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ s T)
    (hBodyLayer : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hBodyStage : BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1) bodyEnum)
    (hPairLayer : FormulaPairAvoidsParamLayersFromAt
      (Base := Base) (Const := Const) (ℓ + 1) pair)
    (hPairStage : FormulaPairAvoidsParamStagesFromAt
      (Base := Base) (Const := Const) ℓ s pair)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ s θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ∃ R : ClosedTheorySet (WithParams Const),
      (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ R) ∧
      ¬ Provable (Const := WithParams Const) R θ ∧
      AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) R ∧
      AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1) R ∧
      (∀ {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
        BodyAvoidsParamLayersFromAt (Base := Base) (Const := Const) (ℓ + 1)
          (⟨σ, φ⟩ : Body Const) →
        BodyAvoidsParamStagesFromAt (Base := Base) (Const := Const) ℓ (s + 1)
          (⟨σ, φ⟩ : Body Const) →
        Provable (Const := WithParams Const) R (.ex φ) →
          ∃ t : ClosedTerm (WithParams Const) σ,
            instantiate (Base := Base) t φ ∈ R) ∧
      (Provable (Const := WithParams Const) T (.or pair.1 pair.2) →
        ∃ δ : ClosedFormula (WithParams Const),
          (δ = pair.1 ∨ δ = pair.2) ∧ δ ∈ R) := by
  classical
  by_cases hOr : Provable (Const := WithParams Const) T (.or pair.1 pair.2)
  · obtain ⟨R, δ, hδchoice, hExt, hδR, hOmit, hAvoidLayer, hAvoidStage, hWitness⟩ :=
      exists_raw_branch_witnessInstance_stage_step_at_of_stageFair
        (Base := Base) (Const := Const) (ℓ := ℓ) (s := s) (T := T)
        bodyEnum hfair pair hLayer hStage hBodyLayer hBodyStage
        hPairLayer hPairStage hθStage hNot hOr
    refine ⟨R, hExt, hOmit, hAvoidLayer, hAvoidStage, hWitness, ?_⟩
    intro _h
    exact ⟨δ, hδchoice, hδR⟩
  · obtain ⟨R, hExt, hOmit, hAvoidLayer, hAvoidStage, hWitness⟩ :=
      exists_raw_witnessInstance_stage_step_of_stageFair
        (Base := Base) (Const := Const) (ℓ := ℓ) (s := s) (T := T)
        bodyEnum hfair hLayer hStage hBodyLayer hBodyStage hθStage hNot
    refine ⟨R, hExt, hOmit, hAvoidLayer, hAvoidStage, hWitness, ?_⟩
    intro hOr'
    exact False.elim (hOr hOr')

/-- A support-respecting scheduler for the fixed-outer-layer raw construction.
At stage `s`, it supplies a local body enumeration that is fair for bodies
already supported below `s+1`, plus one disjunction pair to decide. -/
structure RawAlternatingStageScheduler (ℓ : Nat) where
  body : Nat → Nat → Body Const
  pair : Nat → ClosedFormulaPair Const
  body_fair :
    ∀ s, BodyStageFairAfter (Base := Base) (Const := Const) ℓ (s + 1) (body s)
  body_layer :
    ∀ s, BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) (body s)
  body_stage :
    ∀ s, BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1) (body s)
  pair_layer :
    ∀ s, FormulaPairAvoidsParamLayersFromAt (Base := Base) (Const := Const) (ℓ + 1) (pair s)
  pair_stage :
    ∀ s, FormulaPairAvoidsParamStagesFromAt (Base := Base) (Const := Const) ℓ s (pair s)
  pair_fair :
    ∀ p : ClosedFormulaPair Const,
      FormulaPairAvoidsParamLayersFromAt (Base := Base) (Const := Const) (ℓ + 1) p →
        ∀ N : Nat, ∃ n, N ≤ n ∧ pair n = p

/-- Global pair fairness is incompatible with uniformly avoiding a future
parameter layer.  Real successor constructions must use support-respecting
fairness instead. -/
theorem FormulaPairFairAfter.incompatible_with_avoids_layers
    {ℓ : Nat} {enum : Nat → ClosedFormulaPair Const}
    (hFair : FormulaPairFairAfter (Base := Base) (Const := Const) enum)
    (hAvoid : FormulaPairAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ enum) :
    False := by
  let c : WithParams Const propTy := param propTy (Nat.pair (ℓ + 1) 0)
  let p : ClosedFormulaPair Const :=
    ((.const c : ClosedFormula (WithParams Const)),
      (.top : ClosedFormula (WithParams Const)))
  obtain ⟨n, _hn, hp⟩ := hFair p 0
  have hNo : NoConstOccurrence c (enum n).1 :=
    (hAvoid n propTy (ℓ + 1) 0 (Nat.le_succ ℓ)).1
  have hNoSelf : NoConstOccurrence c (.const c : ClosedFormula (WithParams Const)) := by
    simpa [p, hp] using hNo
  exact noConstOccurrence_self_const_false c hNoSelf

/-- A proof-carrying finite approximation driven by a support-respecting
scheduler. -/
structure RawAlternatingScheduledStageApprox
    (ℓ : Nat) (T : ClosedTheorySet (WithParams Const))
    (θ : ClosedFormula (WithParams Const)) (N : Nat) where
  theory : ClosedTheorySet (WithParams Const)
  base_subset : ∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ theory
  omits : ¬ Provable (Const := WithParams Const) theory θ
  avoids_layer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) theory
  avoids_stage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ N theory

/-- The chosen scheduler-indexed raw approximation chain. -/
noncomputable def rawAlternatingScheduledStageApprox
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (S : RawAlternatingStageScheduler (Base := Base) (Const := Const) ℓ)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    (N : Nat) →
      RawAlternatingScheduledStageApprox (Base := Base) (Const := Const) ℓ T θ N
  | 0 =>
      { theory := T
        base_subset := by intro ψ hψ; exact hψ
        omits := hNot
        avoids_layer := hLayer
        avoids_stage := by simpa using hStage }
  | N + 1 =>
      let prev :=
        rawAlternatingScheduledStageApprox S hLayer hStage hθStage hNot N
      have hθStageN : FormulaAvoidsParamStagesFrom
          (Base := Base) (Const := Const) ℓ N θ := by
        exact FormulaAvoidsParamStagesFrom.mono
          (Base := Base) (Const := Const) (by omega) hθStage
      let stepExists :=
        exists_raw_alternating_stage_step_at_of_stageFair
          (Base := Base) (Const := Const) (ℓ := ℓ) (s := N) (T := prev.theory)
          (S.body N) (S.body_fair N) (S.pair N)
          prev.avoids_layer prev.avoids_stage
          (S.body_layer N) (S.body_stage N) (S.pair_layer N) (S.pair_stage N)
          hθStageN prev.omits
      let R := Classical.choose stepExists
      have hR := Classical.choose_spec stepExists
      { theory := R
        base_subset := by
          intro ψ hψ
          exact hR.1 (prev.base_subset hψ)
        omits := hR.2.1
        avoids_layer := hR.2.2.1
        avoids_stage := hR.2.2.2.1 }

/-- Adjacent monotonicity of the scheduler-indexed raw approximation chain. -/
theorem rawAlternatingScheduledStageApprox_subset_succ
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (S : RawAlternatingStageScheduler (Base := Base) (Const := Const) ℓ)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ)
    (N : Nat) :
    ∀ {ψ : ClosedFormula (WithParams Const)},
      ψ ∈ (rawAlternatingScheduledStageApprox
        (Base := Base) (Const := Const) S hLayer hStage hθStage hNot N).theory →
      ψ ∈ (rawAlternatingScheduledStageApprox
        (Base := Base) (Const := Const) S hLayer hStage hθStage hNot (N + 1)).theory := by
  intro ψ hψ
  let prev :=
    rawAlternatingScheduledStageApprox
      (Base := Base) (Const := Const) S hLayer hStage hθStage hNot N
  change ψ ∈ prev.theory at hψ
  have hθStageN : FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ N θ := by
    exact FormulaAvoidsParamStagesFrom.mono
      (Base := Base) (Const := Const) (by omega) hθStage
  let stepExists :=
    exists_raw_alternating_stage_step_at_of_stageFair
      (Base := Base) (Const := Const) (ℓ := ℓ) (s := N) (T := prev.theory)
      (S.body N) (S.body_fair N) (S.pair N)
      prev.avoids_layer prev.avoids_stage
      (S.body_layer N) (S.body_stage N) (S.pair_layer N) (S.pair_stage N)
      hθStageN prev.omits
  have hR := Classical.choose_spec stepExists
  change ψ ∈ Classical.choose stepExists
  exact hR.1 hψ

/-- If the scheduled disjunction is provable at stage `N`, the next scheduled
approximation contains one of its disjuncts. -/
theorem rawAlternatingScheduledStageApprox_or_branch_succ
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (S : RawAlternatingStageScheduler (Base := Base) (Const := Const) ℓ)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ)
    (N : Nat)
    (hOr : Provable (Const := WithParams Const)
      (rawAlternatingScheduledStageApprox
        (Base := Base) (Const := Const) S hLayer hStage hθStage hNot N).theory
      (.or (S.pair N).1 (S.pair N).2)) :
    ∃ δ : ClosedFormula (WithParams Const),
      (δ = (S.pair N).1 ∨ δ = (S.pair N).2) ∧
        δ ∈ (rawAlternatingScheduledStageApprox
          (Base := Base) (Const := Const) S hLayer hStage hθStage hNot (N + 1)).theory := by
  let prev :=
    rawAlternatingScheduledStageApprox
      (Base := Base) (Const := Const) S hLayer hStage hθStage hNot N
  change Provable (Const := WithParams Const) prev.theory
      (.or (S.pair N).1 (S.pair N).2) at hOr
  have hθStageN : FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ N θ := by
    exact FormulaAvoidsParamStagesFrom.mono
      (Base := Base) (Const := Const) (by omega) hθStage
  let stepExists :=
    exists_raw_alternating_stage_step_at_of_stageFair
      (Base := Base) (Const := Const) (ℓ := ℓ) (s := N) (T := prev.theory)
      (S.body N) (S.body_fair N) (S.pair N)
      prev.avoids_layer prev.avoids_stage
      (S.body_layer N) (S.body_stage N) (S.pair_layer N) (S.pair_stage N)
      hθStageN prev.omits
  have hR := Classical.choose_spec stepExists
  obtain ⟨δ, hδchoice, hδmem⟩ := hR.2.2.2.2.2 hOr
  refine ⟨δ, hδchoice, ?_⟩
  change δ ∈ Classical.choose stepExists
  exact hδmem

/-- The next scheduled approximation witnesses any currently provable
existential whose body is supported below the next stage. -/
theorem rawAlternatingScheduledStageApprox_exists_witness_succ
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (S : RawAlternatingStageScheduler (Base := Base) (Const := Const) ℓ)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ)
    (N : Nat) {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hBodyLayer : BodyAvoidsParamLayersFromAt (Base := Base) (Const := Const) (ℓ + 1)
      (⟨σ, φ⟩ : Body Const))
    (hBodyStage : BodyAvoidsParamStagesFromAt (Base := Base) (Const := Const) ℓ (N + 1)
      (⟨σ, φ⟩ : Body Const))
    (hEx : Provable (Const := WithParams Const)
      (rawAlternatingScheduledStageApprox
        (Base := Base) (Const := Const) S hLayer hStage hθStage hNot N).theory
      (.ex φ)) :
    ∃ t : ClosedTerm (WithParams Const) σ,
      instantiate (Base := Base) t φ ∈
        (rawAlternatingScheduledStageApprox
          (Base := Base) (Const := Const) S hLayer hStage hθStage hNot (N + 1)).theory := by
  let prev :=
    rawAlternatingScheduledStageApprox
      (Base := Base) (Const := Const) S hLayer hStage hθStage hNot N
  change Provable (Const := WithParams Const) prev.theory (.ex φ) at hEx
  have hθStageN : FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ N θ := by
    exact FormulaAvoidsParamStagesFrom.mono
      (Base := Base) (Const := Const) (by omega) hθStage
  let stepExists :=
    exists_raw_alternating_stage_step_at_of_stageFair
      (Base := Base) (Const := Const) (ℓ := ℓ) (s := N) (T := prev.theory)
      (S.body N) (S.body_fair N) (S.pair N)
      prev.avoids_layer prev.avoids_stage
      (S.body_layer N) (S.body_stage N) (S.pair_layer N) (S.pair_stage N)
      hθStageN prev.omits
  have hR := Classical.choose_spec stepExists
  have hExR : Provable (Const := WithParams Const) (Classical.choose stepExists) (.ex φ) :=
    provable_mono (Const := WithParams Const) hR.1 hEx
  exact hR.2.2.2.2.1 hBodyLayer hBodyStage hExR

/-- Monotonicity of the scheduler-indexed approximation chain. -/
theorem rawAlternatingScheduledStageApprox_mono
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (S : RawAlternatingStageScheduler (Base := Base) (Const := Const) ℓ)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ)
    {m n : Nat} (hmn : m ≤ n) :
    ∀ {ψ : ClosedFormula (WithParams Const)},
      ψ ∈ (rawAlternatingScheduledStageApprox
        (Base := Base) (Const := Const) S hLayer hStage hθStage hNot m).theory →
      ψ ∈ (rawAlternatingScheduledStageApprox
        (Base := Base) (Const := Const) S hLayer hStage hθStage hNot n).theory := by
  induction n, hmn using Nat.le_induction with
  | base =>
      intro ψ hψ
      exact hψ
  | succ n _ ih =>
      intro ψ hψ
      exact rawAlternatingScheduledStageApprox_subset_succ
        (Base := Base) (Const := Const) S hLayer hStage hθStage hNot n (ih hψ)

/-- The raw limit of the scheduler-indexed approximation chain. -/
noncomputable def rawAlternatingScheduledStageLimit
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (S : RawAlternatingStageScheduler (Base := Base) (Const := Const) ℓ)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ClosedTheorySet (WithParams Const) :=
  {ψ | ∃ N, ψ ∈ (rawAlternatingScheduledStageApprox
    (Base := Base) (Const := Const) S hLayer hStage hθStage hNot N).theory}

/-- The initial raw base is included in the scheduler-indexed raw limit. -/
theorem subset_rawAlternatingScheduledStageLimit
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (S : RawAlternatingStageScheduler (Base := Base) (Const := Const) ℓ)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T →
      ψ ∈ rawAlternatingScheduledStageLimit
        (Base := Base) (Const := Const) S hLayer hStage hθStage hNot := by
  intro ψ hψ
  refine ⟨0, ?_⟩
  exact (rawAlternatingScheduledStageApprox
    (Base := Base) (Const := Const) S hLayer hStage hθStage hNot 0).base_subset hψ

/-- Every finite scheduler-indexed approximation is included in the raw limit. -/
theorem rawAlternatingScheduledStageApprox_subset_limit
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (S : RawAlternatingStageScheduler (Base := Base) (Const := Const) ℓ)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ)
    (N : Nat) :
    ∀ {ψ : ClosedFormula (WithParams Const)},
      ψ ∈ (rawAlternatingScheduledStageApprox
        (Base := Base) (Const := Const) S hLayer hStage hθStage hNot N).theory →
      ψ ∈ rawAlternatingScheduledStageLimit
        (Base := Base) (Const := Const) S hLayer hStage hθStage hNot := by
  intro ψ hψ
  exact ⟨N, hψ⟩

/-- The scheduler-indexed raw limit preserves the fixed outer support bound. -/
theorem rawAlternatingScheduledStageLimit_avoids_future_layers
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (S : RawAlternatingStageScheduler (Base := Base) (Const := Const) ℓ)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1)
      (rawAlternatingScheduledStageLimit
        (Base := Base) (Const := Const) S hLayer hStage hθStage hNot) := by
  intro ψ hψ σ m k hm
  rcases hψ with ⟨N, hψN⟩
  exact (rawAlternatingScheduledStageApprox
    (Base := Base) (Const := Const) S hLayer hStage hθStage hNot N).avoids_layer
    ψ hψN σ m k hm

/-- A finite list of formulas from the scheduler-indexed raw limit already
occurs in one finite approximation. -/
theorem exists_stage_rawAlternatingScheduledStageLimit
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (S : RawAlternatingStageScheduler (Base := Base) (Const := Const) ℓ)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ∀ (Γ : List (ClosedFormula (WithParams Const))),
      (∀ ψ ∈ Γ, ψ ∈ rawAlternatingScheduledStageLimit
        (Base := Base) (Const := Const) S hLayer hStage hθStage hNot) →
      ∃ N, ∀ ψ ∈ Γ, ψ ∈ (rawAlternatingScheduledStageApprox
        (Base := Base) (Const := Const) S hLayer hStage hθStage hNot N).theory
  | [], _ => ⟨0, by intro ψ hψ; cases hψ⟩
  | a :: Γ, hΓ => by
      obtain ⟨N, hN⟩ :=
        exists_stage_rawAlternatingScheduledStageLimit S hLayer hStage hθStage hNot Γ
          (fun ψ hψ => hΓ ψ (List.mem_cons_of_mem _ hψ))
      obtain ⟨na, hna⟩ := hΓ a List.mem_cons_self
      refine ⟨max N na, fun ψ hψ => ?_⟩
      rcases List.mem_cons.mp hψ with rfl | hψ'
      · exact rawAlternatingScheduledStageApprox_mono
          (Base := Base) (Const := Const) S hLayer hStage hθStage hNot
          (le_max_right N na) hna
      · exact rawAlternatingScheduledStageApprox_mono
          (Base := Base) (Const := Const) S hLayer hStage hθStage hNot
          (le_max_left N na) (hN ψ hψ')

/-- The scheduler-indexed raw limit still omits the target formula. -/
theorem rawAlternatingScheduledStageLimit_omits
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (S : RawAlternatingStageScheduler (Base := Base) (Const := Const) ℓ)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ¬ Provable (Const := WithParams Const)
      (rawAlternatingScheduledStageLimit
        (Base := Base) (Const := Const) S hLayer hStage hθStage hNot) θ := by
  intro hProv
  rcases hProv with ⟨Γ, hΓ, d⟩
  obtain ⟨N, hN⟩ :=
    exists_stage_rawAlternatingScheduledStageLimit
      (Base := Base) (Const := Const) S hLayer hStage hθStage hNot Γ hΓ
  exact (rawAlternatingScheduledStageApprox
    (Base := Base) (Const := Const) S hLayer hStage hθStage hNot N).omits
    ⟨Γ, hN, d⟩

/-- The scheduler-indexed raw limit is consistent whenever it omits the target. -/
theorem rawAlternatingScheduledStageLimit_consistent
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (S : RawAlternatingStageScheduler (Base := Base) (Const := Const) ℓ)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    Consistent (Const := WithParams Const)
      (rawAlternatingScheduledStageLimit
        (Base := Base) (Const := Const) S hLayer hStage hθStage hNot) := by
  intro hbot
  exact rawAlternatingScheduledStageLimit_omits
    (Base := Base) (Const := Const) S hLayer hStage hθStage hNot
    (by
      rcases hbot with ⟨Γ, hΓ, d⟩
      exact ⟨Γ, hΓ, ExtDerivation.botE d⟩)

/-- Supported disjunction primeness for the scheduler-indexed raw limit.  The
pair must be supported below the next outer layer; future-stage support is
obtained by scheduling it sufficiently late. -/
theorem rawAlternatingScheduledStageLimit_prime_or_supported
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (S : RawAlternatingStageScheduler (Base := Base) (Const := Const) ℓ)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ∀ {φ ψ : ClosedFormula (WithParams Const)},
      FormulaPairAvoidsParamLayersFromAt (Base := Base) (Const := Const) (ℓ + 1) (φ, ψ) →
      (.or φ ψ : ClosedFormula (WithParams Const)) ∈
        ClosedTheorySet.provableClosure (Const := WithParams Const)
          (rawAlternatingScheduledStageLimit
            (Base := Base) (Const := Const) S hLayer hStage hθStage hNot) →
        φ ∈ ClosedTheorySet.provableClosure (Const := WithParams Const)
          (rawAlternatingScheduledStageLimit
            (Base := Base) (Const := Const) S hLayer hStage hθStage hNot) ∨
          ψ ∈ ClosedTheorySet.provableClosure (Const := WithParams Const)
            (rawAlternatingScheduledStageLimit
              (Base := Base) (Const := Const) S hLayer hStage hθStage hNot) := by
  intro φ ψ hPairLayer hOr
  rcases hOr with ⟨Γ, hΓ, d⟩
  obtain ⟨N, hN⟩ :=
    exists_stage_rawAlternatingScheduledStageLimit
      (Base := Base) (Const := Const) S hLayer hStage hθStage hNot Γ hΓ
  obtain ⟨n, hNn, hpair⟩ := S.pair_fair (φ, ψ) hPairLayer N
  have hOrN : Provable (Const := WithParams Const)
      (rawAlternatingScheduledStageApprox
        (Base := Base) (Const := Const) S hLayer hStage hθStage hNot N).theory
      (.or φ ψ) := ⟨Γ, hN, d⟩
  have hOrn : Provable (Const := WithParams Const)
      (rawAlternatingScheduledStageApprox
        (Base := Base) (Const := Const) S hLayer hStage hθStage hNot n).theory
      (.or (S.pair n).1 (S.pair n).2) := by
    have hMono : ∀ {ξ : ClosedFormula (WithParams Const)},
        ξ ∈ (rawAlternatingScheduledStageApprox
          (Base := Base) (Const := Const) S hLayer hStage hθStage hNot N).theory →
        ξ ∈ (rawAlternatingScheduledStageApprox
          (Base := Base) (Const := Const) S hLayer hStage hθStage hNot n).theory :=
      rawAlternatingScheduledStageApprox_mono
        (Base := Base) (Const := Const) S hLayer hStage hθStage hNot hNn
    have hLift : Provable (Const := WithParams Const)
        (rawAlternatingScheduledStageApprox
          (Base := Base) (Const := Const) S hLayer hStage hθStage hNot n).theory
        (.or φ ψ) :=
      provable_mono (Const := WithParams Const) hMono hOrN
    simpa [hpair] using hLift
  obtain ⟨δ, hδchoice, hδmem⟩ :=
    rawAlternatingScheduledStageApprox_or_branch_succ
      (Base := Base) (Const := Const) S hLayer hStage hθStage hNot n hOrn
  have hδlimit : δ ∈ rawAlternatingScheduledStageLimit
      (Base := Base) (Const := Const) S hLayer hStage hθStage hNot := by
    exact rawAlternatingScheduledStageApprox_subset_limit
      (Base := Base) (Const := Const) S hLayer hStage hθStage hNot (n + 1) hδmem
  rcases hδchoice with hδ | hδ
  · left
    rw [hpair] at hδ
    cases hδ
    exact ClosedTheorySet.subset_provableClosure
      (Const := WithParams Const)
      (rawAlternatingScheduledStageLimit
        (Base := Base) (Const := Const) S hLayer hStage hθStage hNot)
      hδlimit
  · right
    rw [hpair] at hδ
    cases hδ
    exact ClosedTheorySet.subset_provableClosure
      (Const := WithParams Const)
        (rawAlternatingScheduledStageLimit
          (Base := Base) (Const := Const) S hLayer hStage hθStage hNot)
      hδlimit

/-- Supported existential witness property for the scheduler-indexed raw limit.
The body must be supported below the next outer layer; stage support is obtained
by moving to a sufficiently late approximation. -/
theorem rawAlternatingScheduledStageLimit_exists_witness_supported
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (S : RawAlternatingStageScheduler (Base := Base) (Const := Const) ℓ)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ∀ {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
      BodyAvoidsParamLayersFromAt (Base := Base) (Const := Const) (ℓ + 1)
        (⟨σ, φ⟩ : Body Const) →
      (.ex φ : ClosedFormula (WithParams Const)) ∈
        ClosedTheorySet.provableClosure (Const := WithParams Const)
          (rawAlternatingScheduledStageLimit
            (Base := Base) (Const := Const) S hLayer hStage hθStage hNot) →
        ∃ t : ClosedTerm (WithParams Const) σ,
          instantiate (Base := Base) t φ ∈
            ClosedTheorySet.provableClosure (Const := WithParams Const)
              (rawAlternatingScheduledStageLimit
                (Base := Base) (Const := Const) S hLayer hStage hθStage hNot) := by
  intro σ φ hBodyLayer hEx
  rcases hEx with ⟨Γ, hΓ, d⟩
  obtain ⟨N, hN⟩ :=
    exists_stage_rawAlternatingScheduledStageLimit
      (Base := Base) (Const := Const) S hLayer hStage hθStage hNot Γ hΓ
  let M := max N (maxParam φ)
  have hNM : N ≤ M := le_max_left N (maxParam φ)
  have hBodyStage : BodyAvoidsParamStagesFromAt (Base := Base) (Const := Const) ℓ (M + 1)
      (⟨σ, φ⟩ : Body Const) := by
    exact BodyAvoidsParamStagesFromAt.mono
      (Base := Base) (Const := Const)
      (by
        dsimp [M]
        omega)
      (BodyAvoidsParamStagesFromAt.of_maxParam
        (Base := Base) (Const := Const) ℓ (⟨σ, φ⟩ : Body Const))
  have hExN : Provable (Const := WithParams Const)
      (rawAlternatingScheduledStageApprox
        (Base := Base) (Const := Const) S hLayer hStage hθStage hNot N).theory
      (.ex φ) := ⟨Γ, hN, d⟩
  have hExM : Provable (Const := WithParams Const)
      (rawAlternatingScheduledStageApprox
        (Base := Base) (Const := Const) S hLayer hStage hθStage hNot M).theory
      (.ex φ) := by
    have hMono : ∀ {ξ : ClosedFormula (WithParams Const)},
        ξ ∈ (rawAlternatingScheduledStageApprox
          (Base := Base) (Const := Const) S hLayer hStage hθStage hNot N).theory →
        ξ ∈ (rawAlternatingScheduledStageApprox
          (Base := Base) (Const := Const) S hLayer hStage hθStage hNot M).theory :=
      rawAlternatingScheduledStageApprox_mono
        (Base := Base) (Const := Const) S hLayer hStage hθStage hNot hNM
    exact provable_mono (Const := WithParams Const) hMono hExN
  obtain ⟨t, ht⟩ :=
    rawAlternatingScheduledStageApprox_exists_witness_succ
      (Base := Base) (Const := Const) S hLayer hStage hθStage hNot M
      hBodyLayer hBodyStage hExM
  refine ⟨t, ?_⟩
  exact ClosedTheorySet.subset_provableClosure
    (Const := WithParams Const)
    (rawAlternatingScheduledStageLimit
      (Base := Base) (Const := Const) S hLayer hStage hθStage hNot)
    (rawAlternatingScheduledStageApprox_subset_limit
      (Base := Base) (Const := Const) S hLayer hStage hθStage hNot (M + 1) ht)

/-- The deductive closure of the scheduler-indexed raw limit is a closed,
consistent, supported-prime, supported-witnessed extension that still omits the
target formula.  The support qualifiers are essential: the raw presentation
stays below one outer layer, so unsupported future-layer formulas are not part
of the canonical successor interface. -/
theorem exists_closed_supported_prime_rawAlternatingScheduledStageLimit_separating
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (S : RawAlternatingStageScheduler (Base := Base) (Const := Const) ℓ)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ∃ U : ClosedTheorySet (WithParams Const),
      (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ U) ∧
      DeductivelyClosed (Const := WithParams Const) U ∧
      Consistent (Const := WithParams Const) U ∧
      (∀ {φ ψ : ClosedFormula (WithParams Const)},
        FormulaPairAvoidsParamLayersFromAt (Base := Base) (Const := Const) (ℓ + 1) (φ, ψ) →
        (.or φ ψ : ClosedFormula (WithParams Const)) ∈ U → φ ∈ U ∨ ψ ∈ U) ∧
      (∀ {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
        BodyAvoidsParamLayersFromAt (Base := Base) (Const := Const) (ℓ + 1)
          (⟨σ, φ⟩ : Body Const) →
        (.ex φ : ClosedFormula (WithParams Const)) ∈ U →
          ∃ t : ClosedTerm (WithParams Const) σ,
            instantiate (Base := Base) t φ ∈ U) ∧
      θ ∉ U := by
  let L : ClosedTheorySet (WithParams Const) :=
    rawAlternatingScheduledStageLimit
      (Base := Base) (Const := Const) S hLayer hStage hθStage hNot
  let U : ClosedTheorySet (WithParams Const) :=
    ClosedTheorySet.provableClosure (Const := WithParams Const) L
  refine ⟨U, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ψ hψ
    exact ClosedTheorySet.subset_provableClosure
      (Const := WithParams Const) L
      (subset_rawAlternatingScheduledStageLimit
        (Base := Base) (Const := Const) S hLayer hStage hθStage hNot hψ)
  · exact ClosedTheorySet.provableClosure_deductivelyClosed
      (Const := WithParams Const) L
  · exact ClosedTheorySet.provableClosure_consistent
      (Const := WithParams Const)
      (rawAlternatingScheduledStageLimit_consistent
        (Base := Base) (Const := Const) S hLayer hStage hθStage hNot)
  · intro φ ψ hPair hOr
    exact rawAlternatingScheduledStageLimit_prime_or_supported
      (Base := Base) (Const := Const) S hLayer hStage hθStage hNot hPair hOr
  · intro σ φ hBody hEx
    exact rawAlternatingScheduledStageLimit_exists_witness_supported
      (Base := Base) (Const := Const) S hLayer hStage hθStage hNot hBody hEx
  · exact ClosedTheorySet.not_mem_provableClosure_of_not_provable
      (Const := WithParams Const)
      (rawAlternatingScheduledStageLimit_omits
        (Base := Base) (Const := Const) S hLayer hStage hθStage hNot)

/-- Package the scheduler-indexed raw limit as a supported presented world at
the successor level. -/
theorem exists_supported_presented_rawAlternatingScheduledStageLimit_separating
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (S : RawAlternatingStageScheduler (Base := Base) (Const := Const) ℓ)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ∃ W : SupportedPresentedIntuitionisticWorld (Base := Base) Const,
      W.level = ℓ + 1 ∧
      (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ W.carrier) ∧
      θ ∉ W.carrier := by
  let L : ClosedTheorySet (WithParams Const) :=
    rawAlternatingScheduledStageLimit
      (Base := Base) (Const := Const) S hLayer hStage hθStage hNot
  let W : SupportedPresentedIntuitionisticWorld (Base := Base) Const :=
    { level := ℓ + 1
      raw := L
      raw_avoids_future :=
        rawAlternatingScheduledStageLimit_avoids_future_layers
          (Base := Base) (Const := Const) S hLayer hStage hθStage hNot
      consistent :=
        ClosedTheorySet.provableClosure_consistent
          (Const := WithParams Const)
          (rawAlternatingScheduledStageLimit_consistent
            (Base := Base) (Const := Const) S hLayer hStage hθStage hNot)
      supported_prime_or := by
        intro φ ψ hPair hOr
        exact rawAlternatingScheduledStageLimit_prime_or_supported
          (Base := Base) (Const := Const) S hLayer hStage hθStage hNot hPair hOr
      supported_exists_witness := by
        intro σ φ hBody hEx
        exact rawAlternatingScheduledStageLimit_exists_witness_supported
          (Base := Base) (Const := Const) S hLayer hStage hθStage hNot hBody hEx }
  refine ⟨W, rfl, ?_, ?_⟩
  · intro ψ hψ
    exact ClosedTheorySet.subset_provableClosure
      (Const := WithParams Const) L
      (subset_rawAlternatingScheduledStageLimit
        (Base := Base) (Const := Const) S hLayer hStage hθStage hNot hψ)
  · exact ClosedTheorySet.not_mem_provableClosure_of_not_provable
      (Const := WithParams Const)
      (rawAlternatingScheduledStageLimit_omits
        (Base := Base) (Const := Const) S hLayer hStage hθStage hNot)

/-- Scheduler-based supported successor for an existing presented world. -/
theorem PresentedIntuitionisticWorld.exists_supported_successor_separating
    (W : PresentedIntuitionisticWorld Const)
    (S : RawAlternatingStageScheduler (Base := Base) (Const := Const) W.level)
    {θ : ClosedFormula (WithParams Const)}
    (hθ : FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) W.level θ)
    (hNot : ¬ Provable (Const := WithParams Const) W.raw θ) :
    ∃ W' : SupportedPresentedIntuitionisticWorld (Base := Base) Const,
      W'.level = W.level + 1 ∧
      (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ W.raw → ψ ∈ W'.carrier) ∧
      θ ∉ W'.carrier := by
  have hLayer : AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (W.level + 1) W.raw :=
    AvoidsParamLayersFrom.mono
      (Base := Base) (Const := Const) (Nat.le_succ W.level) W.raw_avoids_future
  have hStage : AvoidsParamStagesFrom
      (Base := Base) (Const := Const) W.level 0 W.raw :=
    AvoidsParamLayersFrom.to_stages
      (Base := Base) (Const := Const) W.raw_avoids_future
  have hθStage : FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) W.level 0 θ :=
    FormulaAvoidsParamLayersFrom.to_stages
      (Base := Base) (Const := Const) hθ
  exact exists_supported_presented_rawAlternatingScheduledStageLimit_separating
    (Base := Base) (Const := Const) (ℓ := W.level) (T := W.raw)
    S hLayer hStage hθStage hNot

/-- If an implication is absent from the closed carrier of a supported presented
world, then adding the antecedent to the raw base cannot derive the consequent. -/
theorem SupportedPresentedIntuitionisticWorld.not_provable_of_not_imp_mem
    (W : SupportedPresentedIntuitionisticWorld Const)
    {φ ψ : ClosedFormula (WithParams Const)}
    (hNotImp : (.imp φ ψ : ClosedFormula (WithParams Const)) ∉ W.carrier) :
    ¬ Provable (Const := WithParams Const) (insert φ W.raw) ψ := by
  intro hInsert
  have hImpRaw : Provable (Const := WithParams Const) W.raw (.imp φ ψ) :=
    provable_imp_of_insert (Const := WithParams Const) hInsert
  exact hNotImp hImpRaw

/-- Scheduler-based implication successor for supported presented worlds.  If
`φ → ψ` is absent, the successor extends the raw base plus `φ` and still omits
`ψ`, while preserving the raw support interface needed by the Kripke frame. -/
theorem SupportedPresentedIntuitionisticWorld.exists_supported_successor_for_imp
    (W : SupportedPresentedIntuitionisticWorld Const)
    (S : RawAlternatingStageScheduler (Base := Base) (Const := Const) W.level)
    {φ ψ : ClosedFormula (WithParams Const)}
    (hφ : FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) W.level φ)
    (hψ : FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) W.level ψ)
    (hNotImp : (.imp φ ψ : ClosedFormula (WithParams Const)) ∉ W.carrier) :
    ∃ W' : SupportedPresentedIntuitionisticWorld (Base := Base) Const,
      W'.level = W.level + 1 ∧
      (∀ {χ : ClosedFormula (WithParams Const)}, χ ∈ W.raw → χ ∈ W'.carrier) ∧
      φ ∈ W'.carrier ∧
      ψ ∉ W'.carrier := by
  have hRawLayer : AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (W.level + 1) W.raw :=
    AvoidsParamLayersFrom.mono
      (Base := Base) (Const := Const) (Nat.le_succ W.level) W.raw_avoids_future
  have hφLayer : FormulaAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (W.level + 1) φ :=
    FormulaAvoidsParamLayersFrom.mono
      (Base := Base) (Const := Const) (Nat.le_succ W.level) hφ
  have hLayer : AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (W.level + 1) (insert φ W.raw) :=
    AvoidsParamLayersFrom.insert
      (Base := Base) (Const := Const) hRawLayer hφLayer
  have hStage : AvoidsParamStagesFrom
      (Base := Base) (Const := Const) W.level 0 (insert φ W.raw) :=
    AvoidsParamStagesFrom.insert
      (Base := Base) (Const := Const)
      (AvoidsParamLayersFrom.to_stages
        (Base := Base) (Const := Const) W.raw_avoids_future)
      (FormulaAvoidsParamLayersFrom.to_stages
        (Base := Base) (Const := Const) hφ)
  have hψStage : FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) W.level 0 ψ :=
    FormulaAvoidsParamLayersFrom.to_stages
      (Base := Base) (Const := Const) hψ
  have hNot : ¬ Provable (Const := WithParams Const) (insert φ W.raw) ψ :=
    SupportedPresentedIntuitionisticWorld.not_provable_of_not_imp_mem
      (Base := Base) (Const := Const) W hNotImp
  obtain ⟨W', hLevel, hExt, hOmit⟩ :=
    exists_supported_presented_rawAlternatingScheduledStageLimit_separating
      (Base := Base) (Const := Const) (ℓ := W.level) (T := insert φ W.raw)
      S hLayer hStage hψStage hNot
  refine ⟨W', hLevel, ?_, ?_, hOmit⟩
  · intro χ hχ
    exact hExt (Set.mem_insert_of_mem φ hχ)
  · exact hExt (Set.mem_insert φ W.raw)

/-- Scheduler-based implication successor at any sufficiently high layer.  This
is the version used by the full canonical implication clause when the
antecedent or consequent mentions parameters above the current world's level. -/
theorem SupportedPresentedIntuitionisticWorld.exists_supported_successor_for_imp_at_bound
    (W : SupportedPresentedIntuitionisticWorld Const)
    {m : Nat}
    (S : RawAlternatingStageScheduler (Base := Base) (Const := Const) m)
    {φ ψ : ClosedFormula (WithParams Const)}
    (hm : W.level ≤ m)
    (hφMax : maxParam φ ≤ m)
    (hψMax : maxParam ψ ≤ m)
    (hNotImp : (.imp φ ψ : ClosedFormula (WithParams Const)) ∉ W.carrier) :
    ∃ W' : SupportedPresentedIntuitionisticWorld (Base := Base) Const,
      W'.level = m + 1 ∧
      (∀ {χ : ClosedFormula (WithParams Const)}, χ ∈ W.raw → χ ∈ W'.carrier) ∧
      φ ∈ W'.carrier ∧
      ψ ∉ W'.carrier := by
  have hRawLayer : AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) W.raw :=
    AvoidsParamLayersFrom.mono
      (Base := Base) (Const := Const) (by omega) W.raw_avoids_future
  have hRawStageLayer : AvoidsParamLayersFrom
      (Base := Base) (Const := Const) m W.raw :=
    AvoidsParamLayersFrom.mono
      (Base := Base) (Const := Const) hm W.raw_avoids_future
  have hφLayer : FormulaAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) φ :=
    FormulaAvoidsParamLayersFrom.mono
      (Base := Base) (Const := Const) (by omega)
      (FormulaAvoidsParamLayersFrom.mono
        (Base := Base) (Const := Const) hφMax
        (FormulaAvoidsParamLayersFrom.of_maxParam
          (Base := Base) (Const := Const) φ))
  have hφStageLayer : FormulaAvoidsParamLayersFrom
      (Base := Base) (Const := Const) m φ :=
    FormulaAvoidsParamLayersFrom.mono
      (Base := Base) (Const := Const) hφMax
      (FormulaAvoidsParamLayersFrom.of_maxParam
        (Base := Base) (Const := Const) φ)
  have hLayer : AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) (insert φ W.raw) :=
    AvoidsParamLayersFrom.insert
      (Base := Base) (Const := Const) hRawLayer hφLayer
  have hStage : AvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 (insert φ W.raw) :=
    AvoidsParamStagesFrom.insert
      (Base := Base) (Const := Const)
      (AvoidsParamLayersFrom.to_stages
        (Base := Base) (Const := Const) hRawStageLayer)
      (FormulaAvoidsParamLayersFrom.to_stages
        (Base := Base) (Const := Const) hφStageLayer)
  have hψStage : FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) m 0 ψ :=
    FormulaAvoidsParamLayersFrom.to_stages
      (Base := Base) (Const := Const)
      (FormulaAvoidsParamLayersFrom.mono
        (Base := Base) (Const := Const) hψMax
        (FormulaAvoidsParamLayersFrom.of_maxParam
          (Base := Base) (Const := Const) ψ))
  have hNot : ¬ Provable (Const := WithParams Const) (insert φ W.raw) ψ :=
    SupportedPresentedIntuitionisticWorld.not_provable_of_not_imp_mem
      (Base := Base) (Const := Const) W hNotImp
  obtain ⟨W', hLevel, hExt, hOmit⟩ :=
    exists_supported_presented_rawAlternatingScheduledStageLimit_separating
      (Base := Base) (Const := Const) (ℓ := m) (T := insert φ W.raw)
      S hLayer hStage hψStage hNot
  refine ⟨W', hLevel, ?_, ?_, hOmit⟩
  · intro χ hχ
    exact hExt (Set.mem_insert_of_mem φ hχ)
  · exact hExt (Set.mem_insert φ W.raw)

/-- If an implication is absent from the closed carrier of a full presented
world, then adding the antecedent to the raw base cannot derive the consequent. -/
theorem FullPresentedIntuitionisticWorld.not_provable_of_not_imp_mem
    (W : FullPresentedIntuitionisticWorld Const)
    {φ ψ : ClosedFormula (WithParams Const)}
    (hNotImp : (.imp φ ψ : ClosedFormula (WithParams Const)) ∉ W.carrier) :
    ¬ Provable (Const := WithParams Const) (insert φ W.raw) ψ := by
  exact SupportedPresentedIntuitionisticWorld.not_provable_of_not_imp_mem
    (Base := Base) (Const := Const) W.toSupported
    (by
      simpa [FullPresentedIntuitionisticWorld.toSupported,
        SupportedPresentedIntuitionisticWorld.carrier,
        FullPresentedIntuitionisticWorld.carrier] using hNotImp)

/-- Raw universal-case separation seed for supported presented worlds.  If
`∀x.φ` is absent from the carrier, then a fresh parameter instance is not
provable from the raw base. -/
theorem SupportedPresentedIntuitionisticWorld.not_provable_fresh_instance_of_not_all_mem
    (W : SupportedPresentedIntuitionisticWorld Const)
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    {m k : Nat} (hm : W.level ≤ m)
    (hφfresh :
      NoConstOccurrence (param σ (Nat.pair m k) : WithParams Const σ) φ)
    (hNotAll : (.all φ : ClosedFormula (WithParams Const)) ∉ W.carrier) :
    ¬ Provable (Const := WithParams Const) W.raw
        (instantiate (Base := Base) (.const (param σ (Nat.pair m k))) φ) := by
  intro hInst
  have hAllRaw : Provable (Const := WithParams Const) W.raw (.all φ) :=
    provable_all_intro_fresh
      (Const := WithParams Const) (T := W.raw)
      (c := param σ (Nat.pair m k))
      (by
        intro ψ hψ
        exact W.raw_avoids_future ψ hψ σ m k hm)
      hφfresh hInst
  exact hNotAll hAllRaw

/-- Scheduler-based universal successor for supported presented worlds.  A
failed universal at `W` yields a supported higher-level successor omitting a
fresh parameter instance. -/
theorem SupportedPresentedIntuitionisticWorld.exists_supported_successor_for_all
    (W : SupportedPresentedIntuitionisticWorld Const)
    {m k : Nat}
    (S : RawAlternatingStageScheduler (Base := Base) (Const := Const) (m + 1))
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hm : W.level ≤ m)
    (hφfresh :
      NoConstOccurrence (param σ (Nat.pair m k) : WithParams Const σ) φ)
    (hφfuture :
      ∀ (τ : Ty Base) (r j : Nat), m + 1 ≤ r →
        NoConstOccurrence (param τ (Nat.pair r j) : WithParams Const τ) φ)
    (hNotAll : (.all φ : ClosedFormula (WithParams Const)) ∉ W.carrier) :
    ∃ W' : SupportedPresentedIntuitionisticWorld (Base := Base) Const,
      W'.level = (m + 1) + 1 ∧
      (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ W.raw → ψ ∈ W'.carrier) ∧
      instantiate (Base := Base) (.const (param σ (Nat.pair m k))) φ ∉ W'.carrier := by
  let θ : ClosedFormula (WithParams Const) :=
    instantiate (Base := Base) (.const (param σ (Nat.pair m k))) φ
  have hRawLayer : AvoidsParamLayersFrom
      (Base := Base) (Const := Const) ((m + 1) + 1) W.raw := by
    exact AvoidsParamLayersFrom.mono
      (Base := Base) (Const := Const) (by omega) W.raw_avoids_future
  have hRawStageLayer : AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) W.raw := by
    exact AvoidsParamLayersFrom.mono
      (Base := Base) (Const := Const) (by omega) W.raw_avoids_future
  have hStage : AvoidsParamStagesFrom
      (Base := Base) (Const := Const) (m + 1) 0 W.raw :=
    AvoidsParamLayersFrom.to_stages
      (Base := Base) (Const := Const) hRawStageLayer
  have hθFuture : FormulaAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) θ := by
    intro τ r j hmr
    exact noConstOccurrence_param_pair_ne_instantiate
      (Const := Const) (σ := τ) (ρ := σ) (m := r) (ℓ := m) (k := j) (j := k)
      (by omega)
      (hφfuture τ r j hmr)
  have hθStage : FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) (m + 1) 0 θ :=
    FormulaAvoidsParamLayersFrom.to_stages
      (Base := Base) (Const := Const) hθFuture
  have hNotθ : ¬ Provable (Const := WithParams Const) W.raw θ :=
    SupportedPresentedIntuitionisticWorld.not_provable_fresh_instance_of_not_all_mem
      (Base := Base) (Const := Const) W hm hφfresh hNotAll
  exact exists_supported_presented_rawAlternatingScheduledStageLimit_separating
    (Base := Base) (Const := Const) (ℓ := m + 1) (T := W.raw)
    S hRawLayer hStage hθStage hNotθ

/-- Finite prefixes of the stage-indexed raw alternating construction.  The
outer layer bound stays fixed, while the future-stage bound advances by the
prefix length. -/
theorem exists_raw_alternating_stage_prefix
    (N : Nat) {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hBodyLayer : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hBodyStage : BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 bodyEnum)
    (hPairLayer : FormulaPairAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (ℓ + 1) pairEnum)
    (hPairStage : FormulaPairAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ 0 pairEnum)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ∃ R : ClosedTheorySet (WithParams Const),
      (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ R) ∧
      ¬ Provable (Const := WithParams Const) R θ ∧
      AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) R ∧
      AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ N R := by
  induction N with
  | zero =>
      refine ⟨T, ?_, hNot, hLayer, ?_⟩
      · intro ψ hψ
        exact hψ
      · simpa using hStage
  | succ N ih =>
      obtain ⟨R, hExt, hOmit, hAvoidLayer, hAvoidStage⟩ := ih
      have hBodyStageN : BodyAvoidsParamStagesFrom
          (Base := Base) (Const := Const) ℓ (N + 1) bodyEnum := by
        exact BodyAvoidsParamStagesFrom.mono
          (Base := Base) (Const := Const) (by omega) hBodyStage
      have hPairStageN : FormulaPairAvoidsParamStagesFrom
          (Base := Base) (Const := Const) ℓ N pairEnum := by
        exact FormulaPairAvoidsParamStagesFrom.mono
          (Base := Base) (Const := Const) (by omega) hPairStage
      have hθStageN : FormulaAvoidsParamStagesFrom
          (Base := Base) (Const := Const) ℓ N θ := by
        exact FormulaAvoidsParamStagesFrom.mono
          (Base := Base) (Const := Const) (by omega) hθStage
      obtain ⟨R', hStepExt, hStepOmit, hStepLayer, hStepStage, _hWitness, _hBranch⟩ :=
        exists_raw_alternating_stage_step
          (Base := Base) (Const := Const) (ℓ := ℓ) (s := N) (T := R)
          bodyEnum hfair pairEnum N hAvoidLayer hAvoidStage hBodyLayer hBodyStageN
          hPairLayer hPairStageN hθStageN hOmit
      refine ⟨R', ?_, hStepOmit, hStepLayer, ?_⟩
      · intro ψ hψ
        exact hStepExt (hExt hψ)
      · simpa using hStepStage

/-- A proof-carrying finite approximation to the stage-indexed raw alternating
construction.  The outer support bound stays fixed at `ℓ + 1`; the stage bound
advances with the approximation index. -/
structure RawAlternatingStageApprox
    (ℓ : Nat) (T : ClosedTheorySet (WithParams Const))
    (θ : ClosedFormula (WithParams Const)) (N : Nat) where
  theory : ClosedTheorySet (WithParams Const)
  base_subset : ∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ theory
  omits : ¬ Provable (Const := WithParams Const) theory θ
  avoids_layer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) theory
  avoids_stage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ N theory

/-- A coherent chosen sequence of stage-indexed finite approximations.  It is
the fixed-outer-layer replacement for the older layer-consuming approximation
chain below. -/
noncomputable def rawAlternatingStageApprox
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hBodyLayer : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hBodyStage : BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 bodyEnum)
    (hPairLayer : FormulaPairAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (ℓ + 1) pairEnum)
    (hPairStage : FormulaPairAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ 0 pairEnum)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    (N : Nat) → RawAlternatingStageApprox (Base := Base) (Const := Const) ℓ T θ N
  | 0 =>
      { theory := T
        base_subset := by intro ψ hψ; exact hψ
        omits := hNot
        avoids_layer := hLayer
        avoids_stage := by simpa using hStage }
  | N + 1 =>
      let prev :=
        rawAlternatingStageApprox
          bodyEnum hfair pairEnum hLayer hStage hBodyLayer hBodyStage
          hPairLayer hPairStage hθStage hNot N
      have hBodyStageN : BodyAvoidsParamStagesFrom
          (Base := Base) (Const := Const) ℓ (N + 1) bodyEnum := by
        exact BodyAvoidsParamStagesFrom.mono
          (Base := Base) (Const := Const) (by omega) hBodyStage
      have hPairStageN : FormulaPairAvoidsParamStagesFrom
          (Base := Base) (Const := Const) ℓ N pairEnum := by
        exact FormulaPairAvoidsParamStagesFrom.mono
          (Base := Base) (Const := Const) (by omega) hPairStage
      have hθStageN : FormulaAvoidsParamStagesFrom
          (Base := Base) (Const := Const) ℓ N θ := by
        exact FormulaAvoidsParamStagesFrom.mono
          (Base := Base) (Const := Const) (by omega) hθStage
      let stepExists :=
        exists_raw_alternating_stage_step
          (Base := Base) (Const := Const) (ℓ := ℓ) (s := N) (T := prev.theory)
          bodyEnum hfair pairEnum N prev.avoids_layer prev.avoids_stage
          hBodyLayer hBodyStageN hPairLayer hPairStageN hθStageN prev.omits
      let R := Classical.choose stepExists
      have hR := Classical.choose_spec stepExists
      { theory := R
        base_subset := by
          intro ψ hψ
          exact hR.1 (prev.base_subset hψ)
        omits := hR.2.1
        avoids_layer := hR.2.2.1
        avoids_stage := hR.2.2.2.1 }

/-- Adjacent monotonicity of the chosen stage-indexed approximation chain. -/
theorem rawAlternatingStageApprox_subset_succ
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hBodyLayer : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hBodyStage : BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 bodyEnum)
    (hPairLayer : FormulaPairAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (ℓ + 1) pairEnum)
    (hPairStage : FormulaPairAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ 0 pairEnum)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ)
    (N : Nat) :
    ∀ {ψ : ClosedFormula (WithParams Const)},
      ψ ∈ (rawAlternatingStageApprox
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
        hBodyStage hPairLayer hPairStage hθStage hNot N).theory →
      ψ ∈ (rawAlternatingStageApprox
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
        hBodyStage hPairLayer hPairStage hθStage hNot (N + 1)).theory := by
  intro ψ hψ
  let prev :=
    rawAlternatingStageApprox
      (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
      hBodyStage hPairLayer hPairStage hθStage hNot N
  change ψ ∈ prev.theory at hψ
  have hBodyStageN : BodyAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ (N + 1) bodyEnum := by
    exact BodyAvoidsParamStagesFrom.mono
      (Base := Base) (Const := Const) (by omega) hBodyStage
  have hPairStageN : FormulaPairAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ N pairEnum := by
    exact FormulaPairAvoidsParamStagesFrom.mono
      (Base := Base) (Const := Const) (by omega) hPairStage
  have hθStageN : FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ N θ := by
    exact FormulaAvoidsParamStagesFrom.mono
      (Base := Base) (Const := Const) (by omega) hθStage
  let stepExists :=
    exists_raw_alternating_stage_step
      (Base := Base) (Const := Const) (ℓ := ℓ) (s := N) (T := prev.theory)
      bodyEnum hfair pairEnum N prev.avoids_layer prev.avoids_stage
      hBodyLayer hBodyStageN hPairLayer hPairStageN hθStageN prev.omits
  have hR := Classical.choose_spec stepExists
  change ψ ∈ Classical.choose stepExists
  exact hR.1 hψ

/-- If the selected disjunction is provable at a stage-indexed raw
approximation, the next approximation contains one of its disjuncts. -/
theorem rawAlternatingStageApprox_or_branch_succ
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hBodyLayer : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hBodyStage : BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 bodyEnum)
    (hPairLayer : FormulaPairAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (ℓ + 1) pairEnum)
    (hPairStage : FormulaPairAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ 0 pairEnum)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ)
    (N : Nat)
    (hOr : Provable (Const := WithParams Const)
      (rawAlternatingStageApprox
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
        hBodyStage hPairLayer hPairStage hθStage hNot N).theory
      (.or (pairEnum N).1 (pairEnum N).2)) :
    ∃ δ : ClosedFormula (WithParams Const),
      (δ = (pairEnum N).1 ∨ δ = (pairEnum N).2) ∧
        δ ∈ (rawAlternatingStageApprox
          (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
          hBodyStage hPairLayer hPairStage hθStage hNot (N + 1)).theory := by
  let prev :=
    rawAlternatingStageApprox
      (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
      hBodyStage hPairLayer hPairStage hθStage hNot N
  change Provable (Const := WithParams Const) prev.theory
      (.or (pairEnum N).1 (pairEnum N).2) at hOr
  have hBodyStageN : BodyAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ (N + 1) bodyEnum := by
    exact BodyAvoidsParamStagesFrom.mono
      (Base := Base) (Const := Const) (by omega) hBodyStage
  have hPairStageN : FormulaPairAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ N pairEnum := by
    exact FormulaPairAvoidsParamStagesFrom.mono
      (Base := Base) (Const := Const) (by omega) hPairStage
  have hθStageN : FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ N θ := by
    exact FormulaAvoidsParamStagesFrom.mono
      (Base := Base) (Const := Const) (by omega) hθStage
  let stepExists :=
    exists_raw_alternating_stage_step
      (Base := Base) (Const := Const) (ℓ := ℓ) (s := N) (T := prev.theory)
      bodyEnum hfair pairEnum N prev.avoids_layer prev.avoids_stage
      hBodyLayer hBodyStageN hPairLayer hPairStageN hθStageN prev.omits
  have hR := Classical.choose_spec stepExists
  obtain ⟨δ, hδchoice, hδmem⟩ := hR.2.2.2.2.2 hOr
  refine ⟨δ, hδchoice, ?_⟩
  change δ ∈ Classical.choose stepExists
  exact hδmem

/-- The next chosen stage-indexed approximation witnesses any existential
already provable at the current approximation. -/
theorem rawAlternatingStageApprox_exists_witness_succ
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hBodyLayer : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hBodyStage : BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 bodyEnum)
    (hPairLayer : FormulaPairAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (ℓ + 1) pairEnum)
    (hPairStage : FormulaPairAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ 0 pairEnum)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ)
    (N : Nat) {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hEx : Provable (Const := WithParams Const)
      (rawAlternatingStageApprox
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
        hBodyStage hPairLayer hPairStage hθStage hNot N).theory
      (.ex φ)) :
    ∃ t : ClosedTerm (WithParams Const) σ,
      instantiate (Base := Base) t φ ∈
        (rawAlternatingStageApprox
          (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
          hBodyStage hPairLayer hPairStage hθStage hNot (N + 1)).theory := by
  let prev :=
    rawAlternatingStageApprox
      (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
      hBodyStage hPairLayer hPairStage hθStage hNot N
  change Provable (Const := WithParams Const) prev.theory (.ex φ) at hEx
  have hBodyStageN : BodyAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ (N + 1) bodyEnum := by
    exact BodyAvoidsParamStagesFrom.mono
      (Base := Base) (Const := Const) (by omega) hBodyStage
  have hPairStageN : FormulaPairAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ N pairEnum := by
    exact FormulaPairAvoidsParamStagesFrom.mono
      (Base := Base) (Const := Const) (by omega) hPairStage
  have hθStageN : FormulaAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ N θ := by
    exact FormulaAvoidsParamStagesFrom.mono
      (Base := Base) (Const := Const) (by omega) hθStage
  let stepExists :=
    exists_raw_alternating_stage_step
      (Base := Base) (Const := Const) (ℓ := ℓ) (s := N) (T := prev.theory)
      bodyEnum hfair pairEnum N prev.avoids_layer prev.avoids_stage
      hBodyLayer hBodyStageN hPairLayer hPairStageN hθStageN prev.omits
  have hR := Classical.choose_spec stepExists
  have hExR : Provable (Const := WithParams Const) (Classical.choose stepExists) (.ex φ) :=
    provable_mono (Const := WithParams Const) hR.1 hEx
  exact hR.2.2.2.2.1 hExR

/-- Monotonicity of the chosen stage-indexed approximation chain. -/
theorem rawAlternatingStageApprox_mono
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hBodyLayer : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hBodyStage : BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 bodyEnum)
    (hPairLayer : FormulaPairAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (ℓ + 1) pairEnum)
    (hPairStage : FormulaPairAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ 0 pairEnum)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ)
    {m n : Nat} (hmn : m ≤ n) :
    ∀ {ψ : ClosedFormula (WithParams Const)},
      ψ ∈ (rawAlternatingStageApprox
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
        hBodyStage hPairLayer hPairStage hθStage hNot m).theory →
      ψ ∈ (rawAlternatingStageApprox
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
        hBodyStage hPairLayer hPairStage hθStage hNot n).theory := by
  induction n, hmn using Nat.le_induction with
  | base =>
      intro ψ hψ
      exact hψ
  | succ n _ ih =>
      intro ψ hψ
      exact rawAlternatingStageApprox_subset_succ
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
        hBodyStage hPairLayer hPairStage hθStage hNot n (ih hψ)

/-- The fixed-outer-layer raw limit of the chosen stage-indexed approximation
chain. -/
noncomputable def rawAlternatingStageLimit
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hBodyLayer : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hBodyStage : BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 bodyEnum)
    (hPairLayer : FormulaPairAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (ℓ + 1) pairEnum)
    (hPairStage : FormulaPairAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ 0 pairEnum)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ClosedTheorySet (WithParams Const) :=
  {ψ | ∃ N, ψ ∈ (rawAlternatingStageApprox
    (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
    hBodyStage hPairLayer hPairStage hθStage hNot N).theory}

/-- The initial raw base is included in the stage-indexed raw limit. -/
theorem subset_rawAlternatingStageLimit
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hBodyLayer : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hBodyStage : BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 bodyEnum)
    (hPairLayer : FormulaPairAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (ℓ + 1) pairEnum)
    (hPairStage : FormulaPairAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ 0 pairEnum)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T →
      ψ ∈ rawAlternatingStageLimit
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
        hBodyStage hPairLayer hPairStage hθStage hNot := by
  intro ψ hψ
  refine ⟨0, ?_⟩
  exact (rawAlternatingStageApprox
    (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
    hBodyStage hPairLayer hPairStage hθStage hNot 0).base_subset hψ

/-- Every finite stage-indexed raw approximation is included in the limit. -/
theorem rawAlternatingStageApprox_subset_limit
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hBodyLayer : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hBodyStage : BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 bodyEnum)
    (hPairLayer : FormulaPairAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (ℓ + 1) pairEnum)
    (hPairStage : FormulaPairAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ 0 pairEnum)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ)
    (N : Nat) :
    ∀ {ψ : ClosedFormula (WithParams Const)},
      ψ ∈ (rawAlternatingStageApprox
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
        hBodyStage hPairLayer hPairStage hθStage hNot N).theory →
      ψ ∈ rawAlternatingStageLimit
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
        hBodyStage hPairLayer hPairStage hθStage hNot := by
  intro ψ hψ
  exact ⟨N, hψ⟩

/-- The stage-indexed raw limit preserves the fixed outer support bound. -/
theorem rawAlternatingStageLimit_avoids_future_layers
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hBodyLayer : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hBodyStage : BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 bodyEnum)
    (hPairLayer : FormulaPairAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (ℓ + 1) pairEnum)
    (hPairStage : FormulaPairAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ 0 pairEnum)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1)
      (rawAlternatingStageLimit
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
        hBodyStage hPairLayer hPairStage hθStage hNot) := by
  intro ψ hψ σ m k hm
  rcases hψ with ⟨N, hψN⟩
  exact (rawAlternatingStageApprox
    (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
    hBodyStage hPairLayer hPairStage hθStage hNot N).avoids_layer ψ hψN σ m k hm

/-- A finite list of formulas from the stage-indexed raw limit already occurs
in one finite stage-indexed raw approximation. -/
theorem exists_stage_rawAlternatingStageLimit
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hBodyLayer : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hBodyStage : BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 bodyEnum)
    (hPairLayer : FormulaPairAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (ℓ + 1) pairEnum)
    (hPairStage : FormulaPairAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ 0 pairEnum)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ∀ (Γ : List (ClosedFormula (WithParams Const))),
      (∀ ψ ∈ Γ, ψ ∈ rawAlternatingStageLimit
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
        hBodyStage hPairLayer hPairStage hθStage hNot) →
      ∃ N, ∀ ψ ∈ Γ, ψ ∈ (rawAlternatingStageApprox
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
        hBodyStage hPairLayer hPairStage hθStage hNot N).theory
  | [], _ => ⟨0, by intro ψ hψ; cases hψ⟩
  | a :: Γ, hΓ => by
      obtain ⟨N, hN⟩ :=
        exists_stage_rawAlternatingStageLimit
          bodyEnum hfair pairEnum hLayer hStage hBodyLayer hBodyStage hPairLayer hPairStage
          hθStage hNot Γ
          (fun ψ hψ => hΓ ψ (List.mem_cons_of_mem _ hψ))
      obtain ⟨na, hna⟩ := hΓ a List.mem_cons_self
      refine ⟨max N na, fun ψ hψ => ?_⟩
      rcases List.mem_cons.mp hψ with rfl | hψ'
      · exact rawAlternatingStageApprox_mono
          (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
          hBodyStage hPairLayer hPairStage hθStage hNot
          (le_max_right N na) hna
      · exact rawAlternatingStageApprox_mono
          (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
          hBodyStage hPairLayer hPairStage hθStage hNot
          (le_max_left N na) (hN ψ hψ')

/-- The stage-indexed raw limit still omits the target formula. -/
theorem rawAlternatingStageLimit_omits
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hBodyLayer : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hBodyStage : BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 bodyEnum)
    (hPairLayer : FormulaPairAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (ℓ + 1) pairEnum)
    (hPairStage : FormulaPairAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ 0 pairEnum)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ¬ Provable (Const := WithParams Const)
      (rawAlternatingStageLimit
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
        hBodyStage hPairLayer hPairStage hθStage hNot) θ := by
  intro hProv
  rcases hProv with ⟨Γ, hΓ, d⟩
  obtain ⟨N, hN⟩ :=
    exists_stage_rawAlternatingStageLimit
      (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
      hBodyStage hPairLayer hPairStage hθStage hNot Γ hΓ
  exact (rawAlternatingStageApprox
    (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
    hBodyStage hPairLayer hPairStage hθStage hNot N).omits
    ⟨Γ, hN, d⟩

/-- The stage-indexed raw limit is consistent whenever it omits the target. -/
theorem rawAlternatingStageLimit_consistent
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hBodyLayer : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hBodyStage : BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 bodyEnum)
    (hPairLayer : FormulaPairAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (ℓ + 1) pairEnum)
    (hPairStage : FormulaPairAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ 0 pairEnum)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    Consistent (Const := WithParams Const)
      (rawAlternatingStageLimit
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
        hBodyStage hPairLayer hPairStage hθStage hNot) := by
  intro hbot
  exact rawAlternatingStageLimit_omits
    (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
    hBodyStage hPairLayer hPairStage hθStage hNot
    (by
      rcases hbot with ⟨Γ, hΓ, d⟩
      exact ⟨Γ, hΓ, ExtDerivation.botE d⟩)

/-- The deductive-closure readout of the stage-indexed raw limit is
disjunction-prime when the pair enumeration is fair. -/
theorem rawAlternatingStageLimit_prime_or
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    (hPairFair : FormulaPairFairAfter (Base := Base) (Const := Const) pairEnum)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hBodyLayer : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hBodyStage : BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 bodyEnum)
    (hPairLayer : FormulaPairAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (ℓ + 1) pairEnum)
    (hPairStage : FormulaPairAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ 0 pairEnum)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ∀ {φ ψ : ClosedFormula (WithParams Const)},
      (.or φ ψ : ClosedFormula (WithParams Const)) ∈
        ClosedTheorySet.provableClosure (Const := WithParams Const)
          (rawAlternatingStageLimit
            (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
            hBodyStage hPairLayer hPairStage hθStage hNot) →
        φ ∈ ClosedTheorySet.provableClosure (Const := WithParams Const)
          (rawAlternatingStageLimit
            (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
            hBodyStage hPairLayer hPairStage hθStage hNot) ∨
          ψ ∈ ClosedTheorySet.provableClosure (Const := WithParams Const)
            (rawAlternatingStageLimit
              (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
              hBodyStage hPairLayer hPairStage hθStage hNot) := by
  intro φ ψ hOr
  rcases hOr with ⟨Γ, hΓ, d⟩
  obtain ⟨N, hN⟩ :=
    exists_stage_rawAlternatingStageLimit
      (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
      hBodyStage hPairLayer hPairStage hθStage hNot Γ hΓ
  obtain ⟨n, hNn, hpair⟩ := hPairFair (φ, ψ) N
  have hOrN : Provable (Const := WithParams Const)
      (rawAlternatingStageApprox
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
        hBodyStage hPairLayer hPairStage hθStage hNot N).theory
      (.or φ ψ) := ⟨Γ, hN, d⟩
  have hOrn : Provable (Const := WithParams Const)
      (rawAlternatingStageApprox
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
        hBodyStage hPairLayer hPairStage hθStage hNot n).theory
      (.or (pairEnum n).1 (pairEnum n).2) := by
    have hMono : ∀ {ξ : ClosedFormula (WithParams Const)},
        ξ ∈ (rawAlternatingStageApprox
          (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
          hBodyStage hPairLayer hPairStage hθStage hNot N).theory →
        ξ ∈ (rawAlternatingStageApprox
          (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
          hBodyStage hPairLayer hPairStage hθStage hNot n).theory :=
      rawAlternatingStageApprox_mono
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
        hBodyStage hPairLayer hPairStage hθStage hNot hNn
    have hLift : Provable (Const := WithParams Const)
        (rawAlternatingStageApprox
          (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
          hBodyStage hPairLayer hPairStage hθStage hNot n).theory
        (.or φ ψ) :=
      provable_mono (Const := WithParams Const) hMono hOrN
    simpa [hpair] using hLift
  obtain ⟨δ, hδchoice, hδmem⟩ :=
    rawAlternatingStageApprox_or_branch_succ
      (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
      hBodyStage hPairLayer hPairStage hθStage hNot n hOrn
  have hδlimit : δ ∈ rawAlternatingStageLimit
      (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
      hBodyStage hPairLayer hPairStage hθStage hNot := by
    exact rawAlternatingStageApprox_subset_limit
      (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
      hBodyStage hPairLayer hPairStage hθStage hNot (n + 1) hδmem
  rcases hδchoice with hδ | hδ
  · left
    rw [hpair] at hδ
    cases hδ
    exact ClosedTheorySet.subset_provableClosure
      (Const := WithParams Const)
      (rawAlternatingStageLimit
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
        hBodyStage hPairLayer hPairStage hθStage hNot)
      hδlimit
  · right
    rw [hpair] at hδ
    cases hδ
    exact ClosedTheorySet.subset_provableClosure
      (Const := WithParams Const)
      (rawAlternatingStageLimit
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
        hBodyStage hPairLayer hPairStage hθStage hNot)
      hδlimit

/-- The deductive-closure readout of the stage-indexed raw limit has the
existential witness property when the body enumeration is fair. -/
theorem rawAlternatingStageLimit_exists_witness
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    {θ : ClosedFormula (WithParams Const)}
    (hLayer : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hStage : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 T)
    (hBodyLayer : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hBodyStage : BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 bodyEnum)
    (hPairLayer : FormulaPairAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (ℓ + 1) pairEnum)
    (hPairStage : FormulaPairAvoidsParamStagesFrom
      (Base := Base) (Const := Const) ℓ 0 pairEnum)
    (hθStage : FormulaAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ 0 θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ∀ {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
      (.ex φ : ClosedFormula (WithParams Const)) ∈
        ClosedTheorySet.provableClosure (Const := WithParams Const)
          (rawAlternatingStageLimit
            (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
            hBodyStage hPairLayer hPairStage hθStage hNot) →
        ∃ t : ClosedTerm (WithParams Const) σ,
          instantiate (Base := Base) t φ ∈
            ClosedTheorySet.provableClosure (Const := WithParams Const)
              (rawAlternatingStageLimit
                (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
                hBodyStage hPairLayer hPairStage hθStage hNot) := by
  intro σ φ hEx
  rcases hEx with ⟨Γ, hΓ, d⟩
  obtain ⟨N, hN⟩ :=
    exists_stage_rawAlternatingStageLimit
      (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
      hBodyStage hPairLayer hPairStage hθStage hNot Γ hΓ
  have hExN : Provable (Const := WithParams Const)
      (rawAlternatingStageApprox
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
        hBodyStage hPairLayer hPairStage hθStage hNot N).theory
      (.ex φ) := ⟨Γ, hN, d⟩
  obtain ⟨t, ht⟩ :=
    rawAlternatingStageApprox_exists_witness_succ
      (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
      hBodyStage hPairLayer hPairStage hθStage hNot N hExN
  refine ⟨t, ?_⟩
  exact ClosedTheorySet.subset_provableClosure
    (Const := WithParams Const)
    (rawAlternatingStageLimit
      (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
      hBodyStage hPairLayer hPairStage hθStage hNot)
    (rawAlternatingStageApprox_subset_limit
      (Base := Base) (Const := Const) bodyEnum hfair pairEnum hLayer hStage hBodyLayer
      hBodyStage hPairLayer hPairStage hθStage hNot (N + 1) ht)

/-- The global full-world raw limit assumptions are incompatible.  A pair
enumeration cannot be both globally fair and uniformly avoid a future parameter
layer, so full presented canonical worlds cannot be obtained from this global
stage construction.  The live construction interface is the supported scheduler
above. -/
theorem full_rawAlternatingStageLimit_global_assumptions_inconsistent
    {ℓ : Nat}
    (pairEnum : Nat → ClosedFormulaPair Const)
    (hPairFair : FormulaPairFairAfter (Base := Base) (Const := Const) pairEnum)
    (hPairLayer : FormulaPairAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (ℓ + 1) pairEnum) :
    False :=
  FormulaPairFairAfter.incompatible_with_avoids_layers
    (Base := Base) (Const := Const) hPairFair hPairLayer

/-- One total raw alternating step.  It always repairs witnesses and advances
the support layer; if the currently enumerated disjunction is derivable, the
result also contains one omission-preserving disjunct. -/
theorem exists_raw_alternating_step
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const) (n : Nat)
    {θ : ClosedFormula (WithParams Const)}
    (hT : AvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ T)
    (hBody : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hPair : FormulaPairAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ pairEnum)
    (hθ : FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ∃ R : ClosedTheorySet (WithParams Const),
      (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ R) ∧
      ¬ Provable (Const := WithParams Const) R θ ∧
      AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) R ∧
      (∀ {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
        Provable (Const := WithParams Const) R (.ex φ) →
          ∃ t : ClosedTerm (WithParams Const) σ,
            instantiate (Base := Base) t φ ∈ R) ∧
      (Provable (Const := WithParams Const) T (.or (pairEnum n).1 (pairEnum n).2) →
        ∃ δ : ClosedFormula (WithParams Const),
          (δ = (pairEnum n).1 ∨ δ = (pairEnum n).2) ∧ δ ∈ R) := by
  classical
  by_cases hOr : Provable (Const := WithParams Const) T (.or (pairEnum n).1 (pairEnum n).2)
  · obtain ⟨R, δ, hδchoice, hExt, hδR, hOmit, hAvoid, hWitness⟩ :=
      exists_raw_branch_witnessInstance_step
        (Base := Base) (Const := Const) (ℓ := ℓ) (T := T)
        bodyEnum hfair pairEnum n hT hBody hPair hθ hNot hOr
    refine ⟨R, hExt, hOmit, hAvoid, hWitness, ?_⟩
    intro _h
    exact ⟨δ, hδchoice, hδR⟩
  · obtain ⟨R, hExt, hOmit, hAvoid, hWitness⟩ :=
      exists_raw_witnessInstance_step
        (Base := Base) (Const := Const) (ℓ := ℓ) (T := T)
        bodyEnum hfair hT hBody hθ hNot
    refine ⟨R, hExt, hOmit, hAvoid, hWitness, ?_⟩
    intro hOr'
    exact False.elim (hOr hOr')

/-- Finite prefixes of the raw alternating construction exist and preserve the
core invariant: extension of the initial raw base, omission of the target, and
support above the advanced layer. -/
theorem exists_raw_alternating_prefix
    (N : Nat) {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    {θ : ClosedFormula (WithParams Const)}
    (hT : AvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ T)
    (hBody : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hPair : FormulaPairAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ pairEnum)
    (hθ : FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ∃ R : ClosedTheorySet (WithParams Const),
      (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ R) ∧
      ¬ Provable (Const := WithParams Const) R θ ∧
      AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + N) R := by
  induction N with
  | zero =>
      refine ⟨T, ?_, hNot, ?_⟩
      · intro ψ hψ
        exact hψ
      · simpa using hT
  | succ N ih =>
      obtain ⟨R, hExt, hOmit, hAvoid⟩ := ih
      have hBodyN : BodyAvoidsParamLayersFrom
          (Base := Base) (Const := Const) ((ℓ + N) + 1) bodyEnum := by
        exact BodyAvoidsParamLayersFrom.mono
          (Base := Base) (Const := Const)
          (by omega)
          hBody
      have hPairN : FormulaPairAvoidsParamLayersFrom
          (Base := Base) (Const := Const) (ℓ + N) pairEnum := by
        exact FormulaPairAvoidsParamLayersFrom.mono
          (Base := Base) (Const := Const)
          (by omega)
          hPair
      have hθN : FormulaAvoidsParamLayersFrom
          (Base := Base) (Const := Const) (ℓ + N) θ := by
        exact FormulaAvoidsParamLayersFrom.mono
          (Base := Base) (Const := Const)
          (by omega)
          hθ
      obtain ⟨R', hStepExt, hStepOmit, hStepAvoid, _hWitness, _hBranch⟩ :=
        exists_raw_alternating_step
          (Base := Base) (Const := Const) (ℓ := ℓ + N) (T := R)
          bodyEnum hfair pairEnum N hAvoid hBodyN hPairN hθN hOmit
      refine ⟨R', ?_, hStepOmit, ?_⟩
      · intro ψ hψ
        exact hStepExt (hExt hψ)
      · simpa [Nat.add_assoc] using hStepAvoid

/-- A proof-carrying finite approximation to the raw alternating construction.
The `N`th approximation extends the initial raw base, still omits the target,
and has support above layer `ℓ + N`. -/
structure RawAlternatingApprox
    (ℓ : Nat) (T : ClosedTheorySet (WithParams Const))
    (θ : ClosedFormula (WithParams Const)) (N : Nat) where
  theory : ClosedTheorySet (WithParams Const)
  base_subset : ∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ theory
  omits : ¬ Provable (Const := WithParams Const) theory θ
  avoids : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + N) theory

/-- A coherent chosen sequence of finite approximations, obtained by recursively
choosing the total alternating step.  This is the raw chain that the later limit
construction will union over. -/
noncomputable def rawAlternatingApprox
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    {θ : ClosedFormula (WithParams Const)}
    (hT : AvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ T)
    (hBody : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hPair : FormulaPairAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ pairEnum)
    (hθ : FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    (N : Nat) → RawAlternatingApprox (Base := Base) (Const := Const) ℓ T θ N
  | 0 =>
      { theory := T
        base_subset := by intro ψ hψ; exact hψ
        omits := hNot
        avoids := by simpa using hT }
  | N + 1 =>
      let prev := rawAlternatingApprox bodyEnum hfair pairEnum hT hBody hPair hθ hNot N
      have hBodyN : BodyAvoidsParamLayersFrom
          (Base := Base) (Const := Const) ((ℓ + N) + 1) bodyEnum := by
        exact BodyAvoidsParamLayersFrom.mono
          (Base := Base) (Const := Const) (by omega) hBody
      have hPairN : FormulaPairAvoidsParamLayersFrom
          (Base := Base) (Const := Const) (ℓ + N) pairEnum := by
        exact FormulaPairAvoidsParamLayersFrom.mono
          (Base := Base) (Const := Const) (by omega) hPair
      have hθN : FormulaAvoidsParamLayersFrom
          (Base := Base) (Const := Const) (ℓ + N) θ := by
        exact FormulaAvoidsParamLayersFrom.mono
          (Base := Base) (Const := Const) (by omega) hθ
      let stepExists :=
        exists_raw_alternating_step
          (Base := Base) (Const := Const) (ℓ := ℓ + N) (T := prev.theory)
          bodyEnum hfair pairEnum N prev.avoids hBodyN hPairN hθN prev.omits
      let R := Classical.choose stepExists
      have hR := Classical.choose_spec stepExists
      { theory := R
        base_subset := by
          intro ψ hψ
          exact hR.1 (prev.base_subset hψ)
        omits := hR.2.1
        avoids := by
          change AvoidsParamLayersFrom (Base := Base) (Const := Const)
            (ℓ + (N + 1)) (Classical.choose stepExists)
          simpa [Nat.add_assoc] using hR.2.2.1 }

/-- Adjacent monotonicity of the chosen raw alternating approximation chain. -/
theorem rawAlternatingApprox_subset_succ
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    {θ : ClosedFormula (WithParams Const)}
    (hT : AvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ T)
    (hBody : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hPair : FormulaPairAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ pairEnum)
    (hθ : FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ)
    (N : Nat) :
    ∀ {ψ : ClosedFormula (WithParams Const)},
      ψ ∈ (rawAlternatingApprox
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot N).theory →
      ψ ∈ (rawAlternatingApprox
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot (N + 1)).theory := by
  intro ψ hψ
  let prev := rawAlternatingApprox
    (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot N
  change ψ ∈ prev.theory at hψ
  have hBodyN : BodyAvoidsParamLayersFrom
      (Base := Base) (Const := Const) ((ℓ + N) + 1) bodyEnum := by
    exact BodyAvoidsParamLayersFrom.mono
      (Base := Base) (Const := Const) (by omega) hBody
  have hPairN : FormulaPairAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (ℓ + N) pairEnum := by
    exact FormulaPairAvoidsParamLayersFrom.mono
      (Base := Base) (Const := Const) (by omega) hPair
  have hθN : FormulaAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (ℓ + N) θ := by
    exact FormulaAvoidsParamLayersFrom.mono
      (Base := Base) (Const := Const) (by omega) hθ
  let stepExists :=
    exists_raw_alternating_step
      (Base := Base) (Const := Const) (ℓ := ℓ + N) (T := prev.theory)
      bodyEnum hfair pairEnum N prev.avoids hBodyN hPairN hθN prev.omits
  have hR := Classical.choose_spec stepExists
  change ψ ∈ Classical.choose stepExists
  exact hR.1 hψ

/-- If the selected disjunction is provable at a raw approximation stage, the
next chosen approximation contains one of its disjuncts. -/
theorem rawAlternatingApprox_or_branch_succ
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    {θ : ClosedFormula (WithParams Const)}
    (hT : AvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ T)
    (hBody : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hPair : FormulaPairAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ pairEnum)
    (hθ : FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ)
    (N : Nat)
    (hOr : Provable (Const := WithParams Const)
      (rawAlternatingApprox
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot N).theory
      (.or (pairEnum N).1 (pairEnum N).2)) :
    ∃ δ : ClosedFormula (WithParams Const),
      (δ = (pairEnum N).1 ∨ δ = (pairEnum N).2) ∧
        δ ∈ (rawAlternatingApprox
          (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot
          (N + 1)).theory := by
  let prev := rawAlternatingApprox
    (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot N
  change Provable (Const := WithParams Const) prev.theory
      (.or (pairEnum N).1 (pairEnum N).2) at hOr
  have hBodyN : BodyAvoidsParamLayersFrom
      (Base := Base) (Const := Const) ((ℓ + N) + 1) bodyEnum := by
    exact BodyAvoidsParamLayersFrom.mono
      (Base := Base) (Const := Const) (by omega) hBody
  have hPairN : FormulaPairAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (ℓ + N) pairEnum := by
    exact FormulaPairAvoidsParamLayersFrom.mono
      (Base := Base) (Const := Const) (by omega) hPair
  have hθN : FormulaAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (ℓ + N) θ := by
    exact FormulaAvoidsParamLayersFrom.mono
      (Base := Base) (Const := Const) (by omega) hθ
  let stepExists :=
    exists_raw_alternating_step
      (Base := Base) (Const := Const) (ℓ := ℓ + N) (T := prev.theory)
      bodyEnum hfair pairEnum N prev.avoids hBodyN hPairN hθN prev.omits
  have hR := Classical.choose_spec stepExists
  obtain ⟨δ, hδchoice, hδmem⟩ := hR.2.2.2.2 hOr
  refine ⟨δ, hδchoice, ?_⟩
  change δ ∈ Classical.choose stepExists
  exact hδmem

/-- The next chosen raw approximation witnesses any existential already provable
at the current approximation. -/
theorem rawAlternatingApprox_exists_witness_succ
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    {θ : ClosedFormula (WithParams Const)}
    (hT : AvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ T)
    (hBody : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hPair : FormulaPairAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ pairEnum)
    (hθ : FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ)
    (N : Nat) {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hEx : Provable (Const := WithParams Const)
      (rawAlternatingApprox
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot N).theory
      (.ex φ)) :
    ∃ t : ClosedTerm (WithParams Const) σ,
      instantiate (Base := Base) t φ ∈
        (rawAlternatingApprox
          (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot
          (N + 1)).theory := by
  let prev := rawAlternatingApprox
    (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot N
  change Provable (Const := WithParams Const) prev.theory (.ex φ) at hEx
  have hBodyN : BodyAvoidsParamLayersFrom
      (Base := Base) (Const := Const) ((ℓ + N) + 1) bodyEnum := by
    exact BodyAvoidsParamLayersFrom.mono
      (Base := Base) (Const := Const) (by omega) hBody
  have hPairN : FormulaPairAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (ℓ + N) pairEnum := by
    exact FormulaPairAvoidsParamLayersFrom.mono
      (Base := Base) (Const := Const) (by omega) hPair
  have hθN : FormulaAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (ℓ + N) θ := by
    exact FormulaAvoidsParamLayersFrom.mono
      (Base := Base) (Const := Const) (by omega) hθ
  let stepExists :=
    exists_raw_alternating_step
      (Base := Base) (Const := Const) (ℓ := ℓ + N) (T := prev.theory)
      bodyEnum hfair pairEnum N prev.avoids hBodyN hPairN hθN prev.omits
  have hR := Classical.choose_spec stepExists
  have hExR : Provable (Const := WithParams Const) (Classical.choose stepExists) (.ex φ) :=
    provable_mono (Const := WithParams Const) hR.1 hEx
  exact hR.2.2.2.1 hExR

/-- Monotonicity of the chosen raw alternating approximation chain. -/
theorem rawAlternatingApprox_mono
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    {θ : ClosedFormula (WithParams Const)}
    (hT : AvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ T)
    (hBody : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hPair : FormulaPairAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ pairEnum)
    (hθ : FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ)
    {m n : Nat} (hmn : m ≤ n) :
    ∀ {ψ : ClosedFormula (WithParams Const)},
      ψ ∈ (rawAlternatingApprox
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot m).theory →
      ψ ∈ (rawAlternatingApprox
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot n).theory := by
  induction n, hmn using Nat.le_induction with
  | base =>
      intro ψ hψ
      exact hψ
  | succ n _ ih =>
      intro ψ hψ
      exact rawAlternatingApprox_subset_succ
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot n
        (ih hψ)

/-- The raw limit of the chosen alternating approximation chain. -/
noncomputable def rawAlternatingLimit
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    {θ : ClosedFormula (WithParams Const)}
    (hT : AvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ T)
    (hBody : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hPair : FormulaPairAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ pairEnum)
    (hθ : FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ClosedTheorySet (WithParams Const) :=
  {ψ | ∃ N, ψ ∈ (rawAlternatingApprox
    (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot N).theory}

/-- The initial raw base is included in the alternating raw limit. -/
theorem subset_rawAlternatingLimit
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    {θ : ClosedFormula (WithParams Const)}
    (hT : AvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ T)
    (hBody : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hPair : FormulaPairAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ pairEnum)
    (hθ : FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T →
      ψ ∈ rawAlternatingLimit
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot := by
  intro ψ hψ
  refine ⟨0, ?_⟩
  exact (rawAlternatingApprox
    (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot 0).base_subset hψ

/-- Every finite raw approximation is included in the alternating raw limit. -/
theorem rawAlternatingApprox_subset_limit
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    {θ : ClosedFormula (WithParams Const)}
    (hT : AvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ T)
    (hBody : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hPair : FormulaPairAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ pairEnum)
    (hθ : FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ)
    (N : Nat) :
    ∀ {ψ : ClosedFormula (WithParams Const)},
      ψ ∈ (rawAlternatingApprox
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot N).theory →
      ψ ∈ rawAlternatingLimit
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot := by
  intro ψ hψ
  exact ⟨N, hψ⟩

/-- A finite list of formulas from the raw alternating limit already occurs in
one finite raw approximation. -/
theorem exists_stage_rawAlternatingLimit
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    {θ : ClosedFormula (WithParams Const)}
    (hT : AvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ T)
    (hBody : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hPair : FormulaPairAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ pairEnum)
    (hθ : FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ∀ (Γ : List (ClosedFormula (WithParams Const))),
      (∀ ψ ∈ Γ, ψ ∈ rawAlternatingLimit
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot) →
      ∃ N, ∀ ψ ∈ Γ, ψ ∈ (rawAlternatingApprox
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot N).theory
  | [], _ => ⟨0, by intro ψ hψ; cases hψ⟩
  | a :: Γ, hΓ => by
      obtain ⟨N, hN⟩ :=
        exists_stage_rawAlternatingLimit bodyEnum hfair pairEnum hT hBody hPair hθ hNot Γ
          (fun ψ hψ => hΓ ψ (List.mem_cons_of_mem _ hψ))
      obtain ⟨na, hna⟩ := hΓ a List.mem_cons_self
      refine ⟨max N na, fun ψ hψ => ?_⟩
      rcases List.mem_cons.mp hψ with rfl | hψ'
      · exact rawAlternatingApprox_mono
          (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot
          (le_max_right N na) hna
      · exact rawAlternatingApprox_mono
          (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot
          (le_max_left N na) (hN ψ hψ')

/-- The raw alternating limit still omits the target formula. -/
theorem rawAlternatingLimit_omits
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    {θ : ClosedFormula (WithParams Const)}
    (hT : AvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ T)
    (hBody : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hPair : FormulaPairAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ pairEnum)
    (hθ : FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ¬ Provable (Const := WithParams Const)
      (rawAlternatingLimit
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot) θ := by
  intro hProv
  rcases hProv with ⟨Γ, hΓ, d⟩
  obtain ⟨N, hN⟩ :=
    exists_stage_rawAlternatingLimit
      (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot Γ hΓ
  exact (rawAlternatingApprox
    (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot N).omits
    ⟨Γ, hN, d⟩

/-- The raw alternating limit is consistent whenever it omits the target formula. -/
theorem rawAlternatingLimit_consistent
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    {θ : ClosedFormula (WithParams Const)}
    (hT : AvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ T)
    (hBody : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hPair : FormulaPairAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ pairEnum)
    (hθ : FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    Consistent (Const := WithParams Const)
      (rawAlternatingLimit
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot) := by
  intro hbot
  exact rawAlternatingLimit_omits
    (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot
    (by
      rcases hbot with ⟨Γ, hΓ, d⟩
      exact ⟨Γ, hΓ, ExtDerivation.botE d⟩)

/-- The deductive-closure readout of the raw alternating limit is
disjunction-prime when the pair enumeration is fair. -/
theorem rawAlternatingLimit_prime_or
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    (hPairFair : FormulaPairFairAfter (Base := Base) (Const := Const) pairEnum)
    {θ : ClosedFormula (WithParams Const)}
    (hT : AvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ T)
    (hBody : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hPair : FormulaPairAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ pairEnum)
    (hθ : FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ∀ {φ ψ : ClosedFormula (WithParams Const)},
      (.or φ ψ : ClosedFormula (WithParams Const)) ∈
        ClosedTheorySet.provableClosure (Const := WithParams Const)
          (rawAlternatingLimit
            (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot) →
        φ ∈ ClosedTheorySet.provableClosure (Const := WithParams Const)
          (rawAlternatingLimit
            (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot) ∨
          ψ ∈ ClosedTheorySet.provableClosure (Const := WithParams Const)
            (rawAlternatingLimit
              (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot) := by
  intro φ ψ hOr
  rcases hOr with ⟨Γ, hΓ, d⟩
  obtain ⟨N, hN⟩ :=
    exists_stage_rawAlternatingLimit
      (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot Γ hΓ
  obtain ⟨n, hNn, hpair⟩ := hPairFair (φ, ψ) N
  have hOrN : Provable (Const := WithParams Const)
      (rawAlternatingApprox
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot N).theory
      (.or φ ψ) := ⟨Γ, hN, d⟩
  have hOrn : Provable (Const := WithParams Const)
      (rawAlternatingApprox
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot n).theory
      (.or (pairEnum n).1 (pairEnum n).2) := by
    have hMono : ∀ {ξ : ClosedFormula (WithParams Const)},
        ξ ∈ (rawAlternatingApprox
          (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot N).theory →
        ξ ∈ (rawAlternatingApprox
          (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot n).theory :=
      rawAlternatingApprox_mono
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot hNn
    have hLift : Provable (Const := WithParams Const)
        (rawAlternatingApprox
          (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot n).theory
        (.or φ ψ) :=
      provable_mono (Const := WithParams Const) hMono hOrN
    simpa [hpair] using hLift
  obtain ⟨δ, hδchoice, hδmem⟩ :=
    rawAlternatingApprox_or_branch_succ
      (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot n hOrn
  have hδlimit : δ ∈ rawAlternatingLimit
      (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot := by
    exact rawAlternatingApprox_subset_limit
      (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot (n + 1) hδmem
  rcases hδchoice with hδ | hδ
  · left
    rw [hpair] at hδ
    cases hδ
    exact ClosedTheorySet.subset_provableClosure
      (Const := WithParams Const)
      (rawAlternatingLimit
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot)
      hδlimit
  · right
    rw [hpair] at hδ
    cases hδ
    exact ClosedTheorySet.subset_provableClosure
      (Const := WithParams Const)
      (rawAlternatingLimit
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot)
      hδlimit

/-- The deductive-closure readout of the raw alternating limit has the
existential witness property when the body enumeration is fair. -/
theorem rawAlternatingLimit_exists_witness
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    {θ : ClosedFormula (WithParams Const)}
    (hT : AvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ T)
    (hBody : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hPair : FormulaPairAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ pairEnum)
    (hθ : FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ∀ {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
      (.ex φ : ClosedFormula (WithParams Const)) ∈
        ClosedTheorySet.provableClosure (Const := WithParams Const)
          (rawAlternatingLimit
            (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot) →
        ∃ t : ClosedTerm (WithParams Const) σ,
          instantiate (Base := Base) t φ ∈
            ClosedTheorySet.provableClosure (Const := WithParams Const)
              (rawAlternatingLimit
                (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot) := by
  intro σ φ hEx
  rcases hEx with ⟨Γ, hΓ, d⟩
  obtain ⟨N, hN⟩ :=
    exists_stage_rawAlternatingLimit
      (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot Γ hΓ
  have hExN : Provable (Const := WithParams Const)
      (rawAlternatingApprox
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot N).theory
      (.ex φ) := ⟨Γ, hN, d⟩
  obtain ⟨t, ht⟩ :=
    rawAlternatingApprox_exists_witness_succ
      (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot N hExN
  refine ⟨t, ?_⟩
  exact ClosedTheorySet.subset_provableClosure
    (Const := WithParams Const)
    (rawAlternatingLimit
      (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot)
    (rawAlternatingApprox_subset_limit
      (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot (N + 1) ht)

/-- The deductive closure of the alternating raw limit is a closed, consistent,
disjunction-prime, existentially witnessed extension that still omits the
target formula. -/
theorem exists_closed_witnessed_prime_rawAlternatingLimit_separating
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    (hPairFair : FormulaPairFairAfter (Base := Base) (Const := Const) pairEnum)
    {θ : ClosedFormula (WithParams Const)}
    (hT : AvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ T)
    (hBody : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hPair : FormulaPairAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ pairEnum)
    (hθ : FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ∃ U : ClosedTheorySet (WithParams Const),
      (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ U) ∧
      DeductivelyClosed (Const := WithParams Const) U ∧
      Consistent (Const := WithParams Const) U ∧
      (∀ {φ ψ : ClosedFormula (WithParams Const)},
        (.or φ ψ : ClosedFormula (WithParams Const)) ∈ U → φ ∈ U ∨ ψ ∈ U) ∧
      (∀ {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
        (.ex φ : ClosedFormula (WithParams Const)) ∈ U →
          ∃ t : ClosedTerm (WithParams Const) σ,
            instantiate (Base := Base) t φ ∈ U) ∧
      θ ∉ U := by
  let L : ClosedTheorySet (WithParams Const) :=
    rawAlternatingLimit
      (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot
  let U : ClosedTheorySet (WithParams Const) :=
    ClosedTheorySet.provableClosure (Const := WithParams Const) L
  refine ⟨U, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ψ hψ
    exact ClosedTheorySet.subset_provableClosure
      (Const := WithParams Const) L
      (subset_rawAlternatingLimit
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot hψ)
  · exact ClosedTheorySet.provableClosure_deductivelyClosed
      (Const := WithParams Const) L
  · exact ClosedTheorySet.provableClosure_consistent
      (Const := WithParams Const)
      (rawAlternatingLimit_consistent
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot)
  · intro φ ψ hOr
    exact rawAlternatingLimit_prime_or
      (Base := Base) (Const := Const) bodyEnum hfair pairEnum hPairFair hT hBody hPair hθ hNot hOr
  · intro σ φ hEx
    exact rawAlternatingLimit_exists_witness
      (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot hEx
  · exact ClosedTheorySet.not_mem_provableClosure_of_not_provable
      (Const := WithParams Const)
      (rawAlternatingLimit_omits
        (Base := Base) (Const := Const) bodyEnum hfair pairEnum hT hBody hPair hθ hNot)

/-- Read the alternating raw limit as a bare closed intuitionistic world.  This
does not assert that the resulting closed carrier has finite future support; use
the raw presentation, not the carrier, for freshness-sensitive arguments. -/
theorem exists_intuitionistic_world_rawAlternatingLimit_separating
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)}
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    (hPairFair : FormulaPairFairAfter (Base := Base) (Const := Const) pairEnum)
    {θ : ClosedFormula (WithParams Const)}
    (hT : AvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ T)
    (hBody : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) bodyEnum)
    (hPair : FormulaPairAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ pairEnum)
    (hθ : FormulaAvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ θ)
    (hNot : ¬ Provable (Const := WithParams Const) T θ) :
    ∃ W : IntuitionisticWorld (WithParams Const),
      (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ W.carrier) ∧
      θ ∉ W.carrier := by
  obtain ⟨U, hExt, hClosed, hCons, hPrime, hWitness, hOmit⟩ :=
    exists_closed_witnessed_prime_rawAlternatingLimit_separating
      (Base := Base) (Const := Const) bodyEnum hfair pairEnum hPairFair
      hT hBody hPair hθ hNot
  let W : IntuitionisticWorld (WithParams Const) :=
    { carrier := U
      closed := hClosed
      consistent := hCons
      prime_or := hPrime
      exists_witness := hWitness }
  refine ⟨W, ?_, ?_⟩
  · intro ψ hψ
    exact hExt hψ
  · exact hOmit

/-- A witness axiom inserted at layer `ℓ` does not mention parameters from any
different layer, provided its body does not. -/
theorem noConstOccurrence_param_pair_ne_witnessAxiom
    {σ ρ : Ty Base} {m ℓ k j : Nat} {φ : Formula (WithParams Const) [ρ]}
    (hm : m ≠ ℓ)
    (hφ : NoConstOccurrence (param σ (Nat.pair m k) : WithParams Const σ) φ) :
    NoConstOccurrence
      (param σ (Nat.pair m k) : WithParams Const σ)
      (witnessAxiom (param ρ (Nat.pair ℓ j)) φ) := by
  exact NoConstOccurrence.imp (NoConstOccurrence.ex hφ)
    (noConstOccurrence_instantiate
      (noConstOccurrence_param_pair_ne_const
        (Const := Const) (σ := σ) (ρ := ρ) (m := m) (ℓ := ℓ) (k := k) (j := j) hm)
      hφ)

/-- A witness axiom inserted at stage `s` of layer `ℓ` does not mention
parameters from a different stage `r` of the same layer, provided its body does
not. -/
theorem noConstOccurrence_param_stage_ne_witnessAxiom
    {σ ρ : Ty Base} {ℓ r s k j : Nat} {φ : Formula (WithParams Const) [ρ]}
    (hrs : r ≠ s)
    (hφ :
      NoConstOccurrence (param σ (Nat.pair ℓ (Nat.pair r k)) : WithParams Const σ) φ) :
    NoConstOccurrence
      (param σ (Nat.pair ℓ (Nat.pair r k)) : WithParams Const σ)
      (witnessAxiom (param ρ (Nat.pair ℓ (Nat.pair s j))) φ) := by
  exact NoConstOccurrence.imp (NoConstOccurrence.ex hφ)
    (noConstOccurrence_param_stage_ne_instantiate
      (Const := Const) (σ := σ) (ρ := ρ) (ℓ := ℓ) (r := r) (s := s)
      (k := k) (j := j) hrs hφ)

/-- A level-`ℓ` witness axiom preserves absence of all strictly higher layers. -/
theorem witnessAxiom_levelWitnessSupply_avoids_future_layers
    {ℓ n : Nat} {enum : Nat → Body Const}
    (hEnum : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) enum) :
    ∀ (σ : Ty Base) (m k : Nat), ℓ + 1 ≤ m →
      NoConstOccurrence (param σ (Nat.pair m k) : WithParams Const σ)
        (witnessAxiom
          (param (enum n).1 ((levelWitnessSupply ℓ).index
            (witnessIndex (witnessChainUsing (levelWitnessSupply ℓ) enum n) (enum n))))
          (enum n).2) := by
  intro σ m k hm
  refine noConstOccurrence_param_pair_ne_witnessAxiom
    (Const := Const) (σ := σ) (ρ := (enum n).1) (m := m) (ℓ := ℓ) (k := k)
    (j := witnessIndex (witnessChainUsing (levelWitnessSupply ℓ) enum n) (enum n))
    ?_ ?_
  · omega
  · exact hEnum n σ m k hm

/-- A witness axiom inserted at stage `s` of layer `ℓ` preserves absence of all
later stages in that same outer layer. -/
theorem witnessAxiom_stageWitnessSupply_avoids_future_stages
    {ℓ s n : Nat} {enum : Nat → Body Const}
    (hEnum : BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1) enum) :
    ∀ (σ : Ty Base) (r k : Nat), s + 1 ≤ r →
      NoConstOccurrence (param σ (Nat.pair ℓ (Nat.pair r k)) : WithParams Const σ)
        (witnessAxiom
          (param (enum n).1 ((stageWitnessSupply ℓ s).index
            (witnessIndex (witnessChainUsing (stageWitnessSupply ℓ s) enum n) (enum n))))
          (enum n).2) := by
  intro σ r k hrs
  refine noConstOccurrence_param_stage_ne_witnessAxiom
    (Const := Const) (σ := σ) (ρ := (enum n).1) (ℓ := ℓ) (r := r) (s := s)
    (k := k)
    (j := witnessIndex (witnessChainUsing (stageWitnessSupply ℓ s) enum n) (enum n))
    ?_ ?_
  · omega
  · exact hEnum n σ r k hrs

/-- Every axiom in a level-`ℓ` witness chain avoids strictly higher parameter
layers when the enumerated bodies do. -/
theorem witnessChainUsing_levelWitnessSupply_avoids_future_layers
    {ℓ : Nat} {enum : Nat → Body Const}
    (hEnum : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) enum) :
    ∀ n, ∀ {ψ : ClosedFormula (WithParams Const)},
      ψ ∈ witnessChainUsing (levelWitnessSupply ℓ) enum n →
        ∀ (σ : Ty Base) (m k : Nat), ℓ + 1 ≤ m →
          NoConstOccurrence (param σ (Nat.pair m k)) ψ := by
  intro n
  induction n with
  | zero =>
      intro ψ hψ
      simp [witnessChainUsing] at hψ
  | succ n ih =>
      intro ψ hψ σ m k hm
      rw [witnessChainUsing] at hψ
      rcases List.mem_cons.mp hψ with hhead | htail
      · subst hhead
        exact witnessAxiom_levelWitnessSupply_avoids_future_layers
          (Const := Const) (ℓ := ℓ) (n := n) (enum := enum) hEnum σ m k hm
      · exact ih htail σ m k hm

/-- Every axiom in a stage-`s` witness chain avoids later stages of the same
outer layer when the enumerated bodies do. -/
theorem witnessChainUsing_stageWitnessSupply_avoids_future_stages
    {ℓ s : Nat} {enum : Nat → Body Const}
    (hEnum : BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1) enum) :
    ∀ n, ∀ {ψ : ClosedFormula (WithParams Const)},
      ψ ∈ witnessChainUsing (stageWitnessSupply ℓ s) enum n →
        ∀ (σ : Ty Base) (r k : Nat), s + 1 ≤ r →
          NoConstOccurrence (param σ (Nat.pair ℓ (Nat.pair r k))) ψ := by
  intro n
  induction n with
  | zero =>
      intro ψ hψ
      simp [witnessChainUsing] at hψ
  | succ n ih =>
      intro ψ hψ σ r k hrs
      rw [witnessChainUsing] at hψ
      rcases List.mem_cons.mp hψ with hhead | htail
      · subst hhead
        exact witnessAxiom_stageWitnessSupply_avoids_future_stages
          (Const := Const) (ℓ := ℓ) (s := s) (n := n) (enum := enum)
          hEnum σ r k hrs
      · exact ih htail σ r k hrs

/-- The level-`ℓ` Henkin saturation of a theory that avoids all strictly higher
layers also avoids those layers.  This is a raw-theory support lemma; deductive
closures may contain theorems mentioning fresh constants. -/
theorem witnessLimitUsing_levelWitnessSupply_avoids_future_layers
    {ℓ : Nat} {T : ClosedTheorySet (WithParams Const)} {enum : Nat → Body Const}
    (hT : AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) T)
    (hEnum : BodyAvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1) enum) :
    AvoidsParamLayersFrom (Base := Base) (Const := Const) (ℓ + 1)
      (witnessLimitUsing (levelWitnessSupply ℓ) T enum) := by
  intro ψ hψ σ m k hm
  simp only [witnessLimitUsing, Set.mem_union, Set.mem_setOf_eq] at hψ
  rcases hψ with hψT | ⟨n, hψn⟩
  · exact hT ψ hψT σ m k hm
  · exact witnessChainUsing_levelWitnessSupply_avoids_future_layers
      (Const := Const) (ℓ := ℓ) (enum := enum) hEnum n hψn σ m k hm

/-- The stage-`s` Henkin saturation of a theory that avoids all later stages in
the same outer layer also avoids those later stages.  This is the support lemma
needed to keep an infinite construction below one outer level. -/
theorem witnessLimitUsing_stageWitnessSupply_avoids_future_stages
    {ℓ s : Nat} {T : ClosedTheorySet (WithParams Const)} {enum : Nat → Body Const}
    (hT : AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1) T)
    (hEnum : BodyAvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1) enum) :
    AvoidsParamStagesFrom (Base := Base) (Const := Const) ℓ (s + 1)
      (witnessLimitUsing (stageWitnessSupply ℓ s) T enum) := by
  intro ψ hψ σ r k hrs
  simp only [witnessLimitUsing, Set.mem_union, Set.mem_setOf_eq] at hψ
  rcases hψ with hψT | ⟨n, hψn⟩
  · exact hT ψ hψT σ r k hrs
  · exact witnessChainUsing_stageWitnessSupply_avoids_future_stages
      (Const := Const) (ℓ := ℓ) (s := s) (enum := enum) hEnum n hψn σ r k hrs

/-- A deductively closed world over the full `WithParams` signature cannot have a
carrier that avoids an entire parameter layer: equality reflexivity puts
`param σ (Nat.pair ℓ k) = param σ (Nat.pair ℓ k)` into the carrier. -/
theorem IntuitionisticWorld.not_avoids_param_layer
    (W : IntuitionisticWorld (WithParams Const)) (ℓ k : Nat) :
    ¬ AvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ W.carrier := by
  intro hAvoid
  let c : WithParams Const (.prop : Ty Base) := param .prop (Nat.pair ℓ k)
  let eqc : ClosedFormula (WithParams Const) := .eq (.const c) (.const c)
  have hEqMem : eqc ∈ W.carrier := by
    apply W.closed
    refine ⟨[], ?_, ?_⟩
    · intro ψ hψ
      cases hψ
    · exact ExtDerivation.eqRefl (.const c)
  have hNo : NoConstOccurrence c eqc := by
    simpa [c, eqc] using hAvoid eqc hEqMem .prop ℓ k (le_refl ℓ)
  exact noConstOccurrence_eq_self_const_false c hNo

/-- Even for a presented world whose raw base avoids future layers, the closed
carrier readout cannot itself avoid an entire parameter layer.  Freshness
arguments must therefore use `raw`, not `carrier`. -/
theorem PresentedIntuitionisticWorld.carrier_not_avoids_param_layer
    (W : PresentedIntuitionisticWorld Const) (ℓ k : Nat) :
    ¬ AvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ W.carrier := by
  exact IntuitionisticWorld.not_avoids_param_layer
    (Base := Base) (Const := Const) W.toIntuitionisticWorld ℓ k

/-- From a presented raw world and a raw-undivable target, the alternating
construction gives a bare closed intuitionistic successor readout.  The theorem
intentionally returns `IntuitionisticWorld`, not `PresentedIntuitionisticWorld`:
the alternating limit may use unbounded future layers, so finite support must
not be silently asserted. -/
theorem PresentedIntuitionisticWorld.exists_intuitionistic_successor_separating
    (W : PresentedIntuitionisticWorld Const)
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    (hPairFair : FormulaPairFairAfter (Base := Base) (Const := Const) pairEnum)
    {θ : ClosedFormula (WithParams Const)}
    (hBody : BodyAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (W.level + 1) bodyEnum)
    (hPair : FormulaPairAvoidsParamLayersFrom
      (Base := Base) (Const := Const) W.level pairEnum)
    (hθ : FormulaAvoidsParamLayersFrom
      (Base := Base) (Const := Const) W.level θ)
    (hNot : ¬ Provable (Const := WithParams Const) W.raw θ) :
    ∃ W' : IntuitionisticWorld (WithParams Const),
      (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ W.raw → ψ ∈ W'.carrier) ∧
      θ ∉ W'.carrier := by
  exact exists_intuitionistic_world_rawAlternatingLimit_separating
    (Base := Base) (Const := Const) (ℓ := W.level) (T := W.raw)
    bodyEnum hfair pairEnum hPairFair W.raw_avoids_future hBody hPair hθ hNot

/-- If an implication is absent from the closed carrier of a presented world,
then adding the antecedent to the raw base cannot derive the consequent. -/
theorem PresentedIntuitionisticWorld.not_provable_of_not_imp_mem
    (W : PresentedIntuitionisticWorld Const)
    {φ ψ : ClosedFormula (WithParams Const)}
    (hNotImp : (.imp φ ψ : ClosedFormula (WithParams Const)) ∉ W.carrier) :
    ¬ Provable (Const := WithParams Const) (insert φ W.raw) ψ := by
  intro hInsert
  have hImpRaw : Provable (Const := WithParams Const) W.raw (.imp φ ψ) :=
    provable_imp_of_insert (Const := WithParams Const) hInsert
  exact hNotImp hImpRaw

/-- Implication successor readout for the canonical truth lemma: if `φ → ψ` is
absent from a presented world's carrier, a bare intuitionistic successor extends
the raw base plus `φ` and still omits `ψ`. -/
theorem PresentedIntuitionisticWorld.exists_intuitionistic_successor_for_imp
    (W : PresentedIntuitionisticWorld Const)
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    (hPairFair : FormulaPairFairAfter (Base := Base) (Const := Const) pairEnum)
    {φ ψ : ClosedFormula (WithParams Const)}
    (hBody : BodyAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (W.level + 1) bodyEnum)
    (hPair : FormulaPairAvoidsParamLayersFrom
      (Base := Base) (Const := Const) W.level pairEnum)
    (hφ : FormulaAvoidsParamLayersFrom
      (Base := Base) (Const := Const) W.level φ)
    (hψ : FormulaAvoidsParamLayersFrom
      (Base := Base) (Const := Const) W.level ψ)
    (hNotImp : (.imp φ ψ : ClosedFormula (WithParams Const)) ∉ W.carrier) :
    ∃ W' : IntuitionisticWorld (WithParams Const),
      (∀ {χ : ClosedFormula (WithParams Const)}, χ ∈ W.raw → χ ∈ W'.carrier) ∧
      φ ∈ W'.carrier ∧
      ψ ∉ W'.carrier := by
  have hT : AvoidsParamLayersFrom
      (Base := Base) (Const := Const) W.level (insert φ W.raw) :=
    AvoidsParamLayersFrom.insert
      (Base := Base) (Const := Const) W.raw_avoids_future hφ
  have hNot : ¬ Provable (Const := WithParams Const) (insert φ W.raw) ψ :=
    PresentedIntuitionisticWorld.not_provable_of_not_imp_mem
      (Base := Base) (Const := Const) W hNotImp
  obtain ⟨W', hExt, hOmit⟩ :=
    exists_intuitionistic_world_rawAlternatingLimit_separating
      (Base := Base) (Const := Const) (ℓ := W.level) (T := insert φ W.raw)
      bodyEnum hfair pairEnum hPairFair hT hBody hPair hψ hNot
  refine ⟨W', ?_, ?_, hOmit⟩
  · intro χ hχ
    exact hExt (Set.mem_insert_of_mem φ hχ)
  · exact hExt (Set.mem_insert φ W.raw)

/-- A separating variant of `exists_witnessed_prime_extension`: if a formula is not
provable from the Henkin witness saturation, there is a witnessed prime extension
still omitting it. -/
theorem exists_witnessed_prime_extension_separatingUsing
    (supply : WitnessSupply)
    {T : ClosedTheorySet (WithParams Const)} (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    {θ : ClosedFormula (WithParams Const)}
    (hNot : ¬ Provable (Const := WithParams Const) (witnessLimitUsing supply T enum) θ) :
    ∃ U : ClosedTheorySet (WithParams Const),
      (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ witnessLimitUsing supply T enum → ψ ∈ U) ∧
      DeductivelyClosed (Const := WithParams Const) U ∧
      Consistent (Const := WithParams Const) U ∧
      (∀ {φ ψ : ClosedFormula (WithParams Const)},
        (.or φ ψ : ClosedFormula (WithParams Const)) ∈ U → φ ∈ U ∨ ψ ∈ U) ∧
      (∀ {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
        (.ex φ : ClosedFormula (WithParams Const)) ∈ U →
          ∃ t : ClosedTerm (WithParams Const) σ, instantiate (Base := Base) t φ ∈ U) ∧
      θ ∉ U := by
  obtain ⟨U, hExt, hClosed, hUcons, hPrime, hOmit⟩ :=
    exists_prime_extension_separating
      (Const := WithParams Const) (T := witnessLimitUsing supply T enum) (φ := θ) hNot
  refine ⟨U, hExt, hClosed, hUcons, hPrime, ?_, hOmit⟩
  intro σ φ hex
  obtain ⟨k, hax⟩ := exists_witnessAxiomUsing supply T enum ⟨σ, φ⟩ (henum ⟨σ, φ⟩)
  refine ⟨.const (param σ k), ?_⟩
  exact hClosed (provable_mp (provable_of_mem (Const := WithParams Const) (hExt hax))
    (provable_of_mem (Const := WithParams Const) hex))

/-- Identity-supply separating witnessed-prime extension. -/
theorem exists_witnessed_prime_extension_separating
    {T : ClosedTheorySet (WithParams Const)} (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    {θ : ClosedFormula (WithParams Const)}
    (hNot : ¬ Provable (Const := WithParams Const) (witnessLimit T enum) θ) :
    ∃ U : ClosedTheorySet (WithParams Const),
      (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ witnessLimit T enum → ψ ∈ U) ∧
      DeductivelyClosed (Const := WithParams Const) U ∧
      Consistent (Const := WithParams Const) U ∧
      (∀ {φ ψ : ClosedFormula (WithParams Const)},
        (.or φ ψ : ClosedFormula (WithParams Const)) ∈ U → φ ∈ U ∨ ψ ∈ U) ∧
      (∀ {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
        (.ex φ : ClosedFormula (WithParams Const)) ∈ U →
          ∃ t : ClosedTerm (WithParams Const) σ, instantiate (Base := Base) t φ ∈ U) ∧
      θ ∉ U := by
  exact exists_witnessed_prime_extension_separatingUsing
    identityWitnessSupply enum henum hNot

/-- A consistent parameter-free theory has an EM-free canonical world. -/
theorem exists_intuitionistic_worldUsing
    (supply : WitnessSupply)
    {T : ClosedTheorySet (WithParams Const)} (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) ψ) :
    ∃ W : IntuitionisticWorld (WithParams Const),
      ∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ W.carrier := by
  obtain ⟨U, hExt, hClosed, hUcons, hPrime, hWitness⟩ :=
    exists_witnessed_prime_extensionUsing (Base := Base) (Const := Const) supply
      enum henum hCons hT0
  refine ⟨?_, ?_⟩
  · exact
      { carrier := U
        closed := hClosed
        consistent := hUcons
        prime_or := hPrime
        exists_witness := hWitness }
  · intro ψ hψ
    exact hExt hψ

/-- Identity-supply EM-free canonical world. -/
theorem exists_intuitionistic_world
    {T : ClosedTheorySet (WithParams Const)} (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ) :
    ∃ W : IntuitionisticWorld (WithParams Const),
      ∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ W.carrier := by
  exact exists_intuitionistic_worldUsing identityWitnessSupply enum henum hCons hT0

/-- Level-supply EM-free canonical world.  The base theory only needs to avoid the
reserved parameter layer `ℓ`, not every parameter. -/
theorem exists_intuitionistic_worldAtLevel
    (ℓ : Nat) {T : ClosedTheorySet (WithParams Const)} (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : Consistent (Const := WithParams Const) T)
    (hTlevel : AvoidsParamLayersFrom (Base := Base) (Const := Const) ℓ T) :
    ∃ W : IntuitionisticWorld (WithParams Const),
      ∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ W.carrier := by
  refine exists_intuitionistic_worldUsing (Base := Base) (Const := Const)
    (levelWitnessSupply ℓ) enum henum hCons ?_
  intro ψ hψ σ k
  exact hTlevel ψ hψ σ ℓ k (le_refl ℓ)

/-- A consistent image of a level-restricted theory has an EM-free canonical
world using the matching level supply. -/
theorem exists_intuitionistic_world_of_levelTheory
    (ℓ : Nat) {T : ClosedTheorySet (LevelParams Const ℓ)} (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : Consistent (Const := WithParams Const) (mapLevelTheory ℓ T)) :
    ∃ W : IntuitionisticWorld (WithParams Const),
      ∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ mapLevelTheory ℓ T → ψ ∈ W.carrier := by
  exact exists_intuitionistic_worldAtLevel
    (Base := Base) (Const := Const) ℓ enum henum hCons
    (mapLevelTheory_avoids_future_layers (Base := Base) (Const := Const) ℓ T)

/-- Moving a level-restricted theory to a larger level preserves the global
canonical-world existence statement. -/
theorem exists_intuitionistic_world_of_castLevelTheory
    {ℓ ℓ' : Nat} (hℓ : ℓ ≤ ℓ') {T : ClosedTheorySet (LevelParams Const ℓ)}
    (enum : Nat → Body Const) (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : Consistent (Const := WithParams Const) (mapLevelTheory ℓ T)) :
    ∃ W : IntuitionisticWorld (WithParams Const),
      ∀ {ψ : ClosedFormula (WithParams Const)},
        ψ ∈ mapLevelTheory ℓ' (castLevelTheory hℓ T) → ψ ∈ W.carrier := by
  have hCons' : Consistent (Const := WithParams Const)
      (mapLevelTheory (Base := Base) (Const := Const) ℓ' (castLevelTheory hℓ T)) := by
    exact (consistent_mapLevelTheory_castLevelTheory_iff
      (Base := Base) (Const := Const) hℓ T).2 hCons
  exact exists_intuitionistic_world_of_levelTheory
    (Base := Base) (Const := Const) ℓ' enum henum hCons'

/-- Successor-level form of `exists_intuitionistic_world_of_castLevelTheory`. -/
theorem exists_intuitionistic_world_of_castLevelTheorySucc
    (ℓ : Nat) {T : ClosedTheorySet (LevelParams Const ℓ)}
    (enum : Nat → Body Const) (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : Consistent (Const := WithParams Const) (mapLevelTheory ℓ T)) :
    ∃ W : IntuitionisticWorld (WithParams Const),
      ∀ {ψ : ClosedFormula (WithParams Const)},
        ψ ∈ mapLevelTheory (ℓ + 1) (castLevelTheorySucc ℓ T) → ψ ∈ W.carrier :=
  exists_intuitionistic_world_of_castLevelTheory
    (Base := Base) (Const := Const) (Nat.le_succ ℓ) enum henum hCons

/-- If a global intuitionistic world extends a level-image theory, that theory
has a successor-level witnessed world after casting the level signature. -/
theorem exists_successor_intuitionistic_world_of_subset
    (ℓ : Nat) {T : ClosedTheorySet (LevelParams Const ℓ)}
    (W : IntuitionisticWorld (WithParams Const))
    (hSub : ∀ {ψ : ClosedFormula (WithParams Const)},
      ψ ∈ mapLevelTheory (Base := Base) (Const := Const) ℓ T → ψ ∈ W.carrier)
    (enum : Nat → Body Const) (henum : ∀ b : Body Const, ∃ n, enum n = b) :
    ∃ W' : IntuitionisticWorld (WithParams Const),
      ∀ {ψ : ClosedFormula (WithParams Const)},
        ψ ∈ mapLevelTheory (Base := Base) (Const := Const) (ℓ + 1)
            (castLevelTheorySucc (Base := Base) (Const := Const) ℓ T) →
          ψ ∈ W'.carrier := by
  have hCons : Consistent (Const := WithParams Const)
      (mapLevelTheory (Base := Base) (Const := Const) ℓ T) :=
    IntuitionisticWorld.consistent_of_subset (W := W) hSub
  exact exists_intuitionistic_world_of_castLevelTheorySucc
    (Base := Base) (Const := Const) ℓ enum henum hCons

/-- Separating EM-free canonical world, packaged behind the new interface. -/
theorem exists_intuitionistic_world_separatingUsing
    (supply : WitnessSupply)
    {T : ClosedTheorySet (WithParams Const)} (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    {θ : ClosedFormula (WithParams Const)}
    (hNot : ¬ Provable (Const := WithParams Const) (witnessLimitUsing supply T enum) θ) :
    ∃ W : IntuitionisticWorld (WithParams Const),
      (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ witnessLimitUsing supply T enum → ψ ∈ W.carrier) ∧
      θ ∉ W.carrier := by
  obtain ⟨U, hExt, hClosed, hUcons, hPrime, hWitness, hOmit⟩ :=
    exists_witnessed_prime_extension_separatingUsing (Base := Base) (Const := Const) supply
      enum henum hNot
  refine ⟨?_, ?_, ?_⟩
  · exact
      { carrier := U
        closed := hClosed
        consistent := hUcons
        prime_or := hPrime
        exists_witness := hWitness }
  · intro ψ hψ
    exact hExt hψ
  · exact hOmit

/-- Identity-supply separating EM-free canonical world. -/
theorem exists_intuitionistic_world_separating
    {T : ClosedTheorySet (WithParams Const)} (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    {θ : ClosedFormula (WithParams Const)}
    (hNot : ¬ Provable (Const := WithParams Const) (witnessLimit T enum) θ) :
    ∃ W : IntuitionisticWorld (WithParams Const),
      (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ witnessLimit T enum → ψ ∈ W.carrier) ∧
      θ ∉ W.carrier := by
  exact exists_intuitionistic_world_separatingUsing identityWitnessSupply enum henum hNot

/-- Level-supply separating EM-free canonical world, with the theorem stated over
the supplied saturation generated from layer `ℓ`. -/
theorem exists_intuitionistic_world_separatingAtLevel
    (ℓ : Nat) {T : ClosedTheorySet (WithParams Const)} (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    {θ : ClosedFormula (WithParams Const)}
    (hNot : ¬ Provable (Const := WithParams Const)
      (witnessLimitUsing (levelWitnessSupply ℓ) T enum) θ) :
    ∃ W : IntuitionisticWorld (WithParams Const),
      (∀ {ψ : ClosedFormula (WithParams Const)},
        ψ ∈ witnessLimitUsing (levelWitnessSupply ℓ) T enum → ψ ∈ W.carrier) ∧
      θ ∉ W.carrier := by
  exact exists_intuitionistic_world_separatingUsing
    (levelWitnessSupply ℓ) enum henum hNot

/-- Raw universal-case separation seed for presented worlds.  If `∀x.φ` is
absent from the closed carrier, then a parameter from any future layer gives an
instance not provable from the raw base. -/
theorem PresentedIntuitionisticWorld.not_provable_fresh_instance_of_not_all_mem
    (W : PresentedIntuitionisticWorld Const)
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    {m k : Nat} (hm : W.level ≤ m)
    (hφfresh :
      NoConstOccurrence (param σ (Nat.pair m k) : WithParams Const σ) φ)
    (hNotAll : (.all φ : ClosedFormula (WithParams Const)) ∉ W.carrier) :
    ¬ Provable (Const := WithParams Const) W.raw
        (instantiate (Base := Base) (.const (param σ (Nat.pair m k))) φ) := by
  intro hInst
  have hAllRaw : Provable (Const := WithParams Const) W.raw (.all φ) :=
    provable_all_intro_fresh
      (Const := WithParams Const) (T := W.raw)
      (c := param σ (Nat.pair m k))
      (by
        intro ψ hψ
        exact W.raw_avoids_future ψ hψ σ m k hm)
      hφfresh hInst
  exact hNotAll hAllRaw

/-- Presented-world universal successor readout with witness repair.  A failed
universal in the carrier yields a future-layer parameter instance omitted by a
closed, consistent, witnessed extension of the raw base.  Disjunction primeness
is supplied by the later alternating construction. -/
theorem PresentedIntuitionisticWorld.exists_closed_witnessed_omitting_fresh_instance
    (W : PresentedIntuitionisticWorld Const)
    (enum : Nat → Body Const) (hfair : BodyFairAfter (Const := Const) enum)
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    {m k : Nat} (hm : W.level ≤ m)
    (hφfresh :
      NoConstOccurrence (param σ (Nat.pair m k) : WithParams Const σ) φ)
    (hφfuture :
      ∀ (τ : Ty Base) (j : Nat),
        NoConstOccurrence
          (param τ ((levelWitnessSupply (m + 1)).index j) : WithParams Const τ) φ)
    (hNotAll : (.all φ : ClosedFormula (WithParams Const)) ∉ W.carrier) :
    ∃ U : ClosedTheorySet (WithParams Const),
      (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ W.raw → ψ ∈ U) ∧
      DeductivelyClosed (Const := WithParams Const) U ∧
      Consistent (Const := WithParams Const) U ∧
      (∀ {ρ : Ty Base} {χ : Formula (WithParams Const) [ρ]},
        (.ex χ : ClosedFormula (WithParams Const)) ∈ U →
          ∃ t : ClosedTerm (WithParams Const) ρ,
            instantiate (Base := Base) t χ ∈ U) ∧
      instantiate (Base := Base) (.const (param σ (Nat.pair m k))) φ ∉ U := by
  let θ : ClosedFormula (WithParams Const) :=
    instantiate (Base := Base) (.const (param σ (Nat.pair m k))) φ
  have hNotθ : ¬ Provable (Const := WithParams Const) W.raw θ :=
    PresentedIntuitionisticWorld.not_provable_fresh_instance_of_not_all_mem
      (Base := Base) (Const := Const) W hm hφfresh hNotAll
  have hRawFuture : ∀ ψ ∈ W.raw, ∀ (τ : Ty Base) (j : Nat),
      NoConstOccurrence (param τ ((levelWitnessSupply (m + 1)).index j)) ψ := by
    intro ψ hψ τ j
    exact W.raw_avoids_future ψ hψ τ (m + 1) j (Nat.le_succ_of_le hm)
  have hθFuture : ∀ (τ : Ty Base) (j : Nat),
      NoConstOccurrence
        (param τ ((levelWitnessSupply (m + 1)).index j) : WithParams Const τ) θ := by
    intro τ j
    exact noConstOccurrence_param_pair_ne_instantiate
      (Const := Const) (σ := τ) (ρ := σ) (m := m + 1) (ℓ := m) (k := j) (j := k)
      (by omega)
      (hφfuture τ j)
  exact exists_closed_witnessed_instanceLimit_separating
    (Base := Base) (Const := Const) (levelWitnessSupply (m + 1))
    (T₀ := W.raw) enum hfair hNotθ hRawFuture hθFuture

/-- Universal successor readout for the canonical truth lemma: if `∀x.φ` is
absent from a presented world's carrier, a bare intuitionistic successor omits
a fresh parameter instance from layer `m`.  The alternating construction starts
at layer `m+1`, so the omitted instance itself is allowed while later reserved
layers remain fresh. -/
theorem PresentedIntuitionisticWorld.exists_intuitionistic_successor_for_all
    (W : PresentedIntuitionisticWorld Const)
    (bodyEnum : Nat → Body Const)
    (hfair : BodyFairAfter (Const := Const) bodyEnum)
    (pairEnum : Nat → ClosedFormulaPair Const)
    (hPairFair : FormulaPairFairAfter (Base := Base) (Const := Const) pairEnum)
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    {m k : Nat} (hm : W.level ≤ m)
    (hBody : BodyAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 2) bodyEnum)
    (hPair : FormulaPairAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) pairEnum)
    (hφfresh :
      NoConstOccurrence (param σ (Nat.pair m k) : WithParams Const σ) φ)
    (hφfuture :
      ∀ (τ : Ty Base) (r j : Nat), m + 1 ≤ r →
        NoConstOccurrence (param τ (Nat.pair r j) : WithParams Const τ) φ)
    (hNotAll : (.all φ : ClosedFormula (WithParams Const)) ∉ W.carrier) :
    ∃ W' : IntuitionisticWorld (WithParams Const),
      (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ W.raw → ψ ∈ W'.carrier) ∧
      instantiate (Base := Base) (.const (param σ (Nat.pair m k))) φ ∉ W'.carrier := by
  let θ : ClosedFormula (WithParams Const) :=
    instantiate (Base := Base) (.const (param σ (Nat.pair m k))) φ
  have hRawFuture : AvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) W.raw := by
    exact AvoidsParamLayersFrom.mono
      (Base := Base) (Const := Const) (Nat.le_succ_of_le hm) W.raw_avoids_future
  have hθFuture : FormulaAvoidsParamLayersFrom
      (Base := Base) (Const := Const) (m + 1) θ := by
    intro τ r j hmr
    exact noConstOccurrence_param_pair_ne_instantiate
      (Const := Const) (σ := τ) (ρ := σ) (m := r) (ℓ := m) (k := j) (j := k)
      (by omega)
      (hφfuture τ r j hmr)
  have hNotθ : ¬ Provable (Const := WithParams Const) W.raw θ :=
    PresentedIntuitionisticWorld.not_provable_fresh_instance_of_not_all_mem
      (Base := Base) (Const := Const) W hm hφfresh hNotAll
  exact exists_intuitionistic_world_rawAlternatingLimit_separating
    (Base := Base) (Const := Const) (ℓ := m + 1) (T := W.raw)
    bodyEnum hfair pairEnum hPairFair hRawFuture hBody hPair hθFuture hNotθ

end ClosedTheorySet

end Mettapedia.Logic.HOL
