import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.Hazards
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.Tower
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ModelS.Fundamental
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ModelS.CodeConstants

/-!
# The normalization model rejects a code destructor

A trusted destructor `pred (all f) ⟶ f` of the quantifier over codes gives a typed code that
is not strongly normalizing. So no model S whose realizer side is the package with the
destructor is sound for it: soundness makes every term typed in a formed context strongly
normalizing, and the loop `Ω = pred ω ω`, with `ω = all (λx. pred x x)`, is typed in the
empty context (`not_soundS`).

The failure lies in the destructor's own obligation. A realizer of a code is a term whose
decoding is strongly normalizing, and nothing more is asked of it. The code `ω` is one: its
decoding unfolds to `Π (x : prop). holds (pred x x)`, where `pred x x` is stuck on the
variable. A realizer of a meaning of `prop → prop → prop` sends two realizers of codes to a
realizer of codes, so the destructor would send `ω` and `ω` to `pred ω ω = Ω`, which is not
strongly normalizing (`pred_not_real`). Hence in any model S whose value side reads `prop`
as its type of codes the destructor is not a valid term of its declared type
(`pred_not_valid`).

Every other obligation can be met. The package has a model S, over the skeleton-free value
side, whose value side computes the destructor, keeps the decoder rigid and reads
implication and the quantifier as constructors, and whose realizer side is the package
under its own reduction. Its laws hold, its codes are read, every root step of the package
preserves meaning, the destructor's own step included since the value side computes it,
and every code constant is a valid term of its declared type. So soundness of the package
for this model is equivalent to the validity of the destructor alone
(`destructorModel_soundS_iff`), and it fails there (`destructorModel_not_soundS`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Hazards

open Normalization
open Consistency (Carrier Kind Model CodesRead World Truth Morph)
open Realizability
open StrongNormalization
open TelescopeAbstraction (subst_empty)

/-! ## No sound model -/

/-- **No model S is sound for a code destructor.** A model whose realizer side is
the package with the destructor would make the typed loop `Ω` strongly
normalizing. -/
theorem not_soundS {L : Type} [UniverseLevel.LevelOrder L] (M : ModelS.SModel Tower.Head L)
    (realizers : M.realizers.rules = withDestructor) : ¬ ModelS.TypedSoundS withDestructor M := by
  intro sound
  have sn := (ModelS.Typed.sn sound .nil (Omega_typed (Γ := .nil))).1
  rw [realizers] at sn
  exact Omega_not_sn sn

/-! ## The root steps of the package with the destructor -/

/-- The quantifier over codes is the package's only quantifier instance, over codes. -/
theorem quantifiers_some {a : DeclName} {T : Tower.Tm 0} (found : codes.quantifiers a = some T) :
    a = allName ∧ T = codes.propT := by
  change List.lookup a [(allName, .const codes.prop)] = some T at found
  unfold List.lookup at found
  cases e : a == allName with
  | false =>
      rw [e] at found
      cases found
  | true =>
      rw [e] at found
      cases found
      exact ⟨eq_of_beq e, rfl⟩

/-- The root steps of the package with the destructor: decoding an implication, decoding a
quantification, and the destructor at a quantified code. -/
theorem root_cases {n : Nat} {t u : Tower.Tm n} (step : withDestructor.computation.step t u) :
    (∃ p q, t = codes.holdsOf (codes.impOf p q)) ∨
      (∃ f, t = codes.holdsOf (.app (.const allName) f) ∧
        u = .pi codes.propT (codes.holdsOf (.app (Presentation.rename wk f) (.var 0)))) ∨
      ∃ f, t = .app (.const predName) (.app (.const allName) f) ∧ u = f := by
  rcases step with (step | step) | step
  · exact step.elim
  · cases step with
    | imp p q => exact .inl ⟨p, q, rfl⟩
    | all carrier f =>
        obtain ⟨rfl, rfl⟩ := quantifiers_some carrier
        exact .inr (.inl ⟨f, rfl, rfl⟩)
    | eq carrier => cases carrier
  · cases step with
    | mk => exact .inr (.inr ⟨_, rfl, rfl⟩)

/-- Every root step occurs at a spine of a constant. -/
theorem spineHeaded : SpineHeaded withDestructor := by
  intro n t u step
  rcases root_cases step with ⟨p, q, rfl⟩ | ⟨f, rfl, -⟩ | ⟨f, rfl, -⟩
  · exact ⟨codes.holds, [codes.impOf p q], rfl⟩
  · exact ⟨codes.holds, [.app (.const allName) f], rfl⟩
  · exact ⟨predName, [.app (.const allName) f], rfl⟩

/-! ## Normal forms -/

theorem const_normal {n : Nat} (c : DeclName) (u : Tower.Tm n) :
    ¬ StrongNormalization.Reduces withDestructor (.const c) u := by
  intro step
  cases step with
  | root r => rcases root_cases r with ⟨_, _, e⟩ | ⟨_, e, -⟩ | ⟨_, e, -⟩ <;> cases e

theorem var_normal {n : Nat} (i : Fin n) (u : Tower.Tm n) :
    ¬ StrongNormalization.Reduces withDestructor (.var i) u := by
  intro step
  cases step with
  | root r => rcases root_cases r with ⟨_, _, e⟩ | ⟨_, e, -⟩ | ⟨_, e, -⟩ <;> cases e

/-- The destructor applied to a variable is stuck. -/
theorem predVar_normal {n : Nat} (i : Fin n) (u : Tower.Tm n) :
    ¬ StrongNormalization.Reduces withDestructor (.app (.const predName) (.var i)) u := by
  intro step
  cases step with
  | root r =>
      rcases root_cases r with ⟨_, _, e⟩ | ⟨_, e, -⟩ | ⟨_, e, -⟩
      · exact absurd (Tm.const.inj (Tm.app.inj e).1) (by decide)
      · exact absurd (Tm.const.inj (Tm.app.inj e).1) (by decide)
      · cases e
  | congAppFun s => exact const_normal _ _ s
  | congAppArg s => exact var_normal _ _ s

/-- `pred x y` is stuck for variables `x` and `y`. -/
theorem predVarVar_normal {n : Nat} (i j : Fin n) (u : Tower.Tm n) :
    ¬ StrongNormalization.Reduces withDestructor
      (.app (.app (.const predName) (.var i)) (.var j)) u := by
  intro step
  cases step with
  | root r => rcases root_cases r with ⟨_, _, e⟩ | ⟨_, e, -⟩ | ⟨_, e, -⟩ <;> cases e
  | congAppFun s => exact predVar_normal _ _ s
  | congAppArg s => exact var_normal _ _ s

/-- `holds (pred x y)` is normal for variables `x` and `y`: the stuck code does not
decode. -/
theorem holdsPred_normal {n : Nat} (i j : Fin n) (u : Tower.Tm n) :
    ¬ StrongNormalization.Reduces withDestructor
      (codes.holdsOf (.app (.app (.const predName) (.var i)) (.var j))) u := by
  intro step
  cases step with
  | root r =>
      rcases root_cases r with ⟨_, _, e⟩ | ⟨_, e, -⟩ | ⟨_, e, -⟩
      · exact absurd (Tm.const.inj (Tm.app.inj (Tm.app.inj (Tm.app.inj e).2).1).1) (by decide)
      · cases e
      · exact absurd (Tm.const.inj (Tm.app.inj e).1) (by decide)
  | congAppFun s => exact const_normal _ _ s
  | congAppArg s => exact predVarVar_normal _ _ _ s

/-- `ω` is normal. -/
theorem omega_normal {n : Nat} (u : Tower.Tm n) :
    ¬ StrongNormalization.Reduces withDestructor omega u := by
  intro step
  cases step with
  | root r =>
      rcases root_cases r with ⟨_, _, e⟩ | ⟨_, e, -⟩ | ⟨_, e, -⟩
      · exact absurd (Tm.const.inj (Tm.app.inj e).1) (by decide)
      · exact absurd (Tm.const.inj (Tm.app.inj e).1) (by decide)
      · exact absurd (Tm.const.inj (Tm.app.inj e).1) (by decide)
  | congAppFun s => exact const_normal _ _ s
  | congAppArg s =>
      cases s with
      | root r => rcases root_cases r with ⟨_, _, e⟩ | ⟨_, e, -⟩ | ⟨_, e, -⟩ <;> cases e
      | congLam s => exact predVarVar_normal _ _ _ s

/-! ## `ω` realizes a code -/

/-- The decoding of the family of `ω` at a variable is strongly normalizing: one β-step
leads to the normal `holds (pred x x)`. -/
theorem holdsBeta_sn {n : Nat} (i : Fin n) :
    SN withDestructor
      (codes.holdsOf (.app (.lam (.app (.app (.const predName) (.var 0)) (.var 0))) (.var i))) := by
  refine SN.intro fun u step => ?_
  cases step with
  | root r =>
      rcases root_cases r with ⟨_, _, e⟩ | ⟨_, e, -⟩ | ⟨_, e, -⟩
      · cases e
      · cases e
      · exact absurd (Tm.const.inj (Tm.app.inj e).1) (by decide)
  | congAppFun s => exact (const_normal _ _ s).elim
  | congAppArg s =>
      cases s with
      | betaPi => exact SN.intro fun v step => (holdsPred_normal i i v step).elim
      | root r => rcases root_cases r with ⟨_, _, e⟩ | ⟨_, e, -⟩ | ⟨_, e, -⟩ <;> cases e
      | congAppFun s =>
          cases s with
          | root r => rcases root_cases r with ⟨_, _, e⟩ | ⟨_, e, -⟩ | ⟨_, e, -⟩ <;> cases e
          | congLam s => exact (predVarVar_normal _ _ _ s).elim
      | congAppArg s => exact (var_normal _ _ s).elim

/-- The decoding of `ω` is strongly normalizing: it unfolds to
`Π (x : prop). holds ((λx. pred x x) x)`. -/
theorem omega_decoding_sn {n : Nat} : SN withDestructor (codes.holdsOf (omega : Tower.Tm n)) := by
  refine SN.intro fun u step => ?_
  cases step with
  | root r =>
      rcases root_cases r with ⟨_, _, e⟩ | ⟨f, e, rfl⟩ | ⟨_, e, -⟩
      · cases e
      · cases e
        exact SN.pi spineHeaded (SN.intro fun v step => (const_normal _ _ step).elim)
          (holdsBeta_sn 0)
      · exact absurd (Tm.const.inj (Tm.app.inj e).1) (by decide)
  | congAppFun s => exact (const_normal _ _ s).elim
  | congAppArg s => exact (omega_normal _ s).elim

/-! ## Realizers of codes -/

/-- The decoder of a realizer side whose reduction is the package with the destructor is
the package's decoder: its decoding of an implication is a root step of the package. -/
theorem decoder_holds (T : Realizers Tower.Head) (rules : T.rules = withDestructor) :
    T.decoders.holds = codes.holds := by
  have step := T.decodes (DecoderStep.imp (n := 0) (.const allName) (.const allName))
  rw [rules] at step
  rcases root_cases step with ⟨_, _, e⟩ | ⟨_, e, -⟩ | ⟨_, e, -⟩
  · exact Tm.const.inj (Tm.app.inj e).1
  · exact Tm.const.inj (Tm.app.inj e).1
  · exact nomatch (Tm.app.inj e).2

/-- `ω = all (λx. pred x x)` realizes a code: its decoding is strongly normalizing. -/
theorem codes_mem_omega (T : Realizers Tower.Head) (rules : T.rules = withDestructor)
    {n : Nat} : T.codes.mem (omega : Tower.Tm n) := by
  show SN T.rules (.app (.const T.decoders.holds) omega)
  rw [rules, decoder_holds T rules]
  exact omega_decoding_sn

/-- `Ω = pred ω ω` realizes no code: realizers are strongly normalizing. -/
theorem not_codes_mem_Omega (T : Realizers Tower.Head) (rules : T.rules = withDestructor)
    {n : Nat} : ¬ T.codes.mem (Omega : Tower.Tm n) := by
  intro mem
  have sn : SN T.rules (Omega : Tower.Tm n) := T.codes.sn mem
  rw [rules] at sn
  exact Omega_not_sn sn

/-! ## The destructor's obligation -/

/-- **The destructor realizes no meaning of `prop → prop → prop`**, over any
setting, daimon and realizer side whose reduction is the package with the
destructor. Such a realizer sends the realizers `ω` and `ω` of codes to a realizer
of codes, while `pred ω ω = Ω` is not strongly normalizing. -/
theorem pred_not_real (S : Consistency.Setting Tower.Head) (star : DeclName)
    (T : Realizers Tower.Head) (realizers : T.rules = withDestructor)
    (φ : (Carrier.arr .prop (.arr .prop .prop) : Carrier .gen).V (candidateReading S star T)) :
    ¬ (Real S star T (.arr .prop (.arr .prop .prop)) φ).mem (.const predName : Tower.Tm 0) := by
  intro real
  have code := codes_mem_omega T realizers (n := 0)
  exact not_codes_mem_Omega T realizers (real T.sn idRen omega code T.sn idRen omega code)

/-- **The destructor is not a valid term of its declared type** in any model S
whose realizer side is the package with the destructor and whose value side
reads `prop` as its type of codes. The type `prop → prop → prop` is interpreted
by the pack of its carrier; with the daimon as the value of both arguments, a
realizer of that pack sends two realizers of codes to a realizer of codes,
while `ω` realizes a code and `pred ω ω` does not. -/
theorem pred_not_valid {L : Type} [UniverseLevel.LevelOrder L]
    (M : ModelS.SModel Tower.Head L) (laws : M.Laws)
    (realizers : M.realizers.rules = withDestructor) (prop : codes.prop = M.prop) :
    ¬ ModelS.ValidTmS M .nil (.const predName) predType := by
  intro valid
  have form : predType = (Carrier.arr .prop (.arr .prop .prop) : Carrier .gen).term M.toModel := by
    rw [show predType = .pi (.const codes.prop) (.pi (.const codes.prop) (.const codes.prop))
      from rfl, prop]
    rfl
  let empty : Sub Tower.Head 0 0 := fun i => Fin.elim0 i
  have den : ValueSide.DenS M.value World.closed (Presentation.subst empty predType)
      (ValueSide.carrierPack M.value (.arr .prop (.arr .prop .prop)) World.closed) := by
    rw [subst_empty, form]
    exact ⟨UniverseLevel.LevelOrder.bot,
      ValueSide.carrier_interp laws.value (.arr .prop (.arr .prop .prop)) World.closed⟩
  have real := (valid.2 (σ' := empty) (ς := empty) trivial den).2
  have daimon : Truth M.reading World.closed (.const M.star : Tower.Tm 0)
      M.reading.neutralMeaning :=
    .neutral .refl .star
  have starVal : (ValueSide.propPack M.value World.closed).Val (.const M.star) :=
    ⟨_, daimon, daimon⟩
  obtain ⟨-, outer⟩ := (ModelS.PiPack.mem_real _).mp real
  have first := outer (Morph.id World.closed) (a := .const M.star) starVal idRen omega
    (codes_mem_omega M.realizers realizers)
  obtain ⟨-, inner⟩ := (ModelS.PiPack.mem_real _).mp first
  exact not_codes_mem_Omega M.realizers realizers (inner (Morph.id World.closed)
    (a := .const M.star) starVal idRen omega (codes_mem_omega M.realizers realizers))

/-! ## A model in which only the destructor's obligation fails -/

/-- The type of numbers the laws of the value side ask for. The package does not declare
it. -/
def numName : DeclName := `hazard.num

/-- The constructor `zero` of the numbers. -/
def zeroName : DeclName := `hazard.zero

/-- The constructor `suc` of the numbers. -/
def sucName : DeclName := `hazard.suc

/-- The daimon: a fresh rigid constant of the value side. -/
def daimonName : DeclName := `hazard.daimon

/-! ### The value side -/

/-- The value side's reduction: the tower with the destructor computing. -/
def valueRules : Rules Tower.Head :=
  { Tower.rules with computation := destructorComputation predName allName }

/-- The roles of the value side: the destructor computes at the quantified code,
implication and the quantifier are constructors, the numbers are an inductive type with
constructors `zero` and `suc`, and every other name is rigid, the decoder included. -/
def valueRoles : Roles Tower.Head := fun name =>
  if name = predName then .computes 1 (.split 0 .constructor fun _ => .leaf)
  else if name = codes.imp then .constructor 2
  else if name = allName then .constructor 1
  else if name = numName then .inductive [(zeroName, []), (sucName, [.recursive])]
  else if name = zeroName then .constructor 0
  else if name = sucName then .constructor 1
  else .rigid

/-- The quantifier ranges over the carrier of codes. -/
def valueAllCarrier (name : DeclName) : Option (Σ k, Carrier k) :=
  if name = allName then some ⟨.gen, .prop⟩ else none

theorem valueAllCarrier_some {a : DeclName} {A : Σ k, Carrier k}
    (found : valueAllCarrier a = some A) : a = allName := by
  unfold valueAllCarrier at found
  by_cases e : a = allName
  · exact e
  · rw [if_neg e] at found
    cases found

/-- The tower's levels, for the value side's reduction. -/
def valueLevels : LevelModel valueRules ℕ where
  level := (TowerModel.levels fun _ => 0).level
  successor := (TowerModel.levels fun _ => 0).successor
  universe_typing := (TowerModel.levels fun _ => 0).universe_typing
  ground_typing := (TowerModel.levels fun _ => 0).ground_typing
  cumulative_universe := (TowerModel.levels fun _ => 0).cumulative_universe
  headEq_level := (TowerModel.levels fun _ => 0).headEq_level
  join_level := (TowerModel.levels fun _ => 0).join_level
  join_exists := (TowerModel.levels fun _ => 0).join_exists
  join_upper := (TowerModel.levels fun _ => 0).join_upper
  cumulative_refl := (TowerModel.levels fun _ => 0).cumulative_refl
  headEq_symm := (TowerModel.levels fun _ => 0).headEq_symm
  headEq_trans := (TowerModel.levels fun _ => 0).headEq_trans
  universe_decided := (TowerModel.levels fun _ => 0).universe_decided

/-- The value side: the tower with the destructor computing, read with the package's codes
and fresh numbers. -/
def valueModel : Model Tower.Head ℕ where
  rules := valueRules
  roles := valueRoles
  zero := zeroName
  suc := sucName
  imp := codes.imp
  allCarrier := valueAllCarrier
  eqCarrier := fun _ => none
  num := numName
  prop := codes.prop
  holds := codes.holds
  levels := valueLevels

theorem valueModel_laws : valueModel.Laws where
  truth :=
    { shape := ⟨fun step => destructor_spine rfl rfl step,
        fun step step' => destructor_deterministic step' step⟩
      zero := rfl
      suc := rfl
      imp := rfl
      all := fun found => by
        obtain rfl := valueAllCarrier_some found
        rfl
      eq := fun found => by cases found
      impNotEq := rfl }
  num := rfl
  prop := rfl
  holds := rfl

/-! ### The realizer side -/

/-- The roles of the realizer side: the decoder and the destructor each compute at one
argument, the code, and the code constructors and the numerals are constructors. -/
def realizerRoles : Roles Tower.Head := fun name =>
  if name = codes.holds then .computes 1 (.split 0 .constructor fun _ => .leaf)
  else if name = predName then .computes 1 (.split 0 .constructor fun _ => .leaf)
  else if name = codes.imp then .constructor 2
  else if name = allName then .constructor 1
  else if name = zeroName then .constructor 0
  else if name = sucName then .constructor 1
  else .rigid

theorem realizerRoles_prop : realizerRoles codes.prop = .rigid := rfl

theorem realizerDecoderRoles : DecoderRoles realizerRoles codes.decoders where
  holds := rfl
  imp := rfl
  all := fun found => by
    obtain ⟨rfl, -⟩ := quantifiers_some found
    rfl
  eq := fun found => by cases found

/-- No term is both a decoding redex and a destructor redex: they are headed by different
constants. -/
theorem decoding_not_destructing {n : Nat} {t u u' : Tower.Tm n}
    (decoding : DecoderStep codes.decoders t u)
    (destructing : DestructorStep predName allName t u') : False := by
  obtain ⟨args, e⟩ := decoderComputation_headed codes.decoders decoding
  cases destructing
  exact absurd (appSpine_const_injective (as := [_]) e).1 (by decide)

/-- The package with the destructor has root shape under the realizer roles. -/
theorem realizerShape : RootShape withDestructor realizerRoles where
  spine := by
    intro n t u step
    rcases step with (step | step) | step
    · exact step.elim
    · exact decoderComputation_spine realizerDecoderRoles step
    · exact destructor_spine rfl rfl step
  deterministic := by
    intro n t u u' step step'
    rcases step with (step | step) | step
    · exact step.elim
    · rcases step' with (step' | step') | step'
      · exact step'.elim
      · exact decoderComputation_deterministic rfl step' step
      · exact (decoding_not_destructing step step').elim
    · rcases step' with (step' | step') | step'
      · exact step'.elim
      · exact (decoding_not_destructing step' step).elim
      · exact destructor_deterministic step' step

theorem realizerReflects : RootReflectsRename withDestructor.computation :=
  RootReflectsRename.union
    (RootReflectsRename.union RootReflectsRename.empty (decoderComputation_reflectsRename _))
    destructor_reflectsRename

/-- The realizer side: the package with the destructor under its own reduction. -/
def realizerSide : Realizers Tower.Head where
  rules := withDestructor
  roles := realizerRoles
  decoders := codes.decoders
  zero := zeroName
  suc := sucName
  shape := realizerShape
  reflects := realizerReflects
  decoderRoles := realizerDecoderRoles
  numerals := ⟨rfl, rfl⟩
  decodes := fun step => .inl (.inr step)

/-- The only inductive type of the value side is the numbers, with the
constructors `zero` and `suc`. -/
theorem valueRoles_inductive {T : DeclName} {cs : List (DeclName × List (Normalization.Field Tower.Head))}
    (role : valueRoles T = .inductive cs) :
    T = numName ∧ cs = [(zeroName, []), (sucName, [.recursive])] := by
  unfold valueRoles at role
  by_cases hp : T = predName
  · rw [if_pos hp] at role
    cases role
  rw [if_neg hp] at role
  by_cases hi : T = codes.imp
  · rw [if_pos hi] at role
    cases role
  rw [if_neg hi] at role
  by_cases ha : T = allName
  · rw [if_pos ha] at role
    cases role
  rw [if_neg ha] at role
  by_cases hn : T = numName
  · rw [if_pos hn] at role
    exact ⟨hn, (Role.inductive.inj role).symm⟩
  rw [if_neg hn] at role
  by_cases hz : T = zeroName
  · rw [if_pos hz] at role
    cases role
  rw [if_neg hz] at role
  by_cases hs : T = sucName
  · rw [if_pos hs] at role
    cases role
  rw [if_neg hs] at role
  cases role

/-- The constructors the numbers list are declared as constructors, with their
numbers of fields. -/
theorem valueRoles_declared : ConstructorsDeclared valueRoles where
  arity := by
    intro T cs k fields role mem
    obtain ⟨rfl, rfl⟩ := valueRoles_inductive role
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · rfl
  distinct := by
    intro T cs role
    obtain ⟨rfl, rfl⟩ := valueRoles_inductive role
    decide

/-- The normalization model of the package with the destructor: its value side, the
daimon and its realizer side, with the tower's levels. -/
def destructorModel : ModelS.SModel Tower.Head Nat where
  toModel := valueModel
  star := daimonName
  realizers := realizerSide

theorem destructorModel_laws : destructorModel.Laws where
  values := valueModel_laws
  star := rfl
  starNotProp := by decide
  starNotHolds := by decide
  declared := valueRoles_declared

/-! ### The obligations that hold -/

/-- Every constant is strongly normalizing in the package with the destructor. -/
theorem const_sn (c : DeclName) {n : Nat} : SN withDestructor (.const c : Tower.Tm n) :=
  SN.intro fun v step => (const_normal c v step).elim

/-- The closed type of every interpretable carrier is strongly normalizing. -/
theorem carrier_sn : ∀ {k : Kind} {C : Carrier k}, C.Interpretable valueModel →
    SN withDestructor (C.term valueModel)
  | _, _, .prop => const_sn _
  | _, _, .num => const_sn _
  | _, _, .rigid _ _ _ => const_sn _
  | _, _, .arr dom cod =>
      SN.pi spineHeaded (carrier_sn dom) (SN.rename realizerReflects wk (carrier_sn cod))

theorem destructorModel_codesRead : CodesRead valueModel codes where
  proofs := .sort _
  prop := rfl
  holds := rfl
  imp := rfl
  all := fun found => by
    obtain ⟨rfl, rfl⟩ := quantifiers_some found
    exact ⟨.gen, .prop, rfl, .prop, rfl⟩
  eq := fun found => by cases found

/-- The package's codes are read by the model. -/
theorem destructorModel_codesReadS : ModelS.CodesReadS destructorModel codes where
  read := destructorModel_codesRead
  decoders := rfl
  propStuck := fun _ _ role => nomatch role.symm.trans realizerRoles_prop
  carrierSN := carrier_sn

/-- Every root step of the package preserves meaning in the model: a decoding, or
the destructor's step, which the value side computes. -/
theorem destructorModel_root {n : Nat} {l r : Tower.Tm n}
    (step : withDestructor.computation.step l r) :
    ModelS.RootSemanticS destructorModel l r := by
  refine ModelS.ModelRootS.semantic destructorModel_laws
    destructorModel_codesRead.decodes ?_
  rcases step with (step | step) | step
  · exact step.elim
  · exact .inr step
  · exact .inl step

/-- Every constant of the package other than the destructor is a valid term of
its declared type in the model. -/
theorem destructorModel_constant {name : DeclName} {type : Tower.Tm 0}
    (notPred : name ≠ predName) (declared : withDestructor.constantType name = some type) :
    ModelS.ValidTmS destructorModel .nil (.const name) type := by
  change (if name = predName then some predType else
    (codes.codeType name).orElse (fun _ => none)) = some type at declared
  rw [if_neg notPred] at declared
  cases code : codes.codeType name with
  | none =>
      rw [code] at declared
      cases declared
  | some T =>
      rw [code] at declared
      cases declared
      exact ModelS.valid_codeS destructorModel_laws destructorModel_codesReadS code

/-- **Soundness comes down to the destructor.** The package with the destructor
is sound for the model exactly when the destructor is a valid term of its
declared type. -/
theorem destructorModel_soundS_iff :
    ModelS.TypedSoundS withDestructor destructorModel ↔
      ModelS.ValidTmS destructorModel .nil (.const predName) predType := by
  refine ⟨fun sound => sound.constants constantType_pred, fun valid => ?_⟩
  refine
    { laws := destructorModel_laws
      headTyping := id
      isUniverse := id
      join := id
      cumulative := id
      headEq := id
      root := fun step => .inl (destructorModel_root step)
      constants := fun {name type} declared => ?_ }
  by_cases same : name = predName
  · subst same
    rw [constantType_pred] at declared
    cases declared
    exact valid
  · exact destructorModel_constant same declared

/-- **The model is not sound for the package, and the destructor's obligation is
where it fails.** -/
theorem destructorModel_not_soundS :
    ¬ ModelS.TypedSoundS withDestructor destructorModel :=
  fun sound => pred_not_valid destructorModel destructorModel_laws rfl rfl
    (destructorModel_soundS_iff.mp sound)

end Hazards
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
