import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.DecidedFragments

/-!
# Settling by conversion: the agreement-closed rule, and a fully sound settling step

Raw typing of a made code is not closed under agreement (`AgreementCounterexample`): an η-expanded
solution can type a code that an agreeing solution does not. **Formed types are closed under
agreement**: agreeing solutions send a type formed in the frame to equal types (`typeEq_of_agree`),
because the type is a judged term of its universe. So the agreement-invariant reading of "typed after
the match" types the code **in its own frame**, at a formed type `B`, and settles only the comparison
of types: `B` usable at the declared type after the solution. This is the conversion rule of the type
theory, under substitution.

* **The conversion predicate** (`conversion m B`): the substitutions along which `B` is usable at the
  row's type. It is a sieve (subtyping is stable under substitution, `below_substitute`), it is closed
  under agreement (`saturation_conversion`), and it types the row wherever the code is typed at `B` in
  its frame (`conversion_le_typing`).
* **Settling decides it exactly** (`conversion_iff_of_principal`): along a principal answer, `B` is
  usable at the row's type exactly when it is so at every solution.
* **Full soundness** (`typedAfterMatch_of_convertsAlong`): a row that converts along a principal answer
  is typed at every solution of the information. No closure hypothesis is needed.
* **Where typing is closed under agreement** (`closedUnderAgreement_of_conversion`): a row whose
  typings at solutions are conversions of one frame typing has typing closed under agreement among
  solutions; rows typed in their frame are of this kind (`conversion_self`).

**The converting settling step** (`convertingStep`) has the settling step's states, firings and plan,
and asks each made row to convert along the plan (`ConvertingShapes`) instead of being typed along it.

* It is **conservative** over the present step (`converting_admits_of_admits`, `converting_result_eq`),
  and admits only what the settling step admits with the same settler (`converting_le_settling`).
* It is **fully sound for every settler** (`converting_typedAfterMatch`, `converting_admitsByConversion`):
  every made row of an admitted firing converts, hence is typed, at every solution of its information.
* With the semantic settler it is **complete for admission by conversion** wherever the information has
  an initial solution (`ideal_converting_admits`), so on decided information it admits exactly the
  firings admitted by conversion (`ideal_converting_iff_of_decided`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep

open _root_.CategoryTheory Opposite Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull (Make State Firing relabel)
open UnificationWithLevels (Agree InitialSolution)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
variable (levels : LevelModel rules L)

/-! ## Formed types are closed under agreement -/

section Types

/-- **Agreeing substitutions send a formed type to equal types**: the type is a judged term of its
universe, and agreement equates the images of judged terms. -/
theorem typeEq_of_agree {Θ Δ : Context rules} {τ τ' : Θ ⟶ Δ}
    (agree : Agree (frames levels) τ τ') (A : TypeOver Δ) :
    TypeEq rules Θ.raw (A.reindex τ).code (A.reindex τ').code := by
  obtain ⟨v, hv, hTyping, -⟩ := levels.successor A.universeWitness
  let code : TotalTerm Δ := ⟨⟨.head A.level, v, hv, .headType hTyping⟩, ⟨A.code, A.formed⟩⟩
  exact ⟨A.level, A.universeWitness, (agree code).2⟩

omit [UniverseLevel.LevelOrder L] in
/-- Subtyping is stable under substitution. -/
theorem below_substitute {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {σ : Sub Head n m}
    {A B : Tm Head n} (below : Below rules Γ A B) (typed : SubstMor rules Γ Δ σ) :
    Below rules Δ (subst σ A) (subst σ B) :=
  Derivable.substitutes below typed

omit [UniverseLevel.LevelOrder L] in
/-- Equal types are usable at each other. -/
theorem below_of_typeEq {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} (equal : TypeEq rules Γ A B) :
    Below rules Γ A B := by
  obtain ⟨u, hu, e⟩ := equal
  exact .subEqual e hu

omit [UniverseLevel.LevelOrder L] in
/-- A type is usable at itself. -/
theorem below_refl_of_isType {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} (type : IsType rules Γ A) :
    Below rules Γ A A :=
  below_of_typeEq (IsType.refl type)

/-- **Agreement keeps usability between formed types.** -/
theorem below_of_agree {Θ Δ : Context rules} {τ τ' : Θ ⟶ Δ}
    (agree : Agree (frames levels) τ τ') (A B : TypeOver Δ)
    (below : Below rules Θ.raw (A.reindex τ').code (B.reindex τ').code) :
    Below rules Θ.raw (A.reindex τ).code (B.reindex τ).code :=
  .subTrans (below_of_typeEq (typeEq_of_agree levels agree A))
    (.subTrans below (below_of_typeEq (typeEq_of_agree levels agree B).symm))

end Types

/-! ## The conversion predicate -/

section Conversion

omit [UniverseLevel.LevelOrder L] in
/-- **The conversion predicate of a made row at a formed type `B`**: the substitutions along which `B`
is usable at the row's type. -/
def conversion {Δ : Context rules} (m : Make Δ) (B : TypeOver Δ) : Subfunctor (yoneda.obj Δ) where
  obj Θ := {τ | Below rules Θ.unop.raw (B.reindex τ).code (m.type.reindex τ).code}
  map {Θ Θ'} g τ inside := by
    show Below rules Θ'.unop.raw (B.reindex (g.unop ≫ τ)).code (m.type.reindex (g.unop ≫ τ)).code
    rw [TypeOver.reindex_comp, TypeOver.reindex_comp]
    exact below_substitute inside g.unop.typed

omit [UniverseLevel.LevelOrder L] in
theorem mem_conversion {Δ Θ : Context rules} (m : Make Δ) (B : TypeOver Δ) (τ : Θ ⟶ Δ) :
    τ ∈ (conversion m B).obj (op Θ) ↔
      Below rules Θ.raw (B.reindex τ).code (m.type.reindex τ).code := Iff.rfl

/-- **The conversion predicate is closed under agreement.** -/
theorem saturation_conversion {Δ : Context rules} (m : Make Δ) (B : TypeOver Δ) :
    saturation levels (conversion m B) = conversion m B := by
  refine le_antisymm ?_ (le_saturation levels _)
  intro Θ τ inside
  obtain ⟨τ', member, agree⟩ := inside
  exact below_of_agree levels agree B m.type member

omit [UniverseLevel.LevelOrder L] in
/-- A made code **typed in its frame at `B`**. -/
def FrameTypedAt {Δ : Context rules} (m : Make Δ) (B : TypeOver Δ) : Prop :=
  Typed rules Δ.raw m.code B.code

omit [UniverseLevel.LevelOrder L] in
/-- **Conversion types the row**: along a substitution where `B` is usable at the row's type, the code
typed at `B` in its frame is typed at the row's type. -/
theorem conversion_le_typing {Δ : Context rules} {m : Make Δ} {B : TypeOver Δ}
    (typed : FrameTypedAt m B) : conversion m B ≤ typing m := by
  intro Θ τ inside
  exact Derivable.sub (typed.substitute τ.typed) inside

omit [UniverseLevel.LevelOrder L] in
/-- **A row's own type converts to itself everywhere**: the conversion predicate at the declared type is
the whole representable. -/
theorem conversion_self {Δ : Context rules} (m : Make Δ) : conversion m m.type = ⊤ := by
  refine le_antisymm le_top ?_
  intro Θ τ _
  exact below_refl_of_isType (m.type.reindex τ).isType

/-- **Settling decides the conversion rule exactly**: along a principal answer, `B` is usable at the
row's type exactly when it is so at every solution. -/
theorem conversion_iff_of_principal {M Δ : Context rules} {I : EquationStore (TotalTerm Δ)}
    {σ : M ⟶ Δ} (principal : (frames levels).Principal I σ) (m : Make Δ) (B : TypeOver Δ) :
    σ ∈ (conversion m B).obj (op M) ↔ solutions levels I ≤ conversion m B := by
  have key := le_saturation_iff_of_principal levels principal (conversion m B)
  rw [saturation_conversion] at key
  exact key.symm

omit [UniverseLevel.LevelOrder L] in
/-- A made row **converts along** σ: its code is typed in its frame at a formed type that σ makes usable
at the row's type. -/
def ConvertsAlong {M Δ : Context rules} (m : Make Δ) (σ : M ⟶ Δ) : Prop :=
  ∃ B : TypeOver Δ, FrameTypedAt m B ∧ σ ∈ (conversion m B).obj (op M)

omit [UniverseLevel.LevelOrder L] in
/-- A row that converts along σ is typed along σ. -/
theorem ConvertsAlong.typed {M Δ : Context rules} {m : Make Δ} {σ : M ⟶ Δ}
    (converts : ConvertsAlong m σ) : (m.reindex σ).WellTyped := by
  obtain ⟨B, typed, inside⟩ := converts
  exact conversion_le_typing typed (op M) inside

omit [UniverseLevel.LevelOrder L] in
/-- A row typed in its frame converts along every substitution, at its own type. -/
theorem convertsAlong_of_wellTyped {M Δ : Context rules} {m : Make Δ} (typed : m.WellTyped)
    (σ : M ⟶ Δ) : ConvertsAlong m σ :=
  ⟨m.type, typed, by rw [conversion_self]; trivial⟩

omit [UniverseLevel.LevelOrder L] in
/-- Along the identity, converting is being typed in the frame. -/
theorem convertsAlong_id_iff {Δ : Context rules} (m : Make Δ) :
    ConvertsAlong m (𝟙 Δ) ↔ m.WellTyped := by
  constructor
  · intro converts
    have typed := converts.typed
    rwa [Make.reindex_id'] at typed
  · exact fun typed => convertsAlong_of_wellTyped typed (𝟙 Δ)

/-- **Full soundness of settling by conversion**: a row that converts along a principal answer is
typed at every solution of the information. -/
theorem typedAfterMatch_of_convertsAlong {M Δ : Context rules} {I : EquationStore (TotalTerm Δ)}
    {σ : M ⟶ Δ} (principal : (frames levels).Principal I σ) {m : Make Δ}
    (converts : ConvertsAlong m σ) : TypedAfterMatch levels I m := by
  obtain ⟨B, typed, inside⟩ := converts
  exact (typedAfterMatch_iff_le levels I m).mpr
    (((conversion_iff_of_principal levels principal m B).mp inside).trans (conversion_le_typing typed))

/-- **Converting along a principal answer is converting at every solution**, through one frame
typing. -/
theorem convertsAlong_iff_of_principal {M Δ : Context rules} {I : EquationStore (TotalTerm Δ)}
    {σ : M ⟶ Δ} (principal : (frames levels).Principal I σ) (m : Make Δ) :
    ConvertsAlong m σ ↔
      ∃ B : TypeOver Δ, FrameTypedAt m B ∧ solutions levels I ≤ conversion m B := by
  constructor
  · rintro ⟨B, typed, inside⟩
    exact ⟨B, typed, (conversion_iff_of_principal levels principal m B).mp inside⟩
  · rintro ⟨B, typed, everywhere⟩
    exact ⟨B, typed, everywhere (op M) principal.sound⟩

/-- **Where typings at solutions are conversions, typing is closed under agreement**: if every typing
of the row at a solution is a conversion of one frame typing, the row's typing is closed under
agreement among solutions. -/
theorem closedUnderAgreement_of_conversion {Δ : Context rules} {I : EquationStore (TotalTerm Δ)}
    {m : Make Δ} {B : TypeOver Δ} (typed : FrameTypedAt m B)
    (through : ∀ (Θ : Context rules) (τ : Θ ⟶ Δ), (frames levels).Models τ I →
      τ ∈ (typing m).obj (op Θ) → τ ∈ (conversion m B).obj (op Θ)) :
    ClosedUnderAgreement levels I m := by
  intro Θ τ τ' solved agree typedThere
  have solved' : (frames levels).Models τ' I :=
    (UnificationWithLevels.models_of_agree agree I).mp solved
  have convertsHere : τ ∈ (conversion m B).obj (op Θ) := by
    rw [← saturation_conversion levels m B]
    exact ⟨τ', through Θ τ' solved' typedThere, agree⟩
  exact conversion_le_typing typed (op Θ) convertsHere

end Conversion

/-! ## The converting settling step -/

section Step

variable {O : Type} [DecidableEq O]

/-- **Converting shapes**: the step's shapes, with every made row converting along the plan. -/
def ConvertingShapes (settler : Settler levels) {s : State rules O} (f : Firing levels s) : Prop :=
  f.taken.Nodup ∧ f.made.Nodup ∧ f.takes.length = f.taken.length ∧ f.reads.length = f.read.length ∧
    ∀ m ∈ f.makes, ConvertsAlong m.2 (plan levels settler f).2

omit [DecidableEq O] in
theorem ConvertingShapes.typed {settler : Settler levels} {s : State rules O} {f : Firing levels s}
    (shapes : ConvertingShapes levels settler f) :
    ∀ m ∈ f.makes, (m.2.reindex (plan levels settler f).2).WellTyped :=
  fun m member => (shapes.2.2.2.2 m member).typed

variable (O) in
/-- **The converting settling step**: the settling step's states, firings and plan, with each made row
converting along the plan. -/
noncomputable def convertingStep (settler : Settler levels) :
    Interface.Step.Standard (frames levels) O (State rules O) (Firing levels) where
  frame s := s.frame
  knowledge s := s.knowledge
  present s := s.present
  selection f := f.selection
  target f := f.helpers.frame
  extension f := f.helpers.weaken
  information f := f.information
  transported := (DependentFull.step levels O).transported
  Shapes f := ConvertingShapes levels settler f
  Holds f _ τ := f.Holds τ
  Admits {s} f := ConvertingShapes levels settler f ∧
    Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ∧
    (frames levels).Solvable f.information ∧ (frames levels).Entails f.information (fun _ τ => f.Holds τ)
  admits_iff _ := Iff.rfl
  preparedResult f p := settledState levels f (plan levels settler f) (ConvertingShapes.typed levels p.1)
  present_preparedResult _ _ := rfl
  preparedSettle f _ := (plan levels settler f).2
  knowledge_preparedResult _ _ := rfl

variable (settler : Settler levels)

/-- **Conservativity of admission**: every firing the present step admits, the converting step admits,
for every settler. -/
theorem converting_admits_of_admits {s : State rules O} {f : Firing levels s}
    (admitted : (DependentFull.step levels O).Admits f) :
    (convertingStep levels O settler).Admits f := by
  obtain ⟨⟨a, b, c, d, typed⟩, enabled, solvable, holds⟩ := admitted
  exact ⟨⟨a, b, c, d, fun m member => convertsAlong_of_wellTyped (typed m member) _⟩,
    enabled, solvable, holds⟩

/-- **The converting step admits only what the settling step admits**, with the same settler: a row
that converts along the plan is typed along it. -/
theorem converting_le_settling {s : State rules O} {f : Firing levels s}
    (admitted : (convertingStep levels O settler).Admits f) : (settlingStep levels O settler).Admits f := by
  obtain ⟨⟨a, b, c, d, rows⟩, enabled, solvable, holds⟩ := admitted
  exact ⟨⟨a, b, c, d, fun m member => (rows m member).typed⟩, enabled, solvable, holds⟩

/-- **Conservativity of results**: with the present step's result. -/
theorem converting_result_eq {s : State rules O} {f : Firing levels s}
    (admitted : (DependentFull.step levels O).Admits f) :
    (convertingStep levels O settler).result f (converting_admits_of_admits levels settler admitted) =
      (DependentFull.step levels O).result f admitted :=
  settledState_eq_of_plan levels f (plan_of_frameTyped levels settler admitted.1.2.2.2.2)
    (ConvertingShapes.typed levels (converting_admits_of_admits levels settler admitted).1)
    admitted.1.2.2.2.2

omit [DecidableEq O] in
/-- **Every made row converts at every solution**, whatever the settler: the plan is the identity, or an
initial solution, and conversion along either reaches every solution. -/
theorem convertingShapes_everywhere {s : State rules O} {f : Firing levels s}
    (shapes : ConvertingShapes levels settler f) :
    ∀ m ∈ f.makes, ∃ B : TypeOver f.helpers.frame,
      FrameTypedAt m.2 B ∧ solutions levels f.information ≤ conversion m.2 B := by
  intro m member
  have converts := shapes.2.2.2.2 m member
  have alongIdentity : ConvertsAlong m.2 (𝟙 f.helpers.frame) →
      ∃ B : TypeOver f.helpers.frame,
        FrameTypedAt m.2 B ∧ solutions levels f.information ≤ conversion m.2 B := by
    intro identity
    refine ⟨m.2.type, (convertsAlong_id_iff m.2).mp identity, ?_⟩
    rw [conversion_self]
    exact le_top
  by_cases typed : FrameTyped levels f
  · rw [plan_of_frameTyped levels settler typed] at converts
    exact alongIdentity converts
  · rw [plan_of_not_frameTyped levels settler typed] at converts
    cases verdict : settler f.information with
    | settled M σ initial =>
        rw [verdict] at converts
        exact (convertsAlong_iff_of_principal levels (principal_of_initial levels initial) m.2).mp converts
    | postponed =>
        rw [verdict] at converts
        exact alongIdentity converts

/-- **Admission by conversion**: the step's admission, with each made row typed in its frame at a type
usable at the row's type at every solution of the information. -/
def AdmitsByConversion {s : State rules O} (f : Firing levels s) : Prop :=
  (f.taken.Nodup ∧ f.made.Nodup ∧ f.takes.length = f.taken.length ∧ f.reads.length = f.read.length ∧
      ∀ m ∈ f.makes, ∃ B : TypeOver f.helpers.frame,
        FrameTypedAt m.2 B ∧ solutions levels f.information ≤ conversion m.2 B) ∧
    Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ∧
    (frames levels).Solvable f.information ∧ (frames levels).Entails f.information (fun _ τ => f.Holds τ)

/-- Admission by conversion is admission after the match. -/
theorem AdmitsByConversion.admitsAfterMatch {s : State rules O} {f : Firing levels s}
    (admitted : AdmitsByConversion levels f) : AdmitsAfterMatch levels f := by
  obtain ⟨⟨a, b, c, d, rows⟩, enabled, solvable, holds⟩ := admitted
  refine ⟨⟨a, b, c, d, fun m member => ?_⟩, enabled, solvable, holds⟩
  obtain ⟨B, typed, everywhere⟩ := rows m member
  exact (typedAfterMatch_iff_le levels _ m.2).mpr (everywhere.trans (conversion_le_typing typed))

/-- **The converting step admits nothing beyond admission by conversion**, whatever the settler. -/
theorem converting_admitsByConversion {s : State rules O} {f : Firing levels s}
    (admitted : (convertingStep levels O settler).Admits f) : AdmitsByConversion levels f := by
  have rows := convertingShapes_everywhere levels settler admitted.1
  obtain ⟨⟨a, b, c, d, _⟩, enabled, solvable, holds⟩ := admitted
  exact ⟨⟨a, b, c, d, rows⟩, enabled, solvable, holds⟩

/-- **Full soundness of the converting step, for every settler**: every made row of an admitted firing
is typed at every solution of its information. -/
theorem converting_typedAfterMatch {s : State rules O} {f : Firing levels s}
    (admitted : (convertingStep levels O settler).Admits f) :
    ∀ m ∈ f.makes, TypedAfterMatch levels f.information m.2 :=
  (converting_admitsByConversion levels settler admitted).admitsAfterMatch.1.2.2.2.2

/-- ... so every firing it admits is admitted after the match. -/
theorem converting_admitsAfterMatch {s : State rules O} {f : Firing levels s}
    (admitted : (convertingStep levels O settler).Admits f) : AdmitsAfterMatch levels f :=
  (converting_admitsByConversion levels settler admitted).admitsAfterMatch

/-- **The semantic settler realizes admission by conversion** wherever the information has an initial
solution. -/
theorem ideal_converting_admits {s : State rules O} {f : Firing levels s}
    (admitted : AdmitsByConversion levels f) {M : Context rules} {σ : M ⟶ f.helpers.frame}
    (initial : InitialSolution (frames levels) f.information σ) :
    (convertingStep levels O (Settler.ideal levels)).Admits f := by
  obtain ⟨⟨a, b, c, d, rows⟩, enabled, solvable, holds⟩ := admitted
  refine ⟨⟨a, b, c, d, fun m member => ?_⟩, enabled, solvable, holds⟩
  by_cases frameTyped : FrameTyped levels f
  · rw [plan_of_frameTyped levels _ frameTyped]
    exact convertsAlong_of_wellTyped (frameTyped m member) _
  · rw [plan_of_not_frameTyped levels _ frameTyped]
    obtain ⟨M', σ', initial', settles⟩ := Settler.ideal_settles levels initial
    rw [settles]
    exact (convertsAlong_iff_of_principal levels (principal_of_initial levels initial') m.2).mpr
      (rows m member)

/-- **On decided information, the converting step with the semantic settler admits exactly the
firings admitted by conversion.** -/
theorem ideal_converting_iff_of_decided {s : State rules O} {f : Firing levels s}
    (decided : Decided levels f.information) :
    (convertingStep levels O (Settler.ideal levels)).Admits f ↔ AdmitsByConversion levels f := by
  refine ⟨converting_admitsByConversion levels _, fun admitted => ?_⟩
  rcases decided with ⟨M, σ, initial⟩ | none
  · exact ideal_converting_admits levels admitted initial
  · exact absurd admitted.2.2.1 none

end Step

end NativeTypesOnTheStep

#print axioms NativeTypesOnTheStep.typeEq_of_agree
#print axioms NativeTypesOnTheStep.below_of_agree
#print axioms NativeTypesOnTheStep.conversion
#print axioms NativeTypesOnTheStep.saturation_conversion
#print axioms NativeTypesOnTheStep.conversion_le_typing
#print axioms NativeTypesOnTheStep.conversion_self
#print axioms NativeTypesOnTheStep.conversion_iff_of_principal
#print axioms NativeTypesOnTheStep.typedAfterMatch_of_convertsAlong
#print axioms NativeTypesOnTheStep.convertsAlong_iff_of_principal
#print axioms NativeTypesOnTheStep.closedUnderAgreement_of_conversion
#print axioms NativeTypesOnTheStep.convertingStep
#print axioms NativeTypesOnTheStep.converting_admits_of_admits
#print axioms NativeTypesOnTheStep.converting_le_settling
#print axioms NativeTypesOnTheStep.converting_result_eq
#print axioms NativeTypesOnTheStep.convertingShapes_everywhere
#print axioms NativeTypesOnTheStep.converting_admitsByConversion
#print axioms NativeTypesOnTheStep.converting_typedAfterMatch
#print axioms NativeTypesOnTheStep.converting_admitsAfterMatch
#print axioms NativeTypesOnTheStep.ideal_converting_admits
#print axioms NativeTypesOnTheStep.ideal_converting_iff_of_decided

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
