import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.OlderUnknown
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalCheckingTower

/-!
# Template inference for neutral codes

The templating step (`TemplateConversion`) asks of each made row a template: a code typed in a template
frame whose variables are filled by the row's frame, the template rule holding along the answer. Templates
are existential, so a decision needs to find one. For neutral codes it can, and the one it finds is
principal.

**The inferred template** (`inferredTemplate`) of a row along an answer `σ : M ⟶ Δ` whose frame `M` is
covered by variables of `Δ` at their own types (`fill?`): the template frame is `M` itself, the template
code is the row's code read at the answer, its type the row's type read at the answer, and each variable
of `M` is filled by a variable of `Δ` it comes from, preferably one of the code's own, since an answer may
identify several variables (D2's coerce answer identifies `x` and `g`). Where the code read at the answer
has the row's type there, its rule holds: the filling conditions are reflexive (`inferred_holds`).

**Neutral codes have principal types** (`Normalization.Synth.principal`): the kernel's synthesis of a
variable, or of a neutral code applied to a variable, gives a type below every type of the code
(`synthNeutral?`, which returns the synthesis derivation). So a template of any kind holds along `σ` only
if the code at the answer has the row's type there (`Template.typed_of_holds`), only if its synthesized
type is usable at it. Between simple types that usability is decided (`typeBelow?`, `typeBelow?_sound`):
between heads exactly, between dependent function types with one domain by their codomains, and refused
between dependent function types whose head domains cannot be equal; and a type is usable at itself,
whatever its former (`usable?`, `usable?_sound`).

**The decision** (`templated?`, `templated?_sound`): where the answer is covered, the code read back
through the cover is the row's code, the code at the answer synthesizes, and the types are decided by
`typeBelow?`, the row is typed by a template along `σ` exactly when the synthesized type is usable at the
row's type.
Row by row (`rowsTemplated?`) and with the computable settler (`templatingAdmits?`,
`templatingAdmits?_sound`) this decides the templating step on its fragment (`decideTemplating`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.TemplateInference

open _root_.CategoryTheory Opposite Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull Interface.DependentFull.Controls
open UnificationWithLevels (InitialSolution)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)
open ComputableControls (HeadBelow headBelow? headBelow?_sound below_heads_iff)

/-! ## Kernel synthesis of neutral codes -/

/-- An argument variable checks against a domain when its declared type is the domain, or both are heads
and the one is usable at the other. -/
def argBelow? {n : Nat} (Γ : Tower.Ctx n) (k : Fin n) (A : Tower.Tm n) : Bool :=
  decide (Ctx.lookup Γ k = A) || headBelow? (Ctx.lookup Γ k) A == some true

theorem argBelow?_sound {n : Nat} {Γ : Tower.Ctx n} (formed : CtxFormed Tower.rules Γ) {k : Fin n}
    {A : Tower.Tm n} (ok : argBelow? Γ k A = true) : Below Tower.rules Γ (Ctx.lookup Γ k) A := by
  unfold argBelow? at ok
  rcases Bool.or_eq_true_iff.mp ok with same | heads
  · obtain rfl := of_decide_eq_true same
    obtain ⟨u, hu, typed⟩ := formed.lookup k
    exact below_refl_of_isType ⟨u, hu, typed⟩
  · exact (headBelow?_sound formed (beq_iff_eq.mp heads)).mp rfl

/-- **Kernel synthesis of a neutral code**: a variable synthesizes its declaration, a neutral code
applied to a variable synthesizes the codomain when the function's synthesized type is a dependent
function type the argument checks against. The derivation is returned with the type. -/
def synthNeutral? {n : Nat} {Γ : Tower.Ctx n} (formed : CtxFormed Tower.rules Γ) :
    (t : Tower.Tm n) → Option {T : Tower.Tm n // Synth setting.R setting.roles Γ t T}
  | .var j => some ⟨Ctx.lookup Γ j, .var j⟩
  | .app f a =>
      match a, synthNeutral? formed f with
      | .var k, some ⟨.pi A B, synthesized⟩ =>
          if ok : argBelow? Γ k A = true then
            some ⟨inst0 (.var k) B, .app synthesized
              (RedTy.refl (Typed.isType (S := setting)
                (Synth.principal (S := setting) TowerModel.facts TowerModel.algebra
                  ContextualDependentNormalCheckingTower.head_typing_unique synthesized formed).1 formed))
              (.switch (.var k) (argBelow?_sound formed ok))⟩
          else none
      | _, _ => none
  | _ => none

/-! ## The inferred template -/

/-- The variables of a neutral code, in order. -/
def neutralVars {n : Nat} : Tower.Tm n → List (Fin n)
  | .var i => [i]
  | .app f a => neutralVars f ++ neutralVars a
  | _ => []

/-- A variable of the answer's frame, read back as a variable of the row's frame at its own type,
preferring the given variables (the row code's own): an answer may identify several variables. -/
def preimage? {M Δ : Context Tower.rules} (σ : M ⟶ Δ) (prefer : List (Fin Δ.arity)) (j : Fin M.arity) :
    Option (Fin Δ.arity) :=
  (prefer ++ List.finRange Δ.arity).find? fun i =>
    decide (σ.substitution i = .var j ∧ subst σ.substitution (Ctx.lookup Δ.raw i) = Ctx.lookup M.raw j)

theorem preimage?_spec {M Δ : Context Tower.rules} {σ : M ⟶ Δ} {prefer : List (Fin Δ.arity)}
    {j : Fin M.arity} {i : Fin Δ.arity} (found : preimage? σ prefer j = some i) :
    σ.substitution i = .var j ∧ subst σ.substitution (Ctx.lookup Δ.raw i) = Ctx.lookup M.raw j := by
  unfold preimage? at found
  have holds := List.find?_some found
  simp only [decide_eq_true_eq] at holds
  exact holds

/-- **The cover's filling**: every variable of the answer's frame read back, when each has a preimage. -/
def fill? {M Δ : Context Tower.rules} (σ : M ⟶ Δ) (prefer : List (Fin Δ.arity)) :
    Option {fill : Fin M.arity → Fin Δ.arity // ∀ j, σ.substitution (fill j) = .var j ∧
      subst σ.substitution (Ctx.lookup Δ.raw (fill j)) = Ctx.lookup M.raw j} :=
  if all : ∀ j : Fin M.arity, (preimage? σ prefer j).isSome = true then
    some ⟨fun j => (preimage? σ prefer j).get (all j), fun j => preimage?_spec (Option.some_get (all j)).symm⟩
  else none

/-- **The inferred template**: the code read at the answer, in the answer's frame, at the row's type read
at the answer, each variable filled back. -/
def inferredTemplate {M Δ : Context Tower.rules} (σ : M ⟶ Δ) (m : Make Δ)
    (fill : Fin M.arity → Fin Δ.arity)
    (typed : Typed Tower.rules M.raw (subst σ.substitution m.code) (m.type.reindex σ).code)
    (filled : m.code = Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.rename fill
      (subst σ.substitution m.code)) : Template m :=
  ⟨M, subst σ.substitution m.code, m.type.reindex σ, fill, typed, filled⟩

/-- **The inferred template's rule holds along the answer**: its filling conditions are reflexive. -/
theorem inferred_holds {M Δ : Context Tower.rules} (σ : M ⟶ Δ) (m : Make Δ)
    (fill : {fill : Fin M.arity → Fin Δ.arity // ∀ j, σ.substitution (fill j) = .var j ∧
      subst σ.substitution (Ctx.lookup Δ.raw (fill j)) = Ctx.lookup M.raw j})
    (typed : Typed Tower.rules M.raw (subst σ.substitution m.code) (m.type.reindex σ).code)
    (filled : m.code = Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.rename fill.val
      (subst σ.substitution m.code)) :
    (inferredTemplate σ m fill.val typed filled).Holds σ := by
  have along : (fun i : Fin M.arity => σ.substitution (fill.val i)) = ids :=
    funext fun j => (fill.property j).1
  refine ⟨fun j => ?_, ?_⟩
  · show Below Tower.rules M.raw (subst σ.substitution (Ctx.lookup Δ.raw (fill.val j)))
      (subst (fun i : Fin M.arity => σ.substitution (fill.val i)) (Ctx.lookup M.raw j))
    rw [along, subst_ids, (fill.property j).2]
    obtain ⟨u, hu, typedLookup⟩ := M.formed.lookup j
    exact below_refl_of_isType ⟨u, hu, typedLookup⟩
  · show Below Tower.rules M.raw
      (subst (fun i : Fin M.arity => σ.substitution (fill.val i)) (m.type.reindex σ).code)
      (m.type.reindex σ).code
    rw [along, subst_ids]
    exact below_refl_of_isType (m.type.reindex σ).isType

/-! ## Usability between simple types -/

/-- **A decision of usability between simple types**: between heads exactly; between dependent function
types with the same domain, by their codomains; dependent function types whose domains are heads that
cannot be equal are refused. Anything else is declined. -/
def typeBelow? : {n : Nat} → Tower.Tm n → Tower.Tm n → Option Bool
  | _, .head h, .head h' => some (decide (HeadBelow h h'))
  | _, .pi A B, .pi A' B' =>
      if A = A' then typeBelow? B B'
      else
        match A, A' with
        | .head h, .head h' => if HeadBelow h h' ∧ HeadBelow h' h then none else some false
        | _, _ => none
  | _, _, _ => none

/-- **The decision is exact where it answers**, between types of a formed context. -/
theorem typeBelow?_sound : ∀ {n : Nat} {Γ : Tower.Ctx n} (_ : CtxFormed Tower.rules Γ) {A B : Tower.Tm n}
    {b : Bool}, IsType Tower.rules Γ A → IsType Tower.rules Γ B → typeBelow? A B = some b →
      (b = true ↔ Below Tower.rules Γ A B)
  | _, _, formed, .head h, .head h', b, _, _, decided => by
      simp only [typeBelow?, Option.some.injEq] at decided
      subst decided
      rw [decide_eq_true_iff, below_heads_iff formed]
  | _, Γ, formed, .pi A B, .pi A' B', b, typeLeft, typeRight, decided => by
      simp only [typeBelow?] at decided
      split at decided
      · rename_i same
        subst same
        obtain ⟨⟨u, hu, tA⟩, typeB⟩ := IsType.pi_parts typeLeft
        obtain ⟨-, typeB'⟩ := IsType.pi_parts typeRight
        have formedA : CtxFormed Tower.rules (.snoc Γ A) := .snoc formed ⟨u, hu, tA⟩
        have piIff : Below Tower.rules Γ (.pi A B) (.pi A B') ↔
            ∃ A₀ B₀, TypeEq Tower.rules Γ (.pi A B') (.pi A₀ B₀) ∧ TypeEq Tower.rules Γ A A₀ ∧
              Below Tower.rules (.snoc Γ A) B B₀ :=
          Below.pi_iff (S := setting) TowerModel.facts formed typeLeft
        rw [typeBelow?_sound formedA typeB typeB' decided, piIff]
        constructor
        · intro below
          exact ⟨A, B', IsType.refl typeRight, IsType.refl ⟨u, hu, tA⟩, below⟩
        · rintro ⟨A₀, B₀, eT, -, below⟩
          obtain ⟨-, eB⟩ := LevelTower.pi_injective eT formed
          exact .subTrans below (below_of_typeEq eB.symm)
      · rename_i differ
        split at decided
        · rename_i h h'
          split at decided
          · cases decided
          · rename_i apart
            simp only [Option.some.injEq] at decided
            subst decided
            simp only [Bool.false_eq_true, false_iff]
            intro below
            have piIff : Below Tower.rules Γ (.pi (.head h) B) (.pi (.head h') B') ↔
                ∃ A₀ B₀, TypeEq Tower.rules Γ (.pi (.head h') B') (.pi A₀ B₀) ∧
                  TypeEq Tower.rules Γ (.head h) A₀ ∧ Below Tower.rules (.snoc Γ (.head h)) B B₀ :=
              Below.pi_iff (S := setting) TowerModel.facts formed typeLeft
            obtain ⟨A₀, B₀, eT, eA, -⟩ := piIff.mp below
            obtain ⟨eA', -⟩ := LevelTower.pi_injective eT formed
            have equal : TypeEq Tower.rules Γ (.head h) (.head h') := eA.trans setting.levels eA'.symm
            exact apart ⟨(below_heads_iff formed h h').mp (below_of_typeEq equal),
              (below_heads_iff formed h' h).mp (below_of_typeEq equal.symm)⟩
        · cases decided
  | _, _, _, .var _, _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .const _, _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .head _, .var _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .head _, .const _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .head _, .pi _ _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .head _, .sigma _ _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .head _, .lam _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .head _, .app _ _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .head _, .pair _ _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .head _, .fst _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .head _, .snd _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .head _, .id _ _ _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .head _, .refl _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .pi _ _, .var _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .pi _ _, .const _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .pi _ _, .head _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .pi _ _, .sigma _ _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .pi _ _, .lam _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .pi _ _, .app _ _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .pi _ _, .pair _ _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .pi _ _, .fst _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .pi _ _, .snd _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .pi _ _, .id _ _ _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .pi _ _, .refl _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .sigma _ _, _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .lam _, _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .app _ _, _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .pair _ _, _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .fst _, _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .snd _, _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .id _ _ _, _, _, _, _, decided => by simp [typeBelow?] at decided
  | _, _, _, .refl _, _, _, _, _, decided => by simp [typeBelow?] at decided

/-- **Usability, decided**: a type is usable at itself, whatever its former; otherwise between simple
types (`typeBelow?`). -/
def usable? {n : Nat} (A B : Tower.Tm n) : Option Bool := if A = B then some true else typeBelow? A B

theorem usable?_sound {n : Nat} {Γ : Tower.Ctx n} (formed : CtxFormed Tower.rules Γ) {A B : Tower.Tm n}
    {b : Bool} (typeA : IsType Tower.rules Γ A) (typeB : IsType Tower.rules Γ B)
    (decided : usable? A B = some b) : b = true ↔ Below Tower.rules Γ A B := by
  unfold usable? at decided
  split at decided
  · rename_i same
    subst same
    simp only [Option.some.injEq] at decided
    subst decided
    exact ⟨fun _ => below_refl_of_isType typeA, fun _ => rfl⟩
  · exact typeBelow?_sound formed typeA typeB decided

/-! ## The decision -/

/-- **The templating decision of a row along an answer**, on its fragment: covered answer, the code read
back through the cover, a neutral code at the answer, types decided by `usable?`. -/
def templated? {M Δ : Context Tower.rules} (σ : M ⟶ Δ) (m : Make Δ) : Option Bool :=
  match fill? σ (neutralVars m.code) with
  | none => none
  | some fill =>
      if m.code = Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.rename fill.val
          (subst σ.substitution m.code) then
        match synthNeutral? M.formed (subst σ.substitution m.code) with
        | some T => usable? T.val (m.type.reindex σ).code
        | none => none
      else none

/-- **The decision is exact where it answers**: the inferred template is principal among all templates. -/
theorem templated?_sound {M Δ : Context Tower.rules} {σ : M ⟶ Δ} {m : Make Δ} {b : Bool}
    (decided : templated? σ m = some b) : b = true ↔ TemplatedAlong m σ := by
  unfold templated? at decided
  split at decided
  · cases decided
  · rename_i fill _
    split at decided
    · rename_i filled
      split at decided
      · rename_i T _
        have principal := Synth.principal (S := setting) TowerModel.facts TowerModel.algebra
          ContextualDependentNormalCheckingTower.head_typing_unique T.property M.formed
        rw [usable?_sound M.formed (Typed.isType (S := setting) principal.1 M.formed)
          (m.type.reindex σ).isType decided]
        constructor
        · intro below
          have typed : Typed Tower.rules M.raw (subst σ.substitution m.code) (m.type.reindex σ).code :=
            .sub principal.1 below
          exact ⟨inferredTemplate σ m fill.val typed filled, inferred_holds σ m fill typed filled⟩
        · rintro ⟨t, holds⟩
          have typed : Typed Tower.rules M.raw (subst σ.substitution m.code) (m.type.reindex σ).code :=
            t.typed_of_holds holds
          exact TypeLe.toBelow (principal.2 typed) (Typed.isType (S := setting) typed M.formed)
      · cases decided
    · cases decided

/-- The templating decision for every made row. -/
def rowsTemplated? {M Δ : Context Tower.rules} (σ : M ⟶ Δ) : List (Nat × Make Δ) → Option Bool
  | [] => some true
  | m :: rest =>
      match templated? σ m.2, rowsTemplated? σ rest with
      | some first, some others => some (first && others)
      | _, _ => none

theorem rowsTemplated?_sound {M Δ : Context Tower.rules} (σ : M ⟶ Δ) :
    ∀ {makes : List (Nat × Make Δ)} {b : Bool}, rowsTemplated? σ makes = some b →
      (b = true ↔ ∀ m ∈ makes, TemplatedAlong m.2 σ)
  | [], b, decided => by
      simp only [rowsTemplated?, Option.some.injEq] at decided
      subst decided
      simp
  | m :: rest, b, decided => by
      unfold rowsTemplated? at decided
      cases first : templated? σ m.2 with
      | none => rw [first] at decided; cases decided
      | some a =>
          cases others : rowsTemplated? σ rest with
          | none => rw [first, others] at decided; cases decided
          | some c =>
              rw [first, others] at decided
              simp only [Option.some.injEq] at decided
              subst decided
              rw [Bool.and_eq_true, templated?_sound first, rowsTemplated?_sound σ others,
                List.forall_mem_cons]

/-! ## The templating step, decided -/

section Step

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
variable (levels : LevelModel rules L) {O : Type} [DecidableEq O] (settler : Settler levels)

/-- **Admission of the templating step, read at a settled answer**, for a firing without queries: its
shapes with each row typed by a template along the answer, its enabling, and its guards at the answer. -/
theorem templating_admits_iff_of_settled {s : State rules O} {f : Firing levels s}
    (noQueries : f.queries = []) {M : Context rules} {σ : M ⟶ f.helpers.frame}
    {initial : InitialSolution (frames levels) f.information σ}
    (verdict : settler f.information = .settled M σ initial) :
    (templatingStep levels O settler).Admits f ↔
      (f.taken.Nodup ∧ f.made.Nodup ∧ f.takes.length = f.taken.length ∧ f.reads.length = f.read.length ∧
        ∀ m ∈ f.makes, TemplatedAlong m.2 σ) ∧
      Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ∧
      (frames levels).Models σ f.guards := by
  have principal := principal_of_initial levels initial
  have guards : (frames levels).Entails f.information (fun _ τ => f.Holds τ) ↔
      (frames levels).Models σ f.guards := by
    rw [← Frames.Principal.entails_models_iff principal f.guards]
    unfold Firing.Holds
    rw [noQueries]
    constructor
    · exact fun entailed b τ solved => (entailed b τ solved).1
    · exact fun entailed b τ solved => ⟨entailed b τ solved, fun q member => absurd member List.not_mem_nil⟩
  constructor
  · rintro ⟨shapes, enabled, _, holds⟩
    exact ⟨(templatingShapes_iff_of_settled levels settler verdict).mp shapes, enabled, guards.mp holds⟩
  · rintro ⟨shapes, enabled, holds⟩
    exact ⟨(templatingShapes_iff_of_settled levels settler verdict).mpr shapes, enabled,
      principal.solvable, guards.mpr holds⟩

end Step

/-- **The decision of admission of the computable templating step**, for a firing without guards or
queries: settled, decide each row's template and check shapes and enabling at the answer; refuted,
refuse; otherwise decline. -/
def templatingAdmits? (families : List (Family setting.levels)) {s : State setting.R Nat}
    (f : Firing setting.levels s) : Option Bool :=
  if f.guards.isEmpty && f.queries.isEmpty then
    match firstDecisionAt setting.levels f.information families with
    | .settled _ σ _ => (rowsTemplated? σ f.makes).map fun rows =>
        rows && decide (f.taken.Nodup ∧ f.made.Nodup ∧ f.takes.length = f.taken.length ∧
          f.reads.length = f.read.length) &&
        decide ((∀ o ∈ f.taken, o ∈ s.present) ∧ (∀ o ∈ f.read, o ∈ s.present) ∧
          (∀ o ∈ f.taken, o ∉ f.read) ∧ ∀ o ∈ f.made, o ∉ s.present)
    | .refuted _ => some false
    | .undecided => none
  else none

/-- **The decision is sound and complete where it answers.** -/
theorem templatingAdmits?_sound (families : List (Family setting.levels)) {s : State setting.R Nat}
    {f : Firing setting.levels s} {b : Bool} (decided : templatingAdmits? families f = some b) :
    b = true ↔ (templatingStep setting.levels Nat (Settler.ofFamilies setting.levels families)).Admits f := by
  unfold templatingAdmits? at decided
  split at decided
  · rename_i empty
    obtain ⟨noGuards, noQueries⟩ := Bool.and_eq_true_iff.mp empty
    have noGuards : f.guards = [] := List.isEmpty_iff.mp noGuards
    have noQueries : f.queries = [] := List.isEmpty_iff.mp noQueries
    cases first : firstDecisionAt setting.levels f.information families with
    | settled M σ initial =>
        rw [first] at decided
        obtain ⟨rows, hrows, rfl⟩ := Option.map_eq_some_iff.mp decided
        have verdict : Settler.ofFamilies setting.levels families f.information = .settled M σ initial := by
          unfold Settler.ofFamilies
          rw [first]
          rfl
        rw [templating_admits_iff_of_settled setting.levels _ noQueries verdict, noGuards,
          Bool.and_eq_true, Bool.and_eq_true, rowsTemplated?_sound σ hrows, decide_eq_true_iff,
          decide_eq_true_iff]
        constructor
        · rintro ⟨⟨rowsHold, a, b, c, d⟩, enabled⟩
          exact ⟨⟨a, b, c, d, rowsHold⟩, (enabled_iff f).mpr enabled, Frames.models_nil _⟩
        · rintro ⟨⟨a, b, c, d, rowsHold⟩, enabled, -⟩
          exact ⟨⟨rowsHold, a, b, c, d⟩, (enabled_iff f).mp enabled⟩
    | refuted none =>
        rw [first] at decided
        simp only [Option.some.injEq] at decided
        subst decided
        simp only [Bool.false_eq_true, false_iff]
        exact fun admitted => none admitted.2.2.1
    | undecided =>
        rw [first] at decided
        cases decided
  · cases decided

/-- A decisive first decision comes from a decisive family of the list. -/
theorem decidedBy_of_firstDecisionAt {Δ : Context setting.R} {I : EquationStore (TotalTerm Δ)} :
    ∀ {families : List (Family setting.levels)}, (firstDecisionAt setting.levels I families).Decisive →
      DecidedBy setting.levels families I
  | [], decisive => decisive.elim
  | F :: rest, decisive => by
      unfold firstDecisionAt at decisive
      cases first : F I with
      | undecided =>
          rw [first] at decisive
          obtain ⟨G, member, d⟩ := decidedBy_of_firstDecisionAt decisive
          exact ⟨G, List.mem_cons_of_mem _ member, d⟩
      | settled M σ initial =>
          exact ⟨F, List.mem_cons_self .., (by rw [first]; trivial : (F I).Decisive)⟩
      | refuted absent =>
          exact ⟨F, List.mem_cons_self .., (by rw [first]; trivial : (F I).Decisive)⟩

/-- **Where the computable templating decision answers, it answers the semantic settler's templating
step.** -/
theorem templatingAdmits?_ideal (families : List (Family setting.levels)) {s : State setting.R Nat}
    {f : Firing setting.levels s} {b : Bool} (decided : templatingAdmits? families f = some b) :
    b = true ↔ (templatingStep setting.levels Nat (Settler.ideal setting.levels)).Admits f := by
  rw [templatingAdmits?_sound families decided]
  apply ofFamilies_templating_iff_ideal
  unfold templatingAdmits? at decided
  split at decided
  · cases first : firstDecisionAt setting.levels f.information families with
    | settled M σ initial => exact decidedBy_of_firstDecisionAt (by rw [first]; trivial)
    | refuted absent => exact decidedBy_of_firstDecisionAt (by rw [first]; trivial)
    | undecided =>
        rw [first] at decided
        cases decided
  · cases decided

/-- **Where N3's computable converting decision answers, it answers the semantic settler's converting
step.** -/
theorem admits?_ideal (families : List (Family setting.levels)) {s : State setting.R Nat}
    {f : Firing setting.levels s} {b : Bool} (decided : ComputableControls.admits? families f = some b) :
    b = true ↔ (convertingStep setting.levels Nat (Settler.ideal setting.levels)).Admits f := by
  rw [ComputableControls.admits?_sound families decided]
  apply ofFamilies_converting_iff_ideal
  unfold ComputableControls.admits? at decided
  split at decided
  · cases first : firstDecisionAt setting.levels f.information families with
    | settled M σ initial => exact decidedBy_of_firstDecisionAt (by rw [first]; trivial)
    | refuted absent => exact decidedBy_of_firstDecisionAt (by rw [first]; trivial)
    | undecided =>
        rw [first] at decided
        cases decided
  · cases decided

/-- **Decidable admission of the templating step on its decided fragment.** -/
def decideTemplating (families : List (Family setting.levels)) {s : State setting.R Nat}
    (f : Firing setting.levels s) {b : Bool} (decided : templatingAdmits? families f = some b) :
    Decidable ((templatingStep setting.levels Nat (Settler.ofFamilies setting.levels families)).Admits f) :=
  if h : b = true then isTrue ((templatingAdmits?_sound families decided).mp h)
  else isFalse fun admitted => h ((templatingAdmits?_sound families decided).mpr admitted)

end NativeTypesOnTheStep.TemplateInference

#print axioms NativeTypesOnTheStep.TemplateInference.argBelow?_sound
#print axioms NativeTypesOnTheStep.TemplateInference.synthNeutral?
#print axioms NativeTypesOnTheStep.TemplateInference.preimage?_spec
#print axioms NativeTypesOnTheStep.TemplateInference.fill?
#print axioms NativeTypesOnTheStep.TemplateInference.inferred_holds
#print axioms NativeTypesOnTheStep.TemplateInference.typeBelow?_sound
#print axioms NativeTypesOnTheStep.TemplateInference.usable?_sound
#print axioms NativeTypesOnTheStep.TemplateInference.templated?_sound
#print axioms NativeTypesOnTheStep.TemplateInference.rowsTemplated?_sound
#print axioms NativeTypesOnTheStep.TemplateInference.templating_admits_iff_of_settled
#print axioms NativeTypesOnTheStep.TemplateInference.templatingAdmits?_sound
#print axioms NativeTypesOnTheStep.TemplateInference.decidedBy_of_firstDecisionAt
#print axioms NativeTypesOnTheStep.TemplateInference.templatingAdmits?_ideal
#print axioms NativeTypesOnTheStep.TemplateInference.admits?_ideal
#print axioms NativeTypesOnTheStep.TemplateInference.decideTemplating

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
