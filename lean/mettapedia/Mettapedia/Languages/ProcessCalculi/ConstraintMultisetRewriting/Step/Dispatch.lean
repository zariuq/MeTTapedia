import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TranslationFrames
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PrincipalAnswers

/-!
# Dispatch: answering in a fibre gives the top frame's admission

A map of frame instances `Φ : FrameMap X Y` carries a cheap fibre `X` into a top instance `Y`.
Most joins to the dependent top run downward: the top decides, and its answer is copied into the
fibre. This file states the upward direction once, at the interface: when answering in `X` gives
`Y`'s admission.

## Principal answers, relatively and uniquely

* `Frames.FactorsOn K answer T`: every solution of `K` factors through `answer` on the terms of `T`.
  A principal answer does so on every set of terms (`Principal.factorsOn`).
* **Uniqueness** (`Principal.unique`, `Principal.of_factors`, `Principal.congr`): two principal
  answers of one store factor through each other on every term of the store's frame, and a
  solution through which a principal answer factors is itself principal. So principal answers are
  determined up to mutual factorization, up to the frame equivalence.
* `Frames.Decides K`: a principal answer or a refutation. `Frames.Answer K` is such a decision as
  data, and a `Frames.Decider` decides every store.

## The license

`Φ.LicensedAt K` has two clauses:
* **factoring**: every source answer that factors the source solutions on a set of terms factors
  every target solution of the translated store on the image of that set. Taking all terms, a
  source principal answer factors every target solution on the image (`LicensedAt.factorsOnImage`,
  the hypothesis of `entails_iff_of_factorsOnImage`);
* **refutation**: the translated store is solvable only when the source store is, so a source
  refutation is a target refutation (`LicensedAt.refutes`).

The factoring clause is stated for answers relative to a set of terms so that licenses compose
(`DispatchCompose`). On a decided store it is equivalent to its absolute reading
(`licensedAt_iff_of_decides`), and to **covering** (`licensedAt_iff_coversAt`): every target solution
of the translated store is, on the image, a later instance of a translated source solution. Covering
is the proof device for instances (`CoversAt.licensedAt`); a target principal answer that is an
instance of a translated source solution covers (`coversAt_of_top`).

## Dispatch

At the frame level (`LicensedAt.solvable_iff`, `LicensedAt.entails_models_iff`,
`entails_absent_iff`, `LicensedAt.entails_count_iff`): on a store the source decides, solvability
and asks of equation guards of the translated store are those of the source store; asks of absence
need only the refutation clause, at each absence extension; asks of counts need the license at the
store and the refutation clause at each extension by matches. Along covering no decision is needed
(`CoversAt.entails_models_iff`, `CoversAt.entails_count_iff`).

At the step level (`dispatch_admits_iff`): for a step `P` over the target frames, at a firing whose
information and guards are the images of source stores (`Dispatched`), under a licensed map that
reflects the equivalence, admission is the shapes, the enabling, source solvability and the
source ask, whenever the source decides its information. With a principal answer the ask is the
guards at the answer (`dispatch_admits_iff_of_principal`); with a refutation the firing is refused
(`dispatch_refused`); with a decision procedure admission is computed by it
(`dispatch_admits_iff_decider`); along covering the source need not decide
(`dispatch_admits_iff_of_coversAt`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)

universe uO uT uH uO' uT' uH' uOcc uS uF

namespace Frames

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} {X : Frames Tm Hom}

section Definitions

variable (X)

/-- `answer` **factors every solution of `K` on the terms of `T`**. -/
def FactorsOn {a m : Obj} (K : EquationStore (Tm a)) (answer : Hom a m) (T : Set (Tm a)) : Prop :=
  ∀ (b : Obj) (f : Hom a b), X.Models f K →
    ∃ residual : Hom m b, ∀ t ∈ T, X.E (X.act f t) (X.act (X.comp residual answer) t)

/-- **A store is decided**: it has a principal answer, or it is refuted. -/
def Decides {a : Obj} (K : EquationStore (Tm a)) : Prop :=
  (∃ (m : Obj) (answer : Hom a m), X.Principal K answer) ∨ ¬ X.Solvable K

/-- **A decision of a store**, as data: a principal answer, or a refutation. -/
inductive Answer {a : Obj} (K : EquationStore (Tm a)) : Type (max uO uH) where
  | principal (m : Obj) (answer : Hom a m) (isPrincipal : X.Principal K answer)
  | refuted (refutation : ¬ X.Solvable K)

/-- **A decision procedure**: a decision of every store. -/
abbrev Decider := ∀ {a : Obj} (K : EquationStore (Tm a)), X.Answer K

end Definitions

namespace Answer

variable {a : Obj} {K : EquationStore (Tm a)}

theorem decides : X.Answer K → X.Decides K
  | .principal m answer isPrincipal => Or.inl ⟨m, answer, isPrincipal⟩
  | .refuted refutation => Or.inr refutation

/-- **What a decision accepts**: guards hold at its principal answer; a refutation accepts no
guards. -/
def Accepts : X.Answer K → EquationStore (Tm a) → Prop
  | .principal _ answer _, guards => X.Models answer guards
  | .refuted _, _ => False

end Answer

/-! ## Principal answers: relative factoring and uniqueness -/

theorem Principal.factorsOn {a m : Obj} {K : EquationStore (Tm a)} {answer : Hom a m}
    (principal : X.Principal K answer) (T : Set (Tm a)) : X.FactorsOn K answer T := by
  intro b f solved
  obtain ⟨residual, through⟩ := principal.factors b f solved
  exact ⟨residual, fun t _ => through t⟩

/-- A principal answer is a solution that factors every solution on all terms. -/
theorem principal_iff_factorsOn_univ {a m : Obj} {K : EquationStore (Tm a)} {answer : Hom a m} :
    X.Principal K answer ↔ X.Models answer K ∧ X.FactorsOn K answer Set.univ := by
  refine ⟨fun principal => ⟨principal.sound, principal.factorsOn Set.univ⟩, ?_⟩
  rintro ⟨sound, factors⟩
  refine ⟨sound, fun b f solved => ?_⟩
  obtain ⟨residual, through⟩ := factors b f solved
  exact ⟨residual, fun t => through t (Set.mem_univ t)⟩

theorem FactorsOn.mono {a m : Obj} {K : EquationStore (Tm a)} {answer : Hom a m} {T T' : Set (Tm a)}
    (factors : X.FactorsOn K answer T') (inside : T ⊆ T') : X.FactorsOn K answer T := by
  intro b f solved
  obtain ⟨residual, through⟩ := factors b f solved
  exact ⟨residual, fun t member => through t (inside member)⟩

/-- **Principal answers are unique up to mutual factorization**: each of two principal answers of
one store factors through the other, on every term of the store's frame. -/
theorem Principal.unique {a m₁ m₂ : Obj} {K : EquationStore (Tm a)} {one : Hom a m₁}
    {two : Hom a m₂} (first : X.Principal K one) (second : X.Principal K two) :
    (∃ r : Hom m₁ m₂, ∀ t : Tm a, X.E (X.act two t) (X.act (X.comp r one) t)) ∧
      ∃ r : Hom m₂ m₁, ∀ t : Tm a, X.E (X.act one t) (X.act (X.comp r two) t) :=
  ⟨first.factors m₂ two second.sound, second.factors m₁ one first.sound⟩

/-- **A solution through which a principal answer factors is principal.** -/
theorem Principal.of_factors {a m₁ m₂ : Obj} {K : EquationStore (Tm a)} {one : Hom a m₁}
    {two : Hom a m₂} (first : X.Principal K one) (solves : X.Models two K)
    (through : ∃ r : Hom m₂ m₁, ∀ t : Tm a, X.E (X.act one t) (X.act (X.comp r two) t)) :
    X.Principal K two := by
  obtain ⟨r, through⟩ := through
  refine ⟨solves, fun b f solved => ?_⟩
  obtain ⟨r₁, factored⟩ := first.factors b f solved
  refine ⟨X.comp r₁ r, fun t => ?_⟩
  have composite : X.act (X.comp (X.comp r₁ r) two) t = X.act r₁ (X.act r (X.act two t)) := by
    rw [X.act_comp, X.act_comp]
  have toOne := factored t
  rw [X.act_comp] at toOne
  have moved := X.preserves r₁ (through t)
  rw [X.act_comp r two] at moved
  rw [composite]
  exact (X.equivalence b).trans toOne moved

/-- **Principal answers are determined by their action up to the equivalence.** -/
theorem Principal.congr {a m : Obj} {K : EquationStore (Tm a)} {one two : Hom a m}
    (principal : X.Principal K one) (same : ∀ t : Tm a, X.E (X.act one t) (X.act two t)) :
    X.Principal K two := by
  refine principal.of_factors ((models_congrE same K).mp principal.sound) ⟨X.id m, fun t => ?_⟩
  rw [X.act_comp, X.act_id]
  exact same t

/-- **Uniqueness, as a characterization**: given one principal answer, the principal answers are
exactly the solutions through which it factors. -/
theorem Principal.unique_iff {a m₁ m₂ : Obj} {K : EquationStore (Tm a)} {one : Hom a m₁}
    (first : X.Principal K one) (two : Hom a m₂) :
    X.Principal K two ↔ X.Models two K ∧
      ∃ r : Hom m₂ m₁, ∀ t : Tm a, X.E (X.act one t) (X.act (X.comp r two) t) :=
  ⟨fun second => ⟨second.sound, (first.unique second).2⟩,
    fun ⟨solves, through⟩ => first.of_factors solves through⟩

/-- Asks of equation guards are decided at a store's decision: the guards at a principal answer,
and vacuously at a refutation. -/
theorem Answer.entails_iff {a : Obj} {K : EquationStore (Tm a)} (answer : X.Answer K)
    (guards : EquationStore (Tm a)) :
    X.Solvable K ∧ X.Entails K (fun _ f => X.Models f guards) ↔ answer.Accepts guards := by
  cases answer with
  | principal m answer principal =>
      exact ⟨fun h => (principal.entails_models_iff guards).mp h.2,
        fun h => ⟨principal.solvable, (principal.entails_models_iff guards).mpr h⟩⟩
  | refuted refutation => exact ⟨fun h => refutation h.1, fun h => h.elim⟩

end Frames

namespace Translation.FrameMap

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {Obj' : Type uO'} {Tm' : Obj' → Type uT'} {Hom' : Obj' → Obj' → Type uH'}
  {X : Frames Tm Hom} {Y : Frames Tm' Hom'} (Φ : FrameMap X Y)

/-! ## Translated stores -/

theorem store_append {a : Obj} (K L : EquationStore (Tm a)) :
    Φ.store (K ++ L) = Φ.store K ++ Φ.store L :=
  List.map_append

theorem store_singleton {a : Obj} (s t : Tm a) : Φ.store [(s, t)] = [(Φ.tm s, Φ.tm t)] := rfl

/-- **Composites act on translated terms as the composite of the translations**, up to the
target equivalence. -/
theorem tm_act_comp {a b c : Obj} (g : Hom b c) (f : Hom a b) (t : Tm a) :
    Y.E (Φ.tm (X.act (X.comp g f) t)) (Y.act (Φ.hom g) (Y.act (Φ.hom f) (Φ.tm t))) := by
  rw [X.act_comp]
  exact (Y.equivalence _).trans (Φ.act g (X.act f t)) (Y.preserves (Φ.hom g) (Φ.act f t))

/-- `FactorsOnImage` is factoring on the range of the translation. -/
theorem factorsOnImage_iff {a : Obj} {m' : Obj'} (K : EquationStore (Tm a))
    (answer' : Hom' (Φ.obj a) m') :
    Φ.FactorsOnImage K answer' ↔
      Y.FactorsOn (Φ.store K) answer' (Set.range fun t : Tm a => Φ.tm t) := by
  constructor
  · intro factors b τ solved
    obtain ⟨residual, through⟩ := factors b τ solved
    refine ⟨residual, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact through t
  · intro factors b τ solved
    obtain ⟨residual, through⟩ := factors b τ solved
    exact ⟨residual, fun t => through _ ⟨t, rfl⟩⟩

/-! ## The license -/

/-- **The dispatch license at a source store.** -/
structure LicensedAt {a : Obj} (K : EquationStore (Tm a)) : Prop where
  /-- A source answer that factors the source solutions on a set of terms factors every target
  solution of the translated store on the image of that set. -/
  factors : ∀ (T : Set (Tm a)) {m : Obj} {answer : Hom a m}, X.Models answer K →
    X.FactorsOn K answer T → Y.FactorsOn (Φ.store K) (Φ.hom answer) ((fun t : Tm a => Φ.tm t) '' T)
  /-- The translated store is solvable only when the source store is: a source refutation is a
  target refutation. -/
  reflects_solvable : Y.Solvable (Φ.store K) → X.Solvable K

/-- **The license on a class of stores.** -/
def LicensedOn (D : (a : Obj) → EquationStore (Tm a) → Prop) : Prop :=
  ∀ (a : Obj) (K : EquationStore (Tm a)), D a K → Φ.LicensedAt K

/-- **The license on every store.** -/
def Licensed : Prop := ∀ (a : Obj) (K : EquationStore (Tm a)), Φ.LicensedAt K

/-- **Covering**: every target solution of the translated store is, on the image, a later
instance of a translated source solution. -/
def CoversAt {a : Obj} (K : EquationStore (Tm a)) : Prop :=
  ∀ (b : Obj') (τ : Hom' (Φ.obj a) b), Y.Models τ (Φ.store K) →
    ∃ (c : Obj) (f : Hom a c) (residual : Hom' (Φ.obj c) b), X.Models f K ∧
      ∀ t : Tm a, Y.E (Y.act τ (Φ.tm t)) (Y.act (Y.comp residual (Φ.hom f)) (Φ.tm t))

variable {Φ}

namespace LicensedAt

variable {a : Obj} {K : EquationStore (Tm a)}

/-- **A source principal answer factors every target solution on the image.** -/
theorem factorsOnImage (licensed : Φ.LicensedAt K) {m : Obj} {answer : Hom a m}
    (principal : X.Principal K answer) : Φ.FactorsOnImage K (Φ.hom answer) := by
  rw [factorsOnImage_iff]
  have image := licensed.factors Set.univ principal.sound (principal.factorsOn Set.univ)
  rwa [Set.image_univ] at image

/-- **A source refutation is a target refutation.** -/
theorem refutes (licensed : Φ.LicensedAt K) (refuted : ¬ X.Solvable K) :
    ¬ Y.Solvable (Φ.store K) :=
  fun solvable => refuted (licensed.reflects_solvable solvable)

/-- **Solvability dispatches.** -/
theorem solvable_iff (licensed : Φ.LicensedAt K) : Y.Solvable (Φ.store K) ↔ X.Solvable K :=
  ⟨licensed.reflects_solvable, Φ.solvable⟩

/-- **Asks of equation guards dispatch** to a source that decides the store. -/
theorem entails_models_iff (reflects : Φ.Reflects) (licensed : Φ.LicensedAt K)
    (decides : X.Decides K) (G : EquationStore (Tm a)) :
    Y.Entails (Φ.store K) (fun _ g => Y.Models g (Φ.store G)) ↔
      X.Entails K (fun _ f => X.Models f G) := by
  rcases decides with ⟨_, _, principal⟩ | refuted
  · exact Φ.entails_iff_of_factorsOnImage reflects principal (licensed.factorsOnImage principal)
  · exact ⟨fun _ b f solved => absurd ⟨b, f, solved⟩ refuted,
      fun _ b g solved => absurd ⟨b, g, solved⟩ (licensed.refutes refuted)⟩

/-- **A licensed decided store is covered.** -/
theorem coversAt (licensed : Φ.LicensedAt K) (decides : X.Decides K) : Φ.CoversAt K := by
  intro b τ solved
  rcases decides with ⟨m, answer, principal⟩ | refuted
  · obtain ⟨residual, through⟩ := licensed.factorsOnImage principal b τ solved
    exact ⟨m, answer, residual, principal.sound, through⟩
  · exact absurd (licensed.reflects_solvable ⟨b, τ, solved⟩) refuted

end LicensedAt

/-- **Covering licenses.** -/
theorem CoversAt.licensedAt {a : Obj} {K : EquationStore (Tm a)} (covers : Φ.CoversAt K) :
    Φ.LicensedAt K where
  factors := by
    intro T m answer _ factors b τ solved
    obtain ⟨c, f, residual, fSolves, through⟩ := covers b τ solved
    obtain ⟨r, fThrough⟩ := factors c f fSolves
    refine ⟨Y.comp residual (Φ.hom r), ?_⟩
    rintro _ ⟨t, inside, rfl⟩
    have toImage := through t
    rw [Y.act_comp] at toImage
    have inner : Y.E (Y.act (Φ.hom f) (Φ.tm t)) (Y.act (Φ.hom r) (Y.act (Φ.hom answer) (Φ.tm t))) :=
      (Y.equivalence _).trans ((Y.equivalence _).symm (Φ.act f t))
        ((Y.equivalence _).trans (Φ.preserves (fThrough t inside)) (Φ.tm_act_comp r answer t))
    rw [Y.act_comp, Y.act_comp]
    exact (Y.equivalence b).trans toImage (Y.preserves residual inner)
  reflects_solvable := by
    rintro ⟨b, τ, solved⟩
    obtain ⟨c, f, -, fSolves, -⟩ := covers b τ solved
    exact ⟨c, f, fSolves⟩

/-- **Asks of equation guards dispatch along covering**, with no decision of the source. -/
theorem CoversAt.entails_models_iff (reflects : Φ.Reflects) {a : Obj} {K : EquationStore (Tm a)}
    (covers : Φ.CoversAt K) (G : EquationStore (Tm a)) :
    Y.Entails (Φ.store K) (fun _ g => Y.Models g (Φ.store G)) ↔
      X.Entails K (fun _ f => X.Models f G) := by
  refine ⟨Φ.entails_reflect reflects, fun asked b τ solved => ?_⟩
  obtain ⟨c, f, residual, fSolves, through⟩ := covers b τ solved
  have later := Frames.models_comp (Φ.models (asked c f fSolves)) residual
  intro e member
  obtain ⟨e₀, present, rfl⟩ := List.mem_map.mp member
  exact (Y.equivalence _).trans (through e₀.1)
    ((Y.equivalence _).trans (later _ (List.mem_map.mpr ⟨e₀, present, rfl⟩))
      ((Y.equivalence _).symm (through e₀.2)))

/-- **On a decided store the license is covering.** -/
theorem licensedAt_iff_coversAt {a : Obj} {K : EquationStore (Tm a)} (decides : X.Decides K) :
    Φ.LicensedAt K ↔ Φ.CoversAt K :=
  ⟨fun licensed => licensed.coversAt decides, CoversAt.licensedAt⟩

/-- **On a decided store the license is its two clauses read absolutely**: every source principal
answer factors every target solution on the image, and a source refutation is a target
refutation. -/
theorem licensedAt_iff_of_decides {a : Obj} {K : EquationStore (Tm a)} (decides : X.Decides K) :
    Φ.LicensedAt K ↔
      (∀ {m : Obj} {answer : Hom a m}, X.Principal K answer → Φ.FactorsOnImage K (Φ.hom answer)) ∧
        (¬ X.Solvable K → ¬ Y.Solvable (Φ.store K)) := by
  refine ⟨fun licensed => ⟨licensed.factorsOnImage, licensed.refutes⟩, ?_⟩
  rintro ⟨factors, refutes⟩
  refine CoversAt.licensedAt fun b τ solved => ?_
  rcases decides with ⟨m, answer, principal⟩ | refuted
  · obtain ⟨residual, through⟩ := factors principal b τ solved
    exact ⟨m, answer, residual, principal.sound, through⟩
  · exact absurd ⟨b, τ, solved⟩ (refutes refuted)

/-- **A target principal answer at a translated source solution covers.** -/
theorem coversAt_of_principal {a m : Obj} {K : EquationStore (Tm a)} {σ : Hom a m}
    (solves : X.Models σ K) (principal : Y.Principal (Φ.store K) (Φ.hom σ)) : Φ.CoversAt K := by
  intro b τ solved
  obtain ⟨residual, through⟩ := principal.factors b τ solved
  exact ⟨m, σ, residual, solves, fun t => through (Φ.tm t)⟩

/-- **A target decision licenses, when its principal answer is an instance of a translated source
solution.** By uniqueness of principal answers, the translated solution is then principal too. -/
theorem coversAt_of_top {a m : Obj} {m' : Obj'} {K : EquationStore (Tm a)}
    {top : Hom' (Φ.obj a) m'} (principal : Y.Principal (Φ.store K) top) {σ : Hom a m}
    (solves : X.Models σ K)
    (through : ∃ r : Hom' (Φ.obj m) m', ∀ u : Tm' (Φ.obj a),
      Y.E (Y.act top u) (Y.act (Y.comp r (Φ.hom σ)) u)) :
    Φ.CoversAt K :=
  coversAt_of_principal solves (principal.of_factors (Φ.models solves) through)

/-- **A target refutation licenses**, vacuously. -/
theorem coversAt_of_refuted {a : Obj} {K : EquationStore (Tm a)}
    (refuted : ¬ Y.Solvable (Φ.store K)) : Φ.CoversAt K :=
  fun b τ solved => absurd ⟨b, τ, solved⟩ refuted

/-! ## Absence dispatches with the refutation clause alone -/

/-- **Absence asks dispatch** when the license holds at each absence extension. Only the
refutation clause is used, and the source need not decide. -/
theorem entails_absent_iff {O : Type*} {a : Obj} {K : EquationStore (Tm a)} (p : Tm a)
    (present : Finset O) (row : O → Tm a)
    (licensed : ∀ o ∈ present, Φ.LicensedAt (K ++ [(p, row o)])) :
    Y.Entails (Φ.store K)
        (fun _ τ => ∀ o ∈ present, ¬ Y.E (Y.act τ (Φ.tm p)) (Y.act τ (Φ.tm (row o)))) ↔
      X.Entails K (fun _ f => ∀ o ∈ present, ¬ X.E (X.act f p) (X.act f (row o))) := by
  constructor
  · intro asked b f solved o inside equated
    refine asked (Φ.obj b) (Φ.hom f) (Φ.models solved) o inside ?_
    exact (Y.equivalence _).trans ((Y.equivalence _).symm (Φ.act f p))
      ((Y.equivalence _).trans (Φ.preserves equated) (Φ.act f (row o)))
  · intro asked b τ solved o inside equated
    have extended : Y.Models τ (Φ.store (K ++ [(p, row o)])) := by
      rw [store_append, store_singleton]
      refine (Frames.models_append τ _ _).mpr ⟨solved, fun e member => ?_⟩
      obtain rfl := List.mem_singleton.mp member
      exact equated
    obtain ⟨c, f, both⟩ := (licensed o inside).reflects_solvable ⟨b, τ, extended⟩
    obtain ⟨old, new⟩ := (Frames.models_append f K _).mp both
    exact asked c f old o inside (new _ (List.mem_singleton_self _))

/-! ## Counting dispatches along covering -/

open Classical in
/-- **Count asks dispatch along covering**, when the license holds at each extension by matches of
present rows. The translated solutions match at least the rows a source solution matches, by
covering, and at most, by the refutation clause at the extension by the rows they match. -/
theorem CoversAt.entails_count_iff (reflects : Φ.Reflects) {O : Type*} {a : Obj}
    {K : EquationStore (Tm a)} (covers : Φ.CoversAt K) (p : Tm a) (present : Finset O)
    (row : O → Tm a) (number : ℕ)
    (licensed : ∀ L : List O, (∀ o ∈ L, o ∈ present) →
      Φ.LicensedAt (K ++ L.map fun o => (p, row o))) :
    Y.Entails (Φ.store K) (fun _ τ =>
        (present.filter fun o => Y.E (Y.act τ (Φ.tm p)) (Y.act τ (Φ.tm (row o)))).card = number) ↔
      X.Entails K (fun _ f =>
        (present.filter fun o => X.E (X.act f p) (X.act f (row o))).card = number) := by
  have image : ∀ {b : Obj} (f : Hom a b) (s t : Tm a),
      Y.E (Y.act (Φ.hom f) (Φ.tm s)) (Y.act (Φ.hom f) (Φ.tm t)) ↔ X.E (X.act f s) (X.act f t) := by
    intro b f s t
    constructor
    · intro same
      exact reflects ((Y.equivalence _).trans (Φ.act f s)
        ((Y.equivalence _).trans same ((Y.equivalence _).symm (Φ.act f t))))
    · intro same
      exact (Y.equivalence _).trans ((Y.equivalence _).symm (Φ.act f s))
        ((Y.equivalence _).trans (Φ.preserves same) (Φ.act f t))
  constructor
  · intro asked b f solved
    rw [← asked (Φ.obj b) (Φ.hom f) (Φ.models solved)]
    congr 1
    exact Finset.filter_congr fun o _ => (image f p (row o)).symm
  · intro asked b τ solved
    obtain ⟨c, f, residual, fSolves, through⟩ := covers b τ solved
    apply le_antisymm
    · have extended : Y.Models τ (Φ.store (K ++ (present.filter fun o =>
          Y.E (Y.act τ (Φ.tm p)) (Y.act τ (Φ.tm (row o)))).toList.map fun o => (p, row o))) := by
        rw [store_append]
        refine (Frames.models_append τ _ _).mpr ⟨solved, fun e member => ?_⟩
        obtain ⟨e₀, inside, rfl⟩ := List.mem_map.mp member
        obtain ⟨o, matched, rfl⟩ := List.mem_map.mp inside
        exact (Finset.mem_filter.mp (Finset.mem_toList.mp matched)).2
      obtain ⟨d, g, both⟩ := (licensed _ fun o matched =>
        (Finset.mem_filter.mp (Finset.mem_toList.mp matched)).1).reflects_solvable ⟨b, τ, extended⟩
      obtain ⟨gK, gNew⟩ := (Frames.models_append g K _).mp both
      rw [← asked d g gK]
      apply Finset.card_le_card
      intro o matched
      refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp matched).1, ?_⟩
      exact gNew _ (List.mem_map.mpr ⟨o, Finset.mem_toList.mpr matched, rfl⟩)
    · rw [← asked c f fSolves]
      apply Finset.card_le_card
      intro o matched
      refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp matched).1, ?_⟩
      have moved := Y.preserves residual ((image f p (row o)).mpr (Finset.mem_filter.mp matched).2)
      rw [← Y.act_comp, ← Y.act_comp] at moved
      exact (Y.equivalence b).trans (through p)
        ((Y.equivalence b).trans moved ((Y.equivalence b).symm (through (row o))))

open Classical in
/-- **Count asks dispatch** to a source that decides the store, under the license at the store and
at each extension by matches of present rows. -/
theorem LicensedAt.entails_count_iff (reflects : Φ.Reflects) {O : Type*} {a : Obj}
    {K : EquationStore (Tm a)} (licensedHere : Φ.LicensedAt K) (decides : X.Decides K) (p : Tm a)
    (present : Finset O) (row : O → Tm a) (number : ℕ)
    (licensed : ∀ L : List O, (∀ o ∈ L, o ∈ present) →
      Φ.LicensedAt (K ++ L.map fun o => (p, row o))) :
    Y.Entails (Φ.store K) (fun _ τ =>
        (present.filter fun o => Y.E (Y.act τ (Φ.tm p)) (Y.act τ (Φ.tm (row o)))).card = number) ↔
      X.Entails K (fun _ f =>
        (present.filter fun o => X.E (X.act f p) (X.act f (row o))).card = number) :=
  (licensedHere.coversAt decides).entails_count_iff reflects p present row number licensed

/-! ## Dispatch at the step -/

variable (Φ)

/-- A translated store, read at a frame the image frame equals. -/
def storeAt {a : Obj} {b' : Obj'} (frame : Φ.obj a = b') (K : EquationStore (Tm a)) :
    EquationStore (Tm' b') :=
  frame ▸ Φ.store K

theorem solvable_storeAt {a : Obj} {b' : Obj'} (frame : Φ.obj a = b') (K : EquationStore (Tm a)) :
    Y.Solvable (Φ.storeAt frame K) ↔ Y.Solvable (Φ.store K) := by
  subst frame
  rfl

theorem entails_storeAt {a : Obj} {b' : Obj'} (frame : Φ.obj a = b') (K G : EquationStore (Tm a)) :
    Y.Entails (Φ.storeAt frame K) (fun _ g => Y.Models g (Φ.storeAt frame G)) ↔
      Y.Entails (Φ.store K) (fun _ g => Y.Models g (Φ.store G)) := by
  subst frame
  rfl

section Step

variable {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}

/-- **A dispatched firing** of a step over the target frames: its information is, up to the target
equivalence of stores, the image of a source store at a source frame, and its guards and predicate
queries are the image of source equation guards. -/
structure Dispatched (P : Step Y O State Firing) [P.Guarded] {s : State} (f : Firing s) where
  source : Obj
  frame : Φ.obj source = P.target f
  problem : EquationStore (Tm source)
  guards : EquationStore (Tm source)
  information : Y.Equivalent (P.information f) (Φ.storeAt frame problem)
  holds : ∀ (b : Obj') (g : Hom' (P.target f) b),
    P.Holds f b g ↔ Y.Models g (Φ.storeAt frame guards)

variable {Φ}

/-- **Dispatch.** At a dispatched firing of a step over the target frames, under a licensed map that
reflects the equivalence, admission is the shapes, the enabling, source solvability and the source
ask of the guards, whenever the source decides the firing's problem. -/
theorem dispatch_admits_iff (reflects : Φ.Reflects) (P : Step Y O State Firing) [P.Guarded] {s : State}
    {f : Firing s} (d : Φ.Dispatched P f) (licensed : Φ.LicensedAt d.problem)
    (decides : X.Decides d.problem) :
    P.Admits f ↔ P.Shapes f ∧
      Enabled (fun _ : O => ()) (P.present s) ((P.selection f).commit (T := Unit)) ∧
      X.Solvable d.problem ∧ X.Entails d.problem (fun _ g => X.Models g d.guards) := by
  have asks : Y.Entails (P.information f) (P.Holds f) ↔
      Y.Entails (Φ.storeAt d.frame d.problem)
        (fun _ g => Y.Models g (Φ.storeAt d.frame d.guards)) := by
    rw [Frames.Equivalent.entails_iff d.information]
    exact ⟨fun asked b g solved => (d.holds b g).mp (asked b g solved),
      fun asked b g solved => (d.holds b g).mpr (asked b g solved)⟩
  rw [P.admits_iff f, Frames.Equivalent.solvable_iff d.information, asks, solvable_storeAt,
    entails_storeAt, licensed.solvable_iff, licensed.entails_models_iff reflects decides]

/-- **Dispatch along covering**: the same conclusion with no decision of the source. -/
theorem dispatch_admits_iff_of_coversAt (reflects : Φ.Reflects) (P : Step Y O State Firing) [P.Guarded]
    {s : State} {f : Firing s} (d : Φ.Dispatched P f) (covers : Φ.CoversAt d.problem) :
    P.Admits f ↔ P.Shapes f ∧
      Enabled (fun _ : O => ()) (P.present s) ((P.selection f).commit (T := Unit)) ∧
      X.Solvable d.problem ∧ X.Entails d.problem (fun _ g => X.Models g d.guards) := by
  have asks : Y.Entails (P.information f) (P.Holds f) ↔
      Y.Entails (Φ.storeAt d.frame d.problem)
        (fun _ g => Y.Models g (Φ.storeAt d.frame d.guards)) := by
    rw [Frames.Equivalent.entails_iff d.information]
    exact ⟨fun asked b g solved => (d.holds b g).mp (asked b g solved),
      fun asked b g solved => (d.holds b g).mpr (asked b g solved)⟩
  rw [P.admits_iff f, Frames.Equivalent.solvable_iff d.information, asks, solvable_storeAt,
    entails_storeAt, covers.licensedAt.solvable_iff, covers.entails_models_iff reflects]

/-- **A source refutation refuses the firing.** Only the refutation clause is used. -/
theorem dispatch_refused (P : Step Y O State Firing) [P.Guarded] {s : State} {f : Firing s}
    (d : Φ.Dispatched P f) (licensed : Φ.LicensedAt d.problem) (refuted : ¬ X.Solvable d.problem) :
    ¬ P.Admits f := by
  intro admitted
  have solvable := P.solvable_information admitted
  rw [Frames.Equivalent.solvable_iff d.information, solvable_storeAt] at solvable
  exact refuted (licensed.reflects_solvable solvable)

/-- **Dispatch at a source principal answer**: admission is the guards at the answer. -/
theorem dispatch_admits_iff_of_principal (reflects : Φ.Reflects) (P : Step Y O State Firing) [P.Guarded]
    {s : State} {f : Firing s} (d : Φ.Dispatched P f) (licensed : Φ.LicensedAt d.problem)
    {m : Obj} {answer : Hom d.source m} (principal : X.Principal d.problem answer) :
    P.Admits f ↔ P.Shapes f ∧
      Enabled (fun _ : O => ()) (P.present s) ((P.selection f).commit (T := Unit)) ∧
      X.Models answer d.guards := by
  rw [dispatch_admits_iff reflects P d licensed (Or.inl ⟨m, answer, principal⟩),
    principal.entails_models_iff]
  exact and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h => h.2, fun h => ⟨principal.solvable, h⟩⟩)

/-- **Dispatch at a decision**: admission is the shapes, the enabling, and what the decision
accepts. -/
theorem dispatch_admits_iff_answer (reflects : Φ.Reflects) (P : Step Y O State Firing) [P.Guarded] {s : State}
    {f : Firing s} (d : Φ.Dispatched P f) (licensed : Φ.LicensedAt d.problem)
    (answer : X.Answer d.problem) :
    P.Admits f ↔ P.Shapes f ∧
      Enabled (fun _ : O => ()) (P.present s) ((P.selection f).commit (T := Unit)) ∧
      answer.Accepts d.guards := by
  rw [dispatch_admits_iff reflects P d licensed answer.decides, answer.entails_iff]

/-- **Dispatch to a decision procedure of the source**: the top's admission is computed by running
the source's decision procedure on the firing's problem and checking the guards at its answer. -/
theorem dispatch_admits_iff_decider (reflects : Φ.Reflects) (decider : X.Decider)
    (P : Step Y O State Firing) [P.Guarded] {s : State} {f : Firing s} (d : Φ.Dispatched P f)
    (licensed : Φ.LicensedAt d.problem) :
    P.Admits f ↔ P.Shapes f ∧
      Enabled (fun _ : O => ()) (P.present s) ((P.selection f).commit (T := Unit)) ∧
      (decider d.problem).Accepts d.guards :=
  dispatch_admits_iff_answer reflects P d licensed (decider d.problem)

end Step

end Translation.FrameMap

#print axioms Frames.Principal.factorsOn
#print axioms Frames.principal_iff_factorsOn_univ
#print axioms Frames.Principal.unique
#print axioms Frames.Principal.of_factors
#print axioms Frames.Principal.congr
#print axioms Frames.Principal.unique_iff
#print axioms Frames.Answer.decides
#print axioms Frames.Answer.entails_iff
#print axioms Translation.FrameMap.tm_act_comp
#print axioms Translation.FrameMap.factorsOnImage_iff
#print axioms Translation.FrameMap.LicensedAt.factorsOnImage
#print axioms Translation.FrameMap.LicensedAt.refutes
#print axioms Translation.FrameMap.LicensedAt.solvable_iff
#print axioms Translation.FrameMap.LicensedAt.entails_models_iff
#print axioms Translation.FrameMap.LicensedAt.coversAt
#print axioms Translation.FrameMap.CoversAt.licensedAt
#print axioms Translation.FrameMap.licensedAt_iff_coversAt
#print axioms Translation.FrameMap.licensedAt_iff_of_decides
#print axioms Translation.FrameMap.coversAt_of_principal
#print axioms Translation.FrameMap.coversAt_of_top
#print axioms Translation.FrameMap.coversAt_of_refuted
#print axioms Translation.FrameMap.entails_absent_iff
#print axioms Translation.FrameMap.CoversAt.entails_count_iff
#print axioms Translation.FrameMap.LicensedAt.entails_count_iff
#print axioms Translation.FrameMap.dispatch_admits_iff
#print axioms Translation.FrameMap.CoversAt.entails_models_iff
#print axioms Translation.FrameMap.dispatch_admits_iff_of_coversAt
#print axioms Translation.FrameMap.dispatch_refused
#print axioms Translation.FrameMap.dispatch_admits_iff_of_principal
#print axioms Translation.FrameMap.dispatch_admits_iff_answer
#print axioms Translation.FrameMap.dispatch_admits_iff_decider

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
