import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.LawfulTransport
import Mettapedia.OSLF.Framework.DerivedModalities

/-!
# The fibration of solution predicates: reindexing across frame and knowledge changes

**Variance.** A morphism `Hom a a'` instantiates what the frame `a` declares by terms of `a'`; it
denotes a contextual substitution from `a'` to `a`. A solution of `a` is a later frame with a
morphism into it (`Frames.Solution`). Predicates over `a` are predicates on its solutions (`Pred`).
A morphism `h : Hom a a'` turns a solution of `a'` into one of `a` by precomposition (`restrict`), so
predicates are reindexed from `a` to `a'` (`reindex`): covariantly in the instantiating morphism,
contravariantly in the substitution it denotes. Reindexing is the Set-level change of base `pb` of
OSLF's derived modalities, with its adjoints `di` and `ui` along `restrict`.

**Equality.** The frame's own equivalence `E` is the selected equality: convertibility at dependent
frames, syntactic equality at ground ones. Two solutions **agree** when they act `E`-alike on every
judged term (`Frames.Agree`). The intended predicates are the **observational** ones, which cannot
tell agreeing solutions apart (`Observational`); the models of a store are observational
(`observational_models`).

## Laws

The frame interface supplies action laws only, not unit and associativity of raw morphisms. So:

* `reindex_id`, `reindex_comp`: reindexing is functorial **on observational predicates**, and
  preserves observationality (`observational_reindex`).
* `Controls.raw_identity_fails`: on a predicate that reads a raw morphism the identity law fails.
* `observational_of_faithful`: on a faithful frame every predicate is observational, so reindexing
  is functorial on all of them.

## Knowledge

* `models_applyStore`: transporting a store along a morphism is reindexing its models.
* `entails_iff_le`: an ask is an inequality in the fibre; `solvable_iff_exists`: solvability is
  inhabitation.
* **Quantifier comparison along a morphism.** What a store asks, its transport asks of the
  precomposed observation (`entails_reindex`), and solvability is reflected (`solvable_of_reindex`):
  only these implications hold in general. Under the lifting property (`Covers`: every solution of
  the store factors through the morphism up to agreement) both become equalities
  (`entails_reindex_iff`, `solvable_reindex_iff`). A principal answer covers its store
  (`covers_of_principal`), and conservative settlement is exactly covering by the settlement
  (`settle_covers`); there the equalities are the tree's `Step.entails_result_iff` and
  `Step.solvable_result_iff`.
* `Controls.ask_needs_cover`, `Controls.solvable_needs_cover`: a morphism that does not cover, with
  each equality failing.

## The step's frame and knowledge changes, in the fibre over the result

* `information_le`: the information refines the starting knowledge along the extension.
* `result_le`: the result refines the information along the settlement; `result_eq` under
  exactness.
* `knowledge_along_le`: the firing's one law, knowledge only refines along it, **derived** from the
  two certificates through the composition law; `run_le`: the same along a run, composite of its
  firings' inequalities.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.SolutionFibration

open Interface
open Mettapedia.OSLF.Framework.DerivedModalities (pb)

universe uO uT uH uOcc uS uF

/-- **Predicates over a frame**: predicates on its solutions. -/
abbrev Pred {Obj : Type uO} (Hom : Obj → Obj → Type uH) (a : Obj) := Frames.Solution Hom a → Prop

section Fibration

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} (X : Frames Tm Hom)

/-- **Precomposition**: a solution of the later frame read as a solution of the earlier one. -/
def restrict {a a' : Obj} (h : Hom a a') (σ : Frames.Solution Hom a') : Frames.Solution Hom a :=
  ⟨σ.1, X.comp σ.2 h⟩

/-- **Reindexing along a frame morphism**: change of base along precomposition. -/
def reindex {a a' : Obj} (h : Hom a a') (φ : Pred Hom a) : Pred Hom a' := pb (restrict X h) φ

/-- **Observational predicates** cannot tell apart solutions that act alike. -/
def Observational {a : Obj} (φ : Pred Hom a) : Prop :=
  ∀ (b : Obj) (f g : Hom a b), X.Agree f g → (φ ⟨b, f⟩ ↔ φ ⟨b, g⟩)

/-- **Reindexing along the identity is the identity**, on observational predicates. -/
theorem reindex_id {a : Obj} {φ : Pred Hom a} (observational : Observational X φ) :
    reindex X (X.id a) φ = φ := by
  funext σ
  obtain ⟨b, f⟩ := σ
  exact propext (observational b _ _ (Frames.agree_id_right (X := X) f))

/-- **Reindexing along a composite is the composite of reindexings**, on observational
predicates. -/
theorem reindex_comp {a a' a'' : Obj} (h : Hom a a') (g : Hom a' a'') {φ : Pred Hom a}
    (observational : Observational X φ) :
    reindex X (X.comp g h) φ = reindex X g (reindex X h φ) := by
  funext σ
  obtain ⟨b, f⟩ := σ
  exact propext (observational b _ _ (Frames.agree_assoc (X := X) h g f).symm)

/-- Reindexing keeps predicates observational. -/
theorem observational_reindex {a a' : Obj} (h : Hom a a') {φ : Pred Hom a}
    (observational : Observational X φ) : Observational X (reindex X h φ) :=
  fun b _ _ same => observational b _ _ (same.comp_right h)

/-- Reindexing is monotone. -/
theorem reindex_mono {a a' : Obj} (h : Hom a a') {φ ψ : Pred Hom a} (le : φ ≤ ψ) :
    reindex X h φ ≤ reindex X h ψ := by
  intro σ holds
  exact le _ holds

/-- **A faithful frame**: morphisms that act alike are equal. -/
def Faithful : Prop := ∀ (a b : Obj) (f g : Hom a b), X.Agree f g → f = g

/-- On a faithful frame every predicate is observational. -/
theorem observational_of_faithful (faithful : Faithful X) {a : Obj} (φ : Pred Hom a) :
    Observational X φ := by
  intro b f g same
  rw [faithful a b f g same]

/-! ## Knowledge -/

/-- **The models of a store**: the predicate its knowledge denotes. -/
def models {a : Obj} (store : EquationStore (Tm a)) : Pred Hom a := fun σ => X.Models σ.2 store

theorem observational_models {a : Obj} (store : EquationStore (Tm a)) :
    Observational X (models X store) :=
  fun _ _ _ same => same.models_iff store

/-- **Transporting a store is reindexing its models.** -/
theorem models_applyStore {a a' : Obj} (h : Hom a a') (store : EquationStore (Tm a)) :
    models X (X.applyStore h store) = reindex X h (models X store) := by
  funext σ
  exact propext (Frames.models_applyStore (X := X) h σ.2 store)

/-- An ask, as a predicate on solutions. -/
def ask {a : Obj} (observation : (b : Obj) → Hom a b → Prop) : Pred Hom a :=
  fun σ => observation σ.1 σ.2

/-- **An ask is an inequality in the fibre.** -/
theorem entails_iff_le {a : Obj} (store : EquationStore (Tm a))
    (observation : (b : Obj) → Hom a b → Prop) :
    X.Entails store observation ↔ models X store ≤ ask observation := by
  constructor
  · intro entails σ solved
    exact entails σ.1 σ.2 solved
  · intro le b f solved
    exact le ⟨b, f⟩ solved

/-- **Solvability is inhabitation of the fibre predicate.** -/
theorem solvable_iff_exists {a : Obj} (store : EquationStore (Tm a)) :
    X.Solvable store ↔ ∃ σ, models X store σ :=
  ⟨fun ⟨b, f, solved⟩ => ⟨⟨b, f⟩, solved⟩, fun ⟨σ, solved⟩ => ⟨σ.1, σ.2, solved⟩⟩

/-- **An ask survives reindexing**: what a store asks, its transport asks of the precomposed
observation. -/
theorem entails_reindex {a a' : Obj} (h : Hom a a') {store : EquationStore (Tm a)}
    {observation : (b : Obj) → Hom a b → Prop} (entails : X.Entails store observation) :
    X.Entails (X.applyStore h store) (fun b σ => observation b (X.comp σ h)) :=
  fun b σ solved => entails b (X.comp σ h) ((Frames.models_applyStore (X := X) h σ store).mp solved)

/-- **Solvability is reflected along every morphism.** -/
theorem solvable_of_reindex {a a' : Obj} (h : Hom a a') {store : EquationStore (Tm a)}
    (solvable : X.Solvable (X.applyStore h store)) : X.Solvable store :=
  Frames.solvable_of_applyStore h solvable

/-- **A morphism covers a store** when every solution of the store factors through it, up to
agreement: the lifting property. -/
def Covers {a a' : Obj} (h : Hom a a') (store : EquationStore (Tm a)) : Prop :=
  ∀ (b : Obj) (f : Hom a b), X.Models f store → ∃ ρ : Hom a' b, X.Agree f (X.comp ρ h)

/-- **A principal answer covers its store.** -/
theorem covers_of_principal {a m : Obj} {store : EquationStore (Tm a)} {answer : Hom a m}
    (principal : X.Principal store answer) : Covers X answer store :=
  fun b f solved => principal.factors b f solved

/-- **Beck–Chevalley for asks, under the lifting property**: a covering morphism's transport asks
exactly what the store asks, of observational asks. -/
theorem entails_reindex_iff {a a' : Obj} {h : Hom a a'} {store : EquationStore (Tm a)}
    (covers : Covers X h store) {observation : (b : Obj) → Hom a b → Prop}
    (observational : Observational X (ask observation)) :
    X.Entails (X.applyStore h store) (fun b σ => observation b (X.comp σ h)) ↔
      X.Entails store observation := by
  constructor
  · intro entails b f solved
    obtain ⟨ρ, agree⟩ := covers b f solved
    have later : X.Models ρ (X.applyStore h store) :=
      (Frames.models_applyStore (X := X) h ρ store).mpr ((agree.models_iff store).mp solved)
    exact (observational b f (X.comp ρ h) agree).mpr (entails b ρ later)
  · exact entails_reindex X h

/-- **Beck–Chevalley for solvability, under the lifting property.** -/
theorem solvable_reindex_iff {a a' : Obj} {h : Hom a a'} {store : EquationStore (Tm a)}
    (covers : Covers X h store) : X.Solvable (X.applyStore h store) ↔ X.Solvable store := by
  constructor
  · exact solvable_of_reindex X h
  · rintro ⟨b, f, solved⟩
    obtain ⟨ρ, agree⟩ := covers b f solved
    exact ⟨b, ρ, (Frames.models_applyStore (X := X) h ρ store).mpr ((agree.models_iff store).mp solved)⟩

end Fibration

/-! ## The step's frame and knowledge changes -/

section Step

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} {X : Frames Tm Hom}
  {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  (P : Interface.Step X O State Firing)

/-- **The information refines the starting knowledge, along the extension.** -/
theorem information_le {s : State} (f : Firing s) :
    models X (P.information f) ≤ reindex X (P.extension f) (models X (P.knowledge s)) := by
  intro σ solved
  exact P.models_knowledge f σ.2 solved

/-- **The result refines the information, along the settlement.** -/
theorem result_le {s : State} {f : Firing s} (admitted : P.Admits f) :
    models X (P.knowledge (P.result f admitted)) ≤
      reindex X (P.settle f admitted) (models X (P.information f)) := by
  intro σ solved
  exact P.result_refines f (P.prepares admitted) σ.2 solved

/-- **Under exactness the result is the information, reindexed along the settlement.** -/
theorem result_eq [P.Exact] {s : State} {f : Firing s} (admitted : P.Admits f) :
    models X (P.knowledge (P.result f admitted)) =
      reindex X (P.settle f admitted) (models X (P.information f)) := by
  funext σ
  exact propext (P.effectCore.models_result_iff P.effectCore_exact f (P.prepares admitted) σ.2)

/-- **A firing only refines knowledge**, as one inequality in the fibre over its result, derived
from the two certificates through the composition law. -/
theorem knowledge_along_le {s : State} {f : Firing s} (admitted : P.Admits f) :
    models X (P.knowledge (P.result f admitted)) ≤
      reindex X (P.along f admitted) (models X (P.knowledge s)) := by
  have composite : reindex X (P.along f admitted) (models X (P.knowledge s)) =
      reindex X (P.settle f admitted) (reindex X (P.extension f) (models X (P.knowledge s))) :=
    reindex_comp X (P.extension f) (P.settle f admitted) (observational_models X (P.knowledge s))
  rw [composite]
  intro σ solved
  exact information_le P f _ (result_le P admitted σ solved)

/-- **Along a run, knowledge only refines**: the composite of its firings' inequalities. -/
theorem run_le : ∀ {s : State} (r : P.Run s),
    models X (P.knowledge r.last) ≤ reindex X r.toLast (models X (P.knowledge s))
  | _, .nil s => by
      intro σ solved
      exact (congrFun (reindex_id X (observational_models X (P.knowledge s))) σ).mpr solved
  | _, .cons f admitted rest => by
      intro σ solved
      have step := knowledge_along_le P admitted _ (run_le rest σ solved)
      exact (congrFun (reindex_comp X (P.along f admitted) rest.toLast
        (observational_models X (P.knowledge _))) σ).mpr step

/-- **Conservative settlement is covering by the settlement.** Under it the comparison of asks
along the settlement is an equality (`Step.entails_result_iff`). -/
theorem settle_covers (conservative : P.ConservativeSettlement) {s : State} {f : Firing s}
    (admitted : P.Admits f) : Covers X (P.settle f admitted) (P.information f) :=
  fun b σ solved => conservative f admitted b σ solved

end Step

/-! ## Controls -/

namespace Controls

/-- **A frame whose morphisms carry a tag the action ignores**; composition always tags. -/
def taggedFrames : Frames (fun _ : Unit => Unit) (fun _ _ : Unit => Bool) where
  E := Eq
  equivalence _ := ⟨fun _ => rfl, fun same => same.symm, fun first second => first.trans second⟩
  act _ t := t
  id _ := false
  comp _ _ := true
  act_id _ := rfl
  act_comp _ _ _ := rfl
  preserves := @fun _ _ _ _ _ same => same

/-- The predicate that reads the tag. -/
def untagged : Pred (fun _ _ : Unit => Bool) () := fun σ => σ.2 = false

/-- **Control: the identity law needs observational predicates.** The predicate that reads the
tag is not observational, and reindexing along the identity changes it. -/
theorem raw_identity_fails :
    ¬ Observational taggedFrames untagged ∧
      reindex taggedFrames (taggedFrames.id ()) untagged ≠ untagged := by
  constructor
  · intro observational
    have bad : true = false := (observational () false true (fun _ => rfl)).mp rfl
    exact absurd bad (by decide)
  · intro same
    have atFalse := congrFun same ⟨(), false⟩
    have bad : true = false := cast atFalse.symm (rfl : false = false)
    exact absurd bad (by decide)

/-- The action of a frame with one declared variable (`none`) and Boolean constants: a morphism
keeps the variable (`none`) or instantiates it by a constant. -/
def bitAct : Option Bool → Option Bool → Option Bool
  | none, t => t
  | some b, none => some b
  | some _, some c => some c

/-- Composition: instantiating first wins. -/
def bitComp (g f : Option Bool) : Option Bool :=
  match f with
  | none => g
  | some b => some b

/-- **The frame of one variable over the Booleans.** -/
def bitFrames : Frames (fun _ : Unit => Option Bool) (fun _ _ : Unit => Option Bool) where
  E := Eq
  equivalence _ := ⟨fun _ => rfl, fun same => same.symm, fun first second => first.trans second⟩
  act := bitAct
  id _ := none
  comp := bitComp
  act_id _ := rfl
  act_comp g f t := by
    cases f <;> cases g <;> cases t <;> rfl
  preserves := @fun _ _ f _ _ same => congrArg (bitAct f) same

/-- The variable is `true` at a solution. -/
def setsTrue (_ : Unit) (f : Option Bool) : Prop := bitAct f none = some true

/-- **Control: the ask comparison needs the lifting property.** Instantiating the variable by
`true` does not cover the empty store: after it the variable is asked to be `true`, before it is
not. -/
theorem ask_needs_cover :
    bitFrames.Entails (a := ()) (bitFrames.applyStore (a := ()) (b := ()) (some true) [])
        (fun b σ => setsTrue b (bitFrames.comp (a := ()) (b := ()) (c := b) σ (some true))) ∧
      ¬ bitFrames.Entails (a := ()) [] setsTrue ∧
      ¬ Covers bitFrames (a := ()) (a' := ()) (some true) [] := by
  refine ⟨fun _ _ _ => rfl, fun entails => ?_, fun covers => ?_⟩
  · have bad : (some false : Option Bool) = some true :=
      entails () (some false) (Frames.models_nil (X := bitFrames) _)
    exact absurd bad (by decide)
  · obtain ⟨ρ, agree⟩ := covers () (some false) (Frames.models_nil (X := bitFrames) _)
    have bad : (some false : Option Bool) = some true := agree none
    exact absurd bad (by decide)

/-- **Control: solvability is not preserved without the lifting property.** The store `x = false`
is solvable; transported along instantiating `x` by `true` it is not. -/
theorem solvable_needs_cover :
    bitFrames.Solvable (a := ()) [(none, some false)] ∧
      ¬ bitFrames.Solvable (a := ())
        (bitFrames.applyStore (a := ()) (b := ()) (some true) [(none, some false)]) := by
  refine ⟨⟨(), some false, fun e member => ?_⟩, ?_⟩
  · rw [List.mem_singleton.mp member]
    exact rfl
  · rintro ⟨b, f, solved⟩
    have here := solved _ (List.mem_map.mpr ⟨(none, some false), List.mem_singleton_self _, rfl⟩)
    cases f with
    | none =>
        have bad : (some true : Option Bool) = some false := here
        exact absurd bad (by decide)
    | some c =>
        have bad : (some true : Option Bool) = some false := here
        exact absurd bad (by decide)

/-- **Positive: the principal answer covers.** Instantiating `x` by `false` is a principal answer
of `x = false`, so the asks of `x = false` are exactly the asks after it. -/
theorem principal_covers :
    bitFrames.Principal (a := ()) (m := ()) [(none, some false)] (some false) ∧
      Covers bitFrames (a := ()) (a' := ()) (some false) [(none, some false)] := by
  have principal : bitFrames.Principal (a := ()) (m := ()) [(none, some false)] (some false) := by
    refine ⟨fun e member => ?_, fun b f solved => ⟨none, fun t => ?_⟩⟩
    · rw [List.mem_singleton.mp member]
      exact rfl
    · have atVar : bitAct f none = bitAct f (some false) := solved _ (List.mem_singleton_self _)
      cases f with
      | none => exact absurd atVar (by decide)
      | some c =>
          have same : c = false := by
            have : (some c : Option Bool) = some false := atVar
            exact Option.some.inj this
          subst same
          cases t <;> exact rfl
  exact ⟨principal, covers_of_principal bitFrames principal⟩

end Controls

#print axioms reindex_id
#print axioms reindex_comp
#print axioms observational_reindex
#print axioms observational_of_faithful
#print axioms observational_models
#print axioms models_applyStore
#print axioms entails_iff_le
#print axioms entails_reindex
#print axioms covers_of_principal
#print axioms entails_reindex_iff
#print axioms solvable_reindex_iff
#print axioms information_le
#print axioms result_le
#print axioms result_eq
#print axioms knowledge_along_le
#print axioms run_le
#print axioms settle_covers
#print axioms Controls.raw_identity_fails
#print axioms Controls.ask_needs_cover
#print axioms Controls.solvable_needs_cover
#print axioms Controls.principal_covers

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.SolutionFibration
