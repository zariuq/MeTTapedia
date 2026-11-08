import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFibre
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.UniverseProfiles

/-!
# Packing telescopes: the simple fibre for every store

**Retracts** (`Frames.HasRetract`): a frame `b` has a retract inside when some frame `c` inside has
morphisms both ways whose composite acts as the identity up to the equivalence. When every frame
has one, solvability and asks of equality guards are the same in the sub-instance and in the
whole instance, for every store (`restrict_solvable_iff_of_retracts`,
`restrict_entails_models_iff_of_retracts`).

**Packing** (`packing`): when the universe heads have joins, every formed telescope is a retract of
a frame with at most one variable of a closed type. The variables are packed into one variable of an
iterated Σ-type: `pack` pairs them, `unpack` projects them, and unpacking after packing reduces to
the identity by β for Σ, so it is the identity up to conversion. No η for pairs is used.

**The fibre theorem for every store** (`simpleStep_admits_iff_of_joins`): with joins, a firing of the
simple step is admitted exactly when its underlying dependent firing is, whatever the knowledge.

Controls over `Consumer.tiny`: its universe has joins, so the theorem holds there with no further
hypothesis (`Consumer.tiny_fibre`); the frame `x : g → g, y : Id (g → g) x x` is not simple and is a
retract of a simple frame (`Consumer.dependent_frame_packed`). The candidate's universe tower has joins,
so the theorem holds there too (`tower_fibre`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)

namespace Frames

universe uO uT uH

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

variable (X : Frames Tm Hom) (Inside : Obj → Prop) in
/-- **A retract inside**: a frame inside with morphisms both ways whose composite acts as the
identity, up to the equivalence. -/
def HasRetract (b : Obj) : Prop :=
  ∃ (c : Obj) (_ : Inside c) (down : Hom b c) (up : Hom c b),
    ∀ t : Tm b, X.E (X.act (X.comp up down) t) t

variable {X : Frames Tm Hom} {Inside : Obj → Prop}

/-- **With retracts everywhere, solvability is preserved and reflected** for every store. -/
theorem restrict_solvable_iff_of_retracts (retracts : ∀ b, HasRetract X Inside b)
    {a : {a : Obj // Inside a}} (store : EquationStore (Tm a.1)) :
    (X.restrict Inside).Solvable (a := a) store ↔ X.Solvable store := by
  refine ⟨restrict_solvable, ?_⟩
  rintro ⟨b, f, solved⟩
  obtain ⟨c, inside, down, -, -⟩ := retracts b
  exact ⟨⟨c, inside⟩, X.comp down f, models_comp solved down⟩

/-- **With retracts everywhere, asks of equality guards are preserved and reflected** for every
store. -/
theorem restrict_entails_models_iff_of_retracts (retracts : ∀ b, HasRetract X Inside b)
    {a : {a : Obj // Inside a}} (store guards : EquationStore (Tm a.1)) :
    (X.restrict Inside).Entails (a := a) store (fun _ f => (X.restrict Inside).Models f guards) ↔
      X.Entails store (fun _ f => X.Models f guards) := by
  refine ⟨fun asked b f solved => ?_, fun asked b f solved => asked b.1 f solved⟩
  obtain ⟨c, inside, down, up, retract⟩ := retracts b
  have inner : X.Models (X.comp down f) guards :=
    asked ⟨c, inside⟩ (X.comp down f) (models_comp solved down)
  refine (models_congrE (fun t => ?_) guards).mp (models_comp inner up)
  rw [X.act_comp, X.act_comp, ← X.act_comp up down]
  exact retract (X.act f t)

end Frames

namespace Dependent

open _root_.CategoryTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveContextual

variable {Head : Type} {rules : Rules Head}

/-! ## Raw facts about closed terms -/

/-- Every substitution acts alike on a closed term. -/
theorem closed_subst_eq {m : Nat} (σ τ : Sub Head 0 m) (T : Tm Head 0) : subst σ T = subst τ T := by
  rw [show σ = τ from funext fun i => i.elim0]

/-- A typed term at a convertible formed type. -/
def convertTerm {Γ : Context rules} {A : TypeOver Γ} (t : Term Γ A) (B : TypeOver Γ)
    (conversion : Conv rules.headEq A.code B.code rules.computation) : Term Γ B :=
  ⟨t.code, .conv t.typed B.formed B.universeWitness conversion⟩

/-! ## Retractions up to conversion -/

theorem retract_pointwise {Y Δ X : Context rules} (σ : Y ⟶ Δ) {pack : Δ ⟶ X} {unpack : X ⟶ Δ}
    (retract : ∀ i, Conv rules.headEq ((pack ≫ unpack).substitution i) (.var i) rules.computation) :
    ∀ i, Conv rules.headEq (((σ ≫ pack) ≫ unpack).substitution i) (σ.substitution i) rules.computation := by
  intro i
  rw [Category.assoc]
  exact Conv.substitute σ.substitution (retract i)

theorem retract_type_conv {Y Δ X : Context rules} (B : TypeOver Δ) (σ : Y ⟶ Δ) {pack : Δ ⟶ X}
    {unpack : X ⟶ Δ}
    (retract : ∀ i, Conv rules.headEq ((pack ≫ unpack).substitution i) (.var i) rules.computation) :
    Conv rules.headEq ((B.reindex unpack).reindex (σ ≫ pack)).code (B.reindex σ).code rules.computation := by
  show Conv rules.headEq (subst (σ ≫ pack).substitution (subst unpack.substitution B.code))
    (subst σ.substitution B.code) rules.computation
  rw [subst_subComp]
  exact Conv.substitutePointwise (retract_pointwise σ retract) B.code

/-! ## Packing -/

/-- The packed frame: no variable, or one variable of a closed type. -/
abbrev packed : Option (TypeOver (empty rules)) → Context rules
  | none => empty rules
  | some T => extend (empty rules) T

theorem packed_simple : ∀ T : Option (TypeOver (empty rules)), Simple (packed T)
  | none => simple_empty
  | some T => by
      have same : T.reindex (toEmpty (empty rules)) = T := by
        rw [← toEmpty_unique _ (𝟙 _), TypeOver.reindex_id]
      have simple := simple_extend (simple_empty (rules := rules)) T
      rw [same] at simple
      exact simple

variable (joins : ∀ {u v : Head}, rules.isUniverse u → rules.isUniverse v →
  ∃ w, rules.join u v w ∧ rules.isUniverse w)

include joins in
/-- **One packing step**: a packing of `Δ` extends to a packing of `Δ.B`. Over no variable, the new
variable is `B` read at the closed point; over one variable `w : T₀`, the two are paired into
`Σ (w : T₀). B`. -/
theorem packing_step {Δ : Context rules} (B : TypeOver Δ) {T : Option (TypeOver (empty rules))}
    (unpack₀ : packed T ⟶ Δ) (pack₀ : Δ ⟶ packed T)
    (retract₀ : ∀ i, Conv rules.headEq ((pack₀ ≫ unpack₀).substitution i) (.var i) rules.computation) :
    ∃ (T' : Option (TypeOver (empty rules))) (unpack : packed T' ⟶ extend Δ B)
      (pack : extend Δ B ⟶ packed T'),
      ∀ i, Conv rules.headEq ((pack ≫ unpack).substitution i) (.var i) rules.computation := by
  cases T with
  | none =>
      refine ⟨some (B.reindex unpack₀), lift unpack₀ rfl,
        pair (projectionHom Δ B ≫ pack₀)
          (convertTerm (newest Δ B) _ (.symm _ _ (retract_type_conv B (projectionHom Δ B) retract₀))),
        fun i => ?_⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · show Conv rules.headEq (subst _ ((lift unpack₀ rfl).substitution 0)) (.var 0) rules.computation
        rw [lift_zero]
        exact .refl _
      · show Conv rules.headEq (((pair (projectionHom Δ B ≫ pack₀)
            (convertTerm (newest Δ B) _ (.symm _ _ (retract_type_conv B (projectionHom Δ B) retract₀))) ≫
              lift unpack₀ rfl) ≫ projectionHom Δ B).substitution j) (.var j.succ) rules.computation
        rw [Category.assoc, lift_projection, ← Category.assoc, pair_projection]
        exact retract_pointwise (projectionHom Δ B) retract₀ j
  | some T₀ =>
      obtain ⟨w, join, universeW⟩ := joins T₀.universeWitness (B.reindex unpack₀).universeWitness
      let sigmaType : TypeOver (empty rules) :=
        ⟨.sigma T₀.code (B.reindex unpack₀).code, w, universeW,
          .sigmaForm T₀.formed T₀.universeWitness (B.reindex unpack₀).formed
            (B.reindex unpack₀).universeWitness join⟩
      have fstTyped : FormationSensitive.Typing rules (extend (empty rules) sigmaType).raw
          (.fst (newest (empty rules) sigmaType).code)
          (subst (toEmpty (extend (empty rules) sigmaType)).substitution T₀.code) := by
        convert FormationSensitive.Typing.fstElim (newest (empty rules) sigmaType).typed using 1
        exact closed_subst_eq _ _ T₀.code
      let fstMap : extend (empty rules) sigmaType ⟶ extend (empty rules) T₀ :=
        pair (toEmpty _) ⟨.fst (newest (empty rules) sigmaType).code, fstTyped⟩
      have sndTyped : FormationSensitive.Typing rules (extend (empty rules) sigmaType).raw
          (.snd (newest (empty rules) sigmaType).code) (subst (fstMap ≫ unpack₀).substitution B.code) := by
        convert FormationSensitive.Typing.sndElim (newest (empty rules) sigmaType).typed using 1
        rw [inst0, subst_subComp]
        exact (subst_subComp _ _ _).symm.trans (congrArg (fun σ => subst σ (B.reindex unpack₀).code)
          (funext fun i => Fin.cases rfl (fun j => j.elim0) i))
      let unpack : extend (empty rules) sigmaType ⟶ extend Δ B :=
        pair (fstMap ≫ unpack₀) ⟨.snd (newest (empty rules) sigmaType).code, sndTyped⟩
      let ρ : extend Δ B ⟶ extend (empty rules) T₀ := projectionHom Δ B ≫ pack₀
      have firstType : (T₀.reindex (pack₀ ≫ projectionHom (empty rules) T₀)).reindex (projectionHom Δ B) =
          T₀.reindex (toEmpty (extend Δ B)) := by
        rw [← TypeOver.reindex_comp,
          toEmpty_unique _ (projectionHom Δ B ≫ pack₀ ≫ projectionHom (empty rules) T₀)]
      let first : Term (extend Δ B) (T₀.reindex (toEmpty (extend Δ B))) :=
        ((pulledNewest pack₀).reindex (projectionHom Δ B)).cast firstType
      have firstCode : first.code = ρ.substitution 0 := by
        show (((pulledNewest pack₀).reindex (projectionHom Δ B)).cast firstType).code = _
        rw [Term.cast_code]
        exact congrArg (subst projection) (pulledNewest_code pack₀)
      have secondType : inst0 first.code (subst (liftSub (toEmpty (extend Δ B)).substitution)
          (B.reindex unpack₀).code) = ((B.reindex unpack₀).reindex ρ).code := by
        rw [← subst_consSub]
        exact congrArg (fun σ => subst σ (B.reindex unpack₀).code)
          (funext fun i => Fin.cases firstCode (fun j => j.elim0) i)
      let second : Term (extend Δ B) ((B.reindex unpack₀).reindex ρ) :=
        convertTerm (newest Δ B) _ (.symm _ _ (retract_type_conv B (projectionHom Δ B) retract₀))
      have secondTyped : FormationSensitive.Typing rules (extend Δ B).raw second.code
          (inst0 first.code (subst (liftSub (toEmpty (extend Δ B)).substitution) (B.reindex unpack₀).code)) := by
        rw [secondType]
        exact second.typed
      let pack : extend Δ B ⟶ extend (empty rules) sigmaType :=
        pair (toEmpty _) ⟨.pair first.code second.code,
          .pairIntro (sigmaType.reindex (toEmpty (extend Δ B))).formed universeW first.typed secondTyped⟩
      have unpackProjection : unpack ≫ projectionHom Δ B = fstMap ≫ unpack₀ := pair_projection _ _
      have firstConv : ∀ k, Conv rules.headEq ((pack ≫ fstMap).substitution k) (ρ.substitution k)
          rules.computation :=
        fun k => Fin.cases (.trans _ _ _ (.rel _ _ (.betaSigmaFst _ _)) (by rw [firstCode]; exact .refl _))
          (fun j => j.elim0) k
      refine ⟨some sigmaType, unpack, pack, fun i => ?_⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · exact .rel _ _ (.betaSigmaSnd _ _)
      · show Conv rules.headEq (((pack ≫ unpack) ≫ projectionHom Δ B).substitution j) (.var j.succ)
          rules.computation
        rw [Category.assoc, unpackProjection, ← Category.assoc]
        exact .trans _ _ _ (Conv.substitutePointwise firstConv (unpack₀.substitution j))
          (retract_pointwise (projectionHom Δ B) retract₀ j)

include joins in
/-- **Packing**: with joins, every formed telescope is a retract, up to conversion, of a frame with
at most one variable of a closed type. -/
theorem packing : ∀ {n : Nat} {Γ : Ctx Head n} (formed : FormationSensitive.ContextFormation rules Γ),
    ∃ (T : Option (TypeOver (empty rules))) (unpack : packed T ⟶ (⟨n, Γ, formed⟩ : Context rules))
      (pack : (⟨n, Γ, formed⟩ : Context rules) ⟶ packed T),
      ∀ i, Conv rules.headEq ((pack ≫ unpack).substitution i) (.var i) rules.computation := by
  intro n Γ formed
  induction formed with
  | nil => exact ⟨none, 𝟙 _, 𝟙 _, fun i => i.elim0⟩
  | @snoc n Γ A u formedΓ typed universeA ih =>
      obtain ⟨T, unpack₀, pack₀, retract₀⟩ := ih
      exact packing_step joins (Δ := ⟨n, Γ, formedΓ⟩) ⟨A, u, universeA, typed⟩ unpack₀ pack₀ retract₀

include joins in
/-- **Every dependent frame has a simple retract**, when universes have joins. -/
theorem simple_retracts : ∀ Δ : Context rules, Frames.HasRetract (frames rules) Simple Δ := by
  intro Δ
  obtain ⟨T, unpack, pack, retract⟩ := packing joins Δ.formed
  refine ⟨packed T, packed_simple T, unpack, pack, fun t => ?_⟩
  have moved := convertible_reindex_of_pointwise (τ := 𝟙 Δ) retract t
  rw [Entry.reindex_id] at moved
  exact moved

variable {O : Type} [DecidableEq O]

include joins in
/-- **The fibre theorem for every store**: with joins, a firing of the simple step is admitted
exactly when its underlying dependent firing is admitted. -/
theorem simpleStep_admits_iff_of_joins {s : SimpleState rules O} (f : SimpleFiring s) :
    (simpleStep (rules := rules) (O := O)).Admits f ↔ (helperStep (rules := rules)).Admits f.firing := by
  have holds : ∀ {b : Context rules} (σ : b ⟶ extend s.state.frame f.firing.helper),
      (frames rules).Models ((frames rules).comp σ (projectionHom s.state.frame f.firing.helper))
          f.firing.guards ↔
        (frames rules).Models σ
          ((frames rules).applyStore (projectionHom s.state.frame f.firing.helper) f.firing.guards) :=
    fun σ => (Frames.models_applyStore (X := frames rules) _ σ _).symm
  have solvable := Frames.restrict_solvable_iff_of_retracts (simple_retracts joins)
    (a := ⟨extend s.state.frame f.firing.helper, f.simple_after⟩) f.firing.information
  have asks := Frames.restrict_entails_models_iff_of_retracts (simple_retracts joins)
    (a := ⟨extend s.state.frame f.firing.helper, f.simple_after⟩) f.firing.information
    ((frames rules).applyStore (projectionHom s.state.frame f.firing.helper) f.firing.guards)
  have fibreAsks :
      (simpleFrames rules).Entails (a := ⟨extend _ f.firing.helper, f.simple_after⟩) f.firing.information
          (fun _ σ => (frames rules).Models ((frames rules).comp σ (projectionHom s.state.frame f.firing.helper))
            f.firing.guards) ↔
        (frames rules).Entails f.firing.information
          (fun _ σ => (frames rules).Models ((frames rules).comp σ (projectionHom s.state.frame f.firing.helper))
            f.firing.guards) :=
    ⟨fun asked => (asks.mp fun b σ solved => (holds σ).mp (asked b σ solved)).mono
        fun _ σ moved => (holds σ).mpr moved,
      fun asked b σ solved => asked b.1 σ solved⟩
  exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr solvable fibreAsks))

/-! ## Controls -/

namespace Consumer

theorem tiny_joins : ∀ {u v : TinyHead}, tiny.isUniverse u → tiny.isUniverse v →
    ∃ w, tiny.join u v w ∧ tiny.isUniverse w :=
  fun hu hv => ⟨.universe, ⟨hu, hv, rfl⟩, rfl⟩

/-- **Over `tiny` the simple fibre decides admission exactly**, for every store. -/
theorem tiny_fibre {s : SimpleState tiny Nat} (f : SimpleFiring s) :
    (simpleStep (rules := tiny) (O := Nat)).Admits f ↔ (helperStep (rules := tiny)).Admits f.firing :=
  simpleStep_admits_iff_of_joins tiny_joins f

/-- **A dependent frame packs**: `x : g → g, y : Id (g → g) x x` is not simple, and is a retract of a
simple frame. -/
theorem dependent_frame_packed :
    ¬ Simple (extend first.after.frame dependent.helper) ∧
      Frames.HasRetract (frames tiny) Simple (extend first.after.frame dependent.helper) :=
  ⟨dependent_leaves_fibre, simple_retracts tiny_joins _⟩

end Consumer

/-! ## The candidate's universe tower -/

/-- The tower's universes have joins: the maximum of two levels. -/
theorem tower_joins : ∀ {u v : Tower.Head}, Tower.rules.isUniverse u → Tower.rules.isUniverse v →
    ∃ w, Tower.rules.join u v w ∧ Tower.rules.isUniverse w := by
  intro u v hu hv
  cases hu with
  | sort left =>
      cases hv with
      | sort right => exact ⟨_, LevelTower.Join.sorts left right, LevelTower.IsUniverse.sort _⟩

/-- **Over the candidate's universe tower the simple fibre decides admission exactly**, for every
store. -/
theorem tower_fibre {O : Type} [DecidableEq O] {s : SimpleState Tower.rules O} (f : SimpleFiring s) :
    (simpleStep (rules := Tower.rules) (O := O)).Admits f ↔ (helperStep (rules := Tower.rules)).Admits f.firing :=
  simpleStep_admits_iff_of_joins tower_joins f

end Dependent

#print axioms Frames.restrict_solvable_iff_of_retracts
#print axioms Frames.restrict_entails_models_iff_of_retracts
#print axioms Dependent.packing_step
#print axioms Dependent.packing
#print axioms Dependent.simple_retracts
#print axioms Dependent.simpleStep_admits_iff_of_joins
#print axioms Dependent.Consumer.tiny_fibre
#print axioms Dependent.Consumer.dependent_frame_packed
#print axioms Dependent.tower_joins
#print axioms Dependent.tower_fibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
