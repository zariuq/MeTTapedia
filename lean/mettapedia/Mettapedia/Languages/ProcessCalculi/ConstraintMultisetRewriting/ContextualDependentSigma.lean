import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUpdateLifting

/-!
# Splitting dependent pair declarations in the typed eta solver

The maps between Gamma,p:Sigma A B and Gamma,a:A,b:B retain the actual
substitution syntax. Beta and eta prove the inverse laws at typed equality,
including the dependent annotation of the second component. A supplied
formed Sigma annotation determines the universe; the maps make no classical
choice of representation or inhabitant.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSigma

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate

variable {Head : Type} {rules : Rules Head}

structure Shape (Γ : Context rules) where
  domain : TypeOver Γ
  codomain : TypeOver (extend Γ domain)
  whole : TypeOver Γ
  code : whole.code = .sigma domain.code codomain.code

theorem inst0_lift {n m : Nat} (solution : Sub Head n m) (value : Tm Head m)
    (body : Tm Head (n + 1)) :
    inst0 value (subst (liftSub solution) body) = subst (consSub value solution) body := by
  unfold inst0
  rw [subst_subComp]
  apply subst_ext
  intro index
  refine Fin.cases rfl (fun index => ?_) index
  exact inst0_rename_wk value (solution index)

namespace Shape

variable {Γ : Context rules} (shape : Shape Γ)

abbrev packed := extend Γ shape.whole
abbrev split := extend (extend Γ shape.domain) shape.codomain

def first {Δ : Context rules} (base : Δ ⟶ Γ) (value : Term Δ (shape.whole.reindex base)) :
    Term Δ (shape.domain.reindex base) := by
  refine ⟨.fst value.code, ?_⟩
  have typed := value.typed
  change Typed rules Δ.raw value.code (subst base.substitution shape.whole.code) at typed
  rw [shape.code] at typed
  exact .fstElim typed

def second {Δ : Context rules} (base : Δ ⟶ Γ) (value : Term Δ (shape.whole.reindex base)) :
    Term Δ (shape.codomain.reindex (pair base (shape.first base value))) := by
  refine ⟨.snd value.code, ?_⟩
  have typed := value.typed
  change Typed rules Δ.raw value.code (subst base.substitution shape.whole.code) at typed
  rw [shape.code] at typed
  have projected := Derivable.sndElim typed
  change Typed rules Δ.raw (.snd value.code)
    (inst0 (.fst value.code) (subst (liftSub base.substitution) shape.codomain.code)) at projected
  rw [inst0_lift] at projected
  exact projected

def makePair {Δ : Context rules} (base : Δ ⟶ Γ) (first : Term Δ (shape.domain.reindex base))
    (second : Term Δ (shape.codomain.reindex (pair base first))) :
    Term Δ (shape.whole.reindex base) := by
  refine ⟨.pair first.code second.code, ?_⟩
  have formed := (shape.whole.reindex base).formed
  change Typed rules Δ.raw (subst base.substitution shape.whole.code) (.head shape.whole.level) at formed
  rw [shape.code] at formed
  have secondTyped := second.typed
  change Typed rules Δ.raw second.code (subst (consSub first.code base.substitution) shape.codomain.code) at secondTyped
  rw [← inst0_lift] at secondTyped
  change Typed rules Δ.raw (.pair first.code second.code) (subst base.substitution shape.whole.code)
  rw [shape.code]
  exact .pairIntro formed shape.whole.universeWitness first.typed secondTyped

def splitBase : shape.split ⟶ Γ :=
  projectionHom (extend Γ shape.domain) shape.codomain ≫ projectionHom Γ shape.domain

def splitFirst : Term shape.split (shape.domain.reindex shape.splitBase) :=
  pulledNewest (projectionHom (extend Γ shape.domain) shape.codomain)

def splitSecond : Term shape.split
    (shape.codomain.reindex (pair shape.splitBase shape.splitFirst)) :=
  (newest (extend Γ shape.domain) shape.codomain).cast
    (congrArg (fun substitution => shape.codomain.reindex substitution)
      (pair_eta (projectionHom (extend Γ shape.domain) shape.codomain))).symm

def pack : shape.split ⟶ shape.packed :=
  pair shape.splitBase (shape.makePair shape.splitBase shape.splitFirst shape.splitSecond)

def unpack : shape.packed ⟶ shape.split :=
  pair (pair (projectionHom Γ shape.whole)
    (shape.first (projectionHom Γ shape.whole) (newest Γ shape.whole)))
    (shape.second (projectionHom Γ shape.whole) (newest Γ shape.whole))

theorem splitFirst_code : shape.splitFirst.code = .var 1 := by
  rw [splitFirst, pulledNewest_code]
  rfl

theorem splitSecond_code : shape.splitSecond.code = .var 0 := by
  exact Term.cast_code _ _

theorem pack_zero : shape.pack.substitution 0 = .pair (.var 1) (.var 0) := by
  change Tm.pair shape.splitFirst.code shape.splitSecond.code = _
  rw [shape.splitFirst_code, shape.splitSecond_code]

theorem pack_succ (index : Fin Γ.arity) :
    shape.pack.substitution index.succ = .var index.succ.succ := rfl

theorem unpack_zero : shape.unpack.substitution 0 = .snd (.var 0) := rfl
theorem unpack_one : shape.unpack.substitution 1 = .fst (.var 0) := rfl
theorem unpack_succ_succ (index : Fin Γ.arity) :
    shape.unpack.substitution index.succ.succ = .var index.succ := rfl

theorem first_beta {Δ : Context rules} (base : Δ ⟶ Γ) (first : Term Δ (shape.domain.reindex base))
    (second : Term Δ (shape.codomain.reindex (pair base first))) :
    Equal rules Δ.raw (.fst (shape.makePair base first second).code) first.code
      (shape.domain.reindex base).code := by
  have formed := (shape.whole.reindex base).formed
  change Typed rules Δ.raw (subst base.substitution shape.whole.code) (.head shape.whole.level) at formed
  rw [shape.code] at formed
  have secondTyped := second.typed
  change Typed rules Δ.raw second.code (subst (consSub first.code base.substitution) shape.codomain.code) at secondTyped
  rw [← inst0_lift] at secondTyped
  exact .betaFst formed shape.whole.universeWitness first.typed secondTyped

theorem second_beta {Δ : Context rules} (base : Δ ⟶ Γ) (first : Term Δ (shape.domain.reindex base))
    (second : Term Δ (shape.codomain.reindex (pair base first))) :
    Equal rules Δ.raw (.snd (shape.makePair base first second).code) second.code
      (shape.codomain.reindex (pair base first)).code := by
  have formed := (shape.whole.reindex base).formed
  change Typed rules Δ.raw (subst base.substitution shape.whole.code) (.head shape.whole.level) at formed
  rw [shape.code] at formed
  have secondTyped := second.typed
  change Typed rules Δ.raw second.code (subst (consSub first.code base.substitution) shape.codomain.code) at secondTyped
  rw [← inst0_lift] at secondTyped
  have equality := Derivable.betaSnd formed shape.whole.universeWitness first.typed secondTyped
  rw [inst0_lift] at equality
  exact equality

theorem eta {Δ : Context rules} (base : Δ ⟶ Γ) (value : Term Δ (shape.whole.reindex base)) :
    Equal rules Δ.raw value.code
      (shape.makePair base (shape.first base value) (shape.second base value)).code
      (shape.whole.reindex base).code := by
  have typed := value.typed
  change Typed rules Δ.raw value.code (subst base.substitution shape.whole.code) at typed
  rw [shape.code] at typed
  have pairTyped := (shape.makePair base (shape.first base value) (shape.second base value)).typed
  change Typed rules Δ.raw _ (subst base.substitution shape.whole.code) at pairTyped
  rw [shape.code] at pairTyped
  change Equal rules Δ.raw _ _ (subst base.substitution shape.whole.code)
  rw [shape.code]
  apply Derivable.etaSigma typed pairTyped
  · exact .symm (shape.first_beta base (shape.first base value) (shape.second base value))
  · have equality := shape.second_beta base (shape.first base value) (shape.second base value)
    change Equal rules Δ.raw _ _ (subst (consSub (.fst value.code) base.substitution) shape.codomain.code) at equality
    rw [← inst0_lift] at equality
    exact .symm equality

theorem pair_split : pair shape.splitBase shape.splitFirst =
    projectionHom (extend Γ shape.domain) shape.codomain := pair_eta _

theorem split_roundtrip : homTypedEquality rules (𝟙 shape.split) (shape.pack ≫ shape.unpack) := by
  refine ⟨(𝟙 shape.split : shape.split ⟶ shape.split).typed, fun index => ?_⟩
  refine Fin.cases ?_ (fun index => Fin.cases ?_ (fun index => ?_) index) index
  · change Equal rules shape.split.raw (.var 0) (.snd (shape.pack.substitution 0))
      (subst ids (Ctx.lookup shape.split.raw 0))
    rw [shape.pack_zero, subst_ids]
    have equality := (shape.second_beta shape.splitBase shape.splitFirst shape.splitSecond).symm
    change Equal rules shape.split.raw shape.splitSecond.code
      (.snd (.pair shape.splitFirst.code shape.splitSecond.code))
      (shape.codomain.reindex (pair shape.splitBase shape.splitFirst)).code at equality
    rw [shape.splitFirst_code, shape.splitSecond_code, shape.pair_split] at equality
    change Equal rules shape.split.raw (.var 0) (.snd (.pair (.var 1) (.var 0)))
      (subst projection shape.codomain.code) at equality
    rw [subst_projection] at equality
    exact equality
  · change Equal rules shape.split.raw (.var 1) (.fst (shape.pack.substitution 0))
      (subst ids (Ctx.lookup shape.split.raw 1))
    rw [shape.pack_zero, subst_ids]
    have equality := (shape.first_beta shape.splitBase shape.splitFirst shape.splitSecond).symm
    change Equal rules shape.split.raw shape.splitFirst.code
      (.fst (.pair shape.splitFirst.code shape.splitSecond.code))
      (subst (subComp projection projection) shape.domain.code) at equality
    rw [shape.splitFirst_code, shape.splitSecond_code, ← subst_subComp,
      subst_projection, subst_projection] at equality
    exact equality
  · change Equal rules shape.split.raw (.var index.succ.succ)
      (shape.pack.substitution index.succ) (subst ids (Ctx.lookup shape.split.raw index.succ.succ))
    rw [shape.pack_succ, subst_ids]
    exact .refl (.var _)

theorem packed_roundtrip : homTypedEquality rules (𝟙 shape.packed) (shape.unpack ≫ shape.pack) := by
  refine ⟨(𝟙 shape.packed : shape.packed ⟶ shape.packed).typed, fun index => ?_⟩
  refine Fin.cases ?_ (fun index => ?_) index
  · change Equal rules shape.packed.raw (.var 0)
      (subst shape.unpack.substitution (shape.pack.substitution 0))
      (subst ids (Ctx.lookup shape.packed.raw 0))
    rw [shape.pack_zero, subst_ids]
    have equality := shape.eta (projectionHom Γ shape.whole) (newest Γ shape.whole)
    change Equal rules shape.packed.raw (.var 0) (.pair (.fst (.var 0)) (.snd (.var 0)))
      (subst projection shape.whole.code) at equality
    rw [subst_projection] at equality
    exact equality
  · change Equal rules shape.packed.raw (.var index.succ)
      (subst shape.unpack.substitution (shape.pack.substitution index.succ))
      (subst ids (Ctx.lookup shape.packed.raw index.succ))
    rw [shape.pack_succ, subst_ids]
    exact .refl (.var _)

variable {L : Type} [UniverseLevel.LevelOrder L] (levels : LevelModel rules L)

theorem factor {Δ : Context rules} (solution : Δ ⟶ shape.packed) (term : TotalTerm shape.packed) :
    (frames levels).E (term.reindex solution) (term.reindex ((solution ≫ shape.unpack) ≫ shape.pack)) := by
  have same := act_equal_of_substEq levels shape.packed_roundtrip term
  rw [reindex_id] at same
  have carried := (frames levels).preserves solution same
  change (frames levels).E (term.reindex solution)
    ((term.reindex (shape.unpack ≫ shape.pack)).reindex solution) at carried
  rw [← reindex_comp, ← Category.assoc] at carried
  exact carried

/-- Splitting retains every equation and factors every original solution,
including its action on later dependent types. -/
def update (problem : EquationStore (TotalTerm shape.packed)) : Update levels problem where
  target := shape.split
  answer := shape.pack
  remaining := (frames levels).applyStore shape.pack problem
  sound := fun Δ residual solved =>
    (Frames.models_applyStore (X := frames levels) shape.pack residual problem).mp solved
  complete := by
    intro Δ solution solved
    refine ⟨solution ≫ shape.unpack, ?_, shape.factor levels solution⟩
    apply (Frames.models_applyStore (X := frames levels) shape.pack _ problem).mpr
    exact (Elimination.models_pointwise levels (shape.factor levels solution) problem).mp solved

theorem fixed_point_solutions_iff (problem : EquationStore (TotalTerm shape.packed))
    (point : Context rules) :
    (∃ solution : point ⟶ shape.packed, (frames levels).Models solution problem) ↔
      ∃ residual : point ⟶ shape.split,
        (frames levels).Models residual ((frames levels).applyStore shape.pack problem) :=
  (shape.update levels problem).fixed_point_solutions_iff point

end Shape
end ContextualDependentSigma
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
