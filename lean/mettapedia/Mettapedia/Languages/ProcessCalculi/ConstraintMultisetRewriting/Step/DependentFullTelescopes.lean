import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullSwap

/-!
# Telescopes of several helpers: lifts, the block exchange, and the diamond

R93 closed the diamond of two firings that make one helper each, up to the swap `Γ.A.B ≅ Γ.B.A`.
This file does the same for firings that make whole telescopes of helpers.

**Lifts of whole telescopes** (`Helpers.reindex`, `Helpers.lift`, `lift_weaken`). A telescope `H`
over `Γ` reindexes along `σ : Δ ⟶ Γ` to a telescope over `Δ`, one helper at a time under the lift of
`σ` (`liftOne`), and `σ` lifts through it to `(H.reindex σ).frame ⟶ H.frame`.

**Reindexed telescopes are pullbacks** (`Helpers.into`, `into_weaken`, `into_lift`, `into_unique`): a
morphism into `Δ` and one into `H.frame` that agree on `Γ` factor uniquely through
`(H.reindex σ).frame`.

**The block exchange** (`exchange`, `exchangeIso`). For two telescopes `H₁, H₂` over `Γ`, the frames
`Γ.H₁.H₂⁺` and `Γ.H₂.H₁⁺` are two pullbacks of one cospan, so they are isomorphic by the unique
comparison, which exchanges the two blocks (`exchange_weaken`, `exchange_lift`). Every morphism with
the same two legs is the exchange (`exchange_unique`); in particular every iterated swap of single
helpers that respects the blocks is it.

**Firings that make telescopes** (`Natural.withHelpers`): a firing with helper telescope `H` and data
at `H.frame` is the helper-free firing of its data at the state carried along `H.weaken`
(`admits_withHelpers`, `toLocal_after_withHelpers`). Its residual after another telescope firing makes
the reindexed telescope and carries its data along the lift (`residualHelpers`).

**The diamond up to the block exchange** (`telescope_diamond`): two admitted telescope firings whose
readings at the common frame `Γ.H₁.H₂⁺` are independent are each admitted after the other, and the
two composites agree along the exchange.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace DependentFull

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}
  {O : Type}

/-! ## Lifting a substitution under a type -/

section Lifts

/-- A morphism into an extended frame is determined by its projection and its newest component. -/
theorem extend_hom_ext {X Γ : Context rules} {A : TypeOver Γ} {f g : X ⟶ extend Γ A}
    (base : f ≫ projectionHom Γ A = g ≫ projectionHom Γ A)
    (newestSame : f.substitution 0 = g.substitution 0) : f = g := by
  apply Hom.ext
  funext index
  refine Fin.cases newestSame (fun index => ?_) index
  exact congrFun (congrArg Hom.substitution base) index

/-- **The lift of a substitution under a type**: `Δ.A[σ] ⟶ Γ.A`. -/
def liftOne {Γ Δ : Context rules} (σ : Δ ⟶ Γ) (A : TypeOver Γ) : extend Δ (A.reindex σ) ⟶ extend Γ A :=
  pair (projectionHom Δ (A.reindex σ) ≫ σ)
    ⟨.var 0, by rw [TypeOver.reindex_comp]; exact (newest Δ (A.reindex σ)).typed⟩

theorem liftOne_projection {Γ Δ : Context rules} (σ : Δ ⟶ Γ) (A : TypeOver Γ) :
    liftOne σ A ≫ projectionHom Γ A = projectionHom Δ (A.reindex σ) ≫ σ :=
  pair_projection _ _

/-- The newest component of a morphism into `Γ.A`, read at the type reindexed along `σ`. -/
def newestAt {X Δ Γ : Context rules} (σ : Δ ⟶ Γ) (A : TypeOver Γ) (a : X ⟶ Δ) (c : X ⟶ extend Γ A)
    (agree : a ≫ σ = c ≫ projectionHom Γ A) : Term X ((A.reindex σ).reindex a) :=
  ⟨c.substitution 0, by
    have typed := (pulledNewest c).typed
    rw [pulledNewest_code, ← agree, TypeOver.reindex_comp] at typed
    exact typed⟩

theorem pair_liftOne {X Δ Γ : Context rules} (σ : Δ ⟶ Γ) (A : TypeOver Γ) (a : X ⟶ Δ) (c : X ⟶ extend Γ A)
    (agree : a ≫ σ = c ≫ projectionHom Γ A) : pair a (newestAt σ A a c agree) ≫ liftOne σ A = c := by
  apply extend_hom_ext
  · rw [Category.assoc, liftOne_projection, ← Category.assoc, pair_projection, agree]
  · rfl

end Lifts

/-! ## Lifts of whole telescopes -/

namespace Helpers

/-- **A telescope reindexed along a substitution**, one helper at a time under the lift. -/
def reindex : {Γ Δ : Context rules} → (σ : Δ ⟶ Γ) → Helpers Γ → Helpers Δ
  | _, Δ, _, .nil _ => .nil Δ
  | _, _, σ, .cons A rest => .cons (A.reindex σ) (reindex (liftOne σ A) rest)

/-- **The lift of a substitution through a telescope**: `(H.reindex σ).frame ⟶ H.frame`. -/
def lift : {Γ Δ : Context rules} → (σ : Δ ⟶ Γ) → (H : Helpers Γ) → (H.reindex σ).frame ⟶ H.frame
  | _, _, σ, .nil _ => σ
  | _, _, σ, .cons A rest => lift (liftOne σ A) rest

theorem length_reindex : ∀ {Γ Δ : Context rules} (σ : Δ ⟶ Γ) (H : Helpers Γ), (H.reindex σ).length = H.length
  | _, _, _, .nil _ => rfl
  | _, _, σ, .cons A rest => congrArg (· + 1) (length_reindex (liftOne σ A) rest)

/-- **The lift covers the substitution**: `lift σ H ≫ H.weaken = (H.reindex σ).weaken ≫ σ`. -/
theorem lift_weaken : ∀ {Γ Δ : Context rules} (σ : Δ ⟶ Γ) (H : Helpers Γ),
    lift σ H ≫ H.weaken = (H.reindex σ).weaken ≫ σ
  | _, _, σ, .nil _ => (Category.comp_id σ).trans (Category.id_comp σ).symm
  | _, _, σ, .cons A rest => by
      show lift (liftOne σ A) rest ≫ (rest.weaken ≫ projectionHom _ A) =
        ((rest.reindex (liftOne σ A)).weaken ≫ projectionHom _ (A.reindex σ)) ≫ σ
      rw [← Category.assoc, lift_weaken (liftOne σ A) rest, Category.assoc, liftOne_projection, Category.assoc]

/-- **Reindexed telescopes are pullbacks**: the factorization of a pair of morphisms that agree on
the old frame. -/
def into : {Γ Δ X : Context rules} → (σ : Δ ⟶ Γ) → (H : Helpers Γ) → (a : X ⟶ Δ) → (b : X ⟶ H.frame) →
    a ≫ σ = b ≫ H.weaken → (X ⟶ (H.reindex σ).frame)
  | _, _, _, _, .nil _, a, _, _ => a
  | _, _, _, σ, .cons A rest, a, b, agree =>
      into (liftOne σ A) rest (pair a (newestAt σ A a (b ≫ rest.weaken) (agree.trans (Category.assoc _ _ _).symm)))
        b (pair_liftOne σ A a _ _)

theorem into_weaken : ∀ {Γ Δ X : Context rules} (σ : Δ ⟶ Γ) (H : Helpers Γ) (a : X ⟶ Δ) (b : X ⟶ H.frame)
    (agree : a ≫ σ = b ≫ H.weaken), into σ H a b agree ≫ (H.reindex σ).weaken = a
  | _, _, _, _, .nil _, a, _, _ => Category.comp_id a
  | _, _, _, σ, .cons A rest, a, b, agree =>
      (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ projectionHom _ (A.reindex σ))
          (into_weaken (liftOne σ A) rest
            (pair a (newestAt σ A a (b ≫ rest.weaken) (agree.trans (Category.assoc _ _ _).symm))) b
            (pair_liftOne σ A a _ _))).trans (pair_projection _ _))

theorem into_lift : ∀ {Γ Δ X : Context rules} (σ : Δ ⟶ Γ) (H : Helpers Γ) (a : X ⟶ Δ) (b : X ⟶ H.frame)
    (agree : a ≫ σ = b ≫ H.weaken), into σ H a b agree ≫ lift σ H = b
  | _, _, _, _, .nil _, _, b, agree => agree.trans (Category.comp_id b)
  | _, _, _, σ, .cons A rest, _, b, _ => into_lift (liftOne σ A) rest _ b _

theorem into_unique : ∀ {Γ Δ X : Context rules} (σ : Δ ⟶ Γ) (H : Helpers Γ) (a : X ⟶ Δ) (b : X ⟶ H.frame)
    (agree : a ≫ σ = b ≫ H.weaken) (m : X ⟶ (H.reindex σ).frame),
    m ≫ (H.reindex σ).weaken = a → m ≫ lift σ H = b → m = into σ H a b agree
  | _, _, _, _, .nil _, _, _, _, m, weakened, _ => (Category.comp_id m).symm.trans weakened
  | _, _, _, σ, .cons A rest, a, b, agree, m, weakened, lifted => by
      have lifted' : m ≫ lift (liftOne σ A) rest = b := lifted
      have same : m ≫ (rest.reindex (liftOne σ A)).weaken =
          pair a (newestAt σ A a (b ≫ rest.weaken) (agree.trans (Category.assoc _ _ _).symm)) := by
        apply extend_hom_ext
        · exact (Category.assoc _ _ _).trans (weakened.trans (pair_projection _ _).symm)
        · have through : (m ≫ (rest.reindex (liftOne σ A)).weaken) ≫ liftOne σ A = b ≫ rest.weaken :=
            (Category.assoc _ _ _).trans ((congrArg (m ≫ ·) (lift_weaken (liftOne σ A) rest).symm).trans
              ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ rest.weaken) lifted')))
          exact congrArg (fun φ => φ.substitution 0) through
      exact into_unique (liftOne σ A) rest _ b _ m same lifted'

end Helpers

/-! ## The block exchange -/

section Exchange

variable {Γ : Context rules}

/-- **The block exchange** `Γ.H₁.H₂⁺ ⟶ Γ.H₂.H₁⁺`: the comparison of two pullbacks of one cospan. -/
def exchange (H₁ H₂ : Helpers Γ) : (H₂.reindex H₁.weaken).frame ⟶ (H₁.reindex H₂.weaken).frame :=
  Helpers.into H₂.weaken H₁ (Helpers.lift H₁.weaken H₂) (H₂.reindex H₁.weaken).weaken
    (Helpers.lift_weaken H₁.weaken H₂)

/-- The exchange sends the lift of one order to the projection of the other. -/
theorem exchange_weaken (H₁ H₂ : Helpers Γ) :
    exchange H₁ H₂ ≫ (H₁.reindex H₂.weaken).weaken = Helpers.lift H₁.weaken H₂ :=
  Helpers.into_weaken _ _ _ _ _

/-- The exchange sends the projection of one order to the lift of the other. -/
theorem exchange_lift (H₁ H₂ : Helpers Γ) :
    exchange H₁ H₂ ≫ Helpers.lift H₂.weaken H₁ = (H₂.reindex H₁.weaken).weaken :=
  Helpers.into_lift _ _ _ _ _

/-- **Every morphism with the exchange's two legs is the exchange.** -/
theorem exchange_unique (H₁ H₂ : Helpers Γ) (m : (H₂.reindex H₁.weaken).frame ⟶ (H₁.reindex H₂.weaken).frame)
    (weakened : m ≫ (H₁.reindex H₂.weaken).weaken = Helpers.lift H₁.weaken H₂)
    (lifted : m ≫ Helpers.lift H₂.weaken H₁ = (H₂.reindex H₁.weaken).weaken) : m = exchange H₁ H₂ :=
  Helpers.into_unique _ _ _ _ _ m weakened lifted

theorem exchange_exchange (H₁ H₂ : Helpers Γ) : exchange H₁ H₂ ≫ exchange H₂ H₁ = 𝟙 _ := by
  have composite := Helpers.into_unique H₁.weaken H₂ (H₂.reindex H₁.weaken).weaken (Helpers.lift H₁.weaken H₂)
    (Helpers.lift_weaken H₁.weaken H₂).symm (exchange H₁ H₂ ≫ exchange H₂ H₁)
    (by rw [Category.assoc, exchange_weaken, exchange_lift])
    (by rw [Category.assoc, exchange_lift, exchange_weaken])
  have identity := Helpers.into_unique H₁.weaken H₂ (H₂.reindex H₁.weaken).weaken (Helpers.lift H₁.weaken H₂)
    (Helpers.lift_weaken H₁.weaken H₂).symm (𝟙 _) (Category.id_comp _) (Category.id_comp _)
  exact composite.trans identity.symm

/-- **The block exchange is an isomorphism** `Γ.H₁.H₂⁺ ≅ Γ.H₂.H₁⁺`. -/
def exchangeIso (H₁ H₂ : Helpers Γ) : (H₂.reindex H₁.weaken).frame ≅ (H₁.reindex H₂.weaken).frame :=
  ⟨exchange H₁ H₂, exchange H₂ H₁, exchange_exchange H₁ H₂, exchange_exchange H₂ H₁⟩

end Exchange

/-! ## Firings that make telescopes -/

namespace Natural

variable {s : State rules O}

/-- **A firing that makes the telescope `H`**, with its data at `H.frame`. -/
abbrev withHelpers (H : Helpers s.frame) (f : Natural levels O H.frame) : Firing levels s :=
  ⟨H, f.taken, f.read, f.takes, f.reads, f.makes, f.tells, f.guards, f.queries.map NaturalQuery.toQuery⟩

theorem row_withHelpers (H : Helpers s.frame) (f : Natural levels O H.frame) :
    (withHelpers H f).row = (s.toLocal.move H.weaken).label :=
  rfl

theorem information_withHelpers (H : Helpers s.frame) (f : Natural levels O H.frame) :
    (withHelpers H f).information = f.toPlain.information (s.toLocal.move H.weaken) := by
  unfold Firing.information Firing.matching
  rw [row_withHelpers]
  show (frames levels).applyStore H.weaken s.knowledge ++
      pairs (s.toLocal.move H.weaken).label f.takes f.taken ++
      pairs (s.toLocal.move H.weaken).label f.reads f.read ++ f.tells =
    (s.toLocal.move H.weaken).knowledge ++
      (pairs (s.toLocal.move H.weaken).label f.takes f.taken ++
        pairs (s.toLocal.move H.weaken).label f.reads f.read ++ f.tells)
  simp only [List.append_assoc]
  rfl

variable [DecidableEq O]

/-- **Admission of a telescope firing is admission of its data at the state carried along the
telescope's weakening.** -/
theorem admits_withHelpers (H : Helpers s.frame) (f : Natural levels O H.frame) :
    (withHelpers H f).Admits ↔ f.toPlain.Admits (s.toLocal.move H.weaken) := by
  have information := information_withHelpers H f
  have row := row_withHelpers H f
  unfold Firing.Admits Firing.Holds
  rw [information, row]
  rfl

theorem toLocal_after_withHelpers (H : Helpers s.frame) (f : Natural levels O H.frame)
    (first : (withHelpers H f).Admits) :
    ((withHelpers H f).after first).toLocal = f.toPlain.after (s.toLocal.move H.weaken) first.1.2.2.2.2 :=
  Local.mk_congr (Δ := H.frame) (information_withHelpers H f) rfl
    (Plain.relabel_row_congr (Δ := H.frame) (row_withHelpers H f) f.makes first.1.2.2.2.2)

/-- **The residual of a telescope firing after another**: the reindexed telescope, and the data
carried along the lift. -/
abbrev residualHelpers {H₁ H₂ : Helpers s.frame} (f : Natural levels O H₁.frame)
    (g : Natural levels O H₂.frame) (first : (withHelpers H₁ f).Admits) :
    Firing levels ((withHelpers H₁ f).after first) :=
  withHelpers (s := (withHelpers H₁ f).after first) (H₂.reindex H₁.weaken) (g.move (Helpers.lift H₁.weaken H₂))

end Natural

/-! ## The diamond up to the block exchange -/

section Diamond

variable {s : State rules O}

/-- The two telescope firings read at the common frame `Γ.H₁.H₂⁺`. -/
def atJointTelescopes {H₁ H₂ : Helpers s.frame} (f : Natural levels O H₁.frame) (g : Natural levels O H₂.frame) :
    Plain levels O (H₂.reindex H₁.weaken).frame × Plain levels O (H₂.reindex H₁.weaken).frame :=
  ((f.move (H₂.reindex H₁.weaken).weaken).toPlain, (g.move (Helpers.lift H₁.weaken H₂)).toPlain)

/-- The common reading of the state at `Γ.H₁.H₂⁺`. -/
abbrev jointState (H₁ H₂ : Helpers s.frame) : Local rules O (H₂.reindex H₁.weaken).frame :=
  s.toLocal.move ((H₂.reindex H₁.weaken).weaken ≫ H₁.weaken)

theorem telescope_state_first (H₁ H₂ : Helpers s.frame) :
    (s.toLocal.move H₁.weaken).move (H₂.reindex H₁.weaken).weaken = jointState H₁ H₂ :=
  Local.move_comp _ _ _

theorem telescope_state_second (H₁ H₂ : Helpers s.frame) :
    (s.toLocal.move H₂.weaken).move (Helpers.lift H₁.weaken H₂) = jointState H₁ H₂ := by
  rw [Local.move_comp, Helpers.lift_weaken]

variable [DecidableEq O]

/-- **The diamond of two telescope firings closes up to the block exchange.** Two admitted firings
that make telescopes `H₁` and `H₂`, whose readings at the common frame are independent, are each
admitted after the other, and the composite of the second after the first agrees with the composite
of the first after the second carried along the exchange. -/
theorem telescope_diamond {H₁ H₂ : Helpers s.frame} {f : Natural levels O H₁.frame}
    {g : Natural levels O H₂.frame} (first : (Natural.withHelpers H₁ f).Admits)
    (second' : (Natural.withHelpers H₂ g).Admits)
    (independent : Independent (jointState H₁ H₂) (atJointTelescopes f g).1
      (atJointTelescopes f g).2) :
    ∃ (afterFirst : (Natural.residualHelpers f g first).Admits)
      (afterSecond : (Natural.residualHelpers g f second').Admits),
      Local.AgreeAlong (levels := levels) (exchange H₁ H₂)
        ((Natural.residualHelpers f g first).after afterFirst).toLocal
        ((Natural.residualHelpers g f second').after afterSecond).toLocal := by
  have localFirst := (Natural.admits_withHelpers H₁ f).mp first
  have localSecond := (Natural.admits_withHelpers H₂ g).mp second'
  have jointSolvable := independent.joint_solvable
  have admitF : (f.move (H₂.reindex H₁.weaken).weaken).toPlain.Admits (jointState H₁ H₂) := by
    have moved := Natural.admits_move (H₂.reindex H₁.weaken).weaken f localFirst (by
      rw [← Natural.information_move]
      refine Frames.solvable_of_subset (fun e member => ?_) jointSolvable
      rw [telescope_state_first] at member
      rcases List.mem_append.mp member with known | own
      · exact List.mem_append_left _ (List.mem_append_left _ known)
      · exact List.mem_append_left _ (List.mem_append_right _ own))
    exact (Plain.admits_congr rfl (telescope_state_first H₁ H₂)).mp moved
  have admitG : (g.move (Helpers.lift H₁.weaken H₂)).toPlain.Admits (jointState H₁ H₂) := by
    have moved := Natural.admits_move (Helpers.lift H₁.weaken H₂) g localSecond (by
      rw [← Natural.information_move]
      refine Frames.solvable_of_subset (fun e member => ?_) jointSolvable
      rw [telescope_state_second] at member
      rcases List.mem_append.mp member with known | own
      · exact List.mem_append_left _ (List.mem_append_left _ known)
      · exact List.mem_append_right _ own)
    exact (Plain.admits_congr rfl (telescope_state_second H₁ H₂)).mp moved
  obtain ⟨gAfterF, fAfterG, knowledge, present, label⟩ := local_diamond admitF admitG independent
  have stateOne : ((Natural.withHelpers H₁ f).after first).toLocal.move (H₂.reindex H₁.weaken).weaken =
      (f.move (H₂.reindex H₁.weaken).weaken).toPlain.after (jointState H₁ H₂)
        admitF.1.2.2.2.2 :=
    (congrArg (Local.move (H₂.reindex H₁.weaken).weaken) (Natural.toLocal_after_withHelpers H₁ f first)).trans
      ((Natural.after_move (H₂.reindex H₁.weaken).weaken f (s.toLocal.move H₁.weaken) localFirst.1.2.2.2.2
        admitF.1.2.2.2.2).symm.trans (Plain.after_congr rfl (telescope_state_first H₁ H₂) _ _))
  have stateTwo : ((Natural.withHelpers H₂ g).after second').toLocal.move (Helpers.lift H₁.weaken H₂) =
      (g.move (Helpers.lift H₁.weaken H₂)).toPlain.after (jointState H₁ H₂)
        admitG.1.2.2.2.2 :=
    (congrArg (Local.move (Helpers.lift H₁.weaken H₂)) (Natural.toLocal_after_withHelpers H₂ g second')).trans
      ((Natural.after_move (Helpers.lift H₁.weaken H₂) g (s.toLocal.move H₂.weaken) localSecond.1.2.2.2.2
        admitG.1.2.2.2.2).symm.trans (Plain.after_congr rfl (telescope_state_second H₁ H₂) _ _))
  have backFirst : (f.move (Helpers.lift H₂.weaken H₁)).move (exchange H₁ H₂) =
      f.move (H₂.reindex H₁.weaken).weaken := by
    rw [Natural.move_comp, exchange_lift]
  have backState : (((Natural.withHelpers H₂ g).after second').toLocal.move
        (H₁.reindex H₂.weaken).weaken).move (exchange H₁ H₂) =
      (g.move (Helpers.lift H₁.weaken H₂)).toPlain.after (jointState H₁ H₂)
        admitG.1.2.2.2.2 :=
    (Local.move_comp (H₁.reindex H₂.weaken).weaken (exchange H₁ H₂)
      ((Natural.withHelpers H₂ g).after second').toLocal).trans
      ((congrArg (fun σ => Local.move σ ((Natural.withHelpers H₂ g).after second').toLocal)
        (exchange_weaken H₁ H₂)).trans stateTwo)
  have afterFirst : (Natural.residualHelpers f g first).Admits :=
    (Natural.admits_withHelpers (s := (Natural.withHelpers H₁ f).after first) (H₂.reindex H₁.weaken)
      (g.move (Helpers.lift H₁.weaken H₂))).mpr ((Plain.admits_congr rfl stateOne).mpr gAfterF)
  have afterSecond : (Natural.residualHelpers g f second').Admits :=
    (Natural.admits_withHelpers (s := (Natural.withHelpers H₂ g).after second') (H₁.reindex H₂.weaken)
      (f.move (Helpers.lift H₂.weaken H₁))).mpr
      ((Natural.admits_move_iff (f.move (Helpers.lift H₂.weaken H₁)) (exchangeIso H₁ H₂) _).mp
        ((Plain.admits_congr (congrArg Natural.toPlain backFirst) backState).mpr fAfterG))
  refine ⟨afterFirst, afterSecond, ?_⟩
  have one : ((Natural.residualHelpers f g first).after afterFirst).toLocal =
      (g.move (Helpers.lift H₁.weaken H₂)).toPlain.after
        ((f.move (H₂.reindex H₁.weaken).weaken).toPlain.after (jointState H₁ H₂)
          admitF.1.2.2.2.2) admitG.1.2.2.2.2 :=
    (Natural.toLocal_after_withHelpers (s := (Natural.withHelpers H₁ f).after first) (H₂.reindex H₁.weaken)
      (g.move (Helpers.lift H₁.weaken H₂)) afterFirst).trans (Plain.after_congr rfl stateOne _ _)
  have two : ((Natural.residualHelpers g f second').after afterSecond).toLocal.move (exchange H₁ H₂) =
      (f.move (H₂.reindex H₁.weaken).weaken).toPlain.after
        ((g.move (Helpers.lift H₁.weaken H₂)).toPlain.after (jointState H₁ H₂)
          admitG.1.2.2.2.2) admitF.1.2.2.2.2 :=
    (congrArg (Local.move (exchange H₁ H₂))
      (Natural.toLocal_after_withHelpers (s := (Natural.withHelpers H₂ g).after second') (H₁.reindex H₂.weaken)
        (f.move (Helpers.lift H₂.weaken H₁)) afterSecond)).trans
      ((Natural.after_move (exchange H₁ H₂) (f.move (Helpers.lift H₂.weaken H₁)) _ afterSecond.1.2.2.2.2
        (Natural.shapes_move (exchange H₁ H₂) (f.move (Helpers.lift H₂.weaken H₁)) afterSecond.1).2.2.2.2).symm.trans
        (Plain.after_congr (congrArg Natural.toPlain backFirst) backState _ _))
  unfold Local.AgreeAlong
  rw [one, two]
  exact ⟨knowledge, present, label⟩

end Diamond

end DependentFull

#print axioms DependentFull.extend_hom_ext
#print axioms DependentFull.liftOne
#print axioms DependentFull.pair_liftOne
#print axioms DependentFull.Helpers.reindex
#print axioms DependentFull.Helpers.lift_weaken
#print axioms DependentFull.Helpers.into_weaken
#print axioms DependentFull.Helpers.into_lift
#print axioms DependentFull.Helpers.into_unique
#print axioms DependentFull.exchange_weaken
#print axioms DependentFull.exchange_lift
#print axioms DependentFull.exchange_unique
#print axioms DependentFull.exchange_exchange
#print axioms DependentFull.exchangeIso
#print axioms DependentFull.Natural.admits_withHelpers
#print axioms DependentFull.Natural.toLocal_after_withHelpers
#print axioms DependentFull.telescope_diamond

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
