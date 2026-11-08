import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullQueries
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentParameterExchange

/-!
# The diamond of helper firings at dependent frames, up to the telescope swap

**Firings with one fresh helper** (`Natural.withHelper`). A firing of the dependent full step that
makes one helper `x : A` over its state's frame `Γ`, with natural queries, is a firing without
helpers at the frame `Γ.A`, fired at the state carried along the weakening `Γ.A ⟶ Γ`: admission and
result are those of the carried state (`admits_withHelper`, `after_withHelper`). Making a helper is
reading the state at the extended frame.

**Moving a firing along a lift of its telescope** (`residualHelper`). After a helper firing `f`
(`x : A`), a second helper firing `g` (`y : B`) is read at `Γ.A`: its helper type is `B` weakened
past `x` (`ContextualDependentParameterExchange.second`), and its patterns, made rows, tells, guards
and queries are carried along the lift `Γ.A.B ⟶ Γ.B` of the weakening under `y` (`lower`).

**The telescope swap** (`swapIso`): `Γ.A.B ≅ Γ.B.A`, from
`ContextualDependentParameterExchange.swap`. It fixes the old frame, sends the lift of each order to
the projection of the other (`swap_lower`, `swap_projection`, `lower_projection`).

**The diamond up to the swap** (`helper_diamond`). Read both firings at the common frame `Γ.A.B`:
`f` along the projection, `g` along its lift (`atJoint`). When these two firings without helpers are
independent there (`Independent`, from `DependentFullIndependence`) and both helper firings are
admitted, each is admitted after the other, and the composite of `g` after `f` agrees with the
composite of `f` after `g` carried along the swap (`AgreeAlong`): the same present occurrences and
labels, and knowledge with the same solutions. The argument reduces the helper diamond to the
diamond of firings without helpers at `Γ.A.B`.

**When no swap exists** (`residual_made_not_mentions`, `no_residual_of_mentions`). The made rows of
every residual after a helper firing are read along the lift, which never reaches the first helper
`x`. A second firing whose made row's type mentions `x` (for instance `Id A x x`) is therefore the
residual of no firing at the start: the run admits no swap.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace DependentFull

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open ContextualDependentParameterExchange (second context base earlier later swap swap_zero swap_one swap_older
  swap_twice)

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}
  {O : Type}

/-! ## The swap of two helpers -/

section Swap

variable {Γ : Context rules}

/-- **The lift of the weakening past the first helper under the second**: `Γ.A.B ⟶ Γ.B`. -/
def lower (first next : TypeOver Γ) : context first next ⟶ extend Γ next :=
  pair (base first next) (later first next)

theorem lower_projection (first next : TypeOver Γ) :
    lower first next ≫ projectionHom Γ next = base first next :=
  pair_projection _ _

theorem swap_projection (first next : TypeOver Γ) :
    swap first next ≫ projectionHom (extend Γ next) (second next first) = lower first next :=
  pair_projection _ _

theorem lower_zero (first next : TypeOver Γ) : (lower first next).substitution 0 = .var 0 :=
  Term.cast_code _ _

theorem lower_succ (first next : TypeOver Γ) (index : Fin Γ.arity) :
    (lower first next).substitution index.succ = .var index.succ.succ := rfl

/-- **The swap sends the lift of one order to the projection of the other.** -/
theorem swap_lower (first next : TypeOver Γ) :
    swap first next ≫ lower next first = projectionHom (extend Γ first) (second first next) := by
  apply Hom.ext
  funext index
  refine Fin.cases ?_ (fun index => ?_) index
  · change subst (swap first next).substitution ((lower next first).substitution 0) =
      .var (0 : Fin (Γ.arity + 1)).succ
    rw [lower_zero]
    exact swap_zero first next
  · change subst (swap first next).substitution ((lower next first).substitution index.succ) =
      .var index.succ.succ
    rw [lower_succ]
    exact swap_older first next index

/-- **The telescope swap** `Γ.A.B ≅ Γ.B.A`. -/
def swapIso (first next : TypeOver Γ) : context first next ≅ context next first :=
  ⟨swap first next, swap next first, swap_twice first next, swap_twice next first⟩

end Swap

/-! ## Carrying along composites -/

theorem Make.reindex_comp {Δ Δ' Θ : Context rules} (m : Make Δ) (σ : Δ' ⟶ Δ) (ρ : Θ ⟶ Δ') :
    (m.reindex σ).reindex ρ = m.reindex (ρ ≫ σ) :=
  congrArg₂ Make.mk (TypeOver.reindex_comp m.type ρ σ).symm (subst_subComp ρ.substitution σ.substitution m.code)

theorem Local.move_comp {Δ Δ' Θ : Context rules} (σ : Δ' ⟶ Δ) (ρ : Θ ⟶ Δ') (c : Local rules O Δ) :
    (c.move σ).move ρ = c.move (ρ ≫ σ) := by
  refine Local.mk_congr ?_ rfl (funext fun o => (ContextualDependentEta.reindex_comp (c.label o) ρ σ).symm)
  show List.map _ (List.map _ c.knowledge) = List.map _ c.knowledge
  rw [List.map_map]
  refine List.map_congr_left fun e _ => ?_
  show ((e.1.reindex σ).reindex ρ, (e.2.reindex σ).reindex ρ) = (e.1.reindex (ρ ≫ σ), e.2.reindex (ρ ≫ σ))
  rw [ContextualDependentEta.reindex_comp e.1 ρ σ, ContextualDependentEta.reindex_comp e.2 ρ σ]

theorem Natural.move_comp {Δ Δ' Θ : Context rules} (σ : Δ' ⟶ Δ) (ρ : Θ ⟶ Δ')
    (f : Natural levels O Δ) : (f.move σ).move ρ = f.move (ρ ≫ σ) := by
  obtain ⟨taken, read, takes, reads, makes, tells, guards, queries⟩ := f
  simp only [Natural.move, Natural.mk.injEq, List.map_map, applyStore_applyStore, true_and]
  refine ⟨List.map_congr_left fun t _ => act_act σ ρ t, List.map_congr_left fun t _ => act_act σ ρ t,
    List.map_congr_left fun m _ => ?_, List.map_congr_left fun q _ => NaturalQuery.move_comp σ ρ q⟩
  show (m.1, (m.2.reindex σ).reindex ρ) = (m.1, m.2.reindex (ρ ≫ σ))
  rw [Make.reindex_comp]

theorem Plain.after_congr [DecidableEq O] {Δ : Context rules} {f f' : Plain levels O Δ}
    {c c' : Local rules O Δ} (firings : f = f') (states : c = c') (typed : ∀ m ∈ f.makes, m.2.WellTyped)
    (typed' : ∀ m ∈ f'.makes, m.2.WellTyped) : f.after c typed = f'.after c' typed' := by
  subst firings
  subst states
  rfl

theorem Plain.admits_congr [DecidableEq O] {Δ : Context rules} {f f' : Plain levels O Δ}
    {c c' : Local rules O Δ} (firings : f = f') (states : c = c') : f.Admits c ↔ f'.Admits c' := by
  subst firings
  subst states
  rfl

/-- **States that agree along a substitution**: the second, read along it, has the first's present
occurrences and labels, and knowledge with the same solutions. -/
def Local.AgreeAlong {Δ Δ' : Context rules} (σ : Δ' ⟶ Δ) (one : Local rules O Δ') (two : Local rules O Δ) :
    Prop :=
  (frames levels).Equivalent one.knowledge (two.move σ).knowledge ∧ one.present = (two.move σ).present ∧
    one.label = (two.move σ).label

/-! ## Firings with one fresh helper -/

namespace Natural

variable {s : State rules O}

/-- **A firing that makes one fresh helper `x : A`**, with its data at the extended frame. -/
abbrev withHelper (A : TypeOver s.frame) (f : Natural levels O (extend s.frame A)) : Firing levels s :=
  ⟨.cons A (.nil _), f.taken, f.read, f.takes, f.reads, f.makes, f.tells, f.guards,
    f.queries.map NaturalQuery.toQuery⟩

theorem weaken_withHelper (A : TypeOver s.frame) (f : Natural levels O (extend s.frame A)) :
    (withHelper A f).helpers.weaken = projectionHom s.frame A :=
  Category.id_comp _

theorem row_withHelper (A : TypeOver s.frame) (f : Natural levels O (extend s.frame A)) :
    (withHelper A f).row = (s.toLocal.move (projectionHom s.frame A)).label := by
  funext o
  show (frames levels).act (withHelper A f).helpers.weaken (s.label o) = (s.label o).reindex (projectionHom s.frame A)
  rw [weaken_withHelper]
  rfl

theorem information_withHelper (A : TypeOver s.frame) (f : Natural levels O (extend s.frame A)) :
    (withHelper A f).information = f.toPlain.information (s.toLocal.move (projectionHom s.frame A)) := by
  have row := row_withHelper A f
  have weaken := weaken_withHelper A f
  unfold Firing.information Firing.matching
  rw [row, weaken]
  show (frames levels).applyStore (projectionHom s.frame A) s.knowledge ++
      pairs (s.toLocal.move (projectionHom s.frame A)).label f.takes f.taken ++
      pairs (s.toLocal.move (projectionHom s.frame A)).label f.reads f.read ++ f.tells =
    (s.toLocal.move (projectionHom s.frame A)).knowledge ++
      (pairs (s.toLocal.move (projectionHom s.frame A)).label f.takes f.taken ++
        pairs (s.toLocal.move (projectionHom s.frame A)).label f.reads f.read ++ f.tells)
  simp only [List.append_assoc]
  rfl

variable [DecidableEq O]

/-- **Admission of a helper firing is admission of its data at the state carried to the extended
frame.** -/
theorem admits_withHelper (A : TypeOver s.frame) (f : Natural levels O (extend s.frame A)) :
    (withHelper A f).Admits ↔ f.toPlain.Admits (s.toLocal.move (projectionHom s.frame A)) := by
  have information := information_withHelper A f
  have row := row_withHelper A f
  unfold Firing.Admits Firing.Holds
  rw [information, row]
  rfl

theorem toLocal_after_withHelper (A : TypeOver s.frame) (f : Natural levels O (extend s.frame A))
    (first : (withHelper A f).Admits) :
    ((withHelper A f).after first).toLocal =
      f.toPlain.after (s.toLocal.move (projectionHom s.frame A)) first.1.2.2.2.2 :=
  Local.mk_congr (Δ := extend s.frame A) (information_withHelper A f) rfl
    (Plain.relabel_row_congr (Δ := extend s.frame A) (row_withHelper A f) f.makes first.1.2.2.2.2)

/-- **The result of a helper firing is the result of its data at the carried state.** -/
theorem after_withHelper (A : TypeOver s.frame) (f : Natural levels O (extend s.frame A))
    (first : (withHelper A f).Admits) :
    (withHelper A f).after first =
      (f.toPlain.after (s.toLocal.move (projectionHom s.frame A)) first.1.2.2.2.2).toState :=
  congrArg Local.toState (toLocal_after_withHelper A f first)

/-- **The residual of a helper firing after another**: its helper type weakened past the first
helper, its data carried along the lift of its telescope. -/
abbrev residualHelper {A B : TypeOver s.frame} (f : Natural levels O (extend s.frame A))
    (g : Natural levels O (extend s.frame B)) (first : (withHelper A f).Admits) :
    Firing levels ((withHelper A f).after first) :=
  withHelper (s := (withHelper A f).after first) (second A B) (g.move (lower A B))

end Natural

/-! ## The diamond up to the swap -/

section Diamond

variable {s : State rules O}

/-- The two helper firings read at the common frame `Γ.A.B`: the first along the projection of the
second helper, the second along its lift. -/
def atJoint {A B : TypeOver s.frame} (f : Natural levels O (extend s.frame A))
    (g : Natural levels O (extend s.frame B)) :
    Plain levels O (context A B) × Plain levels O (context A B) :=
  ((f.move (projectionHom (extend s.frame A) (second A B))).toPlain, (g.move (lower A B)).toPlain)

theorem joint_state_first (A B : TypeOver s.frame) :
    (s.toLocal.move (projectionHom s.frame A)).move (projectionHom (extend s.frame A) (second A B)) =
      s.toLocal.move (base A B) :=
  Local.move_comp _ _ _

theorem joint_state_second (A B : TypeOver s.frame) :
    (s.toLocal.move (projectionHom s.frame B)).move (lower A B) = s.toLocal.move (base A B) := by
  rw [Local.move_comp, lower_projection]

variable [DecidableEq O]

/-- **The diamond of two helper firings closes up to the telescope swap.** Two admitted helper
firings whose readings at the common frame are independent are each admitted after the other, and
the composite of the second after the first agrees with the composite of the first after the second
carried along the swap. -/
theorem helper_diamond {A B : TypeOver s.frame} {f : Natural levels O (extend s.frame A)}
    {g : Natural levels O (extend s.frame B)} (first : (Natural.withHelper A f).Admits)
    (second' : (Natural.withHelper B g).Admits)
    (independent : Independent (s.toLocal.move (base A B)) (atJoint f g).1 (atJoint f g).2) :
    ∃ (afterFirst : (Natural.residualHelper f g first).Admits)
      (afterSecond : (Natural.residualHelper g f second').Admits),
      Local.AgreeAlong (levels := levels) (swap A B) ((Natural.residualHelper f g first).after afterFirst).toLocal
        ((Natural.residualHelper g f second').after afterSecond).toLocal := by
  have localFirst := (Natural.admits_withHelper A f).mp first
  have localSecond := (Natural.admits_withHelper B g).mp second'
  have jointSolvable := independent.joint_solvable
  -- both readings are admitted at the common frame
  have admitF : (f.move (projectionHom (extend s.frame A) (second A B))).toPlain.Admits (s.toLocal.move (base A B)) := by
    have moved := Natural.admits_move (projectionHom (extend s.frame A) (second A B)) f localFirst (by
      rw [← Natural.information_move]
      refine Frames.solvable_of_subset (fun e member => ?_) jointSolvable
      rw [joint_state_first] at member
      rcases List.mem_append.mp member with known | own
      · exact List.mem_append_left _ (List.mem_append_left _ known)
      · exact List.mem_append_left _ (List.mem_append_right _ own))
    exact (Plain.admits_congr rfl (joint_state_first A B)).mp moved
  have admitG : (g.move (lower A B)).toPlain.Admits (s.toLocal.move (base A B)) := by
    have moved := Natural.admits_move (lower A B) g localSecond (by
      rw [← Natural.information_move]
      refine Frames.solvable_of_subset (fun e member => ?_) jointSolvable
      rw [joint_state_second] at member
      rcases List.mem_append.mp member with known | own
      · exact List.mem_append_left _ (List.mem_append_left _ known)
      · exact List.mem_append_right _ own)
    exact (Plain.admits_congr rfl (joint_state_second A B)).mp moved
  obtain ⟨gAfterF, fAfterG, knowledge, present, label⟩ := local_diamond admitF admitG independent
  -- the state after the first helper firing, carried to the common frame
  have stateOne : ((Natural.withHelper A f).after first).toLocal.move
        (projectionHom (extend s.frame A) (second A B)) =
      (f.move (projectionHom (extend s.frame A) (second A B))).toPlain.after (s.toLocal.move (base A B))
        admitF.1.2.2.2.2 :=
    (congrArg (Local.move (projectionHom (extend s.frame A) (second A B)))
      (Natural.toLocal_after_withHelper A f first)).trans
      ((Natural.after_move (projectionHom (extend s.frame A) (second A B)) f
        (s.toLocal.move (projectionHom s.frame A)) localFirst.1.2.2.2.2 admitF.1.2.2.2.2).symm.trans
        (Plain.after_congr rfl (joint_state_first A B) _ _))
  have stateTwo : ((Natural.withHelper B g).after second').toLocal.move (lower A B) =
      (g.move (lower A B)).toPlain.after (s.toLocal.move (base A B)) admitG.1.2.2.2.2 :=
    (congrArg (Local.move (lower A B)) (Natural.toLocal_after_withHelper B g second')).trans
      ((Natural.after_move (lower A B) g (s.toLocal.move (projectionHom s.frame B)) localSecond.1.2.2.2.2
        admitG.1.2.2.2.2).symm.trans (Plain.after_congr rfl (joint_state_second A B) _ _))
  -- the first firing's residual after the second, read along the swap
  have backFirst : (f.move (lower B A)).move (swap A B) = f.move (projectionHom (extend s.frame A) (second A B)) := by
    rw [Natural.move_comp, swap_lower]
  have backState : (((Natural.withHelper B g).after second').toLocal.move
        (projectionHom (extend s.frame B) (second B A))).move (swap A B) =
      (g.move (lower A B)).toPlain.after (s.toLocal.move (base A B)) admitG.1.2.2.2.2 :=
    (Local.move_comp (projectionHom (extend s.frame B) (second B A)) (swap A B)
      ((Natural.withHelper B g).after second').toLocal).trans
      ((congrArg (fun σ => Local.move σ ((Natural.withHelper B g).after second').toLocal)
        (swap_projection A B)).trans stateTwo)
  have afterFirst : (Natural.residualHelper f g first).Admits :=
    (Natural.admits_withHelper (s := (Natural.withHelper A f).after first) (second A B)
      (g.move (lower A B))).mpr ((Plain.admits_congr rfl stateOne).mpr gAfterF)
  have afterSecond : (Natural.residualHelper g f second').Admits :=
    (Natural.admits_withHelper (s := (Natural.withHelper B g).after second') (second B A)
      (f.move (lower B A))).mpr ((Natural.admits_move_iff (f.move (lower B A)) (swapIso A B) _).mp
        ((Plain.admits_congr (congrArg Natural.toPlain backFirst) backState).mpr fAfterG))
  refine ⟨afterFirst, afterSecond, ?_⟩
  -- the two composites at the common frame
  have one : ((Natural.residualHelper f g first).after afterFirst).toLocal =
      (g.move (lower A B)).toPlain.after
        ((f.move (projectionHom (extend s.frame A) (second A B))).toPlain.after (s.toLocal.move (base A B))
          admitF.1.2.2.2.2) admitG.1.2.2.2.2 :=
    (Natural.toLocal_after_withHelper (s := (Natural.withHelper A f).after first) (second A B)
      (g.move (lower A B)) afterFirst).trans (Plain.after_congr rfl stateOne _ _)
  have two : ((Natural.residualHelper g f second').after afterSecond).toLocal.move (swap A B) =
      (f.move (projectionHom (extend s.frame A) (second A B))).toPlain.after
        ((g.move (lower A B)).toPlain.after (s.toLocal.move (base A B)) admitG.1.2.2.2.2) admitF.1.2.2.2.2 :=
    (congrArg (Local.move (swap A B)) (Natural.toLocal_after_withHelper (s := (Natural.withHelper B g).after second')
      (second B A) (f.move (lower B A)) afterSecond)).trans
      ((Natural.after_move (swap A B) (f.move (lower B A)) _ afterSecond.1.2.2.2.2
        (Natural.shapes_move (swap A B) (f.move (lower B A)) afterSecond.1).2.2.2.2).symm.trans
        (Plain.after_congr (congrArg Natural.toPlain backFirst) backState _ _))
  unfold Local.AgreeAlong
  rw [one, two]
  exact ⟨knowledge, present, label⟩

end Diamond

/-! ## When no swap exists -/

section NoSwap

variable {Γ : Context rules}

/-- Two substitutions of `Γ.A.B` that differ only at the first helper `x`. -/
def keepX (n : Nat) : Sub Head (n + 2) (n + 2) := ids

def moveX (n : Nat) : Sub Head (n + 2) (n + 2) :=
  Fin.cases (.var 0) (Fin.cases (.var 0) fun index => .var index.succ.succ)

/-- **The lift never reaches the first helper**: substituting anything for `x` fixes every code read
along the lift. -/
theorem lower_avoids (first next : TypeOver Γ) (code : Tm Head (Γ.arity + 1)) :
    subst (keepX Γ.arity) (subst (lower first next).substitution code) =
      subst (moveX Γ.arity) (subst (lower first next).substitution code) := by
  rw [subst_subComp, subst_subComp]
  apply subst_ext
  intro index
  refine Fin.cases ?_ (fun index => ?_) index
  · show subst (keepX Γ.arity) ((lower first next).substitution 0) =
      subst (moveX Γ.arity) ((lower first next).substitution 0)
    rw [lower_zero]
    rfl
  · rfl

/-- **A code that mentions the first helper `x` twice, `Id T x x`, is read along no lift.** -/
theorem not_lowered (first next : TypeOver Γ) (T : Tm Head (Γ.arity + 2)) :
    ∀ code : Tm Head (Γ.arity + 1),
      subst (lower first next).substitution code ≠ .id T (.var (0 : Fin (Γ.arity + 1)).succ)
        (.var (0 : Fin (Γ.arity + 1)).succ) := by
  intro code same
  have avoided := lower_avoids first next code
  rw [same] at avoided
  have ends := congrArg (fun t : Tm Head (Γ.arity + 2) => match t with
    | .id _ left _ => left
    | _ => .var 0) avoided
  exact absurd ends (by
    show (Tm.var (0 : Fin (Γ.arity + 1)).succ : Tm Head (Γ.arity + 2)) ≠ .var 0
    exact fun h => by cases h)

variable {s : State rules O} [DecidableEq O]

/-- **Every made row of a residual after a helper firing is read along the lift.** -/
theorem residual_made_lowered {A B : TypeOver s.frame} (f : Natural levels O (extend s.frame A))
    (g : Natural levels O (extend s.frame B)) (first : (Natural.withHelper A f).Admits)
    {m : O × Make (context A B)} (member : m ∈ (Natural.residualHelper f g first).makes) :
    ∃ code : Tm Head (s.frame.arity + 1), m.2.type.code = subst (lower A B).substitution code := by
  obtain ⟨m', -, rfl⟩ := List.mem_map.mp member
  exact ⟨m'.2.type.code, rfl⟩

/-- **No swap when a made row's type mentions the first helper.** After a helper firing `x : A`, a
helper firing that makes a row of type `Id T x x` is the residual of no helper firing at the start. -/
theorem no_residual_of_mentions {A : TypeOver s.frame} (f : Natural levels O (extend s.frame A))
    (first : (Natural.withHelper A f).Admits) (B₁ : TypeOver (extend s.frame A))
    (data : Natural levels O (extend (extend s.frame A) B₁)) (T : Tm Head (s.frame.arity + 2))
    (mentions : ∃ m ∈ data.makes, m.2.type.code = .id T (.var (0 : Fin (s.frame.arity + 1)).succ)
      (.var (0 : Fin (s.frame.arity + 1)).succ)) :
    ∀ (B : TypeOver s.frame) (g : Natural levels O (extend s.frame B)),
      Natural.residualHelper f g first ≠ Natural.withHelper (s := (Natural.withHelper A f).after first) B₁ data := by
  intro B g same
  have helpers := congrArg Firing.helpers same
  have makes := congr_arg_heq Firing.makes same
  obtain ⟨rfl, -⟩ := Helpers.cons.inj helpers
  have makes' := eq_of_heq makes
  obtain ⟨m, member, code⟩ := mentions
  have member' : m ∈ (Natural.residualHelper f g first).makes := by
    rw [makes']
    exact member
  obtain ⟨lowered, eq⟩ := residual_made_lowered f g first member'
  exact not_lowered A B T lowered (eq.symm.trans code)

end NoSwap

end DependentFull

#print axioms DependentFull.lower_projection
#print axioms DependentFull.swap_projection
#print axioms DependentFull.swap_lower
#print axioms DependentFull.swapIso
#print axioms DependentFull.Local.move_comp
#print axioms DependentFull.Natural.move_comp
#print axioms DependentFull.Natural.admits_withHelper
#print axioms DependentFull.Natural.after_withHelper
#print axioms DependentFull.helper_diamond
#print axioms DependentFull.lower_avoids
#print axioms DependentFull.not_lowered
#print axioms DependentFull.residual_made_lowered
#print axioms DependentFull.no_residual_of_mentions

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
