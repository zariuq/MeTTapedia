import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EqualityOnTheStep.Codes

/-!
# Two sets with the same members are made equal by a firing, and a program transports along it

A run of `Interface.DependentFull.step` over the frame `X : U0, x : X, g : Ground`, on the sets
`S = λX. Σ X Ground` and `T = λX. Σ Ground X` of `ProgrammingOnTheStep.SetExtensionality`.

* **The start** (`start`): the two swaps of that module as rows `0` and `1`, and the member
  `(x, g) : X ∈ S` as row `2`. There is no knowledge.
* **The extensionality rule** (`extFiring`, `ext_admitted`): it reads the two swaps with the patterns
  `f : Π X. S X → T X` and `g : Π X. T X → S X` (fresh helpers) and makes row `3`,
  `λX. (f X, g X) : setEq S T`. The made row is typed in the bare frame, from the helpers' types;
  the knowledge learns only `f ≐ swap` and `g ≐ swapBack` (`equality_from_swaps`).
* **The transport rule** (`transFiring`, `trans_admitted`): over fresh helpers `a : U0`,
  `s t : U0 → U0`, `e : setEq s t`, `m : s a`, it reads the equality row with `e` and the member with
  `m`, and makes row `4`, `fst (e a) m : t a`. It is one rule for all sets and all members; the
  solution reads `s, t, a` as `S, T, X` (`transported_row`).
* **The run** (`extensionalityRun`): both firings, in order.
* **The knowledge is unchanged in kind** (`tellAtEnd_refused`): in the last state, after the equality
  row and the transported member exist, telling `S ≐ T` is still refused, as in
  `SetExtensionality.extensionality_refused`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace EqualityOnTheStep.Run

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull Interface.DependentFull.Controls
open ProgrammingOnTheStep.SetExtensionality (small U0 sCode tCode setType swapCode swapType
  swapBackType setType_formed s_typed t_typed swap_typed swapBack_typed)

/-! ## Types over frames -/

/-- A type of `U1` over a frame. -/
def largeType (Γ : Context Tower.rules) (code : Tower.Tm Γ.arity)
    (formed : Typed Tower.rules Γ.raw code (.head large)) : TypeOver Γ :=
  ⟨code, large, .sort _, formed⟩

/-- A type of `U0` over a frame. -/
def smallType (Γ : Context Tower.rules) (code : Tower.Tm Γ.arity)
    (formed : Typed Tower.rules Γ.raw code U0) : TypeOver Γ :=
  ⟨code, small, .sort _, formed⟩

/-- Membership `A ∈ S` is a type of `U0`. -/
theorem app_small {n : Nat} {Γ : Tower.Ctx n} {S A : Tower.Tm n} (tS : Typed Tower.rules Γ S setType)
    (tA : Typed Tower.rules Γ A U0) : Typed Tower.rules Γ (.app S A) U0 :=
  Derivable.appElim tS tA

/-! ## The start -/

/-- The forward swap, as a row over any frame. -/
def swapRowAt (Γ : Context Tower.rules) : TotalTerm Γ :=
  ⟨largeType Γ swapType (swapType_formed _), ⟨swapCode, swap_typed _⟩⟩

/-- The backward swap, as a row over any frame. -/
def swapBackRowAt (Γ : Context Tower.rules) : TotalTerm Γ :=
  ⟨largeType Γ swapBackType (swapBackType_formed _), ⟨swapCode, swapBack_typed _⟩⟩

/-- `X ∈ S`, the type `S X`, over `X : U0, x : X, g : Ground`. -/
def memSType : TypeOver triple :=
  smallType triple (.app sCode (.var 2)) (Derivable.appElim (s_typed _) (Derivable.var 2))

theorem member_typed : Typed Tower.rules triple.raw (.pair (.var 1) (.var 0)) (.app sCode (.var 2)) := by
  have x : Typed Tower.rules triple.raw (.var 1) (.var 2) := Derivable.var 1
  have g : Typed Tower.rules triple.raw (.var 0) ground := Derivable.var 0
  have formed : Typed Tower.rules triple.raw (.sigma (.var 2) ground) U0 :=
    .cumul (.sigmaForm (Derivable.var 2) (.sort _) (ground_typed _) (.sort _) (.sorts _ _)) collapse
  have normal : Typed Tower.rules triple.raw (.pair (.var 1) (.var 0)) (.sigma (.var 2) ground) :=
    .pairIntro formed (.sort _) x g
  exact .conv normal (.symm (s_beta (Derivable.var 2))) (.sort _)

/-- **The member**: `(x, g) : X ∈ S`. -/
def memberRow : TotalTerm triple := ⟨memSType, ⟨.pair (.var 1) (.var 0), member_typed⟩⟩

/-- The start: the two swaps (rows `0`, `1`) and the member `(x, g) : X ∈ S` (row `2`), with no
knowledge. -/
def start : State Tower.rules Nat :=
  ⟨triple, [], {0, 1, 2}, fun o =>
    if o = 0 then swapRowAt triple else if o = 1 then swapBackRowAt triple else memberRow⟩

/-! ## The extensionality rule -/

/-- `f : Π X. S X → T X`. -/
def fType : TypeOver triple := largeType triple swapType (swapType_formed _)

abbrev withF : Context Tower.rules := extend triple fType

/-- `g : Π X. T X → S X`. -/
def gType : TypeOver withF := largeType withF swapBackType (swapBackType_formed _)

/-- The frame of the extensionality rule: `X : U0, x : X, g : Ground, f, g'`. -/
abbrev extFrame : Context Tower.rules := extend withF gType

/-- The pattern `f`. -/
def fPattern : TotalTerm extFrame :=
  ⟨largeType extFrame swapType (swapType_formed _), ⟨.var 1, Derivable.var 1⟩⟩

/-- The pattern `g`. -/
def gPattern : TotalTerm extFrame :=
  ⟨largeType extFrame swapBackType (swapBackType_formed _), ⟨.var 0, Derivable.var 0⟩⟩

/-- `setEq S T`, over a frame. -/
def eqType (Γ : Context Tower.rules) : TypeOver Γ :=
  largeType Γ (setEq sCode tCode) (setEq_formed (s_typed _) (t_typed _))

theorem extEvidence_typed :
    Typed Tower.rules extFrame.raw (evidence (.var 1) (.var 0)) (setEq sCode tCode) :=
  evidence_typed (Derivable.var 1) (Derivable.var 0)

/-- **The extensionality rule**: read the two swaps with the patterns `f` and `g`, and make row `3`,
`λX. (f X, g X) : setEq S T`. -/
def extFiring : Firing setting.levels start where
  helpers := .cons fType (.cons gType (.nil _))
  taken := []
  read := [0, 1]
  takes := []
  reads := [fPattern, gPattern]
  makes := [(3, ⟨eqType extFrame, (evidence (.var 1) (.var 0) : Tower.Tm 5)⟩)]
  tells := []
  guards := []
  queries := []

/-- `f ↦ swap`, `g ↦ swapBack`, over the start frame. -/
def extSolution : triple ⟶ extFrame :=
  pair (pair (𝟙 triple) ⟨swapCode, swap_typed _⟩) ⟨swapCode, swapBack_typed _⟩

theorem extFiring_information :
    extFiring.information = [(fPattern, extFiring.row 0), (gPattern, extFiring.row 1)] := rfl

theorem ext_identifies_f : fPattern.reindex extSolution = (extFiring.row 0).reindex extSolution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

theorem ext_identifies_g : gPattern.reindex extSolution = (extFiring.row 1).reindex extSolution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

/-- **The extensionality rule fires on the two swaps.** -/
theorem ext_admitted : (step setting.levels Nat).Admits extFiring := by
  refine ⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
    (enabled_iff extFiring).mpr ⟨fun _ member => absurd member List.not_mem_nil, fun o member => ?_,
      fun _ member => absurd member List.not_mem_nil, fun o member inside => ?_⟩,
    ⟨triple, extSolution, ?_⟩, ?_⟩
  · obtain rfl := List.mem_singleton.mp member
    exact extEvidence_typed
  · rcases List.mem_cons.mp member with rfl | rest
    · show (0 : Nat) ∈ ({0, 1, 2} : Finset Nat)
      decide
    · obtain rfl := List.mem_singleton.mp rest
      show (1 : Nat) ∈ ({0, 1, 2} : Finset Nat)
      decide
  · obtain rfl := List.mem_singleton.mp member
    revert inside
    show (3 : Nat) ∉ ({0, 1, 2} : Finset Nat)
    decide
  · rw [extFiring_information]
    intro e member
    rcases List.mem_cons.mp member with rfl | rest
    · show (frames setting.levels).E (fPattern.reindex extSolution) ((extFiring.row 0).reindex extSolution)
      rw [ext_identifies_f]
      exact ((frames setting.levels).equivalence _).refl _
    · obtain rfl := List.mem_singleton.mp rest
      show (frames setting.levels).E (gPattern.reindex extSolution) ((extFiring.row 1).reindex extSolution)
      rw [ext_identifies_g]
      exact ((frames setting.levels).equivalence _).refl _
  · intro b τ _
    exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

/-- The state the extensionality rule reaches. -/
abbrev middle : State Tower.rules Nat := (step setting.levels Nat).result extFiring ext_admitted

/-- **The equality row**: row `3` is a proof of `setEq S T` whose code is `λX. (f X, g X)`, and the
knowledge holds only the two read equations. -/
theorem equality_row :
    (middle.label 3).1.code = setEq sCode tCode ∧
      (middle.label 3).2.code = (evidence (.var 1) (.var 0) : Tower.Tm 5) ∧
      middle.knowledge = [(fPattern, extFiring.row 0), (gPattern, extFiring.row 1)] :=
  ⟨rfl, rfl, rfl⟩

/-- **The equality is derived from the two swaps**: at every solution of the knowledge, the helpers
`f` and `g` are the forward and the backward swap. -/
theorem equality_from_swaps {Θ : Context Tower.rules} (τ : Θ ⟶ middle.frame)
    (solved : (frames setting.levels).Models τ middle.knowledge) :
    Equal Tower.rules Θ.raw (subst τ.substitution (.var 1 : Tower.Tm 5)) swapCode swapType ∧
      Equal Tower.rules Θ.raw (subst τ.substitution (.var 0 : Tower.Tm 5)) swapCode swapBackType :=
  ⟨(solved _ (List.Mem.head _)).2, (solved _ (List.Mem.tail _ (List.Mem.head _))).2⟩

/-- At the solution `extSolution`, the equality row reads `λX. (swap X, swapBack X)`. -/
theorem equality_row_at_solution :
    subst extSolution.substitution (middle.label 3).2.code = evidence swapCode swapCode := rfl

/-! ## The transport rule -/

/-- `a : U0`. -/
def aType : TypeOver extFrame := smallUniverse _

abbrev withA : Context Tower.rules := extend extFrame aType

/-- `s : U0 → U0`. -/
def sType : TypeOver withA := largeType withA setType (setType_large _)

abbrev withS : Context Tower.rules := extend withA sType

/-- `t : U0 → U0`. -/
def tType : TypeOver withS := largeType withS setType (setType_large _)

abbrev withT : Context Tower.rules := extend withS tType

/-- `e : setEq s t`. -/
def eType : TypeOver withT :=
  largeType withT (setEq (.var 1) (.var 0)) (setEq_formed (Derivable.var 1) (Derivable.var 0))

abbrev withE : Context Tower.rules := extend withT eType

/-- `m : s a`. -/
def mType : TypeOver withE :=
  smallType withE (.app (.var 2) (.var 3)) (app_small (Derivable.var 2) (Derivable.var 3))

/-- The frame of the transport rule: the state's frame and `a, s, t, e, m`. -/
abbrev transFrame : Context Tower.rules := extend withE mType

/-- The pattern `e : setEq s t`. -/
def ePattern : TotalTerm transFrame :=
  ⟨largeType transFrame (setEq (.var 3) (.var 2)) (setEq_formed (Derivable.var 3) (Derivable.var 2)),
    ⟨.var 1, Derivable.var 1⟩⟩

/-- The pattern `m : s a`. -/
def mPattern : TotalTerm transFrame :=
  ⟨smallType transFrame (.app (.var 3) (.var 4)) (app_small (Derivable.var 3) (Derivable.var 4)),
    ⟨.var 0, Derivable.var 0⟩⟩

/-- `t a`, the made row's type. -/
def memTType : TypeOver transFrame :=
  smallType transFrame (.app (.var 2) (.var 4)) (app_small (Derivable.var 2) (Derivable.var 4))

/-- **The coercion is typed in the bare frame**: `fst (e a) m : t a`. -/
theorem coerced_typed :
    Typed Tower.rules transFrame.raw (.app (.fst (.app (.var 1) (.var 4))) (.var 0)) (.app (.var 2) (.var 4)) := by
  have e : Typed Tower.rules transFrame.raw (.var 1) (setEq (.var 3) (.var 2)) := Derivable.var 1
  have a : Typed Tower.rules transFrame.raw (.var 4) U0 := Derivable.var 4
  have both : Typed Tower.rules transFrame.raw (.app (.var 1) (.var 4))
      (.sigma (.pi (.app (.var 3) (.var 4)) (.app (.var 3) (.var 5)))
        (.pi (.app (.var 3) (.var 5)) (.app (.var 5) (.var 6)))) := Derivable.appElim e a
  have forward : Typed Tower.rules transFrame.raw (.fst (.app (.var 1) (.var 4)))
      (.pi (.app (.var 3) (.var 4)) (.app (.var 3) (.var 5))) := Derivable.fstElim both
  have m : Typed Tower.rules transFrame.raw (.var 0) (.app (.var 3) (.var 4)) := Derivable.var 0
  exact Derivable.appElim forward m

/-- **The transport rule**: read the equality row with `e : setEq s t` and the member with `m : s a`,
and make row `4`, `fst (e a) m : t a`. -/
def transFiring : Firing setting.levels middle where
  helpers := .cons aType (.cons sType (.cons tType (.cons eType (.cons mType (.nil _)))))
  taken := []
  read := [3, 2]
  takes := []
  reads := [ePattern, mPattern]
  makes := [(4, ⟨memTType, (.app (.fst (.app (.var 1) (.var 4))) (.var 0) : Tower.Tm 10)⟩)]
  tells := []
  guards := []
  queries := []

/-- The equality row at the start frame: `λX. (swap X, swapBack X)`. -/
def evidenceAt : Tower.Tm 3 := evidence swapCode swapCode

theorem evidenceAt_typed : Typed Tower.rules triple.raw evidenceAt (setEq sCode tCode) :=
  evidence_typed (swap_typed _) (swapBack_typed _)

/-- `f ↦ swap`, `g ↦ swapBack`, `a ↦ X`, `s ↦ S`, `t ↦ T`, `e ↦ λX. (swap X, swapBack X)`,
`m ↦ (x, g)`. -/
def transSolution : triple ⟶ transFrame :=
  pair (pair (pair (pair (pair extSolution ⟨.var 2, Derivable.var 2⟩) ⟨sCode, s_typed _⟩) ⟨tCode, t_typed _⟩)
    ⟨evidenceAt, evidenceAt_typed⟩) ⟨.pair (.var 1) (.var 0), member_typed⟩

theorem transFiring_information :
    transFiring.information =
      [((frames setting.levels).act transFiring.helpers.weaken fPattern,
          (frames setting.levels).act transFiring.helpers.weaken (extFiring.row 0)),
        ((frames setting.levels).act transFiring.helpers.weaken gPattern,
          (frames setting.levels).act transFiring.helpers.weaken (extFiring.row 1)),
        (ePattern, transFiring.row 3), (mPattern, transFiring.row 2)] := rfl

theorem trans_carried_f :
    ((frames setting.levels).act transFiring.helpers.weaken fPattern).reindex transSolution =
      ((frames setting.levels).act transFiring.helpers.weaken (extFiring.row 0)).reindex transSolution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

theorem trans_carried_g :
    ((frames setting.levels).act transFiring.helpers.weaken gPattern).reindex transSolution =
      ((frames setting.levels).act transFiring.helpers.weaken (extFiring.row 1)).reindex transSolution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

theorem trans_identifies_e : ePattern.reindex transSolution = (transFiring.row 3).reindex transSolution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

theorem trans_identifies_m : mPattern.reindex transSolution = (transFiring.row 2).reindex transSolution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

/-- The solution solves the four equations of the transport rule's information. -/
theorem transSolution_models : (frames setting.levels).Models transSolution
    [((frames setting.levels).act transFiring.helpers.weaken fPattern,
        (frames setting.levels).act transFiring.helpers.weaken (extFiring.row 0)),
      ((frames setting.levels).act transFiring.helpers.weaken gPattern,
        (frames setting.levels).act transFiring.helpers.weaken (extFiring.row 1)),
      (ePattern, transFiring.row 3), (mPattern, transFiring.row 2)] := by
  intro e member
  rcases List.mem_cons.mp member with rfl | rest
  · show (frames setting.levels).E
      (((frames setting.levels).act transFiring.helpers.weaken fPattern).reindex transSolution)
      (((frames setting.levels).act transFiring.helpers.weaken (extFiring.row 0)).reindex transSolution)
    rw [trans_carried_f]
    exact ((frames setting.levels).equivalence _).refl _
  rcases List.mem_cons.mp rest with rfl | rest
  · show (frames setting.levels).E
      (((frames setting.levels).act transFiring.helpers.weaken gPattern).reindex transSolution)
      (((frames setting.levels).act transFiring.helpers.weaken (extFiring.row 1)).reindex transSolution)
    rw [trans_carried_g]
    exact ((frames setting.levels).equivalence _).refl _
  rcases List.mem_cons.mp rest with rfl | rest
  · show (frames setting.levels).E (ePattern.reindex transSolution) ((transFiring.row 3).reindex transSolution)
    rw [trans_identifies_e]
    exact ((frames setting.levels).equivalence _).refl _
  obtain rfl := List.mem_singleton.mp rest
  show (frames setting.levels).E (mPattern.reindex transSolution) ((transFiring.row 2).reindex transSolution)
  rw [trans_identifies_m]
  exact ((frames setting.levels).equivalence _).refl _

/-- **The transport rule fires** on the equality row and the member. -/
theorem trans_admitted : (step setting.levels Nat).Admits transFiring := by
  refine ⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
    (enabled_iff transFiring).mpr ⟨fun _ member => absurd member List.not_mem_nil, fun o member => ?_,
      fun _ member => absurd member List.not_mem_nil, fun o member inside => ?_⟩,
    ⟨triple, transSolution, ?_⟩, ?_⟩
  · obtain rfl := List.mem_singleton.mp member
    exact coerced_typed
  · rcases List.mem_cons.mp member with rfl | rest
    · show 3 ∈ middle.present
      decide
    · obtain rfl := List.mem_singleton.mp rest
      show 2 ∈ middle.present
      decide
  · obtain rfl := List.mem_singleton.mp member
    revert inside
    show 4 ∉ middle.present
    decide
  · rw [transFiring_information]
    exact transSolution_models
  · intro b τ _
    exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

/-- The last state. -/
abbrev final : State Tower.rules Nat := (step setting.levels Nat).result transFiring trans_admitted

/-- **The run**: the extensionality rule, then the transport rule. -/
def extensionalityRun : (step setting.levels Nat).Run start :=
  .cons extFiring ext_admitted (.cons transFiring trans_admitted (.nil _))

/-- **The transported member**: row `4` of the last state has type `t a`; the solution reads the type
as `T X` and the member as `fst ((λX. (swap X, swapBack X)) X) (x, g)`. -/
theorem transported_row :
    (final.label 4).1.code = (.app (.var 2) (.var 4) : Tower.Tm 10) ∧
      subst transSolution.substitution (final.label 4).1.code = .app tCode (.var 2) ∧
      subst transSolution.substitution (final.label 4).2.code =
        .app (.fst (.app evidenceAt (.var 2))) (.pair (.var 1) (.var 0)) :=
  ⟨rfl, rfl, rfl⟩

/-- **The solution solves the whole run's knowledge.** -/
theorem extensionalityRun_solved :
    (frames setting.levels).Models transSolution extensionalityRun.last.knowledge := by
  show (frames setting.levels).Models transSolution transFiring.information
  rw [transFiring_information]
  exact transSolution_models

/-! ## The knowledge still refuses `S ≐ T` -/

/-- Tell `S ≐ T` in the last state. -/
def tellAtEnd : Firing setting.levels final where
  helpers := .nil _
  taken := []
  read := []
  takes := []
  reads := []
  makes := []
  tells := [(ProgrammingOnTheStep.SetExtensionality.sRow transFrame,
    ProgrammingOnTheStep.SetExtensionality.tRow transFrame)]
  guards := []
  queries := []

/-- **Still refused**: after the equality row and the transported member exist, the knowledge still
does not equate `S` and `T`; no solution of any knowledge can. -/
theorem tellAtEnd_refused : ¬ (step setting.levels Nat).Admits tellAtEnd := by
  rintro ⟨-, -, ⟨Δ, σ, solved⟩, -⟩
  have told : (frames setting.levels).E
      ((ProgrammingOnTheStep.SetExtensionality.sRow transFrame).reindex σ)
      ((ProgrammingOnTheStep.SetExtensionality.tRow transFrame).reindex σ) :=
    solved _ (List.mem_append_right _ (List.Mem.head _))
  have sSame : (ProgrammingOnTheStep.SetExtensionality.sRow transFrame).reindex σ =
      (ProgrammingOnTheStep.SetExtensionality.sRow (empty Tower.rules)).reindex (toEmpty Δ) :=
    totalTerm_ext (TypeOver.ext rfl rfl) rfl
  have tSame : (ProgrammingOnTheStep.SetExtensionality.tRow transFrame).reindex σ =
      (ProgrammingOnTheStep.SetExtensionality.tRow (empty Tower.rules)).reindex (toEmpty Δ) :=
    totalTerm_ext (TypeOver.ext rfl rfl) rfl
  apply ProgrammingOnTheStep.SetExtensionality.sets_unsolvable (toEmpty Δ)
  show (frames setting.levels).E
    ((ProgrammingOnTheStep.SetExtensionality.sRow (empty Tower.rules)).reindex (toEmpty Δ))
    ((ProgrammingOnTheStep.SetExtensionality.tRow (empty Tower.rules)).reindex (toEmpty Δ))
  rw [← sSame, ← tSame]
  exact told

/-- **D2's refusal still holds**, unchanged: the module is read, not edited. -/
theorem extensionality_still_refused :
    ¬ (step setting.levels Nat).Admits ProgrammingOnTheStep.SetExtensionality.extensionalityFiring :=
  ProgrammingOnTheStep.SetExtensionality.extensionality_refused

end EqualityOnTheStep.Run

#print axioms EqualityOnTheStep.Run.ext_admitted
#print axioms EqualityOnTheStep.Run.equality_row
#print axioms EqualityOnTheStep.Run.equality_from_swaps
#print axioms EqualityOnTheStep.Run.trans_admitted
#print axioms EqualityOnTheStep.Run.extensionalityRun
#print axioms EqualityOnTheStep.Run.transported_row
#print axioms EqualityOnTheStep.Run.extensionalityRun_solved
#print axioms EqualityOnTheStep.Run.tellAtEnd_refused
#print axioms EqualityOnTheStep.Run.extensionality_still_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
