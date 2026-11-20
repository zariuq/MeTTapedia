import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Singletons

/-!
# Asking a bag's guards before its tells

The incoming knowledge and all selected-port equations form the ask problem.
Every tell must still be jointly consistent, but no tell may justify a guard.
This is a separate admission contract; the existing admission is unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled)

universe uO uT uH uE uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

namespace Firing

variable (X : Frames Tm Hom) {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom}
  {P : Program Tm} (s : State Tm O) (f : Firing O E P s.frame)

def askInformation : EquationStore (Tm (E.target f.ext)) :=
  X.applyStore (E.weaken f.ext) s.knowledge ++
    f.matching X s (f.opened X).take f.selection.taken ++
    f.matching X s (f.opened X).read f.selection.read

theorem information_eq_ask :
    f.information X s = f.askInformation X s ++ (f.opened X).tell := rfl

variable [DecidableEq O]

def AdmitsBeforeTells : Prop :=
  f.Shapes X s ∧ Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ∧
    X.Solvable (f.information X s) ∧
      X.Entails (f.askInformation X s) (fun _ σ => f.Holds X s σ)

theorem admits_of_beforeTells (h : f.AdmitsBeforeTells X s) : f.Admits X s := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun b σ solved => h.2.2.2 b σ ?_⟩
  rw [information_eq_ask] at solved
  exact (Frames.models_append σ _ _).mp solved |>.1

theorem beforeTells_iff_of_no_tells (silent : (f.opened X).tell = []) :
    f.AdmitsBeforeTells X s ↔ f.Admits X s := by
  have same : f.information X s = f.askInformation X s := by
    rw [information_eq_ask, silent, List.append_nil]
  simp only [AdmitsBeforeTells, Admits, same]

end Firing

namespace JointFirings

namespace Member

variable (X : Frames Tm Hom) {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom}
  {P : Program Tm} (s : State Tm O) {x : E.Ext s.frame} (m : Member O E P x)

def matchingInformation : EquationStore (Tm (E.target x)) :=
  m.firing.matching X s (m.firing.opened X).take m.selection.taken ++
    m.firing.matching X s (m.firing.opened X).read m.selection.read

theorem own_eq_matching_tells :
    m.own X s = m.matchingInformation X s ++ (m.firing.opened X).tell := rfl

end Member

namespace Bag

variable (X : Frames Tm Hom) {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom}
  {P : Program Tm} (s : State Tm O) (f : Bag O E P s.frame)

def askInformation : EquationStore (Tm (E.target f.ext)) :=
  X.applyStore (E.weaken f.ext) s.knowledge ++
    f.members.flatMap fun m => m.matchingInformation X s

def tells : EquationStore (Tm (E.target f.ext)) :=
  f.members.flatMap fun m => (m.firing.opened X).tell

/-- Full solutions solve all matching equations, regardless of how tells are interleaved. -/
theorem models_ask {b : Obj} {σ : Hom (E.target f.ext) b}
    (solved : X.Models σ (f.information X s)) : X.Models σ (f.askInformation X s) := by
  intro e member
  rcases List.mem_append.mp member with known | matched
  · exact solved e (List.mem_append_left _ known)
  · obtain ⟨m, inside, matched⟩ := List.mem_flatMap.mp matched
    exact solved e (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨m, inside, List.mem_append_left _ matched⟩))

/-- Separating matching from tells preserves exactly the models. -/
theorem models_information_iff {b : Obj} (σ : Hom (E.target f.ext) b) :
    X.Models σ (f.information X s) ↔
      X.Models σ (f.askInformation X s) ∧ X.Models σ (f.tells X s) := by
  constructor
  · intro solved
    refine ⟨models_ask X s f solved, fun e member => ?_⟩
    obtain ⟨m, inside, told⟩ := List.mem_flatMap.mp member
    exact solved e (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨m, inside, List.mem_append_right _ told⟩))
  · rintro ⟨asked, told⟩ e member
    rcases List.mem_append.mp member with known | own
    · exact asked e (List.mem_append_left _ known)
    · obtain ⟨m, inside, own⟩ := List.mem_flatMap.mp own
      rw [Member.own_eq_matching_tells] at own
      rcases List.mem_append.mp own with matched | made
      · exact asked e (List.mem_append_right _ (List.mem_flatMap.mpr ⟨m, inside, matched⟩))
      · exact told e (List.mem_flatMap.mpr ⟨m, inside, made⟩)

variable [DecidableEq O]

/-- Full joint solvability is retained; only the guard problem changes. -/
def AdmitsBeforeTells : Prop :=
  f.Fits X s ∧ Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ∧
    X.Solvable (f.information X s) ∧
      X.Entails (f.askInformation X s) (fun _ σ => f.Holds X s σ)

theorem admits_of_beforeTells (h : f.AdmitsBeforeTells X s) : f.Admits X s :=
  ⟨h.1, h.2.1, h.2.2.1, fun b σ solved => h.2.2.2 b σ (models_ask X s f solved)⟩

/-- A before-tells step is the same firing and has the same complete result. -/
theorem beforeTells_step (h : f.members ≠ [] ∧ f.AdmitsBeforeTells X s) :
    (bagStep X O E P).Admits f ∧
      (bagStep X O E P).preparedResult f ⟨⟨h.1, h.2.1⟩, h.2.2.1, h.2.2.2.1⟩ = f.result X s :=
  ⟨⟨h.1, admits_of_beforeTells X s f h.2⟩, rfl⟩

theorem beforeTells_iff_of_entailed_tells
    (redundant : X.Entails (f.askInformation X s) (fun _ σ => X.Models σ (f.tells X s))) :
    f.AdmitsBeforeTells X s ↔ f.Admits X s := by
  refine ⟨admits_of_beforeTells X s f, ?_⟩
  intro h
  refine ⟨h.1, h.2.1, h.2.2.1, fun b σ asked => h.2.2.2 b σ ?_⟩
  exact (models_information_iff X s f σ).mpr ⟨asked, redundant b σ asked⟩

omit [DecidableEq O] in
theorem tells_nil (silent : ∀ m ∈ f.members, (m.firing.opened X).tell = []) : f.tells X s = [] := by
  exact List.flatMap_eq_nil_iff.mpr silent

theorem beforeTells_iff_of_no_tells
    (silent : ∀ m ∈ f.members, (m.firing.opened X).tell = []) :
    f.AdmitsBeforeTells X s ↔ f.Admits X s := by
  apply beforeTells_iff_of_entailed_tells X s f
  intro b σ _
  rw [tells_nil X s f silent]
  exact Frames.models_nil σ

theorem beforeTells_iff_of_no_checks
    (noChecks : ∀ m ∈ f.members, (m.firing.opened X).checks = [])
    (noCollect : ∀ m ∈ f.members, m.firing.collectOpened X = []) :
    f.AdmitsBeforeTells X s ↔ f.Admits X s := by
  refine ⟨admits_of_beforeTells X s f, fun h => ⟨h.1, h.2.1, h.2.2.1, ?_⟩⟩
  intro b σ _ m inside
  refine ⟨fun c member => ?_, fun q member => ?_⟩
  · rw [noChecks m inside] at member
    cases member
  · change q ∈ (m.firing.collectOpened X).zip m.seen at member
    rw [noCollect m inside] at member
    cases member

omit [DecidableEq O] in
theorem askInformation_single {x : E.Ext s.frame} (m : Member O E P x) :
    (⟨x, [m]⟩ : Bag O E P s.frame).askInformation X s = m.firing.askInformation X s := by
  simp only [askInformation, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Firing.askInformation, Member.matchingInformation, List.append_assoc]

theorem beforeTells_single {x : E.Ext s.frame} (m : Member O E P x) :
    (⟨x, [m]⟩ : Bag O E P s.frame).AdmitsBeforeTells X s ↔
      m.firing.AdmitsBeforeTells X s := by
  simp only [AdmitsBeforeTells, Firing.AdmitsBeforeTells, fits_single,
    selection_single, information_single, askInformation_single, Holds,
    List.mem_singleton, forall_eq]

end Bag

end JointFirings
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax
