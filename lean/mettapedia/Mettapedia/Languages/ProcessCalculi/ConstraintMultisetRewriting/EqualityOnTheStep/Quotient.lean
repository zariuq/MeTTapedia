import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EqualityOnTheStep.Controls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalSupport

/-!
# The quotient of sets by extensional equality: class names, and soundness as a firing

Over the frame `Q : U0, q₁ q₂ : Q`, the classes of sets are **names**: `q₁` and `q₂` are unknowns of
the frame, of an abstract type `Q`. A row `(S, q₁) : Σ (_ : U0 → U0). Q` records that `q₁` is the
class of `S`, and `(T, q₂)` that `q₂` is the class of `T`.

**Soundness is a firing** (`soundFiring`, `sound_admitted`): it reads the two class rows with
patterns `(s, k₁)` and `(t, k₂)` and the evidence row with `e : setEq s t`, and **tells** `k₁ ≐ k₂`.
Only an equation between two names enters the knowledge, so the knowledge stays the decidable
equational theory it was; the undecidable relation `setEq` never enters it, only its witnessed
instances, as equations between names.

**Queries read through witnessed class equations** (`countAfter_admitted`, `countBefore_refused`).
"Exactly one row is the class pair `(S, q₂)`" is refused before the soundness firing: at the identity
solution `q₁` and `q₂` are different variables, which the knowledge never equates (`vars_apart`).
It is admitted after it: every solution of the knowledge equates `q₁` with `q₂`, so `(S, q₁)` is
counted; `(T, q₂)` is never counted, since `S` and `T` stay unequal (`SetExtensionality`).

So the quotient's equality is visible to absence and counting once witnessed, and only then; the sets
themselves are never equated.

**The discipline belongs to the rules** (`unwitnessedTell_admitted`): the step also admits a firing
that tells `q₁ ≐ q₂` without reading any evidence, since the names are unknowns. That class
equations come only from soundness firings is a property of the program's rule set, which the step
does not enforce.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace EqualityOnTheStep.Quotient

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull Interface.DependentFull.Controls
open ProgrammingOnTheStep.SetExtensionality (small U0 sCode tCode setType swapCode swapType
  swapBackType setType_formed s_typed t_typed swap_typed swapBack_typed)

/-! ## Facts of the knowledge used below -/

/-- **Two different variables are never equal in the knowledge** (by normal supports). -/
theorem vars_apart {n : Nat} {Γ : Tower.Ctx n} (formed : CtxFormed Tower.rules Γ) {i j : Fin n}
    (different : i ≠ j) {A : Tower.Tm n} (equal : Equal Tower.rules Γ (.var i) (.var j) A) : False := by
  have supports := ContextualDependentNormalSupport.equal_support
    (S := ContextualDependentEtaLong.Controls.setting) ContextualDependentEtaLong.Controls.rigid
    TowerModel.complete formed equal
    (ContextualDependentNormalObservations.normal_var ContextualDependentEtaLong.Controls.rigid i)
    (ContextualDependentNormalObservations.normal_var ContextualDependentEtaLong.Controls.rigid j)
  have member : i ∈ (Tm.var i : Tower.Tm n).support := by simp [Tm.support]
  rw [supports] at member
  simp [Tm.support] at member
  exact different member

/-- **`S` and `T` are equal at no frame.** -/
theorem sets_apart {Θ : Context Tower.rules} (equal : Equal Tower.rules Θ.raw sCode tCode setType) : False :=
  ProgrammingOnTheStep.SetExtensionality.sets_unsolvable (toEmpty Θ)
    ((equivalent_iff setting.levels _ _).mpr ⟨⟨large, .sort _, .refl (setType_large _)⟩, equal⟩)

/-- Equal pairs of a non-dependent pair type have equal first components. -/
theorem fst_of_pair_equal {n : Nat} {Γ : Tower.Ctx n} {A Q a b a' b' : Tower.Tm n} {u : Tower.Head}
    (formed : Typed Tower.rules Γ (.sigma A (Presentation.rename wk Q)) (.head u))
    (hu : Tower.rules.isUniverse u) (ta : Typed Tower.rules Γ a A) (tb : Typed Tower.rules Γ b Q)
    (ta' : Typed Tower.rules Γ a' A) (tb' : Typed Tower.rules Γ b' Q)
    (equal : Equal Tower.rules Γ (.pair a b) (.pair a' b') (.sigma A (Presentation.rename wk Q))) :
    Equal Tower.rules Γ a a' A := by
  have tb1 : Typed Tower.rules Γ b (inst0 a (Presentation.rename wk Q)) := by rw [inst0_rename_wk]; exact tb
  have tb1' : Typed Tower.rules Γ b' (inst0 a' (Presentation.rename wk Q)) := by rw [inst0_rename_wk]; exact tb'
  exact .trans (.symm (.betaFst formed hu ta tb1)) (.trans (.fstCong equal) (.betaFst formed hu ta' tb1'))

/-- Equal pairs of a non-dependent pair type have equal second components. -/
theorem snd_of_pair_equal {n : Nat} {Γ : Tower.Ctx n} {A Q a b a' b' : Tower.Tm n} {u : Tower.Head}
    (formed : Typed Tower.rules Γ (.sigma A (Presentation.rename wk Q)) (.head u))
    (hu : Tower.rules.isUniverse u) (ta : Typed Tower.rules Γ a A) (tb : Typed Tower.rules Γ b Q)
    (ta' : Typed Tower.rules Γ a' A) (tb' : Typed Tower.rules Γ b' Q)
    (equal : Equal Tower.rules Γ (.pair a b) (.pair a' b') (.sigma A (Presentation.rename wk Q))) :
    Equal Tower.rules Γ b b' Q := by
  have tb1 : Typed Tower.rules Γ b (inst0 a (Presentation.rename wk Q)) := by rw [inst0_rename_wk]; exact tb
  have tb1' : Typed Tower.rules Γ b' (inst0 a' (Presentation.rename wk Q)) := by rw [inst0_rename_wk]; exact tb'
  have left := Derivable.betaSnd formed hu ta tb1
  have right := Derivable.betaSnd formed hu ta' tb1'
  have middle : Equal Tower.rules Γ (.snd (.pair a b)) (.snd (.pair a' b'))
      (inst0 (.fst (.pair a b)) (Presentation.rename wk Q)) := .sndCong equal
  rw [inst0_rename_wk] at left right middle
  exact .trans (.symm left) (.trans middle right)

/-! ## Classes -/

/-- `Σ (_ : U0 → U0). Q`: a set with a class name. -/
def classOf {n : Nat} (Q : Tower.Tm n) : Tower.Tm n := .sigma setType (Presentation.rename wk Q)

theorem classOf_formed {n : Nat} {Γ : Tower.Ctx n} {Q : Tower.Tm n} (tQ : Typed Tower.rules Γ Q U0) :
    Typed Tower.rules Γ (classOf Q) (.head large) :=
  .cumul (.sigmaForm (setType_large Γ) (.sort _) tQ.weaken (.sort _) (.sorts _ _)) large_of_one_zero

/-- `q₂ : Q`, over `Q : U0, q₁ : Q`. -/
def q2Type : TypeOver pairFrame := Run.smallType pairFrame (.var 1) (Derivable.var 1)

/-- **The frame of classes**: `Q : U0, q₁ : Q, q₂ : Q`. -/
abbrev qFrame : Context Tower.rules := extend pairFrame q2Type

theorem classS_typed : Typed Tower.rules qFrame.raw (.pair sCode (.var 1)) (classOf (.var 2)) :=
  .pairIntro (classOf_formed (Derivable.var 2)) (.sort _) (s_typed _) (Derivable.var 1)

theorem classT_typed : Typed Tower.rules qFrame.raw (.pair tCode (.var 0)) (classOf (.var 2)) :=
  .pairIntro (classOf_formed (Derivable.var 2)) (.sort _) (t_typed _) (Derivable.var 0)

/-- `(S, q₁)`: `q₁` is the class of `S`. -/
def classRowS : TotalTerm qFrame :=
  ⟨⟨classOf (.var 2), large, .sort _, classOf_formed (Derivable.var 2)⟩, ⟨.pair sCode (.var 1), classS_typed⟩⟩

/-- `(T, q₂)`: `q₂` is the class of `T`. -/
def classRowT : TotalTerm qFrame :=
  ⟨⟨classOf (.var 2), large, .sort _, classOf_formed (Derivable.var 2)⟩, ⟨.pair tCode (.var 0), classT_typed⟩⟩

/-- The evidence `λX. (swap X, swapBack X) : setEq S T`. -/
def evidenceRowQ : TotalTerm qFrame :=
  ⟨Run.largeType qFrame (setEq sCode tCode) (setEq_formed (s_typed _) (t_typed _)),
    ⟨evidence swapCode swapCode, evidence_typed (swap_typed _) (swapBack_typed _)⟩⟩

/-- **The start**: the two class rows and the evidence; no knowledge. -/
def quotientStart : State Tower.rules Nat :=
  ⟨qFrame, [], {0, 1, 2}, fun o => if o = 0 then classRowS else if o = 1 then classRowT else evidenceRowQ⟩

/-! ## Soundness, as a firing -/

def hsType : TypeOver qFrame := Run.largeType qFrame setType (setType_large _)
abbrev withHs : Context Tower.rules := extend qFrame hsType
def htType : TypeOver withHs := Run.largeType withHs setType (setType_large _)
abbrev withHt : Context Tower.rules := extend withHs htType
/-- `k₁ : Q`. -/
def k1Type : TypeOver withHt := Run.smallType withHt (.var 4) (Derivable.var 4)
abbrev withK1 : Context Tower.rules := extend withHt k1Type
/-- `k₂ : Q`. -/
def k2Type : TypeOver withK1 := Run.smallType withK1 (.var 5) (Derivable.var 5)
abbrev withK2 : Context Tower.rules := extend withK1 k2Type
/-- `e : setEq s t`. -/
def heType : TypeOver withK2 :=
  Run.largeType withK2 (setEq (.var 3) (.var 2)) (setEq_formed (Derivable.var 3) (Derivable.var 2))

/-- The frame of the soundness rule: `Q, q₁, q₂, s, t, k₁, k₂, e`. -/
abbrev soundFrame : Context Tower.rules := extend withK2 heType

/-- The class type `Σ (_ : U0 → U0). Q`, over the soundness frame. -/
def classOver : TypeOver soundFrame := ⟨classOf (.var 7), large, .sort _, classOf_formed (Derivable.var 7)⟩

/-- The pattern `(s, k₁)`. -/
def p0 : TotalTerm soundFrame :=
  ⟨classOver, ⟨.pair (.var 4) (.var 2), .pairIntro (classOf_formed (Derivable.var 7)) (.sort _)
    (Derivable.var 4) (Derivable.var 2)⟩⟩

/-- The pattern `(t, k₂)`. -/
def p1 : TotalTerm soundFrame :=
  ⟨classOver, ⟨.pair (.var 3) (.var 1), .pairIntro (classOf_formed (Derivable.var 7)) (.sort _)
    (Derivable.var 3) (Derivable.var 1)⟩⟩

/-- The pattern `e : setEq s t`. -/
def p2 : TotalTerm soundFrame :=
  ⟨Run.largeType soundFrame (setEq (.var 4) (.var 3)) (setEq_formed (Derivable.var 4) (Derivable.var 3)),
    ⟨.var 0, Derivable.var 0⟩⟩

/-- `k₁ : Q`, as a typed term. -/
def k1Row : TotalTerm soundFrame := ⟨Run.smallType soundFrame (.var 7) (Derivable.var 7), ⟨.var 2, Derivable.var 2⟩⟩

/-- `k₂ : Q`, as a typed term. -/
def k2Row : TotalTerm soundFrame := ⟨Run.smallType soundFrame (.var 7) (Derivable.var 7), ⟨.var 1, Derivable.var 1⟩⟩

/-- **The soundness rule**: read `(s, k₁)`, `(t, k₂)` and `e : setEq s t`, and tell `k₁ ≐ k₂`. -/
def soundFiring : Firing setting.levels quotientStart where
  helpers := .cons hsType (.cons htType (.cons k1Type (.cons k2Type (.cons heType (.nil _)))))
  taken := []
  read := [0, 1, 2]
  takes := []
  reads := [p0, p1, p2]
  makes := []
  tells := [(k1Row, k2Row)]
  guards := []
  queries := []

/-- `Q ↦ Q`, `q₁, q₂, k₁, k₂ ↦ q`, `s ↦ S`, `t ↦ T`, `e ↦ λX. (swap X, swapBack X)`, over
`Q : U0, q : Q`. -/
def soundSolution : pairFrame ⟶ soundFrame :=
  pair (pair (pair (pair (pair (pair (pair (pair (toEmpty pairFrame) ⟨.var 1, Derivable.var 1⟩)
    ⟨.var 0, Derivable.var 0⟩) ⟨.var 0, Derivable.var 0⟩) ⟨sCode, s_typed _⟩) ⟨tCode, t_typed _⟩)
    ⟨.var 0, Derivable.var 0⟩) ⟨.var 0, Derivable.var 0⟩)
    ⟨evidence swapCode swapCode, evidence_typed (swap_typed _) (swapBack_typed _)⟩

theorem soundFiring_information :
    soundFiring.information =
      [(p0, soundFiring.row 0), (p1, soundFiring.row 1), (p2, soundFiring.row 2), (k1Row, k2Row)] := rfl

theorem sound_identifies_0 : p0.reindex soundSolution = (soundFiring.row 0).reindex soundSolution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

theorem sound_identifies_1 : p1.reindex soundSolution = (soundFiring.row 1).reindex soundSolution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

theorem sound_identifies_2 : p2.reindex soundSolution = (soundFiring.row 2).reindex soundSolution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

theorem sound_identifies_tell : k1Row.reindex soundSolution = k2Row.reindex soundSolution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

theorem soundSolution_models : (frames setting.levels).Models soundSolution soundFiring.information := by
  rw [soundFiring_information]
  intro e member
  rcases List.mem_cons.mp member with rfl | rest
  · show (frames setting.levels).E (p0.reindex soundSolution) ((soundFiring.row 0).reindex soundSolution)
    rw [sound_identifies_0]
    exact ((frames setting.levels).equivalence _).refl _
  rcases List.mem_cons.mp rest with rfl | rest
  · show (frames setting.levels).E (p1.reindex soundSolution) ((soundFiring.row 1).reindex soundSolution)
    rw [sound_identifies_1]
    exact ((frames setting.levels).equivalence _).refl _
  rcases List.mem_cons.mp rest with rfl | rest
  · show (frames setting.levels).E (p2.reindex soundSolution) ((soundFiring.row 2).reindex soundSolution)
    rw [sound_identifies_2]
    exact ((frames setting.levels).equivalence _).refl _
  obtain rfl := List.mem_singleton.mp rest
  show (frames setting.levels).E (k1Row.reindex soundSolution) (k2Row.reindex soundSolution)
  rw [sound_identifies_tell]
  exact ((frames setting.levels).equivalence _).refl _

/-- **The soundness rule fires**: the evidence is read, and the knowledge learns `k₁ ≐ k₂`. -/
theorem sound_admitted : (step setting.levels Nat).Admits soundFiring := by
  refine ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, fun _ member => absurd member List.not_mem_nil⟩,
    (enabled_iff soundFiring).mpr ⟨fun _ member => absurd member List.not_mem_nil, fun o member => ?_,
      fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩,
    ⟨pairFrame, soundSolution, soundSolution_models⟩, ?_⟩
  · rcases List.mem_cons.mp member with rfl | rest
    · show (0 : Nat) ∈ ({0, 1, 2} : Finset Nat)
      decide
    rcases List.mem_cons.mp rest with rfl | rest
    · show (1 : Nat) ∈ ({0, 1, 2} : Finset Nat)
      decide
    obtain rfl := List.mem_singleton.mp rest
    show (2 : Nat) ∈ ({0, 1, 2} : Finset Nat)
    decide
  · intro b τ _
    exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

/-- The state after soundness: the classes `q₁` and `q₂` are equal in the knowledge. -/
abbrev classes : State Tower.rules Nat := (step setting.levels Nat).result soundFiring sound_admitted

/-- **At every solution of the knowledge after soundness, `q₂` is `q₁`.** -/
theorem classes_identified {Θ : Context Tower.rules} (τ : Θ ⟶ soundFrame)
    (solved : (frames setting.levels).Models τ classes.knowledge) :
    Equal Tower.rules Θ.raw (τ.substitution 5) (τ.substitution 6) (τ.substitution 7) := by
  have known : classes.knowledge =
      [(p0, soundFiring.row 0), (p1, soundFiring.row 1), (p2, soundFiring.row 2), (k1Row, k2Row)] :=
    soundFiring_information
  rw [known] at solved
  have formed : Typed Tower.rules Θ.raw (.sigma setType (Presentation.rename wk (τ.substitution 7))) (.head large) :=
    (classOf_formed (Derivable.var 7) : Typed Tower.rules soundFrame.raw (classOf (.var 7)) (.head large)).substitute τ.typed
  have t4 : Typed Tower.rules Θ.raw (τ.substitution 4) setType := τ.typed 4
  have t3 : Typed Tower.rules Θ.raw (τ.substitution 3) setType := τ.typed 3
  have t2 : Typed Tower.rules Θ.raw (τ.substitution 2) (τ.substitution 7) := τ.typed 2
  have t1 : Typed Tower.rules Θ.raw (τ.substitution 1) (τ.substitution 7) := τ.typed 1
  have t6 : Typed Tower.rules Θ.raw (τ.substitution 6) (τ.substitution 7) := τ.typed 6
  have t5 : Typed Tower.rules Θ.raw (τ.substitution 5) (τ.substitution 7) := τ.typed 5
  have e0 : Equal Tower.rules Θ.raw (.pair (τ.substitution 4) (τ.substitution 2)) (.pair sCode (τ.substitution 6))
      (.sigma setType (Presentation.rename wk (τ.substitution 7))) := (solved _ (List.Mem.head _)).2
  have e1 : Equal Tower.rules Θ.raw (.pair (τ.substitution 3) (τ.substitution 1)) (.pair tCode (τ.substitution 5))
      (.sigma setType (Presentation.rename wk (τ.substitution 7))) :=
    (solved _ (List.Mem.tail _ (List.Mem.head _))).2
  have told : Equal Tower.rules Θ.raw (τ.substitution 2) (τ.substitution 1) (τ.substitution 7) :=
    (solved _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))).2
  have k1q1 := snd_of_pair_equal formed (.sort _) t4 t2 (s_typed _) t6 e0
  have k2q2 := snd_of_pair_equal formed (.sort _) t3 t1 (t_typed _) t5 e1
  exact .trans (.symm k2q2) (.trans (.symm told) k1q1)

/-! ## Counting reads through the witnessed class equation -/

/-- `(S, q₂)` over the soundness frame. -/
def sq2After : TotalTerm soundFrame :=
  ⟨classOver, ⟨.pair sCode (.var 5), .pairIntro (classOf_formed (Derivable.var 7)) (.sort _) (s_typed _)
    (Derivable.var 5)⟩⟩

/-- **After soundness, ask: exactly one row is `(S, q₂)`.** -/
def countAfter : Firing setting.levels classes where
  helpers := .nil _
  taken := []
  read := []
  takes := []
  reads := []
  makes := []
  tells := []
  guards := []
  queries := [Query.count setting.levels Nat sq2After 1]

theorem countAfter_information : countAfter.information = classes.knowledge :=
  information_plain setting.levels classes.knowledge classes.present classes.label []
    [Query.count setting.levels Nat sq2After 1]

/-- **At every solution after soundness, exactly one row is `(S, q₂)`**: the row `(S, q₁)`. -/
theorem countAfter_holds {Θ : Context Tower.rules} (τ : Θ ⟶ soundFrame)
    (solved : (frames setting.levels).Models τ classes.knowledge) :
    (Query.count setting.levels Nat sq2After 1).Holds classes.present countAfter.row τ := by
  have q2q1 := classes_identified τ solved
  have formed : Typed Tower.rules Θ.raw (.sigma setType (Presentation.rename wk (τ.substitution 7))) (.head large) :=
    (classOf_formed (Derivable.var 7) : Typed Tower.rules soundFrame.raw (classOf (.var 7)) (.head large)).substitute τ.typed
  have t5 : Typed Tower.rules Θ.raw (τ.substitution 5) (τ.substitution 7) := τ.typed 5
  have t6 : Typed Tower.rules Θ.raw (τ.substitution 6) (τ.substitution 7) := τ.typed 6
  have row0 : (frames setting.levels).E ((frames setting.levels).act τ sq2After)
      ((frames setting.levels).act τ (countAfter.row 0)) := by
    refine (equivalent_iff setting.levels _ _).mpr ⟨IsType.refl ⟨large, .sort _, formed⟩, ?_⟩
    show Equal Tower.rules Θ.raw (.pair sCode (τ.substitution 5)) (.pair sCode (τ.substitution 6))
      (.sigma setType (Presentation.rename wk (τ.substitution 7)))
    have second : Equal Tower.rules Θ.raw (τ.substitution 5) (τ.substitution 6)
        (inst0 sCode (Presentation.rename wk (τ.substitution 7))) := by
      rw [inst0_rename_wk]
      exact q2q1
    exact .pairCong formed (.sort _) (.refl (s_typed _)) second
  refine ⟨{0}, fun o => ⟨fun inside => ?_, fun ⟨present, region⟩ => ?_⟩, Finset.card_singleton 0⟩
  · obtain rfl := Finset.mem_singleton.mp inside
    exact ⟨show (0 : Nat) ∈ ({0, 1, 2} : Finset Nat) by decide, row0⟩
  · change o ∈ ({0, 1, 2} : Finset Nat) at present
    rcases Finset.mem_insert.mp present with rfl | rest
    · exact Finset.mem_singleton_self 0
    rcases Finset.mem_insert.mp rest with rfl | rest
    · exfalso
      have pairs : Equal Tower.rules Θ.raw (.pair sCode (τ.substitution 5)) (.pair tCode (τ.substitution 5))
          (.sigma setType (Presentation.rename wk (τ.substitution 7))) := region.2
      exact sets_apart (Θ := Θ) (fst_of_pair_equal formed (.sort _) (s_typed _) t5 (t_typed _) t5 pairs)
    · exfalso
      obtain rfl := Finset.mem_singleton.mp rest
      have types : TypeEq Tower.rules Θ.raw (.sigma setType (Presentation.rename wk (τ.substitution 7)))
          (setEq sCode tCode) := region.1
      exact TypeEq.pi_ne_sigma (TowerModel.facts (L := Nat)) Θ.formed types.symm

/-- **Admitted after soundness.** -/
theorem countAfter_admitted : (step setting.levels Nat).Admits countAfter := by
  refine (admits_iff countAfter).mpr ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl,
      fun _ member => absurd member List.not_mem_nil⟩,
    ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩,
    ?_, fun _ _ _ _ member => absurd member List.not_mem_nil, ?_⟩
  · rw [countAfter_information]
    exact ⟨pairFrame, soundSolution, soundSolution_models⟩
  intro q member Θ τ solved
  obtain rfl := List.mem_singleton.mp member
  rw [countAfter_information] at solved
  exact countAfter_holds τ solved

/-- `(S, q₂)` over the start frame. -/
def sq2Before : TotalTerm qFrame :=
  ⟨⟨classOf (.var 2), large, .sort _, classOf_formed (Derivable.var 2)⟩,
    ⟨.pair sCode (.var 0), .pairIntro (classOf_formed (Derivable.var 2)) (.sort _) (s_typed _) (Derivable.var 0)⟩⟩

/-- **Before soundness, ask the same.** -/
def countBefore : Firing setting.levels quotientStart where
  helpers := .nil _
  taken := []
  read := []
  takes := []
  reads := []
  makes := []
  tells := []
  guards := []
  queries := [Query.count setting.levels Nat sq2Before 1]

theorem countBefore_information : countBefore.information = [] := rfl

/-- **Refused before soundness**: at the identity solution, `q₁` and `q₂` are different variables, so
no row is `(S, q₂)`. -/
theorem countBefore_refused : ¬ (step setting.levels Nat).Admits countBefore := by
  intro admitted
  obtain ⟨-, -, -, -, queries⟩ := (admits_iff countBefore).mp admitted
  have solved : (frames setting.levels).Models (𝟙 qFrame) countBefore.information := by
    rw [countBefore_information]
    exact Frames.models_nil _
  obtain ⟨seen, members, card⟩ := queries _ (List.Mem.head _) qFrame (𝟙 qFrame) solved
  obtain ⟨o, single⟩ := Finset.card_eq_one.mp card
  have inside : o ∈ seen := by rw [single]; exact Finset.mem_singleton_self o
  obtain ⟨present, region⟩ := (members o).mp inside
  have formed : Typed Tower.rules qFrame.raw (classOf (.var 2 : Tower.Tm 3)) (.head large) :=
    classOf_formed (Γ := qFrame.raw) (Q := (.var 2 : Tower.Tm 3)) (Derivable.var 2)
  have q0 : Typed Tower.rules qFrame.raw (.var 0) (.var 2) := Derivable.var 0
  have q1 : Typed Tower.rules qFrame.raw (.var 1) (.var 2) := Derivable.var 1
  change o ∈ ({0, 1, 2} : Finset Nat) at present
  rcases Finset.mem_insert.mp present with rfl | rest
  · have pairs : Equal Tower.rules qFrame.raw (.pair sCode (.var 0)) (.pair sCode (.var 1)) (.sigma setType (.var 3)) :=
      region.2
    exact vars_apart qFrame.formed (by decide)
      (snd_of_pair_equal (Q := .var 2) formed (.sort _) (s_typed _) q0 (s_typed _) q1 pairs)
  rcases Finset.mem_insert.mp rest with rfl | rest
  · have pairs : Equal Tower.rules qFrame.raw (.pair sCode (.var 0)) (.pair tCode (.var 0)) (.sigma setType (.var 3)) :=
      region.2
    exact sets_apart (Θ := qFrame) (fst_of_pair_equal (Q := .var 2) formed (.sort _) (s_typed _) q0 (t_typed _) q0 pairs)
  · obtain rfl := Finset.mem_singleton.mp rest
    have types : TypeEq Tower.rules qFrame.raw (.sigma setType (.var 3)) (setEq sCode tCode) := region.1
    exact TypeEq.pi_ne_sigma (TowerModel.facts (L := Nat)) qFrame.formed types.symm

/-! ## The discipline is the rule set's, not the step's -/

/-- `q₁ : Q`, as a typed term over the start frame. -/
def q1Row : TotalTerm qFrame := ⟨Run.smallType qFrame (.var 2) (Derivable.var 2), ⟨.var 1, Derivable.var 1⟩⟩

/-- `q₂ : Q`, as a typed term over the start frame. -/
def q2Row : TotalTerm qFrame := ⟨Run.smallType qFrame (.var 2) (Derivable.var 2), ⟨.var 0, Derivable.var 0⟩⟩

/-- **A tell between class names that reads no evidence.** -/
def unwitnessedTell : Firing setting.levels quotientStart where
  helpers := .nil _
  taken := []
  read := []
  takes := []
  reads := []
  makes := []
  tells := [(q1Row, q2Row)]
  guards := []
  queries := []

/-- `Q ↦ Q`, `q₁, q₂ ↦ q`, over `Q : U0, q : Q`. -/
def nameSolution : pairFrame ⟶ qFrame :=
  pair (pair (pair (toEmpty pairFrame) ⟨.var 1, Derivable.var 1⟩) ⟨.var 0, Derivable.var 0⟩) ⟨.var 0, Derivable.var 0⟩

theorem unwitnessedTell_information : unwitnessedTell.information = [(q1Row, q2Row)] := rfl

theorem names_identified : q1Row.reindex nameSolution = q2Row.reindex nameSolution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

/-- **The step admits a class equation told without evidence**: `q₁` and `q₂` are unknowns, and
identifying them is solvable. So "class equations come only from soundness firings" is a discipline
of the program's rules, which the step does not enforce. -/
theorem unwitnessedTell_admitted : (step setting.levels Nat).Admits unwitnessedTell := by
  refine ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, fun _ member => absurd member List.not_mem_nil⟩,
    (enabled_iff unwitnessedTell).mpr ⟨fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil⟩,
    ⟨pairFrame, nameSolution, ?_⟩, ?_⟩
  · rw [unwitnessedTell_information]
    intro e member
    obtain rfl := List.mem_singleton.mp member
    show (frames setting.levels).E (q1Row.reindex nameSolution) (q2Row.reindex nameSolution)
    rw [names_identified]
    exact ((frames setting.levels).equivalence _).refl _
  · intro b τ _
    exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

end EqualityOnTheStep.Quotient

#print axioms EqualityOnTheStep.Quotient.unwitnessedTell_admitted
#print axioms EqualityOnTheStep.Quotient.vars_apart
#print axioms EqualityOnTheStep.Quotient.sets_apart
#print axioms EqualityOnTheStep.Quotient.sound_admitted
#print axioms EqualityOnTheStep.Quotient.classes_identified
#print axioms EqualityOnTheStep.Quotient.countAfter_admitted
#print axioms EqualityOnTheStep.Quotient.countBefore_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
