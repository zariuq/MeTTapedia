import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EqualityOnTheStep.Options.RespectComposition
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EqualityOnTheStep.Options.Observability
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PublicationAuthority

/-!
# A publication discipline for class equations

`Quotient` identifies classes of sets by telling equations between class names, read through by
absence and counting. The step also admits such equations without evidence
(`Quotient.unwitnessedTell_admitted`), and they are observed (`Observability.unwitnessed_tell_observed`).

**A second unwitnessed route: reading** (`unwitnessedRead_admitted`, `unwitnessedRead_identifies`).
A firing that tells nothing, but reads the class row `(S, q₁)` with the pattern `(S, q₂)`, is admitted:
the read's matching equation is solvable by identifying the two names, and it becomes knowledge.
After it every solution equates `q₁` and `q₂`, and no evidence was read. So a discipline on tells
alone does not suffice: every equation a firing publishes (its matchings and its tells) counts.

**The discipline on the step** (`Disciplined`). Relative to a table of classes (a set and its name),
a firing is disciplined when every pair of names that its information equates, and that its starting
knowledge did not equate, is justified by a row it reads whose type is extensional equality of the two
classes' sets. The controls:

* the evidence-free tell and the evidence-free read are admitted by the step and are not
  disciplined (`unwitnessedTell_undisciplined`, `unwitnessedRead_undisciplined`);
* the soundness firing of `Quotient` is disciplined (`sound_disciplined`);
* every clause is needed: restricting tells alone admits the read route (`tells_alone_insufficient`),
  and forbidding every new class equation refuses soundness, which identifies the classes
  (`soundness_needs_identification`).

**The discipline in the publication-authority form** (`Registry`, `Publishes`, `Published`). As in
`PublicationAuthority`, class equations are published at one location; actors hold rights; the
kernel publishes an equation only by reading evidence for it; and no other actor holds the `send`
right there (the sole-writer policy). Then:

* every published class equation is witnessed by evidence in the calculus (`published_witnessed`);
* so is every identification the published equations entail, their equivalence closure
  (`identified_witnessed`), because evidence is reflexive, symmetric and transitive
  (`witnessed_refl`, `witnessed_symm`, `witnessed_trans`, by `RespectCoherence.reflE`,
  `SetTheory.setEq_symm` and `RespectComposition.compE`);
* without the sole-writer policy, a writer other than the kernel publishes any equation with no
  evidence (`writer_publishes_without_evidence`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace EqualityOnTheStep.Options.QuotientDiscipline

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull Interface.DependentFull.Controls
open ProgrammingOnTheStep.SetExtensionality (small U0 sCode tCode setType swapCode swapType
  swapBackType setType_formed s_typed t_typed swap_typed swapBack_typed)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes (Rights)
open Observability (EntailsEqual)

/-! ## Reading publishes too -/

/-- **Read the class row `(S, q₁)` with the pattern `(S, q₂)`**, and nothing else. -/
def unwitnessedRead : Firing setting.levels Quotient.quotientStart where
  helpers := .nil _
  taken := []
  read := [0]
  takes := []
  reads := [Quotient.sq2Before]
  makes := []
  tells := []
  guards := []
  queries := []

theorem unwitnessedRead_information :
    unwitnessedRead.information = [(Quotient.sq2Before, unwitnessedRead.row 0)] := rfl

theorem read_identifies : Quotient.sq2Before.reindex Quotient.nameSolution =
    (unwitnessedRead.row 0).reindex Quotient.nameSolution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

/-- **The evidence-free read is admitted.** -/
theorem unwitnessedRead_admitted : (step setting.levels Nat).Admits unwitnessedRead := by
  refine ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, fun _ member => absurd member List.not_mem_nil⟩,
    (enabled_iff unwitnessedRead).mpr ⟨fun _ member => absurd member List.not_mem_nil,
      fun o member => ?_, fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil⟩,
    ⟨pairFrame, Quotient.nameSolution, ?_⟩, ?_⟩
  · obtain rfl := List.mem_singleton.mp member
    show (0 : Nat) ∈ ({0, 1, 2} : Finset Nat)
    decide
  · rw [unwitnessedRead_information]
    intro e member
    obtain rfl := List.mem_singleton.mp member
    show (frames setting.levels).E (Quotient.sq2Before.reindex Quotient.nameSolution)
      ((unwitnessedRead.row 0).reindex Quotient.nameSolution)
    rw [read_identifies]
    exact ((frames setting.levels).equivalence _).refl _
  · intro b τ _
    exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

/-- At a solution of the read's equation, the two names are equal. -/
theorem read_identifies_at {Θ : Context Tower.rules} (τ : Θ ⟶ Quotient.qFrame)
    (solved : (frames setting.levels).Models τ [(Quotient.sq2Before, unwitnessedRead.row 0)]) :
    (frames setting.levels).E ((frames setting.levels).act τ Quotient.q1Row)
      ((frames setting.levels).act τ Quotient.q2Row) := by
  have read := solved _ (List.Mem.head _)
  have pairs : Equal Tower.rules Θ.raw (.pair sCode (τ.substitution 0)) (.pair sCode (τ.substitution 1))
      (.sigma setType (Presentation.rename wk (τ.substitution 2))) := read.2
  have formed : Typed Tower.rules Θ.raw (.sigma setType (Presentation.rename wk (τ.substitution 2))) (.head large) :=
    (Quotient.classOf_formed (Derivable.var 2) :
      Typed Tower.rules Quotient.qFrame.raw (Quotient.classOf (.var 2)) (.head large)).substitute τ.typed
  have names := Quotient.snd_of_pair_equal formed (.sort _) (s_typed _) (τ.typed 0) (s_typed _) (τ.typed 1) pairs
  refine (equivalent_iff setting.levels _ _).mpr ⟨IsType.refl ⟨small, .sort _, τ.typed 2⟩, ?_⟩
  show Equal Tower.rules Θ.raw (τ.substitution 1) (τ.substitution 0) (τ.substitution 2)
  exact .symm names

/-- **After the read, every solution equates the class names `q₁` and `q₂`.** -/
theorem unwitnessedRead_identifies :
    EntailsEqual (frames setting.levels) unwitnessedRead.information
      ((frames setting.levels).act unwitnessedRead.helpers.weaken Quotient.q1Row)
      ((frames setting.levels).act unwitnessedRead.helpers.weaken Quotient.q2Row) := by
  intro b τ solved
  rw [unwitnessedRead_information] at solved
  exact read_identifies_at τ solved

/-- **At the start, no solution is forced to equate `q₁` and `q₂`.** -/
theorem names_apart_at_start :
    ¬ EntailsEqual (frames setting.levels) ([] : EquationStore (TotalTerm Quotient.qFrame))
      Quotient.q1Row Quotient.q2Row := by
  intro entailed
  have atIdentity := entailed Quotient.qFrame (𝟙 Quotient.qFrame) (Frames.models_nil _)
  have terms : Equal Tower.rules Quotient.qFrame.raw (.var 1) (.var 0) (.var 2) := atIdentity.2
  exact Quotient.vars_apart Quotient.qFrame.formed (by decide) terms

/-! ## The discipline on the step -/

/-- **A disciplined firing**, relative to a table of classes (a set's code and its name): every pair
of names that its information equates, and that its starting knowledge did not, is justified by a read
row whose type is extensional equality of the two sets. -/
def Disciplined {st : State Tower.rules Nat} (classes : List (Tower.Tm st.frame.arity × TotalTerm st.frame))
    (f : Firing setting.levels st) : Prop :=
  ∀ c₁ ∈ classes, ∀ c₂ ∈ classes,
    EntailsEqual (frames setting.levels) f.information
        ((frames setting.levels).act f.helpers.weaken c₁.2) ((frames setting.levels).act f.helpers.weaken c₂.2) →
      EntailsEqual (frames setting.levels) ((frames setting.levels).applyStore f.helpers.weaken st.knowledge)
          ((frames setting.levels).act f.helpers.weaken c₁.2) ((frames setting.levels).act f.helpers.weaken c₂.2) ∨
        ∃ o ∈ f.read, (st.label o).1.code = setEq c₁.1 c₂.1 ∨ (st.label o).1.code = setEq c₂.1 c₁.1

/-- **The disciplined step** admits a firing when the step admits it and it is disciplined. -/
def DisciplinedAdmits {st : State Tower.rules Nat} (classes : List (Tower.Tm st.frame.arity × TotalTerm st.frame))
    (f : Firing setting.levels st) : Prop :=
  (step setting.levels Nat).Admits f ∧ Disciplined classes f

/-- The classes of the quotient's start: `S` with name `q₁`, `T` with name `q₂`. -/
def quotientClasses : List (Tower.Tm 3 × TotalTerm Quotient.qFrame) :=
  [(sCode, Quotient.q1Row), (tCode, Quotient.q2Row)]

/-- **The evidence-free tell is not disciplined**: it equates `q₁` and `q₂`, which the empty
knowledge does not, and it reads no row. -/
theorem unwitnessedTell_undisciplined : ¬ Disciplined (st := Quotient.quotientStart) quotientClasses
    Quotient.unwitnessedTell := by
  intro disciplined
  have entailed : EntailsEqual (frames setting.levels) Quotient.unwitnessedTell.information
      ((frames setting.levels).act Quotient.unwitnessedTell.helpers.weaken Quotient.q1Row)
      ((frames setting.levels).act Quotient.unwitnessedTell.helpers.weaken Quotient.q2Row) := by
    intro b τ solved
    rw [Quotient.unwitnessedTell_information] at solved
    exact solved _ (List.Mem.head _)
  rcases disciplined (sCode, Quotient.q1Row) (List.Mem.head _) (tCode, Quotient.q2Row)
      (List.Mem.tail _ (List.Mem.head _)) entailed with old | ⟨o, read, _⟩
  · exact names_apart_at_start old
  · exact absurd read List.not_mem_nil

/-- **The evidence-free read is not disciplined**: it equates `q₁` and `q₂`, and the one row it reads
is a class row, not evidence. -/
theorem unwitnessedRead_undisciplined : ¬ Disciplined (st := Quotient.quotientStart) quotientClasses
    unwitnessedRead := by
  intro disciplined
  rcases disciplined (sCode, Quotient.q1Row) (List.Mem.head _) (tCode, Quotient.q2Row)
      (List.Mem.tail _ (List.Mem.head _)) unwitnessedRead_identifies with old | ⟨o, read, typed⟩
  · exact names_apart_at_start old
  · obtain rfl := List.mem_singleton.mp read
    rcases typed with same | same
    · cases same
    · cases same

/-- **The soundness firing is disciplined**: each pair of different names it equates is justified by
the evidence row it reads, whose type is `setEq S T`. -/
theorem sound_disciplined : Disciplined (st := Quotient.quotientStart) quotientClasses Quotient.soundFiring := by
  intro c₁ member₁ c₂ member₂ _
  have evidenceRead : (2 : Nat) ∈ Quotient.soundFiring.read := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have evidenceType : (Quotient.quotientStart.label 2).1.code = setEq sCode tCode := rfl
  have reflexive : ∀ c : Tower.Tm 3 × TotalTerm Quotient.qFrame,
      EntailsEqual (frames setting.levels)
        ((frames setting.levels).applyStore Quotient.soundFiring.helpers.weaken Quotient.quotientStart.knowledge)
        ((frames setting.levels).act Quotient.soundFiring.helpers.weaken c.2)
        ((frames setting.levels).act Quotient.soundFiring.helpers.weaken c.2) :=
    fun c b τ _ => ((frames setting.levels).equivalence _).refl _
  rcases List.mem_cons.mp member₁ with rfl | rest₁
  · rcases List.mem_cons.mp member₂ with rfl | rest₂
    · exact .inl (reflexive _)
    · obtain rfl := List.mem_singleton.mp rest₂
      exact .inr ⟨2, evidenceRead, .inl evidenceType⟩
  · obtain rfl := List.mem_singleton.mp rest₁
    rcases List.mem_cons.mp member₂ with rfl | rest₂
    · exact .inr ⟨2, evidenceRead, .inr evidenceType⟩
    · obtain rfl := List.mem_singleton.mp rest₂
      exact .inl (reflexive _)

/-- **The controls of the disciplined step**: the two evidence-free identifications are admitted by
the step and refused by the disciplined step; soundness is admitted by both. -/
theorem discipline_controls :
    (step setting.levels Nat).Admits Quotient.unwitnessedTell ∧
      ¬ DisciplinedAdmits (st := Quotient.quotientStart) quotientClasses Quotient.unwitnessedTell ∧
      (step setting.levels Nat).Admits unwitnessedRead ∧
      ¬ DisciplinedAdmits (st := Quotient.quotientStart) quotientClasses unwitnessedRead ∧
      DisciplinedAdmits (st := Quotient.quotientStart) quotientClasses Quotient.soundFiring :=
  ⟨Quotient.unwitnessedTell_admitted, fun h => unwitnessedTell_undisciplined h.2, unwitnessedRead_admitted,
    fun h => unwitnessedRead_undisciplined h.2, Quotient.sound_admitted, sound_disciplined⟩

/-- **Restricting tells alone is not enough**: the read route tells nothing, is admitted, and
identifies the class names. -/
theorem tells_alone_insufficient :
    unwitnessedRead.tells = [] ∧ (step setting.levels Nat).Admits unwitnessedRead ∧
      EntailsEqual (frames setting.levels) unwitnessedRead.information
        ((frames setting.levels).act unwitnessedRead.helpers.weaken Quotient.q1Row)
        ((frames setting.levels).act unwitnessedRead.helpers.weaken Quotient.q2Row) :=
  ⟨rfl, unwitnessedRead_admitted, unwitnessedRead_identifies⟩

/-- **Forbidding every new class equation is too strict**: soundness identifies the classes at every
solution of its knowledge, and the count that sees them (`Quotient.countAfter_admitted`) needs it. -/
theorem soundness_needs_identification :
    (∀ {Θ : Context Tower.rules} (τ : Θ ⟶ Quotient.soundFrame),
        (frames setting.levels).Models τ Quotient.classes.knowledge →
          Equal Tower.rules Θ.raw (τ.substitution 5) (τ.substitution 6) (τ.substitution 7)) ∧
      (step setting.levels Nat).Admits Quotient.countAfter :=
  ⟨fun τ solved => Quotient.classes_identified τ solved, Quotient.countAfter_admitted⟩

/-! ## The discipline in the publication-authority form -/

/-- **Evidence that two closed sets have the same members.** -/
def Witnessed (S T : Tower.Tm 0) : Prop := ∃ e : Tower.Tm 0, Typed Tower.rules .nil e (setEq S T)

theorem setEq_subst {m k : Nat} (τ : Presentation.Sub Tower.Head m k) (S T : Tower.Tm m) :
    subst τ (setEq S T) = setEq (subst τ S) (subst τ T) := by
  simp only [setEq, subst, subst_liftSub_wk]
  rfl

theorem witnessed_refl {S : Tower.Tm 0} (hS : Typed Tower.rules .nil S setType) : Witnessed S S :=
  ⟨Respect.reflE, Respect.reflE_typed hS⟩

theorem witnessed_symm {S T : Tower.Tm 0} (hS : Typed Tower.rules .nil S setType)
    (hT : Typed Tower.rules .nil T setType) : Witnessed S T → Witnessed T S := by
  rintro ⟨e, he⟩
  have symm := SetTheory.setEq_symm.substitute (((Respect.noSub_typed .nil).cons setType hS).cons setType hT)
  have applied := Derivable.appElim symm he
  have typeEq : inst0 e (subst (liftSub (consSub T (consSub S Respect.noSub))) (setEq (.var 1) (.var 2))) =
      setEq T S := by
    show subst (subst0 e) (subst (liftSub (consSub T (consSub S Respect.noSub))) (setEq (.var 1) (.var 2))) = setEq T S
    rw [setEq_subst, setEq_subst]
    exact congrArg₂ setEq (inst0_rename_wk e T) (inst0_rename_wk e S)
  rw [typeEq] at applied
  exact ⟨_, applied⟩

theorem witnessed_trans {S T U : Tower.Tm 0} (hS : Typed Tower.rules .nil S setType)
    (hT : Typed Tower.rules .nil T setType) (hU : Typed Tower.rules .nil U setType) :
    Witnessed S T → Witnessed T U → Witnessed S U := by
  rintro ⟨e, he⟩ ⟨e', he'⟩
  exact ⟨Respect.compE e e', Respect.compE_typed hS hT hU he he'⟩

variable {N L I : Type}

/-- **A class registry**: the set of each class name, the location where class equations are
published, the actors' rights, and the kernel. -/
structure Registry (N L I : Type) where
  setOf : N → Tower.Tm 0
  setOf_typed : ∀ n, Typed Tower.rules .nil (setOf n) setType
  location : L
  rights : I → Rights L
  kernel : I

/-- **The sole-writer policy**: no actor but the kernel holds `send` at the registry. -/
def Registry.SoleWriter (reg : Registry N L I) : Prop :=
  ∀ actor, actor ≠ reg.kernel → reg.rights actor reg.location .send = false

/-- **A publication of a class equation**: the kernel publishes `n₁ ≐ n₂` by reading evidence that
the two sets have the same members; another actor publishes when it holds `send` at the registry. -/
inductive Publishes (reg : Registry N L I) : List (N × N) → List (N × N) → Prop
  | kernel {store : List (N × N)} {n₁ n₂ : N} {e : Tower.Tm 0}
      (evidence : Typed Tower.rules .nil e (setEq (reg.setOf n₁) (reg.setOf n₂))) :
      Publishes reg store ((n₁, n₂) :: store)
  | writer {store : List (N × N)} {n₁ n₂ : N} (actor : I) (notKernel : actor ≠ reg.kernel)
      (holds : reg.rights actor reg.location .send = true) :
      Publishes reg store ((n₁, n₂) :: store)

/-- **The stores of class equations reachable by publications** from the empty store. -/
inductive Published (reg : Registry N L I) : List (N × N) → Prop
  | nil : Published reg []
  | step {store store' : List (N × N)} : Published reg store → Publishes reg store store' → Published reg store'

/-- **Under the sole-writer policy, every published class equation is witnessed.** -/
theorem published_witnessed (reg : Registry N L I) (sole : reg.SoleWriter) {store : List (N × N)}
    (published : Published reg store) : ∀ p ∈ store, Witnessed (reg.setOf p.1) (reg.setOf p.2) := by
  induction published with
  | nil => exact fun _ member => absurd member List.not_mem_nil
  | step _ publishes ih =>
      intro p member
      cases publishes with
      | kernel evidence =>
          rcases List.mem_cons.mp member with rfl | rest
          · exact ⟨_, evidence⟩
          · exact ih p rest
      | writer actor notKernel holds =>
          rw [sole actor notKernel] at holds
          cases holds

/-- **Under the sole-writer policy, every identification the published equations entail is
witnessed**: the equivalence closure of the published equations relates only names whose sets have
evidence of the same members. -/
theorem identified_witnessed (reg : Registry N L I) (sole : reg.SoleWriter) {store : List (N × N)}
    (published : Published reg store) {n₁ n₂ : N}
    (identified : Relation.EqvGen (fun a b => (a, b) ∈ store) n₁ n₂) :
    Witnessed (reg.setOf n₁) (reg.setOf n₂) := by
  induction identified with
  | rel a b inside => exact published_witnessed reg sole published (a, b) inside
  | refl a => exact witnessed_refl (reg.setOf_typed a)
  | symm a b _ ih => exact witnessed_symm (reg.setOf_typed a) (reg.setOf_typed b) ih
  | trans a b c _ _ ih₁ ih₂ =>
      exact witnessed_trans (reg.setOf_typed a) (reg.setOf_typed b) (reg.setOf_typed c) ih₁ ih₂

/-- **Without the sole-writer policy, a writer publishes any class equation with no evidence.** -/
theorem writer_publishes_without_evidence (reg : Registry N L I) (actor : I) (notKernel : actor ≠ reg.kernel)
    (holds : reg.rights actor reg.location .send = true) (n₁ n₂ : N) :
    Published reg [(n₁, n₂)] :=
  .step .nil (.writer actor notKernel holds)

/-- **The registry of the two sets of `SetExtensionality`**, kernel `0`, and only the kernel may send. -/
def setsRegistry : Registry Bool Unit Nat where
  setOf n := if n then sCode else tCode
  setOf_typed n := by
    cases n
    · exact t_typed _
    · exact s_typed _
  location := ()
  rights actor _ _ := actor == 0
  kernel := 0

theorem setsRegistry_sole : setsRegistry.SoleWriter := by
  intro actor notKernel
  have different : actor ≠ 0 := notKernel
  show (actor == 0) = false
  simp [different]

/-- **An example run**: the kernel publishes `S ≐ T` from the swaps' evidence, and the published
classes are witnessed in both directions. -/
theorem setsRegistry_run :
    Published setsRegistry [(true, false)] ∧ Witnessed (setsRegistry.setOf true) (setsRegistry.setOf false) ∧
      Witnessed (setsRegistry.setOf false) (setsRegistry.setOf true) := by
  have run : Published setsRegistry [(true, false)] :=
    .step .nil (.kernel (evidence_typed (swap_typed _) (swapBack_typed _)))
  refine ⟨run, identified_witnessed setsRegistry setsRegistry_sole run (.rel _ _ (List.Mem.head _)), ?_⟩
  exact identified_witnessed setsRegistry setsRegistry_sole run (.symm _ _ (.rel _ _ (List.Mem.head _)))

end EqualityOnTheStep.Options.QuotientDiscipline

#print axioms EqualityOnTheStep.Options.QuotientDiscipline.unwitnessedRead_admitted
#print axioms EqualityOnTheStep.Options.QuotientDiscipline.unwitnessedRead_identifies
#print axioms EqualityOnTheStep.Options.QuotientDiscipline.names_apart_at_start
#print axioms EqualityOnTheStep.Options.QuotientDiscipline.unwitnessedTell_undisciplined
#print axioms EqualityOnTheStep.Options.QuotientDiscipline.unwitnessedRead_undisciplined
#print axioms EqualityOnTheStep.Options.QuotientDiscipline.sound_disciplined
#print axioms EqualityOnTheStep.Options.QuotientDiscipline.discipline_controls
#print axioms EqualityOnTheStep.Options.QuotientDiscipline.tells_alone_insufficient
#print axioms EqualityOnTheStep.Options.QuotientDiscipline.soundness_needs_identification
#print axioms EqualityOnTheStep.Options.QuotientDiscipline.witnessed_symm
#print axioms EqualityOnTheStep.Options.QuotientDiscipline.witnessed_trans
#print axioms EqualityOnTheStep.Options.QuotientDiscipline.published_witnessed
#print axioms EqualityOnTheStep.Options.QuotientDiscipline.identified_witnessed
#print axioms EqualityOnTheStep.Options.QuotientDiscipline.writer_publishes_without_evidence
#print axioms EqualityOnTheStep.Options.QuotientDiscipline.setsRegistry_run

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
