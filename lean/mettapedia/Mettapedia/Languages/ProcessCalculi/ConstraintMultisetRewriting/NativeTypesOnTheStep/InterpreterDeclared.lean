import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.DeclaredComputation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.TypedInterpreter

/-!
# The typed interpreter returns at its declared type once its value type computes

`ProgrammingOnTheStep.TypedInterpreter` runs `eval : Π (t : ty). exp t → val t` on the dependent full
step in a package where every constant is rigid. Its answer `n : nat` never has the declared type
`val tnat` there: handing it to a hole of that type is refused (`TypedInterpreter.return_refused`).

Here the program declares one computing rule, `val tnat ↦ nat` (`valComputation`): the large
elimination of the value type, as a rewrite rule of conversion (`val_computes`). Then:

* **The rule makes its answer at the declared type** (`answer_at_declared_type`): `n : nat` is typed at
  `val tnat` in the rule's own frame, so the present step, with no settling, admits the rule that
  takes the call `eval tnat (lit 3)` and makes `n` at `val tnat` (`eval_admitted_at_declared_type`).
* **Returning to a hole of the declared type is admitted** (`return_admitted`), where the rigid
  package refuses it (`return_separation`).
* **Coherence**: telling `val tnat ≐ nat` in addition changes no admission (`tell_val_coherent`).

The declaration passes the check (`val_rootDeterministic`): `val tnat` has one reduct.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.InterpreterDeclared

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull
open ProgrammingOnTheStep.VectorPackage (u0 U0 natN natC zeroN zeroC succN succC)
open ProgrammingOnTheStep.TypedInterpreter

/-- **The value type computes**: `val tnat ↦ nat`. -/
inductive ValStep : {n : Nat} → Tower.Tm n → Tower.Tm n → Prop
  | tnat {n : Nat} : ValStep (n := n) (.app (.const valN) (.const tnatN)) (.const natN)

/-- The declared root computation of the value type. -/
def valComputation : RootComputation Tower.Head where
  step l r := ValStep l r
  rename := by
    intro n m ρ left right h
    exact match h with
      | .tnat => ValStep.tnat
  substitute := by
    intro n m σ left right h
    exact match h with
      | .tnat => ValStep.tnat

/-- **The interpreter's package with its value type declared computing.** -/
abbrev irules : Rules Tower.Head := declare rules valComputation

abbrev ilevels : LevelModel irules Nat := declareLevels levels valComputation

theorem ityped {n : Nat} {Γ : Tower.Ctx n} {t A : Tower.Tm n} (typed : Typed rules Γ t A) :
    Typed irules Γ t A :=
  typed_declare valComputation typed

/-- The declaration passes the check. -/
theorem val_rootDeterministic : RootDeterministic valComputation := by
  intro n l r r' h h'
  cases h
  cases h'
  rfl

/-- **`val tnat ≡ nat`**, in every context. -/
theorem val_computes {n : Nat} (Γ : Tower.Ctx n) : Equal irules Γ (valC tnatC) natC U0 :=
  .root (declare_step ValStep.tnat) (ityped (val_typed (tnat_typed _))) (ityped (nat_typed _))

def ivalOf (Γ : Context irules) : TypeOver Γ := ⟨valC tnatC, u0, .sort _, ityped (val_typed (tnat_typed _))⟩
def inatOf (Γ : Context irules) : TypeOver Γ := ⟨natC, u0, .sort _, ityped (nat_typed _)⟩

/-! ## The rule makes its answer at the declared type -/

/-- The call `eval tnat (lit 3) : val tnat`. -/
def icallRow : TotalTerm (empty irules) :=
  ⟨ivalOf _, ⟨evalC tnatC (litC three), ityped (call_typed (three_typed _))⟩⟩

def icallState : State irules Nat := ⟨empty irules, [], {0}, fun _ => icallRow⟩

/-- The frame `n : nat`. -/
abbrev iruleFrame : Context irules := extend (empty irules) (inatOf _)

/-- The left side `eval tnat (lit n) : val tnat`. -/
def ievalPattern : TotalTerm iruleFrame :=
  ⟨ivalOf _, ⟨evalC tnatC (litC (.var 0)),
    ityped (call_typed (Derivable.var (R := rules) (Γ := iruleFrame.raw) (0 : Fin 1)))⟩⟩

/-- **The answer `n : nat` has the declared type `val tnat`** in the rule's frame. -/
theorem answer_at_declared_type : Typed irules iruleFrame.raw (.var 0) (valC tnatC) :=
  .conv (Derivable.var (R := irules) (Γ := iruleFrame.raw) (0 : Fin 1)) (.symm (val_computes _)) (.sort _)

/-- **The rule `eval tnat (lit n) = n`, making its answer at the declared type `val tnat`.** -/
def ievalFiring : Firing ilevels icallState where
  helpers := .cons (inatOf _) (.nil _)
  taken := [0]
  read := []
  takes := [ievalPattern]
  reads := []
  makes := [(1, ⟨ivalOf _, (.var 0 : Tower.Tm 1)⟩)]
  tells := []
  guards := []
  queries := []

def ievalSolution : empty irules ⟶ iruleFrame := pair (toEmpty (empty irules)) ⟨three, ityped (three_typed _)⟩

theorem ievalFiring_information : ievalFiring.information = [(ievalPattern, ievalFiring.row 0)] := rfl

theorem ieval_identifies : ievalPattern.reindex ievalSolution = (ievalFiring.row 0).reindex ievalSolution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

/-- **The present step admits it**: no settling is needed, the frame types the answer. -/
theorem eval_admitted_at_declared_type : (step ilevels Nat).Admits ievalFiring := by
  refine ⟨⟨List.nodup_singleton _, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
    (enabled_iff ievalFiring).mpr ⟨fun o member => ?_, fun _ member => absurd member List.not_mem_nil,
      fun _ _ readToo => absurd readToo List.not_mem_nil, fun o member inside => ?_⟩,
    ⟨empty irules, ievalSolution, ?_⟩, ?_⟩
  · obtain rfl := List.mem_singleton.mp member
    exact answer_at_declared_type
  · obtain rfl := List.mem_singleton.mp member
    exact Finset.mem_singleton_self 0
  · obtain rfl := List.mem_singleton.mp member
    exact absurd (Finset.mem_singleton.mp inside) (by decide)
  · rw [ievalFiring_information]
    intro e member
    obtain rfl := List.mem_singleton.mp member
    show (frames ilevels).E (ievalPattern.reindex ievalSolution) ((ievalFiring.row 0).reindex ievalSolution)
    rw [ieval_identifies]
    exact ((frames ilevels).equivalence _).refl _
  · intro b τ _
    exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

/-- **The answer is `3`, at the declared type.** -/
theorem eval_answer_at_declared_type :
    subst ievalSolution.substitution (.var 0 : Tower.Tm 1) = three ∧
      (((step ilevels Nat).result ievalFiring eval_admitted_at_declared_type).label 1).1.code = valC tnatC :=
  ⟨rfl, rfl⟩

/-! ## Returning to a hole of the declared type -/

/-- The frame `r : val tnat, n : nat`. -/
abbrev ireturnFrame : Context irules := extend (extend (empty irules) (ivalOf _)) (inatOf _)

def iemptyState : State irules Nat := ⟨empty irules, [], ∅, fun _ => icallRow⟩

def iholeRow : TotalTerm ireturnFrame := ⟨ivalOf _, ⟨.var 1, Derivable.var (R := irules) (Γ := ireturnFrame.raw) (1 : Fin 2)⟩⟩

def ianswerRow : TotalTerm ireturnFrame := ⟨inatOf _, ⟨.var 0, Derivable.var (R := irules) (Γ := ireturnFrame.raw) (0 : Fin 2)⟩⟩

/-- **Hand the answer to a hole of the declared type**: tell `(r : val tnat) ≐ (n : nat)`. -/
def ireturnFiring : Firing ilevels iemptyState where
  helpers := .cons (ivalOf _) (.cons (inatOf _) (.nil _))
  taken := []
  read := []
  takes := []
  reads := []
  makes := []
  tells := [(iholeRow, ianswerRow)]
  guards := []
  queries := []

/-- The frame `n : nat`, where the return is solved. -/
abbrev answerFrame : Context irules := extend (empty irules) (inatOf _)

theorem answerVar_val : Typed irules answerFrame.raw (.var 0) (valC tnatC) :=
  .conv (Derivable.var (R := irules) (Γ := answerFrame.raw) (0 : Fin 1)) (.symm (val_computes _)) (.sort _)

/-- `r ↦ n`, `n ↦ n`. -/
def returnSolution : answerFrame ⟶ ireturnFrame :=
  pair (pair (toEmpty answerFrame) ⟨.var 0, answerVar_val⟩)
    ⟨.var 0, Derivable.var (R := irules) (Γ := answerFrame.raw) (0 : Fin 1)⟩

theorem ireturnFiring_information : ireturnFiring.information = [(iholeRow, ianswerRow)] := rfl

/-- **The return is admitted** once the value type computes. -/
theorem return_admitted : (step ilevels Nat).Admits ireturnFiring := by
  refine ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, fun _ member => absurd member List.not_mem_nil⟩,
    (enabled_iff ireturnFiring).mpr ⟨fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil⟩, ⟨answerFrame, returnSolution, ?_⟩, ?_⟩
  · rw [ireturnFiring_information]
    intro e member
    obtain rfl := List.mem_singleton.mp member
    exact (equivalent_iff ilevels _ _).mpr ⟨⟨u0, .sort _, val_computes _⟩, .refl answerVar_val⟩
  · intro b τ _
    exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

/-- **The separation**: refused where the value type is rigid, admitted where it computes. -/
theorem return_separation :
    ¬ (step levels Nat).Admits returnFiring ∧ (step ilevels Nat).Admits ireturnFiring :=
  ⟨return_refused, return_admitted⟩

/-! ## Coherence -/

/-- `U0`, as a formed type over a frame of the declared package. -/
def smallUniverseOver (Γ : Context irules) : TypeOver Γ :=
  ⟨U0, .sort (.succ Tower.zero), .sort _, ityped (.headType (.sort _))⟩

/-- **Telling `val tnat ≐ nat` in addition changes no admission.** -/
theorem tell_val_coherent :
    (step ilevels Nat).Admits
        (tellMore ilevels ireturnFiring (computingEquation (smallUniverseOver _)
          (ityped (val_typed (tnat_typed _))) (ityped (nat_typed _)))) ↔
      (step ilevels Nat).Admits ireturnFiring :=
  admits_tellMore_iff ilevels ireturnFiring _ (declare_step ValStep.tnat) _ _

end NativeTypesOnTheStep.InterpreterDeclared

#print axioms NativeTypesOnTheStep.InterpreterDeclared.val_rootDeterministic
#print axioms NativeTypesOnTheStep.InterpreterDeclared.val_computes
#print axioms NativeTypesOnTheStep.InterpreterDeclared.answer_at_declared_type
#print axioms NativeTypesOnTheStep.InterpreterDeclared.eval_admitted_at_declared_type
#print axioms NativeTypesOnTheStep.InterpreterDeclared.eval_answer_at_declared_type
#print axioms NativeTypesOnTheStep.InterpreterDeclared.return_admitted
#print axioms NativeTypesOnTheStep.InterpreterDeclared.return_separation
#print axioms NativeTypesOnTheStep.InterpreterDeclared.tell_val_coherent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
