import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EqualityOnTheStep.Options.QuotientDiscipline
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EqualityOnTheStep.Options.Observational
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EqualityOnTheStep.Options.Univalent
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EqualityOnTheStep.Computation

/-!
# The designs of extensional equality, and their consequences

Each row below is a theorem that bundles the results it rests on. The common law is
`Observability`: on the step, absence and counting read the knowledge, so an extension of the
knowledge's equality is invisible to queries exactly when it identifies nothing new
(`Observability.conservative_iff`, `Observability.count_conservative_iff`).

| design | what stays decidable | what transports automatically | what queries see | what must be rebuilt | set theory on the step |
|---|---|---|---|---|---|
| **A. evidence rows** with generated respect terms (built) | the knowledge, unchanged: transport keeps its solutions (`rowA`) | every family of the code class (membership, constants, `→`, `×`, `Π`, `Σ` over set-free domains), by one firing, coherently along reflexivity and composition; not the intensional identity family | exactly today's answers; absence of members of `S` does not become absence of members of `T` | nothing in the kernel | comprehension definitional; extensionality as evidence with transport; union one universe up; quotients through class names (row D) |
| **B. observational**, propositions proof-irrelevant (model) | must be re-proved: the normalization hypotheses listed in `Observational` | in the model every family of predicate-sets (the sets are equal) | `S` and `T` stay apart judgmentally, so their answers stay separate; proofs of one proposition are identified, so counts of members collapse (`rowB`) | the normalization model, η-long forms, unifier completeness; the intensional identity type gains inhabitants | extensionality for predicate-sets; the proof-relevant `Σ X Ground` only through its truncation |
| **C. univalent** (model) | must be built: interval, Kan operations, unification modulo faces | in the model, the decoding family and the path family, coherently; counting along equivalences (`rowC`) | paths are terms, so answers stay separate unless the interval enters the knowledge | the conversion with an interval; identity with unique proofs cannot be kept | sets equal up to equivalence, transport computes the swap |
| **D. class names** with the publication discipline | the knowledge stays an equational theory of names | classes identified only with evidence, closed under equivalence (`rowD`) | identified classes are counted together; an unwitnessed identification would change answers and is refused | a discipline on the rule set covering tells and read matchings | quotients of sets by extensional equality |
| **R. reflection** (forced negative) | lost in general | everything | `S` and `T` identified, so their absence and counts merge (`rowR`) | the step refuses it today | extensionality as an equation |

**Combinations** (`combinationAB`, `combinationAC`). Evidence rows for data and the
proof-irrelevant universe for propositions combine coherently through truncation, and stop at
families that count members. Evidence that is an equivalence, as the swaps are, also transports
counting, as the univalent model does.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace EqualityOnTheStep.Options.Consequences

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull Interface.DependentFull.Controls
open ProgrammingOnTheStep.SetExtensionality (small U0 sCode tCode setType swapCode swapType
  swapBackType setType_formed s_typed t_typed swap_typed swapBack_typed sRow tRow)
open Observability (CountUnder AbsentUnder count_changes)

/-- **Row A: evidence rows with generated respect terms.** The knowledge keeps its solutions under
transport; every well-formed code has a typed respect term; the generated transport is the identity
along reflexivity and composes along composite evidence, and so does the row the transport firing
makes; the identity family is outside the class; a respect term that is only typed need not be
coherent; absence does not transport. -/
theorem rowA :
    (∀ (st : State Tower.rules Nat) (i j k : Nat) (σ : st.frame ⟶ Transport.Omega),
        (frames setting.levels).Equivalent (Transport.transportBy st i j k σ).information st.knowledge) ∧
      (∀ {n : Nat} {Γ : Tower.Ctx n} {c : Respect.FamCode n}, Respect.WF Γ c →
        Typed Tower.rules Γ (Respect.respOf c) (respType (Respect.famOf c))) ∧
      (∀ {n : Nat} {Γ : Tower.Ctx n} {c : Respect.FamCode n}, Respect.WF Γ c →
        ∀ {S M : Tower.Tm n}, Typed Tower.rules Γ S setType → Typed Tower.rules Γ M (Respect.inst c ids S) →
          Equal Tower.rules Γ (Respect.tr true c ids S S Respect.reflE M) M (Respect.inst c ids S)) ∧
      (∀ {n : Nat} {Γ : Tower.Ctx n} {c : Respect.FamCode n}, Respect.WF Γ c →
        ∀ {S T U e e' M : Tower.Tm n}, Typed Tower.rules Γ S setType → Typed Tower.rules Γ T setType →
          Typed Tower.rules Γ U setType → Typed Tower.rules Γ e (setEq S T) → Typed Tower.rules Γ e' (setEq T U) →
          Typed Tower.rules Γ M (Respect.inst c ids S) →
          Equal Tower.rules Γ (Respect.tr true c ids S U (Respect.compE e e') M)
            (Respect.tr true c ids T U e' (Respect.tr true c ids S T e M)) (Respect.inst c ids U)) ∧
      (∀ {n : Nat} {Γ : Tower.Ctx n} {c : Respect.FamCode n}, Respect.WF Γ c →
        ∀ {S M : Tower.Tm n}, Typed Tower.rules Γ S setType → Typed Tower.rules Γ M (.app (Respect.famOf c) S) →
          Equal Tower.rules Γ (.app (.app (.app (.app (Respect.respOf c) S) S) Respect.reflE) M) M
            (.app (Respect.famOf c) S)) ∧
      (∀ {n : Nat} {Γ : Tower.Ctx n}, CtxFormed Tower.rules Γ → ∀ {c : Respect.FamCode n}, Respect.WF Γ c →
        ∀ {S T U e e' M : Tower.Tm n}, Typed Tower.rules Γ S setType → Typed Tower.rules Γ T setType →
          Typed Tower.rules Γ U setType → Typed Tower.rules Γ e (setEq S T) → Typed Tower.rules Γ e' (setEq T U) →
          Typed Tower.rules Γ M (.app (Respect.famOf c) S) →
          Equal Tower.rules Γ (.app (.app (.app (.app (Respect.respOf c) S) U) (Respect.compE e e')) M)
            (.app (.app (.app (.app (Respect.respOf c) T) U) e') (.app (.app (.app (.app (Respect.respOf c) S) T) e) M))
            (.app (Respect.famOf c) U)) ∧
      (∀ {c : Respect.FamCode 0}, Respect.WF .nil c → ¬ Equal Tower.rules .nil (Respect.famOf c) Controls.idFamily famType) ∧
      (Typed Tower.rules Respect.twoPoints.raw Respect.badRespect (respType (Respect.famOf Respect.groundCode)) ∧
        ¬ Equal Tower.rules Respect.twoPoints.raw
          (.app (.app (.app (.app Respect.badRespect sCode) sCode) Respect.reflE) (.var 0)) (.var 0)
          (.app (Respect.famOf Respect.groundCode) sCode)) ∧
      ((step setting.levels Nat).Admits Controls.absentS ∧ ¬ (step setting.levels Nat).Admits Controls.absentT) :=
  ⟨Observability.transportBy_equivalent, fun {_ _ _} wf => Respect.respOf_typed wf,
    fun {_ _ _} wf {_ _} hS hM => Respect.respOf_refl wf hS hM,
    fun {_ _ _} wf {_ _ _ _ _ _} hS hT hU he he' hM => Respect.respOf_comp wf hS hT hU he he' hM,
    fun {_ _ _} wf {_ _} hS hM => Respect.made_row_refl wf hS hM,
    fun {_ _} formed {_} wf {_ _ _ _ _ _} hS hT hU he he' hM => Respect.made_row_comp formed wf hS hT hU he he' hM,
    fun {_} wf => Respect.idFamily_outside wf,
    ⟨Respect.incoherent_respect.1, Respect.incoherent_respect.2.1⟩,
    ⟨Controls.absentS_admitted, Controls.absentT_refused⟩⟩

/-- **Row A's universal statements have instances**: membership at `X`, the sets `S` and `T`, the
swaps' evidence and the member `(x, g)` satisfy the hypotheses of reflexivity and composition
coherence, and transport by the generated respect term is admitted. -/
theorem rowA_instances :
    Equal Tower.rules triple.raw (Respect.tr true Respect.memberCode ids sCode sCode Respect.reflE (.pair (.var 1) (.var 0)))
        (.pair (.var 1) (.var 0)) (Respect.inst Respect.memberCode ids sCode) ∧
      Equal Tower.rules triple.raw
        (Respect.tr true Respect.memberCode ids sCode tCode (Respect.compE Run.evidenceAt Respect.reflE)
          (.pair (.var 1) (.var 0)))
        (Respect.tr true Respect.memberCode ids tCode tCode Respect.reflE
          (Respect.tr true Respect.memberCode ids sCode tCode Run.evidenceAt (.pair (.var 1) (.var 0))))
        (Respect.inst Respect.memberCode ids tCode) ∧
      (step setting.levels Nat).Admits
        (Transport.transportBy (Transport.classified triple Transport.memberClassifier) 0 1 2 Transport.memberClassifier) :=
  ⟨Respect.respOf_refl Respect.memberCode_wf (s_typed _) Run.member_typed,
    Respect.respOf_comp Respect.memberCode_wf (s_typed _) (t_typed _) (t_typed _) Run.evidenceAt_typed
      (Respect.reflE_typed (t_typed _)) Run.member_typed,
    Transport.classified_transport_admitted triple Transport.memberClassifier⟩

/-- **The observability theorem on the step has an instance**: at the frame of the class names,
the knowledge `q₁ ≐ q₂` against the empty knowledge. -/
theorem knowledge_observed_instance :
    ¬ (step setting.levels Nat).Admits (Observability.countFiring ⟨Quotient.qFrame, [], {0}, fun _ => Quotient.q2Row⟩
        Quotient.q1Row 1) ∧
      (step setting.levels Nat).Admits (Observability.countFiring
        ⟨Quotient.qFrame, [(Quotient.q1Row, Quotient.q2Row)], {0}, fun _ => Quotient.q2Row⟩ Quotient.q1Row 1) := by
  refine Observability.knowledge_observed (fun _ _ solved => solved _ (List.Mem.head _)) ?_
    QuotientDiscipline.names_apart_at_start
  refine ⟨pairFrame, Quotient.nameSolution, ?_⟩
  intro e member
  obtain rfl := List.mem_singleton.mp member
  show (frames setting.levels).E (Quotient.q1Row.reindex Quotient.nameSolution)
    (Quotient.q2Row.reindex Quotient.nameSolution)
  rw [Quotient.names_identified]
  exact ((frames setting.levels).equivalence _).refl _

/-- **Row B: propositions in a proof-irrelevant universe.** In the predicate-family model the two
sets are equal and their members carry no information, while the set-family model counts two
members; in the knowledge, identifying proofs changes a count; the intensional identity of the two
sets, uninhabited in the syntax, is inhabited in the model; the judgmental refusal of `S ≐ T`
stands. -/
theorem rowB :
    (∀ G : Prop, Observational.sPred G = Observational.tPred G) ∧
      (∀ (G : Prop) (m m' : (Mettapedia.TypeTheory.ContextualPredicateFamilies.model.{1}).Tm Observational.smallTypes
          (Observational.sPred G)), m = m') ∧
      (∃ a b : Observational.sFam Unit Bool, a ≠ b) ∧
      (∀ (E' : TotalTerm Observability.quad → TotalTerm Observability.quad → Prop),
        (∀ a b, (frames setting.levels).E a b → E' a b) → E' Observability.member1 Observability.member2 →
          ¬ CountUnder E' Observability.member1 ({0, 1} : Finset Nat) Observability.memberRows 1) ∧
      (∀ G : Prop, Observational.tPred G = Observational.sPred G) ∧
      (∀ {t : Tower.Tm 0}, ¬ Typed Tower.rules .nil t (.id setType tCode sCode)) ∧
      ¬ (step setting.levels Nat).Admits ProgrammingOnTheStep.SetExtensionality.extensionalityFiring :=
  ⟨Observational.sets_equal, Observational.members_irrelevant, Observational.setFamily_counts_two,
    fun E' extension irrelevant => (Observability.proofIrrelevance_observed E' extension irrelevant).2,
    Observational.id_inhabited_in_model, Controls.idSets_uninhabited,
    ProgrammingOnTheStep.SetExtensionality.extensionality_refused⟩

/-- **Row C: univalent equality, in the model.** The two sets are joined by the swap, transport
along it computes the swapped pair and round trips; the path family transports coherently;
equivalences preserve counts; an identity of types with unique proofs is not univalent. -/
theorem rowC :
    (∀ (G X : Type) (x : X) (g : G), Univalent.transport (Univalent.swapPath G X) (x, g) = (g, x)) ∧
      (∀ (G X : Type) (p : Univalent.sFam G X),
        Univalent.transport (Univalent.swapPath G X).symm (Univalent.transport (Univalent.swapPath G X) p) = p) ∧
      (∀ {S₀ R : Type → Type} (p : Univalent.PathFamily S₀ R),
        Univalent.pathFamily_transport (Univalent.SetPath.rfl R) p = p) ∧
      (∀ {A B : Type}, Univalent.Path A B → Nat.card A = Nat.card B) ∧
      ¬ Function.Surjective (fun h : Bool = Bool => Equiv.cast h) :=
  ⟨Univalent.transport_swap, Univalent.swap_round_trip, Univalent.pathFamily_transport_refl,
    Univalent.count_respected, Univalent.uip_not_univalent⟩

/-- **Row D: class names under the publication discipline.** The evidence-free tell and read are
admitted by the step and refused by the disciplined step, soundness passes; restricting tells alone
is not enough; under the sole-writer policy every entailed identification of classes is witnessed;
and an unwitnessed identification is observed by a count. -/
theorem rowD :
    ((step setting.levels Nat).Admits Quotient.unwitnessedTell ∧
        ¬ QuotientDiscipline.DisciplinedAdmits (st := Quotient.quotientStart) QuotientDiscipline.quotientClasses
          Quotient.unwitnessedTell ∧
        (step setting.levels Nat).Admits QuotientDiscipline.unwitnessedRead ∧
        ¬ QuotientDiscipline.DisciplinedAdmits (st := Quotient.quotientStart) QuotientDiscipline.quotientClasses
          QuotientDiscipline.unwitnessedRead ∧
        QuotientDiscipline.DisciplinedAdmits (st := Quotient.quotientStart) QuotientDiscipline.quotientClasses
          Quotient.soundFiring) ∧
      QuotientDiscipline.unwitnessedRead.tells = [] ∧
      (∀ {N L I : Type} (reg : QuotientDiscipline.Registry N L I), reg.SoleWriter →
        ∀ {store : List (N × N)}, QuotientDiscipline.Published reg store → ∀ {n₁ n₂ : N},
          Relation.EqvGen (fun a b => (a, b) ∈ store) n₁ n₂ →
            QuotientDiscipline.Witnessed (reg.setOf n₁) (reg.setOf n₂)) ∧
      (¬ (step setting.levels Nat).Admits Quotient.countBefore ∧
        (step setting.levels Nat).Admits Observability.countAfterTell) :=
  ⟨QuotientDiscipline.discipline_controls, rfl,
    fun {_ _ _} reg sole {_} published {_ _} identified =>
      QuotientDiscipline.identified_witnessed reg sole published identified,
    Observability.unwitnessed_tell_observed⟩

/-- **The two sets are apart in the knowledge.** -/
theorem sets_apart_rows : ¬ (frames setting.levels).E (sRow (empty Tower.rules)) (tRow (empty Tower.rules)) :=
  fun same => Quotient.sets_apart (Θ := empty Tower.rules) same.2

/-- **Row R: reflection, the forced negative.** The step refuses telling `S ≐ T`; and any extension
of the knowledge's equality that identifies the two sets, as equality reflection would, changes the
count of `S` among the one row `T` from `0`, and loses the absence of `S` there. -/
theorem rowR :
    ¬ (step setting.levels Nat).Admits ProgrammingOnTheStep.SetExtensionality.extensionalityFiring ∧
      ∀ (E' : TotalTerm (empty Tower.rules) → TotalTerm (empty Tower.rules) → Prop),
        (∀ a b, (frames setting.levels).E a b → E' a b) → E' (sRow _) (tRow _) →
          (CountUnder (frames setting.levels).E (sRow (empty Tower.rules)) ({0} : Finset Nat)
              (fun _ => tRow (empty Tower.rules)) 0 ∧
            ¬ CountUnder E' (sRow (empty Tower.rules)) ({0} : Finset Nat) (fun _ => tRow (empty Tower.rules)) 0) ∧
          (AbsentUnder (frames setting.levels).E (sRow (empty Tower.rules)) ({0} : Finset Nat)
              (fun _ => tRow (empty Tower.rules)) ∧
            ¬ AbsentUnder E' (sRow (empty Tower.rules)) ({0} : Finset Nat) (fun _ => tRow (empty Tower.rules))) := by
  refine ⟨ProgrammingOnTheStep.SetExtensionality.extensionality_refused, fun E' extension identified => ?_⟩
  have today := Observability.count_zero_of_apart (0 : Nat) sets_apart_rows
  exact ⟨⟨today, count_changes extension (Finset.mem_singleton_self 0) identified sets_apart_rows today⟩,
    fun _ _ => sets_apart_rows, Observability.absence_changes (Finset.mem_singleton_self 0) identified⟩

/-- **A with B: coherent through truncation, up to counting.** Evidence between proof-relevant sets
gives equal truncations, so families of predicate-sets transport along it; a family that counts
members does not. -/
theorem combinationAB :
    (∀ {S T : Mettapedia.GSLT.Core.ContextualLadder.familiesCwf.{1}.Ty Type},
        Observational.SetEvidence S T → Observational.truncate S = Observational.truncate T) ∧
      (Nonempty (Observational.SetEvidence Observational.boolSet Observational.unitSet) ∧
        Observational.TwoMembers Bool Observational.boolSet ∧
        ¬ Observational.TwoMembers Bool Observational.unitSet) :=
  ⟨fun {_ _} e => Observational.truncate_respects e, Observational.counting_not_respected⟩

/-- **A with C: evidence that is an equivalence transports counting.** The swaps are mutually
inverse in the knowledge, and in the univalent model equivalent types have the same number of
elements. -/
theorem combinationAC :
    (∀ {n : Nat} (Γ : Tower.Ctx n),
        Equal Tower.rules (Computation.roundFrame Γ)
          (.app (.app swapCode (.var 1)) (.app (.app swapCode (.var 1)) (.var 0))) (.var 0) (.sigma (.var 1) ground)) ∧
      (∀ (G X : Type), Nat.card (Univalent.sFam G X) = Nat.card (Univalent.tFam G X)) :=
  ⟨Computation.swap_round_trip, fun G X => Univalent.count_respected (Univalent.swapPath G X)⟩

end EqualityOnTheStep.Options.Consequences

#print axioms EqualityOnTheStep.Options.Consequences.rowA
#print axioms EqualityOnTheStep.Options.Consequences.rowA_instances
#print axioms EqualityOnTheStep.Options.Consequences.knowledge_observed_instance
#print axioms EqualityOnTheStep.Options.Consequences.rowB
#print axioms EqualityOnTheStep.Options.Consequences.rowC
#print axioms EqualityOnTheStep.Options.Consequences.rowD
#print axioms EqualityOnTheStep.Options.Consequences.sets_apart_rows
#print axioms EqualityOnTheStep.Options.Consequences.rowR
#print axioms EqualityOnTheStep.Options.Consequences.combinationAB
#print axioms EqualityOnTheStep.Options.Consequences.combinationAC

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
