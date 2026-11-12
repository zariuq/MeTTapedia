import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EqualityOnTheStep.Quotient

/-!
# Queries observe the equality of the knowledge

On the step, absence and counting are asked of the present rows through the knowledge: a query's
region at a solution is the set of rows the solution equates with its pattern (`Query.absent`,
`Query.count`). So the equality the knowledge decides is observable, and every extension of it that
identifies two rows not identified before changes the answer of a count query.

**Under a relation** (`CountUnder`, `AbsentUnder`). For relations `E ≤ E'` on rows:

* `count_changes`: if `E'` relates the pattern to a present row that `E` does not, no number counts
  the pattern under both;
* `absence_changes`: if `E'` relates the pattern to a present row, its absence fails under `E'`;
* `count_conservative_iff`, `absence_conservative_iff`: **`E'` leaves every count (every absence)
  answer unchanged exactly when it relates nothing that `E` does not relate**.

**Under a knowledge** (`EntailsEqual`, `CountAnswer`, `AbsentAnswer`), for any frames of the step's
interface. A store's answer to a query holds when the query holds at every solution of the store.

* `extension_observed`: if a store `K'` entails an equation `s ≐ t` that `K` does not entail, the
  count of `s` among the one row `t` is `1` under `K'` and is not `1` under `K`;
* `answers_of_equivalent`: stores with the same solutions give the same answers;
* `conservative_iff`: **for a refinement `K'` of `K`, every count answer is unchanged exactly when
  every equation `K'` entails is already entailed by `K`.**

**On the dependent full step** (`countFiring`, `countFiring_admits_iff`, `knowledge_observed`): the
firing asking that count is refused at the state with knowledge `K` and admitted at the state with
knowledge `K'`.

**The designs, read through it.**

* *Evidence rows (the built design)*: a transport firing's information has the solutions of the
  knowledge it starts from (`transportBy_equivalent`), so every count and absence answer about any
  rows is the one the old knowledge gives (`transport_answers`). This is why absence does not
  transport (`Controls.absence_does_not_transport`): nothing was identified.
* *Class names*: the evidence-free tell of `Quotient.unwitnessedTell` is observed: the count of
  `(S, q₂)` that `Quotient.countBefore_refused` refuses is admitted after it (`unwitnessed_tell_observed`).
  An unwitnessed class equation is therefore not harmless; it changes answers.
* *A proof-irrelevant knowledge*: two members `(x, g)` and `(x, g')` of `S X` are apart in today's
  knowledge (`members_apart`); any extension of the equality relating them, as definitional proof
  irrelevance would if `S X` were a proposition, changes the count of members from `1`
  (`proofIrrelevance_observed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace EqualityOnTheStep.Options.Observability

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull Interface.DependentFull.Controls
open ProgrammingOnTheStep.SetExtensionality (small U0 sCode tCode setType swapCode swapType
  swapBackType setType_formed s_typed t_typed swap_typed swapBack_typed)

universe uR uO uObj uTm uHom

/-! ## Counting and absence under a relation -/

section Relations

variable {R : Type uR} {O : Type uO}

/-- **Exactly `number` present rows are related to the pattern.** -/
def CountUnder (E : R → R → Prop) (pattern : R) (present : Finset O) (row : O → R) (number : Nat) :
    Prop :=
  ∃ seen : Finset O, (∀ o, o ∈ seen ↔ o ∈ present ∧ E pattern (row o)) ∧ seen.card = number

/-- **No present row is related to the pattern.** -/
def AbsentUnder (E : R → R → Prop) (pattern : R) (present : Finset O) (row : O → R) : Prop :=
  ∀ o ∈ present, ¬ E pattern (row o)

/-- **An extension that relates the pattern to one more present row changes every count of it.** -/
theorem count_changes {E E' : R → R → Prop} (extension : ∀ a b, E a b → E' a b)
    {pattern : R} {present : Finset O} {row : O → R} {o : O} (inside : o ∈ present)
    (identified : E' pattern (row o)) (apart : ¬ E pattern (row o)) {number : Nat}
    (before : CountUnder E pattern present row number) :
    ¬ CountUnder E' pattern present row number := by
  obtain ⟨seen, members, card⟩ := before
  rintro ⟨seen', members', card'⟩
  have sub : seen ⊆ seen' := fun x hx => by
    obtain ⟨p, e⟩ := (members x).mp hx
    exact (members' x).mpr ⟨p, extension _ _ e⟩
  have strict : seen ⊂ seen' := (Finset.ssubset_iff_of_subset sub).mpr
    ⟨o, (members' o).mpr ⟨inside, identified⟩, fun hx => apart ((members o).mp hx).2⟩
  have smaller := Finset.card_lt_card strict
  omega

/-- **An extension that relates the pattern to a present row loses its absence.** -/
theorem absence_changes {E' : R → R → Prop} {pattern : R} {present : Finset O} {row : O → R} {o : O}
    (inside : o ∈ present) (identified : E' pattern (row o)) : ¬ AbsentUnder E' pattern present row :=
  fun absent => absent o inside identified

/-- With one present row `b` apart from the pattern `a`, the count of `a` is `0`. -/
theorem count_zero_of_apart {E : R → R → Prop} {a b : R} (o : O) (apart : ¬ E a b) :
    CountUnder E a {o} (fun _ => b) 0 :=
  ⟨∅, fun x => ⟨fun h => absurd h (Finset.notMem_empty x), fun h => absurd h.2 apart⟩, rfl⟩

/-- **Exactness for counting**: an extension `E'` of `E` leaves every count answer unchanged if and
only if it relates nothing that `E` does not relate. -/
theorem count_conservative_iff (o : O) {E E' : R → R → Prop} (extension : ∀ a b, E a b → E' a b) :
    (∀ (pattern : R) (present : Finset O) (row : O → R) (number : Nat),
        CountUnder E pattern present row number ↔ CountUnder E' pattern present row number) ↔
      ∀ a b, E' a b → E a b := by
  constructor
  · intro same a b identified
    by_contra apart
    have before : CountUnder E a {o} (fun _ => b) 0 := count_zero_of_apart o apart
    exact count_changes extension (Finset.mem_singleton_self o) identified apart before
      ((same a {o} (fun _ => b) 0).mp before)
  · intro back
    have equal : E = E' := funext fun a => funext fun b => propext ⟨extension a b, back a b⟩
    subst equal
    exact fun _ _ _ _ => Iff.rfl

/-- **Exactness for absence**: the same, for the absence answers. -/
theorem absence_conservative_iff (o : O) {E E' : R → R → Prop} (extension : ∀ a b, E a b → E' a b) :
    (∀ (pattern : R) (present : Finset O) (row : O → R),
        AbsentUnder E pattern present row ↔ AbsentUnder E' pattern present row) ↔
      ∀ a b, E' a b → E a b := by
  constructor
  · intro same a b identified
    by_contra apart
    have before : AbsentUnder E a {o} (fun _ => b) := by
      intro x _
      exact apart
    exact absence_changes (Finset.mem_singleton_self o) identified ((same a {o} (fun _ => b)).mp before)
  · intro back
    have equal : E = E' := funext fun a => funext fun b => propext ⟨extension a b, back a b⟩
    subst equal
    exact fun _ _ _ => Iff.rfl

end Relations

/-! ## Counting and absence under a knowledge -/

section Knowledge

variable {Obj : Type uObj} {Tm : Obj → Type uTm} {Hom : Obj → Obj → Type uHom} (X : Frames Tm Hom)
variable {O : Type uO}

/-- **A store entails an equation** when every solution of it equates the two sides. -/
def EntailsEqual {a : Obj} (K : EquationStore (Tm a)) (s t : Tm a) : Prop :=
  X.Entails K (fun _ f => X.E (X.act f s) (X.act f t))

/-- **A store's count answer**: the count holds at every solution of the store. -/
def CountAnswer {a : Obj} (K : EquationStore (Tm a)) (pattern : Tm a) (present : Finset O)
    (row : O → Tm a) (number : Nat) : Prop :=
  X.Entails K (fun _ f => CountUnder (fun s t => X.E (X.act f s) (X.act f t)) pattern present row number)

/-- **A store's absence answer**: the absence holds at every solution of the store. -/
def AbsentAnswer {a : Obj} (K : EquationStore (Tm a)) (pattern : Tm a) (present : Finset O)
    (row : O → Tm a) : Prop :=
  X.Entails K (fun _ f => AbsentUnder (fun s t => X.E (X.act f s) (X.act f t)) pattern present row)

/-- **A store that entails one more equation answers a count differently**: the count of `s` among
the one row `t` is `1` under `K'` and is not `1` under `K`. -/
theorem extension_observed {a : Obj} {K K' : EquationStore (Tm a)} {s t : Tm a}
    (identifies : EntailsEqual X K' s t) (notEntailed : ¬ EntailsEqual X K s t) (o : O) :
    CountAnswer X K' s {o} (fun _ => t) 1 ∧ ¬ CountAnswer X K s {o} (fun _ => t) 1 := by
  constructor
  · intro b f solved
    exact ⟨{o}, fun x => ⟨fun h => ⟨h, identifies b f solved⟩, fun h => h.1⟩, Finset.card_singleton o⟩
  · intro answer
    apply notEntailed
    intro b f solved
    obtain ⟨seen, members, card⟩ := answer b f solved
    obtain ⟨x, single⟩ := Finset.card_eq_one.mp card
    have inside : x ∈ seen := by rw [single]; exact Finset.mem_singleton_self x
    exact ((members x).mp inside).2

/-- **The absence form**: if `K` entails that `s` and `t` are apart and a solvable `K'` entails
`s ≐ t`, the absence of `s` beside the row `t` holds under `K` and fails under `K'`. -/
theorem extension_observed_absence {a : Obj} {K K' : EquationStore (Tm a)} {s t : Tm a}
    (identifies : EntailsEqual X K' s t) (solvable : X.Solvable K')
    (apart : X.Entails K (fun _ f => ¬ X.E (X.act f s) (X.act f t))) (o : O) :
    AbsentAnswer X K s {o} (fun _ => t) ∧ ¬ AbsentAnswer X K' s {o} (fun _ => t) := by
  constructor
  · intro b f solved x _
    exact apart b f solved
  · intro answer
    obtain ⟨b, f, solved⟩ := solvable
    exact answer b f solved o (Finset.mem_singleton_self o) (identifies b f solved)

/-- **Stores with the same solutions give the same count and absence answers.** -/
theorem answers_of_equivalent {a : Obj} {K K' : EquationStore (Tm a)} (same : X.Equivalent K K')
    (pattern : Tm a) (present : Finset O) (row : O → Tm a) :
    (∀ number, CountAnswer X K pattern present row number ↔ CountAnswer X K' pattern present row number) ∧
      (AbsentAnswer X K pattern present row ↔ AbsentAnswer X K' pattern present row) :=
  ⟨fun _ => ⟨fun h b f solved => h b f ((same b f).mpr solved), fun h b f solved => h b f ((same b f).mp solved)⟩,
    ⟨fun h b f solved => h b f ((same b f).mpr solved), fun h b f solved => h b f ((same b f).mp solved)⟩⟩

/-- **The conservative extensions are exactly those already entailed**: for a store `K'` whose
solutions solve `K` (for instance `K'` extends `K`), every count answer is unchanged if and only if
every equation that `K'` entails is entailed by `K`. -/
theorem conservative_iff {a : Obj} {K K' : EquationStore (Tm a)}
    (refines : ∀ (b : Obj) (f : Hom a b), X.Models f K' → X.Models f K) (o : O) :
    (∀ s t, EntailsEqual X K' s t → EntailsEqual X K s t) ↔
      ∀ (pattern : Tm a) (present : Finset O) (row : O → Tm a) (number : Nat),
        CountAnswer X K pattern present row number ↔ CountAnswer X K' pattern present row number := by
  constructor
  · intro entailed pattern present row number
    have same : X.Equivalent K K' := by
      intro b f
      refine ⟨fun solved e member => ?_, refines b f⟩
      exact entailed e.1 e.2 (fun b' f' solved' => solved' e member) b f solved
    exact (answers_of_equivalent X same pattern present row).1 number
  · intro same s t identifies
    by_contra notEntailed
    obtain ⟨after, before⟩ := extension_observed X identifies notEntailed o
    exact before ((same s {o} (fun _ => t) 1).mpr after)

end Knowledge

/-! ## On the dependent full step -/

/-- **A firing that only asks a count**: no helpers, no rows selected, nothing made or told. -/
def countFiring (st : State Tower.rules Nat) (pattern : TotalTerm st.frame) (number : Nat) :
    Firing setting.levels st where
  helpers := .nil _
  taken := []
  read := []
  takes := []
  reads := []
  makes := []
  tells := []
  guards := []
  queries := [Query.count setting.levels Nat pattern number]

theorem countFiring_information (st : State Tower.rules Nat) (pattern : TotalTerm st.frame) (number : Nat) :
    (countFiring st pattern number).information = st.knowledge :=
  information_plain setting.levels st.knowledge st.present st.label []
    [Query.count setting.levels Nat pattern number]

theorem countFiring_row (st : State Tower.rules Nat) (pattern : TotalTerm st.frame) (number : Nat) :
    (countFiring st pattern number).row = st.label :=
  funext fun o => (frames setting.levels).act_id (st.label o)

/-- **Admission of the count firing is the knowledge's count answer.** -/
theorem countFiring_admits_iff (st : State Tower.rules Nat) (pattern : TotalTerm st.frame) (number : Nat) :
    (step setting.levels Nat).Admits (countFiring st pattern number) ↔
      (frames setting.levels).Solvable st.knowledge ∧
        CountAnswer (frames setting.levels) st.knowledge pattern st.present st.label number := by
  have known := countFiring_information st pattern number
  have rows := countFiring_row st pattern number
  constructor
  · intro admitted
    obtain ⟨-, -, solvable, -, queries⟩ := (admits_iff (countFiring st pattern number)).mp admitted
    rw [known] at solvable
    refine ⟨solvable, fun b f solved => ?_⟩
    have asked := queries _ (List.Mem.head _) b f (by rw [known]; exact solved)
    rw [rows] at asked
    exact asked
  · rintro ⟨solvable, answer⟩
    refine (admits_iff (countFiring st pattern number)).mpr
      ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, fun _ member => absurd member List.not_mem_nil⟩,
      ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil,
        fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩,
      by rw [known]; exact solvable, fun b f _ e member => absurd member List.not_mem_nil,
      fun q member b f solved => ?_⟩
    rw [known] at solved
    obtain rfl := List.mem_singleton.mp member
    show (Query.count setting.levels Nat pattern number).Holds st.present (countFiring st pattern number).row f
    rw [rows]
    exact answer b f solved

/-- **On the step, a knowledge that entails one more equation is observed**: at the frame `Γ`, the
firing counting `s` among the one row `t` is refused under `K` and admitted under `K'`. -/
theorem knowledge_observed {Γ : Context Tower.rules} {K K' : EquationStore (TotalTerm Γ)} {s t : TotalTerm Γ}
    (identifies : EntailsEqual (frames setting.levels) K' s t) (solvable : (frames setting.levels).Solvable K')
    (notEntailed : ¬ EntailsEqual (frames setting.levels) K s t) :
    ¬ (step setting.levels Nat).Admits (countFiring ⟨Γ, K, {0}, fun _ => t⟩ s 1) ∧
      (step setting.levels Nat).Admits (countFiring ⟨Γ, K', {0}, fun _ => t⟩ s 1) := by
  obtain ⟨after, before⟩ := extension_observed (frames setting.levels) identifies notEntailed (0 : Nat)
  exact ⟨fun admitted => before ((countFiring_admits_iff _ _ _).mp admitted).2,
    (countFiring_admits_iff _ _ _).mpr ⟨solvable, after⟩⟩

/-! ## The built design is conservative: transport only makes rows -/

/-- **A transport firing's information has the solutions of the knowledge it starts from.** -/
theorem transportBy_equivalent (st : State Tower.rules Nat) (i j k : Nat) (σ : st.frame ⟶ Transport.Omega) :
    (frames setting.levels).Equivalent (Transport.transportBy st i j k σ).information st.knowledge := by
  have known : (frames setting.levels).applyStore (Transport.transportBy st i j k σ).helpers.weaken st.knowledge =
      st.knowledge := Frames.applyStore_id (X := frames setting.levels) st.knowledge
  have row_i : (Transport.transportBy st i j k σ).row i = st.label i := (frames setting.levels).act_id _
  have row_j : (Transport.transportBy st i j k σ).row j = st.label j := (frames setting.levels).act_id _
  intro b f
  constructor
  · intro solved e member
    have carried : e ∈ (frames setting.levels).applyStore (Transport.transportBy st i j k σ).helpers.weaken
        st.knowledge := by
      rw [known]
      exact member
    exact solved e (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ carried)))
  · intro solved e member
    rcases List.mem_append.mp member with front | told
    · rcases List.mem_append.mp front with front | readEq
      · rcases List.mem_append.mp front with knownEq | takenEq
        · rw [known] at knownEq
          exact solved e knownEq
        · exact absurd takenEq List.not_mem_nil
      · obtain ⟨x, inside, rfl⟩ := List.mem_map.mp readEq
        rcases List.mem_cons.mp inside with rfl | rest
        · show (frames setting.levels).E ((frames setting.levels).act f (st.label i))
            ((frames setting.levels).act f ((Transport.transportBy st i j k σ).row i))
          rw [row_i]
          exact ((frames setting.levels).equivalence _).refl _
        · obtain rfl := List.mem_singleton.mp rest
          show (frames setting.levels).E ((frames setting.levels).act f (st.label j))
            ((frames setting.levels).act f ((Transport.transportBy st i j k σ).row j))
          rw [row_j]
          exact ((frames setting.levels).equivalence _).refl _
    · exact absurd told List.not_mem_nil

/-- **Transport changes no answer through the knowledge**: after a transport firing, the knowledge
answers every count and every absence as the knowledge before it did. Only the rows change. -/
theorem transport_answers (st : State Tower.rules Nat) (i j k : Nat) (σ : st.frame ⟶ Transport.Omega)
    (admitted : (step setting.levels Nat).Admits (Transport.transportBy st i j k σ))
    (pattern : TotalTerm st.frame) (present : Finset Nat) (row : Nat → TotalTerm st.frame) :
    (∀ number, CountAnswer (frames setting.levels) ((step setting.levels Nat).result _ admitted).knowledge
        pattern present row number ↔ CountAnswer (frames setting.levels) st.knowledge pattern present row number) ∧
      (AbsentAnswer (frames setting.levels) ((step setting.levels Nat).result _ admitted).knowledge
        pattern present row ↔ AbsentAnswer (frames setting.levels) st.knowledge pattern present row) :=
  answers_of_equivalent (frames setting.levels) (transportBy_equivalent st i j k σ) pattern present row

/-! ## An unwitnessed class equation is observed -/

/-- The state after the evidence-free tell `q₁ ≐ q₂` of `Quotient.unwitnessedTell`. -/
abbrev told : State Tower.rules Nat :=
  (step setting.levels Nat).result Quotient.unwitnessedTell Quotient.unwitnessedTell_admitted

/-- After the tell, ask the count of `Quotient.countBefore`: exactly one row is `(S, q₂)`. -/
def countAfterTell : Firing setting.levels told where
  helpers := .nil _
  taken := []
  read := []
  takes := []
  reads := []
  makes := []
  tells := []
  guards := []
  queries := [Query.count setting.levels Nat Quotient.sq2Before 1]

theorem countAfterTell_information : countAfterTell.information = told.knowledge :=
  information_plain setting.levels told.knowledge told.present told.label []
    [Query.count setting.levels Nat Quotient.sq2Before 1]

/-- The knowledge after the tell is the told equation `q₁ ≐ q₂`. -/
theorem told_knowledge : told.knowledge = [(Quotient.q1Row, Quotient.q2Row)] :=
  Quotient.unwitnessedTell_information

/-- At every solution of the told knowledge, exactly one row is `(S, q₂)`: the row `(S, q₁)`. -/
theorem countAfterTell_holds {Θ : Context Tower.rules} (τ : Θ ⟶ Quotient.qFrame)
    (solved : (frames setting.levels).Models τ told.knowledge) :
    (Query.count setting.levels Nat Quotient.sq2Before 1).Holds told.present countAfterTell.row τ := by
  rw [told_knowledge] at solved
  have q1q2 : Equal Tower.rules Θ.raw (τ.substitution 1) (τ.substitution 0) (τ.substitution 2) :=
    (solved _ (List.Mem.head _)).2
  have formed : Typed Tower.rules Θ.raw (.sigma setType (Presentation.rename wk (τ.substitution 2))) (.head large) :=
    (Quotient.classOf_formed (Derivable.var 2) :
      Typed Tower.rules Quotient.qFrame.raw (Quotient.classOf (.var 2)) (.head large)).substitute τ.typed
  have t0 : Typed Tower.rules Θ.raw (τ.substitution 0) (τ.substitution 2) := τ.typed 0
  have row0 : (frames setting.levels).E ((frames setting.levels).act τ Quotient.sq2Before)
      ((frames setting.levels).act τ (countAfterTell.row 0)) := by
    refine (equivalent_iff setting.levels _ _).mpr ⟨IsType.refl ⟨large, .sort _, formed⟩, ?_⟩
    show Equal Tower.rules Θ.raw (.pair sCode (τ.substitution 0)) (.pair sCode (τ.substitution 1))
      (.sigma setType (Presentation.rename wk (τ.substitution 2)))
    have second : Equal Tower.rules Θ.raw (τ.substitution 0) (τ.substitution 1)
        (inst0 sCode (Presentation.rename wk (τ.substitution 2))) := by
      rw [inst0_rename_wk]
      exact .symm q1q2
    exact .pairCong formed (.sort _) (.refl (s_typed _)) second
  refine ⟨{0}, fun o => ⟨fun inside => ?_, fun ⟨present, region⟩ => ?_⟩, Finset.card_singleton 0⟩
  · obtain rfl := Finset.mem_singleton.mp inside
    exact ⟨show (0 : Nat) ∈ ({0, 1, 2} : Finset Nat) by decide, row0⟩
  · change o ∈ ({0, 1, 2} : Finset Nat) at present
    rcases Finset.mem_insert.mp present with rfl | rest
    · exact Finset.mem_singleton_self 0
    rcases Finset.mem_insert.mp rest with rfl | rest
    · exfalso
      have pairs : Equal Tower.rules Θ.raw (.pair sCode (τ.substitution 0)) (.pair tCode (τ.substitution 0))
          (.sigma setType (Presentation.rename wk (τ.substitution 2))) := region.2
      exact Quotient.sets_apart (Θ := Θ) (Quotient.fst_of_pair_equal formed (.sort _) (s_typed _) t0 (t_typed _) t0 pairs)
    · exfalso
      obtain rfl := Finset.mem_singleton.mp rest
      have types : TypeEq Tower.rules Θ.raw (.sigma setType (Presentation.rename wk (τ.substitution 2)))
          (setEq sCode tCode) := region.1
      exact TypeEq.pi_ne_sigma (TowerModel.facts (L := Nat)) Θ.formed types.symm

/-- **After the unwitnessed tell, the count is admitted.** -/
theorem countAfterTell_admitted : (step setting.levels Nat).Admits countAfterTell := by
  refine (admits_iff countAfterTell).mpr ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl,
      fun _ member => absurd member List.not_mem_nil⟩,
    ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩,
    ?_, fun _ _ _ _ member => absurd member List.not_mem_nil, ?_⟩
  · rw [countAfterTell_information, told_knowledge]
    refine ⟨pairFrame, Quotient.nameSolution, ?_⟩
    intro e member
    obtain rfl := List.mem_singleton.mp member
    show (frames setting.levels).E (Quotient.q1Row.reindex Quotient.nameSolution)
      (Quotient.q2Row.reindex Quotient.nameSolution)
    rw [Quotient.names_identified]
    exact ((frames setting.levels).equivalence _).refl _
  intro q member Θ τ solved
  obtain rfl := List.mem_singleton.mp member
  rw [countAfterTell_information] at solved
  exact countAfterTell_holds τ solved

/-- **The evidence-free tell is observed**: the count that `Quotient.countBefore` asks is refused
before the tell and admitted after it, although no evidence was read. -/
theorem unwitnessed_tell_observed :
    ¬ (step setting.levels Nat).Admits Quotient.countBefore ∧ (step setting.levels Nat).Admits countAfterTell :=
  ⟨Quotient.countBefore_refused, countAfterTell_admitted⟩

/-! ## A proof-irrelevant knowledge is observed by counting -/

/-- The frame `X : U0, x : X, g : Ground, g' : Ground`. -/
abbrev quad : Context Tower.rules := extend triple (groundType _)

theorem quadSigma_formed : Typed Tower.rules quad.raw (.sigma (.var 3) ground) U0 :=
  .cumul (.sigmaForm (Derivable.var 3) (.sort _) (ground_typed _) (.sort _) (.sorts _ _)) collapse

theorem member1_typed : Typed Tower.rules quad.raw (.pair (.var 2) (.var 1)) (.app sCode (.var 3)) :=
  .conv (.pairIntro quadSigma_formed (.sort _) (Derivable.var 2) (Derivable.var 1))
    (.symm (s_beta (Derivable.var 3))) (.sort _)

theorem member2_typed : Typed Tower.rules quad.raw (.pair (.var 2) (.var 0)) (.app sCode (.var 3)) :=
  .conv (.pairIntro quadSigma_formed (.sort _) (Derivable.var 2) (Derivable.var 0))
    (.symm (s_beta (Derivable.var 3))) (.sort _)

/-- `S X`, over the frame. -/
def memberType : TypeOver quad := Run.smallType quad (.app sCode (.var 3)) (Run.app_small (s_typed _) (Derivable.var 3))

/-- The member `(x, g) : S X`. -/
def member1 : TotalTerm quad := ⟨memberType, ⟨.pair (.var 2) (.var 1), member1_typed⟩⟩

/-- The member `(x, g') : S X`. -/
def member2 : TotalTerm quad := ⟨memberType, ⟨.pair (.var 2) (.var 0), member2_typed⟩⟩

/-- **The two members are apart in the knowledge**: equal pairs would have equal second components,
and `g`, `g'` are different variables. -/
theorem members_apart : ¬ (frames setting.levels).E member1 member2 := by
  intro same
  have terms : Equal Tower.rules quad.raw (.pair (.var 2) (.var 1)) (.pair (.var 2) (.var 0)) (.app sCode (.var 3)) :=
    same.2
  have sigmaTerms : Equal Tower.rules quad.raw (.pair (.var 2) (.var 1)) (.pair (.var 2) (.var 0))
      (.sigma (.var 3) ground) :=
    .convEq terms (s_beta (Derivable.var 3)) (.sort _)
  have seconds := Quotient.snd_of_pair_equal (Q := ground) quadSigma_formed (.sort _) (Derivable.var 2)
    (Derivable.var 1) (Derivable.var 2) (Derivable.var 0) sigmaTerms
  exact Quotient.vars_apart quad.formed (by decide) seconds

/-- The two member rows. -/
def memberRows (o : Nat) : TotalTerm quad := if o = 0 then member1 else member2

/-- **Proof irrelevance is observed**: today exactly one present row is `(x, g)`; under any extension
of the knowledge's equality that relates the two members, as definitional proof irrelevance would
relate any two proofs of one proposition, that count is no longer `1`. -/
theorem proofIrrelevance_observed (E' : TotalTerm quad → TotalTerm quad → Prop)
    (extension : ∀ a b, (frames setting.levels).E a b → E' a b) (irrelevant : E' member1 member2) :
    CountUnder (frames setting.levels).E member1 ({0, 1} : Finset Nat) memberRows 1 ∧
      ¬ CountUnder E' member1 ({0, 1} : Finset Nat) memberRows 1 := by
  have today : CountUnder (frames setting.levels).E member1 ({0, 1} : Finset Nat) memberRows 1 := by
    refine ⟨{0}, fun o => ⟨fun inside => ?_, fun ⟨present, related⟩ => ?_⟩, Finset.card_singleton 0⟩
    · obtain rfl := Finset.mem_singleton.mp inside
      exact ⟨by decide, ((frames setting.levels).equivalence _).refl _⟩
    · rcases Finset.mem_insert.mp present with rfl | rest
      · exact Finset.mem_singleton_self 0
      · obtain rfl := Finset.mem_singleton.mp rest
        exact absurd related members_apart
  exact ⟨today, count_changes extension (o := 1) (by decide) irrelevant members_apart today⟩

end EqualityOnTheStep.Options.Observability

#print axioms EqualityOnTheStep.Options.Observability.count_changes
#print axioms EqualityOnTheStep.Options.Observability.count_conservative_iff
#print axioms EqualityOnTheStep.Options.Observability.absence_conservative_iff
#print axioms EqualityOnTheStep.Options.Observability.extension_observed
#print axioms EqualityOnTheStep.Options.Observability.extension_observed_absence
#print axioms EqualityOnTheStep.Options.Observability.conservative_iff
#print axioms EqualityOnTheStep.Options.Observability.countFiring_admits_iff
#print axioms EqualityOnTheStep.Options.Observability.knowledge_observed
#print axioms EqualityOnTheStep.Options.Observability.transportBy_equivalent
#print axioms EqualityOnTheStep.Options.Observability.transport_answers
#print axioms EqualityOnTheStep.Options.Observability.unwitnessed_tell_observed
#print axioms EqualityOnTheStep.Options.Observability.members_apart
#print axioms EqualityOnTheStep.Options.Observability.proofIrrelevance_observed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
