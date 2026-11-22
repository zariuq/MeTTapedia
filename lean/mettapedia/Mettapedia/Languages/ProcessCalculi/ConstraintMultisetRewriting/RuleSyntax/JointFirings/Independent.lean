import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.OneAfterAnother
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Examples

/-!
# Independent members: the bag is admitted exactly when each member is, and runs in any order

## The order of the members does not matter

Over every frame action:

* `realized_perm`: joint realization does not depend on the order of the members;
* `Bag.admitsOwn_perm`: a bag admitted with the guards of each member at its own information stays
  admitted when its members are reordered;
* `Bag.result_perm`: the reordered bag has the same rows, the same labels, and the same knowledge up
  to the order of its equations.

## Members whose unknowns are their own

At the one frame, at a state that mentions only fixed terms (ground rows and ground knowledge), the
members of a jointly fresh bag share no unknown: each one's footprint is fixed terms and its own opened
unknowns (`Scope.independent_of_fixed`, and joint freshness for the openings). There:

* **`admitsOwn_iff_members`**: a bag is admitted (guards at each member's own information) exactly when
  it is jointly fresh, its takes and made identities are apart, its joint selection is enabled as one
  commit, and **each member is admitted by the step of the program**. This holds for every rule,
  including rules with absence, counts and collect query.
* **`any_order`**: for positive rules, an admitted bag is, in every order of its members, a run of the
  step of the program ending at the bag's result (same rows and labels; knowledge up to order).

So where the members are independent, the bag adds to the step of the program only that nothing comes
between its members (`SynchronousUpdate` exhibits what that adds).

## The control: a shared unknown (`SharedUnknown`)

A row labelled by an unknown `x` that nothing binds; one rule reads a row and tells it is `5`, another
reads a row and tells it is `6`. Each match is admitted alone (`five_admitted`, `six_admitted`); the bag of
the two is jointly fresh (`pair_fresh`) and is refused (`pair_refused`): its joint information binds `x`
to `5` and to `6`. The one hypothesis that fails is that the state mentions only fixed terms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open LogicOverTheStep.StepSpan (Succ)
open OneFrame (Terms frames ext)
open Scope (Positive)

universe uO uT uH uE uOcc

/-! ## Reordering the members -/

section Reorder

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Frames Tm Hom) {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}

/-- **Joint realization does not depend on the order of the members.** -/
theorem realized_perm {a : Obj} {x : E.Ext a} {b : Obj} {l l' : List (Member O E P x)}
    (perm : l.Perm l') : ∀ {Q : Hom (E.target x) b → Prop}, Realized X b l Q ↔ Realized X b l' Q := by
  induction perm with
  | nil => exact Iff.rfl
  | cons m _ ih =>
      intro Q
      rw [realized_cons, realized_cons]
      exact forall_congr' fun _ => ih
  | swap m₁ m₂ rest =>
      intro Q
      rw [realized_cons, realized_cons]
      constructor
      · intro realized h₁
        rw [realized_cons]
        intro h₂
        exact Realized.mono X rest (fun u both => ⟨⟨both.1.1, both.2⟩, both.1.2⟩)
          ((realized_cons X m₁ rest _).mp (realized h₂) h₁)
      · intro realized h₂
        rw [realized_cons]
        intro h₁
        exact Realized.mono X rest (fun u both => ⟨⟨both.1.1, both.2⟩, both.1.2⟩)
          ((realized_cons X m₂ rest _).mp (realized h₁) h₂)
  | trans _ _ first second => exact first.trans second

/-- A list of equations solved by a substitution stays solved when reordered. -/
theorem models_perm {a b : Obj} {σ : Hom a b} {K K' : EquationStore (Tm a)} (perm : K.Perm K')
    (solved : X.Models σ K) : X.Models σ K' := fun e member => solved e (perm.mem_iff.mpr member)

variable [DecidableEq O]

/-- Lists that are permutations of one another have the same members as finite sets. -/
theorem mem_toFinset_perm {l l' : List O} (perm : l.Perm l') {o : O} (inside : o ∈ l'.toFinset) :
    o ∈ l.toFinset := List.mem_toFinset.mpr (perm.mem_iff.mpr (List.mem_toFinset.mp inside))

/-- **Reordering the members keeps admission** (guards at each member's own information). -/
theorem Bag.admitsOwn_perm {s : State Tm O} {x : E.Ext s.frame} {l l' : List (Member O E P x)}
    (perm : l.Perm l') (own : Bag.AdmitsOwn X s ⟨x, l⟩) : Bag.AdmitsOwn X s ⟨x, l'⟩ := by
  obtain ⟨⟨fresh, taken, made, lengths⟩, enabled, ⟨c, σ, solved⟩, asks⟩ := own
  have permT := perm.flatMap_right fun m => m.selection.taken
  have permR := perm.flatMap_right fun m => m.selection.read
  have permM := perm.flatMap_right fun m => m.selection.made
  have permO := perm.flatMap_right fun m => m.own X s
  refine ⟨⟨fun b g => (realized_perm X perm).mp (fresh b g), permT.nodup_iff.mp taken,
    permM.nodup_iff.mp made, fun m inside => lengths m (perm.mem_iff.mpr inside)⟩,
    ⟨fun o member => enabled.taken_subset (mem_toFinset_perm permT member),
      fun o member => enabled.kept_subset (mem_toFinset_perm permR member),
      Finset.disjoint_left.mpr fun _ isTaken isKept => Finset.disjoint_left.mp enabled.apart
        (mem_toFinset_perm permT isTaken) (mem_toFinset_perm permR isKept),
      Finset.disjoint_left.mpr fun _ isMade isPresent => Finset.disjoint_left.mp enabled.fresh
        (mem_toFinset_perm permM isMade) isPresent,
      fun q member => by simp [Selection.commit] at member⟩,
    ⟨c, σ, models_perm X (List.Perm.append_left _ permO) solved⟩,
    fun m inside => asks m (perm.mem_iff.mpr inside)⟩

/-- `zip` of two `flatMap`s whose pieces have equal lengths is the `flatMap` of the `zip`s. -/
theorem zip_flatMap {α β γ : Type*} (g : α → List β) (h : α → List γ) :
    ∀ (l : List α), (∀ m ∈ l, (g m).length = (h m).length) →
      (l.flatMap g).zip (l.flatMap h) = l.flatMap fun m => (g m).zip (h m)
  | [], _ => rfl
  | m :: rest, lengths => by
      simp only [List.flatMap_cons]
      rw [List.zip_append (lengths m List.mem_cons_self),
        zip_flatMap g h rest fun m' inside => lengths m' (List.mem_cons_of_mem _ inside)]

/-- **Relabelling depends only on the pairs of identities and rows**, when the identities are apart. -/
theorem relabel_eq_of_zip_perm {a : Obj} (old : O → Tm a) {made made' : List O}
    {rows rows' : List (Tm a)} (nodup : made.Nodup) (nodup' : made'.Nodup)
    (lengths : made.length = rows.length) (lengths' : made'.length = rows'.length)
    (perm : (made.zip rows).Perm (made'.zip rows')) (o : O) :
    relabel old made rows o = relabel old made' rows' o := by
  by_cases inside : o ∈ made
  · obtain ⟨t, paired⟩ := Scope.exists_mem_zip_left made rows lengths o inside
    rw [Firing.relabel_zip old made rows nodup lengths (o, t) paired,
      Firing.relabel_zip old made' rows' nodup' lengths' (o, t) (perm.mem_iff.mp paired)]
  · have outside : o ∉ made' := fun inside' => by
      obtain ⟨t, paired⟩ := Scope.exists_mem_zip_left made' rows' lengths' o inside'
      exact inside (List.of_mem_zip (perm.mem_iff.mpr paired)).1
    rw [Firing.relabel_of_not_mem old made rows inside, Firing.relabel_of_not_mem old made' rows' outside]

/-- The opened made rows of a member, at the extended frame of its bag. -/
def Member.produced {a : Obj} {x : E.Ext a} (m : Member O E P x) : List (Tm (E.target x)) :=
  (m.firing.opened X).produce

/-- **The reordered bag has the same rows, the same labels, and its knowledge reordered.** -/
theorem Bag.result_perm {s : State Tm O} {x : E.Ext s.frame} {l l' : List (Member O E P x)}
    (perm : l.Perm l') (fits : Bag.Fits X s ⟨x, l⟩) :
    (Bag.result X s ⟨x, l'⟩).present = (Bag.result X s ⟨x, l⟩).present ∧
      (Bag.result X s ⟨x, l'⟩).label = (Bag.result X s ⟨x, l⟩).label ∧
      (Bag.result X s ⟨x, l'⟩).knowledge.Perm (Bag.result X s ⟨x, l⟩).knowledge := by
  obtain ⟨-, -, made, lengths⟩ := fits
  have permT := perm.flatMap_right fun m => m.selection.taken
  have permM := perm.flatMap_right fun m => m.selection.made
  have pieces : ∀ m ∈ l, m.selection.made.length = (Member.produced X m).length := by
    intro m inside
    show m.selection.made.length = (m.rule.body.produce.map (X.act m.opening)).length
    rw [List.length_map]
    exact (lengths m inside).2.2.1.symm
  have pieces' : ∀ m ∈ l', m.selection.made.length = (Member.produced X m).length :=
    fun m inside => pieces m (perm.mem_iff.mpr inside)
  have zipped := zip_flatMap (fun m : Member O E P x => m.selection.made) (Member.produced X) l pieces
  have zipped' :=
    zip_flatMap (fun m : Member O E P x => m.selection.made) (Member.produced X) l' pieces'
  have totals : ∀ (k : List (Member O E P x)),
      (∀ m ∈ k, m.selection.made.length = (Member.produced X m).length) →
      (k.flatMap fun m => m.selection.made).length = (k.flatMap (Member.produced X)).length := by
    intro k each
    rw [List.length_flatMap, List.length_flatMap]
    exact congrArg List.sum (List.map_congr_left each)
  have produce' : Bag.produce X (⟨x, l'⟩ : Bag O E P s.frame) = l'.flatMap (Member.produced X) := rfl
  have produce : Bag.produce X (⟨x, l⟩ : Bag O E P s.frame) = l.flatMap (Member.produced X) := rfl
  have zipPerm : ((l'.flatMap fun m => m.selection.made).zip
      (Bag.produce X (⟨x, l'⟩ : Bag O E P s.frame))).Perm
      ((l.flatMap fun m => m.selection.made).zip (Bag.produce X (⟨x, l⟩ : Bag O E P s.frame))) := by
    rw [produce', produce, zipped, zipped']
    exact (perm.flatMap_right _).symm
  refine ⟨?_, ?_, ?_⟩
  · show fire s.present (Bag.selection ⟨x, l'⟩).commit = fire s.present (Bag.selection ⟨x, l⟩).commit
    ext o
    simp only [mem_fire, Selection.commit, Bag.selection, List.mem_toFinset]
    rw [permT.mem_iff, permM.mem_iff]
  · funext o
    exact relabel_eq_of_zip_perm _ (permM.nodup_iff.mp made) made
      ((totals l' pieces').trans (congrArg List.length produce'.symm))
      ((totals l pieces).trans (congrArg List.length produce.symm)) zipPerm o
  · exact List.Perm.append_left _ (perm.flatMap_right fun m => m.own X s).symm

end Reorder

/-! ## Members whose unknowns are their own -/

section Fixed

universe uT' uS' uO'

variable {T : Type uT'} {S : Type uS'} (A : SubstitutionAction T S) {O : Type uO'} [DecidableEq O]
  {P : Program (Terms T)}

/-- **At a state that mentions only fixed terms, a bag with a member is admitted exactly when it is
jointly fresh, its selections are apart, and each member is admitted by the step of the program.** -/
theorem admitsOwn_iff_members {s : State (Terms T) O} {l : List (OneMember A O P)}
    (fixed : ∀ t, s.Mentions t → ∀ σ : S, A.E (A.apply σ t) t) (nonempty : l ≠ []) :
    Bag.AdmitsOwn (frames A) s (bagOf A l) ↔
      (bagOf A l).Fresh (frames A) s ∧ (bagOf A l).selection.taken.Nodup ∧
        (bagOf A l).selection.made.Nodup ∧
        Enabled (fun _ : O => ()) s.present ((bagOf A l).selection.commit (T := Unit)) ∧
        ∀ m ∈ l, m.firing.Admits (frames A) s := by
  classical
  constructor
  · intro own
    exact ⟨own.1.1, own.1.2.1, own.1.2.2.1, own.2.1, fun m inside =>
      Bag.admits_member (frames A) (fun _ _ => ⟨A.identity⟩) own inside⟩
  · rintro ⟨fresh, taken, made, enabled, members⟩
    refine ⟨⟨fresh, taken, made, fun m inside => (members m inside).1.2.2.2⟩, enabled, ?_,
      fun m inside => (members m inside).2.2.2⟩
    -- one solution for every member, realized together
    have solutionOf : ∀ m ∈ l, ∃ σ : S, A.Models σ (m.firing.information (frames A) s) :=
      fun m inside => by
        obtain ⟨_, σ, solved⟩ := (members m inside).2.2.1
        exact ⟨σ, solved⟩
    let pick : OneMember A O P → S := fun m =>
      if inside : m ∈ l then Classical.choose (solutionOf m inside) else A.identity
    obtain ⟨u, -, rules⟩ := Realized.pick (frames A) (fun m => A.compose (pick m) m.opening) l
      (fresh PUnit.unit A.identity)
    have each : ∀ m ∈ l, A.Models u (m.firing.information (frames A) s) := by
      intro m inside
      have solved : A.Models (pick m) (m.firing.information (frames A) s) := by
        simp only [pick, dif_pos inside]
        exact Classical.choose_spec (solutionOf m inside)
      refine Scope.models_information_of_agree A (members m inside).2.1 (fun t foot => ?_) solved
      rcases foot with mentioned | opened
      · exact A.equivalence.trans (fixed t mentioned u) (A.equivalence.symm (fixed t mentioned (pick m)))
      · obtain ⟨t₀, member, rfl⟩ := List.mem_map.mp opened
        have key : A.E (A.apply u (A.apply m.opening t₀))
            (A.apply (A.compose (pick m) m.opening) t₀) := rules m inside t₀ member
        rw [A.apply_compose] at key
        exact key
    obtain ⟨m₀, inM₀⟩ := List.exists_mem_of_ne_nil l nonempty
    refine ⟨PUnit.unit, u, (A.models_append u _ _).mpr ⟨?_, fun e inOwn => ?_⟩⟩
    · intro e known
      have whole := each m₀ inM₀
      rw [Member.information_eq (frames A) s m₀] at whole
      exact ((A.models_append u _ _).mp whole).1 e known
    · obtain ⟨r, inR, inside⟩ := List.mem_flatMap.mp inOwn
      have whole := each r inR
      rw [Member.information_eq (frames A) s r] at whole
      exact ((A.models_append u _ _).mp whole).2 e inside

/-- **In every order of its members, an admitted bag of positive rules is a run of the step of the
program**, ending at a state with the bag's rows and labels, and its knowledge reordered. -/
theorem any_order {s : State (Terms T) O} {l l' : List (OneMember A O P)}
    (positive : ∀ r ∈ l, Positive r.rule) (own : Bag.AdmitsOwn (frames A) s (bagOf A l))
    (perm : l.Perm l') :
    Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) s
        (Bag.result (frames A) s (bagOf A l')) ∧
      (Bag.result (frames A) s (bagOf A l')).present = (Bag.result (frames A) s (bagOf A l)).present ∧
      (Bag.result (frames A) s (bagOf A l')).label = (Bag.result (frames A) s (bagOf A l)).label ∧
      (Bag.result (frames A) s (bagOf A l')).knowledge.Perm
        (Bag.result (frames A) s (bagOf A l)).knowledge :=
  ⟨run_of_admitsOwn A l' s (fun r inside => positive r (perm.mem_iff.mpr inside))
      (Bag.admitsOwn_perm (frames A) perm own),
    Bag.result_perm (frames A) perm own.1⟩

end Fixed

/-! ## The control: a shared unknown -/

namespace SharedUnknown

open Mettapedia.Logic.LP
open Examples (Tm X E c x openRequest)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-- Read any row `x`, tell `x = 6`. -/
def answerSix : Rule Tm := ⟨PUnit.unit, ⟨[], [x], [(x, c 6)], [], []⟩, []⟩

/-- **The program**: tell that a row is `5`; tell that a row is `6`. -/
def program : Program Tm := {Examples.answer, answerSix}

/-- The opening that renames each unknown `n` to `n + k`. -/
def shiftBy (k : ℕ) : Subst atoms := fun n => Term.var (n + k)

/-- Read the row and tell it is `5`, the rule's `x` opened as `x₁`. -/
def five : OneMember action ℕ program := ⟨Examples.answer, Or.inl rfl, shiftBy 1, ⟨[], [0], []⟩, []⟩

/-- Read the row and tell it is `6`, the rule's `x` opened as `x₂`. -/
def six : OneMember action ℕ program := ⟨answerSix, Or.inr rfl, shiftBy 2, ⟨[], [0], []⟩, []⟩

/-- **The bag of the two.** -/
def pair : Bag ℕ E program PUnit.unit := bagOf action [five, six]

theorem five_information : five.firing.information X openRequest = [(.var 1, x), (.var 1, c 5)] := rfl

theorem six_information : six.firing.information X openRequest = [(.var 2, x), (.var 2, c 6)] := rfl

theorem pair_information : Bag.information X openRequest pair =
    [(.var 1, x), (.var 1, c 5), (.var 2, x), (.var 2, c 6)] := rfl

theorem five_admitted : five.firing.Admits X openRequest := by
  refine ⟨⟨fun b g h => ⟨fun v => if v = 1 then h 0 else g v, ?_, ?_⟩, List.nodup_nil, List.nodup_nil,
    rfl, rfl, rfl, rfl⟩, ⟨by decide, by decide, by decide, by decide,
      fun q member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, Examples.everywhere 5, fun e member => ?_⟩,
    fun _ _ _ => ⟨fun check member => absurd member List.not_mem_nil,
      fun q member => absurd member List.not_mem_nil⟩⟩
  · rintro t (member | member | ⟨o, -, rfl⟩)
    · exact absurd member List.not_mem_nil
    · exact absurd member List.not_mem_nil
    · rfl
  · intro t member
    have listed : t ∈ [x, x, c 5] := member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
    rcases listed with rfl | rfl | rfl <;> rfl
  · rw [five_information] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl

theorem six_admitted : six.firing.Admits X openRequest := by
  refine ⟨⟨fun b g h => ⟨fun v => if v = 2 then h 0 else g v, ?_, ?_⟩, List.nodup_nil, List.nodup_nil,
    rfl, rfl, rfl, rfl⟩, ⟨by decide, by decide, by decide, by decide,
      fun q member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, Examples.everywhere 6, fun e member => ?_⟩,
    fun _ _ _ => ⟨fun check member => absurd member List.not_mem_nil,
      fun q member => absurd member List.not_mem_nil⟩⟩
  · rintro t (member | member | ⟨o, -, rfl⟩)
    · exact absurd member List.not_mem_nil
    · exact absurd member List.not_mem_nil
    · rfl
  · intro t member
    have listed : t ∈ [x, x, c 6] := member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
    rcases listed with rfl | rfl | rfl <;> rfl
  · rw [six_information] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl

/-- **The bag is jointly fresh**: the two openings are apart. -/
theorem pair_fresh : Bag.Fresh X openRequest pair := by
  intro b g
  refine (realized_cons X five [six] _).mpr fun h₁ => (realized_cons X six [] _).mpr fun h₂ =>
    (realized_nil X _).mpr ⟨fun v => if v = 1 then h₁ 0 else if v = 2 then h₂ 0 else g v,
      ⟨⟨?_, ?_⟩, ?_⟩⟩
  · rintro t (member | member | ⟨o, -, rfl⟩)
    · exact absurd member List.not_mem_nil
    · exact absurd member List.not_mem_nil
    · rfl
  · intro t member
    have listed : t ∈ [x, x, c 5] := member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
    rcases listed with rfl | rfl | rfl <;> rfl
  · intro t member
    have listed : t ∈ [x, x, c 6] := member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
    rcases listed with rfl | rfl | rfl <;> rfl

/-- **The bag is refused**: its joint information sends the row's unknown to `5` and to `6`. -/
theorem pair_refused : ¬ Bag.Admits X openRequest pair := by
  rintro ⟨-, -, ⟨_, σ, solved⟩, -⟩
  rw [pair_information] at solved
  have read₁ : σ 1 = σ 0 := solved (.var 1, x) List.mem_cons_self
  have told₁ : σ 1 = c 5 := solved (.var 1, c 5) (List.mem_cons_of_mem _ List.mem_cons_self)
  have read₂ : σ 2 = σ 0 :=
    solved (.var 2, x) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have told₂ : σ 2 = c 6 := solved (.var 2, c 6) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self)))
  have clash : (Term.const (5 : ℕ) : Term atoms) = Term.const (6 : ℕ) :=
    told₁.symm.trans (read₁.trans (read₂.symm.trans told₂))
  exact absurd (Term.const.inj clash) (by decide)

/-- **Each member is admitted, the bag is jointly fresh with its selections apart, and it is refused.** -/
theorem members_admitted_bag_refused :
    (∀ m ∈ pair.members, m.firing.Admits X openRequest) ∧ Bag.Fresh X openRequest pair ∧
      ¬ Bag.Admits X openRequest pair := by
  refine ⟨fun m inside => ?_, pair_fresh, pair_refused⟩
  have listed : m ∈ [five, six] := inside
  rcases List.mem_cons.mp listed with rfl | rest
  · exact five_admitted
  · rw [List.mem_singleton.mp rest]
    exact six_admitted

end SharedUnknown

#print axioms realized_perm
#print axioms Bag.admitsOwn_perm
#print axioms zip_flatMap
#print axioms relabel_eq_of_zip_perm
#print axioms Bag.result_perm
#print axioms admitsOwn_iff_members
#print axioms any_order
#print axioms SharedUnknown.five_admitted
#print axioms SharedUnknown.six_admitted
#print axioms SharedUnknown.pair_fresh
#print axioms SharedUnknown.pair_refused
#print axioms SharedUnknown.members_admitted_bag_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings
