import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Independent
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.EveryControls

/-!
# A bag of ground matches is one match of the tensor of their rules

At the one frame, **the tensor of a list of rules** (`tensorOf`) puts their bodies side by side: the take
patterns of all, then their read patterns, tells, checks, made rows and collect patterns. **The tensor
closure of a program** (`tensors`) holds the tensor of every list of its rules.

For a bag of matches of rules with fixed terms, **the tensor firing** (`tensorFiring`) fires the tensor of
the members' rules with the bag's joint selection and the members' seen sets.

* **`admits_iff_tensor`**: the bag is jointly admitted with the guards at the joint information
  (`Bag.Admits`) exactly when its tensor firing is admitted by the step of the tensor closure, when each
  member selects as many rows as its patterns (one direction gives this; the other assumes it).
* **`result_tensor`**: the tensor firing has the bag's rows and labels, and its knowledge has the bag's
  equations.

So, on ground rules, the reading of joint admission that asks the guards at the joint information is the
one-match step of the program closed under tensors: one match of `r₁ ⊗ … ⊗ rₖ` for a bag of matches of
`r₁ … rₖ`. The one-match firing is the restriction to the rules of the program; the bag step adds the
tensors, and every finite tensor (a finite program cannot list them: `Representation.allAtOnce_not_finite`
for "every copy at once"). `every`, `unique` and maximal bags add to this an absence of a further match,
which no tensor says (`Collect`, `Unique.Neighbour`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open OneFrame (Terms frames ext)

section Tensor

universe uT uS uO

variable {T : Type uT} {S : Type uS} (A : SubstitutionAction T S) {O : Type uO} [DecidableEq O]

/-! ## The tensor of rules -/

/-- The take patterns of a rule at the one frame. -/
def takeOf (r : Rule (Terms T)) : List T := r.body.take
/-- The read patterns. -/
def readOf (r : Rule (Terms T)) : List T := r.body.read
/-- The tells. -/
def tellOf (r : Rule (Terms T)) : EquationStore T := r.body.tell
/-- The checks. -/
def checksOf (r : Rule (Terms T)) : List (Check T) := r.body.checks
/-- The made rows. -/
def produceOf (r : Rule (Terms T)) : List T := r.body.produce
/-- The collect patterns. -/
def collectOf (r : Rule (Terms T)) : List T := r.collect

/-- **The tensor of a list of rules**: their bodies side by side. -/
def tensorOf (rs : List (Rule (Terms T))) : Rule (Terms T) :=
  ⟨PUnit.unit, ⟨rs.flatMap takeOf, rs.flatMap readOf, rs.flatMap tellOf, rs.flatMap checksOf,
    rs.flatMap produceOf⟩, rs.flatMap collectOf⟩

/-- **The tensor closure of a program**: the tensor of every list of its rules. -/
def tensors (P : Program (Terms T)) : Program (Terms T) :=
  {r | ∃ rs : List (Rule (Terms T)), (∀ r' ∈ rs, r' ∈ P) ∧ r = tensorOf rs}

/-- A rule of the program is the tensor of itself alone. -/
theorem tensorOf_single (r : Rule (Terms T)) : tensorOf [r] = r := by
  obtain ⟨⟨⟩, ⟨take, read, tell, checks, produce⟩, collect⟩ := r
  simp [tensorOf, takeOf, readOf, tellOf, checksOf, produceOf, collectOf]

variable {P : Program (Terms T)}

/-- **The tensor firing of a bag**: the tensor of the members' rules, the joint selection, the members'
seen sets. -/
def tensorFiring (l : List (OneMember A O P)) : Firing O (ext A) (tensors P) PUnit.unit :=
  ⟨tensorOf (l.map Member.rule), ⟨l.map Member.rule, fun r inside => by
      obtain ⟨m, -, rfl⟩ := List.mem_map.mp inside
      exact m.member, rfl⟩,
    PUnit.unit, A.identity, (bagOf A l).selection, l.flatMap Member.seen⟩

/-! ## Fixed terms are not moved by openings -/

theorem map_fixed {σ : S} : ∀ (ts : List T), (∀ t ∈ ts, A.apply σ t = t) → ts.map (A.apply σ) = ts
  | [], _ => rfl
  | t :: rest, fixed => by
      rw [List.map_cons, fixed t List.mem_cons_self,
        map_fixed rest fun t' inside => fixed t' (List.mem_cons_of_mem _ inside)]

theorem check_map_fixed {σ : S} (c : Check T) (fixed : ∀ t ∈ checkTerms c, A.apply σ t = t) :
    Check.map (A.apply σ) c = c := by
  cases c with
  | equal left right =>
      simp only [Check.map, fixed left (by simp [checkTerms]), fixed right (by simp [checkTerms])]
  | predicate quantifier pattern => simp only [Check.map, fixed pattern (by simp [checkTerms])]
  | count pattern number => simp only [Check.map, fixed pattern (by simp [checkTerms])]

/-- Rules whose terms every substitution fixes. -/
def GroundRule (r : Rule (Terms T)) : Prop := ∀ t ∈ r.terms, ∀ σ : S, A.apply σ t = t

variable {A}

omit [DecidableEq O] in
/-- **The opened body of a ground rule is its body**, field by field. -/
theorem opened_ground {g : Firing O (ext A) P PUnit.unit} (ground : GroundRule A g.rule) :
    (g.opened (frames A)).take = g.rule.body.take ∧ (g.opened (frames A)).read = g.rule.body.read ∧
      (g.opened (frames A)).tell = g.rule.body.tell ∧
      (g.opened (frames A)).checks = g.rule.body.checks ∧
      (g.opened (frames A)).produce = g.rule.body.produce ∧ g.collectOpened (frames A) = g.rule.collect := by
  have inTerms : ∀ t, t ∈ g.rule.body.take ∨ t ∈ g.rule.body.read ∨ t ∈ g.rule.body.tell.map Prod.fst ∨
      t ∈ g.rule.body.tell.map Prod.snd ∨ t ∈ g.rule.body.checks.flatMap checkTerms ∨
      t ∈ g.rule.body.produce ∨ t ∈ g.rule.collect → t ∈ g.rule.terms := by
    intro t inside
    simp only [Rule.terms, List.mem_append]
    tauto
  refine ⟨map_fixed A _ fun t inside => ground t (inTerms t (Or.inl inside)) _,
    map_fixed A _ fun t inside => ground t (inTerms t (Or.inr (Or.inl inside))) _, ?_, ?_,
    map_fixed A _ fun t inside => ground t (inTerms t (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl inside))))))) _,
    map_fixed A _ fun t inside => ground t (inTerms t (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr inside))))))) _⟩
  · show g.rule.body.tell.map (fun pair => (A.apply g.opening pair.1, A.apply g.opening pair.2)) =
      g.rule.body.tell
    conv_rhs => rw [← List.map_id g.rule.body.tell]
    refine List.map_congr_left fun e inside => ?_
    rw [ground e.1 (inTerms _ (Or.inr (Or.inr (Or.inl (List.mem_map_of_mem inside))))),
      ground e.2 (inTerms _ (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_map_of_mem inside))))))]
    rfl
  · show g.rule.body.checks.map (Check.map (A.apply g.opening)) = g.rule.body.checks
    conv_rhs => rw [← List.map_id g.rule.body.checks]
    refine List.map_congr_left fun c inside => ?_
    exact check_map_fixed A c fun t inTermsOf =>
      ground t (inTerms t (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (List.mem_flatMap.mpr ⟨c, inside, inTermsOf⟩))))))) _

/-! ## Lists side by side -/

theorem zipWith_flatMap {α β γ δ : Type*} (f : β → γ → δ) (g : α → List β) (h : α → List γ) :
    ∀ (l : List α), (∀ m ∈ l, (g m).length = (h m).length) →
      List.zipWith f (l.flatMap g) (l.flatMap h) = l.flatMap fun m => List.zipWith f (g m) (h m)
  | [], _ => rfl
  | m :: rest, lengths => by
      simp only [List.flatMap_cons]
      rw [List.zipWith_append (lengths m List.mem_cons_self),
        zipWith_flatMap f g h rest fun m' inside => lengths m' (List.mem_cons_of_mem _ inside)]

theorem length_flatMap_eq {α β γ : Type*} (g : α → List β) (h : α → List γ) (l : List α)
    (lengths : ∀ m ∈ l, (g m).length = (h m).length) :
    (l.flatMap g).length = (l.flatMap h).length := by
  rw [List.length_flatMap, List.length_flatMap]
  exact congrArg List.sum (List.map_congr_left lengths)

/-! ## The bag and its tensor firing -/

/-- **Per-member lengths**: each member selects as many rows as its patterns, and claims as many seen
sets as its collect patterns. -/
def Split (l : List (OneMember A O P)) : Prop :=
  ∀ m ∈ l, m.rule.body.take.length = m.selection.taken.length ∧
    m.rule.body.read.length = m.selection.read.length ∧
    m.rule.body.produce.length = m.selection.made.length ∧ m.rule.collect.length = m.seen.length

variable {l : List (OneMember A O P)}

omit [DecidableEq O] in
theorem tensor_rule_body :
    (tensorFiring A l).rule.body.take = l.flatMap (fun m => takeOf m.rule) ∧
      (tensorFiring A l).rule.body.read = l.flatMap (fun m => readOf m.rule) ∧
      (tensorFiring A l).rule.body.tell = l.flatMap (fun m => tellOf m.rule) ∧
      (tensorFiring A l).rule.body.checks = l.flatMap (fun m => checksOf m.rule) ∧
      (tensorFiring A l).rule.body.produce = l.flatMap (fun m => produceOf m.rule) ∧
      (tensorFiring A l).rule.collect = l.flatMap (fun m => collectOf m.rule) :=
  ⟨List.flatMap_map .., List.flatMap_map .., List.flatMap_map .., List.flatMap_map ..,
    List.flatMap_map .., List.flatMap_map ..⟩

omit [DecidableEq O] in
theorem tensor_ground (ground : ∀ m ∈ l, GroundRule A m.rule) : GroundRule A (tensorFiring A l).rule := by
  intro t inside σ
  have inMember : ∃ m ∈ l, t ∈ m.rule.terms := by
    obtain ⟨take, read, tell, checks, produce, collect⟩ := tensor_rule_body (A := A) (l := l)
    simp only [Rule.terms, List.mem_append, take, read, tell, checks, produce, collect, List.mem_flatMap,
      List.mem_map] at inside
    simp only [Rule.terms, List.mem_append]
    rcases inside with ((((((⟨m, inM, h⟩ | ⟨m, inM, h⟩) | ⟨e, ⟨m, inM, h⟩, rfl⟩) | ⟨e, ⟨m, inM, h⟩, rfl⟩) |
      ⟨c, ⟨m, inM, h⟩, h'⟩) | ⟨m, inM, h⟩) | ⟨m, inM, h⟩)
    · exact ⟨m, inM, Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))⟩
    · exact ⟨m, inM, Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))⟩
    · exact ⟨m, inM, Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map_of_mem h)))))⟩
    · exact ⟨m, inM, Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map_of_mem h))))⟩
    · exact ⟨m, inM, Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨c, h, h'⟩)))⟩
    · exact ⟨m, inM, Or.inl (Or.inr h)⟩
    · exact ⟨m, inM, Or.inr h⟩
  obtain ⟨m, inM, inTerms⟩ := inMember
  exact ground m inM t inTerms σ

omit [DecidableEq O] in
/-- **The tensor firing's information has the bag's equations.** -/
theorem information_tensor (ground : ∀ m ∈ l, GroundRule A m.rule) (split : Split l)
    (s : State (Terms T) O) (e : Equation T) :
    e ∈ (tensorFiring A l).information (frames A) s ↔ e ∈ Bag.information (frames A) s (bagOf A l) := by
  obtain ⟨openTake, openRead, openTell, -, -, -⟩ := opened_ground (tensor_ground ground)
  obtain ⟨bodyTake, bodyRead, bodyTell, -, -, -⟩ := tensor_rule_body (A := A) (l := l)
  have memberOpened : ∀ m ∈ l, (m.firing.opened (frames A)).take = m.rule.body.take ∧
      (m.firing.opened (frames A)).read = m.rule.body.read ∧
      (m.firing.opened (frames A)).tell = m.rule.body.tell := fun m inside =>
    ⟨(opened_ground (g := m.firing) (ground m inside)).1,
      (opened_ground (g := m.firing) (ground m inside)).2.1,
      (opened_ground (g := m.firing) (ground m inside)).2.2.1⟩
  have takes : (tensorFiring A l).matching (frames A) s ((tensorFiring A l).opened (frames A)).take
      (tensorFiring A l).selection.taken =
      l.flatMap fun m => m.firing.matching (frames A) s (m.firing.opened (frames A)).take
        m.selection.taken := by
    unfold Firing.matching
    rw [openTake, bodyTake]
    refine (zipWith_flatMap _ (fun m : OneMember A O P => takeOf m.rule)
      (fun m : OneMember A O P => m.selection.taken) l
      fun m inside => (split m inside).1).trans (List.flatMap_congr fun m inside => ?_)
    rw [(memberOpened m inside).1]
    rfl
  have reads : (tensorFiring A l).matching (frames A) s ((tensorFiring A l).opened (frames A)).read
      (tensorFiring A l).selection.read =
      l.flatMap fun m => m.firing.matching (frames A) s (m.firing.opened (frames A)).read
        m.selection.read := by
    unfold Firing.matching
    rw [openRead, bodyRead]
    refine (zipWith_flatMap _ (fun m : OneMember A O P => readOf m.rule)
      (fun m : OneMember A O P => m.selection.read) l
      fun m inside => (split m inside).2.1).trans (List.flatMap_congr fun m inside => ?_)
    rw [(memberOpened m inside).2.1]
    rfl
  have tells : ((tensorFiring A l).opened (frames A)).tell =
      l.flatMap fun m => (m.firing.opened (frames A)).tell := by
    rw [openTell, bodyTell]
    exact List.flatMap_congr fun m inside => (memberOpened m inside).2.2.symm
  unfold Firing.information Bag.information
  rw [takes, reads, tells]
  simp only [List.mem_append, List.mem_flatMap, Member.own]
  constructor
  · rintro (((known | ⟨m, inM, h⟩) | ⟨m, inM, h⟩) | ⟨m, inM, h⟩)
    · exact Or.inl known
    · exact Or.inr ⟨m, inM, Or.inl (Or.inl h)⟩
    · exact Or.inr ⟨m, inM, Or.inl (Or.inr h)⟩
    · exact Or.inr ⟨m, inM, Or.inr h⟩
  · rintro (known | ⟨m, inM, (h | h) | h⟩)
    · exact Or.inl (Or.inl (Or.inl known))
    · exact Or.inl (Or.inl (Or.inr ⟨m, inM, h⟩))
    · exact Or.inl (Or.inr ⟨m, inM, h⟩)
    · exact Or.inr ⟨m, inM, h⟩

omit [DecidableEq O] in
/-- **The tensor firing's guard predicate is the joint guard predicate of the bag.** -/
theorem holds_tensor (ground : ∀ m ∈ l, GroundRule A m.rule) (split : Split l)
    (s : State (Terms T) O) (σ : S) :
    (tensorFiring A l).Holds (frames A) s (b := PUnit.unit) σ ↔
      Bag.Holds (frames A) s (bagOf A l) (b := PUnit.unit) σ := by
  obtain ⟨-, -, -, openChecks, -, openCollect⟩ := opened_ground (tensor_ground ground)
  obtain ⟨-, -, -, bodyChecks, -, bodyCollect⟩ := tensor_rule_body (A := A) (l := l)
  have zipped : ((tensorFiring A l).collectOpened (frames A)).zip (tensorFiring A l).seen =
      l.flatMap fun m => (collectOf m.rule).zip m.seen := by
    rw [openCollect, bodyCollect]
    exact zipWith_flatMap Prod.mk (fun m : OneMember A O P => collectOf m.rule)
      (fun m : OneMember A O P => m.seen) l fun m inside => (split m inside).2.2.2
  have memberOpened : ∀ m ∈ l, (m.firing.opened (frames A)).checks = m.rule.body.checks ∧
      m.firing.collectOpened (frames A) = m.rule.collect := fun m inside =>
    ⟨(opened_ground (g := m.firing) (ground m inside)).2.2.2.1,
      (opened_ground (g := m.firing) (ground m inside)).2.2.2.2.2⟩
  unfold Firing.Holds Bag.Holds
  rw [openChecks, bodyChecks, zipped]
  constructor
  · rintro ⟨checks, collect⟩ m inM
    unfold Firing.Holds
    rw [(memberOpened m inM).1, (memberOpened m inM).2]
    exact ⟨fun c inside => checks c (List.mem_flatMap.mpr ⟨m, inM, inside⟩),
      fun q inside => collect q (List.mem_flatMap.mpr ⟨m, inM, inside⟩)⟩
  · intro each
    refine ⟨fun c inside => ?_, fun q inside => ?_⟩
    · obtain ⟨m, inM, inChecks⟩ := List.mem_flatMap.mp inside
      have holds := each m inM
      unfold Firing.Holds at holds
      rw [(memberOpened m inM).1] at holds
      exact holds.1 c inChecks
    · obtain ⟨m, inM, inZip⟩ := List.mem_flatMap.mp inside
      have holds := each m inM
      unfold Firing.Holds at holds
      rw [(memberOpened m inM).2] at holds
      exact holds.2 q inZip

/-- **A bag of ground matches is jointly admitted exactly when the firing of the tensor of their rules
is admitted**, each member selecting as many rows as its patterns. -/
theorem admits_iff_tensor (ground : ∀ m ∈ l, GroundRule A m.rule) (split : Split l)
    (s : State (Terms T) O) :
    Bag.Admits (frames A) s (bagOf A l) ↔ (tensorFiring A l).Admits (frames A) s := by
  obtain ⟨bodyTake, bodyRead, -, -, bodyProduce, bodyCollect⟩ := tensor_rule_body (A := A) (l := l)
  have sameModels : ∀ τ : S, A.Models τ ((tensorFiring A l).information (frames A) s) ↔
      A.Models τ (Bag.information (frames A) s (bagOf A l)) := fun τ =>
    ⟨fun solved e inside => solved e ((information_tensor ground split s e).mpr inside),
      fun solved e inside => solved e ((information_tensor ground split s e).mp inside)⟩
  constructor
  · rintro ⟨⟨-, taken, made, -⟩, enabled, ⟨_, τ, solved⟩, asks⟩
    refine ⟨⟨Examples.fresh_of_ground A s _ (tensor_ground ground), taken, made, ?_, ?_, ?_, ?_⟩,
      enabled, ⟨PUnit.unit, τ, (sameModels τ).mpr solved⟩, fun b σ solvedT =>
        (holds_tensor ground split s σ).mpr (asks b σ ((sameModels σ).mp solvedT))⟩
    · rw [bodyTake]
      exact length_flatMap_eq _ _ l fun m inside => (split m inside).1
    · rw [bodyRead]
      exact length_flatMap_eq _ _ l fun m inside => (split m inside).2.1
    · rw [bodyProduce]
      exact length_flatMap_eq _ _ l fun m inside => (split m inside).2.2.1
    · rw [bodyCollect]
      exact length_flatMap_eq _ _ l fun m inside => (split m inside).2.2.2
  · rintro ⟨⟨-, taken, made, -⟩, enabled, ⟨_, τ, solved⟩, asks⟩
    exact ⟨⟨fresh_of_ground_bag A s l ground, taken, made, split⟩, enabled,
      ⟨PUnit.unit, τ, (sameModels τ).mp solved⟩, fun b σ solvedB =>
        (holds_tensor ground split s σ).mp (asks b σ ((sameModels σ).mpr solvedB))⟩

/-- **The tensor firing has the bag's rows and labels, and its knowledge has the bag's equations.** -/
theorem result_tensor (ground : ∀ m ∈ l, GroundRule A m.rule) (split : Split l)
    (s : State (Terms T) O) :
    ((tensorFiring A l).result (frames A) s).present = (Bag.result (frames A) s (bagOf A l)).present ∧
      ((tensorFiring A l).result (frames A) s).label = (Bag.result (frames A) s (bagOf A l)).label ∧
      ∀ e, e ∈ ((tensorFiring A l).result (frames A) s).knowledge ↔
        e ∈ (Bag.result (frames A) s (bagOf A l)).knowledge := by
  obtain ⟨-, -, -, -, openProduce, -⟩ := opened_ground (tensor_ground ground)
  obtain ⟨-, -, -, -, bodyProduce, -⟩ := tensor_rule_body (A := A) (l := l)
  have produced : ((tensorFiring A l).opened (frames A)).produce = Bag.produce (frames A) (bagOf A l) := by
    rw [openProduce, bodyProduce]
    exact List.flatMap_congr fun m inside =>
      ((opened_ground (g := m.firing) (ground m inside)).2.2.2.2.1).symm
  refine ⟨rfl, ?_, information_tensor ground split s⟩
  show relabel ((tensorFiring A l).row (frames A) s) (bagOf A l).selection.made
      ((tensorFiring A l).opened (frames A)).produce =
    relabel (fun o => (frames A).act ((ext A).weaken PUnit.unit) (s.label o)) (bagOf A l).selection.made
      (Bag.produce (frames A) (bagOf A l))
  rw [produced]
  rfl

end Tensor

#print axioms tensorOf_single
#print axioms opened_ground
#print axioms tensor_ground
#print axioms information_tensor
#print axioms holds_tensor
#print axioms admits_iff_tensor
#print axioms result_tensor

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings
