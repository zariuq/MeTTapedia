import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.AskTimingInstances
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreOutcomes

/-!
# Selecting complete commits at the declared ask timing

Filtering the bag chosen by the after-tells commit policy and quantifying
over the matches admitted before tells are different contracts. Their bag
admissions are incomparable: `StepWeb.AskTimingControls.every_incomparable`,
`maximal_incomparable` and `unique_incomparable`. The original
`DisciplinedStep` is unchanged.
`QuantifiedStep` uses the latter reading for every, maximal and unique.
Match identities are the existing parameter, including symmetric identities.
For programs without tells the two constructions coincide.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Bag

open Interface (Frames)

universe uO uT uH uE uOcc uK

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Frames Tm Hom) {O : Type uOcc} [DecidableEq O]
  {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm} (s : State Tm O)

/-- The quantifier uses before-tells admission and the supplied match identity. -/
def CompleteBeforeTellsBy
    (identity : MatchIdentity.{uO, uT, uH, uE, uOcc, uK} O E P)
    (region : identity.Key → Prop) (f : Bag O E P s.frame) : Prop :=
  ∀ g : Firing O E P s.frame, region (identity.key g) → g.AdmitsBeforeTells X s →
    identity.key g ∈ f.keysBy identity

def AdmitsEveryBeforeTellsBy
    (identity : MatchIdentity.{uO, uT, uH, uE, uOcc, uK} O E P)
    (region : identity.Key → Prop) (f : Bag O E P s.frame) : Prop :=
  StepWeb.AdmitsOwnBeforeTells X s f ∧ (∀ key ∈ f.keysBy identity, region key) ∧
    f.DistinctBy identity ∧ f.CompleteBeforeTellsBy X s identity region

def AdmitsUniqueBeforeTellsBy
    (identity : MatchIdentity.{uO, uT, uH, uE, uOcc, uK} O E P)
    (region : identity.Key → Prop) (f : Bag O E P s.frame) : Prop :=
  f.AdmitsEveryBeforeTellsBy X s identity region ∧ f.members.length = 1

variable {X s}

theorem member_beforeTells
    (inhabited : ∀ (r : Rule Tm) (b : Obj), Nonempty (Hom r.locals b))
    {f : Bag O E P s.frame} (own : StepWeb.AdmitsOwnBeforeTells X s f)
    {m : Member O E P f.ext} (inside : m ∈ f.members) : m.firing.AdmitsBeforeTells X s := by
  have after := admits_member X inhabited (StepWeb.admitsOwn_of_ownBeforeTells own) inside
  exact ⟨after.1, after.2.1, after.2.2.1, own.2.2.2 m inside⟩

/-- Completeness uses the same T2 keys; no new presentation equivalence is introduced. -/
theorem AdmitsEveryBeforeTellsBy.keys_perm
    (inhabited : ∀ (r : Rule Tm) (b : Obj), Nonempty (Hom r.locals b))
    {identity : MatchIdentity.{uO, uT, uH, uE, uOcc, uK} O E P}
    {region : identity.Key → Prop} {f g : Bag O E P s.frame}
    (first : f.AdmitsEveryBeforeTellsBy X s identity region)
    (second : g.AdmitsEveryBeforeTellsBy X s identity region) :
    (f.keysBy identity).Perm (g.keysBy identity) := by
  apply (List.perm_ext_iff_of_nodup first.2.2.1 second.2.2.1).mpr
  intro key
  constructor
  · intro member
    obtain ⟨m, inM, rfl⟩ := List.mem_map.mp member
    exact second.2.2.2 m.firing (first.2.1 _ member) (member_beforeTells inhabited first.1 inM)
  · intro member
    obtain ⟨m, inM, rfl⟩ := List.mem_map.mp member
    exact first.2.2.2 m.firing (second.2.1 _ member) (member_beforeTells inhabited second.1 inM)

theorem completeBeforeTellsBy_of_completeBy
    {identity : MatchIdentity.{uO, uT, uH, uE, uOcc, uK} O E P}
    {region : identity.Key → Prop} {f : Bag O E P s.frame}
    (complete : f.CompleteBy X s identity region) : f.CompleteBeforeTellsBy X s identity region :=
  fun g inside before => complete g inside (Firing.admits_of_beforeTells X s g before)

theorem completeBeforeTellsBy_iff_of_entailed
    {identity : MatchIdentity.{uO, uT, uH, uE, uOcc, uK} O E P}
    {region : identity.Key → Prop} {f : Bag O E P s.frame}
    (entailed : ∀ g : Firing O E P s.frame, region (identity.key g) →
      X.Entails (g.askInformation X s) (fun _ σ => X.Models σ (g.opened X).tell)) :
    f.CompleteBeforeTellsBy X s identity region ↔ f.CompleteBy X s identity region := by
  refine ⟨?_, completeBeforeTellsBy_of_completeBy⟩
  intro before g inside after
  exact before g inside ((StepWeb.oneMatch_beforeTells_iff_of_entailed g (entailed g inside)).mpr after)

theorem everyBeforeTellsBy_iff_of_entailed
    {identity : MatchIdentity.{uO, uT, uH, uE, uOcc, uK} O E P}
    {region : identity.Key → Prop} {f : Bag O E P s.frame}
    (entailed : ∀ g : Firing O E P s.frame, region (identity.key g) →
      X.Entails (g.askInformation X s) (fun _ σ => X.Models σ (g.opened X).tell)) :
    f.AdmitsEveryBeforeTellsBy X s identity region ↔ f.AdmitsEveryBy X s identity region := by
  constructor
  · rintro ⟨own, within, distinct, complete⟩
    exact ⟨StepWeb.admitsOwn_of_ownBeforeTells own, within, distinct,
      (completeBeforeTellsBy_iff_of_entailed entailed).mp complete⟩
  · rintro ⟨own, within, distinct, complete⟩
    refine ⟨(StepWeb.ownBeforeTells_iff_of_entailed ?_).mpr own, within, distinct,
      completeBeforeTellsBy_of_completeBy complete⟩
    intro m inside
    exact entailed m.firing (within _ (List.mem_map.mpr ⟨m, inside, rfl⟩))

theorem everyBeforeTellsBy_iff_of_no_tells
    (silent : ∀ r ∈ P, r.body.tell = [])
    {identity : MatchIdentity.{uO, uT, uH, uE, uOcc, uK} O E P}
    {region : identity.Key → Prop} {f : Bag O E P s.frame} :
    f.AdmitsEveryBeforeTellsBy X s identity region ↔ f.AdmitsEveryBy X s identity region := by
  apply everyBeforeTellsBy_iff_of_entailed
  intro g _ b σ _
  rw [StepWeb.opened_tell_nil X g (silent g.rule g.member)]
  exact Frames.models_nil σ

theorem uniqueBeforeTellsBy_iff_of_no_tells
    (silent : ∀ r ∈ P, r.body.tell = [])
    {identity : MatchIdentity.{uO, uT, uH, uE, uOcc, uK} O E P}
    {region : identity.Key → Prop} {f : Bag O E P s.frame} :
    f.AdmitsUniqueBeforeTellsBy X s identity region ↔ f.AdmitsUniqueBy X s identity region :=
  and_congr (everyBeforeTellsBy_iff_of_no_tells silent) Iff.rfl

/-- The ordered instance is exactly the previously named before-tells reading. -/
theorem everyBeforeTellsBy_ordered_iff (Q : Set (Rule Tm)) (f : Bag O E P s.frame) :
    f.AdmitsEveryBeforeTellsBy X s MatchIdentity.ordered (fun key => key.1 ∈ Q) ↔
      StepWeb.AdmitsEveryBeforeTells X s Q f := by
  unfold AdmitsEveryBeforeTellsBy StepWeb.AdmitsEveryBeforeTells CompleteBeforeTellsBy
    StepWeb.CompleteBeforeTells DistinctBy Distinct Within keysBy
  simp only [MatchIdentity.ordered, firingKey_firing]
  constructor
  · rintro ⟨own, within, distinct, complete⟩
    exact ⟨own, fun m inside => within m.key (List.mem_map.mpr ⟨m, inside, rfl⟩), distinct, complete⟩
  · rintro ⟨own, within, distinct, complete⟩
    refine ⟨own, ?_, distinct, complete⟩
    intro key member
    obtain ⟨m, inside, rfl⟩ := List.mem_map.mp member
    exact within m inside

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Bag

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreSyntax

open Mettapedia.Logic.LP
open OneFrame (Terms)
open JointFirings

variable {signature : LPSignature} [DecidableEq signature.vars]
  [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]
  {P : Program (Terms (Term signature))}

/-- The quantified disciplines select their matches at the declared ask timing.
The other disciplines retain their existing admission definitions. -/
def QuantifiedAllowed (discipline : Discipline) (timing : SetStore.AskTiming)
    (rows : Finset (Term signature)) (bag : SetStore.Candidate P) : Prop :=
  match discipline, timing with
  | .every, .beforeTells =>
    bag.AdmitsEveryBeforeTellsBy X (SetStore.represent rows) SymmetricMatches.identity Set.univ
  | .maximal, .beforeTells => StepWeb.AdmitsMaximalBeforeTells X (SetStore.represent rows) bag
  | .unique, .beforeTells =>
    bag.AdmitsUniqueBeforeTellsBy X (SetStore.represent rows) SymmetricMatches.identity Set.univ
  | _, _ => Allowed discipline rows bag

def QuantifiedStep (discipline : Discipline) (timing : SetStore.AskTiming)
    (P : Program (Terms (Term signature))) (rows after : Finset (Term signature)) : Prop :=
  ∃ bag : SetStore.Candidate P, bag.members ≠ [] ∧ SetStore.admitted timing rows bag ∧
    QuantifiedAllowed discipline timing rows bag ∧
    ∃ answer, unifyTotal (bag.information X (SetStore.represent rows)) = some answer ∧
      after = SetStore.setResult rows bag answer ∧ ¬ SetStore.SameRows rows after

theorem quantified_is_step {discipline : Discipline} {timing : SetStore.AskTiming}
    {rows after : Finset (Term signature)} (yes : QuantifiedStep discipline timing P rows after) :
    SetStore.Step timing P rows after := by
  obtain ⟨bag, nonempty, admitted, _, answer, accepted, result, changed⟩ := yes
  exact ⟨bag, nonempty, admitted, answer, accepted, result, changed⟩

theorem quantified_after_iff {discipline : Discipline} {rows after : Finset (Term signature)} :
    QuantifiedStep discipline .afterTells P rows after ↔
      DisciplinedStep discipline .afterTells P rows after := by
  cases discipline <;> rfl

theorem quantifiedAllowed_iff_of_no_tells (silent : ∀ r ∈ P, r.body.tell = [])
    (discipline : Discipline) (timing : SetStore.AskTiming)
    (rows : Finset (Term signature)) (bag : SetStore.Candidate P) :
    QuantifiedAllowed discipline timing rows bag ↔ Allowed discipline rows bag := by
  cases timing with
  | afterTells => cases discipline <;> rfl
  | beforeTells =>
    cases discipline with
    | one | round | synchronous | joint => rfl
    | every => exact Bag.everyBeforeTellsBy_iff_of_no_tells silent
    | maximal => exact StepWeb.maximalBeforeTells_iff_of_no_tells silent
    | unique => exact Bag.uniqueBeforeTellsBy_iff_of_no_tells silent

/-- The propagation contract is independent of the two quantifier readings. -/
theorem quantified_iff_of_no_tells (silent : ∀ r ∈ P, r.body.tell = [])
    {discipline : Discipline} {timing : SetStore.AskTiming}
    {rows after : Finset (Term signature)} :
    QuantifiedStep discipline timing P rows after ↔ DisciplinedStep discipline timing P rows after := by
  simp only [QuantifiedStep, DisciplinedStep,
    quantifiedAllowed_iff_of_no_tells silent]

theorem quantified_timings_iff_of_no_tells (silent : ∀ r ∈ P, r.body.tell = [])
    {discipline : Discipline} {rows after : Finset (Term signature)} :
    QuantifiedStep discipline .beforeTells P rows after ↔
      QuantifiedStep discipline .afterTells P rows after :=
  (quantified_iff_of_no_tells silent).trans
    ((StepWeb.disciplined_iff_of_no_tells silent).trans (quantified_iff_of_no_tells silent).symm)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreSyntax
