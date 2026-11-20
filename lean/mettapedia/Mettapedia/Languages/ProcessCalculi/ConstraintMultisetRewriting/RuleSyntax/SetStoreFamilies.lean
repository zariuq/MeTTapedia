import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreReopening

/-! # Jointly fresh bags of actual admitted first-order matches -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreSyntax

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)
open JointFirings

variable {signature : LPSignature} [DecidableEq signature.vars]
  [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]
  {P : Program (Terms (Term signature))}

abbrev F := Firing (Term signature × ℕ) (E (signature := signature)) P PUnit.unit

universe u

private theorem zipIdx_member {T : Type u} {values : List T} {entry : T × ℕ}
    (inside : entry ∈ values.zipIdx) : entry.1 ∈ values := by
  have position := List.mem_zipIdx inside
  rw [position.2.2]
  exact List.getElem_mem _

def reopenedMember (slots : signature.vars ≃ ℕ) (index : ℕ) (f : F (P := P)) :
    OneMember (FirstOrder.action signature) (Term signature × ℕ) P :=
  Member.ofFiring (reopen slots index f)

def reopenBag (slots : signature.vars ≃ ℕ) (firings : List (F (P := P))) : SetStore.Candidate P :=
  ⟨PUnit.unit, firings.zipIdx.map fun entry => reopenedMember slots entry.2 entry.1⟩

def reopenEntry (slots : signature.vars ≃ ℕ) (rows : Finset (Term signature))
    (firings : List (F (P := P)))
    (admitted : ∀ f ∈ firings, f.Admits X (SetStore.represent rows))
    (entry : {entry // entry ∈ firings.zipIdx}) :
    FirstOrderFreshFamily.Reopened slots (Term signature × ℕ) P where
  index := entry.val.2
  member := reopenedMember slots entry.val.2 entry.val.1
  inner := entry.val.1.opening
  opening_eq := rfl
  realizes h := by
    obtain ⟨assignment, _, values⟩ :=
      (admitted entry.val.1 (zipIdx_member entry.property)).1.1 PUnit.unit (Subst.id signature) h
    exact ⟨assignment, values⟩

def reopenEntries (slots : signature.vars ≃ ℕ) (rows : Finset (Term signature))
    (firings : List (F (P := P)))
    (admitted : ∀ f ∈ firings, f.Admits X (SetStore.represent rows)) :=
  firings.zipIdx.attach.map (reopenEntry slots rows firings admitted)

theorem reopenEntries_members (slots : signature.vars ≃ ℕ) (rows : Finset (Term signature))
    (firings : List (F (P := P))) (admitted : ∀ f ∈ firings, f.Admits X (SetStore.represent rows)) :
    (reopenEntries slots rows firings admitted).map FirstOrderFreshFamily.Reopened.member =
      (reopenBag slots firings).members := by
  unfold reopenEntries
  rw [List.map_map]
  change firings.zipIdx.attach.map (fun entry => reopenedMember slots entry.val.2 entry.val.1) = _
  exact List.attach_map_val (f := fun entry : F (P := P) × ℕ => reopenedMember slots entry.2 entry.1)

theorem reopenBag_fresh (slots : signature.vars ≃ ℕ) (rows : Finset (Term signature)) (ground : GroundRows rows)
    (firings : List (F (P := P))) (admitted : ∀ f ∈ firings, f.Admits X (SetStore.represent rows)) :
    (reopenBag slots firings).Fresh X (SetStore.represent rows) := by
  have distinct : ((reopenEntries slots rows firings admitted).map FirstOrderFreshFamily.Reopened.index).Nodup := by
    unfold reopenEntries
    rw [List.map_map]
    change (firings.zipIdx.attach.map (fun entry => entry.val.2)).Nodup
    rw [List.attach_map_val]
    rw [List.zipIdx_map_snd]
    exact List.nodup_range' 1 (by decide)
  have all := FirstOrderFreshFamily.fresh_composed slots [] (SetStore.represent rows).present Prod.fst
    (reopenEntries slots rows firings admitted) distinct (by
      intro term mentioned
      obtain (known | known | ⟨row, present, rfl⟩) := mentioned
      · cases known
      · cases known
      · exact ground row.1 (present_value rows present))
  rw [reopenEntries_members] at all
  exact all

omit [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
theorem reopenBag_made_nodup (slots : signature.vars ≃ ℕ) (firings : List (F (P := P))) :
    (reopenBag slots firings).selection.made.Nodup := by
  change ((firings.zipIdx.map fun entry => reopenedMember slots entry.2 entry.1).flatMap
    (fun member => member.selection.made)).Nodup
  simp only [List.flatMap_map]
  apply List.nodup_flatMap.mpr
  refine ⟨fun entry _ => newMade_nodup entry.2 entry.1.selection.made, ?_⟩
  have indices : (firings.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range' 1 (by decide)
  have different : firings.zipIdx.Pairwise (fun first second => first.2 ≠ second.2) :=
    List.pairwise_map.mp (List.nodup_iff_pairwise_ne.mp indices)
  exact different.imp fun notEqual => newMade_disjoint notEqual _ _

theorem reopenBag_taken_nil (slots : signature.vars ≃ ℕ) (rows : Finset (Term signature))
    (pure : ∀ rule ∈ P, Propagates rule) (firings : List (F (P := P)))
    (admitted : ∀ f ∈ firings, f.Admits X (SetStore.represent rows)) :
    (reopenBag slots firings).selection.taken = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro member inside
  obtain ⟨entry, present, rfl⟩ := List.mem_map.mp inside
  have yes := admitted entry.1 (zipIdx_member present)
  have lengths := yes.1.2.2.2.1
  rw [(pure entry.1.rule entry.1.member).noTake] at lengths
  exact List.eq_nil_of_length_eq_zero lengths.symm

theorem reopenBag_enabled (slots : signature.vars ≃ ℕ) (rows : Finset (Term signature))
    (pure : ∀ rule ∈ P, Propagates rule) (firings : List (F (P := P)))
    (admitted : ∀ f ∈ firings, f.Admits X (SetStore.represent rows)) :
    MeTTaCalculus.OccurrenceCommits.Enabled (fun _ : Term signature × ℕ => ()) (SetStore.represent rows).present
      ((reopenBag slots firings).selection.commit (T := Unit)) := by
  have noTake := reopenBag_taken_nil slots rows pure firings admitted
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Selection.commit, noTake]
  · intro row read
    obtain ⟨member, inside, selected⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp read)
    obtain ⟨entry, present, rfl⟩ := List.mem_map.mp inside
    exact (admitted entry.1 (zipIdx_member present)).2.1.kept_subset (List.mem_toFinset.mpr selected)
  · simp [Selection.commit, noTake]
  · apply Finset.disjoint_left.mpr
    intro row made present
    obtain ⟨member, inside, selected⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp made)
    obtain ⟨entry, _, rfl⟩ := List.mem_map.mp inside
    obtain ⟨part, _, rfl⟩ := List.mem_map.mp selected
    obtain ⟨old, _, equal⟩ := Finset.mem_image.mp present
    have zero : Nat.pair entry.2 part.2 + 1 = 0 := (congrArg Prod.snd equal).symm
    omega
  · intro query member
    simp [Selection.commit] at member

theorem reopenBag_own (slots : signature.vars ≃ ℕ) (rows : Finset (Term signature)) (ground : GroundRows rows)
    (pure : ∀ rule ∈ P, Propagates rule) (firings : List (F (P := P)))
    (admitted : ∀ f ∈ firings, f.Admits X (SetStore.represent rows)) :
    (reopenBag slots firings).AdmitsOwn X (SetStore.represent rows) := by
  have fresh := reopenBag_fresh slots rows ground firings admitted
  have takes := reopenBag_taken_nil slots rows pure firings admitted
  have made := reopenBag_made_nodup slots firings
  have enabled := reopenBag_enabled slots rows pure firings admitted
  have members : ∀ m ∈ (reopenBag slots firings).members, m.firing.Admits X (SetStore.represent rows) := by
    intro m inside
    obtain ⟨entry, present, rfl⟩ := List.mem_map.mp inside
    exact reopen_admitted slots entry.2 rows ground entry.1 (pure entry.1.rule entry.1.member)
      (admitted entry.1 (zipIdx_member present))
  by_cases nonempty : (reopenBag slots firings).members ≠ []
  · apply (admitsOwn_iff_members (FirstOrder.action signature) (s := SetStore.represent rows) ?_ nonempty).mpr
    · exact ⟨fresh, takes ▸ List.nodup_nil, made, enabled, members⟩
    · intro term mentioned assignment
      obtain (known | known | ⟨row, present, rfl⟩) := mentioned
      · cases known
      · cases known
      · exact FirstOrder.ground_fixed _ _ (ground row.1 (present_value rows present))
  · have empty := Classical.not_not.mp nonempty
    refine ⟨⟨fresh, takes ▸ List.nodup_nil, made, fun m inside => ?_⟩, enabled, ?_, ?_⟩
    · rw [empty] at inside
      cases inside
    · refine ⟨PUnit.unit, Subst.id signature, ?_⟩
      simp only [Bag.information, empty, List.flatMap_nil, List.append_nil]
      exact Interface.Frames.models_nil _
    · intro m inside
      rw [empty] at inside
      cases inside

omit [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
theorem reopenBag_symmetric_keys (slots : signature.vars ≃ ℕ) (firings : List (F (P := P))) :
    (reopenBag slots firings).keysBy SymmetricMatches.identity = firings.map SymmetricMatches.identity.key := by
  change (firings.zipIdx.map fun entry => reopenedMember slots entry.2 entry.1).map
    (fun m => SymmetricMatches.identity.key m.firing) = _
  rw [List.map_map]
  calc
    _ = firings.zipIdx.map (fun entry => SymmetricMatches.identity.key entry.1) := by
      apply List.map_congr_left
      intro entry _
      exact reopen_symmetric_key slots entry.2 entry.1
    _ = (firings.zipIdx.map Prod.fst).map SymmetricMatches.identity.key := List.map_map.symm
    _ = _ := by rw [List.zipIdx_map_fst]

/-- Finite representatives become a genuinely joint-fresh complete bag. -/
theorem exists_every_bag (slots : signature.vars ≃ ℕ) (rows : Finset (Term signature)) (ground : GroundRows rows)
    (pure : ∀ rule ∈ P, Propagates rule) (rules : List (Rule (Terms (Term signature))))
    (covers : ∀ rule ∈ P, rule ∈ rules) :
    ∃ bag : SetStore.Candidate P,
      bag.AdmitsEveryBy X (SetStore.represent rows) SymmetricMatches.identity Set.univ := by
  obtain ⟨representatives, distinct, admitted, complete⟩ :=
    SymmetricMatches.finite_admitted_representatives (SetStore.represent rows) rules covers
  refine ⟨reopenBag slots representatives, reopenBag_own slots rows ground pure representatives admitted,
    (by intro key _; exact Set.mem_univ key), ?_, ?_⟩
  · change ((reopenBag slots representatives).keysBy SymmetricMatches.identity).Nodup
    rw [reopenBag_symmetric_keys]
    exact distinct
  · intro f _ yes
    rw [reopenBag_symmetric_keys]
    exact complete f yes

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreSyntax
