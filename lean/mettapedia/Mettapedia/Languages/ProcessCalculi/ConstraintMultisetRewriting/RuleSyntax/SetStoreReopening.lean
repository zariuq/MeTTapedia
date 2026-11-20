import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreLifting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricFinite

/-! # Reopen admitted ground-source matches without changing their keys -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreSyntax

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)
open JointFirings

variable {signature : LPSignature} [DecidableEq signature.vars]
  [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]
  {P : Program (Terms (Term signature))}

def namespaceMap (slots : signature.vars ≃ ℕ) (index : ℕ) (slot : signature.vars) : signature.vars :=
  slots.symm (Nat.pair index (slots slot))

def namespaceBack (slots : signature.vars ≃ ℕ) (slot : signature.vars) : signature.vars :=
  slots.symm (Nat.unpair (slots slot)).2

omit [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
theorem namespace_inverse (slots : signature.vars ≃ ℕ) (index : ℕ) :
    Function.LeftInverse (namespaceBack slots) (namespaceMap slots index) := by
  intro slot
  simp [namespaceBack, namespaceMap]

def newMade (index : ℕ) (old : List (Term signature × ℕ)) : List (Term signature × ℕ) :=
  old.zipIdx.map fun entry => (entry.1.1, Nat.pair index entry.2 + 1)

omit [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
theorem newMade_nodup (index : ℕ) (old : List (Term signature × ℕ)) : (newMade index old).Nodup := by
  apply List.Nodup.of_map Prod.snd
  have indices : (old.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range' 1 (by decide)
  have injective : Function.Injective (fun n => Nat.pair index n + 1) := by
    intro n m equal
    exact (Nat.pair_eq_pair.mp (Nat.add_right_cancel equal)).2
  simpa only [newMade, List.map_map, Function.comp_def] using indices.map injective

omit [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
theorem newMade_disjoint {first second : ℕ} (different : first ≠ second)
    (left right : List (Term signature × ℕ)) :
    List.Disjoint (newMade first left) (newMade second right) := by
  apply List.disjoint_left.mpr
  intro row leftMember rightMember
  obtain ⟨one, _, oneEq⟩ := List.mem_map.mp leftMember
  obtain ⟨two, _, twoEq⟩ := List.mem_map.mp rightMember
  have address : Nat.pair first one.2 + 1 = Nat.pair second two.2 + 1 :=
    congrArg Prod.snd (oneEq.trans twoEq.symm)
  exact different ((Nat.pair_eq_pair.mp (Nat.add_right_cancel address)).1)

def reopen (slots : signature.vars ≃ ℕ) (index : ℕ)
    (f : Firing (Term signature × ℕ) (E (signature := signature)) P PUnit.unit) :
    Firing (Term signature × ℕ) (E (signature := signature)) P PUnit.unit :=
  ⟨f.rule, f.member, PUnit.unit, (FirstOrderFreshFamily.opening slots index).comp f.opening,
    {f.selection with made := newMade index f.selection.made}, f.seen⟩

omit [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
theorem reopen_ordered_key (slots : signature.vars ≃ ℕ) (index : ℕ)
    (f : Firing (Term signature × ℕ) (E (signature := signature)) P PUnit.unit) :
    firingKey (reopen slots index f) = firingKey f := rfl

omit [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
theorem reopen_symmetric_key (slots : signature.vars ≃ ℕ) (index : ℕ)
    (f : Firing (Term signature × ℕ) (E (signature := signature)) P PUnit.unit) :
    SymmetricMatches.identity.key (reopen slots index f) = SymmetricMatches.identity.key f := rfl

theorem readonly_information (rows : Finset (Term signature))
    (f : Firing (Term signature × ℕ) (E (signature := signature)) P PUnit.unit)
    (pure : Propagates f.rule) :
    f.information X (SetStore.represent rows) =
      (f.opened X).read.zipWith (fun term (row : Term signature × ℕ) => (term, row.1)) f.selection.read := by
  have noTake : (f.opened X).take = [] := by
    change f.rule.body.take.map _ = []
    rw [pure.noTake, List.map_nil]
  have noTell : (f.opened X).tell = [] := by
    change f.rule.body.tell.map _ = []
    rw [pure.noTell, List.map_nil]
  change [] ++ (f.opened X).take.zipWith _ f.selection.taken ++
    (f.opened X).read.zipWith (fun term row => (term, (Subst.id signature).applyTerm row.1)) f.selection.read ++
    (f.opened X).tell = _
  rw [noTake, noTell]
  simp only [List.zipWith_nil_left, List.nil_append, List.append_nil, Subst.applyTerm_id]

omit [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
private theorem matching_rename (rename : Subst signature) (patterns : List (Term signature))
    (rows : List (Term signature × ℕ)) (fixed : ∀ row ∈ rows, rename.applyTerm row.1 = row.1) :
    (patterns.map rename.applyTerm).zipWith (fun term row => (term, row.1)) rows =
      (patterns.zipWith (fun term row => (term, row.1)) rows).map
        (fun equation => (rename.applyTerm equation.1, rename.applyTerm equation.2)) := by
  induction patterns generalizing rows with
  | nil => simp
  | cons term rest ih =>
    cases rows with
    | nil => simp
    | cons row later =>
      simp only [List.map_cons, List.zipWith_cons_cons]
      rw [fixed row List.mem_cons_self, ih later (fun row member => fixed row (List.mem_cons_of_mem _ member))]

theorem reopen_information (slots : signature.vars ≃ ℕ) (index : ℕ) (rows : Finset (Term signature))
    (ground : GroundRows rows)
    (f : Firing (Term signature × ℕ) (E (signature := signature)) P PUnit.unit)
    (pure : Propagates f.rule) (yes : f.Admits X (SetStore.represent rows)) :
    (reopen slots index f).information X (SetStore.represent rows) =
      UnificationRenaming.equations (namespaceMap slots index) (f.information X (SetStore.represent rows)) := by
  rw [readonly_information rows f pure, readonly_information rows (reopen slots index f) pure]
  have reads : ((reopen slots index f).opened X).read =
      (f.opened X).read.map (FirstOrderFreshFamily.opening slots index).applyTerm := by
    change f.rule.body.read.map ((FirstOrderFreshFamily.opening slots index).comp f.opening).applyTerm =
      (f.rule.body.read.map f.opening.applyTerm).map (FirstOrderFreshFamily.opening slots index).applyTerm
    rw [List.map_map]
    apply List.map_congr_left
    intro term _
    exact Subst.applyTerm_comp _ _ _
  rw [reads]
  apply matching_rename
  intro row member
  exact FirstOrder.ground_fixed _ _ (ground row.1
    (present_value rows (yes.2.1.kept_subset (List.mem_toFinset.mpr member))))

theorem reopen_fresh (slots : signature.vars ≃ ℕ) (index : ℕ) (rows : Finset (Term signature))
    (ground : GroundRows rows)
    (f : Firing (Term signature × ℕ) (E (signature := signature)) P PUnit.unit)
    (yes : f.Admits X (SetStore.represent rows)) :
    (reopen slots index f).Fresh X (SetStore.represent rows) := by
  intro b g h
  cases b
  obtain ⟨original, _, localValues⟩ := yes.1.1 PUnit.unit (Subst.id signature) h
  refine ⟨PrivateVariableRenaming.reindex (namespaceBack slots) original, ?_, ?_⟩
  · intro term mentioned
    obtain (known | known | ⟨row, inside, rfl⟩) := mentioned
    · cases known
    · cases known
    · change (PrivateVariableRenaming.reindex _ original).applyTerm ((Subst.id signature).applyTerm row.1) = g.applyTerm row.1
      rw [Subst.applyTerm_id, FirstOrder.ground_fixed _ _ (ground row.1 (present_value rows inside)),
        FirstOrder.ground_fixed g _ (ground row.1 (present_value rows inside))]
  · intro term member
    change (PrivateVariableRenaming.reindex _ original).applyTerm
      (((FirstOrderFreshFamily.opening slots index).comp f.opening).applyTerm term) = h.applyTerm term
    rw [Subst.applyTerm_comp]
    have undo := PrivateVariableRenaming.reindex_renamed (namespaceMap slots index) (namespaceBack slots)
      (namespace_inverse slots index) original (f.opening.applyTerm term)
    exact undo.trans (localValues term member)

theorem reopen_admitted (slots : signature.vars ≃ ℕ) (index : ℕ) (rows : Finset (Term signature))
    (ground : GroundRows rows)
    (f : Firing (Term signature × ℕ) (E (signature := signature)) P PUnit.unit)
    (pure : Propagates f.rule) (yes : f.Admits X (SetStore.represent rows)) :
    (reopen slots index f).Admits X (SetStore.represent rows) := by
  refine ⟨⟨reopen_fresh slots index rows ground f yes, yes.1.2.1, newMade_nodup _ _, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact yes.1.2.2.2.1
  · exact yes.1.2.2.2.2.1
  · simpa only [reopen, newMade, List.length_map, List.length_zipIdx] using yes.1.2.2.2.2.2.1
  · exact yes.1.2.2.2.2.2.2
  · refine ⟨yes.2.1.taken_subset, yes.2.1.kept_subset, yes.2.1.apart, ?_, ?_⟩
    · apply Finset.disjoint_left.mpr
      intro row made present
      obtain ⟨entry, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp made)
      obtain ⟨old, _, equal⟩ := Finset.mem_image.mp present
      have zero : Nat.pair index entry.2 + 1 = 0 := (congrArg Prod.snd equal).symm
      omega
    · intro query member
      simp [Selection.commit] at member
  · obtain ⟨b, assignment, solved⟩ := yes.2.2.1
    cases b
    refine ⟨PUnit.unit, PrivateVariableRenaming.reindex (namespaceBack slots) assignment, ?_⟩
    rw [reopen_information slots index rows ground f pure yes]
    exact PrivateVariableRenaming.reindex_unifies_renamed _ _ (namespace_inverse slots index) _ _ solved
  · intro b assignment solved
    cases b
    rw [reopen_information slots index rows ground f pure yes] at solved
    have original := PrivateVariableRenaming.reindex_unifies (namespaceMap slots index) assignment _ solved
    have holds := yes.2.2.2 PUnit.unit _ original
    refine ⟨?_, ?_⟩
    · intro check member
      obtain ⟨source, inside, rfl⟩ := List.mem_map.mp member
      obtain ⟨left, right, rfl⟩ := pure.positive.1 source inside
      have checked := holds.1 (.equal (f.opening.applyTerm left) (f.opening.applyTerm right))
        (List.mem_map.mpr ⟨Check.equal left right, inside, rfl⟩)
      change (PrivateVariableRenaming.reindex _ assignment).applyTerm (f.opening.applyTerm left) =
        (PrivateVariableRenaming.reindex _ assignment).applyTerm (f.opening.applyTerm right) at checked
      rw [PrivateVariableRenaming.reindex_apply, PrivateVariableRenaming.reindex_apply] at checked
      change assignment.applyTerm (((FirstOrderFreshFamily.opening slots index).comp f.opening).applyTerm left) =
        assignment.applyTerm (((FirstOrderFreshFamily.opening slots index).comp f.opening).applyTerm right)
      have renamed : assignment.applyTerm
          ((FirstOrderFreshFamily.opening slots index).applyTerm (f.opening.applyTerm left)) =
          assignment.applyTerm ((FirstOrderFreshFamily.opening slots index).applyTerm (f.opening.applyTerm right)) := checked
      simpa only [Subst.applyTerm_comp] using renamed
    · intro query member
      change query ∈ (f.rule.collect.map _).zip f.seen at member
      rw [pure.positive.2] at member
      cases member

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreSyntax
