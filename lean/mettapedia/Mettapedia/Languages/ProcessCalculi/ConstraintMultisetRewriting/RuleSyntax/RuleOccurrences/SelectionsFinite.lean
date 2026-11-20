import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.RowLocality

/-!
# Finitely many selections

`RuleSyntax.selections_finite` says that at a finite store the admitted firings of the step of a
program with one rule, extension, opening and choice of made identities are finitely many. The same
holds of the candidate, for every code system:

* **`RFiring.selections_finite`**: the admitted firings with one use, extension and opening, one
  choice of made row identities, and one choice of the rule identities made, the codes installed, the
  occurrences removed and the codes published (`RFiring.sameChoice`) form a finite set. Their taken
  and read lists range over the present rows, and each collect pattern sees a subset of them.

What stays free in a firing is what no admission observes beyond newness and freshness: the made row
identities (`RuleSyntax.Controls.made_choices_infinite`), the opening off the rule's unknowns
(`FreeData.free_data`), and the made rule identities (`WritingBack.Atoms.new_identity_free`). The set
is not empty in general: `UsedUp.once_admitted` is a member of its own.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uO uT uH uE uOcc uR uC uZ

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {R : Type uR} {C : Type uC} {Z : Type uZ}
  {E : Extensions.{uO, uH, uE} Hom} {codes : Codes Tm C Z}

/-- The firings with the use, the extension, the opening and the made row identities of a given one,
and its choice of made rule identities, installed codes, removed occurrences and published codes. -/
def RFiring.sameChoice {s : RState Tm O R C Z} (f g : RFiring O R E codes s) : Prop :=
  g.use = f.use ∧ HEq g.ext f.ext ∧ HEq g.opening f.opening ∧
    g.selection.made = f.selection.made ∧ g.madeRules = f.madeRules ∧
    g.installed = f.installed ∧ g.removedRules = f.removedRules ∧ g.published = f.published

variable (X : Frames Tm Hom) [DecidableEq O]

/-- **Finitely many selections**: at a finite store, the admitted firings with one use, extension,
opening and choice of made identities, installed codes, removed occurrences and published codes
form a finite set. -/
theorem RFiring.selections_finite {s : RState Tm O R C Z} (f : RFiring O R E codes s)
    (ambient : Set C) :
    {g : RFiring O R E codes s | f.sameChoice g ∧ g.Admits X ambient}.Finite := by
  classical
  have bounded : ∀ n, {l : List O | l.length = n ∧ ∀ o ∈ l, o ∈ s.present}.Finite := fun n =>
    LogicOverTheStep.ProgramAdequacy.listsOver_finite s.present n
  let seenSets : Set (List (Finset O)) :=
    {l | l.length = f.spec.collect.length ∧ ∀ x ∈ l, x ∈ s.present.powerset}
  have seenFinite : seenSets.Finite := by
    have := (List.finite_length_eq (s.present.powerset) f.spec.collect.length)
    refine (this.image (List.map Subtype.val)).subset ?_
    rintro l ⟨length, inside⟩
    refine ⟨l.attach.map fun x => ⟨x.1, inside x.1 x.2⟩, by simp [length], ?_⟩
    simp
  let key : RFiring O R E codes s → List O × List O × List (Finset O) :=
    fun g => (g.selection.taken, g.selection.read, g.seen)
  have injective : Set.InjOn key {g | f.sameChoice g ∧ g.Admits X ambient} := by
    rintro ⟨u, x, ι, ⟨taken, read, made⟩, seen, madeR, inst, rem, pub⟩
      ⟨⟨rfl, hx, hι, hmade, hmadeR, hinst, hrem, hpub⟩, -⟩
      ⟨u', x', ι', ⟨taken', read', made'⟩, seen', madeR', inst', rem', pub'⟩
      ⟨⟨rfl, hx', hι', hmade', hmadeR', hinst', hrem', hpub'⟩, -⟩ same
    have keys : (taken, read, seen) = (taken', read', seen') := same
    obtain ⟨rfl, rest⟩ := Prod.mk.inj keys
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
    have m : made = f.selection.made := hmade
    have m' : made' = f.selection.made := hmade'
    have r : madeR = f.madeRules := hmadeR
    have r' : madeR' = f.madeRules := hmadeR'
    have i : inst = f.installed := hinst
    have i' : inst' = f.installed := hinst'
    have d : rem = f.removedRules := hrem
    have d' : rem' = f.removedRules := hrem'
    have p : pub = f.published := hpub
    have p' : pub' = f.published := hpub'
    subst m m' r r' i i' d d' p p'
    have ex : HEq x f.ext := hx
    have ex' : HEq x' f.ext := hx'
    have sameExt : x = x' := eq_of_heq (ex.trans ex'.symm)
    subst sameExt
    have op : HEq ι f.opening := hι
    have op' : HEq ι' f.opening := hι'
    have sameOpening : ι = ι' := eq_of_heq (op.trans op'.symm)
    subst sameOpening
    rfl
  refine Set.Finite.of_finite_image ?_ injective
  refine (((bounded f.spec.body.take.length).prod
    ((bounded f.spec.body.read.length).prod seenFinite))).subset ?_
  rintro ⟨taken, read, seen⟩ ⟨g, ⟨⟨use, -⟩, admitted⟩, image⟩
  have keys : (g.selection.taken, g.selection.read, g.seen) = (taken, read, seen) := image
  obtain ⟨rfl, rest⟩ := Prod.mk.inj keys
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
  obtain ⟨⟨-, ⟨-, -, take, readLength, -, collect⟩, -⟩, enabled, ⟨b, σ, solved⟩, asks⟩ := admitted
  have spec : g.spec = f.spec := by
    show codes.unfold (s.codeOf g.use) = codes.unfold (s.codeOf f.use)
    rw [use]
  have takenPresent : ∀ o ∈ g.selection.taken, o ∈ s.present := fun o member =>
    enabled.taken_subset (List.mem_toFinset.mpr member)
  have readPresent : ∀ o ∈ g.selection.read, o ∈ s.present := fun o member =>
    enabled.kept_subset (List.mem_toFinset.mpr member)
  have seenPresent : ∀ seenSet ∈ g.seen, seenSet ∈ s.present.powerset := by
    intro seenSet member
    have lengths : (g.base.collectOpened X).length = g.seen.length := by
      rw [← collect]
      exact List.length_map _
    obtain ⟨p, paired⟩ := exists_mem_zip_right _ _ lengths seenSet member
    have sees : matchesAt X σ (g.base.row X s.toState) s.present p = seenSet :=
      (asks b σ solved).1.2 _ paired
    rw [Finset.mem_powerset, ← sees]
    intro o inside
    exact ((mem_matchesAt X σ (g.base.row X s.toState) s.present p o).mp inside).1
  have takeLength : g.selection.taken.length = f.spec.body.take.length := by rw [← take, spec]
  have readLength' : g.selection.read.length = f.spec.body.read.length := by
    rw [← readLength, spec]
  have seenLength : g.seen.length = f.spec.collect.length := by rw [← collect, spec]
  exact ⟨⟨takeLength, takenPresent⟩, ⟨readLength', readPresent⟩, seenLength, seenPresent⟩

#print axioms RFiring.selections_finite

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences
