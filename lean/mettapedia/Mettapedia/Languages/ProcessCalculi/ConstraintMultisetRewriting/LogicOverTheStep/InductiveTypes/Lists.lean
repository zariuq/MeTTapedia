import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InductiveTypes.Numbers

/-!
# Lists of numbers on the step: a type whose constructors read another type's region

The list constructors (`lstRules`) read rows of the number region: `cons` reads `natRow x` and
`lstRow l` and makes `lstRow (consE x l)`. Their premises lie outside the list region, so the lists
are a type only together with the numbers: the region is both handles (`inLists`), the constructors
both sets (`listRules`).

* **What the region holds** (`listRules_generated_iff`): the rows of the numerals and the rows of the
  lists of numerals. **Adding the lists is conservative over the numbers**
  (`natRow_generated_conservative`): the list constructors make no number row.
* **Two writers, one per region** (`listSystem`): the number owner writes `num`, the list writer
  writes `lst` and only reads `num`. Together they write the union through its constructors, so
  membership holds on every run (`lists_membership`), with its induction principle
  (`lists_induction`), and together they reach every generated row (`lists_reach`). The list region
  alone is owned by the list writer, so every closure statement about list rows survives the number
  owner (`lists_closure`), though the numbers the lists read are written by that other party.
* **Facts compose along reads** (`junkLists_breaks_membership`): with a number writer that does not
  follow the number constructors and the same list writer, which follows the list constructors, a
  run from the empty store reaches `lstRow (consE junkE nilE)`, a list row that is not generated, and
  the property "is the row of a numeral or of a list of numerals", closed under the constructors
  (`isListRow_ruleClosed`), fails on it. A list writer's discipline does not protect the lists; the
  discipline must hold at every region the constructors read.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InductiveTypes

open WhenTypesApply.ThatsAll
open NamesOnTheStep NamesOnTheStep.IssuingControls
open MeTTaCalculus.InteractionTypes (Rights Facet)

namespace Lists

/-- The region of lists of numbers: the numbers and the lists. -/
abbrev inLists : Handle → Prop := fun n => n = .num ∨ n = .lst

/-- The constructors of lists of numbers, with those of the numbers they read. -/
def listRules : Set (List Expr × Expr) := natRules ∪ lstRules

theorem mem_lstRules {ps : List Expr} {r : Expr} :
    (ps, r) ∈ lstRules ↔
      (ps = [] ∧ r = lstRow nilE) ∨ ∃ x l, ps = [natRow x, lstRow l] ∧ r = lstRow (consE x l) := by
  simp [lstRules]

theorem nil_mem : (([] : List Expr), lstRow nilE) ∈ listRules :=
  Or.inr (mem_lstRules.mpr (Or.inl ⟨rfl, rfl⟩))

theorem cons_mem (x l : Expr) : ([natRow x, lstRow l], lstRow (consE x l)) ∈ listRules :=
  Or.inr (mem_lstRules.mpr (Or.inr ⟨x, l, rfl, rfl⟩))

theorem natRow_ne_lstRow (x l : Expr) : natRow x ≠ lstRow l := by
  simp [natRow, lstRow]

theorem lstRow_injective {l l' : Expr} (same : lstRow l = lstRow l') : l = l' := by
  simp only [lstRow, Expr.app.injEq, true_and] at same
  exact same

theorem consE_injective {x l x' l' : Expr} (same : consE x l = consE x' l') : x = x' ∧ l = l' := by
  simp only [consE, Expr.app.injEq, true_and] at same
  exact same

/-- Rows of numerals and of lists of numerals. -/
def IsListRow (r : Expr) : Prop := (∃ k, r = natRow (numeral k)) ∨ ∃ ks, r = lstRow (listE ks)

/-- That property is closed under the constructors. -/
theorem isListRow_ruleClosed : RuleClosed listRules IsListRow := by
  intro ps r declared premises
  rcases declared with declared | declared
  · rcases Numbers.mem_natRules.mp declared with ⟨rfl, rfl⟩ | ⟨x, rfl, rfl⟩
    · exact Or.inl ⟨0, rfl⟩
    · rcases premises _ (List.mem_singleton_self _) with ⟨k, same⟩ | ⟨ks, same⟩
      · exact Or.inl ⟨k + 1, by rw [natRow_injective same]; rfl⟩
      · exact absurd same (natRow_ne_lstRow _ _)
  · rcases mem_lstRules.mp declared with ⟨rfl, rfl⟩ | ⟨x, l, rfl, rfl⟩
    · exact Or.inr ⟨[], rfl⟩
    · rcases premises (natRow x) (List.mem_cons_self ..) with ⟨k, sameX⟩ | ⟨ks, sameX⟩
      · rcases premises (lstRow l) (List.mem_cons_of_mem _ (List.mem_cons_self ..)) with
          ⟨j, sameL⟩ | ⟨ks, sameL⟩
        · exact absurd sameL.symm (natRow_ne_lstRow _ _)
        · refine Or.inr ⟨k :: ks, ?_⟩
          rw [natRow_injective sameX, lstRow_injective sameL]
          rfl
      · exact absurd sameX (natRow_ne_lstRow _ _)

/-- The rows of numerals and of lists of numerals are generated. -/
theorem listRow_generated {r : Expr} (row : IsListRow r) : Generated listRules ∅ r := by
  rcases row with ⟨k, rfl⟩ | ⟨ks, rfl⟩
  · exact WhenTypesApply.TwoKinds.generated_mono natRules ∅ Set.subset_union_left le_rfl
      (Numbers.numeral_generated k)
  · induction ks with
    | nil => exact Generated.rule nil_mem fun _ member => absurd member List.not_mem_nil
    | cons k ks ih =>
        refine Generated.rule (cons_mem (numeral k) (listE ks)) fun p member => ?_
        rcases List.mem_cons.mp member with rfl | member
        · exact WhenTypesApply.TwoKinds.generated_mono natRules ∅ Set.subset_union_left le_rfl
            (Numbers.numeral_generated k)
        · rw [List.mem_singleton.mp member]
          exact ih

/-- **The generated rows are the rows of numerals and of lists of numerals.** -/
theorem listRules_generated_iff {r : Expr} : Generated listRules ∅ r ↔ IsListRow r :=
  ⟨generated_induction isListRow_ruleClosed, listRow_generated⟩

/-- **The lists are conservative over the numbers**: a number row is generated with the lists exactly
when it is generated without them. -/
theorem natRow_generated_conservative (e : Expr) :
    Generated listRules ∅ (natRow e) ↔ Generated natRules ∅ (natRow e) := by
  rw [listRules_generated_iff, Numbers.natRules_generated_iff]
  constructor
  · rintro (found | ⟨ks, same⟩)
    · exact found
    · exact absurd same (natRow_ne_lstRow _ _)
  · exact Or.inl

/-! ## The parties -/

/-- Rights of the list writer: make and keep list rows, keep number rows. -/
def listRights : Rights Handle := fun n f =>
  (decide (n = .lst) && (decide (f = .send) || decide (f = .peek))) ||
    (decide (n = .num) && decide (f = .peek))

/-- **The list writer**: both list constructors. -/
def listWriter : SchemaPublicationAuthority.Process Schema Handle := ⟨listRights, [.nil, .cons]⟩

/-- The number owner (`true`) and the list writer. -/
def listSystem : Bool → SchemaPublicationAuthority.Process Schema Handle :=
  fun b => cond b Numbers.owner listWriter

/-- A number writer that does not follow the constructors (`true`) and the list writer. -/
def junkLists : Bool → SchemaPublicationAuthority.Process Schema Handle :=
  fun b => cond b Numbers.junkWriter listWriter

theorem owner_writes : Writes activate place inLists listRules Numbers.owner := by
  refine writes_of_each fun schema installed x ρ computed => Or.inl ?_
  simp only [Numbers.owner, List.mem_cons, List.not_mem_nil, or_false] at installed
  rcases installed with rfl | rfl
  · rcases x with _ | ⟨a, rest⟩
    · simp only [activate, Option.some.injEq] at computed
      exact ⟨_, Or.inl Numbers.zero_mem, computed.symm, fun _ member => absurd member List.not_mem_nil⟩
    · simp [activate] at computed
  · rcases x with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp [activate] at computed
    · simp only [activate, Option.some.injEq] at computed
      refine ⟨_, Or.inl (Numbers.succ_mem a), computed.symm, fun p member => ?_⟩
      rw [List.mem_singleton.mp member]
      exact Or.inl rfl
    · simp [activate] at computed

theorem listWriter_writes : Writes activate place inLists listRules listWriter := by
  refine writes_of_each fun schema installed x ρ computed => Or.inl ?_
  simp only [listWriter, List.mem_cons, List.not_mem_nil, or_false] at installed
  rcases installed with rfl | rfl
  · rcases x with _ | ⟨a, rest⟩
    · simp only [activate, Option.some.injEq] at computed
      exact ⟨_, nil_mem, computed.symm, fun _ member => absurd member List.not_mem_nil⟩
    · simp [activate] at computed
  · rcases x with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp [activate] at computed
    · simp [activate] at computed
    · simp only [activate, Option.some.injEq] at computed
      refine ⟨_, cons_mem a b, computed.symm, fun p member => ?_⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact Or.inl rfl
      · rw [List.mem_singleton.mp member]
        exact Or.inr rfl
    · simp [activate] at computed

theorem listSystem_writes (b : Bool) : Writes activate place inLists listRules (listSystem b) := by
  cases b
  · exact listWriter_writes
  · exact owner_writes

theorem listSystem_realizes : RealizeJointly activate place listRules listSystem := by
  intro d declared
  rcases declared with declared | declared
  · rcases Numbers.mem_natRules.mp declared with ⟨first, second⟩ | ⟨x, first, second⟩
    · have same : d = ([], natRow zeroE) := Prod.ext first second
      subst same
      exact ⟨true, rfl, .zero, List.mem_cons_self .., [], rfl⟩
    · have same : d = ([natRow x], natRow (succE x)) := Prod.ext first second
      subst same
      exact ⟨true, rfl, .succ, List.mem_cons_of_mem _ (List.mem_cons_self ..), [x], rfl⟩
  · rcases mem_lstRules.mp declared with ⟨first, second⟩ | ⟨x, l, first, second⟩
    · have same : d = ([], lstRow nilE) := Prod.ext first second
      subst same
      exact ⟨false, rfl, .nil, List.mem_cons_self .., [], rfl⟩
    · have same : d = ([natRow x, lstRow l], lstRow (consE x l)) := Prod.ext first second
      subst same
      exact ⟨false, rfl, .cons, List.mem_cons_of_mem _ (List.mem_cons_self ..), [x, l], rfl⟩

/-! ## The facts for lists of numbers -/

/-- **Membership for lists of numbers, with one writer per region.** -/
theorem lists_membership {C : Conf}
    (run : Relation.ReflTransGen (systemStep activate place listSystem) ProgramAdequacy.emptyStore C)
    {r : Expr} (present : r ∈ contents C) (inside : inLists (place r)) : IsListRow r :=
  listRules_generated_iff.mp
    (membership listSystem_writes run (closedBy_empty _ _) r present inside)

/-- **Every list of numerals is reached** from the empty store by the two writers. -/
theorem lists_reach (ks : List ℕ) :
    ∃ C, Relation.ReflTransGen (systemStep activate place listSystem) ProgramAdequacy.emptyStore C ∧
      lstRow (listE ks) ∈ contents C := by
  obtain ⟨C, run, -, present, -⟩ := reachable_of_generated_system listSystem_realizes
    (listRow_generated (Or.inr ⟨ks, rfl⟩)) _ plain_empty
  exact ⟨C, run, present⟩

/-- **Induction for lists of numbers**: a property that holds of the empty list and passes from a
list to the list with a numeral in front holds of the list of every list row of every state the two
writers reach. -/
theorem lists_induction (P : Expr → Prop) (nilCase : P nilE)
    (consCase : ∀ k l, P l → P (consE (numeral k) l)) {C : Conf}
    (run : Relation.ReflTransGen (systemStep activate place listSystem) ProgramAdequacy.emptyStore C)
    {l : Expr} (present : lstRow l ∈ contents C) : P l := by
  obtain ⟨k, same⟩ | ⟨ks, same⟩ := lists_membership run present (Or.inr rfl)
  · exact absurd same.symm (natRow_ne_lstRow _ _)
  · rw [lstRow_injective same]
    clear same present
    induction ks with
    | nil => exact nilCase
    | cons k ks ih => exact consCase k (listE ks) ih

/-- **The list region is owned by the list writer**, though the numbers it reads are written by
another party: every closure statement about list rows survives the number owner's moves. -/
theorem lists_closure :
    ClosedReadingSurvives (fun actor => processStep activate place (listSystem actor)) contents
      (fun e => place e = .lst) false :=
  closure_of_soleSender (activate := activate) (place := place) (process := listSystem)
    (inType := fun n : Handle => n = Handle.lst) (k := false) fun actor other e atLst => by
    cases actor
    · exact absurd rfl other
    · show Numbers.writerRights (place e) .send = false
      rw [atLst]
      rfl

/-- The junk writer does not write the union through its constructors. -/
theorem junkWriter_not_writes : ¬ Writes activate place inLists listRules Numbers.junkWriter := by
  intro writes
  obtain ⟨ps, declared, _⟩ := writes .junk (List.mem_singleton_self _) [] _ rfl (natRow junkE)
    (List.mem_singleton_self _) (Or.inl rfl) rfl
  have generated : Generated listRules ∅ (natRow junkE) := Generated.rule declared fun p member => by
    rcases declared with declared | declared
    · rcases Numbers.mem_natRules.mp declared with ⟨_, same⟩ | ⟨x, _, same⟩
      · exact absurd (natRow_injective same) (Numbers.numeral_ne_junk 0).symm
      · exact absurd (natRow_injective same) (by simp [junkE, succE])
    · rcases mem_lstRules.mp declared with ⟨_, same⟩ | ⟨x, l, _, same⟩
      · exact absurd same (natRow_ne_lstRow _ _)
      · exact absurd same (natRow_ne_lstRow _ _)
  exact Numbers.junk_not_generated ((natRow_generated_conservative junkE).mp generated)

/-- **Facts compose along reads**: with a number writer that does not follow the number constructors,
the list writer, which follows the list constructors, makes a list row that is not generated, and
"is the row of a numeral or of a list of numerals", closed under the constructors, fails on it. -/
theorem junkLists_breaks_membership :
    ∃ C, Relation.ReflTransGen (systemStep activate place junkLists) ProgramAdequacy.emptyStore C ∧
      lstRow (consE junkE nilE) ∈ contents C ∧ inLists (place (lstRow (consE junkE nilE))) ∧
      ¬ IsListRow (lstRow (consE junkE nilE)) ∧ Writes activate place inLists listRules listWriter := by
  obtain ⟨C₁, moved₁, plain₁, exact₁⟩ :=
    ctor_fires (activate := activate) (place := place) (process := Numbers.junkWriter)
      (d := ([], natRow junkE)) rfl (List.mem_singleton_self _) (x := []) rfl plain_empty
      fun _ member => absurd member List.not_mem_nil
  obtain ⟨C₂, moved₂, plain₂, exact₂⟩ :=
    ctor_fires (activate := activate) (place := place) (process := listWriter)
      (d := ([], lstRow nilE)) rfl (List.mem_cons_self ..) (x := []) rfl plain₁
      fun _ member => absurd member List.not_mem_nil
  obtain ⟨C₃, moved₃, -, exact₃⟩ :=
    ctor_fires (activate := activate) (place := place) (process := listWriter)
      (d := ([natRow junkE, lstRow nilE], lstRow (consE junkE nilE))) rfl
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (x := [junkE, nilE]) rfl plain₂
      fun p member => by
        rcases List.mem_cons.mp member with rfl | member
        · rw [exact₂, exact₁]
          exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
        · rw [List.mem_singleton.mp member, exact₂]
          exact Set.mem_insert _ _
  refine ⟨C₃, ?_, by rw [exact₃]; exact Set.mem_insert _ _, Or.inr rfl, ?_, listWriter_writes⟩
  · exact ((Relation.ReflTransGen.single (⟨true, moved₁⟩ : systemStep activate place junkLists _ _)).tail
      ⟨false, moved₂⟩).tail ⟨false, moved₃⟩
  · rintro (⟨k, same⟩ | ⟨ks, same⟩)
    · exact natRow_ne_lstRow _ _ same.symm
    · have := lstRow_injective same
      cases ks with
      | nil => simp [listE, consE, nilE] at this
      | cons k ks =>
          have heads := (consE_injective this).1
          exact Numbers.numeral_ne_junk k heads.symm

end Lists

#print axioms Lists.isListRow_ruleClosed
#print axioms Lists.listRules_generated_iff
#print axioms Lists.natRow_generated_conservative
#print axioms Lists.listSystem_writes
#print axioms Lists.listSystem_realizes
#print axioms Lists.lists_membership
#print axioms Lists.lists_reach
#print axioms Lists.lists_induction
#print axioms Lists.lists_closure
#print axioms Lists.junkWriter_not_writes
#print axioms Lists.junkLists_breaks_membership

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InductiveTypes
