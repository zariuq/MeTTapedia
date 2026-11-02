import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationParts

/-!
# Components read canonically, renamed

A block of atoms is told by its pattern (`toPattern_injective`), and a named multiset by its canonical block
(`multisetOf_injective`). Every argument outside a named multiset is read by its canonical form
(`canonArgument_canonicalOf`), so reading a component again reads each part canonically (`recanon_apply`), and an
injective renaming reads two components alike exactly when it read them alike before (`recanon_rename_iff`), given
the canonical form below their size.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (liftIndex)

variable {block : ReplicationBlock}

/-! ## Renamings and patterns -/

/-- **An injective renaming tells patterns apart.** -/
theorem rename_injective {relabel : Nat → Nat} (injective : Function.Injective relabel) :
    Function.Injective (rename relabel) := by
  intro first second same
  have back := congrArg (rename (Function.invFun relabel)) same
  rw [rename_comp, rename_comp, Function.invFun_comp injective, rename_id, rename_id] at back
  exact back

theorem liftIndex_injective {relabel : Nat → Nat} (injective : Function.Injective relabel) (cutoff : Nat) :
    Function.Injective (liftIndex cutoff relabel) := by
  intro first second same
  unfold liftIndex at same
  split_ifs at same with firstBelow secondBelow secondBelow
  · exact same
  · omega
  · omega
  · have := injective (by omega : relabel (first - cutoff) = relabel (second - cutoff))
    omega

/-! ## Blocks of atoms told by their patterns -/

theorem body_injective {first second : List Pattern}
    (firstAtomic : ∀ component ∈ first, decompose block.toBlock component = Prenex.atom component)
    (secondAtomic : ∀ component ∈ second, decompose block.toBlock component = Prenex.atom component)
    (same : Prenex.body block.toBlock first = Prenex.body block.toBlock second) : first = second := by
  have firstBody := decompose_body (block := block.toBlock) firstAtomic
  have secondBody := decompose_body (block := block.toBlock) secondAtomic
  rw [same, secondBody] at firstBody
  exact (Prenex.mk.inj firstBody).2.symm

/-- **A restriction is never an atom.** -/
theorem not_restriction_of_atomic {component : Pattern}
    (atomic : decompose block.toBlock component = Prenex.atom component) (binder : Option String) (body : Pattern) :
    component ≠ .apply block.restrict [.lambda binder body] := by
  rintro rfl
  rw [decompose_restrict] at atomic
  have bodyMass := mass_decompose (block := block.toBlock) body
  unfold Prenex.close at atomic
  split_ifs at atomic with used
  · simp [Prenex.restrict, Prenex.atom] at atomic
  · simp only [Prenex.atom, Prenex.mk.injEq] at atomic
    obtain ⟨_, componentsIs⟩ := atomic
    have sizes := congrArg sizeList componentsIs
    rw [sizeList_map_rename] at sizes
    simp only [sizeList, size, Prenex.mass] at sizes bodyMass
    omega

/-- The bag of atoms is no restriction. -/
theorem body_not_restriction {components : List Pattern}
    (atomic : ∀ component ∈ components, decompose block.toBlock component = Prenex.atom component)
    (binder : Option String) (process : Pattern) :
    Prenex.body block.toBlock components ≠ .apply block.restrict [.lambda binder process] := by
  match components, atomic with
  | [], _ => simp [Prenex.body]
  | [component], atomic =>
      simp only [Prenex.body]
      exact not_restriction_of_atomic (atomic component (List.mem_singleton_self _)) binder process
  | _ :: _ :: _, _ => simp [Prenex.body]

/-- **A block of atoms is told by its pattern.** -/
theorem toPattern_injective {first second : Prenex} (firstAtomic : first.Atomic block.toBlock)
    (secondAtomic : second.Atomic block.toBlock)
    (same : Prenex.toPattern block.toBlock first = Prenex.toPattern block.toBlock second) : first = second := by
  obtain ⟨count, components⟩ := first
  obtain ⟨count', components'⟩ := second
  have firstAtoms : ∀ component ∈ components, decompose block.toBlock component = Prenex.atom component := firstAtomic
  have secondAtoms : ∀ component ∈ components', decompose block.toBlock component = Prenex.atom component :=
    secondAtomic
  simp only [Prenex.toPattern] at same
  clear firstAtomic secondAtomic
  induction count generalizing count' with
  | zero =>
      cases count' with
      | zero =>
          simp only [Prenex.restricts] at same
          rw [body_injective firstAtoms secondAtoms same]
      | succ count' =>
          simp only [Prenex.restricts] at same
          exact absurd same (body_not_restriction firstAtoms none _)
  | succ count recurse =>
      cases count' with
      | zero =>
          simp only [Prenex.restricts] at same
          exact absurd same.symm (body_not_restriction secondAtoms none _)
      | succ count' =>
          simp only [Prenex.restricts_succ, Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq, true_and,
            and_true] at same
          have inner := recurse count' same
          simp only [Prenex.mk.injEq] at inner ⊢
          exact ⟨by omega, inner.2⟩

/-- **A named multiset of atoms is told by its canonical block.** -/
theorem multisetOf_injective {first second : Prenex} (firstAtomic : first.Atomic block.toBlock)
    (secondAtomic : second.Atomic block.toBlock)
    (same : multisetOf block.toBlock first = multisetOf block.toBlock second) : first = second := by
  obtain ⟨count, components⟩ := first
  obtain ⟨count', components'⟩ := second
  have restrictionAtom : ∀ {count : Nat} {components : List Pattern}, 0 < count →
      decompose block.toBlock (Prenex.toPattern block.toBlock ⟨count, components⟩) ≠
        Prenex.atom (Prenex.toPattern block.toBlock ⟨count, components⟩) := by
    intro count components positive atomIs
    obtain ⟨smaller, rfl⟩ : ∃ smaller, count = smaller + 1 := ⟨count - 1, by omega⟩
    exact not_restriction_of_atomic atomIs none _ rfl
  unfold multisetOf at same
  simp only at same
  by_cases firstZero : count = 0 <;> by_cases secondZero : count' = 0
  · rw [if_pos firstZero, if_pos secondZero] at same
    simp only [Pattern.collection.injEq, true_and, and_true] at same
    simp only [Prenex.mk.injEq]
    exact ⟨by omega, same⟩
  · rw [if_pos firstZero, if_neg secondZero] at same
    simp only [Pattern.collection.injEq, true_and, and_true] at same
    subst same
    exact absurd (firstAtomic _ (List.mem_singleton_self _)) (restrictionAtom (Nat.pos_of_ne_zero secondZero))
  · rw [if_neg firstZero, if_pos secondZero] at same
    simp only [Pattern.collection.injEq, true_and, and_true] at same
    subst same
    exact absurd (secondAtomic _ (List.mem_singleton_self _)) (restrictionAtom (Nat.pos_of_ne_zero firstZero))
  · rw [if_neg firstZero, if_neg secondZero] at same
    simp only [Pattern.collection.injEq, true_and, and_true, List.cons.injEq] at same
    exact toPattern_injective firstAtomic secondAtomic same

/-! ## Blocks of patterns are blocks of atoms -/

section Atoms

variable {base : Block}

theorem atom_atomic {component : Pattern} (atomic : decompose base component = Prenex.atom component) :
    (decompose base component).Atomic base := by
  rw [atomic]
  intro other member
  simp only [Prenex.atom, List.mem_singleton] at member
  subst member
  exact atomic

mutual
  /-- **The block of a pattern is a block of atoms.** -/
  theorem decompose_atomic (pattern : Pattern) : (decompose base pattern).Atomic base := by
    by_cases isNil : pattern = .apply base.unit []
    · subst isNil
      rw [decompose_unit]
      intro other member
      simp [Prenex.nil] at member
    by_cases isRestriction : ∃ binder body, pattern = .apply base.restrict [.lambda binder body]
    · obtain ⟨binder, body, rfl⟩ := isRestriction
      rw [decompose_restrict]
      have inner := decompose_atomic body
      unfold Prenex.close
      split_ifs
      · exact inner
      · intro other member
        obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
        exact atomic_rename (inner original inOriginal) _
    by_cases isBag : ∃ elements, pattern = .collection .hashBag elements none
    · obtain ⟨elements, rfl⟩ := isBag
      rw [decompose_bag]
      exact decomposeList_atomic elements
    by_cases isEmptyCandidate : ∃ label argument, pattern = .apply label [argument] ∧ label ∈ base.emptyUnits
    · obtain ⟨label, argument, rfl, listed⟩ := isEmptyCandidate
      by_cases empty : label ∈ base.emptyUnits ∧ decompose base argument = Prenex.nil
      · rw [decompose_multiset (fun binder body equal => isRestriction ⟨binder, body, equal⟩), if_pos empty]
        intro other member
        simp [Prenex.nil] at member
      · exact atom_atomic (decompose_multiset_atom (fun binder body equal => isRestriction ⟨binder, body, equal⟩) empty)
    exact atom_atomic (decompose_atom isNil (fun binder body equal => isRestriction ⟨binder, body, equal⟩)
      (fun elements equal => isBag ⟨elements, equal⟩)
      (fun label argument equal listed => isEmptyCandidate ⟨label, argument, equal, listed⟩))
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem decomposeList_atomic (elements : List Pattern) : (decomposeList base elements).Atomic base := by
    match elements with
    | [] =>
        intro other member
        simp [decomposeList, Prenex.nil] at member
    | element :: elements =>
        rw [decomposeList]
        have first := decompose_atomic element
        have rest := decomposeList_atomic elements
        intro other member
        simp only [Prenex.par, List.mem_append, List.mem_map] at member
        rcases member with ⟨original, inOriginal, rfl⟩ | ⟨original, inOriginal, rfl⟩
        · rw [liftBVars_eq_rename]
          exact atomic_rename (first original inOriginal) _
        · rw [liftBVars_eq_rename]
          exact atomic_rename (rest original inOriginal) _
  termination_by sizeOf elements
  decreasing_by all_goals sizeOf_pattern_dec
end

theorem close_nil : (Prenex.nil).close = Prenex.nil := by
  unfold Prenex.close
  simp [Prenex.nil]

mutual
  /-- **A block without components is inaction.** -/
  theorem decompose_nil_of_empty (pattern : Pattern) :
      (decompose base pattern).components = [] → decompose base pattern = Prenex.nil := by
    by_cases isNil : pattern = .apply base.unit []
    · subst isNil
      intro _
      exact decompose_unit base
    by_cases isRestriction : ∃ binder body, pattern = .apply base.restrict [.lambda binder body]
    · obtain ⟨binder, body, rfl⟩ := isRestriction
      rw [decompose_restrict]
      intro empty
      have bodyEmpty : (decompose base body).components = [] := by
        unfold Prenex.close at empty
        split_ifs at empty
        · exact empty
        · simpa using empty
      rw [decompose_nil_of_empty body bodyEmpty, close_nil]
    by_cases isBag : ∃ elements, pattern = .collection .hashBag elements none
    · obtain ⟨elements, rfl⟩ := isBag
      rw [decompose_bag]
      exact decomposeList_nil_of_empty elements
    by_cases isEmptyCandidate : ∃ label argument, pattern = .apply label [argument] ∧ label ∈ base.emptyUnits
    · obtain ⟨label, argument, rfl, listed⟩ := isEmptyCandidate
      rw [decompose_multiset (fun binder body equal => isRestriction ⟨binder, body, equal⟩)]
      split_ifs
      · intro _
        rfl
      · intro empty
        simp [Prenex.atom] at empty
    rw [decompose_atom isNil (fun binder body equal => isRestriction ⟨binder, body, equal⟩)
      (fun elements equal => isBag ⟨elements, equal⟩)
      (fun label argument equal listed => isEmptyCandidate ⟨label, argument, equal, listed⟩)]
    intro empty
    simp [Prenex.atom] at empty
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem decomposeList_nil_of_empty (elements : List Pattern) :
      (decomposeList base elements).components = [] → decomposeList base elements = Prenex.nil := by
    match elements with
    | [] => intro _; rfl
    | element :: elements =>
        rw [decomposeList]
        intro empty
        simp only [Prenex.par, List.append_eq_nil_iff, List.map_eq_nil_iff] at empty
        rw [decompose_nil_of_empty element empty.1, decomposeList_nil_of_empty elements empty.2]
        rfl
  termination_by sizeOf elements
  decreasing_by all_goals sizeOf_pattern_dec
end

/-- **A closed bag is never an atom.** -/
theorem not_bag_of_atomic {component : Pattern} (atomic : decompose base component = Prenex.atom component)
    (elements : List Pattern) : component ≠ .collection .hashBag elements none := by
  rintro rfl
  rw [decompose_bag] at atomic
  have weight := mass_decomposeList (block := base) elements
  rw [atomic] at weight
  simp [Prenex.atom, Prenex.mass, sizeList, size] at weight

/-- Closing restrictions keeps a block's components, renamed. -/
theorem decompose_restricts_components {form : Prenex} (atomic : form.Atomic base) (nonempty : form.components ≠ []) :
    (decompose base (Prenex.toPattern base form)).components ≠ [] := by
  obtain ⟨count, components⟩ := form
  have atoms : ∀ component ∈ components, decompose base component = Prenex.atom component := atomic
  have nonempty' : components ≠ [] := nonempty
  clear atomic nonempty
  simp only [Prenex.toPattern]
  induction count with
  | zero =>
      simp only [Prenex.restricts]
      rw [decompose_body atoms]
      exact nonempty'
  | succ count recurse =>
      rw [Prenex.restricts_succ, decompose_restrict]
      unfold Prenex.close
      split_ifs
      · exact recurse
      · simpa using recurse

end Atoms

/-! ## Parts read canonically -/

theorem decompose_lambda (binder : Option String) (body : Pattern) :
    decompose block.toBlock (.lambda binder body) = Prenex.atom (.lambda binder body) :=
  decompose_atom (by simp) (fun _ _ equal => by cases equal) (fun _ equal => by cases equal)
    (fun _ _ equal => by cases equal)

theorem decompose_bvar (index : Nat) : decompose block.toBlock (.bvar index) = Prenex.atom (.bvar index) :=
  decompose_atom (by simp) (fun _ _ equal => by cases equal) (fun _ equal => by cases equal)
    (fun _ _ equal => by cases equal)

theorem decompose_fvar (name : String) : decompose block.toBlock (.fvar name) = Prenex.atom (.fvar name) :=
  decompose_atom (by simp) (fun _ _ equal => by cases equal) (fun _ equal => by cases equal)
    (fun _ _ equal => by cases equal)

theorem decompose_subst (body replacement : Pattern) :
    decompose block.toBlock (.subst body replacement) = Prenex.atom (.subst body replacement) :=
  decompose_atom (by simp) (fun _ _ equal => by cases equal) (fun _ equal => by cases equal)
    (fun _ _ equal => by cases equal)

theorem decompose_open (kind : CollType) (elements : List Pattern) (rest : String) :
    decompose block.toBlock (.collection kind elements (some rest)) =
      Prenex.atom (.collection kind elements (some rest)) :=
  decompose_atom (by simp) (fun _ _ equal => by cases equal) (fun _ equal => by cases equal)
    (fun _ _ equal => by cases equal)

/-- **An argument read through `canonArgument` is read by its canonical form.** -/
theorem canonArgument_canonicalOf (argument : Pattern) :
    canonArgument (canonicalOf block) argument = canonicalOf block argument := by
  cases argument with
  | lambda binder body =>
      rw [canonicalOf_atom (decompose_lambda binder body), recanon_lambda]
      rfl
  | bvar index =>
      rw [canonicalOf_atom (decompose_bvar index), recanon_bvar]
      rfl
  | fvar name =>
      rw [canonicalOf_atom (decompose_fvar name), recanon_fvar]
      rfl
  | subst body replacement =>
      rw [canonicalOf_atom (decompose_subst body replacement), recanon_subst]
      rfl
  | apply => rfl
  | multiLambda => rfl
  | collection => rfl

/-- **How a component's argument is read canonically**: the restriction's as written, a named multiset's as
`multisetPart`, any other by its canonical form. -/
def partOf (block : ReplicationBlock) (label : String) : Pattern → Pattern :=
  if label = block.restrict then id else if label ∈ block.multisets then multisetPart block else canonicalOf block

theorem recanon_apply (label : String) (arguments : List Pattern) :
    recanon block (.apply label arguments) = .apply label (arguments.map (partOf block label)) := by
  by_cases isRestrict : label = block.restrict
  · subst isRestrict
    rw [recanon_apply_restrict]
    simp only [partOf, if_true, List.map_id]
  by_cases listed : label ∈ block.multisets
  · rw [recanon_apply_multiset isRestrict listed]
    simp only [partOf, if_neg isRestrict, if_pos listed]
  · rw [recanon_apply_other isRestrict listed]
    simp only [partOf, if_neg isRestrict, if_neg listed]
    congr 1
    exact List.map_congr_left fun argument _ => canonArgument_canonicalOf argument

theorem map_eq_map_iff_of {α β : Type} {read read' : α → β} : ∀ {first second : List α},
    (∀ a ∈ first, ∀ b ∈ second, (read a = read b ↔ read' a = read' b)) →
      (first.map read = second.map read ↔ first.map read' = second.map read')
  | [], [], _ => by simp
  | [], _ :: _, _ => by simp
  | _ :: _, [], _ => by simp
  | a :: first, b :: second, same => by
      simp only [List.map_cons, List.cons.injEq]
      rw [same a List.mem_cons_self b List.mem_cons_self, map_eq_map_iff_of fun a' inFirst b' inSecond =>
        same a' (List.mem_cons_of_mem _ inFirst) b' (List.mem_cons_of_mem _ inSecond)]

theorem multisetOf_shape (base : Block) (form : Prenex) :
    ∃ elements, multisetOf base form = .collection .hashBag elements none := by
  unfold multisetOf
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- **A renaming reads named multiset arguments alike exactly when they were read alike**, given the canonical form
below their size and canonical blocks of atoms. -/
theorem multisetPart_rename_iff {bound : Nat} (below : Below block bound)
    (atomicBelow : ∀ pattern, size pattern < bound →
      (normal block (decompose block.toBlock pattern)).Atomic block.toBlock)
    {first second : Pattern} (firstSmall : size first < bound) (secondSmall : size second < bound)
    {relabel : Nat → Nat} (injective : Function.Injective relabel) :
    multisetPart block (rename relabel first) = multisetPart block (rename relabel second) ↔
      multisetPart block first = multisetPart block second := by
  -- open collections and substitutions are read by their canonical forms, others as multisets
  have special : ∀ pattern : Pattern, ((∃ kind elements rest, pattern = .collection kind elements (some rest)) ∨
      ∃ body replacement, pattern = .subst body replacement) →
      multisetPart block pattern = canonicalOf block pattern := by
    rintro pattern (⟨kind, elements, rest, rfl⟩ | ⟨body, replacement, rfl⟩)
    · rw [canonicalOf_atom (decompose_open kind elements rest), recanon_collection]
      rfl
    · rw [canonicalOf_atom (decompose_subst body replacement), recanon_subst]
      rfl
  have specialShape : ∀ pattern : Pattern, ((∃ kind elements rest, pattern = .collection kind elements (some rest)) ∨
      ∃ body replacement, pattern = .subst body replacement) →
      (∃ kind elements rest, multisetPart block pattern = .collection kind elements (some rest)) ∨
        ∃ body replacement, multisetPart block pattern = .subst body replacement := by
    rintro pattern (⟨kind, elements, rest, rfl⟩ | ⟨body, replacement, rfl⟩)
    · exact .inl ⟨kind, _, rest, rfl⟩
    · exact .inr ⟨body, replacement, rfl⟩
  have ordinary : ∀ pattern : Pattern, ¬ ((∃ kind elements rest, pattern = .collection kind elements (some rest)) ∨
      ∃ body replacement, pattern = .subst body replacement) →
      multisetPart block pattern = multisetOf block.toBlock (normal block (decompose block.toBlock pattern)) := by
    intro pattern notSpecial
    push Not at notSpecial
    exact multisetPart_other (fun kind elements rest => notSpecial.1 kind elements rest)
      (fun body replacement => notSpecial.2 body replacement)
  have renameSpecial : ∀ pattern : Pattern, ((∃ kind elements rest, rename relabel pattern =
      .collection kind elements (some rest)) ∨ ∃ body replacement, rename relabel pattern = .subst body replacement) ↔
      ((∃ kind elements rest, pattern = .collection kind elements (some rest)) ∨
        ∃ body replacement, pattern = .subst body replacement) := by
    intro pattern
    cases pattern with
    | collection kind elements rest =>
        rw [rename_collection]
        cases rest <;> simp
    | subst body replacement =>
        rw [rename_subst]
        simp
    | apply => simp [rename_apply]
    | bvar => simp [rename_bvar]
    | fvar => simp [rename_fvar]
    | lambda => simp [rename_lambda]
    | multiLambda => simp [rename_multiLambda]
  -- a special reading is never an ordinary one
  have apart : ∀ pattern pattern' : Pattern,
      ((∃ kind elements rest, pattern = .collection kind elements (some rest)) ∨
        ∃ body replacement, pattern = .subst body replacement) →
      ¬ ((∃ kind elements rest, pattern' = .collection kind elements (some rest)) ∨
        ∃ body replacement, pattern' = .subst body replacement) →
      multisetPart block pattern ≠ multisetPart block pattern' := by
    intro pattern pattern' isSpecial notSpecial same
    rw [ordinary pattern' notSpecial] at same
    obtain ⟨elements, shape⟩ := multisetOf_shape block.toBlock (normal block (decompose block.toBlock pattern'))
    rw [shape] at same
    rcases specialShape pattern isSpecial with ⟨kind, elements', rest, isOpen⟩ | ⟨body, replacement, isSubst⟩
    · rw [isOpen] at same
      simp at same
    · rw [isSubst] at same
      cases same
  have sizeRename : ∀ pattern : Pattern, size (rename relabel pattern) = size pattern := fun pattern =>
    size_rename pattern relabel
  by_cases firstSpecial : (∃ kind elements rest, first = .collection kind elements (some rest)) ∨
      ∃ body replacement, first = .subst body replacement <;>
    by_cases secondSpecial : (∃ kind elements rest, second = .collection kind elements (some rest)) ∨
      ∃ body replacement, second = .subst body replacement
  · rw [special _ ((renameSpecial first).mpr firstSpecial), special _ ((renameSpecial second).mpr secondSpecial),
      special _ firstSpecial, special _ secondSpecial]
    exact below.renamed first second firstSmall secondSmall relabel injective
  · exact iff_of_false (apart _ _ ((renameSpecial first).mpr firstSpecial)
      (fun holds => secondSpecial ((renameSpecial second).mp holds))) (apart _ _ firstSpecial secondSpecial)
  · exact iff_of_false (fun same => apart _ _ ((renameSpecial second).mpr secondSpecial)
      (fun holds => firstSpecial ((renameSpecial first).mp holds)) same.symm)
      (fun same => apart _ _ secondSpecial firstSpecial same.symm)
  · have firstRenamed : ¬ ((∃ kind elements rest, rename relabel first = .collection kind elements (some rest)) ∨
        ∃ body replacement, rename relabel first = .subst body replacement) :=
      fun holds => firstSpecial ((renameSpecial first).mp holds)
    have secondRenamed : ¬ ((∃ kind elements rest, rename relabel second = .collection kind elements (some rest)) ∨
        ∃ body replacement, rename relabel second = .subst body replacement) :=
      fun holds => secondSpecial ((renameSpecial second).mp holds)
    rw [ordinary _ firstRenamed, ordinary _ secondRenamed, ordinary _ firstSpecial, ordinary _ secondSpecial]
    have atomicOf : ∀ pattern : Pattern, size pattern < bound →
        (normal block (decompose block.toBlock pattern)).Atomic block.toBlock := atomicBelow
    have toCanonical : ∀ pattern pattern' : Pattern, size pattern < bound → size pattern' < bound →
        (multisetOf block.toBlock (normal block (decompose block.toBlock pattern)) =
          multisetOf block.toBlock (normal block (decompose block.toBlock pattern')) ↔
            canonicalOf block pattern = canonicalOf block pattern') := by
      intro pattern pattern' small small'
      constructor
      · intro same
        unfold canonicalOf
        rw [multisetOf_injective (atomicOf pattern small) (atomicOf pattern' small') same]
      · intro same
        rw [toPattern_injective (atomicOf pattern small) (atomicOf pattern' small') same]
    rw [toCanonical _ _ (by rw [sizeRename]; exact firstSmall) (by rw [sizeRename]; exact secondSmall),
      toCanonical _ _ firstSmall secondSmall]
    exact below.renamed first second firstSmall secondSmall relabel injective

/-- **A renaming reads two components alike exactly when they were read alike**, given the canonical form below
their size and canonical blocks of atoms. -/
theorem recanon_rename_iff {bound : Nat} (below : Below block bound)
    (atomicBelow : ∀ pattern, size pattern < bound →
      (normal block (decompose block.toBlock pattern)).Atomic block.toBlock)
    {first second : Pattern} (firstSmall : size first ≤ bound) (secondSmall : size second ≤ bound)
    {relabel : Nat → Nat} (injective : Function.Injective relabel) :
    recanon block (rename relabel first) = recanon block (rename relabel second) ↔
      recanon block first = recanon block second := by
  have partIff : ∀ (label : String) (a b : Pattern), size a < bound → size b < bound →
      (partOf block label (rename relabel a) = partOf block label (rename relabel b) ↔
        partOf block label a = partOf block label b) := by
    intro label a b aSmall bSmall
    unfold partOf
    split_ifs
    · exact (rename_injective injective).eq_iff
    · exact multisetPart_rename_iff below atomicBelow aSmall bSmall injective
    · exact below.renamed a b aSmall bSmall relabel injective
  cases first <;> cases second
  case apply.apply label arguments label' arguments' =>
    rw [rename_apply, rename_apply, recanon_apply, recanon_apply, recanon_apply, recanon_apply]
    simp only [Pattern.apply.injEq, List.map_map]
    refine and_congr_right fun sameLabel => ?_
    subst sameLabel
    exact map_eq_map_iff_of fun a aIn b bIn => partIff label a b
      (by have := size_lt_of_mem aIn; simp only [size] at firstSmall; omega)
      (by have := size_lt_of_mem bIn; simp only [size] at secondSmall; omega)
  case lambda.lambda binder body binder' body' =>
    rw [rename_lambda, rename_lambda, recanon_lambda, recanon_lambda, recanon_lambda, recanon_lambda]
    simp only [Pattern.lambda.injEq]
    refine and_congr_right fun _ => ?_
    simp only [size] at firstSmall secondSmall
    exact below.renamed body body' (by omega) (by omega) _ (liftIndex_injective injective 1)
  case multiLambda.multiLambda arity binders body arity' binders' body' =>
    rw [rename_multiLambda, rename_multiLambda, recanon_multiLambda, recanon_multiLambda, recanon_multiLambda,
      recanon_multiLambda]
    simp only [Pattern.multiLambda.injEq]
    constructor
    · rintro ⟨sameArity, sameBinders, sameBody⟩
      subst sameArity
      simp only [size] at firstSmall secondSmall
      exact ⟨rfl, sameBinders, (below.renamed body body' (by omega) (by omega) _
        (liftIndex_injective injective arity)).mp sameBody⟩
    · rintro ⟨sameArity, sameBinders, sameBody⟩
      subst sameArity
      simp only [size] at firstSmall secondSmall
      exact ⟨rfl, sameBinders, (below.renamed body body' (by omega) (by omega) _
        (liftIndex_injective injective arity)).mpr sameBody⟩
  case collection.collection kind elements rest kind' elements' rest' =>
    rw [rename_collection, rename_collection, recanon_collection, recanon_collection, recanon_collection,
      recanon_collection]
    simp only [Pattern.collection.injEq, List.map_map]
    refine and_congr_right fun _ => and_congr_left fun _ => ?_
    exact map_eq_map_iff_of fun a aIn b bIn => below.renamed a b
      (by have := size_lt_of_mem aIn; simp only [size] at firstSmall; omega)
      (by have := size_lt_of_mem bIn; simp only [size] at secondSmall; omega) relabel injective
  case bvar.bvar index index' =>
    rw [rename_bvar, rename_bvar, recanon_bvar, recanon_bvar, recanon_bvar, recanon_bvar]
    simp only [Pattern.bvar.injEq]
    exact injective.eq_iff
  case fvar.fvar name name' =>
    rfl
  case subst.subst body replacement body' replacement' =>
    rw [rename_subst, rename_subst, recanon_subst, recanon_subst, recanon_subst, recanon_subst]
    simp only [Pattern.subst.injEq]
    rw [(rename_injective (liftIndex_injective injective 1)).eq_iff, (rename_injective injective).eq_iff]
  all_goals simp [rename_apply, rename_lambda, rename_multiLambda, rename_collection, rename_subst, rename_bvar,
    rename_fvar, recanon_apply, recanon_lambda, recanon_multiLambda, recanon_collection, recanon_subst, recanon_bvar,
    recanon_fvar]

/-! ## Sizes and shapes of canonical blocks -/

/-- **What a block's pattern weighs and looks like**: its restrictions, its number of components, their weight, and
how many are replications. -/
def Prenex.summary (block : ReplicationBlock) (form : Prenex) : Nat × Nat × Nat × Nat :=
  (form.count, form.components.length, sizeList form.components,
    (form.components.filter (isReplicated block)).length)

theorem size_body_eq (base : Block) (components : List Pattern) :
    size (Prenex.body base components) = sizeList components + (if components.length = 1 then 0 else 1) := by
  match components with
  | [] => simp [Prenex.body, size, sizeList]
  | [component] => simp [Prenex.body, sizeList]
  | first :: second :: rest =>
      simp only [Prenex.body, size, List.length_cons]
      split_ifs with single
      · omega
      · rfl

theorem size_toPattern_eq (base : Block) (form : Prenex) :
    size (Prenex.toPattern base form) =
      2 * form.count + sizeList form.components + (if form.components.length = 1 then 0 else 1) := by
  obtain ⟨count, components⟩ := form
  simp only [Prenex.toPattern]
  induction count with
  | zero => simp only [Prenex.restricts, size_body_eq]; omega
  | succ count recurse =>
      rw [Prenex.restricts_succ]
      simp only [size, sizeList] at recurse ⊢
      omega

theorem size_multisetOf_eq (base : Block) (form : Prenex) :
    size (multisetOf base form) =
      if form.count = 0 then sizeList form.components + 1 else size (Prenex.toPattern base form) + 1 := by
  unfold multisetOf
  split_ifs <;> simp [size, sizeList]

theorem size_toPattern_of_summary {first second : Prenex} (same : first.summary block = second.summary block)
    (base : Block) : size (Prenex.toPattern base first) = size (Prenex.toPattern base second) := by
  simp only [Prenex.summary, Prod.mk.injEq] at same
  rw [size_toPattern_eq, size_toPattern_eq, same.1, same.2.1, same.2.2.1]

theorem size_multisetOf_of_summary {first second : Prenex} (same : first.summary block = second.summary block)
    (base : Block) : size (multisetOf base first) = size (multisetOf base second) := by
  rw [size_multisetOf_eq, size_multisetOf_eq, size_toPattern_of_summary same base]
  simp only [Prenex.summary, Prod.mk.injEq] at same
  rw [same.1, same.2.2.1]

theorem sizeList_map_congr {read read' : Pattern → Pattern} : ∀ {patterns : List Pattern},
    (∀ pattern ∈ patterns, size (read pattern) = size (read' pattern)) →
      sizeList (patterns.map read) = sizeList (patterns.map read')
  | [], _ => rfl
  | pattern :: patterns, same => by
      simp only [List.map_cons, sizeList]
      rw [same pattern List.mem_cons_self,
        sizeList_map_congr fun other member => same other (List.mem_cons_of_mem _ member)]

theorem isReplicated_recanon (component : Pattern) :
    isReplicated block (recanon block component) = isReplicated block component :=
  isReplicated_recanonWith _ component

/-- **A renamed component read again weighs what it weighed read again**, given the canonical form and the
summaries of canonical blocks below its size. -/
theorem recanon_rename_size {bound : Nat} (below : Below block bound)
    (summaryBelow : ∀ pattern, size pattern < bound → ∀ relabel, Function.Injective relabel →
      (normal block (decompose block.toBlock (rename relabel pattern))).summary block =
        (normal block (decompose block.toBlock pattern)).summary block)
    {component : Pattern} (small : size component ≤ bound) {relabel : Nat → Nat}
    (injective : Function.Injective relabel) :
    size (recanon block (rename relabel component)) = size (recanon block component) := by
  have partSize : ∀ (label : String) (argument : Pattern), size argument < bound →
      size (partOf block label (rename relabel argument)) = size (partOf block label argument) := by
    intro label argument argumentSmall
    unfold partOf
    split_ifs
    · exact size_rename argument relabel
    · by_cases special : (∃ kind elements rest, argument = .collection kind elements (some rest)) ∨
          ∃ body replacement, argument = .subst body replacement
      · rcases special with ⟨kind, elements, rest, rfl⟩ | ⟨body, replacement, rfl⟩
        · rw [rename_collection]
          simp only [multisetPart, size, List.map_map]
          congr 1
          exact sizeList_map_congr fun element member => below.sized element (by
            have := size_lt_of_mem member; simp only [size] at argumentSmall; omega) relabel injective
        · rw [rename_subst]
          simp only [multisetPart, size, size_rename]
      · push Not at special
        have special' : (∀ kind elements rest, rename relabel argument ≠ .collection kind elements (some rest)) ∧
            ∀ body replacement, rename relabel argument ≠ .subst body replacement := by
          constructor
          · intro kind elements rest same
            cases argument with
            | collection kind' elements' rest' =>
                rw [rename_collection] at same
                cases rest' with
                | none => simp at same
                | some rest' => exact special.1 kind' elements' rest' rfl
            | subst => simp [rename_subst] at same
            | apply => simp [rename_apply] at same
            | bvar => simp [rename_bvar] at same
            | fvar => simp [rename_fvar] at same
            | lambda => simp [rename_lambda] at same
            | multiLambda => simp [rename_multiLambda] at same
          · intro body replacement same
            cases argument with
            | subst body' replacement' => exact special.2 body' replacement' rfl
            | collection => simp [rename_collection] at same
            | apply => simp [rename_apply] at same
            | bvar => simp [rename_bvar] at same
            | fvar => simp [rename_fvar] at same
            | lambda => simp [rename_lambda] at same
            | multiLambda => simp [rename_multiLambda] at same
        rw [multisetPart_other special'.1 special'.2, multisetPart_other special.1 special.2]
        exact size_multisetOf_of_summary (summaryBelow argument argumentSmall relabel injective) _
    · exact below.sized argument argumentSmall relabel injective
  cases component with
  | apply label arguments =>
      rw [rename_apply, recanon_apply, recanon_apply]
      simp only [size, List.map_map]
      congr 1
      exact sizeList_map_congr fun argument member => partSize label argument (by
        have := size_lt_of_mem member; simp only [size] at small; omega)
  | lambda binder body =>
      rw [rename_lambda, recanon_lambda, recanon_lambda]
      simp only [size] at small ⊢
      rw [below.sized body (by omega) _ (liftIndex_injective injective 1)]
  | multiLambda arity binders body =>
      rw [rename_multiLambda, recanon_multiLambda, recanon_multiLambda]
      simp only [size] at small ⊢
      rw [below.sized body (by omega) _ (liftIndex_injective injective arity)]
  | collection kind elements rest =>
      rw [rename_collection, recanon_collection, recanon_collection]
      simp only [size, List.map_map]
      congr 1
      exact sizeList_map_congr fun element member => below.sized element (by
        have := size_lt_of_mem member; simp only [size] at small; omega) relabel injective
  | bvar index => rfl
  | fvar name => rfl
  | subst body replacement =>
      rw [rename_subst, recanon_subst, recanon_subst]
      simp only [size, size_rename]

/-- **Every reading of some components, through an injective renaming, has one summary**: that of reading again
the components kept when one of each replicated component read again is kept. -/
theorem reading_summary {bound : Nat} (below : Below block bound)
    (atomicBelow : ∀ pattern, size pattern < bound →
      (normal block (decompose block.toBlock pattern)).Atomic block.toBlock)
    (summaryBelow : ∀ pattern, size pattern < bound → ∀ relabel, Function.Injective relabel →
      (normal block (decompose block.toBlock (rename relabel pattern))).summary block =
        (normal block (decompose block.toBlock pattern)).summary block)
    {components : List Pattern} (small : ∀ component ∈ components, size component ≤ bound)
    {relabel : Nat → Nat} (injective : Function.Injective relabel) :
    (dedupReplicated block (sortComponents (components.map fun component => recanon block (rename relabel component)))).length =
        ((dedupBy block (recanon block) components).map (recanon block)).length ∧
      sizeList (dedupReplicated block (sortComponents (components.map fun component =>
          recanon block (rename relabel component)))) =
        sizeList ((dedupBy block (recanon block) components).map (recanon block)) ∧
      ((dedupReplicated block (sortComponents (components.map fun component =>
          recanon block (rename relabel component)))).filter (isReplicated block)).length =
        (((dedupBy block (recanon block) components).map (recanon block)).filter (isReplicated block)).length := by
  set read := fun component => recanon block (rename relabel component) with readIs
  have sameKept : dedupBy block read components = dedupBy block (recanon block) components := by
    refine dedupBy_same components (fun first inFirst second inSecond => ?_) (fun component _ => ?_)
    · exact recanon_rename_iff below atomicBelow (small first inFirst) (small second inSecond) injective
    · simp only [readIs, isReplicated_recanon, isReplicated_rename]
  have permutation : (dedupReplicated block (sortComponents (components.map read))).Perm
      ((dedupBy block (recanon block) components).map read) := by
    rw [← sameKept, dedupBy_map]
    exact content_perm _
  have keptSmall : ∀ component ∈ dedupBy block (recanon block) components, size component ≤ bound :=
    fun component member => small component (dedupBy_subset _ components component member)
  refine ⟨?_, ?_, ?_⟩
  · rw [permutation.length_eq, List.length_map, List.length_map]
  · rw [sizeList_perm permutation]
    exact sizeList_map_congr fun component member =>
      recanon_rename_size below (fun pattern small' => summaryBelow pattern small') (keptSmall component member)
        injective
  · rw [(permutation.filter _).length_eq, List.filter_map, List.filter_map, List.length_map, List.length_map]
    congr 1
    apply List.filter_congr
    intro component _
    simp only [Function.comp_apply, readIs, isReplicated_recanon, isReplicated_rename]

/-! ## Reading again keeps atoms -/

theorem decompose_multiLambda (arity : Nat) (binders : List String) (body : Pattern) :
    decompose block.toBlock (.multiLambda arity binders body) = Prenex.atom (.multiLambda arity binders body) :=
  decompose_atom (by simp) (fun _ _ equal => by cases equal) (fun _ equal => by cases equal)
    (fun _ _ equal => by cases equal)

/-- Open collections and substitutions in a named multiset are read by their canonical forms. -/
theorem multisetPart_special {pattern : Pattern}
    (special : (∃ kind elements rest, pattern = .collection kind elements (some rest)) ∨
      ∃ body replacement, pattern = .subst body replacement) :
    multisetPart block pattern = canonicalOf block pattern := by
  rcases special with ⟨kind, elements, rest, rfl⟩ | ⟨body, replacement, rfl⟩
  · rw [canonicalOf_atom (decompose_open kind elements rest), recanon_collection]
    rfl
  · rw [canonicalOf_atom (decompose_subst body replacement), recanon_subst]
    rfl

/-- **A part read canonically is inaction only when it was**, given canonical blocks of atoms that stay nonempty
below its size. -/
theorem partOf_nil {bound : Nat}
    (atomicBelow : ∀ pattern, size pattern < bound →
      (normal block (decompose block.toBlock pattern)).Atomic block.toBlock)
    (nonEmptyBelow : ∀ pattern, size pattern < bound → (decompose block.toBlock pattern).components ≠ [] →
      (normal block (decompose block.toBlock pattern)).components ≠ [])
    {label : String} (notRestrict : label ≠ block.restrict) {argument : Pattern} (small : size argument < bound)
    (empty : decompose block.toBlock (partOf block label argument) = Prenex.nil) :
    decompose block.toBlock argument = Prenex.nil := by
  have canonicalCase : decompose block.toBlock (canonicalOf block argument) = Prenex.nil →
      decompose block.toBlock argument = Prenex.nil := by
    intro emptyCanonical
    apply decompose_nil_of_empty
    by_contra nonempty
    have stays := decompose_restricts_components (atomicBelow argument small) (nonEmptyBelow argument small nonempty)
    unfold canonicalOf at emptyCanonical
    rw [emptyCanonical] at stays
    exact stays rfl
  unfold partOf at empty
  rw [if_neg notRestrict] at empty
  split_ifs at empty with listed
  · by_cases special : (∃ kind elements rest, argument = .collection kind elements (some rest)) ∨
        ∃ body replacement, argument = .subst body replacement
    · rw [multisetPart_special special] at empty
      exact canonicalCase empty
    · push Not at special
      rw [multisetPart_other special.1 special.2] at empty
      apply decompose_nil_of_empty
      by_contra nonempty
      have normalNonempty := nonEmptyBelow argument small nonempty
      have normalAtomic := atomicBelow argument small
      revert empty
      unfold multisetOf
      split_ifs
      · rw [decompose_bag, decomposeList_atoms normalAtomic]
        intro emptyBag
        simp only [Prenex.nil, Prenex.mk.injEq] at emptyBag
        exact normalNonempty emptyBag.2
      · rw [decompose_bag, decomposeList, decomposeList]
        intro emptyBag
        have stays := decompose_restricts_components normalAtomic normalNonempty
        simp only [Prenex.par, Prenex.nil, Prenex.mk.injEq, List.append_eq_nil_iff, List.map_eq_nil_iff] at emptyBag
        exact stays emptyBag.2.1
  · exact canonicalCase empty

/-- **Reading a component again keeps it an atom**, given canonical blocks of atoms that stay nonempty below its
size. -/
theorem recanon_atomic {bound : Nat}
    (atomicBelow : ∀ pattern, size pattern < bound →
      (normal block (decompose block.toBlock pattern)).Atomic block.toBlock)
    (nonEmptyBelow : ∀ pattern, size pattern < bound → (decompose block.toBlock pattern).components ≠ [] →
      (normal block (decompose block.toBlock pattern)).components ≠ [])
    {component : Pattern} (small : size component ≤ bound)
    (atomic : decompose block.toBlock component = Prenex.atom component) :
    decompose block.toBlock (recanon block component) = Prenex.atom (recanon block component) := by
  cases component with
  | apply label arguments =>
      rw [recanon_apply]
      by_cases isRestrict : label = block.restrict
      · subst isRestrict
        simp only [partOf, if_true, List.map_id]
        exact atomic
      have notRestriction : ∀ binder body, Pattern.apply label (arguments.map (partOf block label)) ≠
          .apply block.restrict [.lambda binder body] := fun _ _ equal => isRestrict (Pattern.apply.inj equal).1
      rcases arguments with _ | ⟨argument, _ | ⟨second, rest⟩⟩
      · have notUnit : label ≠ block.unit := by
          intro same
          subst same
          rw [decompose_unit] at atomic
          simp [Prenex.nil, Prenex.atom] at atomic
        exact decompose_atom (by simpa using notUnit) notRestriction (by simp) (by simp)
      · refine decompose_multiset_atom notRestriction ?_
        rintro ⟨listed, empty⟩
        have argumentSmall : size argument < bound := by
          simp only [size, sizeList] at small
          omega
        have argumentEmpty := partOf_nil atomicBelow nonEmptyBelow isRestrict argumentSmall empty
        have emptyComponent : decompose block.toBlock (.apply label [argument]) = Prenex.nil := by
          rw [decompose_multiset (fun binder body equal => isRestrict (Pattern.apply.inj equal).1),
            if_pos ⟨listed, argumentEmpty⟩]
        rw [emptyComponent] at atomic
        simp [Prenex.nil, Prenex.atom] at atomic
      · exact decompose_atom (by simp) notRestriction (by simp) (fun _ _ equal => by simp at equal)
  | lambda binder body =>
      rw [recanon_lambda]
      exact decompose_lambda _ _
  | multiLambda arity binders body =>
      rw [recanon_multiLambda]
      exact decompose_multiLambda _ _ _
  | collection kind elements rest =>
      rw [recanon_collection]
      have notBag : ¬ (kind = .hashBag ∧ rest = none) := by
        rintro ⟨rfl, rfl⟩
        exact not_bag_of_atomic atomic elements rfl
      exact decompose_atom (by simp) (fun _ _ equal => by cases equal)
        (fun _ equal => by
          simp only [Pattern.collection.injEq] at equal
          exact notBag ⟨equal.1, equal.2.2⟩)
        (fun _ _ equal => by cases equal)
  | bvar index =>
      rw [recanon_bvar]
      exact atomic
  | fvar name =>
      rw [recanon_fvar]
      exact atomic
  | subst body replacement =>
      rw [recanon_subst]
      exact atomic

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks






