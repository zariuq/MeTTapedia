import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Substitution

/-!
# Steps through the canonical form, for calculi whose steps are reactions

In many calculi with restriction a step is a **reaction**: some components of a block, standing side by side under
the block's restrictions, are replaced by what they leave (`Reactions`). In the π-calculus the components are a
listener and an output on one channel; in CCS an action and its co-action; in the ambient calculus an ambient and
a capability. A step then reaches a block with a redex at its front (`StepBlockAt`), and the block's canonical form
steps too: the canonical components hold the redex with canonical parts, and their contractum has the canonical
form of the original contractum (`block_simulation`, `simulation`).

A calculus supplies its redexes with:

- their parts and what they leave, both renamed with the redex, the parts not blocks themselves;
- typing and objecthood of what they leave, and the variables it uses, among those of the parts;
- a redex with canonical parts, leaving what the original leaves up to the static theory;
- a reaction in any bag that holds the parts, and steps under a restriction.

Steps inside a bag and under a restriction keep a block with a redex at its front (`StepBlockAt.inBag`,
`StepBlockAt.restrict`), so a calculus whose steps are reactions with these congruences reaches such blocks; a redex
of one component that is the whole process is such a block too (`StepBlockAt.single`). The canonical argument of a
named multiset of atoms is its members with canonical parts, sorted (`canonMultisetWith_atoms`), which locates a
selected member of a canonical multiset.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Prenex
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution (Assignment substitute lift single substituteList_eq_map
  substitute_single_eq_instantiateBVar)
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars instantiateBVar)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn freeIn_bvar freeIn_apply freeIn_lambda freeIn_multiLambda
  freeIn_subst freeIn_collection)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv DerivedInstance derivedInstance_equivalent
  equationEquiv_fill)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (isObjectPatternList_iff)

variable {language : LanguageDef} {block : Block}

/-! ## Free variables of a substitution -/

theorem freeIn_liftBVars {index arity : Nat} {pattern : Pattern} :
    FreeIn (index + arity) (liftBVars 0 arity pattern) ↔ FreeIn index pattern := by
  rw [liftBVars_eq_rename, freeIn_rename]
  constructor
  · rintro ⟨original, free, equal⟩
    simp only [shiftAbove] at equal
    split_ifs at equal
    · omega
    · rwa [show index = original by omega]
  · intro free
    exact ⟨index, free, by simp [shiftAbove]⟩

theorem freeIn_lift {index arity : Nat} {assignment : Assignment} {original : Nat}
    (free : FreeIn (index + arity) (lift arity assignment original)) :
    arity ≤ original ∧ FreeIn index (assignment (original - arity)) := by
  unfold Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift at free
  split_ifs at free with below
  · rw [freeIn_bvar] at free
    omega
  · exact ⟨by omega, freeIn_liftBVars.mp free⟩

/-- **The variables of a substitution** come from the images of the variables substituted. -/
theorem freeIn_substitute (pattern : Pattern) : ∀ {assignment : Assignment} {index : Nat},
    FreeIn index (substitute assignment pattern) → ∃ original, FreeIn original pattern ∧
      FreeIn index (assignment original) := by
  induction pattern using Pattern.inductionOn with
  | hbvar other => intro assignment index free; exact ⟨other, .bvar _, free⟩
  | hfvar => intro _ _ free; cases free
  | happly label arguments recurse =>
      intro assignment index free
      simp only [substitute, substituteList_eq_map, freeIn_apply, List.mem_map] at free
      obtain ⟨_, ⟨argument, member, rfl⟩, free⟩ := free
      obtain ⟨original, originalFree, image⟩ := recurse argument member free
      exact ⟨original, freeIn_apply.mpr ⟨argument, member, originalFree⟩, image⟩
  | hlambda binder body recurse =>
      intro assignment index free
      simp only [substitute, freeIn_lambda] at free
      obtain ⟨original, originalFree, image⟩ := recurse free
      obtain ⟨above, image⟩ := freeIn_lift image
      exact ⟨original - 1, freeIn_lambda.mpr (by rwa [show original - 1 + 1 = original by omega]), image⟩
  | hmultiLambda arity binders body recurse =>
      intro assignment index free
      simp only [substitute, freeIn_multiLambda] at free
      obtain ⟨original, originalFree, image⟩ := recurse free
      obtain ⟨above, image⟩ := freeIn_lift image
      exact ⟨original - arity, freeIn_multiLambda.mpr (by rwa [show original - arity + arity = original by omega]),
        image⟩
  | hsubst body replacement bodyRecurse replacementRecurse =>
      intro assignment index free
      simp only [substitute, freeIn_subst] at free
      rcases free with free | free
      · obtain ⟨original, originalFree, image⟩ := bodyRecurse free
        obtain ⟨above, image⟩ := freeIn_lift image
        exact ⟨original - 1, freeIn_subst.mpr (.inl (by rwa [show original - 1 + 1 = original by omega])), image⟩
      · obtain ⟨original, originalFree, image⟩ := replacementRecurse free
        exact ⟨original, freeIn_subst.mpr (.inr originalFree), image⟩
  | hcollection kind elements rest recurse =>
      intro assignment index free
      simp only [substitute, substituteList_eq_map, freeIn_collection, List.mem_map] at free
      obtain ⟨_, ⟨element, member, rfl⟩, free⟩ := free
      obtain ⟨original, originalFree, image⟩ := recurse element member free
      exact ⟨original, freeIn_collection.mpr ⟨element, member, originalFree⟩, image⟩

/-- A reception uses the variables its continuation uses past the received one, and the datum's. -/
theorem freeIn_instantiate {index : Nat} {datum body : Pattern} (free : FreeIn index (instantiateBVar datum body)) :
    FreeIn (index + 1) body ∨ FreeIn index datum := by
  rw [← substitute_single_eq_instantiateBVar] at free
  obtain ⟨original, originalFree, image⟩ := freeIn_substitute body free
  cases original with
  | zero => exact .inr image
  | succ original =>
      simp only [single, freeIn_bvar] at image
      subst image
      exact .inl originalFree

open Mettapedia.OSLF.MeTTaIL.CanonicalBags (liftIndex)

/-- Renaming commutes with receiving, the continuation renamed past its received variable. -/
theorem rename_instantiate (relabel : Nat → Nat) (datum body : Pattern) :
    rename relabel (instantiateBVar datum body) =
      instantiateBVar (rename relabel datum) (rename (liftIndex 1 relabel) body) := by
  rw [← substitute_single_eq_instantiateBVar, ← substitute_single_eq_instantiateBVar]
  simp only [rename]
  rw [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute_comp,
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute_comp]
  congr 1
  funext index
  cases index with
  | zero => simp [single, liftIndex, substitute]
  | succ index => simp [single, liftIndex, substitute]

/-! ## Objects -/

theorem isObject_restriction {label : String} {binder : Option String} {body : Pattern} :
    isObjectPattern (.apply label [.lambda binder body]) = isObjectPattern body := by
  simp [isObjectPattern, isObjectPatternList]

theorem isObject_bag {elements : List Pattern} :
    isObjectPattern (.collection .hashBag elements none) = true ↔ ∀ element ∈ elements, isObjectPattern element = true := by
  simp [isObjectPattern, isObjectPatternList_iff]

theorem bag_tail_none {kind : CollType} {elements : List Pattern} {tail : Option String}
    (object : isObjectPattern (.collection kind elements tail) = true) : tail = none := by
  simp only [isObjectPattern, Bool.and_eq_true, Option.isNone_iff_eq_none] at object
  exact object.1

theorem bag_objects {kind : CollType} {elements : List Pattern} {tail : Option String}
    (object : isObjectPattern (.collection kind elements tail) = true) :
    ∀ element ∈ elements, isObjectPattern element = true := by
  simp only [isObjectPattern, Bool.and_eq_true, isObjectPatternList_iff] at object
  exact object.2

theorem isObject_restricts : ∀ (count : Nat) (body : Pattern),
    isObjectPattern (Prenex.restricts block count body) = isObjectPattern body
  | 0, _ => rfl
  | count + 1, body => by rw [Prenex.restricts_succ, isObject_restriction, isObject_restricts count body]

theorem body_of_long {components : List Pattern} (long : 2 ≤ components.length) :
    Prenex.body block components = .collection .hashBag components none := by
  match components, long with
  | _ :: _ :: _, _ => rfl

theorem objects_of_decompose {pattern : Pattern} (object : isObjectPattern pattern = true) :
    ∀ component ∈ (decompose block pattern).components, isObjectPattern component = true := by
  rw [isObject_decompose, List.all_eq_true] at object
  exact object

/-! ## Reactions -/

/-- **The reactions of a calculus with restriction**, for its step relation: redexes, each some components of a
block that react, and what they leave. -/
structure Reactions (language : LanguageDef) (block : Block) (step : Pattern → Pattern → Prop) where
  /-- The redexes. -/
  Redex : Type
  /-- The components that react. -/
  parts : Redex → List Pattern
  /-- What they leave. -/
  result : Redex → List Pattern
  /-- Renaming a redex's variables. -/
  rename : (Nat → Nat) → Redex → Redex
  parts_rename : ∀ relabel redex, parts (rename relabel redex) = (parts redex).map (RestrictionBlocks.rename relabel)
  result_rename : ∀ relabel redex, result (rename relabel redex) = (result redex).map (RestrictionBlocks.rename relabel)
  /-- A part is no block of its own: not the unit, a restriction or a bag. -/
  atoms : ∀ redex, ∀ part ∈ parts redex, decompose block part = Prenex.atom part
  /-- **What a redex leaves are processes**, wherever its parts are. -/
  result_members : ∀ {free : FreeTypeContext} {bound : List TypeExpr} redex,
    Members language block free bound (parts redex) → Members language block free bound (result redex)
  result_objects : ∀ redex, (∀ part ∈ parts redex, isObjectPattern part = true) →
    ∀ element ∈ result redex, isObjectPattern element = true
  /-- **What a redex leaves uses only the variables of its parts.** -/
  freeIn_result : ∀ redex {index : Nat} {element : Pattern}, element ∈ result redex → FreeIn index element →
    ∃ part ∈ parts redex, FreeIn index part
  /-- **A redex with canonical parts**, leaving what the redex leaves, up to the static theory. -/
  canonical : ∀ {free : FreeTypeContext} {bound : List TypeExpr}, BaseContext free bound → ∀ (fuel : Nat) redex,
    Members language block free bound (parts redex) → (∀ part ∈ parts redex, isObjectPattern part = true) →
    ∃ redex', parts redex' = (parts redex).map (canonComponentWith block (fuel + 1)) ∧
      List.Forall₂ (EquationEquiv (engineBasePremises RelationEnv.empty) language) (result redex') (result redex)
  /-- **A redex reacts in any bag that holds its parts.** -/
  react : ∀ {free : FreeTypeContext} {bound : List TypeExpr} redex {components rest : List Pattern},
    components.Perm (parts redex ++ rest) → Members language block free bound components →
    (∀ component ∈ components, isObjectPattern component = true) →
    ∃ target, step (Prenex.body block components) target ∧
      EquationEquiv (engineBasePremises RelationEnv.empty) language target
        (.collection .hashBag (result redex ++ rest) none)
  /-- **Steps happen under a restriction.** -/
  restrict : ∀ {source target : Pattern}, step source target →
    step (.apply block.restrict [.lambda none source]) (.apply block.restrict [.lambda none target])

/-! ## Blocks with a redex at the front -/

section Blocks

variable [laws : BlockSignature language block]

omit laws in
theorem lift_members {free : FreeTypeContext} {bound : List TypeExpr} {elements : List Pattern} (count : Nat)
    (members : Members language block free bound elements) :
    Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound)
      (elements.map (liftBVars 0 count)) := by
  intro element member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  simpa using lift_typed (inner := []) (inserted := List.replicate count (TypeExpr.base block.name)) (outer := bound)
    (members original originalMember)

omit laws in
/-- A block of restrictions carries the static theory of its body. -/
theorem restricts_equation : ∀ (count : Nat) {first second : Pattern},
    EquationEquiv (engineBasePremises RelationEnv.empty) language first second →
      EquationEquiv (engineBasePremises RelationEnv.empty) language (Prenex.restricts block count first)
        (Prenex.restricts block count second)
  | 0, _, _, related => related
  | count + 1, _, _, related => by
      have inside := equationEquiv_fill (.apply block.restrict [] (.lambda none .hole) []) (restricts_equation count related)
      simp only [OneHoleContext.fill, List.nil_append] at inside
      exact inside

omit laws in
/-- Equivalent members make equivalent bags. -/
theorem collection_equation {first second : List Pattern}
    (related : List.Forall₂ (EquationEquiv (engineBasePremises RelationEnv.empty) language) first second) :
    ∀ pre, EquationEquiv (engineBasePremises RelationEnv.empty) language (.collection .hashBag (pre ++ first) none)
      (.collection .hashBag (pre ++ second) none) := by
  induction related with
  | nil => intro pre; exact .refl _
  | @cons head head' tail tail' here _ recurse =>
      intro pre
      have filled := equationEquiv_fill (.collection .hashBag pre .hole tail none) here
      simp only [OneHoleContext.fill] at filled
      have later := recurse (pre ++ [head'])
      simp only [List.append_assoc, List.singleton_append] at later
      exact .trans _ _ _ filled later

/-- **A bag beside a block of restrictions is one block**: the block's restrictions leave the bag and its members
join the others, which are lifted past the restrictions. -/
theorem bag_block_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {count : Nat} {inner others : List Pattern}
    (innerMembers : Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound) inner)
    (othersMembers : Members language block free bound others) :
    EquationEquiv (engineBasePremises RelationEnv.empty) language
      (.collection .hashBag (Prenex.restricts block count (.collection .hashBag inner none) :: others) none)
      (Prenex.restricts block count (.collection .hashBag (inner ++ others.map (liftBVars 0 count)) none)) := by
  have extruded := (extrusions_equivalent count (bag_typed (rest := none) innerMembers) othersMembers).toEquationEquiv
  have outer : Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound)
      (.collection .hashBag inner none :: others.map (liftBVars 0 count)) := by
    intro element member
    rcases List.mem_cons.mp member with rfl | lifted
    · exact bag_typed (rest := none) innerMembers
    · exact lift_members count othersMembers element lifted
  have flattened := laws.flatten (pre := []) (inner := inner) (post := others.map (liftBVars 0 count))
    (bag_typed (rest := none) outer)
  simp only [List.nil_append] at flattened
  exact .trans _ _ _ extruded (restricts_equation count (derivedInstance_equivalent flattened))

variable {step : Pattern → Pattern → Prop}

/-- **A reaction at the front of a block**: `count` restrictions over the reacting components and the rest, which a
source is equivalent to, while the target is equivalent to what the components leave beside the rest, under the same
restrictions. -/
structure ReactsAt (language : LanguageDef) (block : Block) (free : FreeTypeContext) (bound : List TypeExpr)
    (source target : Pattern) (count : Nat) (parts result rest : List Pattern) : Prop where
  members : Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound) (parts ++ rest)
  objects : ∀ element ∈ parts ++ rest, isObjectPattern element = true
  source : EquationEquiv (engineBasePremises RelationEnv.empty) language source
    (Prenex.restricts block count (.collection .hashBag (parts ++ rest) none))
  target : EquationEquiv (engineBasePremises RelationEnv.empty) language target
    (Prenex.restricts block count (.collection .hashBag (result ++ rest) none))

/-- **A block with a redex at its front**: its parts react at the front of the block, leaving what the redex
leaves. -/
abbrev StepBlockAt (reactions : Reactions language block step) (free : FreeTypeContext) (bound : List TypeExpr)
    (source target : Pattern) (count : Nat) (redex : reactions.Redex) (rest : List Pattern) : Prop :=
  ReactsAt language block free bound source target count (reactions.parts redex) (reactions.result redex) rest

/-- Some block with a redex at its front. -/
def StepBlock (reactions : Reactions language block step) (free : FreeTypeContext) (bound : List TypeExpr)
    (source target : Pattern) : Prop :=
  ∃ count redex rest, StepBlockAt reactions free bound source target count redex rest

omit laws in
/-- **A reaction between members of a bag** is a reaction at the front of a block, under no restriction. -/
theorem ReactsAt.ofPerm {free : FreeTypeContext} {bound : List TypeExpr} {elements parts result rest : List Pattern}
    {target : Pattern} (typed : HasType language free bound (.collection .hashBag elements none) (.base block.proc))
    (members : Members language block free bound elements)
    (objects : ∀ element ∈ elements, isObjectPattern element = true)
    (permutation : elements.Perm (parts ++ rest))
    (reached : EquationEquiv (engineBasePremises RelationEnv.empty) language target
      (.collection .hashBag (result ++ rest) none)) :
    ReactsAt language block free bound (.collection .hashBag elements none) target 0 parts result rest := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro element member
    simpa using members element (permutation.mem_iff.mpr member)
  · intro element member
    exact objects element (permutation.mem_iff.mpr member)
  · exact derivedInstance_equivalent (DerivedInstance.bagPerm_of_sorted ⟨free, bound, typed⟩ permutation)
  · exact reached

/-- **A step of a member of a bag** keeps a reaction at the front of a block, when what the components leave are
processes wherever they are: the other members join the rest, lifted past the block's restrictions. -/
theorem ReactsAt.inBag {free : FreeTypeContext} {bound : List TypeExpr} {elements : List Pattern} (position : Nat)
    (inside : position < elements.length) {target : Pattern} {count : Nat} {parts result rest : List Pattern}
    (results : Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound) parts →
      Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound) result)
    (typed : HasType language free bound (.collection .hashBag elements none) (.base block.proc))
    (objects : ∀ element ∈ elements, isObjectPattern element = true)
    (inner : ReactsAt language block free bound elements[position] target count parts result rest) :
    ReactsAt language block free bound (.collection .hashBag elements none)
      (.collection .hashBag (target :: elements.eraseIdx position) none) count parts result
      (rest ++ (elements.eraseIdx position).map (liftBVars 0 count)) := by
  have members := members_of_bag (block := block) typed
  have othersMembers : Members language block free bound (elements.eraseIdx position) := fun element member =>
    members element (List.mem_of_mem_eraseIdx member)
  have permutation := perm_getElem_eraseIdx elements position inside
  have resultMembers : Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound)
      (result ++ rest) := by
    intro element member
    rcases List.mem_append.mp member with inResult | inRest
    · exact results (fun part member => inner.members part (by simp [member])) element inResult
    · exact inner.members element (by simp [inRest])
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro element member
    rw [← List.append_assoc] at member
    rcases List.mem_append.mp member with front | lifted
    · exact inner.members element front
    · exact lift_members count othersMembers element lifted
  · intro element member
    rw [← List.append_assoc] at member
    rcases List.mem_append.mp member with front | lifted
    · exact inner.objects element front
    · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp lifted
      rw [isObject_liftBVars]
      exact objects original (List.mem_of_mem_eraseIdx originalMember)
  · have reordered := derivedInstance_equivalent (base := engineBasePremises RelationEnv.empty)
      (DerivedInstance.bagPerm_of_sorted ⟨free, bound, typed⟩ permutation)
    have filled := equationEquiv_fill (.collection .hashBag [] .hole (elements.eraseIdx position) none) inner.source
    simp only [OneHoleContext.fill, List.nil_append] at filled
    have joined := bag_block_equivalent inner.members othersMembers
    rw [List.append_assoc] at joined
    exact .trans _ _ _ reordered (.trans _ _ _ filled joined)
  · have filled := equationEquiv_fill (.collection .hashBag [] .hole (elements.eraseIdx position) none) inner.target
    simp only [OneHoleContext.fill, List.nil_append] at filled
    have joined := bag_block_equivalent resultMembers othersMembers
    rw [List.append_assoc] at joined
    exact .trans _ _ _ filled joined

/-- **A step of a member of a bag** keeps a block with a redex at its front. -/
theorem StepBlockAt.inBag {reactions : Reactions language block step} {free : FreeTypeContext}
    {bound : List TypeExpr} {elements : List Pattern} (position : Nat) (inside : position < elements.length)
    {target : Pattern} {count : Nat} {redex : reactions.Redex} {rest : List Pattern}
    (typed : HasType language free bound (.collection .hashBag elements none) (.base block.proc))
    (objects : ∀ element ∈ elements, isObjectPattern element = true)
    (inner : StepBlockAt reactions free bound elements[position] target count redex rest) :
    StepBlockAt reactions free bound (.collection .hashBag elements none)
      (.collection .hashBag (target :: elements.eraseIdx position) none) count redex
      (rest ++ (elements.eraseIdx position).map (liftBVars 0 count)) :=
  ReactsAt.inBag position inside (reactions.result_members redex) typed objects inner

omit laws in
/-- **A step under a restriction** keeps a reaction at the front of a block, with one more restriction. -/
theorem ReactsAt.restrict {free : FreeTypeContext} {bound : List TypeExpr} {source target : Pattern} {count : Nat}
    {parts result rest : List Pattern}
    (inner : ReactsAt language block free (.base block.name :: bound) source target count parts result rest) :
    ReactsAt language block free bound (.apply block.restrict [.lambda none source])
      (.apply block.restrict [.lambda none target]) (count + 1) parts result rest := by
  refine ⟨?_, inner.objects, ?_, ?_⟩
  · simpa [List.replicate_succ', List.append_assoc] using inner.members
  · have inside := equationEquiv_fill (.apply block.restrict [] (.lambda none .hole) []) inner.source
    simpa [OneHoleContext.fill, Prenex.restricts] using inside
  · have inside := equationEquiv_fill (.apply block.restrict [] (.lambda none .hole) []) inner.target
    simpa [OneHoleContext.fill, Prenex.restricts] using inside

omit laws in
/-- **A step under a restriction** keeps a block with a redex at its front, with one more restriction. -/
theorem StepBlockAt.restrict {reactions : Reactions language block step} {free : FreeTypeContext}
    {bound : List TypeExpr} {source target : Pattern} {count : Nat} {redex : reactions.Redex} {rest : List Pattern}
    (inner : StepBlockAt reactions free (.base block.name :: bound) source target count redex rest) :
    StepBlockAt reactions free bound (.apply block.restrict [.lambda none source])
      (.apply block.restrict [.lambda none target]) (count + 1) redex rest :=
  ReactsAt.restrict inner

end Blocks

/-! ## The block of a block with a redex at its front -/

theorem decompose_restricts : ∀ (count : Nat) (body : Pattern),
    decompose block (Prenex.restricts block count body) = Prenex.close^[count] (decompose block body)
  | 0, _ => rfl
  | count + 1, body => by
      rw [Prenex.restricts_succ, decompose_restrict, decompose_restricts count body, Function.iterate_succ_apply']

theorem map_liftBVars_zero (cutoff : Nat) (patterns : List Pattern) : patterns.map (liftBVars cutoff 0) = patterns := by
  conv_rhs => rw [← List.map_id patterns]
  exact List.map_congr_left fun pattern _ => Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero pattern cutoff

/-- **The block of a bag with some atoms at its front**: the atoms, lifted past the restrictions of the others'
block, then the others' components. -/
theorem decompose_front : ∀ (heads : List Pattern), (∀ head ∈ heads, decompose block head = Prenex.atom head) →
    ∀ (rest : List Pattern), decompose block (.collection .hashBag (heads ++ rest) none) =
      ⟨(decompose block (.collection .hashBag rest none)).count,
        heads.map (liftBVars 0 (decompose block (.collection .hashBag rest none)).count) ++
          (decompose block (.collection .hashBag rest none)).components⟩
  | [], _, rest => by simp
  | head :: heads, atoms, rest => by
      have later := decompose_front heads (fun head member => atoms head (List.mem_cons_of_mem _ member)) rest
      rw [decompose_bag] at later ⊢
      rw [List.cons_append, decomposeList, atoms head List.mem_cons_self, later]
      simp [Prenex.par, Prenex.atom, map_liftBVars_zero, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero]

theorem any_mentions_iff {index : Nat} {patterns : List Pattern} :
    patterns.any (mentions index) = true ↔ ∃ pattern ∈ patterns, FreeIn index pattern := by
  simp only [List.any_eq_true, mentions_iff]

/-- Variables used by some member of a list. -/
def UsedBy (index : Nat) (patterns : List Pattern) : Prop := ∃ pattern ∈ patterns, FreeIn index pattern

theorem usedBy_append {index : Nat} {first second : List Pattern} :
    UsedBy index (first ++ second) ↔ UsedBy index first ∨ UsedBy index second := by
  simp only [UsedBy, List.mem_append]
  constructor
  · rintro ⟨pattern, member | member, free⟩
    · exact .inl ⟨pattern, member, free⟩
    · exact .inr ⟨pattern, member, free⟩
  · rintro (⟨pattern, member, free⟩ | ⟨pattern, member, free⟩)
    · exact ⟨pattern, .inl member, free⟩
    · exact ⟨pattern, .inr member, free⟩

theorem usedBy_map_rename {index : Nat} {relabel : Nat → Nat} {patterns : List Pattern} :
    UsedBy index (patterns.map (rename relabel)) ↔ ∃ original, UsedBy original patterns ∧ relabel original = index := by
  simp only [UsedBy, List.mem_map]
  constructor
  · rintro ⟨_, ⟨pattern, member, rfl⟩, free⟩
    obtain ⟨original, originalFree, rfl⟩ := (freeIn_rename pattern).mp free
    exact ⟨original, ⟨pattern, member, originalFree⟩, rfl⟩
  · rintro ⟨original, ⟨pattern, member, free⟩, rfl⟩
    exact ⟨_, ⟨pattern, member, rfl⟩, (freeIn_rename pattern).mpr ⟨original, free, rfl⟩⟩

section Simulation

variable [laws : BlockLanguage language block]

/-- **A canonical argument of a sort is equivalent to the argument.** -/
theorem canonArgument_equivalent {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    (fuel : Nat) {argument : Pattern} {sort : String} (typed : HasType language free bound argument (.base sort)) :
    EquationEquiv (engineBasePremises RelationEnv.empty) language (canonArgument (canonWith block fuel) argument)
      argument := by
  cases argument with
  | lambda => cases typed
  | bvar => exact .refl _
  | fvar => exact .refl _
  | subst => exact .refl _
  | apply => exact .symm _ _ (canonWith_sound (block := block) fuel context typed).2.toEquationEquiv
  | multiLambda => cases typed
  | collection => exact .symm _ _ (canonWith_sound (block := block) fuel context typed).2.toEquationEquiv

/-- **Closing as a block with more used variables is closed**: the other block's restrictions are kept or dropped
in turn, and each dropped one is unused here too. -/
theorem closes_follow {free : FreeTypeContext} :
    ∀ (count : Nat) {bound : List TypeExpr} {inner : Nat} {heads heads' tail : List Pattern},
      (∀ index, UsedBy index heads' → UsedBy index heads) →
      Members language block free (List.replicate inner (TypeExpr.base block.name) ++
        (List.replicate count (TypeExpr.base block.name) ++ bound)) (heads' ++ tail) →
      ∃ (final : Nat) (relabel : Nat → Nat),
        Prenex.close^[count] ⟨inner, heads ++ tail⟩ = ⟨final, (heads ++ tail).map (rename relabel)⟩ ∧
        Members language block free (List.replicate final (TypeExpr.base block.name) ++ bound)
          ((heads' ++ tail).map (rename relabel)) ∧
        EquationEquiv (engineBasePremises RelationEnv.empty) language
          (Prenex.restricts block count ((Prenex.toPattern block) ⟨inner, heads' ++ tail⟩))
          ((Prenex.toPattern block) ⟨final, (heads' ++ tail).map (rename relabel)⟩)
  | 0, bound, inner, heads, heads', tail, _, members => by
      have identity : rename id = id := funext rename_id
      refine ⟨inner, id, ?_, ?_, ?_⟩
      · simp [identity]
      · simpa [identity] using members
      · simp only [identity, List.map_id, Prenex.restricts]
        exact .refl _
  | count + 1, bound, inner, heads, heads', tail, used, members => by
      have members' : Members language block free (List.replicate inner (TypeExpr.base block.name) ++
          (.base block.name :: (List.replicate count (TypeExpr.base block.name) ++ bound))) (heads' ++ tail) := by
        simpa [List.replicate_succ] using members
      by_cases kept : (heads ++ tail).any (mentions inner) = true
      · have closed : Prenex.close ⟨inner, heads ++ tail⟩ = ⟨inner + 1, heads ++ tail⟩ := by
          simp [Prenex.close, kept, Prenex.restrict]
        have liftedMembers : Members language block free (List.replicate (inner + 1) (TypeExpr.base block.name) ++
            (List.replicate count (TypeExpr.base block.name) ++ bound)) (heads' ++ tail) := by
          simpa [List.replicate_succ', List.append_assoc] using members'
        obtain ⟨final, relabel, iterated, finalMembers, equivalent⟩ := closes_follow count used liftedMembers
        refine ⟨final, relabel, ?_, finalMembers, ?_⟩
        · rw [Function.iterate_succ_apply, closed, iterated]
        · rw [← restricts_add count 1]
          exact equivalent
      · have unusedHeads : ¬ UsedBy inner (heads ++ tail) := fun usedHere =>
          kept (any_mentions_iff.mpr usedHere)
        have unused : ¬ (heads' ++ tail).any (mentions inner) = true := by
          rw [any_mentions_iff]
          intro usedThere
          rcases usedBy_append.mp usedThere with inHeads | inTail
          · exact unusedHeads (usedBy_append.mpr (.inl (used inner inHeads)))
          · exact unusedHeads (usedBy_append.mpr (.inr inTail))
        have closed : Prenex.close ⟨inner, heads ++ tail⟩ =
            ⟨inner, (heads ++ tail).map (rename (dropIndex inner))⟩ := by
          simp [Prenex.close, kept]
        have otherClosed : Prenex.close ⟨inner, heads' ++ tail⟩ =
            ⟨inner, (heads' ++ tail).map (rename (dropIndex inner))⟩ := by
          simp only [Prenex.close]
          rw [if_neg unused]
        obtain ⟨droppedMembers, dropped⟩ := close_sound (form := ⟨inner, heads' ++ tail⟩) members'
        rw [otherClosed] at droppedMembers dropped
        simp only [List.map_append] at droppedMembers dropped closed
        have used' : ∀ index, UsedBy index (heads'.map (rename (dropIndex inner))) →
            UsedBy index (heads.map (rename (dropIndex inner))) := by
          intro index usedThere
          obtain ⟨original, originalUsed, rfl⟩ := usedBy_map_rename.mp usedThere
          exact usedBy_map_rename.mpr ⟨original, used original originalUsed, rfl⟩
        obtain ⟨final, relabel, iterated, finalMembers, equivalent⟩ := closes_follow count used' droppedMembers
        refine ⟨final, relabel ∘ dropIndex inner, ?_, ?_, ?_⟩
        · rw [Function.iterate_succ_apply, closed, iterated]
          simp [List.map_map, Function.comp_def, rename_comp]
        · simpa [List.map_map, Function.comp_def, rename_comp] using finalMembers
        · rw [← restricts_add count 1]
          have inside := restricts_equation (block := block) count dropped.toEquationEquiv
          simp only [List.map_append, List.map_map, Function.comp_def, rename_comp] at equivalent ⊢
          exact .trans _ _ _ inside equivalent

/-- **A bag with some members in front is one block**: the front members lifted past the others' restrictions,
then the others' components. -/
theorem front_block_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {heads rest : List Pattern}
    (headsMembers : Members language block free bound heads) (restMembers : Members language block free bound rest) :
    EquationEquiv (engineBasePremises RelationEnv.empty) language (.collection .hashBag (heads ++ rest) none)
      ((Prenex.toPattern block) ⟨(decompose block (.collection .hashBag rest none)).count,
        heads.map (liftBVars 0 (decompose block (.collection .hashBag rest none)).count) ++
          (decompose block (.collection .hashBag rest none)).components⟩) := by
  obtain ⟨blockMembers, decomposed⟩ := decompose_sound (block := block) (bag_typed (rest := none) restMembers)
  generalize decompose block (.collection .hashBag rest none) = form at blockMembers decomposed ⊢
  have paired := (par_equivalent (first := ⟨0, heads⟩) (second := form) (by simpa using headsMembers)
    blockMembers).toEquationEquiv
  simp only [Prenex.par, Nat.zero_add, map_liftBVars_zero] at paired
  have split := Relation.EqvGen.symm _ _ (bag_pair_equivalent headsMembers restMembers).toEquationEquiv
  have firstBody := equationEquiv_fill (.collection .hashBag [] .hole [.collection .hashBag rest none] none)
    (bag_body_equivalent headsMembers).toEquationEquiv
  have secondBlock := equationEquiv_fill (.collection .hashBag [Prenex.body block heads] .hole [] none)
    decomposed.toEquationEquiv
  simp only [OneHoleContext.fill, List.nil_append, List.cons_append] at firstBody secondBlock
  exact .trans _ _ _ split (.trans _ _ _ firstBody (.trans _ _ _ secondBlock paired))

omit laws in
theorem restricts_step {step : Pattern → Pattern → Prop} (reactions : Reactions language block step) :
    ∀ (count : Nat) {source target : Pattern}, step source target →
      step (Prenex.restricts block count source) (Prenex.restricts block count target)
  | 0, _, _, stepped => stepped
  | count + 1, _, _, stepped => reactions.restrict (restricts_step reactions count stepped)

variable {step : Pattern → Pattern → Prop}

/-- **The canonical form of a block with a redex at its front steps**, to a process equivalent to the block's
contractum: the redex is found among the canonical components, with canonical parts. -/
theorem block_simulation (reactions : Reactions language block step) {free : FreeTypeContext}
    {bound : List TypeExpr} (context : BaseContext free bound) {count : Nat} {redex : reactions.Redex}
    {rest : List Pattern}
    (members : Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound)
      (reactions.parts redex ++ rest))
    (objects : ∀ element ∈ reactions.parts redex ++ rest, isObjectPattern element = true) :
    ∃ target, step (canon block (Prenex.restricts block count (.collection .hashBag (reactions.parts redex ++ rest)
        none))) target ∧
      EquationEquiv (engineBasePremises RelationEnv.empty) language target
        (Prenex.restricts block count (.collection .hashBag (reactions.result redex ++ rest) none)) := by
  -- the block and its parts
  set source := Prenex.restricts block count (.collection .hashBag (reactions.parts redex ++ rest) none)
    with sourceIs
  have sourceTyped : HasType language free bound source (.base block.proc) :=
    restricts_typed count (bag_typed (rest := none) members)
  have partsMembers : Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound)
      (reactions.parts redex) := fun element member => members element (by simp [member])
  have partsObjects : ∀ part ∈ reactions.parts redex, isObjectPattern part = true := fun element member =>
    objects element (by simp [member])
  have restMembers : Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound) rest :=
    fun element member => members element (by simp [member])
  have restObjects : ∀ element ∈ rest, isObjectPattern element = true := fun element member =>
    objects element (by simp [member])
  have resultMembers := reactions.result_members redex partsMembers
  obtain ⟨tailMembers, -⟩ := decompose_sound (block := block) (bag_typed (rest := none) restMembers)
  have tailObjects := objects_of_decompose (block := block) (pattern := .collection .hashBag rest none)
    ((isObject_bag).mpr restObjects)
  generalize tailFormIs : decompose block (.collection .hashBag rest none) = tailForm at tailMembers tailObjects
  obtain ⟨inner, tail⟩ := tailForm
  simp only at tailMembers tailObjects
  -- following the block's restrictions
  have used : ∀ index, UsedBy index ((reactions.result redex).map (liftBVars 0 inner)) →
      UsedBy index ((reactions.parts redex).map (liftBVars 0 inner)) := by
    rintro index ⟨element, member, free⟩
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    rw [liftBVars_eq_rename, freeIn_rename] at free
    obtain ⟨index', free', rfl⟩ := free
    obtain ⟨part, partMember, partFree⟩ := reactions.freeIn_result redex originalMember free'
    exact ⟨_, List.mem_map_of_mem partMember, by rw [liftBVars_eq_rename, freeIn_rename]; exact ⟨index', partFree, rfl⟩⟩
  have followMembers : Members language block free (List.replicate inner (TypeExpr.base block.name) ++
      (List.replicate count (TypeExpr.base block.name) ++ bound))
      ((reactions.result redex).map (liftBVars 0 inner) ++ tail) := by
    intro element member
    rcases List.mem_append.mp member with lifted | inTail
    · exact lift_members inner resultMembers element lifted
    · exact tailMembers element inTail
  obtain ⟨final, relabel, iterated, finalMembers, follows⟩ := closes_follow count used followMembers
  have decomposed : decompose block source =
      ⟨final, ((reactions.parts redex).map (liftBVars 0 inner) ++ tail).map (rename relabel)⟩ := by
    rw [sourceIs, decompose_restricts, decompose_front _ (reactions.atoms redex), tailFormIs]
    exact iterated
  obtain ⟨componentsMembers, -⟩ := decompose_sound (block := block) sourceTyped
  rw [decomposed] at componentsMembers
  simp only at componentsMembers
  -- the canonical form
  set fuel := 2 * size source with fuelIs
  set components := ((reactions.parts redex).map (liftBVars 0 inner) ++ tail).map (rename relabel)
    with componentsIs
  have canonIs : canon block source = (Prenex.toPattern block) ⟨final, least ((orders (List.range final)).map
      fun order => sortComponents (components.map fun component =>
        canonComponentWith block (fuel + 1) (rename (Prenex.permute final order) component)))⟩ := by
    unfold canon
    rw [show 2 * size source + 2 = (fuel + 1) + 1 by omega]
    simp only [canonWith]
    rw [decomposed]
  have candidatesNonempty : ((orders (List.range final)).map fun order =>
      sortComponents (components.map fun component =>
        canonComponentWith block (fuel + 1) (rename (Prenex.permute final order) component))) ≠ [] := by
    simpa using orders_ne_nil (List.range final)
  obtain ⟨order, orderMember, leastIs⟩ := List.mem_map.mp (least_mem candidatesNonempty)
  rw [← leastIs] at canonIs
  set permutation := Prenex.permute final order with permutationIs
  set relabelling := permutation ∘ (relabel ∘ shiftAbove 0 inner) with relabellingIs
  set renamed := reactions.rename relabelling redex
  set others := tail.map (rename relabel) with othersIs
  have reordered := block_reorder_equivalent (block := block) (bound := bound) (orders_reorders _ order orderMember)
    componentsMembers
  have renamedMembers := reordered.1
  have renamedParts : (reactions.parts redex).map
      (fun part => rename permutation (rename relabel (liftBVars 0 inner part))) = reactions.parts renamed := by
    rw [reactions.parts_rename]
    exact List.map_congr_left fun part _ => by
      rw [liftBVars_eq_rename, rename_comp, rename_comp]
      rfl
  have componentsRenamed : components.map (rename permutation) =
      reactions.parts renamed ++ others.map (rename permutation) := by
    rw [← renamedParts, componentsIs, othersIs]
    simp [List.map_map, Function.comp_def]
  have finalContext := context.replicate final block.name
  have renamedPartsMembers : Members language block free (List.replicate final (TypeExpr.base block.name) ++ bound)
      (reactions.parts renamed) := by
    intro element member
    apply renamedMembers
    rw [← permutationIs, componentsRenamed]
    exact List.mem_append_left _ member
  have renamedPartsObjects : ∀ part ∈ reactions.parts renamed, isObjectPattern part = true := by
    intro part member
    rw [← renamedParts] at member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    rw [isObjectPattern_rename, isObjectPattern_rename, isObject_liftBVars]
    exact partsObjects original originalMember
  have othersRenamedTyped : ∀ component ∈ others, HasType language free
      (List.replicate final (TypeExpr.base block.name) ++ bound) (rename permutation component) (.base block.proc) := by
    intro component member
    apply renamedMembers
    rw [← permutationIs, componentsRenamed]
    exact List.mem_append_right _ (List.mem_map_of_mem member)
  have othersRenamedObjects : ∀ component ∈ others, isObjectPattern (rename permutation component) = true := by
    intro component member
    rw [isObjectPattern_rename]
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    rw [isObjectPattern_rename]
    exact tailObjects original originalMember
  obtain ⟨canonical, canonicalParts, canonicalResult⟩ :=
    reactions.canonical finalContext fuel renamed renamedPartsMembers renamedPartsObjects
  set canonOthers := others.map fun component => canonComponentWith block (fuel + 1) (rename permutation component)
    with canonOthersIs
  have image : components.map (fun component => canonComponentWith block (fuel + 1) (rename permutation component)) =
      reactions.parts canonical ++ canonOthers := by
    have mapped := congrArg (List.map (canonComponentWith block (fuel + 1))) componentsRenamed
    simp only [List.map_map, List.map_append] at mapped
    rw [canonicalParts, canonOthersIs]
    simpa [Function.comp_def] using mapped
  -- the redex among the sorted canonical components
  set sorted := sortComponents (components.map fun component =>
    canonComponentWith block (fuel + 1) (rename permutation component)) with sortedIs
  have sortedPerm : sorted.Perm (reactions.parts canonical ++ canonOthers) := by
    rw [sortedIs, ← image]
    exact List.perm_insertionSort _ _
  have sortedMembers : Members language block free (List.replicate final (TypeExpr.base block.name) ++ bound)
      sorted := by
    intro element member
    have inImage : element ∈ components.map
        (fun component => canonComponentWith block (fuel + 1) (rename permutation component)) := by
      rw [image]; exact sortedPerm.mem_iff.mp member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp inImage
    exact (canonComponentWith_sound (block := block) (fuel + 1) finalContext
      (renamedMembers _ (List.mem_map_of_mem originalMember))).1
  have sortedObjects : ∀ element ∈ sorted, isObjectPattern element = true := by
    intro element member
    have inImage : element ∈ components.map
        (fun component => canonComponentWith block (fuel + 1) (rename permutation component)) := by
      rw [image]; exact sortedPerm.mem_iff.mp member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp inImage
    have renamedObject : isObjectPattern (rename permutation original) = true := by
      rw [isObjectPattern_rename]
      have := objects_of_decompose (block := block)
        (by rw [isObject_restricts, isObject_bag]; exact objects : isObjectPattern source = true)
      rw [decomposed] at this
      exact this original originalMember
    rw [← equationEquiv_isObject (block := block) (canonComponentWith_sound (block := block) (fuel + 1) finalContext
      (renamedMembers _ (List.mem_map_of_mem originalMember))).2.toEquationEquiv]
    exact renamedObject
  obtain ⟨target, stepped, reached⟩ := reactions.react canonical sortedPerm sortedMembers sortedObjects
  refine ⟨Prenex.restricts block final target, ?_, ?_⟩
  · rw [canonIs]
    exact restricts_step reactions final stepped
  · have othersRelated : List.Forall₂ (EquationEquiv (engineBasePremises RelationEnv.empty) language) canonOthers
        (others.map (rename permutation)) := by
      rw [canonOthersIs, List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
      intro component member
      exact .symm _ _ (canonComponentWith_sound (block := block) (fuel + 1) finalContext
        (othersRenamedTyped component member)).2.toEquationEquiv
    have partsRelated := List.rel_append canonicalResult othersRelated
    have uncanonical := restricts_equation (block := block) final (by simpa using collection_equation partsRelated [])
    have renamedResultMembers := reactions.result_members renamed renamedPartsMembers
    have plainMembers : Members language block free (List.replicate final (TypeExpr.base block.name) ++ bound)
        (reactions.result renamed ++ others.map (rename permutation)) := by
      intro element member
      rcases List.mem_append.mp member with inResult | inOthers
      · exact renamedResultMembers element inResult
      · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp inOthers
        exact othersRenamedTyped original originalMember
    have toBody := restricts_equation (block := block) final (bag_body_equivalent plainMembers).toEquationEquiv
    have reorderFollow := block_reorder_equivalent (block := block) (bound := bound)
      (orders_reorders _ order orderMember) finalMembers
    have followRenamed : (((reactions.result redex).map (liftBVars 0 inner) ++ tail).map (rename relabel)).map
        (rename (Prenex.permute final order)) = reactions.result renamed ++ others.map (rename permutation) := by
      rw [← permutationIs, reactions.result_rename]
      simp only [List.map_append, List.map_map, othersIs]
      congr 1
      exact List.map_congr_left fun element _ => by
        simp only [Function.comp_apply]
        rw [liftBVars_eq_rename, rename_comp, rename_comp]
        rfl
    rw [followRenamed] at reorderFollow
    have front := front_block_equivalent resultMembers restMembers
    rw [tailFormIs] at front
    have frontRestricted := restricts_equation (block := block) count front
    exact .trans _ _ _ (restricts_equation (block := block) final reached) (.trans _ _ _ uncanonical (.trans _ _ _ toBody
      (.trans _ _ _ (.symm _ _ reorderFollow.2.toEquationEquiv)
        (.trans _ _ _ (.symm _ _ follows) (.symm _ _ frontRestricted)))))

/-- **A step of a process is matched by a step of its canonical form**, to a contractum with the same canonical
form, once every step reaches a block with a redex at its front. -/
theorem simulation (reactions : Reactions language block step) {free : FreeTypeContext} {bound : List TypeExpr}
    (context : BaseContext free bound) {source target : Pattern}
    (reached : StepBlock reactions free bound source target) (object : isObjectPattern source = true) :
    ∃ target', step (canon block source) target' ∧ canon block target' = canon block target := by
  obtain ⟨count, redex, rest, stepBlock⟩ := reached
  obtain ⟨target', stepped, equivalent⟩ := block_simulation reactions context stepBlock.members stepBlock.objects
  rw [canon_complete (block := block) object stepBlock.source]
  refine ⟨target', stepped, ?_⟩
  have contractumObject : isObjectPattern (Prenex.restricts block count
      (.collection .hashBag (reactions.result redex ++ rest) none)) = true := by
    rw [isObject_restricts, isObject_bag]
    intro element member
    rcases List.mem_append.mp member with inResult | inRest
    · exact reactions.result_objects redex (fun part member => stepBlock.objects part (by simp [member])) element
        inResult
    · exact stepBlock.objects element (by simp [inRest])
  have targetObject : isObjectPattern target' = true := by
    rw [equationEquiv_isObject (block := block) equivalent]
    exact contractumObject
  exact canon_complete (block := block) targetObject (.trans _ _ _ equivalent (.symm _ _ stepBlock.target))

end Simulation

/-! ## Named multisets of atoms -/

/-- **The canonical multiset of a bag of atoms**: its members with canonical parts, sorted. The members of a named
multiset are of a sort other than processes, so each is its own block. -/
theorem canonMultisetWith_atoms (fuel : Nat) {elements : List Pattern}
    (atoms : ∀ element ∈ elements, decompose block element = Prenex.atom element) :
    canonMultisetWith block (fuel + 1) (.collection .hashBag elements none) =
      .collection .hashBag (sortComponents (elements.map (canonComponentWith block fuel))) none := by
  have decomposed : decompose block (.collection .hashBag elements none) = ⟨0, elements⟩ := by
    rw [decompose_bag, decomposeList_atoms atoms]
  have identity : Prenex.permute 0 [] = id := by
    funext index
    simp [Prenex.permute]
  simp only [canonMultisetWith, decomposed, List.range_zero, orders, List.map_cons, List.map_nil, identity, rename_id,
    least, List.foldl_nil, multisetOf, if_pos]

/-- Two members of a list, found again from a permutation. -/
theorem indices_of_perm_two {α : Type} {elements rest : List α} {first second : α}
    (permutation : elements.Perm (first :: second :: rest)) :
    ∃ (i : Nat) (hi : i < elements.length) (j : Nat) (hj : j < (elements.eraseIdx i).length),
      elements[i] = first ∧ (elements.eraseIdx i)[j] = second ∧ ((elements.eraseIdx i).eraseIdx j).Perm rest := by
  have firstMember : first ∈ elements := permutation.mem_iff.mpr (by simp)
  obtain ⟨i, hi, firstAt⟩ := List.getElem_of_mem firstMember
  have others : (elements.eraseIdx i).Perm (second :: rest) := by
    have reordered := (perm_getElem_eraseIdx elements i hi).symm.trans permutation
    rw [firstAt] at reordered
    exact reordered.cons_inv
  have secondMember : second ∈ elements.eraseIdx i := others.mem_iff.mpr (by simp)
  obtain ⟨j, hj, secondAt⟩ := List.getElem_of_mem secondMember
  have remaining := (perm_getElem_eraseIdx (elements.eraseIdx i) j hj).symm.trans others
  rw [secondAt] at remaining
  exact ⟨i, hi, j, hj, firstAt, secondAt, remaining.cons_inv⟩

/-- One member found again from a permutation. -/
theorem index_of_perm_one {α : Type} {elements rest : List α} {first : α}
    (permutation : elements.Perm (first :: rest)) :
    ∃ (i : Nat) (hi : i < elements.length), elements[i] = first ∧ (elements.eraseIdx i).Perm rest := by
  have firstMember : first ∈ elements := permutation.mem_iff.mpr (by simp)
  obtain ⟨i, hi, firstAt⟩ := List.getElem_of_mem firstMember
  have reordered := (perm_getElem_eraseIdx elements i hi).symm.trans permutation
  rw [firstAt] at reordered
  exact ⟨i, hi, firstAt, reordered.cons_inv⟩

section Single

variable [laws : BlockSignature language block] {step : Pattern → Pattern → Prop}

/-- **A reaction of one component that is the whole process** is a reaction at the front of a block, under no
restriction: a one-member bag is its member. -/
theorem ReactsAt.single {free : FreeTypeContext} {bound : List TypeExpr} {source target : Pattern}
    {parts result : List Pattern} (partsIs : parts = [source])
    (typed : HasType language free bound source (.base block.proc)) (object : isObjectPattern source = true)
    (reached : EquationEquiv (engineBasePremises RelationEnv.empty) language target
      (.collection .hashBag result none)) :
    ReactsAt language block free bound source target 0 parts result [] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro element member
    simp only [partsIs, List.append_nil, List.mem_singleton] at member
    subst member
    simpa using typed
  · intro element member
    simp only [partsIs, List.append_nil, List.mem_singleton] at member
    subst member
    exact object
  · rw [partsIs]
    exact .symm _ _ (derivedInstance_equivalent (laws.singleton typed))
  · simpa [Prenex.restricts] using reached

/-- **A redex of one component that is the whole process** is a block with its redex at the front, under no
restriction. -/
theorem StepBlockAt.single {reactions : Reactions language block step} {free : FreeTypeContext}
    {bound : List TypeExpr} {source target : Pattern} {redex : reactions.Redex}
    (parts : reactions.parts redex = [source]) (typed : HasType language free bound source (.base block.proc))
    (object : isObjectPattern source = true)
    (reached : EquationEquiv (engineBasePremises RelationEnv.empty) language target
      (.collection .hashBag (reactions.result redex) none)) :
    StepBlockAt reactions free bound source target 0 redex [] :=
  ReactsAt.single parts typed object reached

end Single

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
