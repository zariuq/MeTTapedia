import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPartnerAdequacy
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiMoleculeRepresentation
import Mettapedia.Languages.ProcessCalculi.PiCalculus.ReadBackCanonical
import Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexReflection

/-!
# π's front door and the named π-calculus

The front door reads `piCalc` modulo its static theory (`PiPartners.Reduces`); the named π-calculus reduces modulo
its structural congruence, which also unfolds replicated input. On translations of named processes the two reductions
agree:

- **A reduction of a translation is a named reduction** (`reduces_named`): the front door's reduction is a
  communication of a presentation of the canonical form, which is a communication of the translation's own guards
  beside copies of its servers' inputs (`PrenexForm.reflect_presented`); it reads back as a named reduction, the copies
  absorbed by their servers (`parList_absorb`).
- **A named reduction is a reduction of the translation** (`named_reduces`), the block of the translation read as a
  molecule, a server firing through a copy of its input unfolded beside it; so the named calculus's saturated reduction
  bisimilarity is `piCalc`'s beside named partners (`saturated_iff_namedSaturated`), and the front door's
  partner-labelled native types under named partners characterize it (`agree_iff_named`).
- **Replication goes beyond the named calculus** (`replicated_output_not_named`): `piCalc` replicates any process, the
  named calculus inputs only, so a replicated output is a partner no named process translates to.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiNamed

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.OSLF.MeTTaIL.Substitution (freeVars instantiateBVar)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv)
open Mettapedia.Languages.ProcessCalculi.PiCalculus
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance (piCalc piToPattern PiRawStep piToPattern_hasType
  piToPattern_admissible)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexForm (Readable readBack readable_piToPattern
  readBack_piToPattern readBack_canon rawStep_readBack normal normal_equivalent openWith_nil named_normal named_object)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPrenexForms (reading domain canon canonical typed_of_domain
  domain_of_typed names_eq)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPartners (processes Reduces reduces_canonical rawSuccessors_sound
  process_of_raw equivalent_of_canon_eq)

/-! ## Translations at the front door -/

/-- **A translation is a process** of the front door. -/
theorem translation_process (process : Process) : processes (piToPattern process) :=
  domain_of_typed (by rw [names_eq]; exact piToPattern_hasType process) (piToPattern_admissible process).object

/-- Processes related by `piCalc`'s laws are equivalent at the front door. -/
theorem equivalent_of_equation {first second : Pattern} (firstIn : processes first) (secondIn : processes second)
    (equivalent : EquationEquiv (engineBasePremises RelationEnv.empty) piCalc first second) :
    ObjectEquivalent RelationEnv.empty piCalc reading first second := by
  refine equivalent_of_canon_eq firstIn secondIn ?_
  unfold canon
  rw [if_pos firstIn, if_pos secondIn]
  exact Mettapedia.GSLT.LanguageDef.RestrictionBlocks.canonR_complete (block := Blocks.piRepBlock)
    (typed_of_domain firstIn).2 (typed_of_domain secondIn).2
    (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.restrictionsBind_of_typed (block := Blocks.piRepBlock) _
      (typed_of_domain firstIn).1) equivalent

/-! ## Blocks read as molecules -/

open Mettapedia.OSLF.NativeTypes.GeneratedLogic.Pi.LeastPartners (Guarded Prime Molecule Internal Fires Lifts rules
  Denotes BagDenotes lifts_congruent denotes_congruent bag_reacts_of_reduces)
open Mettapedia.GSLT.BagRelativePushout (bag bag_injective)
open Mettapedia.GSLT.SemiSaturated (Reacts)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexForm (isGuard guard_cases nameOf isName Named
  named_piToPattern)

theorem guarded_readBack {avoid : Finset Name} {env : List Name} {component : Pattern}
    (guard : isGuard component = true) : Guarded (readBack avoid env component) := by
  rcases guard_cases guard with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> simp only [readBack]
  · exact .input _ _ _
  · exact .replicate _ _ _
  · exact .output _ _

/-- A component of a block read back as a guarded process. -/
def toPrime (avoid : Finset Name) (env : List Name) (component : Pattern) : Prime :=
  if guarded : Guarded (readBack avoid env component) then ⟨_, guarded⟩ else ⟨.output "" "", .output _ _⟩

theorem toPrime_val {avoid : Finset Name} {env : List Name} {component : Pattern} (guard : isGuard component = true) :
    (toPrime avoid env component).1 = readBack avoid env component := by
  simp [toPrime, guarded_readBack guard]

/-- **A reaction of a single molecule** is a communication inside it. -/
theorem singleton_reacts {molecule : Molecule} {next : Multiset Molecule}
    (reacts : Reacts rules (bag {molecule}) (bag next)) : ∃ result, Internal molecule result ∧ next = {result} := by
  obtain ⟨rule, member, redex, reactum, redexEq, reactumEq, contained, rfl⟩ :=
    Mettapedia.GSLT.BagSaturated.reacts_iff.mp reacts
  rcases member with ⟨inner, result, internal, rfl⟩ | ⟨first, second, result, _, rfl⟩
  · obtain rfl := bag_injective redexEq
    obtain rfl := bag_injective reactumEq
    obtain rfl : inner = molecule := by simpa using contained
    exact ⟨result, internal, by simp⟩
  · obtain rfl := bag_injective redexEq
    have := Multiset.card_le_card contained
    simp at this

theorem exists_perm_map_cons {α β : Type} [DecidableEq α] {map : α → β} {list : List α} {head : β} {rest : List β}
    (perm : (list.map map).Perm (head :: rest)) :
    ∃ element tail, list.Perm (element :: tail) ∧ map element = head ∧ (tail.map map).Perm rest := by
  obtain ⟨element, member, rfl⟩ := List.mem_map.mp (perm.symm.subset List.mem_cons_self)
  refine ⟨element, list.erase element, List.perm_cons_erase member, rfl, ?_⟩
  exact ((perm.symm.trans ((List.perm_cons_erase member).map map)).cons_inv).symm

/-- **Names of distinct variables are distinct**, when the names given are distinct and avoid the free names. -/
theorem nameOf_injective {avoid : Finset Name} {env : List Name} (nodup : env.Nodup)
    (apart : ∀ name ∈ env, name ∉ avoid) {first second : Pattern} (firstNamed : isName first = true)
    (secondNamed : isName second = true) (firstScoped : first.isWellScopedAt env.length = true)
    (secondScoped : second.isWellScopedAt env.length = true) (firstAvoided : ∀ name ∈ freeVars first, name ∈ avoid)
    (secondAvoided : ∀ name ∈ freeVars second, name ∈ avoid) (same : nameOf env first = nameOf env second) :
    first = second := by
  cases first with
  | fvar a =>
      cases second with
      | fvar b => simp only [nameOf] at same; rw [same]
      | bvar j =>
          simp only [Pattern.isWellScopedAt, decide_eq_true_eq] at secondScoped
          simp only [nameOf, List.getD_eq_getElem _ _ secondScoped] at same
          exact absurd (firstAvoided a (by simp [freeVars])) (apart a (same ▸ List.getElem_mem _))
      | _ => simp [isName] at secondNamed
  | bvar i =>
      cases second with
      | fvar b =>
          simp only [Pattern.isWellScopedAt, decide_eq_true_eq] at firstScoped
          simp only [nameOf, List.getD_eq_getElem _ _ firstScoped] at same
          exact absurd (secondAvoided b (by simp [freeVars])) (apart b (same ▸ List.getElem_mem _))
      | bvar j =>
          simp only [Pattern.isWellScopedAt, decide_eq_true_eq] at firstScoped secondScoped
          simp only [nameOf, List.getD_eq_getElem _ _ firstScoped, List.getD_eq_getElem _ _ secondScoped] at same
          rw [(List.Nodup.getElem_inj_iff nodup).mp same]
      | _ => simp [isName] at secondNamed
  | _ => simp [isName] at firstNamed

local notation:50 first " ≅ " second => Mettapedia.Languages.ProcessCalculi.PiCalculus.Congruent first second

open Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexForm (scoped_unary avoided_unary)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexForm (namedList_iff readBack_restricts readBack_bag
  readBack_receive instantiate_facts decompose_reads freshNames freshNames_length freshNames_nodup freshNames_fresh
  scoped_binary scoped_lambda avoided_binary avoided_lambda piReactions)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Members Prenex isObject_restricts isObject_bag restricts_step
  restricts_equation)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Blocks (piBlock)

theorem readable_bag {avoid : Finset Name} {depth : Nat} {elements : List Pattern}
    (all : ∀ element ∈ elements, Readable avoid depth element) :
    Readable avoid depth (.collection .hashBag elements none) :=
  ⟨by simp only [Named]; exact namedList_iff.mpr fun element member => (all element member).named,
    by simpa only [Pattern.isWellScopedAt, Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff]
      using fun element member => (all element member).inScope,
    fun name free => by
      simp only [freeVars, List.mem_flatMap] at free
      obtain ⟨element, member, inside⟩ := free
      exact (all element member).avoided name inside⟩

/-- **The read-back of a communication's result denotes the result's molecule**: the continuation's lifted
restrictions join the block's, its components the others. -/
theorem result_reads {avoid : Finset Name} {names : List Name} (nodup : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ avoid) {others : List Pattern} (othersGuards : ∀ other ∈ others, isGuard other = true)
    (othersReadable : ∀ other ∈ others, Readable avoid names.length other) {received : Pattern}
    (receivedReadable : Readable avoid names.length received) {continuation : Process}
    (receives : continuation ≅ readBack avoid names.reverse received) {lifted : Finset Name}
    {components : Multiset Prime} (lifts : Lifts continuation lifted components)
    (liftedFresh : Disjoint lifted (names.toFinset ∪ (parList (others.map (readBack avoid names.reverse))).freeNames)) :
    ∃ process, Denotes ⟨names.toFinset ∪ lifted, ↑(others.map (toPrime avoid names.reverse)) + components⟩ process ∧
      (readBack avoid [] (Prenex.restricts piBlock names.length (.collection .hashBag (received :: others) none)) ≅
        process) := by
  obtain ⟨liftedNames, primes, liftedNodup, liftedEq, primesEq, continuationCongruent⟩ := lifts_congruent lifts
  have bagReadable : Readable avoid (([] : List Name).length + names.length)
      (.collection .hashBag (received :: others) none) := by
    refine (readable_bag fun element member => ?_).depth
      (show names.length = ([] : List Name).length + names.length by simp)
    rcases List.mem_cons.mp member with rfl | inOthers
    · exact receivedReadable
    · exact othersReadable element inOthers
  have restricted := readBack_restricts (avoid := avoid) names bagReadable nodup
    (fun name member => ⟨fresh name member, by simp⟩)
  rw [List.append_nil, readBack_bag, List.map_cons] at restricted
  have othersVal : (others.map (toPrime avoid names.reverse)).map Subtype.val =
      others.map (readBack avoid names.reverse) := by
    rw [List.map_map]
    exact List.map_congr_left fun other member => toPrime_val (othersGuards other member)
  refine ⟨nuList (names ++ liftedNames) (parList ((primes ++ others.map (toPrime avoid names.reverse)).map
    Subtype.val)), ⟨names ++ liftedNames, primes ++ others.map (toPrime avoid names.reverse), ?_, ?_, ?_, rfl⟩, ?_⟩
  · refine List.nodup_append.mpr ⟨nodup, liftedNodup, fun first firstMember second secondMember same => ?_⟩
    have inLifted : second ∈ lifted := liftedEq ▸ List.mem_toFinset.mpr secondMember
    exact Finset.disjoint_left.mp liftedFresh inLifted
      (Finset.mem_union_left _ (List.mem_toFinset.mpr (same ▸ firstMember)))
  · rw [List.toFinset_append, liftedEq]
  · rw [← Multiset.coe_add, primesEq, add_comm]
  · refine restricted.trans ?_
    rw [nuList_append]
    refine nuList_congruent names ?_
    simp only [parList]
    refine (Congruent.par (receives.symm.trans continuationCongruent) (Congruent.refl _)).trans ?_
    have extrude : Disjoint liftedNames.toFinset (parList (others.map (readBack avoid names.reverse))).freeNames := by
      rw [liftedEq]
      exact liftedFresh.mono_right Finset.subset_union_right
    refine (nuList_extrude extrude).trans (nuList_congruent liftedNames ?_)
    rw [List.map_append, othersVal]
    exact (parList_append _ _).symm

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (decompose decompose_sound restricts_typed body_perm_equivalent
  bag_typed)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPrenexForms (step_iff_raw)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPartners (isState_of_process)

/-- A block's front-door facts: a process equivalent to the translation, whose read-back after a step is equivalent
to the step's target. -/
theorem reduct_equivalent {avoid : Finset Name} {target : Pattern} (targetIn : processes target)
    (targetReadable : Readable avoid ([] : List Name).length target) :
    ObjectEquivalent RelationEnv.empty piCalc reading (piToPattern (readBack avoid [] target)) target := by
  have typed := typed_of_domain targetIn
  rw [targetReadable.translation, openWith_nil]
  obtain ⟨normalTyped, normalEquivalent⟩ :=
    normal_equivalent _ (Nat.lt_succ_self _) typed.1 typed.2 targetReadable.named
  have normalIn : processes (normal target) := domain_of_typed normalTyped
    (named_object _ (Nat.lt_succ_self _) (named_normal _ (Nat.lt_succ_self _) targetReadable.named))
  exact .symm _ _ (equivalent_of_equation targetIn normalIn normalEquivalent)

/-- The components of a block in which two communicate: the block, as a permutation of them. -/
theorem block_equivalent {source : Pattern} (sourceIn : processes source) {form : Prenex}
    (members : Members piCalc piBlock PiPrenexForms.names (List.replicate form.count (.base "Name") ++ []) form.components)
    (blockEquivalent : EquationEquiv (engineBasePremises RelationEnv.empty) piCalc source (form.toPattern piBlock))
    {first second : Pattern} {rest : List Pattern} (perm : form.components.Perm (first :: second :: rest))
    (blockIn : processes (Prenex.restricts piBlock form.count (.collection .hashBag (first :: second :: rest) none))) :
    ObjectEquivalent RelationEnv.empty piCalc reading source
      (Prenex.restricts piBlock form.count (.collection .hashBag (first :: second :: rest) none)) := by
  refine equivalent_of_equation sourceIn blockIn (.trans _ _ _ blockEquivalent ?_)
  exact restricts_equation form.count (body_perm_equivalent members perm).toEquationEquiv

theorem block_process {form : Prenex}
    (members : Members piCalc piBlock PiPrenexForms.names (List.replicate form.count (.base "Name") ++ []) form.components)
    (objects : ∀ component ∈ form.components, isObjectPattern component = true)
    {elements : List Pattern} (perm : form.components.Perm elements) :
    processes (Prenex.restricts piBlock form.count (.collection .hashBag elements none)) := by
  apply domain_of_typed
  · exact restricts_typed (block := piBlock) form.count (bag_typed (block := piBlock) (rest := none) fun element member => members element (perm.symm.subset member))
  · rw [isObject_restricts, isObject_bag]
    exact fun element member => objects element (perm.symm.subset member)

/-- **A named reduction is a reduction of the translation**, to a pattern equivalent to the translation of a process
congruent to the reduct. -/
theorem named_reduces {source reduct : Process} (step : Nonempty (source ⇝ reduct)) :
    ∃ target : Pattern, Reduces (piToPattern source) target ∧
      ∃ reduct' : Process, (reduct' ≅ reduct) ∧
        ObjectEquivalent RelationEnv.empty piCalc reading (piToPattern reduct') target := by
  have sourceIn := translation_process source
  set avoid := source.freeNames with avoidIs
  have readable : Readable avoid ([] : List Name).length (piToPattern source) :=
    readable_piToPattern (Finset.Subset.refl _)
  have reads := decompose_reads avoid _ [] (Nat.lt_succ_self _) readable
  have typedSource := typed_of_domain sourceIn
  obtain ⟨members, blockEquivalent⟩ := decompose_sound (block := piBlock) typedSource.1
  generalize formIs : decompose piBlock (piToPattern source) = form at reads members blockEquivalent
  have objects : ∀ component ∈ form.components, isObjectPattern component = true := fun component member =>
    named_object _ (Nat.lt_succ_self _) (reads.readable component member).named
  have namesLength : (freshNames avoid form.count).length = form.count := freshNames_length _ _
  have namesNodup := freshNames_nodup form.count avoid
  have namesFresh : ∀ name ∈ freshNames avoid form.count, name ∉ avoid := fun _ member => freshNames_fresh _ member
  generalize freshNames avoid form.count = names at namesLength namesNodup namesFresh
  have componentReadable : ∀ component ∈ form.components, Readable avoid names.reverse.length component :=
    fun component member => (reads.readable component member).depth (by simp [namesLength])
  have primesVal : (form.components.map (toPrime avoid names.reverse)).map Subtype.val =
      form.components.map (readBack avoid names.reverse) := by
    rw [List.map_map]
    exact List.map_congr_left fun component member => toPrime_val (reads.guards component member)
  set molecule : Molecule := ⟨names.toFinset, ↑(form.components.map (toPrime avoid names.reverse))⟩ with moleculeIs
  have denotation : source ≅ nuList names (parList ((form.components.map
      (toPrime avoid names.reverse)).map Subtype.val)) := by
    rw [primesVal]
    have expanded := reads.reads names namesLength namesNodup fun name member => ⟨namesFresh name member, by simp⟩
    simp only [List.append_nil] at expanded
    exact (readBack_piToPattern (by rw [avoidIs])).symm.trans expanded
  have bagDenotes : BagDenotes {molecule}
      (parList [nuList names (parList ((form.components.map (toPrime avoid names.reverse)).map Subtype.val))]) :=
    ⟨[molecule], [_], rfl, .cons ⟨names, form.components.map (toPrime avoid names.reverse), namesNodup, rfl, rfl, rfl⟩
      .nil, rfl⟩
  obtain ⟨namedStep⟩ := reduces_of_congruent ((Congruent.nilRight _).trans denotation.symm) step (Congruent.refl _)
  obtain ⟨next, reached, reacts, nextDenotes, reductCongruent⟩ := bag_reacts_of_reduces bagDenotes namedStep
  obtain ⟨result, internal, rfl⟩ := singleton_reacts reacts
  obtain ⟨resultMolecules, resultProcesses, resultEq, resultDenote, rfl⟩ := nextDenotes
  obtain rfl : resultMolecules = [result] := Multiset.coe_eq_singleton.mp resultEq
  obtain ⟨resultProcess, resultDenotes⟩ : ∃ resultProcess, resultProcesses = [resultProcess] ∧
      Denotes result resultProcess := by
    cases resultDenote with
    | cons head tail => cases tail; exact ⟨_, rfl, head⟩
  obtain ⟨rfl, resultDenotes⟩ := resultDenotes
  -- the communication inside the molecule
  cases internal with
  | @comm receiver sender continuation kept lifted components contained fires lifts liftedFresh =>
  obtain ⟨others, othersEq⟩ := Multiset.le_iff_exists_add.mp contained
  have othersEq' : (↑(form.components.map (toPrime avoid names.reverse)) : Multiset Prime) =
      {receiver, sender} + others := othersEq
  have perm : (form.components.map (toPrime avoid names.reverse)).Perm (receiver :: sender :: others.toList) := by
    apply Multiset.coe_eq_coe.mp
    rw [othersEq', ← Multiset.cons_coe, ← Multiset.cons_coe, Multiset.coe_toList]
    simp [Multiset.insert_eq_cons]
  obtain ⟨first, tail, firstPerm, firstPrime, tailPerm⟩ := exists_perm_map_cons perm
  obtain ⟨second, rest, secondPerm, secondPrime, restPerm⟩ := exists_perm_map_cons tailPerm
  have componentsPerm : form.components.Perm (first :: second :: rest) := firstPerm.trans (secondPerm.cons first)
  have firstMember : first ∈ form.components := componentsPerm.symm.subset List.mem_cons_self
  have secondMember : second ∈ form.components :=
    componentsPerm.symm.subset (List.mem_cons_of_mem _ List.mem_cons_self)
  have restMember : ∀ other ∈ rest, other ∈ form.components := fun other member =>
    componentsPerm.symm.subset (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))
  have othersIs : others = ↑(rest.map (toPrime avoid names.reverse)) := by
    rw [← Multiset.coe_toList others]
    exact (Multiset.coe_eq_coe.mpr restPerm).symm
  have bodyMinus : molecule.body - {receiver, sender} = ↑(rest.map (toPrime avoid names.reverse)) := by
    show (↑(form.components.map (toPrime avoid names.reverse)) : Multiset Prime) - {receiver, sender} = _
    rw [othersEq', add_tsub_cancel_left, othersIs]
  have firstVal := congrArg Subtype.val firstPrime
  have secondVal := congrArg Subtype.val secondPrime
  rw [toPrime_val (reads.guards first firstMember)] at firstVal
  rw [toPrime_val (reads.guards second secondMember)] at secondVal
  have restFresh : Disjoint lifted (names.toFinset ∪
      (parList (rest.map (readBack avoid names.reverse))).freeNames) := by
    refine liftedFresh.mono_right (Finset.union_subset_union (Finset.Subset.refl _) fun name free => ?_)
    obtain ⟨process, member, inside⟩ := mem_freeNames_parList.mp free
    obtain ⟨other, otherMember, rfl⟩ := List.mem_map.mp member
    refine Mettapedia.OSLF.NativeTypes.GeneratedLogic.Pi.LeastPartners.Molecule.mem_bodyNames.mpr
      ⟨toPrime avoid names.reverse other, ?_, by rwa [toPrime_val (reads.guards other (restMember other otherMember))]⟩
    exact Multiset.mem_coe.mpr (List.mem_map_of_mem (restMember other otherMember))
  have namesApart : ∀ name ∈ names.reverse, name ∉ avoid := fun name member =>
    namesFresh name (List.mem_reverse.mp member)
  have firstReadable := componentReadable first firstMember
  have secondReadable := componentReadable second secondMember
  rcases guard_cases (reads.guards second secondMember) with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ |
    ⟨channel', datum, rfl⟩
  · cases fires <;> simp [readBack] at secondVal
  · cases fires <;> simp [readBack] at secondVal
  have secondNamed := secondReadable.named
  simp only [Named, Bool.and_eq_true] at secondNamed
  rcases guard_cases (reads.guards first firstMember) with ⟨channel, binder, body, rfl⟩ |
    ⟨channel, binder, body, rfl⟩ | ⟨_, _, rfl⟩
  · -- an input
    cases fires with
    | replicate => simp [readBack] at firstVal
    | input x y z received =>
    simp only [readBack, Process.input.injEq] at firstVal
    simp only [readBack, Process.output.injEq] at secondVal
    obtain ⟨rfl, rfl, rfl⟩ := firstVal
    obtain ⟨sameChannel, rfl⟩ := secondVal
    have firstNamed := firstReadable.named
    simp only [Named, Bool.and_eq_true] at firstNamed
    obtain rfl : channel' = channel := nameOf_injective (List.nodup_reverse.mpr namesNodup) namesApart
      secondNamed.1 firstNamed.1 (scoped_binary secondReadable.inScope).1 (scoped_binary firstReadable.inScope).1
      (avoided_binary secondReadable.avoided).1 (avoided_binary firstReadable.avoided).1 sameChannel
    have blockIn := block_process members objects componentsPerm
    have raw : PiRawStep (Prenex.restricts piBlock form.count
        (.collection .hashBag (.apply "PiInp" [channel', .lambda binder body] :: .apply "PiOut" [channel', datum] ::
          rest) none))
        (Prenex.restricts piBlock form.count (.collection .hashBag (instantiateBVar datum body :: rest) none)) :=
      piReactions.restricts_step _ (by
        simpa using PiRawStep.comm (elements := .apply "PiInp" [channel', .lambda binder body] ::
          .apply "PiOut" [channel', datum] :: rest) (tail := none) 0 (by simp) 0 (by simp) channel' binder body datum
          rfl rfl)
    have targetIn := process_of_raw blockIn raw
    obtain ⟨witness, valid⟩ := step_iff_raw.mpr raw
    have bodyScoped := scoped_lambda (scoped_binary firstReadable.inScope).2
    have bodyAvoided := avoided_lambda (avoided_binary firstReadable.avoided).2
    have datumScoped := (scoped_binary secondReadable.inScope).2
    have datumAvoided := (avoided_binary secondReadable.avoided).2
    have receivedFacts := instantiate_facts firstNamed.2 bodyScoped bodyAvoided secondNamed.2 datumScoped datumAvoided
    have restReadable : ∀ other ∈ rest, Readable avoid names.length other := fun other member =>
      (componentReadable other (restMember other member)).depth (by simp)
    obtain ⟨resultProcess', resultDenotes', reductReads⟩ := result_reads namesNodup namesFresh
      (fun other member => reads.guards other (restMember other member)) restReadable
      ((⟨receivedFacts.1, receivedFacts.2.1, receivedFacts.2.2⟩ : Readable avoid names.reverse.length _).depth
        (by simp))
      (readBack_receive avoid firstNamed.2 bodyScoped bodyAvoided secondNamed.2 datumScoped datumAvoided)
      lifts restFresh
    rw [namesLength] at reductReads
    have targetReadable : Readable avoid ([] : List Name).length
        (Prenex.restricts piBlock form.count (.collection .hashBag (instantiateBVar datum body :: rest) none)) := by
      refine Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexForm.Readable.restricts form.count
        (readable_bag fun element member => ?_)
      rcases List.mem_cons.mp member with rfl | inRest
      · exact ⟨receivedFacts.1, by simpa [namesLength] using receivedFacts.2.1, receivedFacts.2.2⟩
      · exact (reads.readable element (restMember element inRest))
    refine ⟨_, ⟨isState_of_process sourceIn, isState_of_process targetIn, _, _, witness,
      block_equivalent sourceIn members blockEquivalent.toEquationEquiv componentsPerm blockIn, isState_of_process blockIn, valid,
      isState_of_process targetIn, .refl _, rfl⟩, readBack avoid [] _, ?_, reduct_equivalent targetIn targetReadable⟩
    rw [bodyMinus] at resultDenotes
    simp only [add_zero] at resultDenotes
    exact reductReads.trans ((denotes_congruent resultDenotes' resultDenotes).trans
      ((Congruent.nilRight _).symm.trans reductCongruent.symm))
  · -- a server: a copy of its input, unfolded beside it, communicates
    cases fires with
    | input => simp [readBack] at firstVal
    | replicate x y z received =>
    simp only [readBack, Process.replicate.injEq] at firstVal
    simp only [readBack, Process.output.injEq] at secondVal
    obtain ⟨rfl, rfl, rfl⟩ := firstVal
    obtain ⟨sameChannel, rfl⟩ := secondVal
    have firstNamed := firstReadable.named
    simp only [Named, Bool.and_eq_true] at firstNamed
    have inputScoped := scoped_unary firstReadable.inScope
    have inputAvoided := avoided_unary firstReadable.avoided
    obtain rfl : channel' = channel := nameOf_injective (List.nodup_reverse.mpr namesNodup) namesApart
      secondNamed.1 firstNamed.1 (scoped_binary secondReadable.inScope).1 (scoped_binary inputScoped).1
      (avoided_binary secondReadable.avoided).1 (avoided_binary inputAvoided).1 sameChannel
    have blockIn := block_process members objects componentsPerm
    set input := Pattern.apply "PiInp" [channel', .lambda binder body] with inputIs
    set server := Pattern.apply "PiRep" [input] with serverIs
    set output := Pattern.apply "PiOut" [channel', datum] with outputIs
    -- the block with the copy is the block
    have serverTyped := members _ firstMember
    have inputTyped := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.replicate_argument_typed
      (block := Blocks.piRepBlock) serverTyped
    have unfoldedMembers : Members piCalc piBlock PiPrenexForms.names
        (List.replicate form.count (.base "Name") ++ []) (input :: output :: server :: rest) := by
      intro element member
      simp only [List.mem_cons] at member
      rcases member with rfl | rfl | rfl | inRest
      · exact inputTyped
      · exact members _ secondMember
      · exact serverTyped
      · exact members element (restMember element inRest)
    have unfoldedIn : processes (Prenex.restricts piBlock form.count
        (.collection .hashBag (input :: output :: server :: rest) none)) := by
      apply domain_of_typed (restricts_typed (block := piBlock) form.count
        (bag_typed (block := piBlock) (rest := none) unfoldedMembers))
      rw [isObject_restricts, isObject_bag]
      intro element member
      simp only [List.mem_cons] at member
      rcases member with rfl | rfl | rfl | inRest
      · have serverObject := objects _ firstMember
        simpa [serverIs, isObjectPattern, isObjectPatternList] using serverObject
      · exact objects _ secondMember
      · exact objects _ firstMember
      · exact objects element (restMember element inRest)
    have unfolding : EquationEquiv (engineBasePremises RelationEnv.empty) piCalc
        (Prenex.restricts piBlock form.count (.collection .hashBag (server :: output :: rest) none))
        (Prenex.restricts piBlock form.count (.collection .hashBag (input :: output :: server :: rest) none)) := by
      refine Mettapedia.GSLT.LanguageDef.RestrictionBlocks.restricts_equation (block := piBlock) form.count ?_
      have unfoldServer := (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.unfold_equivalent
        (block := Blocks.piRepBlock) inputTyped).toEquationEquiv
      have inBag := Mettapedia.GSLT.LanguageDef.EquationSemantics.equationEquiv_fill
        (.collection .hashBag [] .hole (output :: rest) none) unfoldServer
      simp only [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill, List.nil_append] at inBag
      have nestedTyped : HasType piCalc PiPrenexForms.names (List.replicate form.count (.base "Name") ++ [])
          (.collection .hashBag ([] ++ .collection .hashBag [input, server] none :: output :: rest) none)
          (.base "Proc") := by
        refine bag_typed (block := piBlock) (rest := none) fun element member => ?_
        simp only [List.nil_append, List.mem_cons] at member
        rcases member with rfl | rfl | inRest
        · exact bag_typed (block := piBlock) (rest := none) fun inner innerMember => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at innerMember
            rcases innerMember with rfl | rfl
            · exact inputTyped
            · exact serverTyped
        · exact members _ secondMember
        · exact members element (restMember element inRest)
      have flattened := Mettapedia.GSLT.LanguageDef.EquationSemantics.derivedInstance_equivalent
        (base := engineBasePremises RelationEnv.empty) (Blocks.piBlockSignature.flatten nestedTyped)
      simp only [List.nil_append, List.cons_append] at flattened
      have permuted := Mettapedia.GSLT.LanguageDef.EquationSemantics.derivedInstance_equivalent
        (base := engineBasePremises RelationEnv.empty)
        (Mettapedia.GSLT.LanguageDef.EquationSemantics.DerivedInstance.bagPerm_of_sorted
          ⟨_, _, bag_typed (block := piBlock) (rest := none)
            (fun element member => unfoldedMembers element ((List.Perm.swap output server rest).cons input |>.subset
              member))⟩
          ((List.Perm.swap output server rest).cons input))
      exact Relation.EqvGen.trans _ _ _ inBag (Relation.EqvGen.trans _ _ _ flattened permuted)
    have raw : PiRawStep (Prenex.restricts piBlock form.count
        (.collection .hashBag (input :: output :: server :: rest) none))
        (Prenex.restricts piBlock form.count (.collection .hashBag (instantiateBVar datum body :: server :: rest)
          none)) :=
      piReactions.restricts_step _ (by
        simpa using PiRawStep.comm (elements := input :: output :: server :: rest) (tail := none) 0 (by simp) 0
          (by simp) channel' binder body datum rfl rfl)
    have targetIn := process_of_raw unfoldedIn raw
    obtain ⟨witness, valid⟩ := step_iff_raw.mpr raw
    have bodyScoped := scoped_lambda (scoped_binary inputScoped).2
    have bodyAvoided := avoided_lambda (avoided_binary inputAvoided).2
    have datumScoped := (scoped_binary secondReadable.inScope).2
    have datumAvoided := (avoided_binary secondReadable.avoided).2
    have receivedFacts := instantiate_facts firstNamed.2 bodyScoped bodyAvoided secondNamed.2 datumScoped datumAvoided
    have serverReadable : Readable avoid names.length server :=
      (componentReadable _ firstMember).depth (by simp)
    have serverGuard : isGuard server = true := rfl
    have serverPrime : toPrime avoid names.reverse server =
        ⟨.replicate (nameOf names.reverse channel') (Mettapedia.FreshString.fresh (avoid ∪ names.reverse.toFinset))
          (readBack avoid (Mettapedia.FreshString.fresh (avoid ∪ names.reverse.toFinset) :: names.reverse) body),
          .replicate _ _ _⟩ := by
      apply Subtype.ext
      rw [toPrime_val serverGuard]
      simp only [serverIs, inputIs, readBack]
    have othersReadable : ∀ other ∈ server :: rest, Readable avoid names.length other := fun other member => by
      rcases List.mem_cons.mp member with rfl | inRest
      · exact serverReadable
      · exact (componentReadable other (restMember other inRest)).depth (by simp)
    have othersFresh : Disjoint lifted (names.toFinset ∪
        (parList ((server :: rest).map (readBack avoid names.reverse))).freeNames) := by
      refine liftedFresh.mono_right (Finset.union_subset_union (Finset.Subset.refl _) fun name free => ?_)
      obtain ⟨process, member, inside⟩ := mem_freeNames_parList.mp free
      obtain ⟨other, otherMember, rfl⟩ := List.mem_map.mp member
      rcases List.mem_cons.mp otherMember with rfl | inRest
      · refine Mettapedia.OSLF.NativeTypes.GeneratedLogic.Pi.LeastPartners.Molecule.mem_bodyNames.mpr
          ⟨toPrime avoid names.reverse server, ?_, ?_⟩
        · exact Multiset.mem_coe.mpr (List.mem_map_of_mem firstMember)
        · rw [toPrime_val (reads.guards _ firstMember)]
          exact inside
      · refine Mettapedia.OSLF.NativeTypes.GeneratedLogic.Pi.LeastPartners.Molecule.mem_bodyNames.mpr
          ⟨toPrime avoid names.reverse other, ?_, by rwa [toPrime_val (reads.guards other (restMember other inRest))]⟩
        exact Multiset.mem_coe.mpr (List.mem_map_of_mem (restMember other inRest))
    obtain ⟨resultProcess', resultDenotes', reductReads⟩ := result_reads namesNodup namesFresh
      (fun other member => by
        rcases List.mem_cons.mp member with rfl | inRest
        · exact serverGuard
        · exact reads.guards other (restMember other inRest)) othersReadable
      ((⟨receivedFacts.1, receivedFacts.2.1, receivedFacts.2.2⟩ : Readable avoid names.reverse.length _).depth
        (by simp))
      (readBack_receive avoid firstNamed.2 bodyScoped bodyAvoided secondNamed.2 datumScoped datumAvoided)
      lifts othersFresh
    rw [namesLength] at reductReads
    have targetReadable : Readable avoid ([] : List Name).length
        (Prenex.restricts piBlock form.count (.collection .hashBag (instantiateBVar datum body :: server :: rest)
          none)) := by
      refine Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexForm.Readable.restricts form.count
        (readable_bag fun element member => ?_)
      rcases List.mem_cons.mp member with rfl | inOthers
      · exact ⟨receivedFacts.1, by simpa [namesLength] using receivedFacts.2.1, receivedFacts.2.2⟩
      · exact (othersReadable element inOthers).depth (by simp [namesLength])
    refine ⟨_, ⟨isState_of_process sourceIn, isState_of_process targetIn, _, _, witness,
      .trans _ _ _ (block_equivalent sourceIn members blockEquivalent.toEquationEquiv componentsPerm blockIn)
        (equivalent_of_equation blockIn unfoldedIn unfolding), isState_of_process unfoldedIn, valid,
      isState_of_process targetIn, .refl _, rfl⟩, readBack avoid [] _, ?_, reduct_equivalent targetIn targetReadable⟩
    rw [bodyMinus] at resultDenotes
    have sameResult : ↑(rest.map (toPrime avoid names.reverse)) +
        {⟨.replicate (nameOf names.reverse channel') (Mettapedia.FreshString.fresh (avoid ∪ names.reverse.toFinset))
          (readBack avoid (Mettapedia.FreshString.fresh (avoid ∪ names.reverse.toFinset) :: names.reverse) body),
          .replicate _ _ _⟩} + components =
        ↑((server :: rest).map (toPrime avoid names.reverse)) + components := by
      rw [List.map_cons, serverPrime, ← Multiset.cons_coe, ← Multiset.singleton_add]
      abel
    rw [sameResult] at resultDenotes
    exact reductReads.trans ((denotes_congruent resultDenotes' resultDenotes).trans
      ((Congruent.nilRight _).symm.trans reductCongruent.symm))
  · cases fires <;> simp [readBack] at firstVal

/-! ## Reductions of translations are named reductions -/

/-- **Copies of servers' inputs beside the servers are absorbed**, in the named calculus. -/
theorem parList_absorb {servers : List Process} : ∀ {copies : List Process},
    (∀ copy ∈ copies, ∃ x y P, copy = .input x y P ∧ Process.replicate x y P ∈ servers) →
      (parList (servers ++ copies) ≅ parList servers)
  | [], _ => by
      rw [List.append_nil]
      exact Congruent.refl _
  | copy :: copies, absorbed => by
      obtain ⟨x, y, P, rfl, member⟩ := absorbed _ List.mem_cons_self
      have rest := parList_absorb (copies := copies) fun other inOthers =>
        absorbed other (List.mem_cons_of_mem _ inOthers)
      have serverPerm := List.perm_cons_erase member
      refine (parList_perm List.perm_middle).trans ((Congruent.par (Congruent.refl _) rest).trans ?_)
      refine (Congruent.par (Congruent.refl _) (parList_perm serverPerm)).trans ?_
      refine ((Congruent.assoc _ _ _).symm.trans (Congruent.par ⟨.symm _ _ (.replicate_unfold x y P)⟩
        (Congruent.refl _))).trans ?_
      exact parList_perm serverPerm.symm

open Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexForm (Reads decompose_reads freshNames freshNames_length
  freshNames_nodup freshNames_fresh reflect_presented)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPrenexForms (names names_context presentations)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (canonR replicationPresentations restricts_typed body_typed)

/-- **A reduction of a translation is a named reduction**, to a process whose translation is equivalent to the
reduct: the reduction is a communication of a presentation of the canonical form, which is one of the translation's
own guards beside copies of its servers' inputs, and these copies are absorbed by the servers. -/
theorem reduces_named {source : Process} {target : Pattern} (step : Reduces (piToPattern source) target) :
    ∃ reduct : Process, Nonempty (source ⇝ reduct) ∧
      ObjectEquivalent RelationEnv.empty piCalc reading (piToPattern reduct) target := by
  classical
  have sourceIn := translation_process source
  obtain ⟨shown, presented, next, member, nextStep, equivalent⟩ := reduces_canonical sourceIn step
  have raw := rawSuccessors_sound _ (Nat.lt_succ_self _) member
  have presentedR : shown ∈ replicationPresentations Blocks.piRepBlock 2
      (canonR Blocks.piRepBlock (piToPattern source)) := by
    have inPresentations := presented
    unfold canon presentations at inPresentations
    rw [if_pos sourceIn] at inPresentations
    exact inPresentations
  have typedX := (typed_of_domain sourceIn).1
  have objectX := (typed_of_domain sourceIn).2
  have readable₀ : Readable source.freeNames ([] : List Name).length (piToPattern source) :=
    readable_piToPattern (Finset.Subset.refl _)
  have reads₀ := decompose_reads source.freeNames _ [] (Nat.lt_succ_self _) readable₀
  obtain ⟨copies, copiesIn, target', stepped, equivalent'⟩ :=
    reflect_presented names_context typedX objectX reads₀.guards presentedR raw
  set form := decompose piBlock (piToPattern source) with formIs
  -- reading back, past the reduct's names
  set avoid := source.freeNames ∪ (freeVars target').toFinset with avoidIs
  have readable : Readable avoid ([] : List Name).length (piToPattern source) :=
    readable_piToPattern Finset.subset_union_left
  have reads := decompose_reads avoid _ [] (Nat.lt_succ_self _) readable
  set freshOnes := freshNames avoid form.count with freshOnesIs
  have freshLength : freshOnes.length = form.count := freshNames_length _ _
  have freshNodup : freshOnes.Nodup := freshNames_nodup _ _
  have freshAvoid : ∀ name ∈ freshOnes, name ∉ avoid ∧ name ∉ ([] : List Name) := fun name inNames =>
    ⟨freshNames_fresh _ inNames, by simp⟩
  -- the copies are inputs of servers among the guards
  have copyShape : ∀ copy ∈ copies, ∃ channel binder body,
      copy = .apply "PiInp" [channel, .lambda binder body] := by
    intro copy inCopies
    have serverGuard := reads.guards _ (copiesIn copy inCopies)
    rcases Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexForm.guard_cases serverGuard with
      ⟨_, _, _, equal⟩ | ⟨channel, binder, body, equal⟩ | ⟨_, _, equal⟩
    · simp at equal
    · simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at equal
      exact ⟨channel, binder, body, equal⟩
    · simp at equal
  have copyReadable : ∀ copy ∈ copies, Readable avoid (([] : List Name).length + form.count) copy := by
    intro copy inCopies
    have serverReadable := reads.readable _ (copiesIn copy inCopies)
    obtain ⟨channel, binder, body, rfl⟩ := copyShape copy inCopies
    exact ⟨by simpa [Named] using serverReadable.named,
      by simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using serverReadable.inScope,
      fun name free => serverReadable.avoided name (by simpa [freeVars] using free)⟩
  have allReadable : ∀ component ∈ form.components ++ copies,
      Readable avoid (([] : List Name).length + freshOnes.length) component := by
    intro component inAll
    rw [freshLength]
    rcases List.mem_append.mp inAll with inForm | inCopies
    · exact reads.readable component inForm
    · exact copyReadable component inCopies
  have blockReads := Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexForm.readBack_toPattern freshOnes
    allReadable freshNodup freshAvoid
  set readOne := readBack avoid (freshOnes.reverse ++ []) with readOneIs
  have absorbed : (parList ((form.components ++ copies).map readOne) ≅
      parList (form.components.map readOne)) := by
    rw [List.map_append]
    refine parList_absorb fun copy inCopies => ?_
    obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inCopies
    obtain ⟨channel, binder, body, rfl⟩ := copyShape original inOriginal
    have server := List.mem_map_of_mem (f := readOne) (copiesIn _ inOriginal)
    have inputRead : readOne (.apply "PiInp" [channel, .lambda binder body]) =
        .input (nameOf (freshOnes.reverse ++ []) channel)
          (Mettapedia.FreshString.fresh (avoid ∪ (freshOnes.reverse ++ []).toFinset))
          (readBack avoid (Mettapedia.FreshString.fresh (avoid ∪ (freshOnes.reverse ++ []).toFinset) ::
            (freshOnes.reverse ++ [])) body) := by
      simp only [readOneIs, readBack]
    have serverRead : readOne (.apply "PiRep" [.apply "PiInp" [channel, .lambda binder body]]) =
        .replicate (nameOf (freshOnes.reverse ++ []) channel)
          (Mettapedia.FreshString.fresh (avoid ∪ (freshOnes.reverse ++ []).toFinset))
          (readBack avoid (Mettapedia.FreshString.fresh (avoid ∪ (freshOnes.reverse ++ []).toFinset) ::
            (freshOnes.reverse ++ [])) body) := by
      simp only [readOneIs, readBack]
    rw [serverRead] at server
    exact ⟨_, _, _, inputRead, server⟩
  have sourceReads := reads.reads freshOnes freshLength freshNodup freshAvoid
  have blockIs : Prenex.toPattern piBlock ⟨freshOnes.length, form.components ++ copies⟩ =
      Prenex.restricts piBlock form.count (Prenex.body piBlock (form.components ++ copies)) := by
    rw [freshLength]
    rfl
  rw [blockIs] at blockReads
  have sourceBlock : (source ≅
      readBack avoid [] (Prenex.restricts piBlock form.count (Prenex.body piBlock (form.components ++ copies)))) :=
    (readBack_piToPattern Finset.subset_union_left).symm.trans
      (sourceReads.trans ((nuList_congruent freshOnes absorbed).symm.trans blockReads.symm))
  -- the communication reads back as a named reduction
  have blockReadable : Readable avoid ([] : List Name).length
      (Prenex.restricts piBlock form.count (Prenex.body piBlock (form.components ++ copies))) :=
    Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexForm.Readable.restricts form.count
      (Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexForm.Readable.body fun component inAll => by
        have := allReadable component inAll
        rwa [freshLength] at this)
  obtain ⟨targetNamed, namedStep⟩ := rawStep_readBack avoid stepped [] blockReadable.named blockReadable.inScope
    blockReadable.avoided
  refine ⟨readBack avoid [] target', reduces_of_congruent sourceBlock namedStep (Congruent.refl _), ?_⟩
  -- the reduct reads as the communication's target
  have blockIn : processes (Prenex.restricts piBlock form.count (Prenex.body piBlock (form.components ++ copies))) := by
    obtain ⟨members, -⟩ := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.decompose_sound (block := piBlock) typedX
    apply domain_of_typed
    · refine restricts_typed (block := piBlock) form.count (body_typed (block := piBlock) fun component inAll => ?_)
      rcases List.mem_append.mp inAll with inForm | inCopies
      · exact members component inForm
      · exact Mettapedia.GSLT.LanguageDef.RestrictionBlocks.replicate_argument_typed (block := Blocks.piRepBlock)
          (members _ (copiesIn component inCopies))
    · exact named_object _ (Nat.lt_succ_self _) blockReadable.named
  have targetIn := process_of_raw blockIn stepped
  have nextIn := PiPartners.reduces_process sourceIn nextStep
  have targetReadable : Readable avoid ([] : List Name).length target' :=
    ⟨targetNamed, by simpa using (typed_of_domain targetIn).1.isWellScopedAt,
      fun name free => Finset.mem_union_right _ (List.mem_toFinset.mpr free)⟩
  exact .trans _ _ _ (reduct_equivalent targetIn targetReadable)
    (.trans _ _ _ (equivalent_of_equation targetIn nextIn equivalent') (.symm _ _ equivalent))

/-! ## Reductions up to the laws -/

open Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPartners (par par_process par_congr reduces_process frontDoor
  isPartnerLabel partnerLabel partnerContext exists_hole isPartnerLabel_partnerLabel step_partner_iff
  closedUnder finiteUpTo)

theorem reduces_source {first second target : Pattern} (firstIn : processes first) (secondIn : processes second)
    (equivalent : ObjectEquivalent RelationEnv.empty piCalc reading first second) (step : Reduces first target) :
    Reduces second target :=
  (referenceStructure_saturated RelationEnv.empty piCalc reading).stepSource
    (Indistinct.of_states (isState_of_process firstIn) (isState_of_process secondIn) equivalent) step

theorem reduces_target {source first second : Pattern} (firstIn : processes first) (secondIn : processes second)
    (equivalent : ObjectEquivalent RelationEnv.empty piCalc reading first second) (step : Reduces source first) :
    Reduces source second :=
  (referenceStructure_saturated RelationEnv.empty piCalc reading).stepTarget
    (Indistinct.of_states (isState_of_process firstIn) (isState_of_process secondIn) equivalent) step

/-- **A translation of a parallel composition is the bag of the two.** -/
theorem par_translation (first second : Process) :
    ObjectEquivalent RelationEnv.empty piCalc reading (piToPattern (first ||| second))
      (par (piToPattern first) (piToPattern second)) :=
  equivalent_of_equation (translation_process _)
    (par_process (translation_process first) (translation_process second))
    (.symm _ _ (Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance.piPar_equivalent_bag
      (piToPattern_hasType first) (piToPattern_hasType second)))

theorem par_congr_right {first partner partner' : Pattern} (firstIn : processes first) (partnerIn : processes partner)
    (partnerIn' : processes partner')
    (equivalent : ObjectEquivalent RelationEnv.empty piCalc reading partner partner') :
    ObjectEquivalent RelationEnv.empty piCalc reading (par first partner) (par first partner') := by
  have swap : ∀ {left right : Pattern}, processes left → processes right →
      ObjectEquivalent RelationEnv.empty piCalc reading (par left right) (par right left) := fun leftIn rightIn =>
    equivalent_of_equation (par_process leftIn rightIn) (par_process rightIn leftIn)
      (Mettapedia.GSLT.LanguageDef.EquationSemantics.derivedInstance_equivalent
        (Mettapedia.GSLT.LanguageDef.EquationSemantics.DerivedInstance.bagPerm_of_sorted
          ⟨PiPrenexForms.names, [], (typed_of_domain (par_process leftIn rightIn)).1⟩ (List.Perm.swap _ _ [])))
  exact .trans _ _ _ (swap firstIn partnerIn) (.trans _ _ _ (par_congr partnerIn partnerIn' firstIn equivalent)
    (swap partnerIn' firstIn))

/-- **A named process read back from a named process pattern**, its translation equivalent to the pattern. -/
theorem named_translation {partner : Pattern} (partnerIn : processes partner) (named : Named partner = true) :
    ∃ process : Process, ObjectEquivalent RelationEnv.empty piCalc reading (piToPattern process) partner :=
  ⟨readBack (freeVars partner).toFinset [] partner, reduct_equivalent partnerIn
    ⟨named, by simpa using (typed_of_domain partnerIn).1.isWellScopedAt,
      fun name free => List.mem_toFinset.mpr free⟩⟩

/-! ## Saturated bisimilarity beside named partners -/

/-- **A saturated reduction bisimulation beside named partners**: beside every named process, a reduction of either
side is matched by one of the other, to related processes. -/
def IsNamedSaturated (relation : Pattern → Pattern → Prop) : Prop :=
  ∀ ⦃first second⦄, relation first second → ∀ partner, processes partner → Named partner = true →
    (∀ next, Reduces (par first partner) next →
      ∃ matched, Reduces (par second partner) matched ∧ relation next matched) ∧
    (∀ next, Reduces (par second partner) next →
      ∃ matched, Reduces (par first partner) matched ∧ relation matched next)

/-- **Saturated reduction bisimilarity beside named partners.** -/
def NamedSaturatedBisimilar (first second : Pattern) : Prop :=
  ∃ relation, IsNamedSaturated relation ∧
    (∀ ⦃left right⦄, relation left right → processes left ∧ processes right) ∧ relation first second

theorem namedSaturated_of_saturated {first second : Pattern}
    (bisimilar : PiPartners.SaturatedReductionBisimilar first second) : NamedSaturatedBisimilar first second := by
  obtain ⟨relation, saturated, inProcesses, related⟩ := bisimilar
  exact ⟨relation, fun _ _ relatedHere partner partnerIn _ => saturated relatedHere partner partnerIn, inProcesses,
    related⟩

/-- **The named calculus's saturated bisimilarity is closed under structural congruence.** -/
theorem saturated_congruent {first first' second second' : Process} (bisimilar : SaturatedReductionBisimilar first second)
    (left : first ≅ first') (right : second ≅ second') : SaturatedReductionBisimilar first' second' := by
  obtain ⟨relation, saturated, related⟩ := bisimilar
  refine ⟨fun a b => ∃ a' b', (a ≅ a') ∧ relation a' b' ∧ (b' ≅ b), ?_, first, second, left.symm, related, right⟩
  rintro a b ⟨a', b', aCongruent, relatedHere, bCongruent⟩ context
  refine ⟨fun next step => ?_, fun next step => ?_⟩
  · obtain ⟨matched, step', relatedNext⟩ := (saturated relatedHere context).1 next
      (reduces_of_congruent (Congruent.par aCongruent.symm (Congruent.refl _)) step (Congruent.refl _))
    exact ⟨matched, reduces_of_congruent (Congruent.par bCongruent.symm (Congruent.refl _)) step' (Congruent.refl _),
      next, matched, Congruent.refl _, relatedNext, Congruent.refl _⟩
  · obtain ⟨matched, step', relatedNext⟩ := (saturated relatedHere context).2 next
      (reduces_of_congruent (Congruent.par bCongruent (Congruent.refl _)) step (Congruent.refl _))
    exact ⟨matched, reduces_of_congruent (Congruent.par aCongruent (Congruent.refl _)) step' (Congruent.refl _),
      matched, next, Congruent.refl _, relatedNext, Congruent.refl _⟩

/-- **Saturated bisimilarity beside named partners, of translations, is the named calculus's.** -/
theorem named_of_namedSaturated {first second : Process}
    (bisimilar : NamedSaturatedBisimilar (piToPattern first) (piToPattern second)) :
    SaturatedReductionBisimilar first second := by
  obtain ⟨relation, saturated, inProcesses, related⟩ := bisimilar
  refine ⟨fun left right => ∃ left' right' leftPattern rightPattern, (left ≅ left') ∧ (right ≅ right') ∧
      relation leftPattern rightPattern ∧
      ObjectEquivalent RelationEnv.empty piCalc reading (piToPattern left') leftPattern ∧
      ObjectEquivalent RelationEnv.empty piCalc reading (piToPattern right') rightPattern, ?_,
    first, second, _, _, Congruent.refl _, Congruent.refl _, related, .refl _, .refl _⟩
  rintro left right ⟨left', right', leftPattern, rightPattern, leftCongruent, rightCongruent, relatedHere,
    leftEquivalent, rightEquivalent⟩ context
  obtain ⟨leftIn, rightIn⟩ := inProcesses relatedHere
  have contextIn := translation_process context
  have leftBag : ObjectEquivalent RelationEnv.empty piCalc reading (piToPattern (left' ||| context))
      (par leftPattern (piToPattern context)) :=
    .trans _ _ _ (par_translation _ _) (par_congr (translation_process left') leftIn contextIn leftEquivalent)
  have rightBag : ObjectEquivalent RelationEnv.empty piCalc reading (piToPattern (right' ||| context))
      (par rightPattern (piToPattern context)) :=
    .trans _ _ _ (par_translation _ _) (par_congr (translation_process right') rightIn contextIn rightEquivalent)
  refine ⟨fun next step => ?_, fun next step => ?_⟩
  · obtain ⟨target, targetStep, next', nextCongruent, nextEquivalent⟩ := named_reduces
      (reduces_of_congruent (Congruent.par leftCongruent.symm (Congruent.refl _)) step (Congruent.refl _))
    have stepped := reduces_source (translation_process _) (par_process leftIn contextIn) leftBag targetStep
    obtain ⟨matched, matchedStep, relatedNext⟩ :=
      (saturated relatedHere _ contextIn (named_piToPattern context)).1 target stepped
    have back := reduces_source (par_process rightIn contextIn) (translation_process _) (.symm _ _ rightBag)
      matchedStep
    obtain ⟨reduct, reductStep, reductEquivalent⟩ := reduces_named back
    exact ⟨reduct, reduces_of_congruent (Congruent.par rightCongruent (Congruent.refl _)) reductStep
      (Congruent.refl _), next', reduct, target, matched, nextCongruent.symm, Congruent.refl _, relatedNext,
      nextEquivalent, reductEquivalent⟩
  · obtain ⟨target, targetStep, next', nextCongruent, nextEquivalent⟩ := named_reduces
      (reduces_of_congruent (Congruent.par rightCongruent.symm (Congruent.refl _)) step (Congruent.refl _))
    have stepped := reduces_source (translation_process _) (par_process rightIn contextIn) rightBag targetStep
    obtain ⟨matched, matchedStep, relatedNext⟩ :=
      (saturated relatedHere _ contextIn (named_piToPattern context)).2 target stepped
    have back := reduces_source (par_process leftIn contextIn) (translation_process _) (.symm _ _ leftBag)
      matchedStep
    obtain ⟨reduct, reductStep, reductEquivalent⟩ := reduces_named back
    exact ⟨reduct, reduces_of_congruent (Congruent.par leftCongruent (Congruent.refl _)) reductStep
      (Congruent.refl _), reduct, next', matched, target, Congruent.refl _, nextCongruent.symm, relatedNext,
      reductEquivalent, nextEquivalent⟩

/-- **The named calculus's saturated bisimilarity is `piCalc`'s beside named partners**, on translations. -/
theorem namedSaturated_of_named {first second : Process} (bisimilar : SaturatedReductionBisimilar first second) :
    NamedSaturatedBisimilar (piToPattern first) (piToPattern second) := by
  refine ⟨fun left right => processes left ∧ processes right ∧ ∃ left' right',
      SaturatedReductionBisimilar left' right' ∧
      ObjectEquivalent RelationEnv.empty piCalc reading (piToPattern left') left ∧
      ObjectEquivalent RelationEnv.empty piCalc reading (piToPattern right') right, ?_,
    fun _ _ both => ⟨both.1, both.2.1⟩, translation_process _, translation_process _, first, second, bisimilar,
    .refl _, .refl _⟩
  rintro left right ⟨leftIn, rightIn, left', right', bisimilarHere, leftEquivalent, rightEquivalent⟩ partner partnerIn
    partnerNamed
  obtain ⟨context, contextEquivalent⟩ := named_translation partnerIn partnerNamed
  have contextIn := translation_process context
  have leftBag : ObjectEquivalent RelationEnv.empty piCalc reading (piToPattern (left' ||| context))
      (par left partner) :=
    .trans _ _ _ (par_translation _ _) (.trans _ _ _
      (par_congr (translation_process left') leftIn contextIn leftEquivalent)
      (par_congr_right leftIn contextIn partnerIn contextEquivalent))
  have rightBag : ObjectEquivalent RelationEnv.empty piCalc reading (piToPattern (right' ||| context))
      (par right partner) :=
    .trans _ _ _ (par_translation _ _) (.trans _ _ _
      (par_congr (translation_process right') rightIn contextIn rightEquivalent)
      (par_congr_right rightIn contextIn partnerIn contextEquivalent))
  obtain ⟨relation, saturated, related⟩ := bisimilarHere
  refine ⟨fun next step => ?_, fun next step => ?_⟩
  · have stepped := reduces_source (par_process leftIn partnerIn) (translation_process _) (.symm _ _ leftBag) step
    obtain ⟨reduct, reductStep, reductEquivalent⟩ := reduces_named stepped
    obtain ⟨matched, matchedStep, relatedNext⟩ := (saturated related context).1 reduct reductStep
    obtain ⟨target, targetStep, matched', matchedCongruent, matchedEquivalent⟩ := named_reduces matchedStep
    have back := reduces_source (translation_process _) (par_process rightIn partnerIn) rightBag targetStep
    exact ⟨target, back, reduces_process (par_process leftIn partnerIn) step,
      reduces_process (par_process rightIn partnerIn) back, reduct, matched',
      saturated_congruent ⟨relation, saturated, relatedNext⟩ (Congruent.refl _) matchedCongruent.symm,
      reductEquivalent, matchedEquivalent⟩
  · have stepped := reduces_source (par_process rightIn partnerIn) (translation_process _) (.symm _ _ rightBag) step
    obtain ⟨reduct, reductStep, reductEquivalent⟩ := reduces_named stepped
    obtain ⟨matched, matchedStep, relatedNext⟩ := (saturated related context).2 reduct reductStep
    obtain ⟨target, targetStep, matched', matchedCongruent, matchedEquivalent⟩ := named_reduces matchedStep
    have back := reduces_source (translation_process _) (par_process leftIn partnerIn) leftBag targetStep
    exact ⟨target, back, reduces_process (par_process leftIn partnerIn) back,
      reduces_process (par_process rightIn partnerIn) step, matched', reduct,
      saturated_congruent ⟨relation, saturated, relatedNext⟩ matchedCongruent.symm (Congruent.refl _),
      matchedEquivalent, reductEquivalent⟩

/-- **π's saturated reduction bisimilarity, named, is `piCalc`'s beside named partners.** -/
theorem saturated_iff_namedSaturated {first second : Process} :
    SaturatedReductionBisimilar first second ↔ NamedSaturatedBisimilar (piToPattern first) (piToPattern second) :=
  ⟨namedSaturated_of_named, named_of_namedSaturated⟩

/-- **`piCalc`'s saturated bisimilarity beside every partner implies the named calculus's.** -/
theorem named_of_saturated {first second : Process}
    (bisimilar : PiPartners.SaturatedReductionBisimilar (piToPattern first) (piToPattern second)) :
    SaturatedReductionBisimilar first second :=
  named_of_namedSaturated (namedSaturated_of_saturated bisimilar)

/-! ## Named partners at the front door -/

/-- Whether a partner label's partner is a named process. -/
def namedPartner : StepLabel → Bool
  | .context _ (.collection .hashBag [_, partner] none) .any => Named partner
  | _ => false

/-- **A named partner's label**: a partner label whose partner is named. -/
def isNamedPartnerLabel (label : StepLabel) : Bool := isPartnerLabel label && namedPartner label

theorem isPartnerLabel_of_named {label : StepLabel} (named : isNamedPartnerLabel label = true) :
    isPartnerLabel label = true := by
  simp only [isNamedPartnerLabel, Bool.and_eq_true] at named
  exact named.1

theorem exists_of_isNamedPartnerLabel {label : StepLabel} (named : isNamedPartnerLabel label = true) :
    ∃ hole partner, label = partnerLabel hole partner ∧
      Mettapedia.OSLF.NativeTypes.GeneratedLogic.avoidsHole hole partner = true ∧
        processes partner ∧ Named partner = true := by
  obtain ⟨hole, partner, rfl, avoids, partnerIn⟩ :=
    PiPartners.exists_of_isPartnerLabel (isPartnerLabel_of_named named)
  simp only [isNamedPartnerLabel, Bool.and_eq_true] at named
  exact ⟨hole, partner, rfl, avoids, partnerIn, by simpa [namedPartner, partnerLabel, partnerContext] using named.2⟩

theorem isNamedPartnerLabel_partnerLabel {hole : String} {partner : Pattern}
    (avoids : Mettapedia.OSLF.NativeTypes.GeneratedLogic.avoidsHole hole partner = true)
    (partnerIn : processes partner) (named : Named partner = true) :
    isNamedPartnerLabel (partnerLabel hole partner) = true := by
  have partnerOf := isPartnerLabel_partnerLabel avoids partnerIn
  simp only [isNamedPartnerLabel, partnerOf, Bool.true_and]
  simpa [namedPartner, partnerLabel, partnerContext] using named

theorem closedUnderNamed : frontDoor.ClosedUnder isNamedPartnerLabel processes :=
  fun _ _ _ sourceIn named step => closedUnder sourceIn (isPartnerLabel_of_named named) step

theorem finiteUpToNamed :
    frontDoor.FiniteUpTo isNamedPartnerLabel processes (Indistinct RelationEnv.empty piCalc reading) :=
  fun source sourceIn label named => finiteUpTo source sourceIn label (isPartnerLabel_of_named named)

/-- **Native types under named partners are forward bisimilarity under named partners.** -/
theorem agree_iff_forwardBisimilar_named {first second : Pattern} (firstIn : processes first)
    (secondIn : processes second) :
    frontDoor.AgreeOn (Formula.forwardOn isNamedPartnerLabel) first second ↔
      frontDoor.ForwardBisimilar isNamedPartnerLabel first second :=
  NativeStructure.agree_iff_forwardBisimilar (referenceStructure_saturated RelationEnv.empty piCalc reading)
    finiteUpToNamed closedUnderNamed firstIn secondIn

/-- **Forward bisimilarity under named partners is saturated bisimilarity beside named partners.** -/
theorem forwardBisimilar_iff_namedSaturated {first second : Pattern} (firstIn : processes first)
    (secondIn : processes second) :
    frontDoor.ForwardBisimilar isNamedPartnerLabel first second ↔ NamedSaturatedBisimilar first second := by
  constructor
  · rintro ⟨relation, bisimulation, related⟩
    refine ⟨fun left right => processes left ∧ processes right ∧ relation left right, ?_,
      fun _ _ both => ⟨both.1, both.2.1⟩, firstIn, secondIn, related⟩
    rintro left right ⟨leftIn, rightIn, relatedHere⟩ partner partnerIn named
    obtain ⟨hole, avoids⟩ := exists_hole partnerIn
    have admitted := isNamedPartnerLabel_partnerLabel avoids partnerIn named
    refine ⟨fun next step => ?_, fun next step => ?_⟩
    · obtain ⟨matched, step', relatedNext⟩ := bisimulation.forth relatedHere admitted
        ((step_partner_iff avoids partnerIn leftIn).mpr step)
      exact ⟨matched, (step_partner_iff avoids partnerIn rightIn).mp step',
        closedUnderNamed leftIn admitted ((step_partner_iff avoids partnerIn leftIn).mpr step),
        closedUnderNamed rightIn admitted step', relatedNext⟩
    · obtain ⟨matched, step', relatedNext⟩ := bisimulation.back relatedHere admitted
        ((step_partner_iff avoids partnerIn rightIn).mpr step)
      exact ⟨matched, (step_partner_iff avoids partnerIn leftIn).mp step',
        closedUnderNamed leftIn admitted step',
        closedUnderNamed rightIn admitted ((step_partner_iff avoids partnerIn rightIn).mpr step), relatedNext⟩
  · rintro ⟨relation, saturated, inProcesses, related⟩
    refine ⟨relation, ⟨?_, ?_⟩, related⟩
    · intro left right label next relatedHere named step
      obtain ⟨hole, partner, rfl, avoids, partnerIn, partnerNamed⟩ := exists_of_isNamedPartnerLabel named
      obtain ⟨leftIn, rightIn⟩ := inProcesses relatedHere
      obtain ⟨matched, step', relatedNext⟩ := (saturated relatedHere partner partnerIn partnerNamed).1 next
        ((step_partner_iff avoids partnerIn leftIn).mp step)
      exact ⟨matched, (step_partner_iff avoids partnerIn rightIn).mpr step', relatedNext⟩
    · intro left right label next' relatedHere named step
      obtain ⟨hole, partner, rfl, avoids, partnerIn, partnerNamed⟩ := exists_of_isNamedPartnerLabel named
      obtain ⟨leftIn, rightIn⟩ := inProcesses relatedHere
      obtain ⟨matched, step', relatedNext⟩ := (saturated relatedHere partner partnerIn partnerNamed).2 next'
        ((step_partner_iff avoids partnerIn rightIn).mp step)
      exact ⟨matched, (step_partner_iff avoids partnerIn leftIn).mpr step', relatedNext⟩

/-- **The front door's native types under named partners characterize the named π-calculus's saturated reduction
bisimilarity**: two named processes are saturated reduction bisimilar exactly when their translations satisfy the
same forward formulas under named partners. -/
theorem agree_iff_named {first second : Process} :
    frontDoor.AgreeOn (Formula.forwardOn isNamedPartnerLabel) (piToPattern first) (piToPattern second) ↔
      SaturatedReductionBisimilar first second :=
  (agree_iff_forwardBisimilar_named (translation_process first) (translation_process second)).trans
    ((forwardBisimilar_iff_namedSaturated (translation_process first) (translation_process second)).trans
      saturated_iff_namedSaturated.symm)

open Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPrenexForms (names)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff isObjectPatternList_iff)

/-! ## Beyond the named calculus -/

/-- **Replication goes beyond the named calculus**: a replicated output is a process of `piCalc` that no named process
translates to, the named calculus replicating inputs only. The front door's characterization above is beside named
partners. -/
theorem replicated_output_not_named :
    processes (.apply "PiRep" [.apply "PiOut" [.fvar "x", .fvar "w"]]) ∧
      Named (.apply "PiRep" [.apply "PiOut" [.fvar "x", .fvar "w"]]) = false := by
  constructor
  · decide +kernel
  · decide

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiNamed
