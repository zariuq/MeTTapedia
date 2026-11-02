import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ComputedNormalForm
import Mettapedia.Languages.ProcessCalculi.PiCalculus.Blocks
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Typed
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Certificates
import Mettapedia.Languages.ProcessCalculi.PiCalculus.AuthoredStepReflection
import Mettapedia.Languages.ProcessCalculi.PiCalculus.AuthoredSemantics
import Mettapedia.GSLT.LanguageDef.Continued.ContinuationDecorationBinding
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseCanonicalProjection

/-!
# Canonical forms for the π-calculus

The π-calculus of the tree (`piCalc`) composes processes in parallel in a bag that declares the flattening
algebra with inaction as its unit, and it has one sort. Its parallel fragment (`piParallelFragment`: the same
rules, without the restriction laws) has as canonical forms the bag normal form on closed processes
(`AlgebraForms.canonical`). `piCalc`'s restriction laws identify more processes, so these are not its canonical
forms.

**A step from any process is matched by a step from its normal form**, to a result with the same normal form
(`simulation`). The steps are read through the occurrence specification of the three rules (`PiRawStep`):
- a communication finds its input and its output among the components of the normal form, with normalized
  parts, and the normal form commutes with substitution (`AlgebraForms.normalForm_instantiateBVar`);
- a step inside a component whose normal form is a bag becomes a step of the flattened bag, with the other
  components as a frame (`frame`, `reorder`);
- inaction has no step (`unit_stuck`).

The rule may change: a communication inside a nested bag is a congruence step of the outer bag, and once the
bags are flattened it is a communication at the top.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiForms

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (instantiateBVar instantiateBVarAt)
open Mettapedia.OSLF.MeTTaIL.PatternCode (sortPatterns)
open Mettapedia.GSLT.LanguageDef.BagNormalForm
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.GeneralPremise (instantiateBVarAt_objects instantiateBVarAt_canonical)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
  (PiRawStep piCalc piBagPresentation piParallelFragment piParallelBagTheory params_of_label category_of_member
    restriction_typed)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Blocks (piBlock)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.GSLT.LanguageDef (defaultBasePremises)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.AlgebraForms (Structural normalForm_instantiateBVar
  normalForm_idempotent contents_normalizeBag normalizeBag_single contents_map_structural)

/-- The normal form of the π-calculus's laws. -/
local notation "nf" => normalForm (some "PiNil")

/-! ## Lists -/

theorem perm_getElem_eraseIdx : ∀ (list : List Pattern) (index : ℕ) (bound : index < list.length),
    list.Perm (list[index] :: list.eraseIdx index)
  | _ :: _, 0, _ => by simp
  | head :: tail, index + 1, bound => by
    simp only [List.getElem_cons_succ, List.eraseIdx_cons_succ]
    exact ((perm_getElem_eraseIdx tail index (by simpa using bound)).cons head).trans (List.Perm.swap _ _ _)

theorem exists_index_of_perm {list rest : List Pattern} {element : Pattern} (perm : list.Perm (element :: rest)) :
    ∃ (index : ℕ) (bound : index < list.length), list[index] = element ∧ (list.eraseIdx index).Perm rest := by
  have member : element ∈ list := perm.symm.subset (by simp)
  have bound := List.idxOf_lt_length_of_mem member
  refine ⟨list.idxOf element, bound, List.getElem_idxOf bound, ?_⟩
  rw [← List.erase_eq_eraseIdx_of_idxOf rfl]
  simpa using perm.erase element

theorem exists_two_indices_of_perm {list rest : List Pattern} {first second : Pattern}
    (perm : list.Perm (first :: second :: rest)) :
    ∃ (i : ℕ) (hi : i < list.length) (j : ℕ) (hj : j < (list.eraseIdx i).length),
      list[i] = first ∧ (list.eraseIdx i)[j] = second ∧ ((list.eraseIdx i).eraseIdx j).Perm rest := by
  obtain ⟨i, hi, atFirst, restPerm⟩ := exists_index_of_perm perm
  obtain ⟨j, hj, atSecond, lastPerm⟩ := exists_index_of_perm restPerm
  exact ⟨i, hi, j, hj, atFirst, atSecond, lastPerm⟩

/-- The two occurrences a communication selects, and what remains. -/
theorem perm_two_selected (list : List Pattern) (i : ℕ) (hi : i < list.length) (j : ℕ)
    (hj : j < (list.eraseIdx i).length) :
    list.Perm (list[i] :: (list.eraseIdx i)[j] :: (list.eraseIdx i).eraseIdx j) :=
  (perm_getElem_eraseIdx list i hi).trans ((perm_getElem_eraseIdx _ j hj).cons _)

/-! ## Bag contents -/

theorem bagContents_perm {first second : List Pattern} (perm : first.Perm second) :
    (bagContents "PiNil" first).Perm (bagContents "PiNil" second) :=
  (perm.flatMap_right splice).filter _

/-- A component that is neither a bag nor inaction contributes itself. -/
theorem contents_plain {pattern : Pattern} (notUnit : pattern ≠ .apply "PiNil" []) (notBag : ¬ IsBagNode pattern) :
    bagContents "PiNil" [pattern] = [pattern] := by
  simp [bagContents, splice_of_not_bag notBag, notUnit]

theorem contents_apply {label : String} {arguments : List Pattern} (notUnit : label ≠ "PiNil") :
    bagContents "PiNil" [.apply label arguments] = [.apply label arguments] :=
  contents_plain (by simp [notUnit]) (by rintro ⟨_, same⟩; cases same)

/-- Normalizing the components of normal forms again changes no contents. -/
theorem contents_renormal (patterns : List Pattern) :
    (bagContents "PiNil" ((bagContents "PiNil" (patterns.map nf)).map nf)).Perm
      (bagContents "PiNil" (patterns.map nf)) := by
  have each := contents_map_structural "PiNil" Structural.identity 0 (elements := patterns)
    fun element _ => (normalForm_idempotent "PiNil" element).symm
  simp only [Structural.identity] at each
  exact each.symm

/-- A normal form whose contents are at least two is the bag of its sorted contents. -/
theorem normalForm_bag_of_long {elements : List Pattern}
    (long : 2 ≤ (bagContents "PiNil" (elements.map nf)).length) :
    nf (.collection .hashBag elements none) =
      .collection .hashBag (sortPatterns (bagContents "PiNil" (elements.map nf))) none := by
  rw [normalForm_bag]
  simp only [normalizeBag]
  have sortedLong : 2 ≤ (sortPatterns (bagContents "PiNil" (elements.map nf))).length := by simpa using long
  generalize sortPatterns (bagContents "PiNil" (elements.map nf)) = sorted at sortedLong ⊢
  match sorted, sortedLong with
  | _ :: _ :: _, _ => rfl

/-- Two lists with the same contents normalize alike as bags. -/
theorem normalForm_bag_congr {first second : List Pattern}
    (same : (bagContents "PiNil" (first.map nf)).Perm (bagContents "PiNil" (second.map nf))) :
    nf (.collection .hashBag first none) = nf (.collection .hashBag second none) := by
  rw [normalForm_bag, normalForm_bag]
  exact normalizeBag_contents_perm "PiNil" same

theorem contents_cons_congr {first second : Pattern} {rest rest' : List Pattern} (same : first = second)
    (restPerm : (bagContents "PiNil" rest).Perm (bagContents "PiNil" rest')) :
    (bagContents "PiNil" (first :: rest)).Perm (bagContents "PiNil" (second :: rest')) := by
  rw [bagContents_cons "PiNil" first rest, bagContents_cons "PiNil" second rest', same]
  exact restPerm.append_left _

/-! ## Steps of a bag -/

/-- **Inaction has no step.** -/
theorem unit_stuck {target : Pattern} : ¬ PiRawStep (.apply "PiNil" []) target := by
  intro step
  generalize sourceIs : Pattern.apply "PiNil" [] = source at step
  cases step with
  | comm => cases sourceIs
  | par => cases sourceIs
  | res => simp at sourceIs

/-- **A step of a bag keeps a frame**: its result is a bag, and other components added to the source are
added to the result. -/
theorem frame {elements : List Pattern} {tail : Option String} {target : Pattern}
    (step : PiRawStep (.collection .hashBag elements tail) target) :
    ∃ components, target = .collection .hashBag components none ∧
      ∀ others, PiRawStep (.collection .hashBag (elements ++ others) none)
        (.collection .hashBag (components ++ others) none) := by
  cases step with
  | comm i hi j hj channel binder body datum input output =>
    refine ⟨_, rfl, fun others => ?_⟩
    have hi' : i < (elements ++ others).length := by simp; omega
    have eraseFirst : (elements ++ others).eraseIdx i = elements.eraseIdx i ++ others :=
      List.eraseIdx_append_of_lt_length hi others
    have hj' : j < ((elements ++ others).eraseIdx i).length := by rw [eraseFirst]; simp; omega
    have eraseSecond : ((elements ++ others).eraseIdx i).eraseIdx j = (elements.eraseIdx i).eraseIdx j ++ others := by
      rw [eraseFirst, List.eraseIdx_append_of_lt_length hj others]
    have fired := PiRawStep.comm (elements := elements ++ others) (tail := none) i hi' j hj' channel binder body
      datum ((List.getElem_append_left hi).trans input)
      (((List.getElem_of_eq eraseFirst hj').trans (List.getElem_append_left hj)).trans output)
    rw [eraseSecond] at fired
    simpa using fired
  | par i hi inner =>
    refine ⟨_, rfl, fun others => ?_⟩
    have hi' : i < (elements ++ others).length := by simp; omega
    have fired := PiRawStep.par (elements := elements ++ others) (tail := none) i hi'
      (by rw [List.getElem_append_left hi]; exact inner)
    rw [List.eraseIdx_append_of_lt_length hi others] at fired
    simpa using fired

/-- **A step of a bag is a step of every reordering of it**, to a reordered result. -/
theorem reorder {elements other components : List Pattern} {tail : Option String}
    (step : PiRawStep (.collection .hashBag elements tail) (.collection .hashBag components none))
    (perm : elements.Perm other) :
    ∃ components', PiRawStep (.collection .hashBag other none) (.collection .hashBag components' none) ∧
      components'.Perm components := by
  cases step with
  | comm i hi j hj channel binder body datum input output =>
    have selected := perm_two_selected elements i hi j hj
    rw [input, output] at selected
    obtain ⟨i', hi', j', hj', atInput, atOutput, restPerm⟩ := exists_two_indices_of_perm (selected.symm.trans perm).symm
    exact ⟨_, PiRawStep.comm (tail := none) i' hi' j' hj' channel binder body datum atInput atOutput,
      restPerm.cons _⟩
  | par i hi inner =>
    obtain ⟨i', hi', atSelected, restPerm⟩ :=
      exists_index_of_perm ((perm_getElem_eraseIdx elements i hi).symm.trans perm).symm
    exact ⟨_, PiRawStep.par (tail := none) i' hi' (by rw [atSelected]; exact inner), restPerm.cons _⟩

/-! ## The simulation -/

theorem tail_none {kind : CollType} {elements : List Pattern} {tail : Option String}
    (object : isObjectPattern (.collection kind elements tail) = true) : tail = none := by
  simp only [isObjectPattern, Bool.and_eq_true, Option.isNone_iff_eq_none] at object
  exact object.1

theorem element_object {kind : CollType} {elements : List Pattern} {tail : Option String}
    (object : isObjectPattern (.collection kind elements tail) = true) {element : Pattern}
    (member : element ∈ elements) : isObjectPattern element = true := by
  simp only [isObjectPattern, Bool.and_eq_true] at object
  exact isObjectPatternList_iff.mp object.2 element member

/-- The components of a bag in which a communication fires: its two partners, normalized, and the contents of
the rest. -/
theorem contents_of_selected {elements rest : List Pattern} {first second : Pattern}
    (perm : elements.Perm (first :: second :: rest)) (firstLabel : ∃ arguments, nf first = .apply "PiInp" arguments)
    (secondLabel : ∃ arguments, nf second = .apply "PiOut" arguments) :
    (bagContents "PiNil" (elements.map nf)).Perm (nf first :: nf second :: bagContents "PiNil" (rest.map nf)) := by
  have mapped := bagContents_perm (perm.map nf)
  simp only [List.map_cons] at mapped
  refine mapped.trans ?_
  rw [bagContents_cons, bagContents_cons "PiNil" (nf second)]
  obtain ⟨firstArguments, firstIs⟩ := firstLabel
  obtain ⟨secondArguments, secondIs⟩ := secondLabel
  rw [firstIs, secondIs, contents_apply (by decide), contents_apply (by decide)]
  rfl

/-- **A step from any object process is matched by a step from its normal form**, to a result with the same
normal form. -/
theorem simulation {source target : Pattern} (step : PiRawStep source target) :
    isObjectPattern source = true → ∃ target', PiRawStep (nf source) target' ∧ nf target' = nf target := by
  induction step with
  | @comm elements tail i hi j hj channel binder body datum input output =>
    intro object
    obtain rfl := tail_none object
    have selected := perm_two_selected elements i hi j hj
    rw [input, output] at selected
    have contents := contents_of_selected selected ⟨_, rfl⟩ ⟨_, rfl⟩
    simp only [List.map_cons, List.map_nil, normalForm, normalFormList_eq_map] at contents
    have long : 2 ≤ (bagContents "PiNil" (elements.map nf)).length := by
      rw [contents.length_eq]; simp
    rw [normalForm_bag_of_long long]
    obtain ⟨i', hi', j', hj', atInput, atOutput, restPerm⟩ :=
      exists_two_indices_of_perm ((sortPatterns_perm _).trans contents)
    refine ⟨_, PiRawStep.comm (tail := none) i' hi' j' hj' _ binder _ _ atInput atOutput, ?_⟩
    apply normalForm_bag_congr
    simp only [List.map_cons]
    exact contents_cons_congr (normalForm_instantiateBVar "PiNil" datum body).symm
      ((bagContents_perm (restPerm.map nf)).trans (contents_renormal _))
  | @par elements tail i hi target inner recurse =>
    intro object
    obtain rfl := tail_none object
    obtain ⟨target', fired, same⟩ := recurse (element_object object (List.getElem_mem hi))
    have split := perm_getElem_eraseIdx elements i hi
    have contents : (bagContents "PiNil" (elements.map nf)).Perm
        (bagContents "PiNil" [nf elements[i]] ++ bagContents "PiNil" ((elements.eraseIdx i).map nf)) := by
      have mapped := bagContents_perm (split.map nf)
      simp only [List.map_cons] at mapped
      rwa [bagContents_cons] at mapped
    have wholeTarget : ∀ result : Pattern, nf result = nf target →
        nf (.collection .hashBag (target :: elements.eraseIdx i) none) =
          normalizeBag (some "PiNil") (nf result :: (elements.eraseIdx i).map nf) := by
      intro result sameResult
      rw [normalForm_bag, List.map_cons, sameResult]
    have normal := rootNormal_normalForm "PiNil" elements[i]
    by_cases bag : IsBagNode (nf elements[i])
    · obtain ⟨components, isBag⟩ := bag
      obtain ⟨-, componentsLong, plain⟩ := normal components isBag
      have spliced : bagContents "PiNil" [nf elements[i]] = components := by
        rw [isBag]
        simp only [bagContents, List.flatMap_cons, List.flatMap_nil, List.append_nil, splice_bag]
        exact List.filter_eq_self.mpr fun component member => by simpa using (plain component member).1
      rw [spliced] at contents
      rw [isBag] at fired
      obtain ⟨results, rfl, framed⟩ := frame fired
      have long : 2 ≤ (bagContents "PiNil" (elements.map nf)).length := by
        rw [contents.length_eq]; simp; omega
      rw [normalForm_bag_of_long long]
      obtain ⟨results', reordered, resultsPerm⟩ :=
        reorder (framed _) ((sortPatterns_perm _).trans contents).symm
      refine ⟨_, reordered, ?_⟩
      rw [wholeTarget _ same, normalForm_bag]
      apply normalizeBag_contents_perm
      rw [bagContents_cons]
      refine (bagContents_perm (resultsPerm.map nf)).trans ?_
      rw [List.map_append, bagContents_append]
      refine List.Perm.append ?_ (contents_renormal _)
      rw [normalForm_bag]
      exact (contents_normalizeBag "PiNil" fun component member => by
        obtain ⟨original, -, rfl⟩ := List.mem_map.mp member
        exact rootNormal_normalForm "PiNil" original).symm
    · by_cases unit : nf elements[i] = .apply "PiNil" []
      · rw [unit] at fired
        exact absurd fired unit_stuck
      · rw [contents_plain unit bag] at contents
        by_cases lone : bagContents "PiNil" ((elements.eraseIdx i).map nf) = []
        · rw [lone] at contents
          have alone : bagContents "PiNil" (elements.map nf) = [nf elements[i]] := List.perm_singleton.mp contents
          have nfSource : nf (.collection .hashBag elements none) = nf elements[i] := by
            rw [normalForm_bag]
            simp only [normalizeBag, alone, sortPatterns_singleton, collapse]
          rw [nfSource]
          refine ⟨target', fired, ?_⟩
          rw [wholeTarget _ same]
          refine (normalizeBag_single "PiNil" (rootNormal_normalForm "PiNil" target')).symm.trans ?_
          apply normalizeBag_contents_perm
          rw [bagContents_cons "PiNil" (nf target') ((elements.eraseIdx i).map nf), lone, List.append_nil]
        · have long : 2 ≤ (bagContents "PiNil" (elements.map nf)).length := by
            rw [contents.length_eq]
            have := List.length_pos_of_ne_nil lone
            simp; omega
          rw [normalForm_bag_of_long long]
          obtain ⟨i', hi', atSelected, restPerm⟩ := exists_index_of_perm ((sortPatterns_perm _).trans contents)
          refine ⟨_, PiRawStep.par (tail := none) i' hi' (by rw [atSelected]; exact fired), ?_⟩
          rw [wholeTarget _ same, normalForm_bag, List.map_cons]
          apply normalizeBag_contents_perm
          exact contents_cons_congr rfl ((bagContents_perm (restPerm.map nf)).trans (contents_renormal _))
  | @res binder source target inner recurse =>
    intro object
    have bodyObject : isObjectPattern source = true := by
      simpa [isObjectPattern, isObjectPatternList] using object
    obtain ⟨target', fired, same⟩ := recurse bodyObject
    refine ⟨.apply "PiNu" [.lambda none target'], ?_, ?_⟩
    · simp only [List.map_cons, List.map_nil, normalForm, normalFormList_eq_map]
      exact PiRawStep.res binder fired
    · simp only [List.map_cons, List.map_nil, normalForm, normalFormList_eq_map]
      rw [same]

/-! ## Steps keep processes sorted -/

/-- The parallel constructor is a bare bag of `piCalc`. -/
theorem piBare : BareBagPresentation piCalc piCalc.terms[1] (some "PiNil") := piBagPresentation.asBare rfl

/-- The typing of a constructor application, rebuilt with arguments typed at the same parameters. -/
theorem rebuild_apply {free : FreeTypeContext} {bound : List TypeExpr} {label : String}
    {arguments arguments' : List Pattern} {type : TypeExpr}
    (typed : HasType piCalc free bound (.apply label arguments) type)
    (retyped : ∀ rule ∈ piCalc.terms, rule.label = label →
      ArgumentsHaveTypes piCalc free bound arguments rule.params →
        ArgumentsHaveTypes piCalc free bound arguments' rule.params) :
    HasType piCalc free bound (.apply label arguments') type := by
  obtain ⟨rule, member, rfl, notBare, rfl, typedArguments⟩ := hasType_apply_inversion typed
  exact HasType.constructor member notBare (retyped rule member rfl typedArguments)

/-- A channel and a binder: the channel has the sort, and the body has it under one more bound variable of
the sort. -/
theorem listener_typed {free : FreeTypeContext} {bound : List TypeExpr} {label : String}
    (listener : label = "PiInp") {channel body : Pattern} {binder : Option String}
    {type : TypeExpr} (typed : HasType piCalc free bound (.apply label [channel, .lambda binder body]) type) :
    HasType piCalc free bound channel (.base "Name") ∧
      HasType piCalc free (.base "Name" :: bound) body (.base "Proc") := by
  obtain ⟨rule, member, labelIs, -, -, arguments⟩ := hasType_apply_inversion typed
  have params : rule.params =
      [.simple "x" (.base "Name"), .abstraction "body" (.arrow (.base "Name") (.base "Proc"))] := by
    subst listener
    exact (params_of_label member).1 labelIs.symm
  rw [params] at arguments
  cases arguments with
  | cons _ channelType channelTyped rest =>
    cases rest with
    | cons _ bodyType bodyTyped _ =>
      simp only [parameterType?, Option.some.injEq] at channelType bodyType
      subst channelType bodyType
      cases bodyTyped with
      | lambda inner => exact ⟨channelTyped, inner⟩

theorem output_typed {free : FreeTypeContext} {bound : List TypeExpr} {channel datum : Pattern} {type : TypeExpr}
    (typed : HasType piCalc free bound (.apply "PiOut" [channel, datum]) type) :
    HasType piCalc free bound channel (.base "Name") ∧ HasType piCalc free bound datum (.base "Name") := by
  obtain ⟨rule, member, labelIs, -, -, arguments⟩ := hasType_apply_inversion typed
  rw [(params_of_label member).2.2.1 labelIs.symm] at arguments
  cases arguments with
  | cons _ channelType channelTyped rest =>
    cases rest with
    | cons _ datumType datumTyped _ =>
      simp only [parameterType?, Option.some.injEq] at channelType datumType
      subst channelType datumType
      exact ⟨channelTyped, datumTyped⟩

/-- An admissible bag: no tail, and admissible elements. -/
theorem bag_elements {free : FreeTypeContext} {bound : List TypeExpr} {elements : List Pattern}
    {tail : Option String}
    (admissible : Admissible piCalc free bound (.base "Proc") (.collection .hashBag elements tail)) :
    tail = none ∧ ∀ element ∈ elements, Admissible piCalc free bound (.base "Proc") element := by
  refine ⟨tail_none admissible.object, fun element member => ⟨?_, ?_, element_object admissible.object member⟩⟩
  · obtain ⟨-, -, typed⟩ := bag_typing piBare admissible.typed rfl
    exact elementsHaveType_iff.mp typed element member
  · have canonical := admissible.canonical
    simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_iff] at canonical
    exact canonical element member

/-- A bag of admissible elements is admissible. -/
theorem bag_admissible {free : FreeTypeContext} {bound : List TypeExpr} {elements : List Pattern}
    (each : ∀ element ∈ elements, Admissible piCalc free bound (.base "Proc") element) :
    Admissible piCalc free bound (.base "Proc") (.collection .hashBag elements none) where
  typed := bag_hasType piBare (elementsHaveType_iff.mpr fun element member => (each element member).typed)
  canonical := by
    simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_iff]
    exact fun element member => (each element member).canonical
  object := by
    simp only [isObjectPattern, Option.isNone_none, Bool.true_and, isObjectPatternList_iff]
    exact fun element member => (each element member).object

theorem binder_parts {free : FreeTypeContext} {bound : List TypeExpr} {label : String} {channel body : Pattern}
    {binder : Option String} {type : TypeExpr}
    (admissible : Admissible piCalc free bound type (.apply label [channel, .lambda binder body])) :
    binder = none ∧ channel.hasCanonicalBinderMetadata = true ∧ body.hasCanonicalBinderMetadata = true ∧
      isObjectPattern channel = true ∧ isObjectPattern body = true := by
  have canonical := admissible.canonical
  have object := admissible.object
  simp only [Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true,
    Option.isNone_iff_eq_none] at canonical
  simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true] at object
  exact ⟨canonical.2.1.1, canonical.1, canonical.2.1.2, object.1, object.2.1⟩

theorem output_parts {free : FreeTypeContext} {bound : List TypeExpr} {channel datum : Pattern}
    (admissible : Admissible piCalc free bound (.base "Proc") (.apply "PiOut" [channel, datum])) :
    Admissible piCalc free bound (.base "Name") datum := by
  have canonical := admissible.canonical
  have object := admissible.object
  simp only [Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true] at canonical
  simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true] at object
  exact ⟨(output_typed admissible.typed).2, canonical.2.1, object.2.1⟩

theorem instantiate_admissible {free : FreeTypeContext} {bound : List TypeExpr} {body replacement : Pattern}
    (bodyAdmissible : Admissible piCalc free (.base "Name" :: bound) (.base "Proc") body)
    (replacementAdmissible : Admissible piCalc free bound (.base "Name") replacement) :
    Admissible piCalc free bound (.base "Proc") (instantiateBVar replacement body) :=
  ⟨HasType.instantiateBVar bodyAdmissible.typed replacementAdmissible.typed,
    instantiateBVarAt_canonical 0 bodyAdmissible.canonical replacementAdmissible.canonical,
    instantiateBVarAt_objects 0 bodyAdmissible.object replacementAdmissible.object⟩

/-- **A step keeps a sorted object process sorted**, in every context. -/
theorem admissible_of_raw {source target : Pattern} (step : PiRawStep source target) :
    ∀ {free : FreeTypeContext} {bound : List TypeExpr}, Admissible piCalc free bound (.base "Proc") source →
      Admissible piCalc free bound (.base "Proc") target := by
  induction step with
  | @comm elements tail i hi j hj channel binder body datum input output =>
    intro free bound admissible
    obtain ⟨-, each⟩ := bag_elements admissible
    have inputAdmissible := input ▸ each _ (List.getElem_mem hi)
    have outputAdmissible := output ▸ each _ (List.mem_of_mem_eraseIdx (List.getElem_mem hj))
    obtain ⟨-, -, bodyCanonical, -, bodyObject⟩ := binder_parts inputAdmissible
    have body' : Admissible piCalc free (.base "Name" :: bound) (.base "Proc") body :=
      ⟨(listener_typed rfl inputAdmissible.typed).2, bodyCanonical, bodyObject⟩
    apply bag_admissible
    intro element member
    rcases List.mem_cons.mp member with rfl | inRest
    · exact instantiate_admissible body' (output_parts outputAdmissible)
    · exact each element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx inRest))
  | @par elements tail i hi target inner recurse =>
    intro free bound admissible
    obtain ⟨-, each⟩ := bag_elements admissible
    apply bag_admissible
    intro element member
    rcases List.mem_cons.mp member with rfl | inRest
    · exact recurse (each _ (List.getElem_mem hi))
    · exact each element (List.mem_of_mem_eraseIdx inRest)
  | @res binder source target inner recurse =>
    intro free bound admissible
    have canonical := admissible.canonical
    have object := admissible.object
    simp only [Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true,
      Option.isNone_iff_eq_none] at canonical
    simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true] at object
    have result := recurse ⟨restriction_typed admissible.typed, canonical.1.2, object.1⟩
    refine ⟨?_, ?_, ?_⟩
    · refine rebuild_apply admissible.typed fun rule member labelIs _ => ?_
      rw [(params_of_label member).2.2.2 labelIs]
      exact .cons trivial rfl (HasType.lambda result.typed) .nil
    · simp [Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList, result.canonical]
    · simp [isObjectPattern, isObjectPatternList, result.object]

/-! ## Coherence -/

open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep (StepValid ReferenceProfile contextualStep_iff_step)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance (pi_step_iff_raw)

/-- The parallel fragment's static theory is its bag alone. -/
theorem bareBagTheory : BareBagTheory piParallelFragment piCalc.terms[1] (some "PiNil") :=
  piParallelBagTheory.asBare rfl

theorem profile : ReferenceProfile piParallelFragment := profile_of_aligned (by decide)

/-- **π's reading**: the typed reading, each law between two object terms of one sort whose free variables are names
of the name sort. -/
def reading : LanguageReading := { equations := .typed .raw .empty .sorts (some "Name") }

/-- The context of π's free names. -/
abbrev names : FreeTypeContext := EquationReading.nameContext (some "Name")

/-- Object processes with no free bound variable, their free variables names. -/
def domain (term : Pattern) : Bool :=
  checkOpenPatternWellSorted piParallelFragment names [] (.base "Proc") term

/-- The canonical form of a process of the fragment: its bag normal form, on the domain. -/
def canon (term : Pattern) : Pattern := if domain term then normalForm (some "PiNil") term else term

theorem domain_iff {term : Pattern} :
    domain term = true ↔ Admissible piParallelFragment names [] (.base "Proc") term := by
  unfold domain
  rw [checkOpenPatternWellSorted_eq_true_iff]
  constructor
  · rintro ⟨typed, canonical, object, -⟩
    exact ⟨typed, canonical, object⟩
  · intro admissible
    exact ⟨admissible.typed, admissible.canonical, admissible.object,
      by simpa [ScopeSafeAt] using admissible.typed.isWellScopedAt⟩

/-- **A typed object of the fragment has one sort**: a free name has the name sort, and every constructor makes a
process. -/
theorem sort_unique {term : Pattern} {first second : String}
    (firstTyped : HasType piParallelFragment names [] term (.base first))
    (secondTyped : HasType piParallelFragment names [] term (.base second)) (object : isObjectPattern term = true) :
    first = second := by
  cases firstTyped with
  | bvar lookup => simp at lookup
  | fvar lookup =>
      cases secondTyped with
      | fvar lookup' =>
          simp only [names, EquationReading.nameContext, Option.some.injEq, TypeExpr.base.injEq] at lookup lookup'
          exact lookup.symm.trans lookup'
  | constructor member =>
      obtain ⟨rule', member', labelIs, -, typeIs, -⟩ := hasType_apply_inversion secondTyped
      simp only [TypeExpr.base.injEq] at typeIs
      rw [category_of_member member, typeIs, category_of_member member']
  | subst => simp [isObjectPattern] at object
  | collectionConstructor member =>
      rw [category_of_member member]
      have sortIs := (bag_typing bareBagTheory.toBareBagPresentation secondTyped rfl).2.1
      simp only [TypeExpr.base.injEq] at sortIs
      rw [sortIs]
      rfl

/-- A typed object of the fragment carries no binder names, so it is in the domain. -/
theorem domain_of_typed {term : Pattern} (typed : HasType piParallelFragment names [] term (.base "Proc"))
    (object : isObjectPattern term = true) : domain term = true :=
  domain_iff.mpr ⟨typed, (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.metadata_of_typed (block := piBlock) _
    (HasType.of_terms_subset (source := piParallelFragment) (target := piCalc) (fun _ member => member) typed)
    object).1 ⟨_, rfl⟩, object⟩

/-- **A step of π's reading relates the domain only to the domain**, both ways. -/
theorem domain_iff_of_step {relEnv : RelationEnv} {first second : Pattern}
    (step : ObjectStep relEnv piParallelFragment reading first second) :
    domain first = true ↔ domain second = true := by
  obtain ⟨-, -, type, ⟨sort, rfl⟩, firstFormed, secondFormed, -⟩ := step
  constructor
  · intro admitted
    obtain rfl := sort_unique firstFormed.typed (domain_iff.mp admitted).typed firstFormed.object
    exact domain_of_typed secondFormed.typed secondFormed.object
  · intro admitted
    obtain rfl := sort_unique secondFormed.typed (domain_iff.mp admitted).typed secondFormed.object
    exact domain_of_typed firstFormed.typed firstFormed.object

theorem domain_iff_of_equivalent {relEnv : RelationEnv} {first second : Pattern}
    (equivalent : ObjectEquivalent relEnv piParallelFragment reading first second) :
    domain first = true ↔ domain second = true := by
  induction equivalent with
  | rel _ _ step => exact domain_iff_of_step step
  | refl => exact Iff.rfl
  | symm _ _ _ same => exact same.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- **A chain of the bag's laws from a typed object is an equivalence of π's reading.** -/
theorem objectEquivalent_of_path {relEnv : RelationEnv} {base : BasePremiseEvaluator} {source target : Pattern}
    (path : Path base piParallelFragment source target)
    (admissible : Admissible piParallelFragment names [] (.base "Proc") source) :
    ObjectEquivalent relEnv piParallelFragment reading source target := by
  induction path with
  | refl => exact Relation.EqvGen.refl _
  | tail before step previous =>
    have middle := path_admissible bareBagTheory before admissible rfl
    have last := step_admissible bareBagTheory step middle rfl
    exact Relation.EqvGen.trans _ _ _ previous (Relation.EqvGen.rel _ _ ⟨middle.object, last.object, .base "Proc",
      ⟨"Proc", rfl⟩, ⟨middle.object, middle.typed, by simp⟩, ⟨last.object, last.typed, by simp⟩,
      Mettapedia.OSLF.MeTTaIL.ReferenceStep.disciplinedStep_raw_iff.mpr
        (AlgebraForms.step_of_equationContextStep bareBagTheory.equationsEmpty step)⟩)

theorem normal_admissible {term : Pattern} (admissible : Admissible piParallelFragment names [] (.base "Proc") term) :
    Admissible piParallelFragment names [] (.base "Proc") (normalForm (some "PiNil") term) :=
  path_admissible bareBagTheory (path_normalForm bareBagTheory defaultBasePremises term admissible rfl) admissible rfl

/-- The fragment and `piCalc` type the same processes. -/
theorem admissible_iff {free : FreeTypeContext} {bound : List TypeExpr} {type : TypeExpr} {term : Pattern} :
    Admissible piParallelFragment free bound type term ↔ Admissible piCalc free bound type term :=
  ⟨fun admitted => ⟨HasType.of_terms_subset (source := piParallelFragment) (target := piCalc)
      (fun _ member => member) admitted.typed, admitted.canonical, admitted.object⟩,
    fun admitted => ⟨HasType.of_terms_subset (source := piCalc) (target := piParallelFragment)
      (fun _ member => member) admitted.typed, admitted.canonical, admitted.object⟩⟩

/-- The reference steps of the fragment are the steps of π's occurrence specification. -/
theorem step_iff_raw {source target : Pattern} :
    (∃ witness, StepValid RelationEnv.empty piParallelFragment source witness target) ↔ PiRawStep source target :=
  (contextualStep_iff_step RelationEnv.empty piParallelFragment profile).symm.trans
    ⟨fun step => (pi_step_iff_raw source target).mp
        (Mettapedia.OSLF.MeTTaIL.ContextualStep.Step.mono_rules (lang₁ := piParallelFragment) (lang₂ := piCalc)
          (fun _ member => member) step),
      fun raw => Mettapedia.OSLF.MeTTaIL.ContextualStep.Step.mono_rules (lang₁ := piCalc)
        (lang₂ := piParallelFragment) (fun _ member => member) ((pi_step_iff_raw source target).mpr raw)⟩

/-- **The bag normal form gives canonical forms** on object processes, in π's typed reading, whose domain is read
off them. -/
theorem canonicalDetermined (relEnv : RelationEnv) :
    CanonicalDetermined relEnv piParallelFragment canon domain reading where
  object admitted := (domain_iff.mp admitted).object
  determined term := by
    unfold canon
    by_cases admitted : domain term = true
    · rw [if_pos admitted, admitted]
      exact domain_iff.mpr (normal_admissible (domain_iff.mp admitted))
    · rw [if_neg admitted]
  equivalent {term} admitted := by
    unfold canon
    rw [if_pos admitted]
    exact objectEquivalent_of_path (path_normalForm bareBagTheory defaultBasePremises term (domain_iff.mp admitted) rfl)
      (domain_iff.mp admitted)
  same {first second} admitted equivalent := by
    have secondAdmitted := (domain_iff_of_equivalent equivalent).mp admitted
    unfold canon
    rw [if_pos admitted, if_pos secondAdmitted]
    exact normalForm_eq_of_equationEquiv bareBagTheory.toBagTheory (Relation.EqvGen.mono
      (fun _ _ step => AlgebraForms.equationContextStep_of_step bareBagTheory.equationsEmpty defaultBasePremises step)
      _ _ equivalent.equivalent)
  closed {term} admitted := by
    unfold canon
    rw [if_pos admitted]
    have before := (domain_iff.mp admitted).typed.isWellScopedAt
    have after := (normal_admissible (domain_iff.mp admitted)).typed.isWellScopedAt
    simp only [List.length_nil] at before after
    rw [before, after]

theorem canonical (relEnv : RelationEnv) : Canonical relEnv piParallelFragment canon domain reading :=
  (canonicalDetermined relEnv).canonical

/-- **Coherence for plain steps**: a step from any process equivalent to a canonical one is matched, up to
canonical form, by a step listed at it, wherever the fuel lists its steps. -/
theorem coherentPlain (fuel : ℕ) :
    CoherentPlain RelationEnv.empty piParallelFragment fuel canon domain List.singleton reading :=
  coherentPlain_of_simulation (canonical RelationEnv.empty) fun {redex witness contractum} _ admitted valid => by
    have redexAdmissible := domain_iff.mp admitted
    have raw := step_iff_raw.mp ⟨witness, valid⟩
    obtain ⟨contractum', raw', same⟩ := simulation raw redexAdmissible.object
    have normalAdmissible := normal_admissible redexAdmissible
    obtain ⟨witness', valid'⟩ := step_iff_raw.mpr raw'
    have contractumAdmitted : domain contractum = true :=
      domain_iff.mpr (admissible_iff.mpr (admissible_of_raw raw (admissible_iff.mp redexAdmissible)))
    have contractum'Admitted : domain contractum' = true :=
      domain_iff.mpr (admissible_iff.mpr (admissible_of_raw raw' (admissible_iff.mp normalAdmissible)))
    refine ⟨witness', contractum', ?_, ?_⟩
    · unfold canon
      rw [if_pos admitted]
      exact valid'
    · unfold canon
      rw [if_pos contractumAdmitted, if_pos contractum'Admitted]
      exact same

/-! ## Computing -/

open Mettapedia.OSLF.NativeTypes.GeneratedLogic.ComputedNormalForm (fastNormalForm fastNormalForm_eq)

/-- The canonical form, computed. -/
def fastCanon (term : Pattern) : Pattern := if domain term then fastNormalForm "PiNil" term else term

theorem fastCanon_eq : fastCanon = canon := by
  funext term
  unfold fastCanon canon
  rw [fastNormalForm_eq]

/-- **The parallel fragment's canonical forms, as the front door takes them**: coherent for plain steps. -/
def forms (fuel : ℕ) : CanonicalForms RelationEnv.empty piParallelFragment fuel where
  reading := reading
  canon := fastCanon
  domain := domain
  canonical := by rw [fastCanon_eq]; exact canonical RelationEnv.empty
  labels := plainLabel
  coherent := by rw [fastCanon_eq]; exact CoherentPlain.on (coherentPlain fuel)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiForms
