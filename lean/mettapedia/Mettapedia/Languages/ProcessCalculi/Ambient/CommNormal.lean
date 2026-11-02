import Mettapedia.Languages.ProcessCalculi.Ambient.CommLaws
import Mettapedia.Languages.ProcessCalculi.Ambient.DecodingRoot

/-!
# The path normal form decides the laws of paths

The path normal form (`pathNF`) reads every prefix by a capability as the prefixes it makes. It commutes with
substituting toVariables for toVariables (`pathNF_substitute`), renaming bound toVariables among them (`pathNF_rename`), keeps object terms object terms (`isObject_pathNF`), and carries each shape of the
core's laws to a shape (`pathNF_ambShape`), while the two sides of a law of paths have one normal form
(`PathShape.pathNF_eq`). Prefixes made by a typed capability carry the core's chains (`prefixes_fill`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Comm

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution (Assignment substitute lift substituteList_eq_map)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext isObjectPattern isObjectPatternList
  hasType_apply_inversion)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (isObjectPatternList_iff)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (ProcEquiv rename rename_bvar rename_fvar rename_apply rename_lambda
  rename_multiLambda rename_subst rename_collection liftBVars_eq_rename LawShape size swapInner)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (AmbShape ambientBlock ambientRepBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (nameType procType cap_apply_inv name_cases_ambient acap_inv)

/-! ## Prefixes and the normal form, read syntactically -/

/-- **A capability term the laws of paths read**: `in n`, `out n`, `open n`, `ε` or a path. -/
def readCap : Pattern → Bool
  | .apply label arguments =>
      (decide (label ∈ ["CapIn", "CapOut", "CapOpen"]) && arguments.length == 1) ||
        (label == "CapEps" && arguments.length == 0) || (label == "CapPath" && arguments.length == 2)
  | _ => false

/-- A capability no law of paths reads stays a prefix. -/
theorem prefixes_other {capability process : Pattern} (other : readCap capability = false) :
    prefixes capability process = .apply "ACap" [capability, process] := by
  unfold prefixes
  split <;> simp_all [readCap]

/-- **An assignment of toVariables**: every variable is sent to a variable. -/
def VariableAssignment (assignment : Assignment) : Prop :=
  ∀ index, (∃ other, assignment index = .bvar other) ∨ ∃ name, assignment index = .fvar name

theorem VariableAssignment.lift {assignment : Assignment} (toVariables : VariableAssignment assignment) (arity : Nat) :
    VariableAssignment (lift arity assignment) := by
  intro index
  unfold Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift
  split
  · exact .inl ⟨index, rfl⟩
  · rcases toVariables (index - arity) with ⟨other, same⟩ | ⟨name, same⟩
    · exact .inl ⟨other + arity, by rw [same]; simp [liftBVars]⟩
    · exact .inr ⟨name, by rw [same]; simp [liftBVars]⟩

/-- A renaming is an assignment of toVariables. -/
theorem variableAssignment_rename (relabel : Nat → Nat) : VariableAssignment fun index => .bvar (relabel index) :=
  fun index => .inl ⟨relabel index, rfl⟩

theorem readCap_substitute {assignment : Assignment} (toVariables : VariableAssignment assignment) (pattern : Pattern) :
    readCap (substitute assignment pattern) = readCap pattern := by
  cases pattern with
  | bvar index => rcases toVariables index with ⟨other, same⟩ | ⟨name, same⟩ <;> simp [substitute, same, readCap]
  | _ => simp [substitute, readCap, substituteList_eq_map]

/-- The readable capability terms, one by one. -/
theorem readCap_cases {label : String} {arguments : List Pattern} (readable : readCap (.apply label arguments) = true) :
    (label ∈ ["CapIn", "CapOut", "CapOpen"] ∧ ∃ name, arguments = [name]) ∨ (label = "CapEps" ∧ arguments = []) ∨
      (label = "CapPath" ∧ ∃ first rest, arguments = [first, rest]) := by
  simp only [readCap, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at readable
  rcases readable with (⟨listed, length⟩ | ⟨rfl, length⟩) | ⟨rfl, length⟩
  · exact .inl ⟨listed, List.length_eq_one_iff.mp length⟩
  · exact .inr (.inl ⟨rfl, List.length_eq_zero_iff.mp length⟩)
  · exact .inr (.inr ⟨rfl, List.length_eq_two.mp length⟩)

/-- **Prefixes commute with substituting toVariables for toVariables.** -/
theorem prefixes_substitute {assignment : Assignment} (toVariables : VariableAssignment assignment)
    (capability : Pattern) : ∀ process : Pattern,
    substitute assignment (prefixes capability process) =
      prefixes (substitute assignment capability) (substitute assignment process) := by
  induction capability using Pattern.inductionOn with
  | happly label arguments recurse =>
      intro process
      by_cases readable : readCap (.apply label arguments) = true
      · rcases readCap_cases readable with ⟨listed, name, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, first, rest, rfl⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
          rcases listed with rfl | rfl | rfl <;> simp [prefixes, substitute, substituteList_eq_map]
        · simp [prefixes, substitute, substituteList_eq_map]
        · simp only [prefixes, substitute, substituteList_eq_map, List.map_cons, List.map_nil]
          rw [recurse first (by simp), recurse rest (by simp)]
      · have other : readCap (.apply label arguments) = false := by simpa using readable
        rw [prefixes_other other, prefixes_other (by rw [readCap_substitute toVariables]; exact other)]
        simp [substitute, substituteList_eq_map]
  | hbvar index =>
      intro process
      rw [prefixes_other rfl, prefixes_other (by rw [readCap_substitute toVariables]; rfl)]
      simp [substitute, substituteList_eq_map]
  | hfvar name =>
      intro process
      rw [prefixes_other rfl, prefixes_other (by rw [readCap_substitute toVariables]; rfl)]
      simp [substitute, substituteList_eq_map]
  | hlambda binder body _ =>
      intro process
      rw [prefixes_other rfl, prefixes_other (by rw [readCap_substitute toVariables]; rfl)]
      simp [substitute, substituteList_eq_map]
  | hmultiLambda arity binders body _ =>
      intro process
      rw [prefixes_other rfl, prefixes_other (by rw [readCap_substitute toVariables]; rfl)]
      simp [substitute, substituteList_eq_map]
  | hsubst body replacement _ _ =>
      intro process
      rw [prefixes_other rfl, prefixes_other (by rw [readCap_substitute toVariables]; rfl)]
      simp [substitute, substituteList_eq_map]
  | hcollection kind elements rest _ =>
      intro process
      rw [prefixes_other rfl, prefixes_other (by rw [readCap_substitute toVariables]; rfl)]
      simp [substitute, substituteList_eq_map]

theorem pathNF_acap (capability process : Pattern) :
    pathNF (.apply "ACap" [capability, process]) = prefixes capability (pathNF process) := by
  simp [pathNF]

/-- Off a prefix by a capability, the normal form reads the arguments. -/
theorem pathNF_apply_other {label : String} {arguments : List Pattern}
    (other : ¬ (label = "ACap" ∧ arguments.length = 2)) :
    pathNF (.apply label arguments) = .apply label (arguments.map pathNF) := by
  rw [← pathNFList_eq_map]
  unfold pathNF
  split <;> simp_all

@[simp] theorem pathNF_bvar (index : Nat) : pathNF (.bvar index) = .bvar index := by simp [pathNF]

@[simp] theorem pathNF_fvar (name : String) : pathNF (.fvar name) = .fvar name := by simp [pathNF]

@[simp] theorem pathNF_lambda (binder : Option String) (body : Pattern) :
    pathNF (.lambda binder body) = .lambda binder (pathNF body) := by simp [pathNF]

@[simp] theorem pathNF_multiLambda (arity : Nat) (binders : List String) (body : Pattern) :
    pathNF (.multiLambda arity binders body) = .multiLambda arity binders (pathNF body) := by simp [pathNF]

@[simp] theorem pathNF_subst (body replacement : Pattern) :
    pathNF (.subst body replacement) = .subst (pathNF body) (pathNF replacement) := by simp [pathNF]

@[simp] theorem pathNF_collection (kind : CollType) (elements : List Pattern) (rest : Option String) :
    pathNF (.collection kind elements rest) = .collection kind (elements.map pathNF) rest := by
  rw [← pathNFList_eq_map]
  simp [pathNF]

/-- **The normal form commutes with substituting toVariables for toVariables.** -/
theorem pathNF_substitute (pattern : Pattern) : ∀ {assignment : Assignment}, VariableAssignment assignment →
    pathNF (substitute assignment pattern) = substitute assignment (pathNF pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro assignment toVariables
      rcases toVariables index with ⟨other, same⟩ | ⟨name, same⟩ <;> simp [substitute, same]
  | hfvar name => intro _ _; simp [substitute]
  | happly label arguments recurse =>
      intro assignment toVariables
      by_cases prefixed : label = "ACap" ∧ arguments.length = 2
      · obtain ⟨rfl, length⟩ := prefixed
        obtain ⟨capability, process, rfl⟩ := List.length_eq_two.mp length
        simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil]
        rw [pathNF_acap, pathNF_acap, recurse process (by simp) toVariables, prefixes_substitute toVariables]
      · simp only [substitute, substituteList_eq_map]
        rw [pathNF_apply_other (by simpa using prefixed), pathNF_apply_other prefixed]
        simp only [substitute, substituteList_eq_map, List.map_map]
        congr 1
        exact List.map_congr_left fun argument member => recurse argument member toVariables
  | hlambda binder body recurse =>
      intro assignment toVariables
      simp [substitute, recurse (toVariables.lift 1)]
  | hmultiLambda arity binders body recurse =>
      intro assignment toVariables
      simp [substitute, recurse (toVariables.lift arity)]
  | hsubst body replacement bodyRecurse replacementRecurse =>
      intro assignment toVariables
      simp [substitute, bodyRecurse (toVariables.lift 1), replacementRecurse toVariables]
  | hcollection kind elements rest recurse =>
      intro assignment toVariables
      simp only [substitute, substituteList_eq_map, pathNF_collection, List.map_map]
      congr 1
      exact List.map_congr_left fun element member => recurse element member toVariables

/-- **The normal form commutes with renaming bound toVariables.** -/
theorem pathNF_rename (pattern : Pattern) (relabel : Nat → Nat) :
    pathNF (rename relabel pattern) = rename relabel (pathNF pattern) :=
  pathNF_substitute pattern (variableAssignment_rename relabel)

theorem pathNF_lift (cutoff shift : Nat) (pattern : Pattern) :
    pathNF (liftBVars cutoff shift pattern) = liftBVars cutoff shift (pathNF pattern) := by
  rw [liftBVars_eq_rename, liftBVars_eq_rename, pathNF_rename]

/-- **Prefixes keep object terms.** -/
theorem isObject_prefixes (capability : Pattern) : ∀ {process : Pattern}, isObjectPattern capability = true →
    isObjectPattern process = true → isObjectPattern (prefixes capability process) = true := by
  induction capability using Pattern.inductionOn with
  | happly label arguments recurse =>
      intro process capabilityObject processObject
      by_cases readable : readCap (.apply label arguments) = true
      · rcases readCap_cases readable with ⟨listed, name, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, first, rest, rfl⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
          rcases listed with rfl | rfl | rfl <;>
            simp_all [prefixes, isObjectPattern, isObjectPatternList]
        · simpa [prefixes] using processObject
        · simp only [isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true] at capabilityObject
          simp only [prefixes]
          exact recurse first (by simp) capabilityObject.1 (recurse rest (by simp) capabilityObject.2 processObject)
      · rw [prefixes_other (by simpa using readable)]
        simp_all [isObjectPattern, isObjectPatternList]
  | hbvar index =>
      intro process _ processObject
      rw [prefixes_other rfl]
      simp_all [isObjectPattern, isObjectPatternList]
  | hfvar name =>
      intro process _ processObject
      rw [prefixes_other rfl]
      simp_all [isObjectPattern, isObjectPatternList]
  | hlambda binder body _ =>
      intro process capabilityObject processObject
      rw [prefixes_other rfl]
      simp_all [isObjectPattern, isObjectPatternList]
  | hmultiLambda arity binders body _ =>
      intro process capabilityObject processObject
      rw [prefixes_other rfl]
      simp_all [isObjectPattern, isObjectPatternList]
  | hsubst body replacement _ _ => intro _ capabilityObject; simp [isObjectPattern] at capabilityObject
  | hcollection kind elements rest _ =>
      intro process capabilityObject processObject
      rw [prefixes_other rfl]
      simp_all [isObjectPattern, isObjectPatternList]

/-- **The normal form keeps object terms.** -/
theorem isObject_pathNF (pattern : Pattern) : isObjectPattern pattern = true → isObjectPattern (pathNF pattern) = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _; rfl
  | hfvar name => intro _; rfl
  | happly label arguments recurse =>
      intro object
      have objects : ∀ argument ∈ arguments, isObjectPattern argument = true := by
        simpa [isObjectPattern, isObjectPatternList_iff] using object
      by_cases prefixed : label = "ACap" ∧ arguments.length = 2
      · obtain ⟨rfl, length⟩ := prefixed
        obtain ⟨capability, process, rfl⟩ := List.length_eq_two.mp length
        rw [pathNF_acap]
        exact isObject_prefixes _ (objects _ (by simp)) (recurse process (by simp) (objects _ (by simp)))
      · rw [pathNF_apply_other prefixed]
        simp only [isObjectPattern, isObjectPatternList_iff, List.mem_map]
        rintro _ ⟨argument, member, rfl⟩
        exact recurse argument member (objects argument member)
  | hlambda binder body recurse => intro object; simpa [isObjectPattern] using recurse (by simpa [isObjectPattern] using object)
  | hmultiLambda arity binders body recurse =>
      intro object; simpa [isObjectPattern] using recurse (by simpa [isObjectPattern] using object)
  | hsubst body replacement _ _ => intro object; simp [isObjectPattern] at object
  | hcollection kind elements rest recurse =>
      intro object
      simp only [isObjectPattern, Bool.and_eq_true, isObjectPatternList_iff] at object
      simp only [pathNF_collection, isObjectPattern, Bool.and_eq_true, isObjectPatternList_iff, List.mem_map]
      refine ⟨object.1, ?_⟩
      rintro _ ⟨element, member, rfl⟩
      exact recurse element member (object.2 element member)

/-! ## The shapes of the core's laws, in normal form -/

@[simp] theorem pathNF_apply_ne {label : String} (different : label ≠ "ACap") (arguments : List Pattern) :
    pathNF (.apply label arguments) = .apply label (arguments.map pathNF) :=
  pathNF_apply_other fun same => different same.1

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (SortedEquiv.typed_iff)

/-- **The normal form of a typed object process is a typed process**, the process's own equivalent. -/
theorem pathNF_typed {free : FreeTypeContext} {bound : List TypeExpr} {process : Pattern}
    (typed : HasType ambientCoreCalc free bound process procType) (object : isObjectPattern process = true) :
    HasType ambientCoreCalc free bound (pathNF process) procType := by
  have commTyped := typed.of_terms_subset core_terms_comm
  have equivalent := pathNF_equivalent (size process + 1) (Nat.lt_succ_self _) commTyped object
  exact ((SortedEquiv.typed_iff equivalent).mp commTyped).of_terms_subset comm_terms_core

/-- **Each shape of the core's laws between typed object processes stays a shape in normal form.** -/
theorem pathNF_ambShape {free : FreeTypeContext} {bound : List TypeExpr} {source target : Pattern}
    (shape : AmbShape source target) (typed : HasType ambientCoreCalc free bound source procType)
    (object : isObjectPattern source = true) : AmbShape (pathNF source) (pathNF target) := by
  cases shape with
  | law shape =>
      cases shape with
      | restrictionNil binder => simpa using AmbShape.law (.restrictionNil (block := ambientRepBlock) binder)
      | exchange outerBinder innerBinder body =>
          simpa [pathNF_rename] using
            AmbShape.law (.exchange (block := ambientRepBlock) outerBinder innerBinder (pathNF body))
      | @extrusion members selected inside binder body chosen =>
          have inside' : selected < (members.map pathNF).length := by simpa using inside
          have chosen' : (members.map pathNF)[selected] = .apply "ANu" [.lambda binder (pathNF body)] := by
            simp [chosen]
          have shape := AmbShape.law (.extrusion (block := ambientRepBlock) inside' chosen')
          have lifted : (members.eraseIdx selected).map (pathNF ∘ liftBVars 0 1) =
              ((members.map pathNF).eraseIdx selected).map (liftBVars 0 1) := by
            rw [List.eraseIdx_map, List.map_map]
            exact List.map_congr_left fun member _ => pathNF_lift 0 1 member
          simpa [lifted] using shape
      | @extrusionReverse binder members selected inside originals erased =>
          have inside' : selected < (members.map pathNF).length := by simpa using inside
          have erased' : (members.map pathNF).eraseIdx selected = (originals.map pathNF).map (liftBVars 0 1) := by
            rw [List.eraseIdx_map, erased, List.map_map, List.map_map]
            exact List.map_congr_left fun original _ => pathNF_lift 0 1 original
          have shape := AmbShape.law (.extrusionReverse (block := ambientRepBlock) (binder := binder) inside' erased')
          simpa using shape
      | emptyUnit listed => simp at listed
      | unfold process rest => simpa using AmbShape.law (.unfold (block := ambientRepBlock) (pathNF process) rest)
      | unfoldSwap process rest =>
          simpa using AmbShape.law (.unfoldSwap (block := ambientRepBlock) (pathNF process) rest)
      | replicationNil => simpa using AmbShape.law (.replicationNil (block := ambientRepBlock))
      | twice process => simpa using AmbShape.law (.twice (block := ambientRepBlock) (pathNF process))
      | par first second rest swapped =>
          cases swapped
          · simpa using AmbShape.law (.par (block := ambientRepBlock) (pathNF first) (pathNF second) rest false)
          · simpa using AmbShape.law (.par (block := ambientRepBlock) (pathNF first) (pathNF second) rest true)
      | parReverse first second rest swapped =>
          cases swapped
          · simpa using AmbShape.law (.parReverse (block := ambientRepBlock) (pathNF first) (pathNF second) rest false)
          · simpa using AmbShape.law (.parReverse (block := ambientRepBlock) (pathNF first) (pathNF second) rest true)
      | idempotent process rest =>
          simpa using AmbShape.law (.idempotent (block := ambientRepBlock) (pathNF process) rest)
      | bagPerm permutation => simpa using AmbShape.law (.bagPerm (block := ambientRepBlock) (permutation.map pathNF))
      | flatten pre inner post =>
          simpa using AmbShape.law (.flatten (block := ambientRepBlock) (pre.map pathNF) (inner.map pathNF)
            (post.map pathNF))
      | singleton notLambda =>
          have members := Mettapedia.Languages.ProcessCalculi.Ambient.Encoding.bag_inv typed
          have elementTyped := members target List.mem_cons_self
          have elementObject : isObjectPattern target = true := by
            simpa [isObjectPattern, isObjectPatternList] using object
          have normalTyped := pathNF_typed elementTyped elementObject
          have notLambda' : ∀ binder body, pathNF target ≠ .lambda binder body := fun binder body same => by
            rw [same] at normalTyped
            cases normalTyped
          simpa using AmbShape.law (.singleton (block := ambientRepBlock) notLambda')
      | unitElim pre post =>
          simpa using AmbShape.law (.unitElim (block := ambientRepBlock) (pre.map pathNF) (post.map pathNF))
      | emptyBag => simpa using AmbShape.law (.emptyBag (block := ambientRepBlock))
  | boundary name binder body =>
      simpa [pathNF_lift] using AmbShape.boundary (pathNF name) binder (pathNF body)
  | boundaryReverse name binder body =>
      simpa [pathNF_lift] using AmbShape.boundaryReverse (pathNF name) binder (pathNF body)

/-- **A typed object name is its own normal form.** -/
theorem pathNF_name {free : FreeTypeContext} {bound : List TypeExpr} {name : Pattern}
    (typed : HasType ambientCoreCalc free bound name nameType) (object : isObjectPattern name = true) :
    pathNF name = name := by
  rcases name_cases_ambient typed rfl object with ⟨index, rfl, -⟩ | ⟨name, rfl, -⟩ <;> rfl

/-- **The two sides of a law of paths between typed object processes have one normal form.** -/
theorem PathShape.pathNF_eq {free : FreeTypeContext} {bound : List TypeExpr} {source target : Pattern}
    (shape : PathShape source target) (typed : HasType ambientCoreCalc free bound source procType)
    (object : isObjectPattern source = true) : pathNF source = pathNF target := by
  induction shape with
  | eps process => simp [pathNF_acap, prefixes]
  | dot first rest process => simp [pathNF_acap, prefixes]
  | capPrefix listed name process =>
      obtain ⟨capabilityTyped, -⟩ := acap_inv typed
      have nameObject : isObjectPattern name = true := by
        simp [isObjectPattern, isObjectPatternList] at object
        exact object.1
      rcases cap_apply_inv capabilityTyped with ⟨-, name', same, nameTyped⟩ | ⟨-, same⟩ | ⟨-, _, _, same, -⟩
      · simp only [List.cons.injEq, and_true] at same
        subst same
        have unchanged := pathNF_name nameTyped nameObject
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at listed
        rcases listed with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [pathNF_acap, prefixes, unchanged]
      · simp at same
      · simp at same

/-! ## Prefixes in a context -/

open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (SortedEquiv.fill sizeList BaseContext)
open Mettapedia.GSLT.LanguageDef.WellSorted (hasType_collection_inversion
  matchesParameterRepresentation_abstractionNamed_iff)

/-- **The prefixes a typed object capability makes are a context of processes.** -/
theorem prefixes_context {free : FreeTypeContext} {bound : List TypeExpr} :
    ∀ (fuel : Nat) {capability : Pattern}, size capability < fuel →
      HasType ambientCoreCalc free bound capability capType → isObjectPattern capability = true →
      ∃ context : OneHoleContext, (∀ process, prefixes capability process = context.fill process) ∧
        ∀ process, HasType ambientCoreCalc free bound process procType →
          HasType ambientCoreCalc free bound (context.fill process) procType
  | 0, _, small, _, _ => absurd small (Nat.not_lt_zero _)
  | fuel + 1, capability, small, typed, object => by
      have prefixContext : ∀ {capability : Pattern}, readCap capability = false →
          HasType ambientCoreCalc free bound capability capType →
          ∃ context : OneHoleContext, (∀ process, prefixes capability process = context.fill process) ∧
            ∀ process, HasType ambientCoreCalc free bound process procType →
              HasType ambientCoreCalc free bound (context.fill process) procType :=
        fun {capability} other capabilityTyped =>
          ⟨.apply "ACap" [capability] .hole [], fun process => prefixes_other other,
            fun _ processTyped => Mettapedia.Languages.ProcessCalculi.Ambient.Full.acap_typed capabilityTyped
              processTyped⟩
      cases capability with
      | bvar index => exact prefixContext rfl typed
      | fvar name => exact prefixContext rfl typed
      | lambda binder body => cases typed
      | multiLambda arity binders body => cases typed
      | subst body replacement => simp [isObjectPattern] at object
      | collection kind elements rest =>
          rcases hasType_collection_inversion typed with ⟨_, typeIs, _⟩ |
            ⟨rule, parameterName, elementType, member, collectionShape, typeIs, -⟩
          · cases typeIs
          simp only [ambientCoreCalc, Mettapedia.Languages.ProcessCalculi.Ambient.Full.terms, commTerms,
            Mettapedia.Languages.ProcessCalculi.Ambient.Full.prefixRule, capRule, List.cons_append,
            List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl <;> simp_all [GrammarRule.bareParams]
      | apply label arguments =>
          have objects : ∀ argument ∈ arguments, isObjectPattern argument = true := by
            simpa [isObjectPattern, isObjectPatternList_iff] using object
          rcases cap_apply_inv typed with ⟨listed, name, rfl, nameTyped⟩ | ⟨rfl, rfl⟩ |
            ⟨rfl, first, rest, rfl, firstTyped, restTyped⟩
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
            rcases listed with rfl | rfl | rfl
            · exact ⟨.apply "AIn" [name] .hole [], fun _ => by simp [prefixes, OneHoleContext.fill],
                fun _ processTyped => Mettapedia.Languages.ProcessCalculi.Ambient.Full.prefix_typed (by simp)
                  nameTyped processTyped⟩
            · exact ⟨.apply "AOut" [name] .hole [], fun _ => by simp [prefixes, OneHoleContext.fill],
                fun _ processTyped => Mettapedia.Languages.ProcessCalculi.Ambient.Full.prefix_typed (by simp)
                  nameTyped processTyped⟩
            · exact ⟨.apply "AOpen" [name] .hole [], fun _ => by simp [prefixes, OneHoleContext.fill],
                fun _ processTyped => Mettapedia.Languages.ProcessCalculi.Ambient.Full.prefix_typed (by simp)
                  nameTyped processTyped⟩
          · exact ⟨.hole, fun _ => by simp [prefixes, OneHoleContext.fill], fun _ processTyped => processTyped⟩
          · have firstSmall : size first < fuel := by
              simp only [size, sizeList] at small
              omega
            have restSmall : size rest < fuel := by
              simp only [size, sizeList] at small
              omega
            obtain ⟨firstContext, firstFills, firstRebuild⟩ :=
              prefixes_context fuel firstSmall firstTyped (objects first (by simp))
            obtain ⟨restContext, restFills, restRebuild⟩ :=
              prefixes_context fuel restSmall restTyped (objects rest (by simp))
            exact ⟨firstContext.comp restContext, fun process => by simp [prefixes, firstFills, restFills],
              fun process processTyped => by
                rw [OneHoleContext.fill_comp]
                exact firstRebuild _ (restRebuild _ processTyped)⟩

/-! ## A law in a context, in normal form -/

/-- **A shape of a law with paths between typed object processes relates their normal forms by the core's laws.** -/
theorem shape_pathNF {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {source target : Pattern} (shape : CommShape source target)
    (sourceTyped : HasType ambientCoreCalc free bound source procType)
    (targetTyped : HasType ambientCoreCalc free bound target procType)
    (sourceObject : isObjectPattern source = true) (targetObject : isObjectPattern target = true) :
    ProcEquiv ambientCoreCalc ambientBlock free bound (pathNF source) (pathNF target) := by
  cases shape with
  | core shape =>
      exact (Mettapedia.Languages.ProcessCalculi.Ambient.Full.AmbShape.objectChain context (.inl ⟨"Proc", rfl⟩)
        (pathNF_ambShape shape sourceTyped sourceObject) (pathNF_typed sourceTyped sourceObject)
        (pathNF_typed targetTyped targetObject) (isObject_pathNF _ sourceObject)
        (isObject_pathNF _ targetObject)).toSortedEquiv
  | path shape =>
      rw [shape.pathNF_eq sourceTyped sourceObject]
      exact .refl _

/-- No law applies at a name, whichever side of it the context holds. -/
theorem no_names_either {free : FreeTypeContext} {bound : List TypeExpr} {source target : Pattern}
    (shape : CommShape source target ∨ CommShape target source) (context : OneHoleContext)
    (sourceTyped : HasType ambientCoreCalc free bound (context.fill source) nameType)
    (targetTyped : HasType ambientCoreCalc free bound (context.fill target) nameType)
    (sourceObject : isObjectPattern (context.fill source) = true)
    (targetObject : isObjectPattern (context.fill target) = true) : False := by
  rcases shape with shape | shape
  · exact Mettapedia.Languages.ProcessCalculi.Ambient.Encoding.no_names shape.notVariable context sourceTyped
      sourceObject
  · exact Mettapedia.Languages.ProcessCalculi.Ambient.Encoding.no_names shape.notVariable context targetTyped
      targetObject

/-- No law applies inside a capability term, whichever side of it the context holds. -/
theorem no_caps_either {free : FreeTypeContext} {bound : List TypeExpr} {source target : Pattern}
    (shape : CommShape source target ∨ CommShape target source) (context : OneHoleContext)
    (sourceTyped : HasType ambientCoreCalc free bound (context.fill source) capType)
    (targetTyped : HasType ambientCoreCalc free bound (context.fill target) capType)
    (sourceObject : isObjectPattern (context.fill source) = true)
    (targetObject : isObjectPattern (context.fill target) = true) : False := by
  rcases shape with shape | shape
  · exact Mettapedia.Languages.ProcessCalculi.Ambient.Encoding.no_caps shape.notVariable shape.notCap context
      sourceTyped sourceObject
  · exact Mettapedia.Languages.ProcessCalculi.Ambient.Encoding.no_caps shape.notVariable shape.notCap context
      targetTyped targetObject

/-- The argument of a binding constructor is an abstraction. -/
theorem abstraction_argument {free : FreeTypeContext} {bound : List TypeExpr} {label : String} {argument : Pattern}
    (listed : label ∈ ["ANu", "AInName", "AInCap"])
    (typed : HasType ambientCoreCalc free bound (.apply label [argument]) procType) :
    ∃ binder body, argument = .lambda binder body := by
  obtain ⟨rule, member, labelIs, -, -, arguments⟩ := hasType_apply_inversion typed
  simp only [ambientCoreCalc, Mettapedia.Languages.ProcessCalculi.Ambient.Full.terms, commTerms,
    Mettapedia.Languages.ProcessCalculi.Ambient.Full.prefixRule, capRule, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> subst labelIs <;> simp at listed <;>
    cases arguments with
    | cons representation _ _ _ =>
        obtain ⟨body, same⟩ := (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mp representation
        exact ⟨_, body, same⟩

/-- **A law at an abstraction's position is in its body**: the context fills to abstractions on both sides, and no
shape relates two abstractions. -/
theorem lambda_context {source target : Pattern} (shape : CommShape source target ∨ CommShape target source)
    {inner : OneHoleContext} (sourceLambda : ∃ binder body, inner.fill source = .lambda binder body)
    (targetLambda : ∃ binder body, inner.fill target = .lambda binder body) :
    ∃ binder body, inner = .lambda binder body := by
  cases inner with
  | hole =>
      obtain ⟨binder, body, same⟩ := sourceLambda
      obtain ⟨binder', body', same'⟩ := targetLambda
      simp only [OneHoleContext.fill] at same same'
      rcases shape with shape | shape
      · exact absurd same (shape.notLambda _ _)
      · exact absurd same' (shape.notLambda _ _)
  | lambda binder inner => exact ⟨binder, inner, rfl⟩
  | _ =>
      obtain ⟨binder, body, same⟩ := sourceLambda
      simp [OneHoleContext.fill] at same

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Members bag_fill restrict_fill replicate_fill)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (arguments_length positions_one positions_two prefix_inv
  amb_inv nu_inv input_inv output_inv bag_inv tail_none size_lt_of_mem')

/-- **A law with paths in a context, between typed object processes, relates their normal forms by the core's
laws.** -/
theorem pathNF_fill {free : FreeTypeContext} {source target : Pattern}
    (shape : CommShape source target ∨ CommShape target source) :
    ∀ (fuel : Nat) (context : OneHoleContext) {bound : List TypeExpr},
      size (context.fill source) < fuel → BaseContext free bound →
      HasType ambientCoreCalc free bound (context.fill source) procType →
      HasType ambientCoreCalc free bound (context.fill target) procType →
      isObjectPattern (context.fill source) = true → isObjectPattern (context.fill target) = true →
      ProcEquiv ambientCoreCalc ambientBlock free bound (pathNF (context.fill source)) (pathNF (context.fill target))
  | 0, _, _, small, _, _, _, _, _ => absurd small (Nat.not_lt_zero _)
  | fuel + 1, context, bound, small, baseContext, sourceTyped, targetTyped, sourceObject, targetObject => by
      -- a constructor whose first argument is a name and whose second is a process
      have named : ∀ {label : String}, label ≠ "ACap" →
          (∀ {name process : Pattern}, HasType ambientCoreCalc free bound (.apply label [name, process]) procType →
            HasType ambientCoreCalc free bound name nameType ∧ HasType ambientCoreCalc free bound process procType) →
          (∀ {name first second : Pattern}, HasType ambientCoreCalc free bound name nameType →
            ProcEquiv ambientCoreCalc ambientBlock free bound first second →
            ProcEquiv ambientCoreCalc ambientBlock free bound (.apply label [name, first]) (.apply label [name, second])) →
          ∀ {before after : List Pattern} {inner : OneHoleContext}, (before ++ inner.fill source :: after).length = 2 →
            size (.apply label (before ++ inner.fill source :: after)) < fuel + 1 →
            HasType ambientCoreCalc free bound (.apply label (before ++ inner.fill source :: after)) procType →
            HasType ambientCoreCalc free bound (.apply label (before ++ inner.fill target :: after)) procType →
            isObjectPattern (.apply label (before ++ inner.fill source :: after)) = true →
            isObjectPattern (.apply label (before ++ inner.fill target :: after)) = true →
            ProcEquiv ambientCoreCalc ambientBlock free bound (pathNF (.apply label (before ++ inner.fill source :: after)))
              (pathNF (.apply label (before ++ inner.fill target :: after))) := by
        intro label notCap inv fill before after inner length small sourceTyped targetTyped sourceObject targetObject
        rcases positions_two length with ⟨rfl, last, rfl⟩ | ⟨first, rfl, rfl⟩
        · simp only [List.nil_append] at sourceTyped targetTyped sourceObject targetObject
          exact (no_names_either shape inner (inv sourceTyped).1 (inv targetTyped).1
            (by simp [isObjectPattern, isObjectPatternList] at sourceObject; exact sourceObject.1)
            (by simp [isObjectPattern, isObjectPatternList] at targetObject; exact targetObject.1)).elim
        · simp only [List.singleton_append] at small sourceTyped targetTyped sourceObject targetObject ⊢
          obtain ⟨nameTyped, contentTyped⟩ := inv sourceTyped
          obtain ⟨-, targetContentTyped⟩ := inv targetTyped
          have nameObject : isObjectPattern first = true := by
            simp [isObjectPattern, isObjectPatternList] at sourceObject; exact sourceObject.1
          have contentSmall : size (inner.fill source) < fuel := by
            simp only [size, sizeList] at small
            omega
          have recurse := pathNF_fill shape fuel inner contentSmall baseContext contentTyped targetContentTyped
            (by simp [isObjectPattern, isObjectPatternList] at sourceObject; exact sourceObject.2)
            (by simp [isObjectPattern, isObjectPatternList] at targetObject; exact targetObject.2)
          rw [pathNF_apply_ne notCap, pathNF_apply_ne notCap]
          simp only [List.map_cons, List.map_nil, pathNF_name nameTyped nameObject]
          exact fill nameTyped recurse
      cases context with
      | hole =>
          simp only [OneHoleContext.fill] at sourceTyped targetTyped sourceObject targetObject ⊢
          rcases shape with shape | shape
          · exact shape_pathNF baseContext shape sourceTyped targetTyped sourceObject targetObject
          · exact .symm _ _ (shape_pathNF baseContext shape targetTyped sourceTyped targetObject sourceObject)
      | lambda binder inner => cases sourceTyped
      | multiLambda arity binders inner => cases sourceTyped
      | substBody inner replacement => simp [OneHoleContext.fill, isObjectPattern] at sourceObject
      | substReplacement body inner => simp [OneHoleContext.fill, isObjectPattern] at sourceObject
      | collection kind before inner after rest =>
          simp only [OneHoleContext.fill] at small sourceTyped targetTyped sourceObject targetObject ⊢
          rcases hasType_collection_inversion sourceTyped with ⟨_, typeIs, _⟩ |
            ⟨rule, parameterName, elementType, member, collectionShape, typeIs, elementsTyped⟩
          · cases typeIs
          simp only [ambientCoreCalc, Mettapedia.Languages.ProcessCalculi.Ambient.Full.terms, commTerms,
            Mettapedia.Languages.ProcessCalculi.Ambient.Full.prefixRule, capRule, List.cons_append,
            List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl <;>
            simp [GrammarRule.bareParams] at collectionShape
          obtain ⟨rfl, rfl, rfl⟩ := collectionShape
          obtain rfl := tail_none sourceObject
          have sourceMembers := bag_inv sourceTyped
          have targetMembers := bag_inv targetTyped
          have sourceObjects : ∀ element ∈ before ++ inner.fill source :: after, isObjectPattern element = true := by
            simpa [isObjectPattern, isObjectPatternList_iff] using sourceObject
          have targetObjects : ∀ element ∈ before ++ inner.fill target :: after, isObjectPattern element = true := by
            simpa [isObjectPattern, isObjectPatternList_iff] using targetObject
          have innerSmall : size (inner.fill source) < fuel := by
            have := size_lt_of_mem' (element := inner.fill source) (elements := before ++ inner.fill source :: after)
              (by simp)
            simp only [size] at small
            omega
          have recurse := pathNF_fill shape fuel inner innerSmall baseContext (sourceMembers _ (by simp))
            (targetMembers _ (by simp)) (sourceObjects _ (by simp)) (targetObjects _ (by simp))
          have beforeMembers : Members ambientCoreCalc ambientBlock free bound (before.map pathNF) := by
            intro element member
            obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
            exact pathNF_typed (sourceMembers original (by simp [originalMember]))
              (sourceObjects original (by simp [originalMember]))
          have afterMembers : Members ambientCoreCalc ambientBlock free bound (after.map pathNF) := by
            intro element member
            obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
            exact pathNF_typed (sourceMembers original (by simp [originalMember]))
              (sourceObjects original (by simp [originalMember]))
          simp only [pathNF_collection, List.map_append, List.map_cons]
          exact bag_fill (language := ambientCoreCalc) (block := ambientBlock) beforeMembers afterMembers recurse
      | apply label before inner after =>
          simp only [OneHoleContext.fill] at small sourceTyped targetTyped sourceObject targetObject ⊢
          obtain ⟨rule, member, rfl, notBare, typeIs, argumentsTyped⟩ := hasType_apply_inversion sourceTyped
          have length := arguments_length argumentsTyped
          simp only [ambientCoreCalc, Mettapedia.Languages.ProcessCalculi.Ambient.Full.terms, commTerms,
            Mettapedia.Languages.ProcessCalculi.Ambient.Full.prefixRule, capRule, List.cons_append,
            List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl <;>
            simp only [procType, TypeExpr.base.injEq] at typeIs <;> try (exact absurd typeIs (by decide))
          · -- inaction has no argument
            simp at length
          · -- the bag is no constructor application
            exact absurd ⟨"ps", .hashBag, .base "Proc", rfl⟩ notBare
          · -- restriction: the law is in its body
            obtain ⟨rfl, rfl⟩ := positions_one length
            simp only [List.nil_append] at small sourceTyped targetTyped sourceObject targetObject ⊢
            obtain ⟨binder, body, rfl⟩ := lambda_context shape (abstraction_argument (by simp) sourceTyped)
              (abstraction_argument (by simp) targetTyped)
            simp only [OneHoleContext.fill] at small sourceTyped targetTyped sourceObject targetObject ⊢
            obtain ⟨rfl, bodyTyped⟩ := nu_inv sourceTyped
            obtain ⟨-, targetBodyTyped⟩ := nu_inv targetTyped
            have bodySmall : size (body.fill source) < fuel := by
              simp only [size, sizeList] at small
              omega
            have recurse := pathNF_fill shape fuel body bodySmall (baseContext.cons "Name") bodyTyped targetBodyTyped
              (by simpa [isObjectPattern, isObjectPatternList] using sourceObject)
              (by simpa [isObjectPattern, isObjectPatternList] using targetObject)
            simp only [pathNF_apply_ne (show "ANu" ≠ "ACap" by decide), List.map_cons, List.map_nil, pathNF_lambda]
            exact restrict_fill (language := ambientCoreCalc) (block := ambientBlock) recurse
          · -- replication
            obtain ⟨rfl, rfl⟩ := positions_one length
            simp only [List.nil_append] at small sourceTyped targetTyped sourceObject targetObject ⊢
            have innerTyped := Mettapedia.Languages.ProcessCalculi.Ambient.Encoding.rep_inv sourceTyped
            have targetInnerTyped := Mettapedia.Languages.ProcessCalculi.Ambient.Encoding.rep_inv targetTyped
            have innerSmall : size (inner.fill source) < fuel := by
              simp only [size, sizeList] at small
              omega
            have recurse := pathNF_fill shape fuel inner innerSmall baseContext innerTyped targetInnerTyped
              (by simpa [isObjectPattern, isObjectPatternList] using sourceObject)
              (by simpa [isObjectPattern, isObjectPatternList] using targetObject)
            simp only [pathNF_apply_ne (show "ARep" ≠ "ACap" by decide), List.map_cons, List.map_nil]
            exact replicate_fill (block := ambientRepBlock) recurse
          · -- an ambient
            exact named (by decide) amb_inv Mettapedia.Languages.ProcessCalculi.Ambient.Full.amb_fill length small
              sourceTyped targetTyped sourceObject targetObject
          · exact named (by decide) (prefix_inv (by simp))
              (Mettapedia.Languages.ProcessCalculi.Ambient.Full.prefix_fill (by simp)) length small sourceTyped
              targetTyped sourceObject targetObject
          · exact named (by decide) (prefix_inv (by simp))
              (Mettapedia.Languages.ProcessCalculi.Ambient.Full.prefix_fill (by simp)) length small sourceTyped
              targetTyped sourceObject targetObject
          · exact named (by decide) (prefix_inv (by simp))
              (Mettapedia.Languages.ProcessCalculi.Ambient.Full.prefix_fill (by simp)) length small sourceTyped
              targetTyped sourceObject targetObject
          · -- a prefix by a capability term
            rcases positions_two length with ⟨rfl, last, rfl⟩ | ⟨first, rfl, rfl⟩
            · simp only [List.nil_append] at sourceTyped targetTyped sourceObject targetObject
              exact (no_caps_either shape inner (acap_inv sourceTyped).1 (acap_inv targetTyped).1
                (by simp [isObjectPattern, isObjectPatternList] at sourceObject; exact sourceObject.1)
                (by simp [isObjectPattern, isObjectPatternList] at targetObject; exact targetObject.1)).elim
            · simp only [List.singleton_append] at small sourceTyped targetTyped sourceObject targetObject ⊢
              obtain ⟨capabilityTyped, contentTyped⟩ := acap_inv sourceTyped
              obtain ⟨-, targetContentTyped⟩ := acap_inv targetTyped
              have capabilityObject : isObjectPattern first = true := by
                simp [isObjectPattern, isObjectPatternList] at sourceObject; exact sourceObject.1
              have contentSmall : size (inner.fill source) < fuel := by
                simp only [size, sizeList] at small
                omega
              have recurse := pathNF_fill shape fuel inner contentSmall baseContext contentTyped targetContentTyped
                (by simp [isObjectPattern, isObjectPatternList] at sourceObject; exact sourceObject.2)
                (by simp [isObjectPattern, isObjectPatternList] at targetObject; exact targetObject.2)
              rw [pathNF_acap, pathNF_acap]
              obtain ⟨prefixContext, fills, rebuild⟩ :=
                prefixes_context (size first + 1) (Nat.lt_succ_self _) capabilityTyped capabilityObject
              rw [fills, fills]
              exact SortedEquiv.fill prefixContext rebuild recurse
          · -- the input of a name: the law is in its body
            obtain ⟨rfl, rfl⟩ := positions_one length
            simp only [List.nil_append] at small sourceTyped targetTyped sourceObject targetObject ⊢
            obtain ⟨binder, body, rfl⟩ := lambda_context shape (abstraction_argument (by simp) sourceTyped)
              (abstraction_argument (by simp) targetTyped)
            simp only [OneHoleContext.fill] at small sourceTyped targetTyped sourceObject targetObject ⊢
            obtain ⟨rfl, bodyTyped⟩ := input_inv (sort := "Name") List.mem_cons_self sourceTyped
            obtain ⟨-, targetBodyTyped⟩ := input_inv (sort := "Name") List.mem_cons_self targetTyped
            have bodySmall : size (body.fill source) < fuel := by
              simp only [size, sizeList] at small
              omega
            have recurse := pathNF_fill shape fuel body bodySmall (baseContext.cons "Name") bodyTyped targetBodyTyped
              (by simpa [isObjectPattern, isObjectPatternList] using sourceObject)
              (by simpa [isObjectPattern, isObjectPatternList] using targetObject)
            simp only [pathNF_apply_ne (show "AInName" ≠ "ACap" by decide), List.map_cons, List.map_nil,
              pathNF_lambda]
            exact Mettapedia.Languages.ProcessCalculi.Ambient.Full.input_fill (by simp) recurse
          · -- the output of a name: no law applies at its message
            obtain ⟨rfl, rfl⟩ := positions_one length
            simp only [List.nil_append] at sourceTyped targetTyped sourceObject targetObject
            exact (no_names_either shape inner (output_inv (sort := "Name") List.mem_cons_self sourceTyped)
              (output_inv (sort := "Name") List.mem_cons_self targetTyped)
              (by simpa [isObjectPattern, isObjectPatternList] using sourceObject)
              (by simpa [isObjectPattern, isObjectPatternList] using targetObject)).elim
          · -- the input of a capability: the law is in its body
            obtain ⟨rfl, rfl⟩ := positions_one length
            simp only [List.nil_append] at small sourceTyped targetTyped sourceObject targetObject ⊢
            obtain ⟨binder, body, rfl⟩ := lambda_context shape (abstraction_argument (by simp) sourceTyped)
              (abstraction_argument (by simp) targetTyped)
            simp only [OneHoleContext.fill] at small sourceTyped targetTyped sourceObject targetObject ⊢
            obtain ⟨rfl, bodyTyped⟩ :=
              input_inv (sort := "Cap") (List.mem_cons_of_mem _ List.mem_cons_self) sourceTyped
            obtain ⟨-, targetBodyTyped⟩ :=
              input_inv (sort := "Cap") (List.mem_cons_of_mem _ List.mem_cons_self) targetTyped
            have bodySmall : size (body.fill source) < fuel := by
              simp only [size, sizeList] at small
              omega
            have recurse := pathNF_fill shape fuel body bodySmall (baseContext.cons "Cap") bodyTyped targetBodyTyped
              (by simpa [isObjectPattern, isObjectPatternList] using sourceObject)
              (by simpa [isObjectPattern, isObjectPatternList] using targetObject)
            simp only [pathNF_apply_ne (show "AInCap" ≠ "ACap" by decide), List.map_cons, List.map_nil,
              pathNF_lambda]
            exact Mettapedia.Languages.ProcessCalculi.Ambient.Full.input_fill (by simp) recurse
          · -- the output of a capability: no law applies inside its message
            obtain ⟨rfl, rfl⟩ := positions_one length
            simp only [List.nil_append] at sourceTyped targetTyped sourceObject targetObject
            exact (no_caps_either shape inner
              (output_inv (sort := "Cap") (List.mem_cons_of_mem _ List.mem_cons_self) sourceTyped)
              (output_inv (sort := "Cap") (List.mem_cons_of_mem _ List.mem_cons_self) targetTyped)
              (by simpa [isObjectPattern, isObjectPatternList] using sourceObject)
              (by simpa [isObjectPattern, isObjectPatternList] using targetObject)).elim

/-! ## Completeness -/

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (ObjectChain sortedEquiv_mono)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)

/-- **A chain of laws with paths between object processes relates their normal forms by the core's laws.** -/
theorem pathNF_chain {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {first second : Pattern} (chain : ObjectChain ambientCommCalc free bound procType first second) :
    ProcEquiv ambientCoreCalc ambientBlock free bound (pathNF first) (pathNF second) := by
  induction chain with
  | rel first second step =>
      obtain ⟨⟨stepped, firstTyped, secondTyped⟩, firstObject, secondObject⟩ := step
      cases stepped with
      | inContext stepContext generator =>
          exact pathNF_fill (comm_generator_shape generator) _ stepContext (Nat.lt_succ_self _) context
            (firstTyped.of_terms_subset comm_terms_core) (secondTyped.of_terms_subset comm_terms_core) firstObject
            secondObject
  | refl => exact .refl _
  | symm _ _ _ recurse => exact .symm _ _ recurse
  | trans _ _ _ _ _ left right => exact .trans _ _ _ left right

/-! ## The canonical form of ambients with paths -/

open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (NameContext)
open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (canonA canonA_facts canonA_same)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (ambient_objectChain ambient_premises_nil)

/-- **The canonical form of a process with paths**: the located canonical form of its path normal form, read
back. -/
def canonComm (process : Pattern) : Pattern := canonA (pathNF process)

/-- The core's chains are chains with paths. -/
theorem comm_of_core {free : FreeTypeContext} {bound : List TypeExpr} {first second : Pattern}
    (equivalent : ProcEquiv ambientCoreCalc ambientBlock free bound first second) :
    ProcEquiv ambientCommCalc ambientBlock free bound first second :=
  sortedEquiv_mono core_terms_comm (fun _ member => List.mem_append_left _ member)
    (fun _ member => ambient_premises_nil member) equivalent

/-- **The canonical form of a closed object process with paths is a closed object process equivalent to it.** -/
theorem canonComm_facts {free : FreeTypeContext} (names : NameContext free) {process : Pattern}
    (typed : HasType ambientCommCalc free [] process procType) (object : isObjectPattern process = true) :
    HasType ambientCommCalc free [] (canonComm process) procType ∧ isObjectPattern (canonComm process) = true ∧
      ProcEquiv ambientCommCalc ambientBlock free [] process (canonComm process) := by
  have normal := pathNF_equivalent (size process + 1) (Nat.lt_succ_self _) typed object
  have normalTyped := pathNF_typed (typed.of_terms_subset comm_terms_core) object
  obtain ⟨canonTyped, canonObject, -, canonEquivalent⟩ := canonA_facts names normalTyped (isObject_pathNF _ object)
  exact ⟨canonTyped.of_terms_subset core_terms_comm, canonObject, .trans _ _ _ normal (comm_of_core canonEquivalent)⟩

/-- **Processes with paths related by a chain of laws through object processes have one canonical form.** -/
theorem canonComm_same {free : FreeTypeContext} (names : NameContext free) (context : BaseContext free [])
    {first second : Pattern} (firstTyped : HasType ambientCommCalc free [] first procType)
    (firstObject : isObjectPattern first = true) (secondTyped : HasType ambientCommCalc free [] second procType)
    (secondObject : isObjectPattern second = true)
    (chain : ObjectChain ambientCommCalc free [] procType first second) : canonComm first = canonComm second := by
  have firstNormal := isObject_pathNF _ firstObject
  have secondNormal := isObject_pathNF _ secondObject
  exact canonA_same names (pathNF_typed (firstTyped.of_terms_subset comm_terms_core) firstObject) firstNormal
    (pathNF_typed (secondTyped.of_terms_subset comm_terms_core) secondObject) secondNormal
    (ambient_objectChain context (pathNF_chain context chain) firstNormal secondNormal)

end Mettapedia.Languages.ProcessCalculi.Ambient.Comm
