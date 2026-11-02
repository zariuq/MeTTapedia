import Mettapedia.Languages.ProcessCalculi.Ambient.CommPaths
import Mettapedia.Languages.ProcessCalculi.Ambient.FullEquivalences

/-!
# Equivalences of ambients with paths and communication

- **Typing**: the pure calculus's processes are processes here (`pure_typed`); the capabilities, the capability prefix
  and the inputs and outputs are typed by their declarations.
- **The laws of paths**: each shape of one (`PathShape`: the empty path, a path, a capability prefix) is an instance
  of it (`PathShape.instance`), so equivalent (`eps_equivalent`, `dot_equivalent`, `capPrefix_equivalent`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Comm

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (ProcEquiv SortedEquiv recoverValue?_zero)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (readsRaw_of_none)
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.RuleBinding (arguments? dependencies? occurrenceDeclared sitePattern? occurrenceAt?)
open Mettapedia.OSLF.MeTTaIL.ScopedEquationExecution (Orientation orientedRule applyEquationAt mem_applyEquationAt_iff)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (ambientNuCalc ambientBlock terms prefixRule)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (nameType procType)

variable {free : FreeTypeContext} {bound : List TypeExpr}

/-! ## Typing -/

/-- **A process of the pure calculus is a process here.** -/
theorem pure_typed {pattern : Pattern} {type : TypeExpr} (typed : HasType ambientNuCalc free bound pattern type) :
    HasType ambientCommCalc free bound pattern type :=
  HasType.of_terms_subset (List.subset_append_left terms commTerms) typed

/-- A capability over a name. -/
theorem capability_typed {label : String} (listed : label ∈ ["CapIn", "CapOut", "CapOpen"]) {name : Pattern}
    (nameTyped : HasType ambientCommCalc free bound name nameType) :
    HasType ambientCommCalc free bound (.apply label [name]) capType := by
  have arguments : ArgumentsHaveTypes ambientCommCalc free bound [name] [.simple "n" (.base "Name")] :=
    .cons trivial rfl nameTyped .nil
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl
  · exact .constructor (rule := ambientCommCalc.terms[8]) (List.getElem_mem (by decide))
      (by simp [UsesBareCollection, GrammarRule.bareParams, ambientCommCalc, terms, commTerms, capRule]) arguments
  · exact .constructor (rule := ambientCommCalc.terms[9]) (List.getElem_mem (by decide))
      (by simp [UsesBareCollection, GrammarRule.bareParams, ambientCommCalc, terms, commTerms, capRule]) arguments
  · exact .constructor (rule := ambientCommCalc.terms[10]) (List.getElem_mem (by decide))
      (by simp [UsesBareCollection, GrammarRule.bareParams, ambientCommCalc, terms, commTerms, capRule]) arguments

/-- The empty path. -/
theorem eps_typed : HasType ambientCommCalc free bound (.apply "CapEps" []) capType :=
  .constructor (rule := ambientCommCalc.terms[11]) (List.getElem_mem (by decide))
    (by simp [UsesBareCollection, GrammarRule.bareParams, ambientCommCalc, terms, commTerms]) .nil

/-- A path. -/
theorem path_typed {first rest : Pattern} (firstTyped : HasType ambientCommCalc free bound first capType)
    (restTyped : HasType ambientCommCalc free bound rest capType) :
    HasType ambientCommCalc free bound (.apply "CapPath" [first, rest]) capType :=
  .constructor (rule := ambientCommCalc.terms[12]) (List.getElem_mem (by decide))
    (by simp [UsesBareCollection, GrammarRule.bareParams, ambientCommCalc, terms, commTerms])
    (.cons trivial rfl firstTyped (.cons trivial rfl restTyped .nil))

/-- A process prefixed by a capability. -/
theorem acap_typed {capability process : Pattern} (capabilityTyped : HasType ambientCommCalc free bound capability capType)
    (processTyped : HasType ambientCommCalc free bound process procType) :
    HasType ambientCommCalc free bound (.apply "ACap" [capability, process]) procType :=
  .constructor (rule := ambientCommCalc.terms[13]) (List.getElem_mem (by decide))
    (by simp [UsesBareCollection, GrammarRule.bareParams, ambientCommCalc, terms, commTerms])
    (.cons trivial rfl capabilityTyped (.cons trivial rfl processTyped .nil))

/-- A capability of the pure calculus before a process. -/
theorem prefix_typed {label : String} (listed : label ∈ ["AIn", "AOut", "AOpen"]) {name process : Pattern}
    (nameTyped : HasType ambientCommCalc free bound name nameType)
    (processTyped : HasType ambientCommCalc free bound process procType) :
    HasType ambientCommCalc free bound (.apply label [name, process]) procType := by
  have arguments : ArgumentsHaveTypes ambientCommCalc free bound [name, process]
      [.simple "n" (.base "Name"), .simple "p" (.base "Proc")] :=
    .cons trivial rfl nameTyped (.cons trivial rfl processTyped .nil)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl
  · exact .constructor (rule := ambientCommCalc.terms[5]) (List.getElem_mem (by decide))
      (by simp [UsesBareCollection, GrammarRule.bareParams, ambientCommCalc, terms, prefixRule]) arguments
  · exact .constructor (rule := ambientCommCalc.terms[6]) (List.getElem_mem (by decide))
      (by simp [UsesBareCollection, GrammarRule.bareParams, ambientCommCalc, terms, prefixRule]) arguments
  · exact .constructor (rule := ambientCommCalc.terms[7]) (List.getElem_mem (by decide))
      (by simp [UsesBareCollection, GrammarRule.bareParams, ambientCommCalc, terms, prefixRule]) arguments

/-- An ambient of a name around a process. -/
theorem amb_typed {name process : Pattern} (nameTyped : HasType ambientCommCalc free bound name nameType)
    (processTyped : HasType ambientCommCalc free bound process procType) :
    HasType ambientCommCalc free bound (.apply "AAmb" [name, process]) procType :=
  .constructor (rule := ambientCommCalc.terms[4]) (List.getElem_mem (by decide))
    (by simp [UsesBareCollection, GrammarRule.bareParams, ambientCommCalc, terms])
    (.cons trivial rfl nameTyped (.cons trivial rfl processTyped .nil))

/-- The input of a name. -/
theorem inName_typed {body : Pattern} (typed : HasType ambientCommCalc free (nameType :: bound) body procType) :
    HasType ambientCommCalc free bound (.apply "AInName" [.lambda none body]) procType :=
  .constructor (rule := ambientCommCalc.terms[14]) (List.getElem_mem (by decide))
    (by simp [UsesBareCollection, GrammarRule.bareParams, ambientCommCalc, terms, commTerms])
    (.cons trivial rfl (.lambda typed) .nil)

/-- The output of a name. -/
theorem outName_typed {name : Pattern} (nameTyped : HasType ambientCommCalc free bound name nameType) :
    HasType ambientCommCalc free bound (.apply "AOutName" [name]) procType :=
  .constructor (rule := ambientCommCalc.terms[15]) (List.getElem_mem (by decide))
    (by simp [UsesBareCollection, GrammarRule.bareParams, ambientCommCalc, terms, commTerms])
    (.cons trivial rfl nameTyped .nil)

/-- The input of a capability. -/
theorem inCap_typed {body : Pattern} (typed : HasType ambientCommCalc free (capType :: bound) body procType) :
    HasType ambientCommCalc free bound (.apply "AInCap" [.lambda none body]) procType :=
  .constructor (rule := ambientCommCalc.terms[16]) (List.getElem_mem (by decide))
    (by simp [UsesBareCollection, GrammarRule.bareParams, ambientCommCalc, terms, commTerms])
    (.cons trivial rfl (.lambda typed) .nil)

/-- The output of a capability. -/
theorem outCap_typed {capability : Pattern} (capabilityTyped : HasType ambientCommCalc free bound capability capType) :
    HasType ambientCommCalc free bound (.apply "AOutCap" [capability]) procType :=
  .constructor (rule := ambientCommCalc.terms[17]) (List.getElem_mem (by decide))
    (by simp [UsesBareCollection, GrammarRule.bareParams, ambientCommCalc, terms, commTerms])
    (.cons trivial rfl capabilityTyped .nil)

/-- **A name is a variable**: no constructor makes a name. -/
theorem name_cases {pattern : Pattern} {type : TypeExpr} (typed : HasType ambientCommCalc free bound pattern type)
    (isName : type = nameType) (object : isObjectPattern pattern = true) :
    (∃ index, pattern = .bvar index ∧ bound[index]? = some nameType) ∨
      (∃ name, pattern = .fvar name ∧ free name = some nameType) := by
  cases typed with
  | bvar found => exact .inl ⟨_, rfl, isName ▸ found⟩
  | fvar found => exact .inr ⟨_, rfl, isName ▸ found⟩
  | constructor member _ _ =>
      simp only [ambientCommCalc, terms, commTerms, prefixRule, capRule, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> simp_all
  | collectionConstructor member _ _ =>
      simp only [ambientCommCalc, terms, commTerms, prefixRule, capRule, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> simp_all
  | lambda => cases isName
  | multiLambda => cases isName
  | subst => simp [isObjectPattern] at object
  | collection => cases isName

/-! ## The signature -/

open Mettapedia.GSLT.LanguageDef.BagNormalForm (BagPresentation)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (BlockSignature ReplicationSignature ParallelBag)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (ambientRepBlock)

/-- The parallel constructor declares the bag monoid with inaction as its unit. -/
theorem commBagPresentation : BagPresentation ambientCommCalc ambientCommCalc.terms[1] (some "AZero") where
  bagAuthored := List.getElem_mem (by decide)
  bagShape := ⟨"ps", rfl⟩
  bagAlgebra := rfl
  otherParameters := by
    intro rule member different parameter present
    simp only [ambientCommCalc, terms, commTerms, prefixRule, capRule, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    · simp at present
    · exact False.elim (different rfl)
    all_goals
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    all_goals rcases present with rfl | rfl <;> rfl
  unitAuthored := by
    intro unit same
    cases Option.some.inj same
    exact ⟨ambientCommCalc.terms[0], List.getElem_mem (by decide), rfl, rfl, rfl⟩

/-- **The calculus has the signature of the restriction-block theory**: a bare parallel bag with inaction as unit,
restriction binding a name over a process, and the laws of restriction declared. -/
instance commSignature : BlockSignature ambientCommCalc ambientBlock where
  bag := ⟨ambientCommCalc.terms[1], ParallelBag.ofBare (commBagPresentation.asBare rfl), rfl⟩
  lawsDeclared := by
    intro law member
    simp only [ambientCommCalc, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.replicationBlockLaws]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ member))
  restrictAuthored := ⟨ambientCommCalc.terms[2], List.getElem_mem (by decide), rfl⟩
  restrictShape := by
    intro rule member labelIs
    simp only [ambientCommCalc, terms, commTerms, prefixRule, capRule, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> simp_all
  unitShape := by
    intro rule member labelIs
    simp only [ambientCommCalc, terms, commTerms, prefixRule, capRule, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> simp_all
  multisetShape := by
    intro rule member listed
    simp at listed
  emptyUnitShape := by
    intro label listed
    simp at listed
  emptyUnitAuthored := by
    intro label listed
    simp at listed
  labelsUnique := by decide
  params := by
    intro rule member notBare _ parameter present
    simp only [ambientCommCalc, terms, commTerms, prefixRule, capRule, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    · simp at present
    · exact absurd ⟨"ps", .hashBag, .base "Proc", rfl⟩ notBare
    all_goals
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    all_goals rcases present with rfl | rfl <;> simp [parameterType?]
  arrowsAbstract := by
    intro rule member notBare _ parameter present domain sort found
    simp only [ambientCommCalc, terms, commTerms, prefixRule, capRule, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    · simp at present
    · exact absurd ⟨"ps", .hashBag, .base "Proc", rfl⟩ notBare
    all_goals
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    all_goals rcases present with rfl | rfl <;> simp_all [parameterType?]

/-- **The calculus has the signature of replication.** -/
instance commReplicationSignature : ReplicationSignature ambientCommCalc ambientRepBlock where
  toBlockSignature := commSignature
  replicationDeclared := fun _ member =>
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ member))
  replicateAuthored := ⟨ambientCommCalc.terms[3], List.getElem_mem (by decide), rfl⟩
  replicateShape := by
    intro rule member labelIs
    simp only [ambientCommCalc, terms, commTerms, prefixRule, capRule, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> simp_all
  replicateFresh := by decide

/-! ## The laws of paths -/

theorem pathLaw_mem {equation : Equation} (listed : equation ∈ pathLaws) :
    List.Mem equation ambientCommCalc.equations :=
  List.mem_append_right _ listed

/-- **The shapes of the laws of paths**, one orientation each: the empty path, a path, and a capability prefix. -/
inductive PathShape : Pattern → Pattern → Prop where
  | eps (process : Pattern) : PathShape (.apply "ACap" [.apply "CapEps" [], process]) process
  | dot (first rest process : Pattern) :
      PathShape (.apply "ACap" [.apply "CapPath" [first, rest], process])
        (.apply "ACap" [first, .apply "ACap" [rest, process]])
  | capPrefix {cap fused : String}
      (listed : (cap, fused) ∈ [("CapIn", "AIn"), ("CapOut", "AOut"), ("CapOpen", "AOpen")]) (name process : Pattern) :
      PathShape (.apply "ACap" [.apply cap [name], process]) (.apply fused [name, process])

/-- **Each shape of a law of paths is an instance of the law.** -/
theorem PathShape.instance {base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator}
    {source target : Pattern} (shape : PathShape source target) :
    Mettapedia.GSLT.LanguageDef.EquationSemantics.EquationInstance base ambientCommCalc source target :=
  match shape with
  | .eps process =>
      ⟨0, .forward (initialBindings := [("P", process)]) (finalBindings := [("P", process)])
        (pathLaw_mem (equation := pathEps) (by simp [pathLaws])) (readsRaw_of_none rfl)
        (by simp [pathEps, Mettapedia.OSLF.MeTTaIL.Match.matchPattern, Mettapedia.OSLF.MeTTaIL.Match.matchArgs,
          Mettapedia.OSLF.MeTTaIL.Match.mergeBindings]) (.nil _)
        (by simp [pathEps, Mettapedia.OSLF.MeTTaIL.Match.applyBindings])⟩
  | .dot first rest process =>
      ⟨0, .forward (initialBindings := [("P", process), ("K", rest), ("M", first)])
        (finalBindings := [("P", process), ("K", rest), ("M", first)])
        (pathLaw_mem (equation := pathDot) (by simp [pathLaws])) (readsRaw_of_none rfl)
        (by simp [pathDot, Mettapedia.OSLF.MeTTaIL.Match.matchPattern, Mettapedia.OSLF.MeTTaIL.Match.matchArgs,
          Mettapedia.OSLF.MeTTaIL.Match.mergeBindings]) (.nil _)
        (by simp [pathDot, Mettapedia.OSLF.MeTTaIL.Match.applyBindings])⟩
  | @PathShape.capPrefix cap fused listed name process => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at listed
      have member : Mettapedia.Languages.ProcessCalculi.Ambient.Comm.capPrefix cap fused ∈ pathLaws := by
        rcases listed with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [pathLaws]
      exact ⟨0, .forward (initialBindings := [("P", process), ("n", name)])
        (finalBindings := [("P", process), ("n", name)])
        (pathLaw_mem member) (readsRaw_of_none rfl)
        (by simp [Mettapedia.Languages.ProcessCalculi.Ambient.Comm.capPrefix,
          Mettapedia.OSLF.MeTTaIL.Match.matchPattern, Mettapedia.OSLF.MeTTaIL.Match.matchArgs,
          Mettapedia.OSLF.MeTTaIL.Match.mergeBindings]) (.nil _)
        (by simp [Mettapedia.Languages.ProcessCalculi.Ambient.Comm.capPrefix,
          Mettapedia.OSLF.MeTTaIL.Match.applyBindings])⟩

/-- **`ε.P ≡ P`.** -/
theorem eps_equivalent {process : Pattern} (typed : HasType ambientCommCalc free bound process procType) :
    ProcEquiv ambientCommCalc ambientBlock free bound (.apply "ACap" [.apply "CapEps" [], process]) process :=
  SortedEquiv.ofInstance (PathShape.eps process).instance (acap_typed eps_typed typed) typed

/-- **`(M.M').P ≡ M.(M'.P)`.** -/
theorem dot_equivalent {first rest process : Pattern}
    (firstTyped : HasType ambientCommCalc free bound first capType)
    (restTyped : HasType ambientCommCalc free bound rest capType)
    (typed : HasType ambientCommCalc free bound process procType) :
    ProcEquiv ambientCommCalc ambientBlock free bound (.apply "ACap" [.apply "CapPath" [first, rest], process])
      (.apply "ACap" [first, .apply "ACap" [rest, process]]) :=
  SortedEquiv.ofInstance (PathShape.dot first rest process).instance
    (acap_typed (path_typed firstTyped restTyped) typed) (acap_typed firstTyped (acap_typed restTyped typed))

/-- **A capability prefix is the pure calculus's prefix**: `(in n).P ≡ in n.P`, and so for `out` and `open`. -/
theorem capPrefix_equivalent {cap fused : String}
    (listed : (cap, fused) ∈ [("CapIn", "AIn"), ("CapOut", "AOut"), ("CapOpen", "AOpen")]) {name process : Pattern}
    (nameTyped : HasType ambientCommCalc free bound name nameType)
    (typed : HasType ambientCommCalc free bound process procType) :
    ProcEquiv ambientCommCalc ambientBlock free bound (.apply "ACap" [.apply cap [name], process])
      (.apply fused [name, process]) := by
  have labels := listed
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at labels
  have capTyped : HasType ambientCommCalc free bound (.apply cap [name]) capType :=
    capability_typed (by rcases labels with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp) nameTyped
  have fusedTyped : HasType ambientCommCalc free bound (.apply fused [name, process]) procType :=
    prefix_typed (by rcases labels with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp) nameTyped typed
  exact SortedEquiv.ofInstance (PathShape.capPrefix listed name process).instance (acap_typed capTyped typed)
    fusedTyped

/-! ## Contexts -/

theorem amb_fill {name first second : Pattern} (nameTyped : HasType ambientCommCalc free bound name nameType)
    (equivalent : ProcEquiv ambientCommCalc ambientBlock free bound first second) :
    ProcEquiv ambientCommCalc ambientBlock free bound (.apply "AAmb" [name, first]) (.apply "AAmb" [name, second]) :=
  SortedEquiv.fill (.apply "AAmb" [name] .hole []) (fun _ typed => amb_typed nameTyped typed) equivalent

theorem prefix_fill {label : String} (listed : label ∈ ["AIn", "AOut", "AOpen"]) {name first second : Pattern}
    (nameTyped : HasType ambientCommCalc free bound name nameType)
    (equivalent : ProcEquiv ambientCommCalc ambientBlock free bound first second) :
    ProcEquiv ambientCommCalc ambientBlock free bound (.apply label [name, first]) (.apply label [name, second]) :=
  SortedEquiv.fill (.apply label [name] .hole []) (fun _ typed => prefix_typed listed nameTyped typed) equivalent

theorem acap_fill {capability first second : Pattern}
    (capabilityTyped : HasType ambientCommCalc free bound capability capType)
    (equivalent : ProcEquiv ambientCommCalc ambientBlock free bound first second) :
    ProcEquiv ambientCommCalc ambientBlock free bound (.apply "ACap" [capability, first])
      (.apply "ACap" [capability, second]) :=
  SortedEquiv.fill (.apply "ACap" [capability] .hole []) (fun _ typed => acap_typed capabilityTyped typed) equivalent

theorem inName_fill {first second : Pattern}
    (equivalent : ProcEquiv ambientCommCalc ambientBlock free (nameType :: bound) first second) :
    ProcEquiv ambientCommCalc ambientBlock free bound (.apply "AInName" [.lambda none first])
      (.apply "AInName" [.lambda none second]) :=
  SortedEquiv.fill (.apply "AInName" [] (.lambda none .hole) []) (fun _ typed => inName_typed typed) equivalent

theorem inCap_fill {first second : Pattern}
    (equivalent : ProcEquiv ambientCommCalc ambientBlock free (capType :: bound) first second) :
    ProcEquiv ambientCommCalc ambientBlock free bound (.apply "AInCap" [.lambda none first])
      (.apply "AInCap" [.lambda none second]) :=
  SortedEquiv.fill (.apply "AInCap" [] (.lambda none .hole) []) (fun _ typed => inCap_typed typed) equivalent

/-! ## The path normal form is equivalent -/

open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff isObjectPatternList_iff)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (size Members restrict_fill collection_congr)

/-- **A capability is its own path normal form**: it holds no capability prefix. -/
theorem pathNF_capability : ∀ (fuel : Nat) {capability : Pattern}, size capability < fuel →
    HasType ambientCommCalc free bound capability capType → isObjectPattern capability = true →
    pathNF capability = capability
  | 0, _, small, _, _ => absurd small (Nat.not_lt_zero _)
  | fuel + 1, capability, small, typed, object => by
      cases capability with
      | bvar index => rfl
      | fvar name => rfl
      | lambda binder body => cases typed
      | multiLambda arity binders body => cases typed
      | subst body replacement => simp [isObjectPattern] at object
      | collection kind elements rest =>
          rcases hasType_collection_inversion typed with ⟨_, typeIs, _⟩ |
            ⟨rule, parameterName, elementType, member, shape, typeIs, elementsTyped⟩
          · cases typeIs
          · simp only [ambientCommCalc, terms, commTerms, prefixRule, capRule, List.cons_append, List.nil_append,
              List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
              rfl | rfl | rfl <;> simp_all [GrammarRule.bareParams]
      | apply label arguments =>
          obtain ⟨rule, member, rfl, notBare, typeIs, argumentsTyped⟩ := hasType_apply_inversion typed
          have objects : ∀ argument ∈ arguments, isObjectPattern argument = true := by
            simpa [isObjectPattern, isObjectPatternList_iff] using object
          have argumentSmall : ∀ argument ∈ arguments, size argument < fuel := by
            intro argument inArguments
            have := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.size_lt_of_mem inArguments
            simp only [size] at small
            omega
          simp only [ambientCommCalc, terms, commTerms, prefixRule, capRule, List.cons_append, List.nil_append,
            List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl <;> simp only [capType, TypeExpr.base.injEq] at typeIs <;>
            try (exact absurd typeIs (by decide))
          -- `in n`, `out n`, `open n`: a name
          · cases argumentsTyped with
            | cons _ parameter nameTyped rest =>
                cases rest
                simp only [parameterType?, Option.some.injEq] at parameter
                subst parameter
                rcases name_cases nameTyped rfl (objects _ List.mem_cons_self) with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;>
                  simp [pathNF, pathNFList]
          · cases argumentsTyped with
            | cons _ parameter nameTyped rest =>
                cases rest
                simp only [parameterType?, Option.some.injEq] at parameter
                subst parameter
                rcases name_cases nameTyped rfl (objects _ List.mem_cons_self) with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;>
                  simp [pathNF, pathNFList]
          · cases argumentsTyped with
            | cons _ parameter nameTyped rest =>
                cases rest
                simp only [parameterType?, Option.some.injEq] at parameter
                subst parameter
                rcases name_cases nameTyped rfl (objects _ List.mem_cons_self) with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;>
                  simp [pathNF, pathNFList]
          -- the empty path
          · cases argumentsTyped
            simp [pathNF, pathNFList]
          -- a path: both halves are their own normal forms
          · cases argumentsTyped with
            | @cons _ first _ _ _ _ _ firstParameter firstTyped rest =>
                cases rest with
                | @cons _ second _ _ _ _ _ secondParameter secondTyped last =>
                    cases last
                    simp only [parameterType?, Option.some.injEq] at firstParameter secondParameter
                    subst firstParameter secondParameter
                    have firstSame := pathNF_capability fuel (argumentSmall _ List.mem_cons_self) firstTyped
                      (objects _ List.mem_cons_self)
                    have secondSame := pathNF_capability fuel
                      (argumentSmall _ (List.mem_cons_of_mem _ List.mem_cons_self)) secondTyped
                      (objects _ (List.mem_cons_of_mem _ List.mem_cons_self))
                    simp [pathNF, pathNFList, firstSame, secondSame]

/-- **A prefix by a capability is the prefixes it makes.** -/
theorem prefixes_equivalent : ∀ (fuel : Nat) {capability process : Pattern}, size capability < fuel →
    HasType ambientCommCalc free bound capability capType → isObjectPattern capability = true →
    HasType ambientCommCalc free bound process procType →
    ProcEquiv ambientCommCalc ambientBlock free bound (.apply "ACap" [capability, process])
      (prefixes capability process)
  | 0, _, _, small, _, _, _ => absurd small (Nat.not_lt_zero _)
  | fuel + 1, capability, process, small, typed, object, processTyped => by
      cases capability with
      | bvar index => exact .refl _
      | fvar name => exact .refl _
      | lambda binder body => cases typed
      | multiLambda arity binders body => cases typed
      | subst body replacement => simp [isObjectPattern] at object
      | collection kind elements rest =>
          rcases hasType_collection_inversion typed with ⟨_, typeIs, _⟩ |
            ⟨rule, parameterName, elementType, member, shape, typeIs, elementsTyped⟩
          · cases typeIs
          · simp only [ambientCommCalc, terms, commTerms, prefixRule, capRule, List.cons_append, List.nil_append,
              List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
              rfl | rfl | rfl <;> simp_all [GrammarRule.bareParams]
      | apply label arguments =>
          obtain ⟨rule, member, rfl, notBare, typeIs, argumentsTyped⟩ := hasType_apply_inversion typed
          have objects : ∀ argument ∈ arguments, isObjectPattern argument = true := by
            simpa [isObjectPattern, isObjectPatternList_iff] using object
          have argumentSmall : ∀ argument ∈ arguments, size argument < fuel := by
            intro argument inArguments
            have := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.size_lt_of_mem inArguments
            simp only [size] at small
            omega
          simp only [ambientCommCalc, terms, commTerms, prefixRule, capRule, List.cons_append, List.nil_append,
            List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl <;> simp only [capType, TypeExpr.base.injEq] at typeIs <;>
            try (exact absurd typeIs (by decide))
          -- `in n`, `out n`, `open n`: the pure calculus's prefix
          · cases argumentsTyped with
            | cons _ parameter nameTyped rest =>
                cases rest
                simp only [parameterType?, Option.some.injEq] at parameter
                subst parameter
                exact capPrefix_equivalent (by simp) nameTyped processTyped
          · cases argumentsTyped with
            | cons _ parameter nameTyped rest =>
                cases rest
                simp only [parameterType?, Option.some.injEq] at parameter
                subst parameter
                exact capPrefix_equivalent (by simp) nameTyped processTyped
          · cases argumentsTyped with
            | cons _ parameter nameTyped rest =>
                cases rest
                simp only [parameterType?, Option.some.injEq] at parameter
                subst parameter
                exact capPrefix_equivalent (by simp) nameTyped processTyped
          -- the empty path: nothing
          · cases argumentsTyped
            exact eps_equivalent processTyped
          -- a path: its first capability's prefixes before the rest's
          · cases argumentsTyped with
            | @cons _ first _ _ _ _ _ firstParameter firstTyped rest =>
                cases rest with
                | @cons _ second _ _ _ _ _ secondParameter secondTyped last =>
                    cases last
                    simp only [parameterType?, Option.some.injEq] at firstParameter secondParameter
                    subst firstParameter secondParameter
                    have secondEquivalent := prefixes_equivalent fuel
                      (argumentSmall _ (List.mem_cons_of_mem _ List.mem_cons_self)) secondTyped
                      (objects _ (List.mem_cons_of_mem _ List.mem_cons_self)) processTyped
                    have secondPrefixed := (SortedEquiv.typed_iff secondEquivalent).mp
                      (acap_typed secondTyped processTyped)
                    have firstEquivalent := prefixes_equivalent fuel (argumentSmall _ List.mem_cons_self) firstTyped
                      (objects _ List.mem_cons_self) secondPrefixed
                    exact .trans _ _ _ (dot_equivalent firstTyped secondTyped processTyped)
                      (.trans _ _ _ (acap_fill firstTyped secondEquivalent) firstEquivalent)

/-- **A process is equivalent to its path normal form.** -/
theorem pathNF_equivalent : ∀ (fuel : Nat) {bound : List TypeExpr} {process : Pattern}, size process < fuel →
    HasType ambientCommCalc free bound process procType → isObjectPattern process = true →
    ProcEquiv ambientCommCalc ambientBlock free bound process (pathNF process)
  | 0, _, _, small, _, _ => absurd small (Nat.not_lt_zero _)
  | fuel + 1, bound, process, small, typed, object => by
      cases process with
      | bvar index => exact .refl _
      | fvar name => exact .refl _
      | lambda binder body => cases typed
      | multiLambda arity binders body => cases typed
      | subst body replacement => simp [isObjectPattern] at object
      | collection kind elements rest =>
          rcases hasType_collection_inversion typed with ⟨_, typeIs, _⟩ |
            ⟨rule, parameterName, elementType, member, shape, typeIs, elementsTyped⟩
          · cases typeIs
          · simp only [ambientCommCalc, terms, commTerms, prefixRule, capRule, List.cons_append, List.nil_append,
              List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
              rfl | rfl | rfl <;>
              simp [GrammarRule.bareParams] at shape
            obtain ⟨rfl, rfl, rfl⟩ := shape
            have tailNone : rest = none := by
              simpa [isObjectPattern] using (Bool.and_eq_true _ _).mp object |>.1
            subst tailNone
            have objects : ∀ element ∈ elements, isObjectPattern element = true := by
              simpa [isObjectPattern, isObjectPatternList_iff] using object
            have members : Members ambientCommCalc ambientBlock free bound elements :=
              fun element member => elementsHaveType_iff.mp elementsTyped element member
            have related : List.Forall₂ (ProcEquiv ambientCommCalc ambientBlock free bound) elements
                (elements.map pathNF) := by
              rw [List.forall₂_map_right_iff]
              refine List.forall₂_same.mpr fun element member => ?_
              have elementSmall : size element < fuel := by
                have := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.size_lt_of_mem member
                simp only [size] at small
                omega
              exact pathNF_equivalent fuel elementSmall (members element member) (objects element member)
            simp only [pathNF, pathNFList_eq_map]
            exact collection_congr (language := ambientCommCalc) (block := ambientBlock) none members related []
              Members.nil
      | apply label arguments =>
          obtain ⟨rule, member, rfl, notBare, typeIs, argumentsTyped⟩ := hasType_apply_inversion typed
          have objects : ∀ argument ∈ arguments, isObjectPattern argument = true := by
            simpa [isObjectPattern, isObjectPatternList_iff] using object
          have argumentSmall : ∀ argument ∈ arguments, size argument < fuel := by
            intro argument inArguments
            have := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.size_lt_of_mem inArguments
            simp only [size] at small
            omega
          simp only [ambientCommCalc, terms, commTerms, prefixRule, capRule, List.cons_append, List.nil_append,
            List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl <;> simp only [procType, TypeExpr.base.injEq] at typeIs <;>
            try (exact absurd typeIs (by decide))
          · -- inaction
            cases argumentsTyped
            exact .refl _
          · exact absurd ⟨"ps", .hashBag, .base "Proc", rfl⟩ notBare
          · -- restriction
            cases argumentsTyped with
            | cons representation parameterType argumentTyped rest =>
                cases rest
                obtain ⟨body, rfl⟩ :=
                  (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mp representation
                simp only [parameterType?, Option.some.injEq] at parameterType
                subst parameterType
                cases argumentTyped with
                | lambda bodyTyped =>
                    have bodySmall : size body < fuel := by
                      have := argumentSmall _ List.mem_cons_self
                      simp only [size] at this
                      omega
                    have bodyObject : isObjectPattern body = true := by
                      simpa [isObjectPattern] using objects _ List.mem_cons_self
                    exact restrict_fill (language := ambientCommCalc) (block := ambientBlock)
                      (pathNF_equivalent fuel bodySmall bodyTyped bodyObject)
          · -- replication
            cases argumentsTyped with
            | @cons _ argument _ _ _ _ representation parameterType argumentTyped rest =>
                cases rest
                simp only [parameterType?, Option.some.injEq] at parameterType
                subst parameterType
                exact Mettapedia.GSLT.LanguageDef.RestrictionBlocks.replicate_fill (language := ambientCommCalc)
                  (block := ambientRepBlock)
                  (pathNF_equivalent fuel (argumentSmall _ List.mem_cons_self) argumentTyped
                    (objects _ List.mem_cons_self))
          · -- an ambient
            cases argumentsTyped with
            | @cons _ name _ _ _ _ _ nameParameter nameTyped rest =>
                cases rest with
                | @cons _ content _ _ _ _ _ contentParameter contentTyped last =>
                    cases last
                    simp only [parameterType?, Option.some.injEq] at nameParameter contentParameter
                    subst nameParameter contentParameter
                    have nameSame : pathNF name = name := by
                      rcases name_cases nameTyped rfl (objects _ List.mem_cons_self) with
                        ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> rfl
                    rw [pathNF_apply_of_ne (by decide), List.map_cons, List.map_cons, List.map_nil, nameSame]
                    exact amb_fill nameTyped (pathNF_equivalent fuel
                      (argumentSmall _ (List.mem_cons_of_mem _ List.mem_cons_self)) contentTyped
                      (objects _ (List.mem_cons_of_mem _ List.mem_cons_self)))
          -- `in n.P`, `out n.P`, `open n.P`
          all_goals try (
            cases argumentsTyped with
            | @cons _ name _ _ _ _ _ nameParameter nameTyped rest =>
                cases rest with
                | @cons _ content _ _ _ _ _ contentParameter contentTyped last =>
                    cases last
                    simp only [parameterType?, Option.some.injEq] at nameParameter contentParameter
                    subst nameParameter contentParameter
                    have nameSame : pathNF name = name := by
                      rcases name_cases nameTyped rfl (objects _ List.mem_cons_self) with
                        ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> rfl
                    rw [pathNF_apply_of_ne (by decide), List.map_cons, List.map_cons, List.map_nil, nameSame]
                    exact prefix_fill (by simp) nameTyped (pathNF_equivalent fuel
                      (argumentSmall _ (List.mem_cons_of_mem _ List.mem_cons_self)) contentTyped
                      (objects _ (List.mem_cons_of_mem _ List.mem_cons_self))))
          -- a capability prefix: the prefixes it makes
          · cases argumentsTyped with
            | @cons _ capability _ _ _ _ _ capabilityParameter capabilityTyped rest =>
                cases rest with
                | @cons _ content _ _ _ _ _ contentParameter contentTyped last =>
                    cases last
                    simp only [parameterType?, Option.some.injEq] at capabilityParameter contentParameter
                    subst capabilityParameter contentParameter
                    have contentEquivalent := pathNF_equivalent fuel
                      (argumentSmall _ (List.mem_cons_of_mem _ List.mem_cons_self)) contentTyped
                      (objects _ (List.mem_cons_of_mem _ List.mem_cons_self))
                    have normalTyped := (SortedEquiv.typed_iff contentEquivalent).mp contentTyped
                    show ProcEquiv ambientCommCalc ambientBlock free bound (.apply "ACap" [capability, content])
                      (prefixes capability (pathNF content))
                    exact .trans _ _ _ (acap_fill capabilityTyped contentEquivalent)
                      (prefixes_equivalent (size capability + 1) (Nat.lt_succ_self _) capabilityTyped
                        (objects _ List.mem_cons_self) normalTyped)
          -- the input of a name: its body, under the binder
          · cases argumentsTyped with
            | cons representation parameterType argumentTyped rest =>
                cases rest
                obtain ⟨body, rfl⟩ :=
                  (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mp representation
                simp only [parameterType?, Option.some.injEq] at parameterType
                subst parameterType
                cases argumentTyped with
                | lambda bodyTyped =>
                    have bodySmall : size body < fuel := by
                      have := argumentSmall _ List.mem_cons_self
                      simp only [size] at this
                      omega
                    have bodyObject : isObjectPattern body = true := by
                      simpa [isObjectPattern] using objects _ List.mem_cons_self
                    rw [pathNF_apply_of_ne (by decide), List.map_cons, List.map_nil]
                    exact inName_fill (pathNF_equivalent fuel bodySmall bodyTyped bodyObject)
          -- the output of a name: a variable
          · cases argumentsTyped with
            | @cons _ name _ _ _ _ _ parameter nameTyped rest =>
                cases rest
                simp only [parameterType?, Option.some.injEq] at parameter
                subst parameter
                have nameSame : pathNF name = name := by
                  rcases name_cases nameTyped rfl (objects _ List.mem_cons_self) with
                    ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> rfl
                rw [pathNF_apply_of_ne (by decide), List.map_cons, List.map_nil, nameSame]
                exact .refl _
          -- the input of a capability: its body, under the binder
          · cases argumentsTyped with
            | cons representation parameterType argumentTyped rest =>
                cases rest
                obtain ⟨body, rfl⟩ :=
                  (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mp representation
                simp only [parameterType?, Option.some.injEq] at parameterType
                subst parameterType
                cases argumentTyped with
                | lambda bodyTyped =>
                    have bodySmall : size body < fuel := by
                      have := argumentSmall _ List.mem_cons_self
                      simp only [size] at this
                      omega
                    have bodyObject : isObjectPattern body = true := by
                      simpa [isObjectPattern] using objects _ List.mem_cons_self
                    rw [pathNF_apply_of_ne (by decide), List.map_cons, List.map_nil]
                    exact inCap_fill (pathNF_equivalent fuel bodySmall bodyTyped bodyObject)
          -- the output of a capability: its own normal form
          · cases argumentsTyped with
            | cons _ parameter capabilityTyped rest =>
                cases rest
                simp only [parameterType?, Option.some.injEq] at parameter
                subst parameter
                rw [pathNF_apply_of_ne (by decide), List.map_cons, List.map_nil,
                  pathNF_capability (size _ + 1) (Nat.lt_succ_self _) capabilityTyped (objects _ List.mem_cons_self)]
                exact .refl _

end Mettapedia.Languages.ProcessCalculi.Ambient.Comm
