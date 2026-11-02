import Mettapedia.Languages.ProcessCalculi.Ambient.EncodingSteps

/-!
# Equivalences of mobile ambients

The ambient calculus has the restriction-block signature and the signature of replication, so the block theory's
equivalences hold for it. Here are the ones of its own constructors:

- an ambient, a capability, a prefix by a capability term and an input carry chains of laws through their processes
  (`amb_fill`, `prefix_fill`, `acap_fill`, `input_fill`);
- **the boundary law as an equivalence** (`boundary_equivalent`): `m[(νx) P] ≡ (νx) m↑[P]`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Full

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc commTerms capRule capType)

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars liftBVarsList_eq_map)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (ProcEquiv SortedEquiv recoverValue?_one recoverValue?_zero
  instantiateValue?_one instantiateValue?_shift restrict_typed)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (declaredInstanceAt_of_applyEquationAt)
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.RuleBinding (arguments? dependencies? occurrenceDeclared sitePattern? occurrenceAt?)
open Mettapedia.OSLF.MeTTaIL.ScopedEquationExecution (Orientation orientedRule applyEquationAt mem_applyEquationAt_iff)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (nameType procType)

/-! ## Typing -/

/-- **An ambient of a name around a process is a process.** -/
theorem amb_typed {free : FreeTypeContext} {bound : List TypeExpr} {name process : Pattern}
    (nameTyped : HasType ambientCoreCalc free bound name nameType)
    (processTyped : HasType ambientCoreCalc free bound process procType) :
    HasType ambientCoreCalc free bound (.apply "AAmb" [name, process]) procType :=
  .constructor (rule := ambientCoreCalc.terms[4]) (List.getElem_mem (by decide))
    (by simp [UsesBareCollection, GrammarRule.bareParams, ambientCoreCalc, terms])
    (.cons trivial rfl nameTyped (.cons trivial rfl processTyped .nil))

/-- **A capability of a name before a process is a process.** -/
theorem prefix_typed {free : FreeTypeContext} {bound : List TypeExpr} {label : String}
    (listed : label ∈ ["AIn", "AOut", "AOpen"]) {name process : Pattern}
    (nameTyped : HasType ambientCoreCalc free bound name nameType)
    (processTyped : HasType ambientCoreCalc free bound process procType) :
    HasType ambientCoreCalc free bound (.apply label [name, process]) procType := by
  have arguments : ArgumentsHaveTypes ambientCoreCalc free bound [name, process]
      [.simple "n" (.base "Name"), .simple "p" (.base "Proc")] :=
    .cons trivial rfl nameTyped (.cons trivial rfl processTyped .nil)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl
  · exact .constructor (rule := ambientCoreCalc.terms[5]) (List.getElem_mem (by decide))
      (by simp [UsesBareCollection, GrammarRule.bareParams, ambientCoreCalc, terms, prefixRule]) arguments
  · exact .constructor (rule := ambientCoreCalc.terms[6]) (List.getElem_mem (by decide))
      (by simp [UsesBareCollection, GrammarRule.bareParams, ambientCoreCalc, terms, prefixRule]) arguments
  · exact .constructor (rule := ambientCoreCalc.terms[7]) (List.getElem_mem (by decide))
      (by simp [UsesBareCollection, GrammarRule.bareParams, ambientCoreCalc, terms, prefixRule]) arguments

/-- **A capability term over a name**: `in n`, `out n`, `open n`. -/
theorem capTerm_typed {free : FreeTypeContext} {bound : List TypeExpr} {label : String}
    (listed : label ∈ ["CapIn", "CapOut", "CapOpen"]) {name : Pattern}
    (nameTyped : HasType ambientCoreCalc free bound name nameType) :
    HasType ambientCoreCalc free bound (.apply label [name]) capType := by
  have arguments : ArgumentsHaveTypes ambientCoreCalc free bound [name] [.simple "n" (.base "Name")] :=
    .cons trivial rfl nameTyped .nil
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl
  · exact .constructor (rule := ambientCoreCalc.terms[8]) (List.getElem_mem (by decide))
      (by simp [UsesBareCollection, GrammarRule.bareParams, ambientCoreCalc, terms, commTerms, capRule]) arguments
  · exact .constructor (rule := ambientCoreCalc.terms[9]) (List.getElem_mem (by decide))
      (by simp [UsesBareCollection, GrammarRule.bareParams, ambientCoreCalc, terms, commTerms, capRule]) arguments
  · exact .constructor (rule := ambientCoreCalc.terms[10]) (List.getElem_mem (by decide))
      (by simp [UsesBareCollection, GrammarRule.bareParams, ambientCoreCalc, terms, commTerms, capRule]) arguments

/-- **The empty path is a capability term.** -/
theorem eps_typed {free : FreeTypeContext} {bound : List TypeExpr} :
    HasType ambientCoreCalc free bound (.apply "CapEps" []) capType :=
  .constructor (rule := ambientCoreCalc.terms[11]) (List.getElem_mem (by decide))
    (by simp [UsesBareCollection, GrammarRule.bareParams, ambientCoreCalc, terms, commTerms]) .nil

/-- **The path of two capability terms is a capability term.** -/
theorem path_typed {free : FreeTypeContext} {bound : List TypeExpr} {first second : Pattern}
    (firstTyped : HasType ambientCoreCalc free bound first capType)
    (secondTyped : HasType ambientCoreCalc free bound second capType) :
    HasType ambientCoreCalc free bound (.apply "CapPath" [first, second]) capType :=
  .constructor (rule := ambientCoreCalc.terms[12]) (List.getElem_mem (by decide))
    (by simp [UsesBareCollection, GrammarRule.bareParams, ambientCoreCalc, terms, commTerms])
    (.cons trivial rfl firstTyped (.cons trivial rfl secondTyped .nil))

/-- **A capability term before a process is a process.** -/
theorem acap_typed {free : FreeTypeContext} {bound : List TypeExpr} {capability process : Pattern}
    (capabilityTyped : HasType ambientCoreCalc free bound capability capType)
    (processTyped : HasType ambientCoreCalc free bound process procType) :
    HasType ambientCoreCalc free bound (.apply "ACap" [capability, process]) procType :=
  .constructor (rule := ambientCoreCalc.terms[13]) (List.getElem_mem (by decide))
    (by simp [UsesBareCollection, GrammarRule.bareParams, ambientCoreCalc, terms, commTerms])
    (.cons trivial rfl capabilityTyped (.cons trivial rfl processTyped .nil))

/-- **An input of a name or of a capability, over a process binding it, is a process.** -/
theorem input_typed {free : FreeTypeContext} {bound : List TypeExpr} {label sort : String}
    (listed : (label, sort) ∈ [("AInName", "Name"), ("AInCap", "Cap")]) {body : Pattern}
    (bodyTyped : HasType ambientCoreCalc free (.base sort :: bound) body procType) :
    HasType ambientCoreCalc free bound (.apply label [.lambda none body]) procType := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at listed
  rcases listed with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact .constructor (rule := ambientCoreCalc.terms[14]) (List.getElem_mem (by decide))
      (by simp [UsesBareCollection, GrammarRule.bareParams, ambientCoreCalc, terms, commTerms])
      (.cons trivial rfl (.lambda bodyTyped) .nil)
  · exact .constructor (rule := ambientCoreCalc.terms[16]) (List.getElem_mem (by decide))
      (by simp [UsesBareCollection, GrammarRule.bareParams, ambientCoreCalc, terms, commTerms])
      (.cons trivial rfl (.lambda bodyTyped) .nil)

/-- **An output of a name or of a capability is a process.** -/
theorem output_typed {free : FreeTypeContext} {bound : List TypeExpr} {label sort : String}
    (listed : (label, sort) ∈ [("AOutName", "Name"), ("AOutCap", "Cap")]) {message : Pattern}
    (messageTyped : HasType ambientCoreCalc free bound message (.base sort)) :
    HasType ambientCoreCalc free bound (.apply label [message]) procType := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at listed
  rcases listed with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact .constructor (rule := ambientCoreCalc.terms[15]) (List.getElem_mem (by decide))
      (by simp [UsesBareCollection, GrammarRule.bareParams, ambientCoreCalc, terms, commTerms])
      (.cons trivial rfl messageTyped .nil)
  · exact .constructor (rule := ambientCoreCalc.terms[17]) (List.getElem_mem (by decide))
      (by simp [UsesBareCollection, GrammarRule.bareParams, ambientCoreCalc, terms, commTerms])
      (.cons trivial rfl messageTyped .nil)

/-! ## Contexts -/

/-- **An ambient carries chains through its process.** -/
theorem amb_fill {free : FreeTypeContext} {bound : List TypeExpr} {name first second : Pattern}
    (nameTyped : HasType ambientCoreCalc free bound name nameType)
    (equivalent : ProcEquiv ambientCoreCalc ambientBlock free bound first second) :
    ProcEquiv ambientCoreCalc ambientBlock free bound (.apply "AAmb" [name, first]) (.apply "AAmb" [name, second]) :=
  SortedEquiv.fill (.apply "AAmb" [name] .hole []) (fun _ typed => amb_typed nameTyped typed) equivalent

/-- **A capability carries chains through its continuation.** -/
theorem prefix_fill {free : FreeTypeContext} {bound : List TypeExpr} {label : String}
    (listed : label ∈ ["AIn", "AOut", "AOpen"]) {name first second : Pattern}
    (nameTyped : HasType ambientCoreCalc free bound name nameType)
    (equivalent : ProcEquiv ambientCoreCalc ambientBlock free bound first second) :
    ProcEquiv ambientCoreCalc ambientBlock free bound (.apply label [name, first]) (.apply label [name, second]) :=
  SortedEquiv.fill (.apply label [name] .hole []) (fun _ typed => prefix_typed listed nameTyped typed) equivalent

/-- **A prefix by a capability term carries chains through its continuation.** -/
theorem acap_fill {free : FreeTypeContext} {bound : List TypeExpr} {capability first second : Pattern}
    (capabilityTyped : HasType ambientCoreCalc free bound capability capType)
    (equivalent : ProcEquiv ambientCoreCalc ambientBlock free bound first second) :
    ProcEquiv ambientCoreCalc ambientBlock free bound (.apply "ACap" [capability, first])
      (.apply "ACap" [capability, second]) :=
  SortedEquiv.fill (.apply "ACap" [capability] .hole []) (fun _ typed => acap_typed capabilityTyped typed) equivalent

/-- **An input carries chains through its body**, under its binder. -/
theorem input_fill {free : FreeTypeContext} {bound : List TypeExpr} {label sort : String}
    (listed : (label, sort) ∈ [("AInName", "Name"), ("AInCap", "Cap")]) {first second : Pattern}
    (equivalent : ProcEquiv ambientCoreCalc ambientBlock free (.base sort :: bound) first second) :
    ProcEquiv ambientCoreCalc ambientBlock free bound (.apply label [.lambda none first])
      (.apply label [.lambda none second]) :=
  SortedEquiv.fill (.apply label [] (.lambda none .hole) []) (fun _ typed => input_typed listed typed) equivalent

/-! ## The boundary law -/

/-- **The boundary law, read through its declaration**: a restriction inside an ambient moves out over the ambient's
name, which does not use it and is read one binder deeper. -/
theorem boundary_instance {ambient : Nat} {name body : Pattern} (nameScoped : name.isWellScopedAt ambient = true)
    (bodyScoped : body.isWellScopedAt (1 + ambient) = true) :
    .apply "ANu" [.lambda none (.apply "AAmb" [liftBVars 0 1 name, body])] ∈
      applyEquationAt ambientCoreCalc ambient ambientBoundary .forward
        (.apply "AAmb" [name, .apply "ANu" [.lambda none body]]) := by
  have bodyScoped' : body.isWellScopedAt (ambient + 1) = true := by rwa [Nat.add_comm]
  have liftedScoped : (liftBVars 0 1 name).isWellScopedAt (ambient + 1) = true := by
    have lifted := Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_isWellScopedAt (cutoff := 0) (shift := 1)
      (ambient := ambient) (pattern := name) (by simpa using nameScoped)
    simpa [Nat.add_comm] using lifted
  rw [mem_applyEquationAt_iff]
  refine ⟨rfl, ?_, ?_, _, [("P", ⟨[.base "Name"], ambient, body⟩), ("m", ⟨[], ambient, name⟩)], rfl, rfl, ?_, ?_⟩
  · simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, bodyScoped', nameScoped]
  · simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, bodyScoped', liftedScoped]
  · simp only [matchRuleAt, matchRuleWithAt]
    refine mem_matchAtWith_apply.mpr ⟨_, rfl, mem_matchArgsAtWith_cons.mpr
      ⟨name, [.apply "ANu" [.lambda none body]], [("m", ⟨[], ambient, name⟩)], rfl, mem_matchAtWith_fvar.mpr ?_,
        mem_matchArgsAtWith_cons.mpr ⟨_, [], _, rfl, mem_matchAtWith_apply.mpr ⟨_, rfl,
          mem_matchArgsAtWith_cons.mpr ⟨_, [], _, rfl, mem_matchAtWith_lambda.mpr ⟨none, body, rfl,
            mem_matchAtWith_fvar.mpr ?_⟩, mem_matchArgsAtWith_nil.mpr ⟨rfl, rfl⟩⟩⟩,
          mem_matchArgsAtWith_nil.mpr ⟨rfl, rfl⟩⟩⟩⟩
    · simp [captureWith?_literal, capture?, orientedRule, ambientBoundary, dependencies?, arguments?,
        occurrenceDeclared, sitePattern?, occurrenceAt?, recoverValue?_zero nameScoped, assign, lookup]
    · simp [captureWith?_literal, capture?, orientedRule, ambientBoundary, dependencies?, arguments?,
        occurrenceDeclared, sitePattern?, occurrenceAt?, recoverValue?_one bodyScoped, assign, lookup]
  · simp [reduct?, instantiateAt?, instantiateWith?, instantiateArgsWith?, orientedRule, ambientBoundary, arguments?,
      dependencies?, occurrenceDeclared, sitePattern?, occurrenceAt?, lookup, instantiateValue?_one bodyScoped,
      instantiateValue?_shift nameScoped]

/-- **The boundary law as an equivalence**: `m[(νx) P] ≡ (νx) m↑[P]`. -/
theorem boundary_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {name body : Pattern}
    (nameTyped : HasType ambientCoreCalc free bound name nameType)
    (bodyTyped : HasType ambientCoreCalc free (nameType :: bound) body procType) :
    ProcEquiv ambientCoreCalc ambientBlock free bound (.apply "AAmb" [name, .apply "ANu" [.lambda none body]])
      (.apply "ANu" [.lambda none (.apply "AAmb" [liftBVars 0 1 name, body])]) := by
  have nameScoped : name.isWellScopedAt bound.length = true := nameTyped.isWellScopedAt
  have bodyScoped : body.isWellScopedAt (1 + bound.length) = true := by
    simpa [Nat.add_comm] using bodyTyped.isWellScopedAt
  have liftedTyped : HasType ambientCoreCalc free (nameType :: bound) (liftBVars 0 1 name) nameType := by
    simpa using Mettapedia.GSLT.LanguageDef.RestrictionBlocks.lift_typed (language := ambientCoreCalc)
      (inner := []) (inserted := [nameType]) (outer := bound) nameTyped
  have member : ambientBoundary ∈ ambientCoreCalc.equations := List.mem_append_right _ (List.mem_singleton_self _)
  exact SortedEquiv.ofInstance ⟨0, .declared (orientation := .forward) (ambient := bound.length) member rfl
    (declaredInstanceAt_of_applyEquationAt (boundary_instance nameScoped bodyScoped))⟩
    (amb_typed nameTyped (restrict_typed (block := ambientBlock) bodyTyped))
    (restrict_typed (block := ambientBlock) (amb_typed liftedTyped bodyTyped))

end Mettapedia.Languages.ProcessCalculi.Ambient.Full
