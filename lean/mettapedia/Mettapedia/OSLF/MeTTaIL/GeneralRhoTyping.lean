import Mettapedia.OSLF.MeTTaIL.GeneralRhoRuntime
import Mettapedia.GSLT.LanguageDef.ReflectiveInstantiationTyping

/-!
# Original-grammar typing of the contextual rho family

Typing uses the shipped declaration positions, including the bare parallel
collection and the Name binder on input. Derived presentation judgments are
translated structurally to the original grammar; no finite source decoder
or caller-supplied typing enumeration participates.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRho

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.Examples.ScopedRhoBinding
open DerivedPresentationSyntax

def typeFree (free : FreeSortContext) : FreeTypeContext :=
  fun name => (free name).map TypeExpr.base

def typeBound (bound : List String) : List TypeExpr := bound.map TypeExpr.base

def unitRule : GrammarRule := rhoCalc.terms[0]
def dropRule : GrammarRule := rhoCalc.terms[1]
def quoteRule : GrammarRule := rhoCalc.terms[2]
def parallelRule : GrammarRule := rhoCalc.terms[3]
def outputRule : GrammarRule := rhoCalc.terms[4]
def inputRule : GrammarRule := rhoCalc.terms[5]

theorem unit_typed (free : FreeTypeContext) (bound : List TypeExpr) :
    HasType language free bound (.apply "PZero" []) (.base "Proc") :=
  .constructor (rule := unitRule) (by decide +kernel)
    (by simp [UsesBareCollection, unitRule, rhoCalc]) .nil

theorem drop_typed {free : FreeTypeContext} {bound : List TypeExpr} {name : Pattern}
    (typed : HasType language free bound name (.base "Name")) :
    HasType language free bound (.apply "PDrop" [name]) (.base "Proc") :=
  .constructor (rule := dropRule) (by decide +kernel)
    (by simp [UsesBareCollection, dropRule, rhoCalc, TypeExpr.name, TypeExpr.baseType])
    (.cons (by trivial) rfl typed .nil)

theorem quote_typed {free : FreeTypeContext} {bound : List TypeExpr} {body : Pattern}
    (typed : HasType language free bound body (.base "Proc")) :
    HasType language free bound (.apply "NQuote" [body]) (.base "Name") :=
  .constructor (rule := quoteRule) (by decide +kernel)
    (by simp [UsesBareCollection, quoteRule, rhoCalc, TypeExpr.proc, TypeExpr.baseType])
    (.cons (by trivial) rfl typed .nil)

theorem output_arguments {free : FreeTypeContext} {bound : List TypeExpr} {channel payload : Pattern}
    (channelTyped : HasType language free bound channel (.base "Name"))
    (payloadTyped : HasType language free bound payload (.base "Proc")) :
    ArgumentsHaveTypes language free bound [channel, payload] outputRule.params :=
  .cons (by trivial) rfl channelTyped (.cons (by trivial) rfl payloadTyped .nil)

theorem output_typed {free : FreeTypeContext} {bound : List TypeExpr} {channel payload : Pattern}
    (channelTyped : HasType language free bound channel (.base "Name"))
    (payloadTyped : HasType language free bound payload (.base "Proc")) :
    HasType language free bound (output channel payload) (.base "Proc") :=
  .constructor (rule := outputRule) (by decide +kernel)
    (by simp [UsesBareCollection, outputRule, rhoCalc])
    (output_arguments channelTyped payloadTyped)

theorem input_arguments {free : FreeTypeContext} {bound : List TypeExpr} {channel body : Pattern}
    (channelTyped : HasType language free bound channel (.base "Name"))
    (bodyTyped : HasType language free (.base "Name" :: bound) body (.base "Proc")) :
    ArgumentsHaveTypes language free bound [channel, .lambda none body] inputRule.params :=
  .cons (by trivial) rfl channelTyped (.cons (by trivial) rfl (.lambda bodyTyped) .nil)

theorem input_typed {free : FreeTypeContext} {bound : List TypeExpr} {channel body : Pattern}
    (channelTyped : HasType language free bound channel (.base "Name"))
    (bodyTyped : HasType language free (.base "Name" :: bound) body (.base "Proc")) :
    HasType language free bound (input channel body) (.base "Proc") :=
  .constructor (rule := inputRule) (by decide +kernel)
    (by simp [UsesBareCollection, inputRule, rhoCalc])
    (input_arguments channelTyped bodyTyped)

theorem parallel_typed {free : FreeTypeContext} {bound : List TypeExpr} {elements : List Pattern}
    (typed : ElementsHaveType language free bound elements (.base "Proc")) :
    HasType language free bound (.collection .hashBag elements none) (.base "Proc") :=
  .collectionConstructor (rule := parallelRule) (by decide +kernel) rfl typed

theorem source_typed {free : FreeTypeContext} {bound : List TypeExpr}
    {channel body payload : Pattern} {rest : List Pattern}
    (channelTyped : HasType language free bound channel (.base "Name"))
    (bodyTyped : HasType language free (.base "Name" :: bound) body (.base "Proc"))
    (payloadTyped : HasType language free bound payload (.base "Proc"))
    (restTyped : ElementsHaveType language free bound rest (.base "Proc")) :
    HasType language free bound (source channel body payload rest) (.base "Proc") :=
  parallel_typed (.cons (input_typed channelTyped bodyTyped)
    (.cons (output_typed channelTyped payloadTyped) restTyped))

mutual
theorem derived_name_typed {scope : QuoteScope} {free : FreeSortContext} {bound : List String} {name : Pattern}
    (typed : NameWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound name) :
    HasType language (typeFree free) (typeBound bound) name (.base "Name") := by
  cases typed with
  | bvar selected =>
      apply HasType.bvar
      simp only [typeBound, List.getElem?_map, selected, Option.map_some]
      rfl
  | fvar selected =>
      apply HasType.fvar
      simp only [typeFree, selected, Option.map_some]
      rfl
  | quote process => exact quote_typed (derived_process_typed process)
termination_by sizeOf name

theorem derived_process_typed {scope : QuoteScope} {free : FreeSortContext} {bound : List String} {process : Pattern}
    (typed : ProcWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound process) :
    HasType language (typeFree free) (typeBound bound) process (.base "Proc") := by
  cases typed with
  | bvar selected =>
      apply HasType.bvar
      simp only [typeBound, List.getElem?_map, selected, Option.map_some]
      rfl
  | fvar selected =>
      apply HasType.fvar
      simp only [typeFree, selected, Option.map_some]
      rfl
  | unit => exact unit_typed _ _
  | drop name => exact drop_typed (derived_name_typed name)
  | output channel payload => exact output_typed (derived_name_typed channel) (derived_process_typed payload)
  | input channel body => exact input_typed (derived_name_typed channel) (derived_process_typed body)
  | parallel processes => exact parallel_typed (derived_processes_typed processes)
termination_by sizeOf process

theorem derived_processes_typed {scope : QuoteScope} {free : FreeSortContext} {bound : List String} {processes : List Pattern}
    (typed : ProcListWellSorted (rhoReflectivePresentation.withQuoteScope scope) free bound processes) :
    ElementsHaveType language (typeFree free) (typeBound bound) processes (.base "Proc") := by
  cases typed with
  | nil => exact .nil _ _
  | cons process processes => exact .cons (derived_process_typed process) (derived_processes_typed processes)
termination_by sizeOf processes
end

def reflectiveWitness : LanguageDef.ReflectivePresentationWitness language
    rhoReflectivePresentation.toReflectivePresentationDecl where
  quote := quoteRule
  drop := dropRule
  unit := unitRule
  equation := rhoCalc.equations[0]
  quoteParameter := "p"
  dropParameter := "n"
  processSort := by decide +kernel
  nameSort := by decide +kernel
  quoteDropDistinct := by decide
  quoteUnique := by decide +kernel
  quoteCategory := rfl
  quoteParameters := rfl
  dropUnique := by decide +kernel
  dropCategory := rfl
  dropParameters := rfl
  unitUnique := by decide +kernel
  unitCategory := rfl
  unitParameters := rfl
  equationUnique := rfl
  equationShape := rfl
  contextFresh := by
    intro constructor found
    simp [rhoReflectivePresentation] at found

end Mettapedia.OSLF.MeTTaIL.GeneralRho
