import Mettapedia.Languages.MeTTa.PeTTa.OutputPlanChildren

/-!
# Replaying a compiler layer on its actual source children

Only calls made by the layer need agreement. Held arguments remain held,
binding rows keep their order and shared child allowance, and branch output
construction retains its actual allocation and aliases.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.OutputPlan

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

theorem ArgumentsRel.with_property {child : Supply → Atom → Result → Prop} {property : Atom → Prop}
    {held : Nat → Bool} {supply : Supply} {index : Nat} {input : List Atom} {result : Results}
    (rule : ArgumentsRel child held supply index input result)
    (all : ∀ expression ∈ input, property expression) :
    ArgumentsRel (fun s e r => child s e r ∧ property e) held supply index input result := by
  induction rule with
  | nil supply index => exact .nil supply index
  | heldArgument supply index first rest later heldHere tail ih =>
      exact .heldArgument supply index first rest later heldHere
        (ih (fun expression present => all expression (List.mem_cons_of_mem first present)))
  | evaluatedArgument supply index first rest entered later evaluatedHere head tail ih =>
      exact .evaluatedArgument supply index first rest entered later evaluatedHere
        ⟨head,all first List.mem_cons_self⟩
        (ih (fun expression present => all expression (List.mem_cons_of_mem first present)))

theorem BindingsRel.with_property {child : Supply → Atom → Result → Prop} {property : Atom → Prop}
    {supply : Supply} {rows : List Atom} {body : Atom} {result : Result}
    (rule : BindingsRel child supply rows body result)
    (bodyProperty : property body) (all : ∀ expression ∈ rowTerms rows, property expression) :
    BindingsRel (fun s e r => child s e r ∧ property e) supply rows body result := by
  induction rule with
  | last supply row pattern value body p v b parsed patternRule valueRule bodyRule =>
      have members := rowTerm_member [row] row pattern value List.mem_cons_self parsed
      exact .last supply row pattern value body p v b parsed
        ⟨patternRule,all pattern members.1⟩ ⟨valueRule,all value members.2⟩ ⟨bodyRule,bodyProperty⟩
  | next supply row nextRow pattern value body rest p v b parsed patternRule valueRule tail ih =>
      have members := rowTerm_member (row :: nextRow :: rest) row pattern value List.mem_cons_self parsed
      have later : ∀ expression ∈ rowTerms (nextRow :: rest), property expression := by
        intro expression present
        apply all expression
        simp only [rowTerms,parsed]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ present)
      exact .next supply row nextRow pattern value body rest p v b parsed
        ⟨patternRule,all pattern members.1⟩ ⟨valueRule,all value members.2⟩ (ih bodyProperty later)

theorem CasesRel.with_property {context : Context} {child : Supply → Atom → Result → Prop}
    {property : Atom → Prop} {supply : Supply} {rows : SpaceSemantics.Cases} {output : Atom}
    {result : Supply × List Atom} (rule : CasesRel context child supply rows output result)
    (all : ∀ row ∈ rows, property row.2) :
    CasesRel context (fun s e r => child s e r ∧ property e) supply rows output result := by
  induction rule with
  | nil supply output => exact .nil supply output
  | cons supply pattern body output rest compiled selected later passive bodyRule branchRule tail ih =>
      exact .cons supply pattern body output rest compiled selected later passive
        ⟨bodyRule,all (pattern,body) List.mem_cons_self⟩ branchRule
        (ih (fun row present => all row (List.mem_cons_of_mem _ present)))

theorem Layer.with_property {context : Context} {child : Supply → Atom → Result → Prop}
    {property : Atom → Prop} {supply : Supply} {shape : Shape} {result : Result}
    (rule : Layer context child supply shape result)
    (all : ∀ expression ∈ shape.children, property expression) :
    Layer context (fun s e r => child s e r ∧ property e) supply shape result := by
  cases rule with
  | value expression => exact .value supply expression
  | quoted expression => exact .quoted supply expression
  | empty => exact .empty supply
  | binding pattern value body p v b patternRule valueRule bodyRule =>
      exact .binding supply pattern value body p v b
        ⟨patternRule,all pattern (by simp [Shape.children])⟩
        ⟨valueRule,all value (by simp [Shape.children])⟩
        ⟨bodyRule,all body (by simp [Shape.children])⟩
  | bindings rows body result rowRules =>
      exact .bindings supply rows body result
        (rowRules.with_property (all body List.mem_cons_self)
          (fun expression present => all expression (List.mem_cons_of_mem _ present)))
  | alternatives values compiled selected arguments branches =>
      exact .alternatives supply values compiled selected (arguments.with_property all) branches
  | collection body compiled bodyRule =>
      exact .collection supply body compiled ⟨bodyRule,all body (by simp [Shape.children])⟩
  | first body compiled bodyRule =>
      exact .first supply body compiled ⟨bodyRule,all body (by simp [Shape.children])⟩
  | condition condition yes no tested yesPlan noPlan yesGoal noGoal testedRule yesRule noRule yesBranch noBranch =>
      exact .condition supply condition yes no tested yesPlan noPlan yesGoal noGoal
        ⟨testedRule,all condition (by simp [Shape.children])⟩
        ⟨yesRule,all yes (by simp [Shape.children])⟩
        ⟨noRule,all no (by simp [Shape.children])⟩ yesBranch noBranch
  | selection key rows parsed selected compiled rowReader keyRule caseRules =>
      exact .selection supply key rows parsed selected compiled rowReader
        ⟨keyRule,all key List.mem_cons_self⟩
        (caseRules.with_property (fun row present => all row.2
          (List.mem_cons_of_mem _ (parsed_case_member rowReader row present))))
  | query location pattern body space compiled locationRule bodyRule =>
      exact .query supply location pattern body space compiled
        ⟨locationRule,all location (by simp [Shape.children])⟩
        ⟨bodyRule,all body (by simp [Shape.children])⟩
  | nativeCall head arguments compiled mode nativeHead argumentRules modeRule =>
      exact .nativeCall supply head arguments compiled mode nativeHead (argumentRules.with_property all) modeRule
  | authoredCall head arguments compiled signature notNative argumentRules lookup =>
      exact .authoredCall supply head arguments compiled signature notNative (argumentRules.with_property all) lookup
  | constructor head arguments compiled notNative argumentRules notRegistered notCallable =>
      exact .constructor supply head arguments compiled notNative (argumentRules.with_property all) notRegistered notCallable
  | grounded head arguments compiled argumentRules =>
      exact .grounded supply head arguments compiled (argumentRules.with_property all)
  | listHead head arguments first compiled emitted headRule argumentRules output normal =>
      exact .listHead supply head arguments first compiled emitted
        ⟨headRule,all (.expression head) List.mem_cons_self⟩
        (argumentRules.with_property (fun expression present => all expression (List.mem_cons_of_mem _ present))) output normal

theorem perform_replay (context : Context) (before after : Supply → Atom → Option Result)
    (supply : Supply) (shape : Shape) (result : Result)
    (same : ∀ s e r, e ∈ shape.children → before s e = some r → after s e = some r)
    (computed : perform context before supply shape = some result) :
    perform context after supply shape = some result := by
  have source := layer_has_rule context before (fun s e r => before s e = some r)
    (fun _ _ _ edge => edge) supply shape result computed
  have witnessed := source.with_property (fun _ present => present)
  exact layer_of_rule context after _ (fun s e r edge => same s e r edge.2 edge.1) witnessed

end Mettapedia.Languages.MeTTa.PeTTa.OutputPlan
