import Mettapedia.GSLT.Parsing.ClassAwareChartDemand
import Mettapedia.GSLT.Parsing.ClassAwareChartClosure

/-! Root-directed demand saturation retains every ParserPack derivation.
The proof follows source derivations and their left-to-right bodies; needed
children are justified by recognized prefixes, independently of the backend. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareChartDemand

open ClassAwarePackedForest ClassAwarePackedForestSaturation
open ClassAwareParserPackCorrespondence ClassAwareParserPackEnumeration ParserProfileSemantics
open ClassAwareParserPackCertificate ClassAwareNativeForestQualification PresentationExprSemantics

theorem Saturated.body_requested {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {state : State} (valid : Saturated profile plan input state)
    (position : Fin plan.structural.length) (start : Nat)
    (needed : ((plan.structural.get position).resultSort, start) ∈ state.requests) :
    bodyRequests (recognizedNodeKeys (forest state)) profile input (plan.structural.get position).items start ⊆ state.requests := by
  intro request member
  apply valid.requests
  apply List.mem_flatMap.mpr
  refine ⟨((plan.structural.get position).resultSort, start), needed, ?_⟩
  apply List.mem_flatMap.mpr
  exact ⟨_, List.get_mem _ position, by simpa using member⟩

theorem Saturated.lexical_family {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {state : State} (valid : Saturated profile plan input state)
    (position : Fin plan.lexical.productions.length) {start stop : Nat} {children : List CST}
    (needed : ((plan.lexical.productions.get position).resultSort, start) ∈ state.requests)
    (matched : CSTTerminalMatchesAt profile input (plan.lexical.productions.get position).matcher start stop children) :
    (⟨⟨(plan.lexical.productions.get position).resultSort, start, stop⟩, .lexical position.val,
      [.terminal (plan.lexical.productions.get position).matcher start stop]⟩ : Family) ∈ state.families := by
  apply valid.lexical
  apply List.mem_flatMap.mpr
  refine ⟨((plan.lexical.productions.get position).resultSort, start), needed, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨position, List.mem_finRange position, ?_⟩
  simp only [beq_self_eq_true, ↓reduceIte]
  rw [terminalMatch?_complete matched]
  exact List.mem_singleton_self _

theorem Saturated.structural_family {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {state : State} (valid : Saturated profile plan input state)
    (position : Fin plan.structural.length) {start : Nat} (body : RecognizedItemsRow)
    (needed : ((plan.structural.get position).resultSort, start) ∈ state.requests)
    (member : body ∈ enumerateRecognizedItems (forest state) profile input (plan.structural.get position).items start) :
    (⟨⟨(plan.structural.get position).resultSort, start, body.stop⟩, .structural position.val, body.children⟩ : Family) ∈
      state.families := by
  apply valid.structural
  apply List.mem_flatMap.mpr
  refine ⟨((plan.structural.get position).resultSort, start), needed, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨position, List.mem_finRange position, ?_⟩
  simp only [beq_self_eq_true, ↓reduceIte]
  exact List.mem_map.mpr ⟨body, member, rfl⟩

theorem Saturated.derivation_unfolds {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {state : State} (valid : Saturated profile plan input state)
    {sort : String} {start stop : Nat} {tree : CST}
    (derivation : ParserPackDerivesAt profile plan input sort start stop tree)
    (needed : (sort, start) ∈ state.requests) :
    Unfolds (forest state) sort (Certificate.ofDerivation derivation) := by
  refine ParserPackDerivesAt.rec
    (motive_1 := fun sort start _ _ derivation =>
      (sort, start) ∈ state.requests → Unfolds (forest state) sort (Certificate.ofDerivation derivation))
    (motive_2 := fun items start _ _ derivation =>
      bodyRequests (recognizedNodeKeys (forest state)) profile input items start ⊆ state.requests →
        ItemsUnfold (forest state) (ItemsCertificate.ofDerivation derivation))
    ?_ ?_ ?_ ?_ ?_ derivation needed <;> clear derivation needed
  · intro start stop position bounded matcher resultSort ruleLabel children matcherEq sortEq labelEq matched needed
    let row : Fin plan.lexical.productions.length := ⟨position, bounded⟩
    have neededRow : ((plan.lexical.productions.get row).resultSort, start) ∈ state.requests := by
      rw [sortEq]
      exact needed
    have matchedRow : CSTTerminalMatchesAt profile input (plan.lexical.productions.get row).matcher start stop children := by
      rw [matcherEq]
      exact matched
    have present := valid.lexical_family row neededRow matchedRow
    intro family member
    simp only [Certificate.ofDerivation, certificateFamilies, List.mem_singleton] at member
    subst family
    simpa only [row, matcherEq, sortEq, certificateFamily, forest] using present
  · intro start stop trees position bounded resultSort ruleLabel sortEq labelEq body bodyIH needed
    let row : Fin plan.structural.length := ⟨position, bounded⟩
    have neededRow : ((plan.structural.get row).resultSort, start) ∈ state.requests := by
      rw [sortEq]
      exact needed
    have children := bodyIH (valid.body_requested row _ neededRow)
    have member := items_row_mem_enumerateRecognizedItems body children
    have present := valid.structural_family row _ neededRow member
    intro family occurs
    simp only [Certificate.ofDerivation, certificateFamilies, List.mem_cons] at occurs
    rcases occurs with rfl | tail
    · simpa only [row, sortEq, certificateFamily, forest] using present
    · exact children family tail
  · intro cursor requests family member
    simp [ItemsCertificate.ofDerivation, itemsFamilies] at member
  · intro matcher start middle items stop children matched rest restIH requests
    have terminalEq := terminalMatch?_complete (show CSTTerminalMatchesAt profile input _ _ _ matched.cst from ⟨matched, rfl⟩)
    have tailRequests : bodyRequests (recognizedNodeKeys (forest state)) profile input items middle ⊆ state.requests := by
      simpa [bodyRequests, terminalEq] using requests
    exact restIH tailRequests
  · intro resultSort start middle tree items stop children head rest headIH restIH requests
    have headNeeded : (resultSort, start) ∈ state.requests := requests (by simp [bodyRequests])
    have headUnfolds := headIH headNeeded
    have keyMember := certificateKey_mem_recognizedNodeKeys headUnfolds
    have keyEq : certificateKey resultSort (Certificate.ofDerivation head) = ⟨resultSort, start, middle⟩ := by
      cases head <;> rfl
    rw [keyEq] at keyMember
    have tailRequests : bodyRequests (recognizedNodeKeys (forest state)) profile input items middle ⊆ state.requests := by
      intro request member
      apply requests
      simp only [bodyRequests, List.mem_cons]
      right
      apply List.mem_flatMap.mpr
      exact ⟨⟨resultSort, start, middle⟩, List.mem_filter.mpr ⟨keyMember, by simp⟩, member⟩
    have tailUnfolds := restIH tailRequests
    intro family member
    simp only [ItemsCertificate.ofDerivation, itemsFamilies, List.mem_append] at member
    exact member.elim (headUnfolds family) (tailUnfolds family)

theorem Saturated.root_complete {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {state : State} (valid : Saturated profile plan input state) :
    RootParserComplete (ClassAwareChartClosure.recognizedForest plan input state.families) profile plan input := by
  intro tree derivation
  have unfolds := valid.derivation_unfolds derivation valid.root
  have familyPresent := unfolds _ (certificateFamily_mem_certificateFamilies _ _)
  have keyEq : certificateKey plan.lexical.startSort (Certificate.ofDerivation derivation) =
      ClassAwareChartClosure.rootKey plan input := by cases derivation <;> rfl
  have parentEq : (certificateFamily plan.lexical.startSort (Certificate.ofDerivation derivation)).parent =
      ClassAwareChartClosure.rootKey plan input := by cases derivation <;> rfl
  have recognized : ClassAwareChartClosure.rootKey plan input ∈ state.families.map Family.parent :=
    List.mem_map.mpr ⟨_, familyPresent, parentEq⟩
  exact ⟨by simp [ClassAwareChartClosure.recognizedForest, recognized, keyEq], unfolds⟩

end Mettapedia.GSLT.Parsing.ClassAwareChartDemand
