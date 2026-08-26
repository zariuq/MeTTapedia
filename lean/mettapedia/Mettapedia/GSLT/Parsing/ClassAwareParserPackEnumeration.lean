import Mettapedia.GSLT.Parsing.ClassAwareParserPackCertificate

/-!
# Height-bounded enumeration of class-aware ParserPack derivations

`ParserPackDerivesAt` may have infinite proof fibres when an authored grammar
contains zero-width recursive cycles.  Consequently there is no honest finite
enumerator for every plan.  This module instead enumerates the exact finite
certificate/CST fibre below an explicit intrinsic derivation height.

The construction is independent of GLL and GLR output.  A later grammar
progress theorem may supply a complete height bound for a particular plan.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareParserPackEnumeration

open Mettapedia.GSLT.Parsing.ClassAwareParserPackCertificate
open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
open Mettapedia.GSLT.Parsing.ParserProfileSemantics
open Mettapedia.GSLT.Parsing.PresentationExprSemantics

/-- Finite output of one complete derivation enumeration. -/
structure DerivationRow where
  certificate : Certificate
  tree : CST
  deriving DecidableEq, Repr

/-- Finite output of one item-vector derivation enumeration. -/
structure ItemsRow where
  certificate : ItemsCertificate
  children : List CST
  deriving DecidableEq, Repr

/-- The unique possible terminal result at one cursor, when it exists. -/
def terminalMatch? (profile : ParserProfileLayer) (input : List Nat)
    (matcher : TerminalMatcher) (start : Nat) :
    Option (Nat × List CST) :=
  match matcher with
  | .any =>
      input[start]?.map fun codepoint =>
        (start + 1, [.terminal [codepoint] start (start + 1)])
  | .eof =>
      if start = input.length then some (start, []) else none
  | .char expected =>
      match input[start]? with
      | some codepoint =>
          if expected = codepoint then
            some (start + 1, [.terminal [codepoint] start (start + 1)])
          else none
      | none => none
  | .class className =>
      match input[start]? with
      | some codepoint =>
          if profile.classAccepts? className codepoint = some true then
            some (start + 1, [.terminal [codepoint] start (start + 1)])
          else none
      | none => none

/-- Executable terminal matching constructs the exact semantic witness. -/
def terminalMatch?_sound
    {profile : ParserProfileLayer} {input : List Nat}
    {matcher : TerminalMatcher} {start stop : Nat} {children : List CST}
    (accepted : terminalMatch? profile input matcher start =
      some (stop, children)) :
    CSTTerminalMatchesAt profile input matcher start stop children := by
  cases matcher with
  | any =>
      cases lookup : input[start]? with
      | none => simp [terminalMatch?, lookup] at accepted
      | some codepoint =>
          simp only [terminalMatch?, lookup, Option.map_some] at accepted
          cases accepted
          exact ⟨.any lookup, rfl⟩
  | eof =>
      by_cases atEnd : start = input.length
      · rw [terminalMatch?, if_pos atEnd] at accepted
        have pairExact : (start, []) = (stop, children) :=
          Option.some.inj accepted
        have stopExact : start = stop := congrArg Prod.fst pairExact
        have childrenExact : ([] : List CST) = children :=
          congrArg Prod.snd pairExact
        subst stop
        subst children
        exact ⟨.eof atEnd, rfl⟩
      · simp [terminalMatch?, atEnd] at accepted
  | char expected =>
      cases lookup : input[start]? with
      | none => simp [terminalMatch?, lookup] at accepted
      | some codepoint =>
          by_cases exactCodepoint : expected = codepoint
          · simp only [terminalMatch?, lookup, exactCodepoint, if_pos,
              Option.some.injEq, Prod.mk.injEq] at accepted
            rcases accepted with ⟨rfl, rfl⟩
            subst expected
            exact ⟨.char lookup, rfl⟩
          · simp [terminalMatch?, lookup, exactCodepoint] at accepted
  | «class» className =>
      cases lookup : input[start]? with
      | none => simp [terminalMatch?, lookup] at accepted
      | some codepoint =>
          by_cases classEvidence :
              profile.classAccepts? className codepoint = some true
          · simp only [terminalMatch?, lookup, classEvidence, if_pos,
              Option.some.injEq, Prod.mk.injEq] at accepted
            rcases accepted with ⟨rfl, rfl⟩
            exact ⟨.classMember lookup classEvidence, rfl⟩
          · simp [terminalMatch?, lookup, classEvidence] at accepted

/-- Every semantic terminal match is returned by the executable matcher. -/
theorem terminalMatch?_complete
    {profile : ParserProfileLayer} {input : List Nat}
    {matcher : TerminalMatcher} {start stop : Nat} {children : List CST}
    (matched : CSTTerminalMatchesAt profile input matcher
      start stop children) :
    terminalMatch? profile input matcher start = some (stop, children) := by
  rcases matched with ⟨matched, rfl⟩
  cases matched with
  | any lookup => simp [terminalMatch?, lookup, TerminalMatchesAt.cst]
  | eof atEnd => simp [terminalMatch?, atEnd, TerminalMatchesAt.cst]
  | char lookup => simp [terminalMatch?, lookup, TerminalMatchesAt.cst]
  | classMember lookup evidence =>
      change profile.classAccepts? _ _ = some true at evidence
      simp [terminalMatch?, lookup, evidence, TerminalMatchesAt.cst]

/-- Lexical rows do not recurse and are therefore available at every positive
height.  Physical production positions remain certificate identities. -/
def enumerateLexicalRows
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (resultSort : String) (start stop : Nat) :
    List DerivationRow :=
  (List.finRange plan.lexical.productions.length).flatMap fun position =>
    let production := plan.lexical.productions.get position
    if production.resultSort = resultSort then
      match terminalMatch? profile input production.matcher start with
      | some (actualStop, children) =>
          if actualStop = stop then
            [{ certificate :=
                .lexical position.val production.matcher start actualStop
               tree := .node production.label start actualStop children }]
          else []
      | none => []
    else []

mutual
  /-- Enumerate complete derivations whose intrinsic height is at most
  `fuel`.  Both lexical and structural production occurrences are inspected
  from the supplied plan. -/
  def enumerateDerivationsWithin
      (fuel : Nat) (profile : ParserProfileLayer)
      (plan : CompiledParserPackPlan) (input : List Nat)
      (resultSort : String) (start stop : Nat) : List DerivationRow :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
        enumerateLexicalRows profile plan input resultSort start stop ++
          (List.finRange plan.structural.length).flatMap fun position =>
            let production := plan.structural.get position
            if production.resultSort = resultSort then
              (enumerateItemsWithin fuel profile plan input production.items
                start stop).map fun body =>
                  { certificate :=
                      .structural position.val start stop body.certificate
                    tree := .node production.label start stop body.children }
            else []

  /-- Enumerate exact left-to-right item-vector derivations below a height
  bound.  Nonterminal split positions are finite because the requested final
  cursor bounds every monotone derivation cursor. -/
  def enumerateItemsWithin
      (fuel : Nat) (profile : ParserProfileLayer)
      (plan : CompiledParserPackPlan) (input : List Nat)
      (items : List PackItem) (start stop : Nat) : List ItemsRow :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
        match items with
        | [] =>
            if start = stop then
              [{ certificate := .nil start, children := [] }]
            else []
        | .terminal matcher :: rest =>
            match terminalMatch? profile input matcher start with
            | none => []
            | some (middle, _) =>
                (enumerateItemsWithin fuel profile plan input rest
                  middle stop).map fun tail =>
                    { certificate :=
                        .terminal matcher start middle tail.certificate
                      children := tail.children }
        | .nonterminal childSort :: rest =>
            (List.range (stop + 1)).flatMap fun middle =>
              (enumerateDerivationsWithin fuel profile plan input childSort
                start middle).flatMap fun head =>
                  (enumerateItemsWithin fuel profile plan input rest
                    middle stop).map fun tail =>
                      { certificate :=
                          .nonterminal childSort start middle
                            head.certificate tail.certificate
                        children := head.tree :: tail.children }
end

/-- Root enumeration uses the authored start sort and exact whole-input span. -/
def enumerateRootWithin
    (fuel : Nat) (profile : ParserProfileLayer)
    (plan : CompiledParserPackPlan) (input : List Nat) :
    List DerivationRow :=
  enumerateDerivationsWithin fuel profile plan input
    plan.lexical.startSort 0 input.length

/-! ## Cursor monotonicity -/

theorem TerminalMatchesAt.start_le_stop
    {profile : ParserProfileLayer} {input : List Nat}
    {matcher : TerminalMatcher} {start stop : Nat}
    (matched : TerminalMatchesAt profile input matcher start stop) :
    start ≤ stop := by
  cases matched <;> omega

theorem ParserPackDerivesAt.start_le_stop
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {resultSort : String} {start stop : Nat}
    {tree : CST}
    (derivation : ParserPackDerivesAt profile plan input
      resultSort start stop tree) : start ≤ stop := by
  induction derivation using ParserPackDerivesAt.rec
    (motive_2 := fun _ start stop _ _ => start ≤ stop)
    with
  | lexical _ _ _ _ _ matched =>
      rcases matched with ⟨matched, _⟩
      exact TerminalMatchesAt.start_le_stop matched
  | structural _ _ _ _ _ bodyIH => exact bodyIH
  | nil => exact Nat.le_refl _
  | terminal matched _ restIH =>
      exact Nat.le_trans (TerminalMatchesAt.start_le_stop matched) restIH
  | nonterminal _ _ headIH restIH =>
      exact Nat.le_trans headIH restIH

theorem ParserPackItemsDeriveAt.start_le_stop
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {items : List PackItem} {start stop : Nat}
    {children : List CST}
    (derivation : ParserPackItemsDeriveAt profile plan input
      items start stop children) : start ≤ stop := by
  induction derivation using ParserPackItemsDeriveAt.rec
    (motive_1 := fun _ start stop _ _ => start ≤ stop)
    with
  | lexical _ _ _ _ _ matched =>
      rcases matched with ⟨matched, _⟩
      exact TerminalMatchesAt.start_le_stop matched
  | structural _ _ _ _ _ bodyIH => exact bodyIH
  | nil => exact Nat.le_refl _
  | terminal matched _ restIH =>
      exact Nat.le_trans (TerminalMatchesAt.start_le_stop matched) restIH
  | nonterminal _ _ headIH restIH =>
      exact Nat.le_trans headIH restIH

/-! ## Soundness of bounded enumeration -/

/-- Every enumerated lexical row replays against the exact supplied plan and
input. -/
theorem enumerateLexicalRows_sound
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {resultSort : String} {start stop : Nat}
    {row : DerivationRow}
    (member : row ∈ enumerateLexicalRows profile plan input
      resultSort start stop) :
    Nonempty (Replays profile plan input row.certificate
      resultSort start stop row.tree) := by
  simp only [enumerateLexicalRows, List.mem_flatMap] at member
  obtain ⟨position, _, positionMember⟩ := member
  by_cases resultSortExact :
      (plan.lexical.productions.get position).resultSort = resultSort
  · rw [if_pos resultSortExact] at positionMember
    cases matchedResult :
        terminalMatch? profile input
          (plan.lexical.productions.get position).matcher start with
    | none =>
        rw [matchedResult] at positionMember
        simp at positionMember
    | some result =>
        rcases result with ⟨actualStop, children⟩
        rw [matchedResult] at positionMember
        simp only at positionMember
        by_cases stopExact : actualStop = stop
        · rw [if_pos stopExact] at positionMember
          simp only [List.mem_singleton] at positionMember
          subst row
          subst actualStop
          have matched := terminalMatch?_sound matchedResult
          exact ⟨.lexical position.val position.isLt rfl
            resultSortExact rfl matched⟩
        · rw [if_neg stopExact] at positionMember
          simp at positionMember
  · rw [if_neg resultSortExact] at positionMember
    simp at positionMember

/-- Both mutually recursive enumerators are sound at every finite height. -/
theorem enumerateWithin_sound (fuel : Nat) :
    (∀ (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
        (input : List Nat) (resultSort : String) (start stop : Nat)
        (row : DerivationRow),
      row ∈ enumerateDerivationsWithin fuel profile plan input
          resultSort start stop →
        Nonempty (Replays profile plan input row.certificate
          resultSort start stop row.tree)) ∧
    (∀ (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
        (input : List Nat) (items : List PackItem) (start stop : Nat)
        (row : ItemsRow),
      row ∈ enumerateItemsWithin fuel profile plan input items start stop →
        Nonempty (ItemsReplays profile plan input row.certificate
          items start stop row.children)) := by
  induction fuel with
  | zero =>
      constructor <;> intro <;> simp [enumerateDerivationsWithin,
        enumerateItemsWithin]
  | succ fuel inductionHypothesis =>
      constructor
      · intro profile plan input resultSort start stop row member
        rw [enumerateDerivationsWithin] at member
        rcases List.mem_append.mp member with lexicalMember | structuralMember
        · exact enumerateLexicalRows_sound lexicalMember
        · obtain ⟨position, _, positionMember⟩ :=
            List.mem_flatMap.mp structuralMember
          by_cases resultSortExact :
              (plan.structural.get position).resultSort = resultSort
          · rw [if_pos resultSortExact] at positionMember
            obtain ⟨body, bodyMember, rowExact⟩ :=
              List.mem_map.mp positionMember
            subst row
            obtain ⟨bodyReplay⟩ := inductionHypothesis.2
              profile plan input (plan.structural.get position).items
                start stop body bodyMember
            exact ⟨.structural position.val position.isLt
              resultSortExact rfl bodyReplay⟩
          · rw [if_neg resultSortExact] at positionMember
            simp at positionMember
      · intro profile plan input items start stop row member
        cases items with
        | nil =>
            by_cases cursorExact : start = stop
            · simp only [enumerateItemsWithin, cursorExact, if_pos,
                List.mem_singleton] at member
              subst row
              subst stop
              exact ⟨.nil⟩
            · simp [enumerateItemsWithin, cursorExact] at member
        | cons item rest =>
            cases item with
            | terminal matcher =>
                cases matchedResult :
                    terminalMatch? profile input matcher start with
                | none =>
                    simp [enumerateItemsWithin, matchedResult] at member
                | some result =>
                    rcases result with ⟨middle, terminalChildren⟩
                    simp only [enumerateItemsWithin, matchedResult] at member
                    obtain ⟨tail, tailMember, rowExact⟩ :=
                      List.mem_map.mp member
                    subst row
                    obtain ⟨tailReplay⟩ := inductionHypothesis.2
                      profile plan input rest middle stop tail tailMember
                    have matched := terminalMatch?_sound matchedResult
                    exact ⟨.terminal matched.1 tailReplay⟩
            | nonterminal childSort =>
                simp only [enumerateItemsWithin] at member
                obtain ⟨middle, _, middleMember⟩ :=
                  List.mem_flatMap.mp member
                obtain ⟨head, headMember, tailRowsMember⟩ :=
                  List.mem_flatMap.mp middleMember
                obtain ⟨tail, tailMember, rowExact⟩ :=
                  List.mem_map.mp tailRowsMember
                subst row
                obtain ⟨headReplay⟩ := inductionHypothesis.1
                  profile plan input childSort start middle head headMember
                obtain ⟨tailReplay⟩ := inductionHypothesis.2
                  profile plan input rest middle stop tail tailMember
                exact ⟨.nonterminal headReplay tailReplay⟩

/-- Public soundness theorem for complete derivation rows. -/
theorem enumerateDerivationsWithin_sound
    {fuel : Nat} {profile : ParserProfileLayer}
    {plan : CompiledParserPackPlan} {input : List Nat}
    {resultSort : String} {start stop : Nat} {row : DerivationRow}
    (member : row ∈ enumerateDerivationsWithin fuel profile plan input
      resultSort start stop) :
    Nonempty (Replays profile plan input row.certificate
      resultSort start stop row.tree) :=
  (enumerateWithin_sound fuel).1 _ _ _ _ _ _ _ member

/-- Public soundness theorem for item-vector rows. -/
theorem enumerateItemsWithin_sound
    {fuel : Nat} {profile : ParserProfileLayer}
    {plan : CompiledParserPackPlan} {input : List Nat}
    {items : List PackItem} {start stop : Nat} {row : ItemsRow}
    (member : row ∈ enumerateItemsWithin fuel profile plan input
      items start stop) :
    Nonempty (ItemsReplays profile plan input row.certificate
      items start stop row.children) :=
  (enumerateWithin_sound fuel).2 _ _ _ _ _ _ _ member

/-! ## Completeness below intrinsic height -/

/-- Every semantic ParserPack derivation appears with its exact finite
certificate and CST as soon as the requested fuel reaches its intrinsic
height.  The item-vector cases are proved simultaneously. -/
theorem ParserPackDerivesAt.mem_enumerateDerivationsWithin
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {resultSort : String} {start stop : Nat}
    {tree : CST}
    (derivation : ParserPackDerivesAt profile plan input
      resultSort start stop tree) :
    ∀ fuel, derivation.height ≤ fuel →
      ({ certificate := Certificate.ofDerivation derivation
         tree := tree } : DerivationRow) ∈
        enumerateDerivationsWithin fuel profile plan input
          resultSort start stop := by
  induction derivation using ParserPackDerivesAt.rec
    (motive_2 := fun items start stop children itemDerivation =>
      ∀ fuel, itemDerivation.height ≤ fuel →
        ({ certificate := ItemsCertificate.ofDerivation itemDerivation
           children := children } : ItemsRow) ∈
          enumerateItemsWithin fuel profile plan input items start stop)
    with
  | lexical position valid matcherExact resultSortExact ruleLabelExact matched =>
      intro fuel heightBound
      cases fuel with
      | zero => simp [ParserPackDerivesAt.height] at heightBound
      | succ fuel =>
          rw [enumerateDerivationsWithin]
          apply List.mem_append_left
          simp only [enumerateLexicalRows, List.mem_flatMap]
          let occurrence : Fin plan.lexical.productions.length :=
            ⟨position, valid⟩
          refine ⟨occurrence, by simp, ?_⟩
          have terminalComplete := terminalMatch?_complete matched
          simp only [occurrence, resultSortExact, if_pos, matcherExact,
            terminalComplete, ruleLabelExact, List.mem_singleton]
          rfl
  | structural position valid resultSortExact ruleLabelExact body bodyIH =>
      intro fuel heightBound
      cases fuel with
      | zero => simp [ParserPackDerivesAt.height] at heightBound
      | succ fuel =>
          have bodyBound : body.height ≤ fuel := by
            simp only [ParserPackDerivesAt.height] at heightBound
            omega
          rw [enumerateDerivationsWithin]
          apply List.mem_append_right
          apply List.mem_flatMap.mpr
          let occurrence : Fin plan.structural.length := ⟨position, valid⟩
          refine ⟨occurrence, by simp, ?_⟩
          simp only [occurrence, resultSortExact, if_pos]
          apply List.mem_map.mpr
          refine ⟨{ certificate := ItemsCertificate.ofDerivation body
                    children := _ }, bodyIH fuel bodyBound, ?_⟩
          rw [ruleLabelExact]
          rfl
  | nil =>
      rename_i cursor fuel heightBound
      cases fuel with
      | zero => simp [ParserPackItemsDeriveAt.height] at heightBound
      | succ fuel => simp [enumerateItemsWithin,
          ItemsCertificate.ofDerivation]
  | terminal matched rest restIH =>
      rename_i fuel heightBound
      cases fuel with
      | zero => simp [ParserPackItemsDeriveAt.height] at heightBound
      | succ fuel =>
          have restBound : rest.height ≤ fuel := by
            simp only [ParserPackItemsDeriveAt.height] at heightBound
            omega
          have terminalComplete := terminalMatch?_complete
            (show CSTTerminalMatchesAt profile input _ _ _ matched.cst from
              ⟨matched, rfl⟩)
          simp only [enumerateItemsWithin, terminalComplete]
          apply List.mem_map.mpr
          refine ⟨{ certificate := ItemsCertificate.ofDerivation rest
                    children := _ }, restIH fuel restBound, ?_⟩
          rfl
  | nonterminal head rest headIH restIH =>
      rename_i fuel heightBound
      cases fuel with
      | zero => simp [ParserPackItemsDeriveAt.height] at heightBound
      | succ fuel =>
          have headBound : head.height ≤ fuel := by
            simp only [ParserPackItemsDeriveAt.height] at heightBound
            omega
          have restBound : rest.height ≤ fuel := by
            simp only [ParserPackItemsDeriveAt.height] at heightBound
            omega
          simp only [enumerateItemsWithin]
          apply List.mem_flatMap.mpr
          refine ⟨_, List.mem_range.mpr
            (Nat.lt_succ_of_le
              (ParserPackItemsDeriveAt.start_le_stop rest)), ?_⟩
          apply List.mem_flatMap.mpr
          refine ⟨{ certificate := Certificate.ofDerivation head
                    tree := _ }, headIH fuel headBound, ?_⟩
          apply List.mem_map.mpr
          refine ⟨{ certificate := ItemsCertificate.ofDerivation rest
                    children := _ }, restIH fuel restBound, ?_⟩
          rfl

/-- Height-bounded completeness stated for root derivations. -/
theorem ParserPackRootDerives.mem_enumerateRootWithin
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {tree : CST}
    (derivation : ParserPackRootDerives profile plan input tree)
    {fuel : Nat} (heightBound : derivation.height ≤ fuel) :
    ({ certificate := Certificate.ofDerivation derivation
       tree := tree } : DerivationRow) ∈
      enumerateRootWithin fuel profile plan input := by
  exact
    Mettapedia.GSLT.Parsing.ClassAwareParserPackEnumeration.ParserPackDerivesAt.mem_enumerateDerivationsWithin
      derivation fuel heightBound

/-- A plan/input pair has a complete finite root catalogue at `fuel` when
every root derivation has intrinsic height at most that bound.  This is an
explicit guest-semantic property, not a backend claim. -/
def RootHeightBound
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (fuel : Nat) : Prop :=
  ∀ (tree : CST)
    (derivation : ParserPackRootDerives profile plan input tree),
      derivation.height ≤ fuel

/-- Erase bounded root rows into the certificate/CST catalogue format. -/
def rootCatalogueRows
    (fuel : Nat) (profile : ParserProfileLayer)
    (plan : CompiledParserPackPlan) (input : List Nat) :
    List (Certificate × CST) :=
  (enumerateRootWithin fuel profile plan input).map fun row =>
    (row.certificate, row.tree)

/-- Every row emitted for a root query has exact replay evidence. -/
theorem rootCatalogueRows_replay
    {fuel : Nat} {profile : ParserProfileLayer}
    {plan : CompiledParserPackPlan} {input : List Nat}
    {entry : Certificate × CST}
    (member : entry ∈ rootCatalogueRows fuel profile plan input) :
    Nonempty (Replays profile plan input entry.1
      plan.lexical.startSort 0 input.length entry.2) := by
  obtain ⟨row, rowMember, rowExact⟩ := List.mem_map.mp member
  subst entry
  exact enumerateDerivationsWithin_sound rowMember

/-- A semantic height bound makes the executable rows exhaustive for every
root derivation, including duplicate production occurrences. -/
theorem rootCatalogueRows_complete
    {fuel : Nat} {profile : ParserProfileLayer}
    {plan : CompiledParserPackPlan} {input : List Nat}
    (bounded : RootHeightBound profile plan input fuel)
    (tree : CST)
    (derivation : ParserPackRootDerives profile plan input tree) :
    (Certificate.ofDerivation derivation, tree) ∈
      rootCatalogueRows fuel profile plan input := by
  apply List.mem_map.mpr
  refine ⟨{ certificate := Certificate.ofDerivation derivation
            tree := tree }, ?_, rfl⟩
  exact ParserPackRootDerives.mem_enumerateRootWithin
    derivation (bounded tree derivation)

/-! ## Executable controls -/

private def terminalCanaryProfile : ParserProfileLayer := {
  name := "TerminalEnumerationCanary"
  startSort := "Value"
  classes := [
    { name := "capital-a", kind := .points [65] },
    { name := "not-quote", kind := .except [34] }]
  states := []
}

theorem terminal_any_positive :
    terminalMatch? terminalCanaryProfile [65] .any 0 =
      some (1, [.terminal [65] 0 1]) := by
  decide

theorem terminal_class_positive :
    terminalMatch? terminalCanaryProfile [65] (.class "capital-a") 0 =
      some (1, [.terminal [65] 0 1]) := by
  decide

theorem terminal_class_negative :
    terminalMatch? terminalCanaryProfile [66] (.class "capital-a") 0 = none := by
  decide

theorem terminal_eof_positive :
    terminalMatch? terminalCanaryProfile [65] .eof 1 = some (1, []) := by
  decide

theorem terminal_eof_negative :
    terminalMatch? terminalCanaryProfile [65] .eof 0 = none := by
  decide

private def alternativePlan : CompiledParserPackPlan := {
  lexical := {
    profileName := terminalCanaryProfile.name
    startSort := "Value"
    classes := terminalCanaryProfile.classes
    productions := [
      { label := "value-left", resultSort := "Value",
        matcher := .char 65, childSlots := [0] },
      { label := "value-right", resultSort := "Value",
        matcher := .char 65, childSlots := [0] }]
  }
  structural := []
}

private def singleAlternativePlan : CompiledParserPackPlan := {
  lexical := {
    profileName := terminalCanaryProfile.name
    startSort := "Value"
    classes := terminalCanaryProfile.classes
    productions := [
      { label := "value-left", resultSort := "Value",
        matcher := .char 65, childSlots := [0] }]
  }
  structural := []
}

/-- Positive occurrence control: equal terminal behavior at two physical
production positions yields two independently identified rows. -/
theorem two_lexical_occurrences_are_enumerated :
    enumerateRootWithin 1 terminalCanaryProfile alternativePlan [65] = [
      { certificate := .lexical 0 (.char 65) 0 1
        tree := .node "value-left" 0 1 [.terminal [65] 0 1] },
      { certificate := .lexical 1 (.char 65) 0 1
        tree := .node "value-right" 0 1 [.terminal [65] 0 1] }
    ] := by
  decide

/-- Negative height control: fuel zero cannot masquerade as a complete
enumeration even for a one-step lexical derivation. -/
theorem zero_height_omits_lexical_derivations :
    enumerateRootWithin 0 terminalCanaryProfile alternativePlan [65] = [] := by
  rfl

/-- Semantic-sensitivity control: adding a production occurrence to the
supplied plan observably changes the reference enumeration. -/
theorem adding_production_changes_enumeration :
    enumerateRootWithin 1 terminalCanaryProfile singleAlternativePlan [65] ≠
      enumerateRootWithin 1 terminalCanaryProfile alternativePlan [65] := by
  decide

end Mettapedia.GSLT.Parsing.ClassAwareParserPackEnumeration
